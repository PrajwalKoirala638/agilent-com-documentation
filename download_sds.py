#!/usr/bin/env python3
# Agilent SDS downloader.
#
# JOB 1: Downloads the Safety Data Sheet PDFs found on Agilent's chemical-standards search page.
# Every document can exist in several regional versions; exactly ONE version is downloaded per document:
#   1. _NAEnglish.pdf is the default and is always preferred.
#   2. If it is not available, _NACanada.pdf is downloaded instead.
#   3. If neither is available, one of _Australia.pdf, _EUEnglish.pdf, _MalayEnglish.pdf or _UKEnglish.pdf is used.
#   4. If none of these versions exists, the document is skipped. Any other file format is ignored.
#
# JOB 2 (runs after job 1 has finished): Walks through the result pages of
# https://www.agilent.com/en/search/safety-data-sheets and downloads every card that is labelled
# "English - United States". It downloads those on the current page, goes to the next page, and repeats.
#
# The browser is controlled through invisible_playwright (Playwright on an anti-detect Firefox).
#
# How the script works:
#   * Before anything is requested, the download folder is checked: a document that already has a file there is skipped.
#   * It starts one browser window at 1920x1080 with a single "results" tab.
#   * It visits the home page and a few other pages first, behaving like an ordinary visitor.
#   * It then searches the keywords a-z and 0-9, one after another.
#   * A default (_NAEnglish) version is downloaded as soon as it is found. Fallback versions wait until every
#     keyword has been searched, so a better version found on a later page is never missed.
#   * After each page of results it downloads the PDFs found there, using a short-lived second tab
#     that is opened only when something needs downloading and closed right afterwards.
#   * Only the results tab is ever kept open; popups, extra tabs and extra windows are closed at once.
#   * A SQLite database remembers every URL and file name, so nothing is downloaded twice.
#   * If the browser crashes, or the internet drops, the browser is restarted and the work continues.
#   * Random pauses, back-off waits and a "stop after too many blocks" rule keep the traffic gentle.
#   * Keywords that could not be searched are retried once at the end.
#   * Everything is logged to the console at DEBUG level.

import asyncio  # Lets us check several internet hosts at the same time
import logging  # Prints log lines to the console
import math  # Distance and curve calculations for human-like mouse movement
import random  # Picks random pause lengths and random actions
import re  # Regular expressions for link matching and text cleaning
import shutil  # Finds the "ping" program on the system PATH
import socket  # Opens a plain TCP connection when ping is unavailable
import sqlite3  # Built-in database that remembers what has been downloaded
import string  # Supplies the lowercase letters and digits used as search keywords
import subprocess  # Runs "ping" as an external process
import sys  # Gives access to standard output and the current platform name
import threading  # Runs the internet check in the background
import time  # Provides sleep() and the current time
from concurrent.futures import (
    ThreadPoolExecutor,
)  # Runs the async internet check in its own clean thread
from contextlib import (
    contextmanager,
)  # Turns a method into something usable in a "with" block
from dataclasses import dataclass  # Makes small classes that only hold data
from pathlib import Path  # Object-oriented filesystem paths
from typing import (
    Any,
    Iterator,
    Optional,
)  # Type hints for generators, optional values and Playwright objects
from urllib.parse import unquote, urlparse  # Helpers to read a file name out of a URL

from invisible_playwright import (
    InvisiblePlaywright,
)  # Playwright on an anti-detect Firefox

from invisible_playwright._pw.sync_api import (  # The Playwright copy bundled with invisible_playwright (its errors only match this copy)
    Dialog,  # Type of alert/confirm popups
    Download,  # Type of a browser download
    Page,  # Type of a browser tab
    Error as PlaywrightError,  # Base error class raised by Playwright
    TimeoutError as PlaywrightTimeoutError,  # Error raised when Playwright waits too long
)  # End of the import list

# ============================================================== SETTINGS

SEARCH_URL_TEMPLATE = "https://www.agilent.com/en/product/chemical-standards/search-results?tabname=related_part_number&keyword={search_keyword}"  # Search page address; the keyword is filled in later
SEARCH_KEYWORDS = list(
    string.ascii_lowercase + string.digits
)  # Every keyword to search: the letters a-z followed by the digits 0-9
HOME_PAGE_URL = (
    "https://www.agilent.com/"  # The page visited first, like a normal visitor would
)
HOME_PAGE_BROWSING_SECONDS = (
    30  # How long to move the mouse and scroll on the home page
)
OTHER_PAGES_TO_VISIT = 3  # How many other pages are opened from the home page
OTHER_PAGE_BROWSING_SECONDS = 30  # How long to stay on each of those pages
DEFAULT_VERSION_SUFFIX = (
    "_NAEnglish.pdf"  # The preferred version of every document (USA English)
)
FIRST_FALLBACK_VERSION_SUFFIX = (
    "_NACanada.pdf"  # Used only when the default version is not available
)
OTHER_VERSION_SUFFIXES = (
    "_Australia.pdf",
    "_EUEnglish.pdf",
    "_MalayEnglish.pdf",
    "_UKEnglish.pdf",
)  # Used only when neither version above is available; tried in this order
ALLOWED_VERSION_SUFFIXES_BEST_FIRST = (
    DEFAULT_VERSION_SUFFIX,
    FIRST_FALLBACK_VERSION_SUFFIX,
) + OTHER_VERSION_SUFFIXES  # Every format that may be downloaded, best first; all other formats are ignored

# ---- Job 2: the "Safety Data Sheets (SDS)" search page
SDS_PAGE_PLAIN_URL = "https://www.agilent.com/en/search/safety-data-sheets"  # The page with every safety data sheet
SDS_PAGE_FILTERED_URL = (
    "https://www.agilent.com/en/search/safety-data-sheets"
    "?cq=%40objecttype%3D%3D%22Material%20Safety%20Data%20Sheet%22"
    "%20AND%20%40locale%3D%3D%22English_UNITED%20STATES%22"
)  # Same page, but asking the search engine for US English documents only (tried first)
TRY_FILTERED_SDS_URL_FIRST = (
    True  # If the filtered address shows no results, the plain address is used instead
)
US_ENGLISH_LABEL = (
    "English - United States"  # Only cards carrying this language tag are downloaded
)
SDS_RESULTS_SCOPE_SELECTOR = "[data-tab-content='documentsSupport']"  # The results tab that holds the safety data sheet cards
SDS_NEXT_BUTTON_SELECTOR = (
    SDS_RESULTS_SCOPE_SELECTOR + " agt-pagination button[data-action='next']"
)  # The "next page" button of that tab
MAXIMUM_SDS_RESULT_PAGES = (
    600  # Safety limit; the site shows at most 500 pages of 10 results
)
SDS_PAGE_CHANGE_TIMEOUT_SECONDS = (
    20  # How long to wait for new cards to appear after clicking "next"
)

BROWSER_WINDOW_WIDTH_PIXELS = 1920  # Browser window width in pixels (full HD)
BROWSER_WINDOW_HEIGHT_PIXELS = 1080  # Browser window height in pixels (full HD)

DOWNLOAD_FOLDER = Path("PDFs").resolve()  # Full path of the folder where PDFs are saved
DATABASE_FILE_PATH = Path(
    "download_history.sqlite3"
).resolve()  # Full path of the SQLite history file
MAXIMUM_FILE_NAME_STEM_LENGTH = 150  # Longest allowed file name, not counting ".pdf"
MAXIMUM_URLS_PER_DATABASE_QUERY = (
    500  # Most "?" placeholders used in one SQL query (SQLite has a limit)
)

MAXIMUM_RESULT_PAGES_PER_KEYWORD = (
    200  # Safety limit on how many result pages are followed per keyword
)
PAGE_LOAD_TIMEOUT_MILLISECONDS = (
    30_000  # How long to wait for a page to open, in milliseconds
)
DOWNLOAD_START_TIMEOUT_MILLISECONDS = (
    60_000  # How long to wait for the browser to start one download, in milliseconds
)

PAUSE_SECONDS_RANGE_BETWEEN_RESULT_PAGES = (
    2.0,
    5.0,
)  # Random pause range (seconds) before moving to the next result page
PAUSE_SECONDS_RANGE_BETWEEN_DOWNLOADS = (
    1.0,
    3.0,
)  # Random pause range (seconds) between two downloads
PAUSE_SECONDS_RANGE_BETWEEN_KEYWORDS = (
    5.0,
    10.0,
)  # Random pause range (seconds) before the next keyword
ACTIVITY_SECONDS_RANGE_AFTER_OPENING_SEARCH_PAGE = (
    3.0,
    6.0,
)  # Random activity time (seconds) after a search page opens
MAXIMUM_ACCESS_DENIED_ATTEMPTS = (
    3  # How many times a page showing "Access Denied" is retried
)
ACCESS_DENIED_BACKOFF_SECONDS = (
    30  # First back-off wait in seconds; it doubles on every further attempt
)
MAXIMUM_CONSECUTIVE_BLOCKS = 5  # The whole run stops after this many blocks in a row
MAXIMUM_BROWSER_RESTARTS = (
    5  # How many times the browser may be restarted after a crash
)

INTERNET_CHECK_HOSTS = (
    "1.1.1.1",
    "8.8.8.8",
)  # Public addresses used to test whether the internet works
INTERNET_CHECK_INTERVAL_SECONDS = 10  # How often the background internet check runs
PING_TIMEOUT_SECONDS = 5  # How long to wait for one ping answer
FALLBACK_CONNECTION_TEST_PORT = (
    53  # Port for a plain connection test when ping is unavailable (the DNS port)
)
FALLBACK_CONNECTION_TEST_TIMEOUT_SECONDS = (
    2  # How long to wait for that fallback connection test
)

download_logger = logging.getLogger(
    "sds_downloader"
)  # The logger used by every function in this script


def validate_settings() -> None:  # Stop immediately if a setting above is obviously wrong
    assert (
        SEARCH_KEYWORDS
    ), "SEARCH_KEYWORDS must contain at least one keyword"  # There must be something to search
    assert (
        BROWSER_WINDOW_WIDTH_PIXELS > 0 and BROWSER_WINDOW_HEIGHT_PIXELS > 0
    ), "The browser window size must be positive"  # A window needs a real size
    assert all(
        version_suffix.lower().endswith(".pdf")
        for version_suffix in ALLOWED_VERSION_SUFFIXES_BEST_FIRST
    ), "Every version suffix must end with .pdf"  # We only download PDF files
    assert len(
        {
            version_suffix.lower()
            for version_suffix in ALLOWED_VERSION_SUFFIXES_BEST_FIRST
        }
    ) == len(
        ALLOWED_VERSION_SUFFIXES_BEST_FIRST
    ), "The version suffixes must all be different"  # A suffix listed twice would be ambiguous
    for pause_range in (
        PAUSE_SECONDS_RANGE_BETWEEN_RESULT_PAGES,
        PAUSE_SECONDS_RANGE_BETWEEN_DOWNLOADS,
        PAUSE_SECONDS_RANGE_BETWEEN_KEYWORDS,
        ACTIVITY_SECONDS_RANGE_AFTER_OPENING_SEARCH_PAGE,
    ):  # Look at every random pause range
        assert (
            0 <= pause_range[0] <= pause_range[1]
        ), f"Pause range {pause_range} must be (low, high) with low <= high"  # The low value must not exceed the high value


class AccessBlockedError(
    Exception
):  # Raised when the website keeps blocking us and the run should stop
    """The website kept blocking us; the whole run should stop."""  # Short description of the error


class InternetOutageError(
    Exception
):  # Raised when the internet is down in the middle of a step
    """The internet is down; the current step should be retried once it is back."""  # Short description of the error


@dataclass  # Automatically creates the constructor for this little data holder
class RunStatistics:  # Running totals for the whole run
    downloaded_count: int = 0  # PDFs saved to disk
    skipped_count: int = (
        0  # URLs skipped because the file already exists or is not a PDF
    )
    unavailable_count: int = 0  # URLs whose page says it may no longer exist
    failed_count: int = 0  # URLs that could not be downloaded this time
    consecutive_block_count: int = 0  # "Access Denied" pages seen in a row


# ============================================================== LOGGING


def configure_console_logging() -> None:  # Send every log message to the console at DEBUG level
    console_handler = logging.StreamHandler(
        sys.stdout
    )  # Create a handler that writes to standard output
    console_handler.setLevel(
        logging.DEBUG
    )  # Let every message level through, including DEBUG
    console_handler.setFormatter(
        logging.Formatter(
            "%(asctime)s | %(levelname)-8s | %(message)s", "%Y-%m-%d %H:%M:%S"
        )
    )  # Choose how each line looks
    download_logger.setLevel(
        logging.DEBUG
    )  # Make DEBUG the lowest level the logger accepts
    if (
        not download_logger.handlers
    ):  # Only attach a handler once, so lines are never printed twice
        download_logger.addHandler(
            console_handler
        )  # Attach the console handler to our logger
    download_logger.propagate = (
        False  # Stop the root logger from printing every line a second time
    )


def attach_browser_event_logging(
    browser_page: Page,
) -> None:  # Connect logging to one browser tab
    """Log console output, errors, failed requests, navigation, downloads and popups of one tab."""  # Short description
    browser_page.on(
        "console",
        lambda console_message: download_logger.debug(
            "BROWSER CONSOLE [%s] %s", console_message.type, console_message.text
        ),
    )  # Log what the website prints to its own console
    browser_page.on(
        "pageerror",
        lambda page_error: download_logger.error("BROWSER PAGE ERROR %s", page_error),
    )  # Log JavaScript errors raised by the website
    browser_page.on(
        "requestfailed",
        lambda failed_request: download_logger.warning(
            "REQUEST FAILED %s %s -> %s",
            failed_request.method,
            failed_request.url,
            failed_request.failure,
        ),
    )  # Log network requests that failed
    browser_page.on(
        "response",
        lambda http_response: download_logger.warning(
            "HTTP %s %s", http_response.status, http_response.url
        )
        if http_response.status >= 400
        else None,
    )  # Log HTTP error answers (400 and above)
    browser_page.on(
        "framenavigated",
        lambda navigated_frame: download_logger.info(
            "NAVIGATED to %s", navigated_frame.url
        )
        if navigated_frame.parent_frame is None
        else None,
    )  # Log changes of the top-level page address
    browser_page.on(
        "download",
        lambda started_download: download_logger.info(
            "BROWSER DOWNLOAD STARTED url=%s suggested_name=%s",
            started_download.url,
            started_download.suggested_filename,
        ),
    )  # Log every download the browser starts

    def handle_dialog_popup(
        dialog_popup: Dialog,
    ) -> None:  # Deal with alert/confirm popups so they can never block us
        download_logger.warning(
            "BROWSER DIALOG [%s] %s", dialog_popup.type, dialog_popup.message
        )  # Log what the popup said
        dialog_popup.dismiss()  # Close the popup

    browser_page.on(
        "dialog", handle_dialog_popup
    )  # Attach the popup handler to this tab


def log_run_statistics(
    run_statistics: RunStatistics, summary_label: str
) -> None:  # Print the running totals on one line
    download_logger.info(
        "%s: downloaded %d | skipped %d | page unavailable %d | failed %d",
        summary_label,
        run_statistics.downloaded_count,
        run_statistics.skipped_count,
        run_statistics.unavailable_count,
        run_statistics.failed_count,
    )  # Write the summary line


# ============================================================== SMALL HELPERS


def split_into_batches(
    items_to_split: list, maximum_batch_size: int
) -> Iterator[list]:  # Hand out a long list in smaller pieces
    for batch_start_position in range(
        0, len(items_to_split), maximum_batch_size
    ):  # Jump forward one batch at a time
        yield items_to_split[
            batch_start_position : batch_start_position + maximum_batch_size
        ]  # Give back the next piece of the list


def remove_fragment_from_url(
    page_url: str,
) -> str:  # Remove the "#section" part of a web address
    return page_url.split("#")[0]  # Keep only what comes before the first "#"


# ============================================================== DATABASE
#
# Two tables:
#   collected_urls   -- every PDF URL ever seen, and whether it has been handled
#   downloaded_files -- every file name actually saved, so duplicate names are caught too


class DownloadDatabase:  # Wraps the SQLite connection and every query this script needs
    def __init__(self, database_path: Path):  # Open (or create) the database file
        download_logger.info(
            "Opening database: %s", database_path
        )  # Tell the user which database file is used
        self.database_connection = sqlite3.connect(
            database_path
        )  # Connect to the database file on disk
        self.safe_file_names_found_in_folder: set[
            str
        ] = (
            set()
        )  # Clean names of the PDFs seen in the download folder, so files are recognised even when their names use capitals or spaces
        with self.database_connection:  # Save the changes automatically when this block ends
            self.database_connection.execute(
                "CREATE TABLE IF NOT EXISTS collected_urls (source_url TEXT PRIMARY KEY, is_processed INTEGER NOT NULL DEFAULT 0)"
            )  # One row per URL, with a "done" flag
            self.database_connection.execute(
                "CREATE TABLE IF NOT EXISTS downloaded_files (file_name TEXT PRIMARY KEY COLLATE NOCASE, source_url TEXT NOT NULL, downloaded_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP)"
            )  # One row per saved file name

    def close_database(self) -> None:  # Close the database connection
        self.database_connection.close()  # Release the database file

    def register_pdf_files_already_on_disk(
        self, pdf_folder: Path
    ) -> None:  # Look at the download folder first and remember every PDF in it
        """Scan the download folder so every PDF that is already there is skipped and never downloaded again."""  # Short description
        newly_registered_count = (
            0  # Counts how many existing files were newly registered in the database
        )
        with self.database_connection:  # Save the changes automatically when this block ends
            for pdf_path in pdf_folder.iterdir():  # Look at every file in the folder
                if (
                    not pdf_path.is_file() or pdf_path.suffix.lower() != ".pdf"
                ):  # Ignore sub-folders and files that are not PDFs (.PDF counts too)
                    continue  # Move on to the next file
                self.safe_file_names_found_in_folder.add(
                    build_safe_file_name(pdf_path.name)
                )  # Remember its clean name, so "Foo Bar_NAEnglish.PDF" matches "foo_bar_naenglish.pdf"
                insert_result = self.database_connection.execute(
                    "INSERT OR IGNORE INTO downloaded_files (file_name, source_url) VALUES (?, ?)",
                    (pdf_path.name, "found on disk before first run"),
                )  # Also record it in the database
                newly_registered_count += (
                    insert_result.rowcount
                )  # Add one when a new row was really inserted
        download_logger.info(
            "Download folder check: %d PDF file(s) found in %s (%d newly recorded); documents that already have a file are skipped",
            len(self.safe_file_names_found_in_folder),
            pdf_folder,
            newly_registered_count,
        )  # Report the result

    def ignore_urls_in_unwanted_formats(
        self,
    ) -> None:  # Drop old pending URLs whose format we never download
        """Mark pending URLs that are not in one of the wanted formats as done (for example after a settings change)."""  # Short description
        pending_urls = self.load_unprocessed_urls()  # Every URL that is still waiting
        ignored_urls = [
            pending_url
            for pending_url in pending_urls
            if not is_wanted_version_pdf_url(pending_url)
        ]  # Keep the ones in an unwanted format
        for ignored_url in ignored_urls:  # Go through each URL that should be ignored
            self.mark_url_processed(
                ignored_url
            )  # Mark it as done so it is never downloaded
        download_logger.info(
            "Ignored %d pending URL(s) that are not in one of the %d wanted formats",
            len(ignored_urls),
            len(ALLOWED_VERSION_SUFFIXES_BEST_FIRST),
        )  # Report the result

    def save_newly_found_urls(self, found_urls: set) -> None:  # Store newly found URLs
        with self.database_connection:  # Save the changes automatically when this block ends
            insert_result = self.database_connection.executemany(
                "INSERT OR IGNORE INTO collected_urls (source_url) VALUES (?)",
                [(found_url,) for found_url in found_urls],
            )  # Insert many URLs at once, ignoring known ones
        download_logger.info(
            "Saved %d new URL(s) (%d were already known)",
            insert_result.rowcount,
            len(found_urls) - insert_result.rowcount,
        )  # Report the result

    def load_unprocessed_urls(self) -> list:  # Get every URL that still needs work
        database_rows = self.database_connection.execute(
            "SELECT source_url FROM collected_urls WHERE is_processed = 0 ORDER BY source_url"
        )  # Ask the database for the waiting URLs
        return [
            database_row[0] for database_row in database_rows.fetchall()
        ]  # Return just the URL text of each row

    def keep_only_unprocessed_urls(
        self, candidate_urls: list
    ) -> list:  # Keep only the URLs from this list that are still waiting
        pending_urls: set[
            str
        ] = set()  # Collects the URLs the database says are waiting
        for url_batch in split_into_batches(
            candidate_urls, MAXIMUM_URLS_PER_DATABASE_QUERY
        ):  # Work in batches so SQLite's variable limit is never exceeded
            placeholder_text = ",".join(
                "?" for url_in_batch in url_batch
            )  # One "?" per URL in this batch
            database_rows = self.database_connection.execute(
                f"SELECT source_url FROM collected_urls WHERE is_processed = 0 AND source_url IN ({placeholder_text})",
                url_batch,
            )  # Ask which of these URLs are still waiting
            pending_urls.update(
                database_row[0] for database_row in database_rows.fetchall()
            )  # Remember the waiting ones
        return [
            candidate_url
            for candidate_url in candidate_urls
            if candidate_url in pending_urls
        ]  # Keep the candidates in their original order

    def mark_url_processed(self, source_url: str) -> None:  # Mark one URL as done
        with self.database_connection:  # Save the change automatically when this block ends
            self.database_connection.execute(
                "UPDATE collected_urls SET is_processed = 1 WHERE source_url = ?",
                (source_url,),
            )  # Switch the "done" flag on

    def is_file_name_already_saved(
        self, file_name: str
    ) -> bool:  # Check whether a file name was already saved
        """The download folder is checked first because the files on disk are the truth; the database is only a backup record."""  # Short description
        if (
            file_name in self.safe_file_names_found_in_folder
            or (DOWNLOAD_FOLDER / file_name).exists()
        ):  # The file is in the download folder
            return True  # Nothing more to check
        matching_row = self.database_connection.execute(
            "SELECT 1 FROM downloaded_files WHERE file_name = ?", (file_name,)
        ).fetchone()  # Otherwise look the name up in the database
        return matching_row is not None  # True when a matching row exists

    def record_saved_file(
        self, file_name: str, source_url: str
    ) -> None:  # Save a record of a downloaded file
        with self.database_connection:  # Save the change automatically when this block ends
            self.database_connection.execute(
                "INSERT OR IGNORE INTO downloaded_files (file_name, source_url) VALUES (?, ?)",
                (file_name, source_url),
            )  # Insert a row describing the saved file
        self.safe_file_names_found_in_folder.add(
            file_name
        )  # The file is now in the download folder as well

    def is_file_for_url_already_downloaded(
        self, source_url: str
    ) -> bool:  # Cheap check done before downloading anything
        """If the file name that the URL implies is already known or on disk, there is no need to download it."""  # Short description
        guessed_file_name = guess_file_name_from_url(
            source_url
        )  # Predict the file name from the URL itself
        if guessed_file_name is None:  # The URL does not reveal a trustworthy name
            return False  # We cannot tell, so assume it still needs downloading
        safe_file_name = build_safe_file_name(
            guessed_file_name
        )  # Apply the naming rules to the guess
        return self.is_file_name_already_saved(
            safe_file_name
        )  # Checks the download folder first, then the database

    def is_any_version_of_document_saved(
        self, document_key: str
    ) -> bool:  # Check whether a file for this document was already saved, in any wanted format
        """A document is finished as soon as one of its wanted versions has been saved."""  # Short description
        for (
            version_suffix
        ) in ALLOWED_VERSION_SUFFIXES_BEST_FIRST:  # Check every wanted format
            possible_file_name = build_safe_file_name(
                document_key + version_suffix
            )  # The name this version would be saved under
            if self.is_file_name_already_saved(
                possible_file_name
            ):  # Found in the download folder or, failing that, in the database
                return True  # One version is enough
        return False  # No version of this document has been saved yet


# ============================================================== FILE NAMES


def guess_file_name_from_url(
    source_url: str,
) -> Optional[str]:  # Predict the file name before downloading
    last_path_segment = Path(
        unquote(urlparse(source_url).path)
    ).name  # Take the last part of the address path, with %20-style codes decoded
    return (
        last_path_segment if last_path_segment.lower().endswith(".pdf") else None
    )  # Only trust names that really end in .pdf


def find_version_suffix_in_url(
    source_url: str,
) -> Optional[str]:  # Work out which wanted format (if any) a PDF address is in
    lowercase_path = unquote(
        urlparse(source_url).path
    ).lower()  # The address path in lowercase, with %20-style codes decoded
    for (
        version_suffix
    ) in ALLOWED_VERSION_SUFFIXES_BEST_FIRST:  # Check the wanted formats one by one
        if lowercase_path.endswith(
            version_suffix.lower()
        ):  # The address ends with this format
            return version_suffix  # Found the format
    return None  # The address is not in any wanted format, so it is ignored


def is_wanted_version_pdf_url(
    source_url: str,
) -> bool:  # True when the address is a PDF in one of the wanted formats
    return (
        find_version_suffix_in_url(source_url) is not None
    )  # Any wanted format counts


def get_document_key_from_url(
    source_url: str,
) -> str:  # The file name without its format ending; every version of a document shares it
    version_suffix = (
        find_version_suffix_in_url(source_url) or ""
    )  # The format ending of this address
    lowercase_file_name = Path(
        unquote(urlparse(source_url).path)
    ).name.lower()  # The file name in lowercase
    return lowercase_file_name[
        : len(lowercase_file_name) - len(version_suffix)
    ]  # Cut the format ending off


def get_version_rank_from_url(
    source_url: str,
) -> int:  # 0 is the default version; higher numbers are less preferred
    version_suffix = find_version_suffix_in_url(
        source_url
    )  # The format of this address
    if version_suffix is None:  # Not a wanted format
        return len(
            ALLOWED_VERSION_SUFFIXES_BEST_FIRST
        )  # Rank it after every wanted format
    return ALLOWED_VERSION_SUFFIXES_BEST_FIRST.index(
        version_suffix
    )  # Its position in the best-first list


def group_urls_by_document(
    source_urls,
) -> dict:  # Put every version of the same document together, best version first
    urls_by_document: dict[
        str, list[str]
    ] = {}  # Maps a document key to the addresses of its versions
    for source_url in sorted(
        set(source_urls)
    ):  # Go through each distinct address in a stable order
        if not is_wanted_version_pdf_url(source_url):  # An unwanted format
            continue  # Ignore it
        urls_by_document.setdefault(get_document_key_from_url(source_url), []).append(
            source_url
        )  # File it under its document
    for candidate_urls in urls_by_document.values():  # Look at every document
        candidate_urls.sort(
            key=get_version_rank_from_url
        )  # Put the default version first, then the fallbacks in order
    return urls_by_document  # Give the groups back


def build_safe_file_name(
    raw_file_name: str,
) -> str:  # Clean a file name so it follows the naming rules
    file_name_stem = (
        raw_file_name[:-4] if raw_file_name.lower().endswith(".pdf") else raw_file_name
    )  # Remove ".pdf" before cleaning
    file_name_stem = re.sub(
        r"[^a-z0-9_]+", "_", file_name_stem.lower()
    )  # Lowercase everything and replace odd characters with underscores
    file_name_stem = re.sub(r"_+", "_", file_name_stem)  # Merge repeated underscores
    version_ending = ""  # The format ending (such as _naenglish) must never be cut off when a long name is shortened
    for (
        version_suffix
    ) in (
        ALLOWED_VERSION_SUFFIXES_BEST_FIRST
    ):  # Check whether the name ends with a wanted format
        if file_name_stem.endswith(version_suffix[:-4].lower()):  # It does
            version_ending = version_suffix[:-4].lower()  # Remember the ending
            break  # No need to look further
    document_part = file_name_stem[
        : len(file_name_stem) - len(version_ending)
    ]  # Everything before the format ending
    document_part = document_part[
        : MAXIMUM_FILE_NAME_STEM_LENGTH - len(version_ending)
    ].strip(
        "_"
    )  # Shorten only the document part and trim the ends
    return (
        (document_part or "document") + version_ending + ".pdf"
    )  # Use "document" if nothing is left, then add the ending and .pdf


# ============================================================== BLOCK TRACKING


def register_access_block(
    run_statistics: RunStatistics,
) -> None:  # Count one more "Access Denied" in a row
    run_statistics.consecutive_block_count += (
        1  # Add one to the blocks-in-a-row counter
    )
    download_logger.warning(
        "Consecutive access blocks: %d/%d",
        run_statistics.consecutive_block_count,
        MAXIMUM_CONSECUTIVE_BLOCKS,
    )  # Show the current count
    if (
        run_statistics.consecutive_block_count >= MAXIMUM_CONSECUTIVE_BLOCKS
    ):  # Check whether the limit has been reached
        raise AccessBlockedError(
            f"The website blocked {MAXIMUM_CONSECUTIVE_BLOCKS} requests in a row. Stopping so the block does not get worse. Try again later or contact Agilent."
        )  # Stop the whole run


def reset_access_blocks(
    run_statistics: RunStatistics,
) -> None:  # A page loaded fine, so the blocks-in-a-row count starts again
    run_statistics.consecutive_block_count = 0  # Set the counter back to zero


# ============================================================== PAGE CHECKS & ACTIONS

PAGE_UNAVAILABLE_MESSAGE = "the page may be temporarily unavailable or may no longer exist"  # Text shown on the website's error page


def is_access_denied_error_page(
    browser_page: Page,
) -> bool:  # Check whether the website blocked this visit
    try:  # Reading the page can fail while it is changing
        page_title, page_source = (
            browser_page.title(),
            browser_page.content(),
        )  # Read the page title and its HTML source
    except PlaywrightError:  # The page could not be read
        return False  # Assume the page is fine
    lowercase_page_source = (
        page_source.lower()
    )  # Lowercase copy so the checks ignore capital letters
    is_blocked_by_website = (  # Decide whether this is the "Access Denied" block page
        "access denied" in page_title.lower()  # The title says "Access Denied"
        or "errors.edgesuite.net"
        in lowercase_page_source  # The page links to the Akamai error site
        or "you don't have permission to access"
        in lowercase_page_source  # The usual block message appears
    )  # End of the decision
    if is_blocked_by_website:  # The website blocked us
        block_reference_match = re.search(
            r"Reference #([0-9a-fA-F.]+)", page_source
        )  # Look for the block's reference number
        download_logger.warning(
            "ACCESS DENIED page detected (reference %s) at %s",
            block_reference_match.group(1) if block_reference_match else "unknown",
            browser_page.url,
        )  # Record the block
    return is_blocked_by_website  # Tell the caller whether we were blocked


def is_page_unavailable_error_page(
    browser_page: Page,
) -> bool:  # Check for the "page may no longer exist" error page
    try:  # Reading the page can fail while it is changing
        visible_text = browser_page.inner_text(
            "body", timeout=3000
        )  # Read the text a person would see; give up after 3 seconds if the page has no body
    except PlaywrightError:  # The page could not be read
        return False  # Assume the page is fine
    normalized_text = re.sub(
        r"\s+", " ", visible_text.lower()
    )  # Lowercase the text and squeeze all whitespace into single spaces
    error_message_found = (
        PAGE_UNAVAILABLE_MESSAGE in normalized_text
    )  # Look for the known error message
    if error_message_found:  # The page is the error page
        download_logger.warning(
            "PAGE UNAVAILABLE message found at %s", browser_page.url
        )  # Record it
    return error_message_found  # Tell the caller what we found


def is_results_page_usable(
    browser_page: Page, run_statistics: RunStatistics
) -> bool:  # Check a result page before reading it
    if is_page_unavailable_error_page(
        browser_page
    ):  # Check for the "page may no longer exist" message
        return False  # Skip this page
    if is_access_denied_error_page(browser_page):  # Check for the "Access Denied" page
        register_access_block(
            run_statistics
        )  # Count the block, which may stop the whole run
        return False  # Skip this page
    reset_access_blocks(
        run_statistics
    )  # The page is fine, so the blocks-in-a-row count starts again
    return True  # The page can be read


def wait_for_network_to_settle(
    browser_page: Page,
) -> None:  # Wait until the page stops loading data
    try:  # Waiting can time out on pages that never stop loading
        browser_page.wait_for_load_state(
            "networkidle", timeout=20_000
        )  # Wait up to 20 seconds for a quiet network
    except PlaywrightTimeoutError:  # The page kept loading data
        pass  # Carry on anyway, the page is probably usable
    time.sleep(2)  # Give the page's scripts a little extra time to draw the results


def dismiss_cookie_banner(
    browser_page: Page,
) -> None:  # Close the cookie popup if it shows up
    for accept_selector in (
        "#onetrust-accept-btn-handler",
        "button[id*='accept' i]",
    ):  # Known ways of finding the accept button
        try:  # Ignore any problem finding or clicking the button
            accept_button = browser_page.locator(
                accept_selector
            ).first  # Find the first matching button
            if accept_button.is_visible():  # Only click it if it is really on screen
                accept_button.click(timeout=3000)  # Accept the cookies
                time.sleep(0.5)  # Give the popup a moment to disappear
                return  # Stop after the first button that worked
        except PlaywrightError:  # The button was missing or could not be clicked
            continue  # Try the next way of finding it


def scroll_to_bottom_of_page(
    browser_page: Page, pause_seconds: float = 0.8
) -> None:  # Scroll down so lazily loaded results appear
    previous_page_height = 0  # The page height measured in the previous round
    for _scroll_round in range(15):  # Scroll at most 15 times
        browser_page.evaluate(
            "window.scrollTo(0, document.documentElement.scrollHeight)"
        )  # Jump to the bottom of the page
        time.sleep(pause_seconds)  # Wait for more content to load
        current_page_height = browser_page.evaluate(
            "document.documentElement.scrollHeight"
        )  # Measure the page again
        if (
            current_page_height == previous_page_height
        ):  # Check whether the page stopped growing
            break  # Everything is loaded, so stop scrolling
        previous_page_height = (
            current_page_height  # Remember this height for the next comparison
        )


PDF_OR_SAFETY_DATA_SHEET_LINK_PATTERN = re.compile(
    r"\.pdf(\?|#|$)|msds|/sds|sds[_/\-.]|safety[-_ ]?data", re.IGNORECASE
)  # Matches links that look like PDFs or safety data sheets
PDF_URL_INSIDE_PAGE_SOURCE_PATTERN = re.compile(
    r"https?://[^\s\"'<>\\]+?\.pdf(?:\?[^\s\"'<>\\]*)?", re.IGNORECASE
)  # Matches .pdf addresses hidden inside the page source


def extract_pdf_urls_from_page(
    browser_page: Page,
) -> set:  # Find every PDF address on the page that is in a wanted format
    found_urls = set()  # Collects the addresses found on this page
    for link_url in browser_page.evaluate(
        "() => Array.from(document.querySelectorAll('a[href]')).map(linkElement => linkElement.href)"
    ):  # Read the address of every link on the page
        if link_url.startswith("http") and PDF_OR_SAFETY_DATA_SHEET_LINK_PATTERN.search(
            link_url
        ):  # Keep links that look like PDFs or safety data sheets
            found_urls.add(link_url)  # Remember the link
    page_source_text = browser_page.content().replace(
        "\\/", "/"
    )  # Page source with JSON-style escaped slashes turned back into normal ones
    for url_found_in_source in PDF_URL_INSIDE_PAGE_SOURCE_PATTERN.findall(
        page_source_text
    ):  # Also search the raw page source for hidden PDF addresses
        found_urls.add(
            url_found_in_source.replace("\\u0026", "&").replace("&amp;", "&")
        )  # Remember it after decoding escaped ampersands
    wanted_urls = {
        found_url for found_url in found_urls if is_wanted_version_pdf_url(found_url)
    }  # Keep only the wanted formats and ignore all others
    download_logger.debug(
        "Found %d PDF link(s), %d in a wanted format", len(found_urls), len(wanted_urls)
    )  # Record how many links were found
    return wanted_urls  # Give back only the addresses in a wanted format


NEXT_PAGE_BUTTON_SELECTORS = [  # Different ways the "next page" button might be found
    "button[aria-label*='next' i]",  # Buttons whose label mentions "next"
    "a[aria-label*='next' i]",  # Links whose label mentions "next"
    "li.next:not(.disabled) a",  # A link inside an enabled "next" list item
    "a.next",  # A link with a "next" class
    "button.next",  # A button with a "next" class
    "[class*='pagination'] [class*='next']",  # A "next" element inside a pagination block
    "xpath=//button[normalize-space()='Next' or normalize-space()='>']",  # A button whose text is Next or >
    "xpath=//a[normalize-space()='Next' or normalize-space()='>']",  # A link whose text is Next or >
]  # End of the selector list


def click_next_page_button(
    browser_page: Page,
) -> bool:  # Go to the next page of results if there is one
    for (
        next_button_selector
    ) in NEXT_PAGE_BUTTON_SELECTORS:  # Try each known way of finding the button
        matching_locator = browser_page.locator(
            next_button_selector
        )  # Find every element matching this selector
        try:  # Counting can fail if the page changes at the wrong moment
            match_count = matching_locator.count()  # Count the matching elements
        except PlaywrightError:  # The selector could not be used
            continue  # Try the next selector
        for match_position in range(match_count):  # Check each match by its position
            candidate_button = matching_locator.nth(match_position)  # Pick one match
            try:  # The element may disappear or be covered
                if (
                    not candidate_button.is_visible()
                    or not candidate_button.is_enabled()
                ):  # The button is hidden or disabled
                    continue  # Skip this one
                if candidate_button.get_attribute(
                    "aria-disabled"
                ) == "true" or "disabled" in (
                    candidate_button.get_attribute("class") or ""
                ):  # Other ways a button can be marked disabled
                    continue  # Skip this one
                click_element_like_a_human(
                    browser_page, candidate_button
                )  # Move the pointer to the button like a person and click it
                download_logger.info(
                    "Clicked next page button (%s)", next_button_selector
                )  # Record the click
                return True  # We moved to another page
            except PlaywrightError:  # The click did not work
                continue  # Try the next match
    download_logger.info(
        "No usable next page button found"
    )  # Record that the last page was reached
    return False  # There is no further page


# ============================================================== HUMAN-LIKE BEHAVIOUR
#
# Three parts:
#   1. Links           -- which links an ordinary visitor might click
#   2. Human-like input -- curved mouse paths, wheel scrolling, random key presses, clicking, and
#                          pausing with activity instead of sitting still
#   3. The routine      -- home page first, then a few other pages, then scraping starts
#
# Random letters are only pressed, never submitted: Enter and other special keys are never used,
# and any focused text box is un-focused first, so no new search is ever started by accident.

# ---------------------------------------------------------------- 1. LINKS

LINKS_TO_AVOID_WHILE_BROWSING_PATTERN = re.compile(  # Pattern for links an ordinary visitor would not click while browsing
    r"log-?in|log-?out|sign-?in|sign-?out|register|cart|checkout|account"  # Login, logout, sign-in, registration, shopping and account pages
    r"|\.pdf|msds|/sds|mailto:|tel:|javascript:",  # Documents, e-mail, phone and script links
    re.IGNORECASE,  # Ignore capital letters
)  # End of the pattern
DESCRIBE_ALL_LINKS_SCRIPT = (  # JavaScript that describes every link on the page, in page order
    "() => Array.from(document.querySelectorAll('a[href]')).map((linkElement, linkIndex) => {"  # Go through every link and remember its position
    "const linkBox = linkElement.getBoundingClientRect();"  # Size and position of the link on screen
    "const linkStyle = getComputedStyle(linkElement);"  # How the link is displayed
    "return {"  # Start the description of this link
    "index: linkIndex,"  # Position of the link among all links
    "href: linkElement.href,"  # Full address of the link
    "visible: linkBox.width > 20 && linkBox.height > 10 && linkStyle.visibility !== 'hidden' && linkStyle.display !== 'none',"  # Is the link big enough and shown
    "new_tab: linkElement.target === '_blank',"  # Does the link open a new tab
    "download: linkElement.hasAttribute('download'),"  # Is it a download link
    "};"  # End of the description of this link
    "})"  # End of the loop over all links
)  # End of the script
REMOVE_KEYBOARD_FOCUS_FROM_TEXT_BOXES_SCRIPT = (  # JavaScript that takes the keyboard focus away from any text box
    "() => { const focusedElement = document.activeElement;"  # The element that currently has the keyboard focus
    " if (focusedElement && focusedElement !== document.body && (['INPUT', 'TEXTAREA', 'SELECT'].includes(focusedElement.tagName) || focusedElement.isContentEditable)) focusedElement.blur(); }"  # If it is a text box, take the focus away
)  # End of the script


def pick_random_internal_link(
    browser_page: Page, visited_urls: set
) -> Optional[tuple]:  # Choose a random visible Agilent link we have not used yet
    candidate_links = []  # Collects (position on the page, address) pairs
    for link_description in browser_page.evaluate(
        DESCRIBE_ALL_LINKS_SCRIPT
    ):  # Look at every link on the page
        link_url = link_description["href"]  # The full address of the link
        parsed_url = urlparse(link_url)  # Split the address into its parts
        website_host_name = (
            parsed_url.hostname or ""
        )  # The website name, empty if missing
        if (
            not link_description["visible"]
            or link_description["new_tab"]
            or link_description["download"]
        ):  # Hidden, popup or download link
            continue  # An ordinary visitor would not click it here
        if parsed_url.scheme not in ("http", "https"):  # Not a normal web address
            continue  # Skip it
        if website_host_name != "agilent.com" and not website_host_name.endswith(
            ".agilent.com"
        ):  # Not an Agilent page (look-alike domains are rejected)
            continue  # Stay on Agilent's own website
        if LINKS_TO_AVOID_WHILE_BROWSING_PATTERN.search(
            link_url
        ):  # Login, cart, PDF and similar links
            continue  # Skip it
        if (
            remove_fragment_from_url(link_url) in visited_urls
        ):  # Already visited, or it is the page we are on
            continue  # We want different pages
        candidate_links.append(
            (link_description["index"], link_url)
        )  # This link is a good candidate
    return (
        random.choice(candidate_links) if candidate_links else None
    )  # Pick one at random, if there is any


# ---------------------------------------------------------------- 2. HUMAN-LIKE INPUT

current_mouse_x = 200.0  # Where the pointer is horizontally (Playwright cannot tell us, so we remember it)
current_mouse_y = 200.0  # Where the pointer is vertically


def reset_mouse_position() -> None:  # Put the remembered pointer position back to its starting place
    global current_mouse_x, current_mouse_y  # We change the module-level position variables
    current_mouse_x, current_mouse_y = (
        200.0,
        200.0,
    )  # A fresh browser starts with the pointer here


def get_visible_page_size(
    browser_page: Page,
) -> tuple:  # Width and height of the visible page area
    visible_page_size = browser_page.viewport_size or {
        "width": BROWSER_WINDOW_WIDTH_PIXELS,
        "height": BROWSER_WINDOW_HEIGHT_PIXELS,
    }  # Fall back to full HD if the size is unknown
    return (
        visible_page_size["width"],
        visible_page_size["height"],
    )  # Give both numbers back


def move_mouse_like_a_human(
    browser_page: Page, pointer_target_x: float, pointer_target_y: float
) -> None:  # Move the pointer along a curved, slightly shaky path
    global current_mouse_x, current_mouse_y  # We update the remembered pointer position at the end
    visible_page_width, visible_page_height = get_visible_page_size(
        browser_page
    )  # Size of the page area
    pointer_target_x = min(
        max(pointer_target_x, 1), visible_page_width - 1
    )  # Keep the target inside the page horizontally
    pointer_target_y = min(
        max(pointer_target_y, 1), visible_page_height - 1
    )  # Keep the target inside the page vertically
    pointer_start_x, pointer_start_y = (
        current_mouse_x,
        current_mouse_y,
    )  # Where the pointer is now
    travel_distance = math.hypot(
        pointer_target_x - pointer_start_x, pointer_target_y - pointer_start_y
    )  # Straight-line distance to travel
    if travel_distance < 2:  # The pointer is already there
        return  # Nothing to do
    movement_step_count = max(
        12, min(60, int(travel_distance / 10))
    )  # Longer moves use more small steps
    curve_bend_amount = travel_distance * random.uniform(
        0.1, 0.3
    )  # How strongly the path curves
    control_point_x = (pointer_start_x + pointer_target_x) / 2 + random.choice(
        (-1, 1)
    ) * curve_bend_amount * random.random()  # Curve control point, pulled sideways
    control_point_y = (pointer_start_y + pointer_target_y) / 2 + random.choice(
        (-1, 1)
    ) * curve_bend_amount * random.random()  # Curve control point, pulled up or down
    for movement_step_number in range(
        1, movement_step_count + 1
    ):  # Walk along the curve step by step
        progress_fraction = (
            movement_step_number / movement_step_count
        )  # How far along the path we are, from 0 to 1
        eased_progress = (
            progress_fraction * progress_fraction * (3 - 2 * progress_fraction)
        )  # Start slowly, speed up in the middle, slow down at the end
        curve_point_x = (
            (1 - eased_progress) ** 2 * pointer_start_x
            + 2 * (1 - eased_progress) * eased_progress * control_point_x
            + eased_progress**2 * pointer_target_x
        )  # Horizontal position on the curve
        curve_point_y = (
            (1 - eased_progress) ** 2 * pointer_start_y
            + 2 * (1 - eased_progress) * eased_progress * control_point_y
            + eased_progress**2 * pointer_target_y
        )  # Vertical position on the curve
        if movement_step_number < movement_step_count:  # Every step except the last one
            curve_point_x += random.uniform(-1.0, 1.0)  # Tiny hand shake, horizontal
            curve_point_y += random.uniform(-1.0, 1.0)  # Tiny hand shake, vertical
        browser_page.mouse.move(
            curve_point_x, curve_point_y
        )  # Move the pointer to this point
        time.sleep(random.uniform(0.004, 0.014))  # Tiny pause between steps
    current_mouse_x, current_mouse_y = (
        pointer_target_x,
        pointer_target_y,
    )  # Remember where the pointer ended up


def click_element_like_a_human(
    browser_page: Page, target_element
) -> None:  # Move the pointer to an element like a person and click it
    target_element.scroll_into_view_if_needed(
        timeout=5000
    )  # Bring the element into view
    element_box = (
        target_element.bounding_box()
    )  # Position and size of the element on screen
    if element_box is None:  # The element has no size right now
        target_element.click(timeout=5000)  # Fall back to a normal click
        return  # Done
    click_position_x = element_box["x"] + element_box["width"] * random.uniform(
        0.3, 0.7
    )  # A spot inside the element, horizontally
    click_position_y = element_box["y"] + element_box["height"] * random.uniform(
        0.3, 0.7
    )  # A spot inside the element, vertically
    move_mouse_like_a_human(
        browser_page, click_position_x, click_position_y
    )  # Move the pointer there like a person
    time.sleep(random.uniform(0.2, 0.6))  # Hesitate briefly before clicking
    browser_page.mouse.click(
        current_mouse_x, current_mouse_y, delay=random.randint(50, 150)
    )  # Click, holding the button down for a moment


def scroll_like_a_human(
    browser_page: Page, scroll_pixels: int
) -> None:  # Scroll with the mouse wheel in small, uneven notches
    scroll_direction = (
        1 if scroll_pixels > 0 else -1
    )  # Down is positive, up is negative
    remaining_pixels = abs(scroll_pixels)  # How much is still left to scroll
    while remaining_pixels > 0:  # Keep scrolling until the distance is covered
        wheel_notch_pixels = min(
            remaining_pixels, random.randint(40, 120)
        )  # Size of this wheel notch
        browser_page.mouse.wheel(
            0, scroll_direction * wheel_notch_pixels
        )  # Turn the wheel a little
        remaining_pixels -= wheel_notch_pixels  # Count the notch off
        time.sleep(random.uniform(0.02, 0.09))  # Short pause between notches
        if random.random() < 0.08:  # Now and then
            time.sleep(random.uniform(0.3, 0.9))  # Stop for a moment as if reading


def press_random_letter_keys_like_a_human(
    browser_page: Page,
) -> None:  # Press a few random letter keys with human-like timing
    browser_page.evaluate(
        REMOVE_KEYBOARD_FOCUS_FROM_TEXT_BOXES_SCRIPT
    )  # No text box may have focus, so the letters cannot change a search box
    for _key_press_number in range(random.randint(2, 6)):  # Press a few keys
        random_letter = random.choice(
            string.ascii_lowercase
        )  # Pick a random letter a-z (never Enter or other special keys)
        browser_page.keyboard.press(
            random_letter, delay=random.randint(40, 140)
        )  # Press and release it, holding the key briefly
        time.sleep(random.uniform(0.08, 0.35))  # Typing rhythm between keys
        if random.random() < 0.15:  # Sometimes
            time.sleep(random.uniform(0.4, 1.0))  # Hesitate like someone thinking


def act_like_a_human_on_page(
    browser_page: Page, duration_seconds: float
) -> None:  # Move the mouse, scroll and press random letters for a while
    activity_end_time = time.time() + duration_seconds  # The moment when we stop
    visible_page_width, visible_page_height = get_visible_page_size(
        browser_page
    )  # Size of the page area
    while time.time() < activity_end_time:  # Keep going until the time is up
        try:  # Browser actions can fail while the page is changing
            random_action_choice = random.random()  # Pick what to do next
            if random_action_choice < 0.2:  # Sometimes
                press_random_letter_keys_like_a_human(
                    browser_page
                )  # Press a few random letters
            elif random_action_choice < 0.55:  # Most often the visitor reads the page
                scroll_like_a_human(
                    browser_page, random.randint(200, 650)
                )  # Scroll down
            elif (
                random_action_choice < 0.9
            ):  # Often the visitor moves the mouse somewhere else
                move_mouse_like_a_human(
                    browser_page,
                    random.uniform(40, visible_page_width - 40),
                    random.uniform(40, visible_page_height - 40),
                )  # Move to a random spot
            else:  # Occasionally the visitor looks back up
                scroll_like_a_human(
                    browser_page, -random.randint(100, 300)
                )  # Scroll up a little
        except PlaywrightError as browser_error:  # The action did not work
            if is_browser_closed_error(browser_error):  # The browser itself is gone
                raise  # Let the caller deal with it
        remaining_seconds = activity_end_time - time.time()  # Time left
        if remaining_seconds > 0:  # There is still time to spend
            time.sleep(
                min(remaining_seconds, random.uniform(0.5, 2.0))
            )  # Pause like a person between actions


def pause_while_acting_like_a_human(
    browser_page: Page,
    minimum_seconds: float,
    maximum_seconds: float,
    pause_reason: str,
) -> None:  # Wait a random time while still looking active
    pause_seconds = random.uniform(
        minimum_seconds, maximum_seconds
    )  # Pick a random length inside the range
    download_logger.debug(
        "Pausing %.1f seconds with mouse and keyboard activity (%s)",
        pause_seconds,
        pause_reason,
    )  # Record the pause and why it happens
    try:  # The browser can fail while we act
        act_like_a_human_on_page(
            browser_page, pause_seconds
        )  # Move the mouse, scroll and press random letters
    except (
        PlaywrightError,
        PlaywrightTimeoutError,
    ) as browser_error:  # The browser had a problem
        download_logger.debug(
            "Activity during the pause failed: %s", str(browser_error).splitlines()[0]
        )  # Record the problem
        time.sleep(
            pause_seconds
        )  # Simply wait instead; the next step deals with the browser


# ---------------------------------------------------------------- 3. THE BROWSING ROUTINE


def open_random_link(
    browser_page: Page, visited_urls: set
) -> Optional[str]:  # Click a random link and return the address of the page it opens
    for _attempt_number in range(
        5
    ):  # Try a few different links in case one does not work
        chosen_candidate = pick_random_internal_link(
            browser_page, visited_urls
        )  # Choose a link
        if chosen_candidate is None:  # There is no suitable link on this page
            return None  # Give up
        (
            link_position,
            link_url,
        ) = chosen_candidate  # Position and address of the chosen link
        visited_urls.add(
            remove_fragment_from_url(link_url)
        )  # Never choose this one again
        page_url_before_click = remove_fragment_from_url(
            browser_page.url
        )  # Where we are right now
        try:  # Clicking can fail
            chosen_link = browser_page.locator("a[href]").nth(
                link_position
            )  # Find the link by its position on the page
            click_element_like_a_human(
                browser_page, chosen_link
            )  # Move the pointer to it like a person and click it
            browser_page.wait_for_url(lambda new_page_url, previous_page_url=page_url_before_click: remove_fragment_from_url(str(new_page_url)) != previous_page_url, wait_until="domcontentloaded", timeout=8000)  # type: ignore[misc]  # Wait until we really arrived on another page
        except (
            PlaywrightError,
            PlaywrightTimeoutError,
        ) as browser_error:  # The click did not lead anywhere
            if is_browser_closed_error(browser_error):  # The browser itself is gone
                raise  # Stop browsing
            download_logger.debug(
                "Browsing: link %s did not open a page", link_url
            )  # Record it
            continue  # Try another link
        return browser_page.url  # We are now on a new page
    return None  # None of the links worked


def return_to_home_page(
    browser_page: Page, home_page_url: str
) -> None:  # Go back to the home page like a person would
    try:  # Going back can fail
        browser_page.go_back(
            wait_until="domcontentloaded", timeout=15_000
        )  # Press the back button
    except (
        PlaywrightError,
        PlaywrightTimeoutError,
    ) as browser_error:  # Going back did not work
        if is_browser_closed_error(browser_error):  # The browser itself is gone
            raise  # Stop browsing
    if remove_fragment_from_url(browser_page.url) != remove_fragment_from_url(
        home_page_url
    ):  # We are not on the home page
        browser_page.goto(
            home_page_url, wait_until="domcontentloaded"
        )  # Open it directly instead
    time.sleep(random.uniform(1.0, 2.0))  # Let the home page draw itself


def browse_like_a_normal_visitor(
    browser_page: Page,
) -> None:  # Move around the home page, then open a few different pages from it
    try:  # Any browser problem just ends the browsing early
        home_page_url = browser_page.url  # The page we start from and keep returning to
        visited_urls = {
            remove_fragment_from_url(home_page_url),
            remove_fragment_from_url(HOME_PAGE_URL),
        }  # Pages that count as already seen
        download_logger.info(
            "Browsing: mouse, scrolling and random keys on the home page for about %d seconds",
            HOME_PAGE_BROWSING_SECONDS,
        )  # Record the first step
        act_like_a_human_on_page(
            browser_page, HOME_PAGE_BROWSING_SECONDS
        )  # Home page: mouse, scrolling and random letters
        for visit_number in range(
            1, OTHER_PAGES_TO_VISIT + 1
        ):  # Open the other pages one by one
            visit_start_time = time.time()  # When this visit began
            opened_page_url = open_random_link(
                browser_page, visited_urls
            )  # Click a random link on the home page
            if opened_page_url is None:  # No link worked
                download_logger.warning(
                    "Browsing: could not open another page, stopping early"
                )  # Record it
                break  # Stop browsing
            download_logger.info(
                "Browsing: page %d/%d opened (about %d seconds on it): %s",
                visit_number,
                OTHER_PAGES_TO_VISIT,
                OTHER_PAGE_BROWSING_SECONDS,
                opened_page_url,
            )  # Record the visit
            seconds_left_on_page = max(
                2.0, OTHER_PAGE_BROWSING_SECONDS - (time.time() - visit_start_time)
            )  # The rest of this visit's time
            act_like_a_human_on_page(
                browser_page, seconds_left_on_page
            )  # Other pages: mouse, scrolling and random letters
            if visit_number < OTHER_PAGES_TO_VISIT:  # Another visit follows
                return_to_home_page(
                    browser_page, home_page_url
                )  # Go back to the home page first
    except (
        PlaywrightError,
        PlaywrightTimeoutError,
    ) as browser_error:  # Something went wrong in the browser
        download_logger.warning(
            "Browsing like a normal visitor ended early: %s",
            str(browser_error).splitlines()[0],
        )  # Record it; scraping goes on anyway
        return  # Leave the function
    download_logger.info("Finished browsing like a normal visitor")  # Record the end


def warm_up_session_on_home_page(
    browser_page: Page,
) -> bool:  # Open the home page and browse around a little first
    download_logger.info(
        "Warm-up: opening the home page %s", HOME_PAGE_URL
    )  # Record the first step
    try:  # Opening the page can fail
        browser_page.goto(
            HOME_PAGE_URL, wait_until="domcontentloaded"
        )  # Open the home page
    except PlaywrightError as browser_error:  # The page could not be opened
        download_logger.error(
            "Warm-up: could not open the home page: %s", browser_error
        )  # Record the error
        return False  # The warm-up failed
    wait_for_network_to_settle(browser_page)  # Let the home page finish loading
    dismiss_cookie_banner(browser_page)  # Accept the cookie popup like a normal visitor
    if is_access_denied_error_page(
        browser_page
    ):  # Check whether even the home page is blocked
        download_logger.error(
            "Warm-up: the home page itself shows Access Denied"
        )  # Record the problem
        return False  # The warm-up failed
    browse_like_a_normal_visitor(
        browser_page
    )  # Move around the home page and open a few other pages
    return True  # The warm-up worked


PAGE_STATUS_OPENED = "opened"  # The page opened normally
PAGE_STATUS_UNAVAILABLE = (
    "unavailable"  # The page shows the "page may no longer exist" message
)
PAGE_STATUS_BLOCKED = "blocked"  # The page kept showing "Access Denied"
PAGE_STATUS_FAILED = "failed"  # The page could not be opened at all


def open_page_politely(
    browser_page: Page, page_url: str, run_statistics: RunStatistics
) -> str:  # Open a page, backing off if the website blocks us
    """Open a page; if blocked, wait, visit the home page again, and retry a limited number of times."""  # Short description
    for attempt_number in range(
        1, MAXIMUM_ACCESS_DENIED_ATTEMPTS + 1
    ):  # Try a limited number of times
        download_logger.info(
            "Opening %s (attempt %d/%d)",
            page_url,
            attempt_number,
            MAXIMUM_ACCESS_DENIED_ATTEMPTS,
        )  # Record the attempt
        try:  # Opening the page can fail
            browser_page.goto(page_url, wait_until="domcontentloaded")  # Open the page
        except PlaywrightError as browser_error:  # The page could not be opened
            if is_browser_closed_error(browser_error):  # The browser itself is gone
                raise  # Let the restart logic start a new browser and retry this keyword
            download_logger.error(
                "Could not open %s: %s", page_url, browser_error
            )  # Record the error
            return PAGE_STATUS_FAILED  # Give up on this page
        wait_for_network_to_settle(browser_page)  # Wait for the page to finish loading
        if is_page_unavailable_error_page(
            browser_page
        ):  # Check for the "page may no longer exist" message
            return PAGE_STATUS_UNAVAILABLE  # Skip this page, retrying will not help
        if not is_access_denied_error_page(
            browser_page
        ):  # Check whether the website let us in
            reset_access_blocks(
                run_statistics
            )  # The blocks-in-a-row count starts again
            return PAGE_STATUS_OPENED  # The page opened normally
        register_access_block(
            run_statistics
        )  # Count the block, which may stop the whole run
        if (
            attempt_number < MAXIMUM_ACCESS_DENIED_ATTEMPTS
        ):  # Another attempt is still allowed
            backoff_seconds = ACCESS_DENIED_BACKOFF_SECONDS * (
                2 ** (attempt_number - 1)
            ) + random.uniform(
                0, 5
            )  # Wait longer after every block
            download_logger.info(
                "Backing off for %.0f seconds, then revisiting the home page",
                backoff_seconds,
            )  # Explain the wait
            time.sleep(backoff_seconds)  # Wait before trying again
            warm_up_session_on_home_page(
                browser_page
            )  # Visit the home page again to refresh the session
    download_logger.error(
        "Still blocked after %d attempt(s): %s",
        MAXIMUM_ACCESS_DENIED_ATTEMPTS,
        page_url,
    )  # Record the failure
    return PAGE_STATUS_BLOCKED  # The page could not be opened


# ============================================================== DOWNLOADING

DOWNLOAD_OUTCOME_STARTED = "download started"  # The browser started downloading a file
DOWNLOAD_OUTCOME_PAGE_UNAVAILABLE = (
    "page unavailable"  # The link led to the "page may no longer exist" message
)
DOWNLOAD_OUTCOME_ACCESS_DENIED = (
    "access denied"  # The link led to the "Access Denied" page
)
DOWNLOAD_OUTCOME_NOT_A_DOWNLOAD = (
    "not a download"  # The link led to an ordinary web page instead of a file
)
DOWNLOAD_OUTCOME_TIMED_OUT = "timeout"  # Nothing happened before the time limit


def start_browser_download(
    browser_page: Page, source_url: str
) -> tuple:  # Ask the browser to download one URL
    """Open a URL and wait for the browser to report a download, or work out what else happened."""  # Short description
    first_started_download = None  # Will hold the first download the browser reports

    def remember_first_download(
        started_download: Download,
    ) -> None:  # Called by the browser whenever a download starts
        nonlocal first_started_download  # We change the variable that belongs to the outer function
        if first_started_download is None:  # Only the first download matters
            first_started_download = started_download  # Remember it

    browser_page.on(
        "download", remember_first_download
    )  # Start listening for downloads on this tab
    try:  # Make sure the listener is always removed again
        try:  # Opening a download link raises an error, which is normal
            navigation_response = browser_page.goto(
                source_url, wait_until="commit", timeout=PAGE_LOAD_TIMEOUT_MILLISECONDS
            )  # Open the link
        except PlaywrightError as navigation_error:  # The browser reported an error for the navigation
            if "Download is starting" in str(
                navigation_error
            ) or "NS_BINDING_ABORTED" in str(
                navigation_error
            ):  # Expected when the link turns into a download
                navigation_response = (
                    None  # The navigation became a download straight away
                )
            else:  # Some other, real error
                raise  # Let the calling code handle it

        if (
            navigation_response is not None
            and "text/html"
            in navigation_response.headers.get("content-type", "").lower()
        ):  # The server answered with a web page
            try:  # Waiting for the page can time out
                browser_page.wait_for_load_state(
                    "domcontentloaded", timeout=15_000
                )  # Let the page finish loading
            except PlaywrightTimeoutError:  # The page took too long
                pass  # Continue with whatever has loaded
            if is_page_unavailable_error_page(
                browser_page
            ):  # Check for the "page may no longer exist" message
                return (
                    None,
                    DOWNLOAD_OUTCOME_PAGE_UNAVAILABLE,
                )  # No PDF exists at this address
            if is_access_denied_error_page(
                browser_page
            ):  # Check for the "Access Denied" page
                return (
                    None,
                    DOWNLOAD_OUTCOME_ACCESS_DENIED,
                )  # The website blocked this request
            return (
                None,
                DOWNLOAD_OUTCOME_NOT_A_DOWNLOAD,
            )  # Some other web page, not a file

        download_wait_deadline = (
            time.time() + DOWNLOAD_START_TIMEOUT_MILLISECONDS / 1000
        )  # The moment when we give up waiting
        while (
            first_started_download is None and time.time() < download_wait_deadline
        ):  # Wait for the browser to report the download
            browser_page.wait_for_timeout(
                200
            )  # Wait a moment while Playwright processes browser events
        if first_started_download is not None:  # The browser reported a download
            return first_started_download, DOWNLOAD_OUTCOME_STARTED  # Hand it back
        return None, DOWNLOAD_OUTCOME_TIMED_OUT  # Nothing happened in time
    finally:  # Always runs, even after an error
        browser_page.remove_listener(
            "download", remember_first_download
        )  # Stop listening for downloads


URL_RESULT_SAVED = "saved"  # The file was downloaded and saved
URL_RESULT_FILE_ALREADY_EXISTS = (
    "file already exists"  # A file with this name was already saved
)
URL_RESULT_VERSION_NOT_AVAILABLE = "version not available"  # This version does not exist, so the next best version may be tried
URL_RESULT_TRY_AGAIN_LATER = "try again later"  # A temporary problem; no lower-priority version may be used instead


def mark_versions_as_skipped(
    download_database: DownloadDatabase,
    version_urls: list,
    run_statistics: RunStatistics,
    reason_text: str,
) -> None:  # Mark versions as finished without downloading them
    for version_url in version_urls:  # Go through each version
        download_logger.info(
            "  SKIP: %s: %s", reason_text, version_url
        )  # Explain the skip
        download_database.mark_url_processed(
            version_url
        )  # Never try this version again
        run_statistics.skipped_count += 1  # Count the skip


def skip_documents_already_in_download_folder(
    download_database: DownloadDatabase, found_urls: set, run_statistics: RunStatistics
) -> set:  # Drop every document that already has a file, before anything is requested
    """Check the download folder first: documents that already have a file are marked as finished and never requested."""  # Short description
    urls_still_needed: set[
        str
    ] = set()  # Collects the addresses of documents that have no file yet
    for document_key, version_urls in group_urls_by_document(
        found_urls
    ).items():  # Look at one document at a time
        if download_database.is_any_version_of_document_saved(
            document_key
        ):  # The download folder (or the database) already has a file for it
            mark_versions_as_skipped(
                download_database,
                version_urls,
                run_statistics,
                "this document already has a file in the download folder",
            )  # Skip every version of it
        else:  # No file yet
            urls_still_needed.update(version_urls)  # Keep it for the download steps
    return urls_still_needed  # Give back only what still needs work


def download_single_url(
    download_page: Page,
    download_database: DownloadDatabase,
    source_url: str,
    run_statistics: RunStatistics,
    internet_monitor: "InternetMonitor",
) -> str:  # Download one version and say what happened
    try:  # Starting a download can raise browser errors
        started_download, download_outcome = start_browser_download(
            download_page, source_url
        )  # Let the browser download the file
    except PlaywrightError as browser_error:  # A real browser error happened
        if is_browser_closed_error(
            browser_error
        ):  # Check whether the browser itself has closed
            raise  # Let the restart logic deal with it; this URL stays pending
        if (
            internet_monitor.confirm_internet_is_down()
        ):  # Check whether a lost internet connection caused the error
            raise InternetOutageError(
                "The internet went down while downloading"
            ) from browser_error  # Wait for it; this URL stays pending
        download_logger.error(
            "  FAILED to open %s: %s", source_url, str(browser_error).splitlines()[0]
        )  # Record the failure
        run_statistics.failed_count += 1  # Count the failure
        return URL_RESULT_TRY_AGAIN_LATER  # A temporary problem

    if (
        download_outcome == DOWNLOAD_OUTCOME_PAGE_UNAVAILABLE
    ):  # The link led to the "page may no longer exist" message
        download_logger.warning(
            "  SKIP: page unavailable, no PDF at %s", source_url
        )  # Explain the skip
        download_database.mark_url_processed(source_url)  # Never try this URL again
        run_statistics.unavailable_count += 1  # Count it as unavailable
        reset_access_blocks(
            run_statistics
        )  # The website answered normally, so the blocks-in-a-row count starts again
        return URL_RESULT_VERSION_NOT_AVAILABLE  # This version does not exist
    if (
        download_outcome == DOWNLOAD_OUTCOME_ACCESS_DENIED
    ):  # The website blocked this request
        download_logger.error(
            "  FAILED: access denied for %s", source_url
        )  # Record the failure
        run_statistics.failed_count += 1  # Count the failure
        register_access_block(
            run_statistics
        )  # Count the block, which may stop the whole run
        return URL_RESULT_TRY_AGAIN_LATER  # A temporary problem
    if (
        download_outcome == DOWNLOAD_OUTCOME_NOT_A_DOWNLOAD
    ):  # The link is an ordinary web page, not a PDF
        download_logger.warning(
            "  SKIP: the link is a web page, not a PDF: %s", source_url
        )  # Explain the skip
        download_database.mark_url_processed(source_url)  # Never try this URL again
        run_statistics.skipped_count += 1  # Count it as skipped
        reset_access_blocks(
            run_statistics
        )  # The website answered normally, so the blocks-in-a-row count starts again
        return URL_RESULT_VERSION_NOT_AVAILABLE  # This version is not a real file
    if started_download is None:  # The browser never produced a download
        if (
            internet_monitor.confirm_internet_is_down()
        ):  # Check whether a lost internet connection is the reason
            raise InternetOutageError(
                "The internet went down while downloading"
            )  # Wait for it; this URL stays pending
        download_logger.error(
            "  FAILED: no download (%s) for %s", download_outcome, source_url
        )  # Record the failure
        run_statistics.failed_count += 1  # Count the failure
        return URL_RESULT_TRY_AGAIN_LATER  # A temporary problem
    reset_access_blocks(
        run_statistics
    )  # A download started, so the blocks-in-a-row count starts again

    return check_and_save_finished_download(
        started_download, source_url, download_database, run_statistics
    )  # Check, name and save the finished download


def download_best_version_of_each_document(
    download_page: Page,
    download_database: DownloadDatabase,
    documents_to_download: dict,
    run_statistics: RunStatistics,
    internet_monitor: "InternetMonitor",
    page_for_mouse_activity: Page,
) -> None:  # Download exactly one version per document
    """Try the versions of each document best first, stop at the first one that is saved, skip all the others."""  # Short description
    already_contacted_website = (
        False  # Tracks whether we already contacted the website in this batch
    )
    for document_position, (document_key, candidate_urls) in enumerate(
        documents_to_download.items(), start=1
    ):  # Handle one document at a time
        download_logger.info(
            "(%d/%d) Document '%s' has %d version(s) to try, best first",
            document_position,
            len(documents_to_download),
            document_key,
            len(candidate_urls),
        )  # Record the progress
        for version_position, source_url in enumerate(
            candidate_urls
        ):  # Try the versions from best to worst
            internet_monitor.raise_error_if_internet_is_down()  # Stop here and wait if the internet is down
            lower_priority_urls = candidate_urls[
                version_position + 1 :
            ]  # The versions that are worse than this one
            download_logger.info(
                "  Trying version %d of %d: %s",
                version_position + 1,
                len(candidate_urls),
                source_url,
            )  # Record the attempt

            if download_database.is_file_for_url_already_downloaded(
                source_url
            ):  # The file for this version already exists
                download_logger.info(
                    "  SKIP: the file for this URL already exists"
                )  # Explain the skip
                download_database.mark_url_processed(
                    source_url
                )  # Remember that this URL is finished
                run_statistics.skipped_count += 1  # Count the skip
                url_result = URL_RESULT_FILE_ALREADY_EXISTS  # The document is covered
            else:  # The file still has to be downloaded
                if already_contacted_website:  # Only pause between two real requests
                    page_for_mouse_activity.bring_to_front()  # Show the results tab, because a hidden tab would look odd to the website
                    pause_while_acting_like_a_human(
                        page_for_mouse_activity,
                        *PAUSE_SECONDS_RANGE_BETWEEN_DOWNLOADS,
                        "between downloads",
                    )  # Move the mouse and scroll instead of sitting still
                already_contacted_website = (
                    True  # From now on we have contacted the website
                )
                url_result = download_single_url(
                    download_page,
                    download_database,
                    source_url,
                    run_statistics,
                    internet_monitor,
                )  # Download this version

            if url_result in (
                URL_RESULT_SAVED,
                URL_RESULT_FILE_ALREADY_EXISTS,
            ):  # The document now has its file
                mark_versions_as_skipped(
                    download_database,
                    lower_priority_urls,
                    run_statistics,
                    "a better version of this document is already saved",
                )  # Never download the other versions
                break  # Go on with the next document
            if (
                url_result == URL_RESULT_TRY_AGAIN_LATER
            ):  # A temporary problem with the best remaining version
                download_logger.warning(
                    "  This version will be retried later, so no lower-priority version is downloaded now"
                )  # Explain why we stop here
                break  # Leave the other versions pending and go on with the next document
            if (
                lower_priority_urls
            ):  # This version does not exist and there are others to try
                download_logger.info(
                    "  This version is not available, trying the next best version"
                )  # Explain what happens next
            else:  # That was the last version
                download_logger.warning(
                    "  No wanted version of this document could be downloaded, skipping it"
                )  # Explain that the document is skipped

    log_run_statistics(
        run_statistics, "Totals so far"
    )  # Show the totals after this batch


def check_and_save_finished_download(
    started_download: Download,
    source_url: str,
    download_database: DownloadDatabase,
    run_statistics: RunStatistics,
) -> str:  # Check and save a completed download
    """Check that the file is a real PDF, give it a clean name, skip duplicates, and save it."""  # Short description
    suggested_file_name = (
        started_download.suggested_filename
    )  # The file name the browser would have used
    download_failure = (
        started_download.failure()
    )  # Wait for the download to end and get any error
    if download_failure:  # The browser reported that the download failed
        download_logger.error(
            "  FAILED: browser download error '%s' for %s", download_failure, source_url
        )  # Record the failure
        run_statistics.failed_count += 1  # Count the failure
        return URL_RESULT_TRY_AGAIN_LATER  # A temporary problem

    with open(
        started_download.path(), "rb"
    ) as downloaded_file_handle:  # Open the downloaded file for reading
        file_start_bytes = downloaded_file_handle.read(4)  # Read its first four bytes
    if file_start_bytes != b"%PDF":  # Real PDF files always start with %PDF
        download_logger.error(
            "  FAILED: downloaded file is not a PDF, treating this version as unavailable: %s",
            source_url,
        )  # Record the problem
        started_download.delete()  # Throw the file away
        download_database.mark_url_processed(
            source_url
        )  # A broken file will not fix itself, so stop retrying it
        run_statistics.failed_count += 1  # Count the failure
        return URL_RESULT_VERSION_NOT_AVAILABLE  # The next best version may be tried

    safe_file_name = build_safe_file_name(
        suggested_file_name
    )  # Apply the naming rules to the real name
    safe_file_path = (
        DOWNLOAD_FOLDER / safe_file_name
    )  # Full path where the PDF will be saved
    if download_database.is_file_name_already_saved(
        safe_file_name
    ):  # Check whether this file name is already in the download folder or the database
        download_logger.info(
            "  DUPLICATE file name, not saved: %s", safe_file_name
        )  # Explain what happens
        started_download.delete()  # Discard the extra copy
        download_database.mark_url_processed(
            source_url
        )  # Remember that this URL is finished
        run_statistics.skipped_count += 1  # Count it as skipped
        return URL_RESULT_FILE_ALREADY_EXISTS  # The document already has its file

    started_download.save_as(safe_file_path)  # Save the PDF into the PDFs folder
    download_database.record_saved_file(
        safe_file_name, source_url
    )  # Write the file name into the database
    download_database.mark_url_processed(
        source_url
    )  # Remember that this URL is finished
    run_statistics.downloaded_count += 1  # Count the success
    download_logger.info(
        "  SAVED: %s (%d bytes)", safe_file_path, safe_file_path.stat().st_size
    )  # Record the result
    return URL_RESULT_SAVED  # The document now has its file


def keep_only_documents_with_default_version(
    urls_grouped_by_document: dict,
) -> dict:  # Keep the documents whose best pending version is the default one
    return {
        document_key: [candidate_urls[0]]
        for document_key, candidate_urls in urls_grouped_by_document.items()
        if candidate_urls and get_version_rank_from_url(candidate_urls[0]) == 0
    }  # Only the default version is kept for each of them


def select_documents_with_default_version(
    download_database: DownloadDatabase, found_urls: set
) -> dict:  # Documents that can be downloaded right away because their default version was found
    pending_urls = download_database.keep_only_unprocessed_urls(
        sorted(found_urls)
    )  # Leave out versions that are already finished
    return keep_only_documents_with_default_version(
        group_urls_by_document(pending_urls)
    )  # Only documents with a pending default version


def select_documents_for_final_download(
    download_database: DownloadDatabase, some_keywords_were_not_searched: bool
) -> dict:  # Everything that is still waiting once all keywords are searched
    urls_grouped_by_document = group_urls_by_document(
        download_database.load_unprocessed_urls()
    )  # Every document that still has a pending version
    if (
        some_keywords_were_not_searched
    ):  # A better version might be hiding in a keyword that was never searched
        download_logger.warning(
            "Some keywords were not searched, so only default versions are downloaded now; fallback versions wait for the next run"
        )  # Explain the limit
        urls_grouped_by_document = keep_only_documents_with_default_version(
            urls_grouped_by_document
        )  # Never download a fallback version too early
    return urls_grouped_by_document  # Give the documents back


def download_documents_using_temporary_tab(
    browser_session: "BrowserSession",
    download_database: DownloadDatabase,
    documents_to_download: dict,
    run_statistics: RunStatistics,
) -> None:  # Download, opening a second tab only when needed
    """Skip documents that already have a file, then open the download tab only if something is left to do."""  # Short description
    documents_still_needed = {}  # Collects the documents that really have no file yet
    for (
        document_key,
        candidate_urls,
    ) in documents_to_download.items():  # Check each document before opening any tab
        if download_database.is_any_version_of_document_saved(
            document_key
        ):  # One version is already saved
            mark_versions_as_skipped(
                download_database,
                candidate_urls,
                run_statistics,
                "this document already has a saved version",
            )  # Never download another version
        else:  # The document still needs a file
            documents_still_needed[
                document_key
            ] = candidate_urls  # Keep it for downloading
    if not documents_still_needed:  # Check whether anything is left to download
        download_logger.info(
            "Nothing to download in this batch, so no second tab is opened"
        )  # Record the decision
        return  # Leave without opening a tab
    browser_session.internet_monitor.raise_error_if_internet_is_down()  # Do not open a tab while the internet is down
    with browser_session.temporary_download_tab() as download_page:  # Open the second tab and close it afterwards
        download_best_version_of_each_document(
            download_page,
            download_database,
            documents_still_needed,
            run_statistics,
            browser_session.internet_monitor,
            browser_session.active_results_page,
        )  # Download one version of each document


# ============================================================== SCRAPING (JOB 1: KEYWORD SEARCH)


def search_one_keyword_and_download_pdfs(
    browser_session: "BrowserSession",
    download_database: DownloadDatabase,
    search_keyword: str,
    run_statistics: RunStatistics,
) -> bool:  # Search one keyword; returns True when it was searched
    results_page = (
        browser_session.active_results_page
    )  # The tab used for browsing the search results
    browser_session.close_unneeded_tabs()  # Start every keyword with only the results tab open
    browser_session.internet_monitor.raise_error_if_internet_is_down()  # Wait for the internet before opening the search page
    search_url = SEARCH_URL_TEMPLATE.format(
        search_keyword=search_keyword
    )  # Build the search address
    download_logger.info(
        "Opening search page for keyword '%s': %s", search_keyword, search_url
    )  # Record what we are about to open

    page_status = open_page_politely(
        results_page, search_url, run_statistics
    )  # Open the page, backing off if blocked
    if (
        page_status == PAGE_STATUS_FAILED
        and browser_session.internet_monitor.confirm_internet_is_down()
    ):  # The page failed because the internet is down
        raise InternetOutageError(
            "The internet went down while opening the search page"
        )  # Wait for it, then retry
    if page_status != PAGE_STATUS_OPENED:  # Check whether the page opened normally
        download_logger.warning(
            "[%s] skipping this keyword for now (page status: %s)",
            search_keyword,
            page_status,
        )  # Explain the skip
        return False  # Nothing was collected; the keyword will be retried at the end
    dismiss_cookie_banner(results_page)  # Close the cookie popup if it is present
    pause_while_acting_like_a_human(
        results_page,
        *ACTIVITY_SECONDS_RANGE_AFTER_OPENING_SEARCH_PAGE,
        "after opening the search page",
    )  # Move the mouse and scroll before reading the results

    all_keyword_urls: set[
        str
    ] = set()  # Collects the URLs from every result page of this keyword
    for page_number in range(
        1, MAXIMUM_RESULT_PAGES_PER_KEYWORD + 1
    ):  # Walk through the result pages
        browser_session.close_unneeded_tabs()  # Close any tab other than the results and download tabs
        browser_session.internet_monitor.raise_error_if_internet_is_down()  # Stop here and wait if the internet is down
        results_page.bring_to_front()  # Keep the results tab in front
        if page_number > 1:  # A next result page has just opened
            pause_while_acting_like_a_human(
                results_page,
                *ACTIVITY_SECONDS_RANGE_AFTER_OPENING_SEARCH_PAGE,
                "after opening a result page",
            )  # Move the mouse and scroll before reading the results
        scroll_to_bottom_of_page(
            results_page
        )  # Make sure every result on this page has loaded

        urls_on_this_page = extract_pdf_urls_from_page(
            results_page
        )  # Read the PDF addresses from this page
        new_urls = (
            urls_on_this_page - all_keyword_urls
        )  # Work out which ones we have not seen for this keyword
        all_keyword_urls |= (
            urls_on_this_page  # Add this page's addresses to the keyword total
        )
        download_logger.info(
            "[%s] page %d: %d link(s), %d new, %d total",
            search_keyword,
            page_number,
            len(urls_on_this_page),
            len(new_urls),
            len(all_keyword_urls),
        )  # Show progress

        if new_urls:  # Only touch the database when there is something new
            download_database.save_newly_found_urls(
                new_urls
            )  # Store the new addresses in the database
            urls_without_files = skip_documents_already_in_download_folder(
                download_database, new_urls, run_statistics
            )  # Check the download folder first and skip documents that already have a file
            default_version_documents = select_documents_with_default_version(
                download_database, urls_without_files
            )  # Documents whose default version is on this page and that have no file yet
            download_logger.info(
                "[%s] page %d: downloading %d default version(s) right away; fallback versions wait until every keyword is searched",
                search_keyword,
                page_number,
                len(default_version_documents),
            )  # Say what happens next
            download_documents_using_temporary_tab(
                browser_session,
                download_database,
                default_version_documents,
                run_statistics,
            )  # Download them now

        if page_number > 1 and not new_urls:  # Check whether paging gave us nothing new
            download_logger.info(
                "[%s] no new links on this page, stopping", search_keyword
            )  # Explain why we stop
            break  # Stop, because we are probably seeing the same page again

        pause_while_acting_like_a_human(
            results_page,
            *PAUSE_SECONDS_RANGE_BETWEEN_RESULT_PAGES,
            "before the next result page",
        )  # Move the mouse and scroll instead of sitting still
        results_page.bring_to_front()  # Return to the results tab before looking for the next page button
        if not click_next_page_button(results_page):  # Try to go to the next page
            break  # There is no next page, so this keyword is finished
        wait_for_network_to_settle(
            results_page
        )  # Wait for the next page of results to load
        if not is_results_page_usable(
            results_page, run_statistics
        ):  # Check for the error page or "Access Denied"
            download_logger.warning(
                "[%s] the next result page is not usable, moving on", search_keyword
            )  # Explain the skip
            break  # Skip the rest of this keyword and go to the next one

    download_logger.info(
        "[%s] finished with %d PDF link(s)", search_keyword, len(all_keyword_urls)
    )  # Summarise the keyword
    del all_keyword_urls  # Release the memory held by this keyword's address set
    browser_session.close_unneeded_tabs()  # The keyword is done, so close anything that is not needed
    return True  # The keyword was searched


# ============================================================== SCRAPING (JOB 2: US ENGLISH SDS PAGE)
#
# The page https://www.agilent.com/en/search/safety-data-sheets shows 10 cards per page. Every card has
#   <a class="pub-ext" href="/library/msds/....pdf">  and a tag line such as  <span class="meta-text">English - United States</span>
# Only the cards tagged "English - United States" are downloaded. Then the "next" button of the
# pagination bar is clicked, and the same is repeated on the following page.

READ_SDS_CARDS_SCRIPT = (  # JavaScript that describes every card in the safety data sheet results tab
    "(scopeSelector) => {"  # The argument is the CSS selector of the results tab
    "const scope = document.querySelector(scopeSelector);"  # Find the results tab
    "if (!scope) return [];"  # No tab means no cards
    "return Array.from(scope.querySelectorAll('.compendiumcard')).map(card => {"  # Go through every card
    "const link = card.querySelector('a.pub-ext');"  # The link to the PDF
    "const labels = Array.from(card.querySelectorAll('.meta-text')).map(tag => tag.innerText.trim());"  # The tags: date, file type, language
    "return {href: link ? link.href : null, labels: labels};"  # Give back the address and the tags
    "});"  # End of the loop over cards
    "}"  # End of the function
)  # End of the script


def read_sds_cards(
    browser_page: Page,
) -> list:  # Read every card of the current result page
    card_descriptions = browser_page.evaluate(
        READ_SDS_CARDS_SCRIPT, SDS_RESULTS_SCOPE_SELECTOR
    )  # Ask the page for its cards
    return [
        card_description
        for card_description in card_descriptions
        if card_description.get("href")
    ]  # Ignore cards without a link


def get_us_english_urls_from_cards(
    card_descriptions: list,
) -> set:  # Keep only the cards tagged "English - United States"
    us_english_urls = {
        card_description["href"]
        for card_description in card_descriptions
        if US_ENGLISH_LABEL in card_description["labels"]
        and urlparse(card_description["href"]).path.lower().endswith(".pdf")
    }  # Only real PDF links with the right language tag
    return us_english_urls  # Give the addresses back


def wait_for_sds_cards_to_appear(
    browser_page: Page, timeout_seconds: float
) -> bool:  # Wait until at least one card is on the page
    wait_deadline = time.time() + timeout_seconds  # The moment when we give up
    while time.time() < wait_deadline:  # Keep checking until the time is up
        try:  # Reading can fail while the page is changing
            if read_sds_cards(browser_page):  # There are cards
                return True  # Done
        except PlaywrightError as browser_error:  # The read did not work
            if is_browser_closed_error(browser_error):  # The browser itself is gone
                raise  # Let the restart logic deal with it
        time.sleep(0.5)  # Wait a moment and look again
    return False  # No cards appeared in time


def wait_for_sds_cards_to_change(
    browser_page: Page, previous_links: tuple
) -> bool:  # Wait until the page shows different cards than before
    wait_deadline = (
        time.time() + SDS_PAGE_CHANGE_TIMEOUT_SECONDS
    )  # The moment when we give up
    while time.time() < wait_deadline:  # Keep checking until the time is up
        try:  # Reading can fail while the page is changing
            current_links = tuple(
                card_description["href"]
                for card_description in read_sds_cards(browser_page)
            )  # The addresses now on the page
            if (
                current_links and current_links != previous_links
            ):  # New cards are showing
                time.sleep(1)  # Let the page finish drawing
                return True  # The page changed
        except PlaywrightError as browser_error:  # The read did not work
            if is_browser_closed_error(browser_error):  # The browser itself is gone
                raise  # Let the restart logic deal with it
        time.sleep(0.5)  # Wait a moment and look again
    return False  # The cards never changed


def click_next_sds_page(
    browser_page: Page,
) -> bool:  # Click the "next" button of the safety data sheet results
    next_button = browser_page.locator(
        SDS_NEXT_BUTTON_SELECTOR
    ).first  # The first matching "next" button inside the right tab
    try:  # The button may be missing or disabled
        if next_button.count() == 0:  # There is no such button
            download_logger.info("[SDS page] no next button found")  # Record it
            return False  # Nothing to click
        if (
            next_button.is_disabled()
            or next_button.get_attribute("aria-disabled") == "true"
            or next_button.get_attribute("disabled") is not None
        ):  # The button is switched off, which means this is the last page
            download_logger.info(
                "[SDS page] the next button is disabled, last page reached"
            )  # Record it
            return False  # Nothing to click
        click_element_like_a_human(
            browser_page, next_button
        )  # Move the pointer to the button like a person and click it
        download_logger.info("[SDS page] clicked the next button")  # Record the click
        return True  # We asked for the next page
    except PlaywrightError as browser_error:  # The click did not work
        if is_browser_closed_error(browser_error):  # The browser itself is gone
            raise  # Let the restart logic deal with it
        download_logger.warning(
            "[SDS page] clicking next failed (%s), trying the generic next button search",
            str(browser_error).splitlines()[0],
        )  # Record the problem
        return click_next_page_button(
            browser_page
        )  # Fall back to the generic search for a next button


def read_sds_page_position(
    browser_page: Page,
) -> str:  # A short text such as "11 - 20 of 200087 results" for the log
    try:  # The element may be missing
        return (
            browser_page.locator(SDS_RESULTS_SCOPE_SELECTOR + " .agt-pagination__info")
            .first.inner_text(timeout=2000)
            .strip()
        )  # Read the pagination info text
    except PlaywrightError:  # The element could not be read
        return "position unknown"  # Say so


def open_sds_search_page(
    browser_page: Page, run_statistics: RunStatistics
) -> bool:  # Open the safety data sheet page; returns True when cards are showing
    page_urls_to_try = (
        [SDS_PAGE_FILTERED_URL, SDS_PAGE_PLAIN_URL]
        if TRY_FILTERED_SDS_URL_FIRST
        else [SDS_PAGE_PLAIN_URL]
    )  # The filtered address is tried first, the plain one is the fallback
    for page_url in page_urls_to_try:  # Try the addresses in order
        page_status = open_page_politely(
            browser_page, page_url, run_statistics
        )  # Open the page, backing off if blocked
        if page_status != PAGE_STATUS_OPENED:  # The page did not open normally
            download_logger.warning(
                "[SDS page] could not open %s (status: %s)", page_url, page_status
            )  # Record it
            continue  # Try the next address
        dismiss_cookie_banner(browser_page)  # Close the cookie popup if it is present
        if wait_for_sds_cards_to_appear(browser_page, 25):  # Cards are showing
            download_logger.info(
                "[SDS page] opened with results: %s", page_url
            )  # Record it
            return True  # Done
        download_logger.warning(
            "[SDS page] no result cards showed up at %s", page_url
        )  # The filtered address may not be understood by the site
    return False  # Nothing worked


def download_us_english_urls(
    browser_session: "BrowserSession",
    download_database: DownloadDatabase,
    us_english_urls: set,
    run_statistics: RunStatistics,
) -> bool:  # Download every address that has no file yet; returns True when a request was made
    pending_urls = sorted(
        us_english_url
        for us_english_url in us_english_urls
        if not download_database.is_file_for_url_already_downloaded(us_english_url)
    )  # The download folder is checked first, so existing files are never requested again
    skipped_count = len(us_english_urls) - len(
        pending_urls
    )  # How many were already on disk
    run_statistics.skipped_count += skipped_count  # Count them as skipped
    if not pending_urls:  # Nothing to do
        download_logger.info(
            "[SDS page] nothing new to download (%d already saved)", skipped_count
        )  # Record it
        return False  # No request was made
    download_database.save_newly_found_urls(
        set(pending_urls)
    )  # Store the addresses so a failed one can be retried later
    browser_session.internet_monitor.raise_error_if_internet_is_down()  # Do not open a tab while the internet is down
    with browser_session.temporary_download_tab() as download_page:  # Open the second tab and close it afterwards
        for url_position, pending_url in enumerate(
            pending_urls
        ):  # Download one address at a time
            browser_session.internet_monitor.raise_error_if_internet_is_down()  # Stop here and wait if the internet is down
            if url_position > 0:  # Only pause between two real requests
                browser_session.active_results_page.bring_to_front()  # Show the results tab, because a hidden tab would look odd to the website
                pause_while_acting_like_a_human(
                    browser_session.active_results_page,
                    *PAUSE_SECONDS_RANGE_BETWEEN_DOWNLOADS,
                    "between downloads",
                )  # Move the mouse and scroll instead of sitting still
            download_logger.info(
                "  (%d/%d) US English: %s",
                url_position + 1,
                len(pending_urls),
                pending_url,
            )  # Record the progress
            download_single_url(
                download_page,
                download_database,
                pending_url,
                run_statistics,
                browser_session.internet_monitor,
            )  # Download it
    log_run_statistics(
        run_statistics, "Totals so far"
    )  # Show the totals after this page
    return True  # Requests were made


def download_all_us_english_sds(
    browser_session: "BrowserSession",
    download_database: DownloadDatabase,
    run_statistics: RunStatistics,
) -> None:  # Walk through every result page and download the "English - United States" documents
    results_page = (
        browser_session.active_results_page
    )  # The tab used for browsing the results
    browser_session.close_unneeded_tabs()  # Start with only the results tab open
    browser_session.internet_monitor.raise_error_if_internet_is_down()  # Wait for the internet before opening the page
    download_logger.info(
        "Job 2: US English documents from %s", SDS_PAGE_PLAIN_URL
    )  # Record what we are about to do
    if not open_sds_search_page(
        results_page, run_statistics
    ):  # Open the page and wait for cards
        if (
            browser_session.internet_monitor.confirm_internet_is_down()
        ):  # The internet is the reason
            raise InternetOutageError(
                "The internet went down while opening the SDS page"
            )  # Wait for it, then retry
        download_logger.error(
            "[SDS page] could not open the page with results, giving up on job 2"
        )  # Record it
        return  # Nothing more to do
    pause_while_acting_like_a_human(
        results_page,
        *ACTIVITY_SECONDS_RANGE_AFTER_OPENING_SEARCH_PAGE,
        "after opening the SDS page",
    )  # Move the mouse and scroll before reading the results

    total_us_english_links_seen = 0  # Running count of US English links found
    for page_number in range(
        1, MAXIMUM_SDS_RESULT_PAGES + 1
    ):  # Walk through the result pages
        browser_session.close_unneeded_tabs()  # Close any tab other than the results and download tabs
        browser_session.internet_monitor.raise_error_if_internet_is_down()  # Stop here and wait if the internet is down
        results_page.bring_to_front()  # Keep the results tab in front

        card_descriptions = read_sds_cards(results_page)  # Read every card on this page
        all_links_on_page = tuple(
            card_description["href"] for card_description in card_descriptions
        )  # Every address on the page, used to notice when the page changes
        us_english_urls = get_us_english_urls_from_cards(
            card_descriptions
        )  # Keep the US English ones
        total_us_english_links_seen += len(us_english_urls)  # Add them to the total
        download_logger.info(
            "[SDS page] page %d (%s): %d card(s), %d US English, %d US English in total",
            page_number,
            read_sds_page_position(results_page),
            len(card_descriptions),
            len(us_english_urls),
            total_us_english_links_seen,
        )  # Show progress

        if us_english_urls:  # Only download when this page has something
            download_us_english_urls(
                browser_session, download_database, us_english_urls, run_statistics
            )  # Download the US English documents of this page

        pause_while_acting_like_a_human(
            results_page,
            *PAUSE_SECONDS_RANGE_BETWEEN_RESULT_PAGES,
            "before the next result page",
        )  # Move the mouse and scroll instead of sitting still
        results_page.bring_to_front()  # Return to the results tab before looking for the next page button
        if not click_next_sds_page(results_page):  # Try to go to the next page
            download_logger.info("[SDS page] there is no further page")  # Record it
            break  # The last page was reached
        if not wait_for_sds_cards_to_change(
            results_page, all_links_on_page
        ):  # Wait until the next page's cards are showing
            download_logger.warning(
                "[SDS page] the cards did not change after clicking next, stopping"
            )  # Explain why we stop
            break  # Stop, because paging does not work any more
        if not is_results_page_usable(
            results_page, run_statistics
        ):  # Check for the error page or "Access Denied"
            download_logger.warning(
                "[SDS page] the next result page is not usable, stopping"
            )  # Explain the stop
            break  # Stop here

    download_logger.info(
        "[SDS page] finished; %d US English link(s) seen", total_us_english_links_seen
    )  # Summarise the job
    browser_session.close_unneeded_tabs()  # The job is done, so close anything that is not needed


# ============================================================== INTERNET MONITOR


def is_host_responding(
    host_address: str,
) -> bool:  # Check whether one address answers us
    if shutil.which("ping"):  # Check whether the ping program is installed
        if sys.platform.startswith("win"):  # Windows uses different ping options
            ping_command = [
                "ping",
                "-n",
                "1",
                "-w",
                str(PING_TIMEOUT_SECONDS * 1000),
                host_address,
            ]  # One ping, timeout in milliseconds
        elif sys.platform.startswith(
            "linux"
        ):  # Linux uses -W for the timeout in seconds
            ping_command = [
                "ping",
                "-c",
                "1",
                "-W",
                str(PING_TIMEOUT_SECONDS),
                host_address,
            ]  # One ping, timeout in seconds
        else:  # macOS and other systems
            ping_command = [
                "ping",
                "-c",
                "1",
                host_address,
            ]  # One ping; the time limit is enforced by subprocess.run below
        try:  # Running ping can fail or take too long
            ping_result = subprocess.run(
                ping_command,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=PING_TIMEOUT_SECONDS + 2,
                check=False,
            )  # Run ping quietly
            if ping_result.returncode == 0:  # Exit code 0 means the host answered
                return True  # The host responded
        except (
            subprocess.TimeoutExpired,
            OSError,
        ):  # Ping took too long or could not run
            pass  # Fall through to the plain connection test
    try:  # Some networks block ping, so also try a plain connection
        with socket.create_connection(
            (host_address, FALLBACK_CONNECTION_TEST_PORT),
            timeout=FALLBACK_CONNECTION_TEST_TIMEOUT_SECONDS,
        ):  # Connect to the host
            return True  # The connection worked, so the host responded
    except OSError:  # The connection did not work
        return False  # The host did not respond


async def check_one_host_in_background(
    host_address: str,
) -> bool:  # Check one host in a helper thread so several can run together
    return await asyncio.to_thread(
        is_host_responding, host_address
    )  # Wait for the blocking check without freezing the event loop


async def check_all_hosts_at_once() -> bool:  # Check every host in parallel and report whether any answered
    host_responded_flags = await asyncio.gather(
        *(
            check_one_host_in_background(host_address)
            for host_address in INTERNET_CHECK_HOSTS
        )
    )  # Start all checks together and wait for all of them
    return any(host_responded_flags)  # One answer is enough to prove the internet works


def check_internet_connection() -> bool:  # The internet works when at least one address answers
    # Playwright's sync API may already own an event loop in the main thread, so the async check
    # always runs in its own short-lived thread, where asyncio.run() is safe.
    with ThreadPoolExecutor(
        max_workers=1
    ) as single_worker_pool:  # A pool with exactly one fresh thread
        return single_worker_pool.submit(
            asyncio.run, check_all_hosts_at_once()
        ).result()  # Run the async check there and wait for its answer


class InternetMonitor:  # Checks the internet in a background thread and tells the session when it goes down
    """Watches the internet in a background thread and flags the browser for a restart after an outage."""  # Short description

    def __init__(self):  # Prepare the shared state
        self.internet_available_event = (
            threading.Event()
        )  # Set while the internet works
        self.stop_requested_event = (
            threading.Event()
        )  # Set when the monitor should stop
        self.internet_state_lock = (
            threading.Lock()
        )  # Prevents two threads from changing the state at the same time
        self.outage_callback = None  # Function called when the internet goes down
        self.internet_outage_occurred = (
            False  # True when the browser must be restarted because of an outage
        )
        self.monitor_thread = None  # The background thread

    def start_monitoring(
        self, outage_callback
    ) -> None:  # Do a first check and start the background thread
        self.outage_callback = outage_callback  # Remember what to call on an outage
        if check_internet_connection():  # First check, done right now
            self.internet_available_event.set()  # The internet works
            download_logger.info("Internet check: the internet is working")  # Record it
        else:  # No answer from any address
            download_logger.warning(
                "Internet check: no answer yet, waiting for the internet"
            )  # Record it
        self.monitor_thread = threading.Thread(
            target=self._keep_checking_internet, name="internet-monitor", daemon=True
        )  # Create the monitor thread
        self.monitor_thread.start()  # Start checking in the background

    def stop_monitoring(self) -> None:  # Stop the background thread
        self.stop_requested_event.set()  # Ask the thread to finish
        if self.monitor_thread:  # Check whether it was ever started
            self.monitor_thread.join(timeout=15)  # Wait a little for it to finish

    def _keep_checking_internet(self) -> None:  # The work done by the background thread
        while (
            not self.stop_requested_event.is_set()
        ):  # Keep going until we are told to stop
            self.update_internet_status(
                check_internet_connection()
            )  # Check the internet and react to any change
            self.stop_requested_event.wait(
                INTERNET_CHECK_INTERVAL_SECONDS
            )  # Sleep, but wake up early when stopping

    def update_internet_status(
        self, internet_is_working: bool
    ) -> None:  # React when the internet goes down or comes back
        internet_just_went_down = (
            False  # Becomes True when the internet has just gone down
        )
        with self.internet_state_lock:  # Only one thread may change the state at a time
            internet_was_available = (
                self.internet_available_event.is_set()
            )  # What we believed until now
            if (
                internet_is_working and not internet_was_available
            ):  # The internet came back
                self.internet_available_event.set()  # Record that it works again
                download_logger.warning("INTERNET IS BACK")  # Tell the user
            elif (
                not internet_is_working and internet_was_available
            ):  # The internet just went down
                self.internet_available_event.clear()  # Record that it does not work
                self.internet_outage_occurred = (
                    True  # Remember that the browser must be restarted afterwards
                )
                internet_just_went_down = True  # The outage callback has to be called
                download_logger.error("INTERNET IS DOWN")  # Tell the user
        if (
            internet_just_went_down and self.outage_callback
        ):  # Call the outage callback outside the lock
            try:  # Calling it can fail
                self.outage_callback()  # Handle the outage
            except Exception:  # Anything unexpected
                download_logger.exception(
                    "Could not handle the internet outage"
                )  # Log the details

    def confirm_internet_is_down(
        self,
    ) -> bool:  # Check right now whether the internet is down
        internet_is_working = check_internet_connection()  # Do a live check
        self.update_internet_status(
            internet_is_working
        )  # Update the shared state and handle the outage if needed
        return not internet_is_working  # True when the internet is down

    def raise_error_if_internet_is_down(
        self,
    ) -> None:  # Cheap check used before every request
        if (
            not self.internet_available_event.is_set()
        ):  # The monitor says the internet is down
            raise InternetOutageError(
                "The internet is down"
            )  # Make the restart logic wait for it

    def read_and_clear_outage_flag(
        self,
    ) -> bool:  # Tell whether an outage happened since the last restart
        with self.internet_state_lock:  # Only one thread may change the state at a time
            outage_had_occurred, self.internet_outage_occurred = (
                self.internet_outage_occurred,
                False,
            )  # Read the flag and reset it
            return outage_had_occurred  # Give the old value back

    def wait_until_internet_available(self) -> None:  # Block until the internet works
        waited_seconds = 0  # Counts how long we have waited
        while not self.internet_available_event.wait(
            timeout=INTERNET_CHECK_INTERVAL_SECONDS
        ):  # Wait for the "internet works" signal
            waited_seconds += (
                INTERNET_CHECK_INTERVAL_SECONDS  # Add the time we just waited
            )
            download_logger.info(
                "Still waiting for the internet (%.0f seconds so far)", waited_seconds
            )  # Show progress
        if waited_seconds:  # Check whether we really had to wait
            download_logger.info(
                "The internet is back after about %.0f seconds", waited_seconds
            )  # Record it


# ============================================================== BROWSER SESSION

ERROR_PHRASES_MEANING_BROWSER_IS_CLOSED = (
    "has been closed",
    "target closed",
    "browser closed",
    "connection closed",
    "browser has disconnected",
)  # Known phrases that mean "the browser is gone"


def is_browser_closed_error(
    browser_error: Exception,
) -> bool:  # Check whether an error means the browser is gone
    error_text = str(
        browser_error
    ).lower()  # Lowercase the error text so capitals do not matter
    return any(
        closed_phrase in error_text
        for closed_phrase in ERROR_PHRASES_MEANING_BROWSER_IS_CLOSED
    )  # True if any known phrase appears


class BrowserSession:  # Owns the browser and both tabs; can restart everything if the browser closes or crashes
    """Owns the browser and both tabs; can restart everything if the browser closes or crashes."""  # Short description

    def __init__(self, internet_monitor: InternetMonitor):  # Set up an empty session
        self.internet_monitor = internet_monitor  # Tells us whether the internet works
        self.download_page: Optional[
            Page
        ] = None  # The temporary download tab, only set while it is open
        self.is_download_tab_being_opened = (
            False  # True for a moment while we open the download tab ourselves
        )
        self.invisible_playwright_launcher: Optional[
            InvisiblePlaywright
        ] = None  # The browser launcher, once started
        self.connected_browser: Any = None  # The Playwright Browser object
        self.browser_context: Any = None  # The browser context that owns both tabs
        self.results_page: Optional[
            Page
        ] = None  # The tab used for browsing the search results
        self.browser_restart_count = 0  # How many times the browser had to be restarted

    @property  # Lets the code write session.active_results_page without brackets
    def active_results_page(
        self,
    ) -> Page:  # The results tab, or a clear error when no browser is running
        if (
            self.results_page is None
        ):  # The browser was never started or has been stopped
            raise RuntimeError(
                "The browser is not running, so there is no results tab"
            )  # Fail loudly instead of with a confusing None error
        return self.results_page  # Hand back the open results tab

    def start_browser(self) -> None:  # Start the browser and open the results tab
        download_logger.info(
            "Starting the browser through invisible_playwright at %dx%d",
            BROWSER_WINDOW_WIDTH_PIXELS,
            BROWSER_WINDOW_HEIGHT_PIXELS,
        )  # Record it
        self.invisible_playwright_launcher = InvisiblePlaywright(
            extra_prefs={"pdfjs.disabled": True}
        )  # Prepare the launcher; without this Firefox shows PDFs in its viewer instead of downloading them
        self.connected_browser = (
            self.invisible_playwright_launcher.__enter__()
        )  # Launch the browser
        self.browser_context = self.connected_browser.new_context(
            viewport={
                "width": BROWSER_WINDOW_WIDTH_PIXELS,
                "height": BROWSER_WINDOW_HEIGHT_PIXELS,
            },
            screen={
                "width": BROWSER_WINDOW_WIDTH_PIXELS,
                "height": BROWSER_WINDOW_HEIGHT_PIXELS,
            },
        )  # Create the context both tabs live in, with a full HD window
        self.browser_context.set_default_timeout(
            PAGE_LOAD_TIMEOUT_MILLISECONDS
        )  # Default time limit for page actions in every tab
        self.results_page = self.browser_context.new_page()  # Open the first tab
        attach_browser_event_logging(
            self.results_page
        )  # Start logging everything the results tab does
        self.browser_context.on(
            "page", self._close_unexpected_new_tab
        )  # Close any popup or extra tab the moment it opens
        self.results_page.bring_to_front()  # Show the results tab
        reset_mouse_position()  # A fresh browser starts with the pointer at a known place
        self.results_page.mouse.move(
            current_mouse_x, current_mouse_y
        )  # Tell the new tab where the pointer is, so the first human-like move does not start from a corner

    @staticmethod  # This method does not need access to the session
    def _close_tab_ignoring_errors(
        tab_to_close: Page,
    ) -> None:  # Close a tab, ignoring any error if it is already gone
        try:  # Closing can fail if the tab is already gone
            tab_to_close.close()  # Close the tab
        except PlaywrightError:  # The tab or browser was already gone
            pass  # Nothing more to do

    def _close_unexpected_new_tab(
        self, new_tab: Page
    ) -> None:  # Close tabs that nobody asked for
        if self.is_download_tab_being_opened or new_tab in (
            self.results_page,
            self.download_page,
        ):  # This is a tab we want
            return  # Leave it open
        download_logger.info(
            "Closing an unexpected new tab: %s", new_tab.url
        )  # Record which tab is closed
        self._close_tab_ignoring_errors(new_tab)  # Close it

    def _list_all_browser_contexts(
        self,
    ) -> list:  # Find every browser context, so tabs in stray windows are found too
        try:  # Asking the browser can fail if it is already gone
            all_browser_contexts = list(
                self.connected_browser.contexts
            )  # Every context the browser currently has
        except (
            PlaywrightError,
            AttributeError,
        ):  # The browser is gone or was never started
            all_browser_contexts = []  # We cannot see any contexts
        if (
            self.browser_context is not None
            and self.browser_context not in all_browser_contexts
        ):  # Our own context must always be included
            all_browser_contexts.append(self.browser_context)  # Add it
        return all_browser_contexts  # Give the list back

    def _close_tabs_except(
        self, tabs_to_keep: tuple
    ) -> None:  # Close every tab and window that is not in the given list
        for (
            browser_context
        ) in self._list_all_browser_contexts():  # Look at every context, not only ours
            try:  # Reading the tab list can fail if the browser is gone
                open_tabs = list(browser_context.pages)  # Every tab of this context
            except PlaywrightError:  # The context is gone
                continue  # Nothing to close here
            for open_tab in open_tabs:  # Look at every open tab
                if open_tab not in tabs_to_keep:  # A tab we do not need
                    download_logger.info(
                        "Closing an unneeded tab: %s", open_tab.url
                    )  # Record which tab is closed
                    self._close_tab_ignoring_errors(
                        open_tab
                    )  # Close it; closing a window's last tab closes the window

    def close_unneeded_tabs(
        self,
    ) -> None:  # Keep only the results tab (and the download tab while it is in use)
        self._close_tabs_except(
            (self.results_page, self.download_page)
        )  # Close everything else

    def close_all_tabs(
        self,
    ) -> None:  # Close every tab and window, used when the work is finished
        self._close_tabs_except(())  # Keep nothing open

    def handle_internet_outage(
        self,
    ) -> None:  # Called by the monitor thread when the internet goes down
        # Playwright's sync API must only be used from the thread that started it, so this thread
        # cannot close the browser. The main thread notices the outage at its next step
        # (raise_error_if_internet_is_down) and restart_browser() closes the old browser.
        download_logger.error(
            "The internet is down: the browser will be closed and restarted by the main thread"
        )  # Record it

    @contextmanager  # Turns the method below into something usable in a "with" block
    def temporary_download_tab(
        self,
    ) -> Iterator[Page]:  # Open a second tab only while downloads need it
        download_logger.info(
            "Opening a temporary second tab for downloading"
        )  # Record it
        self.is_download_tab_being_opened = (
            True  # Tell the popup guard that the next new tab is wanted
        )
        try:  # Make sure the flag is always reset
            try:  # Opening the tab through the page can be blocked as a popup
                with self.browser_context.expect_page(
                    timeout=PAGE_LOAD_TIMEOUT_MILLISECONDS
                ) as new_tab_event_info:  # Wait for the new tab to appear
                    self.active_results_page.evaluate(
                        "() => { window.open('about:blank', '_blank'); }"
                    )  # Ask Firefox to open a blank tab in the same window
                new_download_page = new_tab_event_info.value  # The second tab
            except PlaywrightTimeoutError:  # No tab appeared, probably because it was blocked as a popup
                download_logger.warning(
                    "The tab did not open from the page, opening it directly instead"
                )  # Record the fallback
                new_download_page = (
                    self.browser_context.new_page()
                )  # Open the tab directly
            self.active_results_page.bring_to_front()  # Keep showing the results tab; downloads work from a background tab
        finally:  # Always runs
            self.is_download_tab_being_opened = (
                False  # The popup guard may close unexpected tabs again
            )

        self.download_page = new_download_page  # Remember the tab so the guards leave it alone while it is open
        attach_browser_event_logging(
            new_download_page
        )  # Start logging everything the download tab does
        try:  # Make sure the tab is always closed again
            yield new_download_page  # Hand the tab to the code inside the "with" block
        finally:  # Always runs, even after an error
            self.download_page = None  # The download tab is going away
            download_logger.info("Closing the temporary download tab")  # Record it
            self._close_tab_ignoring_errors(
                new_download_page
            )  # Close the second tab as soon as the downloads are done
            try:  # The remaining steps can fail if the browser itself is gone
                self.close_unneeded_tabs()  # Make sure nothing but the results tab is left open
                self.active_results_page.bring_to_front()  # Show the results tab again
            except PlaywrightError:  # The tab or browser was already gone
                pass  # Nothing more to do

    def stop_browser(self) -> None:  # Close the browser
        if (
            self.invisible_playwright_launcher is not None
        ):  # Check whether a browser was ever started
            try:  # Closing tabs can fail if the browser is already gone
                self.close_all_tabs()  # Close every tab and window first, so nothing is left behind
                if self.browser_context is not None:  # Our context still exists
                    self.browser_context.close()  # Close the context itself
            except PlaywrightError:  # The browser was already gone
                pass  # Nothing more to close
            try:  # The browser may already be dead
                self.invisible_playwright_launcher.__exit__(
                    None, None, None
                )  # Close the browser
            except Exception as closing_error:  # Anything raised by a browser that is already gone
                download_logger.debug(
                    "Ignoring error while closing the browser: %s", closing_error
                )  # Record it
        self.invisible_playwright_launcher = None  # Forget the old launcher
        self.connected_browser = None  # Forget the old browser
        self.browser_context = None  # Forget the old context
        self.results_page = None  # Forget the old results tab
        self.download_page = None  # Forget the old download tab

    def restart_browser(
        self,
    ) -> None:  # Start a fresh browser after the old one closed or crashed
        if (
            self.internet_monitor.read_and_clear_outage_flag()
        ):  # Check whether this restart is only because the internet was down
            download_logger.info(
                "This restart is due to an internet outage, so it does not count towards the limit"
            )  # Say so
        else:  # The restart has another reason, such as a crash
            self.browser_restart_count += 1  # Count this restart
            if (
                self.browser_restart_count > MAXIMUM_BROWSER_RESTARTS
            ):  # Check whether we have restarted too often
                raise RuntimeError(
                    f"The browser closed more than {MAXIMUM_BROWSER_RESTARTS} times, giving up"
                )  # Stop the run
        download_logger.error(
            "Browser problem detected. Restarting (%d/%d)",
            self.browser_restart_count,
            MAXIMUM_BROWSER_RESTARTS,
        )  # Record it
        self.stop_browser()  # Close whatever is left of the old browser
        self.internet_monitor.wait_until_internet_available()  # Do not start the browser until the internet works
        time.sleep(3)  # Give the system a moment to free resources
        self.start_browser()  # Start a fresh browser with a new results tab
        warm_up_session_on_home_page(
            self.active_results_page
        )  # Visit the home page again to refresh the session
        self.close_unneeded_tabs()  # Leave only the results tab open after the warm-up


def run_step_and_restart_browser_if_needed(
    browser_session: BrowserSession, step_description: str, step_to_run
):  # Run a step, restarting the browser if needed, and return its result
    """Run a step, transparently restarting the browser and retrying after a crash or internet outage."""  # Short description
    while True:  # Keep trying until the step finishes or we give up
        try:  # The step may fail if the browser closes
            return step_to_run()  # Run the step and hand back whatever it returns
        except InternetOutageError as outage_error:  # The internet went down
            download_logger.warning(
                "Internet outage during %s: %s", step_description, outage_error
            )  # Record it
            browser_session.restart_browser()  # Wait for the internet, then start a fresh browser
        except PlaywrightError as browser_error:  # A browser error happened
            if is_browser_closed_error(
                browser_error
            ):  # Check whether the browser or its tab closed
                download_logger.error(
                    "Browser closed during %s: %s",
                    step_description,
                    str(browser_error).splitlines()[0],
                )  # Record it
                browser_session.restart_browser()  # Start a new browser, which raises an error if the restarts ran out
            elif (
                browser_session.internet_monitor.confirm_internet_is_down()
            ):  # Check whether a lost internet connection is the cause
                download_logger.warning(
                    "The internet is down, so the error during %s is expected",
                    step_description,
                )  # Say so
                browser_session.restart_browser()  # Wait for the internet, then start a fresh browser
            else:  # Some other, real browser error
                download_logger.exception(
                    "Browser error during %s, skipping this step", step_description
                )  # Record the full error
                return (
                    None  # Go on with the next step instead of crashing the whole run
                )


# ============================================================== MAIN PROGRAM


def search_keywords_and_return_failed_ones(
    browser_session: BrowserSession,
    download_database: DownloadDatabase,
    keywords_to_search: list,
    run_statistics: RunStatistics,
) -> list:  # Search a list of keywords and return the ones that failed
    failed_keywords = []  # Keywords that could not be searched this time
    for keyword_position, search_keyword in enumerate(
        keywords_to_search, start=1
    ):  # Go through the keywords one by one
        if keyword_position > 1:  # Only pause between two keywords
            pause_while_acting_like_a_human(
                browser_session.active_results_page,
                *PAUSE_SECONDS_RANGE_BETWEEN_KEYWORDS,
                "before the next keyword",
            )  # Move the mouse and scroll instead of sitting still
        keyword_was_searched = run_step_and_restart_browser_if_needed(  # Search the keyword, restarting the browser if it closes
            browser_session,  # The session that owns the browser
            f"keyword '{search_keyword}'",  # Description used in log messages
            lambda keyword_to_search=search_keyword: search_one_keyword_and_download_pdfs(
                browser_session, download_database, keyword_to_search, run_statistics
            ),  # The work to do for this keyword
        )  # End of the restart wrapper
        if keyword_was_searched is not True:  # The keyword was skipped or hit an error
            failed_keywords.append(search_keyword)  # Remember it for a second try
    return failed_keywords  # Give back the keywords that still need work


def run_sds_downloader() -> None:  # Run the whole job from start to finish
    configure_console_logging()  # Turn on console logging first so everything is shown
    validate_settings()  # Stop early if a setting is obviously wrong
    download_logger.info(
        "Download folder: %s", DOWNLOAD_FOLDER
    )  # Record where PDFs are saved
    download_logger.info(
        "Keywords: %s", " ".join(SEARCH_KEYWORDS)
    )  # Record which keywords will be searched

    DOWNLOAD_FOLDER.mkdir(exist_ok=True)  # Make sure the PDFs folder exists
    download_database = DownloadDatabase(DATABASE_FILE_PATH)  # Open the SQLite database
    download_database.register_pdf_files_already_on_disk(
        DOWNLOAD_FOLDER
    )  # Remember PDFs that are already in the folder
    download_database.ignore_urls_in_unwanted_formats()  # Skip old pending URLs that are not in a wanted format

    run_statistics = RunStatistics()  # Running totals for the whole run

    try:  # Make sure the database is closed even if something fails
        internet_monitor = InternetMonitor()  # Prepare the background internet check
        browser_session = BrowserSession(internet_monitor)  # Build the browser session
        try:  # Make sure the monitor and the browser are always stopped at the end
            internet_monitor.start_monitoring(
                browser_session.handle_internet_outage
            )  # Check the internet in the background
            internet_monitor.wait_until_internet_available()  # Do not start the browser while the internet is down
            browser_session.start_browser()  # Start the browser with a single results tab
            if not warm_up_session_on_home_page(
                browser_session.active_results_page
            ):  # Visit the home page and browse around first
                download_logger.warning(
                    "Warm-up did not finish cleanly, continuing anyway"
                )  # Record the problem
            browser_session.close_unneeded_tabs()  # Leave only the results tab open after the warm-up

            # ---------------- JOB 1: keyword search on the chemical standards pages
            still_failed_keywords: list = (
                []
            )  # Keywords that could not be searched even after a second try
            failed_keywords = search_keywords_and_return_failed_ones(
                browser_session, download_database, SEARCH_KEYWORDS, run_statistics
            )  # Search every keyword once
            if failed_keywords:  # Some keywords could not be searched
                download_logger.info(
                    "Retrying %d keyword(s) that failed: %s",
                    len(failed_keywords),
                    " ".join(failed_keywords),
                )  # Say which ones
                still_failed_keywords = search_keywords_and_return_failed_ones(
                    browser_session, download_database, failed_keywords, run_statistics
                )  # Give them a second chance
                if still_failed_keywords:  # Some keywords failed twice
                    download_logger.warning(
                        "Keywords that still failed: %s",
                        " ".join(still_failed_keywords),
                    )  # Report them

            download_logger.info(
                "All keywords searched: downloading the best available version of every remaining document"
            )  # Record the final step of job 1
            run_step_and_restart_browser_if_needed(  # Download the remaining documents, restarting the browser if it closes
                browser_session,  # The session that owns the browser
                "the final download of the best remaining versions",  # Description used in log messages
                lambda: download_documents_using_temporary_tab(
                    browser_session,
                    download_database,
                    select_documents_for_final_download(
                        download_database, bool(still_failed_keywords)
                    ),
                    run_statistics,
                ),  # Re-reads the waiting documents on every attempt
            )  # End of the restart wrapper
            log_run_statistics(
                run_statistics, "JOB 1 FINISHED"
            )  # Show the totals after job 1

            # ---------------- JOB 2: every "English - United States" document on the SDS search page
            run_step_and_restart_browser_if_needed(  # Walk the SDS result pages, restarting the browser if it closes
                browser_session,  # The session that owns the browser
                "the US English SDS pages",  # Description used in log messages
                lambda: download_all_us_english_sds(
                    browser_session, download_database, run_statistics
                ),  # The work to do for job 2
            )  # End of the restart wrapper
            log_run_statistics(
                run_statistics, "JOB 2 FINISHED"
            )  # Show the totals after job 2
        finally:  # Always runs, even after an error
            internet_monitor.stop_monitoring()  # Stop the background internet check
            browser_session.close_all_tabs()  # The work is finished, so close every tab and window
            browser_session.stop_browser()  # Close the browser
    except AccessBlockedError as blocked_error:  # The website blocked us too many times in a row
        download_logger.error(
            "STOPPED EARLY: %s", blocked_error
        )  # Explain why the run ended
    except KeyboardInterrupt:  # The user pressed Ctrl+C
        download_logger.warning(
            "Stopped by the user; progress is saved and the next run continues from here"
        )  # Explain what happens
    except Exception:  # Anything unexpected that escaped the code above
        download_logger.exception(
            "Unexpected error, stopping"
        )  # Record the full error with its traceback
        raise  # Pass the error on so the script exits with an error code
    finally:  # Always runs at the very end
        log_run_statistics(run_statistics, "FINAL")  # Show the final totals
        download_database.close_database()  # Close the database
        download_logger.info("Database closed, finished")  # Record the final step


if (
    __name__ == "__main__"
):  # Only run when this file is executed directly, not when it is imported
    run_sds_downloader()  # Start the job
