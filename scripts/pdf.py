"""Export a rendered deck to PDF via reveal.js's print mode. Called by `./slides pdf`.

Usage: python scripts/pdf.py DECK_DIR OUT.pdf [--steps]
  --steps  one page per fragment step (default: one page per slide)
"""
import functools
import http.server
import shutil
import sys
import threading

from playwright.sync_api import sync_playwright

deck_dir, out = sys.argv[1], sys.argv[2]
steps = "--steps" in sys.argv[3:]

# Serve the deck on a free port for the duration of the export.
class QuietHandler(http.server.SimpleHTTPRequestHandler):
    def log_message(self, *args):
        pass

handler = functools.partial(QuietHandler, directory=deck_dir)
server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler)
threading.Thread(target=server.serve_forever, daemon=True).start()

query = "print-pdf" + ("" if steps else "&pdfSeparateFragments=false")
url = f"http://127.0.0.1:{server.server_address[1]}/?{query}"

chrome = next(filter(None, map(shutil.which, ["google-chrome", "chromium", "chromium-browser"])), None)
with sync_playwright() as p:
    browser = p.chromium.launch(executable_path=chrome) if chrome else p.chromium.launch()
    page = browser.new_page()
    page.goto(url, wait_until="networkidle")
    # reveal.js lays out the print pages once it is ready; also wait for KaTeX/fonts.
    page.wait_for_function("window.Reveal && Reveal.isReady() && document.querySelector('.pdf-page')")
    page.evaluate("document.fonts.ready")
    page.wait_for_timeout(500)
    page.pdf(path=out, prefer_css_page_size=True, print_background=True)
    browser.close()

server.shutdown()
print(f"PDF written to {out}")
