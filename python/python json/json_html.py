#!/usr/bin/env python3

import json
import os

# Use current directory
BASE_DIR = os.path.abspath(".")

# Paths
report_path = os.path.join(BASE_DIR, "binning_report.json")
out_path = os.path.join(BASE_DIR, "report_summary.html")

with open(report_path) as f:
    data = json.load(f)

summary = data.get("summary", {})
buckets = data.get("bucket", [])

with open(out_path, "w",encoding="utf-8") as html:
    html.write("<html><head><title>Binning Summary</title>")
    html.write("""
    <style>
        body { font-family: Arial; margin: 20px; }
        .bucket { margin: 10px 0; padding: 10px; border: 1px solid #ddd; border-radius: 5px; }
        .fail { color: red; font-weight: bold; }
        .pass { color: green; font-weight: bold; }
        .unknown { color: orange; font-weight: bold; }
        h2, h3 { color: #2c3e50; }
        ul { padding-left: 20px; }
        li { margin-bottom: 3px; }
        .hint { font-size: 0.9em; color: #555; }
    </style>
    """)
    html.write("</head><body>")
    html.write("<h2>🧪 RDA Binning Summary</h2>")
    html.write(f"<p><b>Binning Type:</b> {summary.get('binning_type', 'N/A')}</p>")
    html.write(f"<p><b>Rule File:</b> {summary.get('binning_rule', 'N/A')}</p>")
    html.write(f"<p><b>Version:</b> {summary.get('version', 'N/A')}</p>")
    html.write(f"<p><b>Total Buckets:</b> {len(buckets)}</p>")

    for i, bucket in enumerate(buckets, 1):
        status = bucket.get("status", "UNKNOWN")
        css_class = "fail" if status == "FAIL" else "pass" if status == "PASS" else "unknown"
        html.write(f"<div class='bucket'><h3>📦 Bucket {i}</h3>")
        html.write(f"<p><b>Status:</b> <span class='{css_class}'>{status}</span></p>")
        html.write(f"<p><b>Error Type:</b> {bucket.get('error_type', 'N/A')}</p>")
        html.write(f"<p><b>Hint Case:</b> {bucket.get('hint_case', 'N/A')}</p>")
        if bucket.get("hint_message"):
            html.write(f"<p class='hint'><b>Hint:</b> {bucket.get('hint_message')}</p>")
        html.write(f"<p><b>Failing Testcases ({bucket.get('count', 0)}):</b></p><ul>")
        for case in bucket.get("cases", []):
            html.write(f"<li>{case}</li>")
        html.write("</ul></div>")

    html.write("</body></html>")

print(f"✅ HTML summary generated: {out_path}")
