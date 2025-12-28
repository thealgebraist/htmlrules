import urllib.request
import sys
import re

def fetch_clean(url, outfile):
    print(f"Fetching {url}...")
    headers = {'User-Agent': 'Mozilla/5.0'} 
    req = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(req) as response:
            html = response.read().decode('utf-8', errors='ignore')
    except Exception as e:
        print(f"Error: {e}")
        return

    # Basic cleaning
    html = re.sub(r'<script.*?>.*?</script>', '', html, flags=re.DOTALL)
    html = re.sub(r'<style.*?>.*?</style>', '', html, flags=re.DOTALL)
    html = re.sub(r'<!--.*?-->', '', html, flags=re.DOTALL)
    html = re.sub(r'<!DOCTYPE.*?>', '', html, flags=re.DOTALL)
    
    # Normalize whitespace
    html = re.sub(r'\s+', ' ', html).strip()
    
    with open(outfile, 'w') as f:
        f.write(html)
    print(f"Saved to {outfile}")

fetch_clean('https://cnn.com', 'cnn.html')
fetch_clean('https://google.com', 'google.html')
fetch_clean('https://www.dr.dk', 'dr.html')
