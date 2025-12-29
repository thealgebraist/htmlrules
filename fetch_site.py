import sys
import urllib.request

def fetch(url):
    try:
        with urllib.request.urlopen(url) as response:
            print(response.read().decode('utf-8'))
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 fetch_site.py <url>")
        sys.exit(1)
    fetch(sys.argv[1])