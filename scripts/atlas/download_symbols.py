#!/usr/bin/env python3
"""Download symbol archives advertised in the current Atlas catalog."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess

SITE = 'https://anyonatlas.org'


def fetch(url):
    return subprocess.run(['curl', '-LfsS', '--retry', '4', '--max-time', '90', url],
                          check=True, capture_output=True).stdout


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('data/symbols'))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    raw = fetch(SITE + '/data-v2/catalog/manifest.json')
    manifest = json.loads(raw)
    (args.output / 'catalog-manifest.json').write_bytes(raw)
    downloads = []
    for kind, group in manifest['kinds'].items():
        desc = group['core']
        core_raw = fetch(SITE + '/data-v2/' + desc['file'])
        if hashlib.sha256(core_raw).hexdigest() != desc['sha256']:
            raise ValueError('catalog core hash mismatch')
        core = json.loads(core_raw)
        if 'symbolsComputed' not in core['fields']:
            continue
        fields = core['fields']
        for row in core['rows']:
            if not row[fields.index('symbolsComputed')]:
                continue
            rid = row[fields.index('id')]
            match = re.fullmatch(r'[BF](\d{2})-(\d{5})', rid)
            if not match:
                raise ValueError(f'bad record ID {rid!r}')
            rank, index = map(int, match.groups())
            info = next(r for r in group['ranks'] if r['rank'] == rank)
            chunk = index // info['detailChunkSize']
            url = f'{SITE}/data-v2/catalog/{kind}/details/{rank:02}/{chunk:04}.json.gz'
            detail = json.loads(gzip.decompress(fetch(url)))
            record = next(r for r in detail['records'] if r['id'] == rid)
            for symbol, entry in record.get('symbolDownloads', {}).items():
                if symbol not in ('F', 'R') or not entry['url'].startswith('/symbols/') or Path(entry['filename']).name != entry['filename']:
                    raise ValueError(f'unsafe symbol descriptor for {rid}')
                target = args.output / entry['filename']
                if not target.exists() or target.stat().st_size != entry['bytes'] or digest(target) != entry['sha256']:
                    partial = target.with_suffix(target.suffix + '.part')
                    subprocess.run(['curl', '-LfsS', '--retry', '4', '-C', '-', SITE + entry['url'], '-o', str(partial)], check=True)
                    if partial.stat().st_size != entry['bytes'] or digest(partial) != entry['sha256']:
                        raise ValueError(f'archive hash or length mismatch: {rid} {symbol}')
                    partial.replace(target)
                downloads.append({'id': rid, **entry})
                print(f'Verified {rid} {symbol}: {target}', flush=True)
    (args.output / 'symbols-manifest.json').write_text(json.dumps({'sourceFingerprint': manifest['sourceFingerprint'], 'downloads': downloads}, indent=2) + '\n')
    print(f'Catalog snapshot {manifest["sourceFingerprint"]}: {len(downloads)} symbol archives')


if __name__ == '__main__':
    main()
