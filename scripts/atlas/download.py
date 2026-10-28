#!/usr/bin/env python3
"""Download and hash-check the Atlas's published exact export source shards."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess

BASE = 'https://anyonatlas.org/export-v1/'
FAMILIES = ('identifiers-exact', 'modular-exact', 'structure', 'fusion')


def get(url):
    return subprocess.run(['curl', '--fail', '--silent', '--show-error', '--location',
                           '--retry', '4', '--max-time', '90', '-H',
                           'Accept-Encoding: identity', url], check=True, capture_output=True).stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('data/atlas'))
    parser.add_argument('--workers', type=int, default=6)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    raw = get(BASE + 'manifest.json')
    manifest = json.loads(raw)
    if manifest['schemaVersion'] != 1:
        raise ValueError('Unsupported export manifest schema')
    (args.output / 'manifest.json').write_bytes(raw)
    descriptors = [c['families'][family] for kind in manifest['kinds'].values()
                   for rank in kind['ranks'] for c in rank['chunks'] for family in FAMILIES]

    def download(desc):
        target = args.output / desc['file']
        if target.exists() and hashlib.sha256(target.read_bytes()).hexdigest() == desc['sha256']:
            return
        payload = get(BASE + desc['file'])
        if hashlib.sha256(payload).hexdigest() != desc['sha256']:
            raise ValueError(f"SHA-256 mismatch: {desc['file']}")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(payload)

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        for i, _ in enumerate(pool.map(download, descriptors), 1):
            if i % 100 == 0 or i == len(descriptors):
                print(f'{i}/{len(descriptors)} shards verified', flush=True)
    print(f"Snapshot {manifest['sourceFingerprint']}; counts {manifest['counts']}")


if __name__ == '__main__':
    main()
