"""Export only sealed website bytes into a fresh deployment directory."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import stat

from check_release_gate import require_approved

ROOT = Path(__file__).resolve().parents[1]
ENVELOPE = ('audit/release/REVIEW.json', 'PUBLICATION-STATUS.json')


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def checked_relative(rel):
    if not isinstance(rel, str) or not rel or '\\' in rel or ':' in rel:
        raise ValueError('Invalid release path: ' + repr(rel))
    path = PurePosixPath(rel)
    if path.is_absolute() or path.as_posix() != rel or any(p in ('.', '..') for p in path.parts):
        raise ValueError('Noncanonical release path: ' + rel)
    return path


def reject_links(path):
    """Reject symbolic links and Windows reparse points in existing components."""
    for part in (path, *path.parents):
        if part.is_symlink():
            raise ValueError('Deployment paths cannot contain symbolic links: ' + str(part))
        if part.exists() and getattr(part.lstat(), 'st_file_attributes', 0) & getattr(stat, 'FILE_ATTRIBUTE_REPARSE_POINT', 0x400):
            raise ValueError('Deployment paths cannot contain reparse points: ' + str(part))


def export_files(source_root, destination, files):
    """Copy and verify a supplied allowlist; callers must authenticate it first."""
    source_root = Path(source_root).absolute()
    destination = Path(destination).absolute()
    reject_links(source_root)
    reject_links(destination)
    source_root = source_root.resolve()
    destination = destination.resolve()
    if destination == source_root or destination.is_relative_to(source_root):
        raise ValueError('Deployment destination must be outside the source website')
    if destination.exists():
        raise ValueError('Deployment destination must not already exist')
    if not files:
        raise ValueError('Empty deployment allowlist')

    planned = []
    seen = set()
    for rel, expected in files.items():
        relative = checked_relative(rel)
        if rel.casefold() in seen:
            raise ValueError('Case-ambiguous deployment path: ' + rel)
        seen.add(rel.casefold())
        source = source_root.joinpath(*relative.parts)
        target = destination.joinpath(*relative.parts)
        reject_links(source)
        if not source.resolve().is_relative_to(source_root) or not target.resolve().is_relative_to(destination):
            raise ValueError('Deployment path escapes its root: ' + rel)
        if not source.is_file() or sha256(source.read_bytes()) != expected:
            raise ValueError('Approved website file changed or missing: ' + rel)
        planned.append((rel, source, target, expected))

    destination.mkdir(parents=True, exist_ok=False)
    for rel, source, target, expected in planned:
        # Authenticate the exact bytes being written, not an earlier stat result.
        reject_links(source)
        content = source.read_bytes()
        if sha256(content) != expected:
            raise ValueError('Approved website changed during export: ' + rel)
        target.parent.mkdir(parents=True, exist_ok=True)
        reject_links(target.parent)
        with target.open('xb') as output:
            output.write(content)
        if sha256(target.read_bytes()) != expected:
            raise ValueError('Exported website byte mismatch: ' + rel)

    actual = set()
    for path in destination.rglob('*'):
        reject_links(path)
        if path.is_file():
            actual.add(path.relative_to(destination).as_posix())
    if actual != set(files):
        raise ValueError('Exported website differs from the exact allowlist')
    return {'result': 'PASS', 'destination': str(destination), 'files': len(actual),
            'scope': 'Exact approved website bytes; no rebuild or unlisted file is included.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--destination', required=True)
    args = parser.parse_args()
    require_approved()
    manifest = json.loads((ROOT / 'audit/release/RELEASE-FILES.json').read_text(encoding='utf-8'))
    files = dict(manifest['website'])
    for rel in ENVELOPE:
        if rel in files:
            raise ValueError('Approval envelope must not create a hash cycle')
        # The gate checks these exact public copies against the root envelopes.
        files[rel] = sha256((ROOT / 'site/dist' / rel).read_bytes())
    print(json.dumps(export_files(ROOT / 'site/dist', args.destination, files)))


if __name__ == '__main__':
    main()
