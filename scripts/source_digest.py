"""Print a deterministic SHA-256 digest of the release source tree."""

from hashlib import sha256
from pathlib import Path


root = Path(__file__).resolve().parent.parent
files = sorted(
    path
    for path in root.rglob("*")
    if path.is_file()
    and not any(part in {".git", ".lake"} for part in path.relative_to(root).parts)
    and path.suffix not in {".olean", ".ilean", ".trace", ".log"}
    and path.name != ".DS_Store"
)
digest = sha256()
for path in files:
    relative = path.relative_to(root).as_posix().encode()
    digest.update(relative)
    digest.update(b"\0")
    digest.update(sha256(path.read_bytes()).digest())
print(f"{digest.hexdigest()}  {len(files)} files")
