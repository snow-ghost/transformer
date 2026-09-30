#!/usr/bin/env python3
"""Download artifacts only for the pinned Mathlib modules imported by this library."""
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
modules = sorted({module for file in (root / "VerifiedClassifier").glob("*.lean")
                  for module in re.findall(r"^import (Mathlib\.\S+)", file.read_text(), re.M)})
subprocess.run(["lake", "exe", "cache", "get", *modules], cwd=root, check=True)
