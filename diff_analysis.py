""""""

from pathlib import Path
import glob
import subprocess

agda_dir = Path(__file__).parent / "Plasmaduck"
targets = list(map(lambda p: agda_dir / p, glob.glob("**/*.agda", root_dir=agda_dir)))
# git diff-files -c


class Definition:
    file: Path
    name: str

    def __init__(self, name: str, file: Path) -> None:
        self.file = file
        self.name = name

    def __eq__(self, value: object) -> bool:
        if isinstance(value, Definition):
            return value.name == self.name and value.file == self.file
        return False

    def __hash__(self) -> int:
        return hash((self.name, self.file))


class Graph:
    edges: dict[Definition, set[Definition]]

    def __init__(self) -> None:
        self.edges = dict()

    # def _ensure_source_exists(self, source: Definition) -> set[Definition]:
    #     return self.edges.get(source, set())

    def add_edge(self, source: Definition, target: Definition) -> None:
        self.edges.get(source, set()).add(target)


def inspect_file(file: Path):
    """(I love file name injection into commands that I'm running.)

    NOT SAFE! Injects filename directly into a command, and so could enable arbitrary code execution.
    """
    print(f"inspecting {file}")
    if '"' in str(file):
        raise ValueError("Unsafe use of inspect_file I think?")
    complete = subprocess.run(
        ["git", "diff-files", "-c", file], capture_output=True, text=True
    )
    print(complete.stderr)
    print(complete.stdout)
    if complete.returncode != 0:
        raise ValueError


for t in targets:
    inspect_file(t)
