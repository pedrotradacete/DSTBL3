import DSTBL3

/-- Small executable entry point for the Lake target; it is not part of the
paper formalization, but keeps the generated project runnable. -/
def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
