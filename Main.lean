import CounterQuasi

def main : IO Unit := do
  IO.println "这是一段相当错误的代码，它在尝试计算 succ #t："
  IO.println <| repr Counterexample
  IO.println "但是，在 Quasi 类型中，它偏偏能通过类型检查。"
  IO.println <| repr <| Quasi.annotate TSys (fun _ ↦ none) Counterexample
