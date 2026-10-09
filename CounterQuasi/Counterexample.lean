import CounterQuasi.Quasi
import CounterQuasi.Gradual

inductive GroundType where
  | boolean
  | number
deriving DecidableEq

instance : Repr GroundType where
  reprPrec
  | .boolean, _ => "boolean"
  | .number, _ => "number"

inductive Constant where
  | false | true
  | ofNat (n : Nat)
  | succ
deriving DecidableEq

notation "#f" => Constant.false
notation "#t" => Constant.true
instance : OfNat Constant n where ofNat := .ofNat n

instance : Repr Constant where
  reprPrec
  | #f, _ => "#f"
  | #t, _ => "#t"
  | .ofNat n, p => reprPrec n p
  | .succ, _ => "succ"

open GroundType

abbrev TSys : TypeSystem where
  𝕏 := String
  𝔾 := GroundType
  ℂ := Constant
  Δ
  | #f | #t => boolean
  | .ofNat _ => number
  | .succ => number ⟶ number

abbrev succ : TSys.𝔼 := Constant.succ

macro "#quasi" t:term : command =>
  `(#eval Quasi.annotate TSys (fun _ ↦ none) $t)
macro "#gradual" t:term : command =>
  `(#eval Gradual.annotate TSys (fun _ ↦ none) $t)

/--
info: some ⟨??, ((lambda "x" : number =>
   (succ : number ⟶ number)
     ("x" : number :> number <: number) : number) : number ⟶ number :> ?? ⟶ number <: boolean ⟶ ??)
   (#t : boolean) : ??⟩
-/
#guard_msgs in #quasi (lambda "x" : number => succ "x") #t

/-- info: none -/
#guard_msgs in #gradual (lambda "x" : number => succ "x") #t

/-- info: some ⟨??, (succ : number ⟶ number :> ?? ⟶ number <: boolean ⟶ ??) (#t : boolean) : ??⟩ -/
#guard_msgs in #quasi succ #t

/-- info: none -/
#guard_msgs in #gradual succ #t

/--
info: some ⟨?? ⟶ ??, (lambda "x" : ?? =>
   ("x" : ?? :> number ⟶ ?? <: number ⟶ ??)
     ((succ : number ⟶ number)
       ("x" : ?? :> number <: number) : number) : ??) : ?? ⟶ ??⟩
-/
#guard_msgs in #quasi lambda "x" => .apply "x" (succ "x")
/--
info: some ⟨?? ⟶ ??, lambda "x" : ?? =>
   (("x" : ?? : number ⟶ ??)
     ((succ : number ⟶ number)
       ("x" : ?? : number) : number) : ??) : ?? ⟶ ??⟩
-/
#guard_msgs in #gradual lambda "x" => .apply "x" (succ "x")

/--
info: some ⟨number, (lambda "f" : ?? ⟶ number =>
   (("f" : ?? ⟶ number)
     (1 : number : ??) : number) : (?? ⟶ number) ⟶ number)
   (lambda "x" : number =>
     ((succ : number ⟶ number)
       ("x" : number) : number) : number ⟶ number : ?? ⟶ number) : number⟩
-/
#guard_msgs in #gradual
  (lambda "f" : ?? ⟶ number => .apply "f" 1)
    (lambda "x" : number => succ "x")
