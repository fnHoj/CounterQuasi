inductive PartialType (G : Type u) where
  | ground (γ : G)
  | unknown
  | function (σ τ : PartialType G)

notation "⦗" G:min "⦘" => PartialType G

inductive Expression (X : Type u) (G : Type v) (C : Type w) where
  | constant (c : C)
  | var (x : X)
  | lambda (x : X) (σ : ⦗G⦘) (e : Expression X G C)
  | apply (e₁ e₂ : Expression X G C)

set_option linter.checkUnivs false in
structure TypeSystem.{u, v, w} where
  𝕏 : Type v
  [vars_decidableEq : DecidableEq 𝕏]
  𝔾 : Type u
  [grounds_decidableEq : DecidableEq 𝔾]
  ℂ : Type w
  Δ : ℂ → ⦗𝔾⦘

namespace PartialType

instance : Coe G ⦗G⦘ where coe := .ground

notation "??" => unknown
infixr:65 " ⟶ " => function

protected def reprPrec [Repr G] (τ : ⦗G⦘) (n : Nat) : Std.Format := match τ with
  | .ground γ => reprPrec γ n
  | ?? => "??"
  | σ ⟶ τ =>
    let s : Std.Format := σ.reprPrec 66 ++ " ⟶ " ++ τ.reprPrec 65
    if n ≤ 65 then s else "(" ++ s ++ ")"

instance [Repr G] : Repr ⦗G⦘ where reprPrec := PartialType.reprPrec

theorem ground_eq : ground γ₁ = ground γ₂ ↔ γ₁ = γ₂ where
  mp h := by injection h
  mpr | rfl => rfl

theorem function_eq : σ₁ ⟶ τ₁ = σ₂ ⟶ τ₂ ↔ σ₁ = σ₂ ∧ τ₁ = τ₂ where
  mp h := by injection h; constructor <;> assumption
  mpr | ⟨rfl, rfl⟩ => rfl

instance instDecidableEqPartialType [inst : DecidableEq G] : DecidableEq ⦗G⦘
  | .ground γ₁, .ground γ₂ => by rw [ground_eq]; apply inst
  | ??, ?? => .isTrue rfl
  | σ₁ ⟶ τ₁, σ₂ ⟶ τ₂ => by
    rw [function_eq]
    have := instDecidableEqPartialType σ₁ σ₂
    have := instDecidableEqPartialType τ₁ τ₂
    infer_instance
  | .ground _, ?? | .ground _, _ ⟶ _
  | ??, .ground _ | ??, _ ⟶ _
  | _ ⟶ _, .ground _ | _ ⟶ _, ?? => .isFalse nofun

end PartialType

namespace Expression

instance : Coe C (Expression X G C) where coe := constant
instance : Coe X (Expression X G C) where coe := var
instance [inst : OfNat C n] : OfNat (Expression X G C) n where
  ofNat := .constant inst.ofNat
instance : CoeFun (Expression X G C) (fun _ ↦ Expression X G C → Expression X G C) where
  coe := apply

notation:min "lambda " x:min " : " σ:min " => " e:min => lambda x σ e
notation:min "lambda " x:min " => " e:min => lambda x : ?? => e

protected def reprPrec [Repr X] [Repr G] [Repr C] (n : Nat) : Expression X G C → Std.Format
  | constant v | var v => reprPrec v n
  | apply e₁ e₂ =>
    let s : Std.Format := e₁.reprPrec max_prec ++ " " ++ e₂.reprPrec (max_prec + 1)
    if n ≤ max_prec then s else "(" ++ s ++ ")"
  | lambda x => e =>
    let s : Std.Format := "lambda " ++ reprPrec x 10 ++ " => " ++ e.reprPrec 10
    if n ≤ 10 then s else "(" ++ s ++ ")"
  | lambda x : σ => e =>
    let s : Std.Format := "lambda " ++ reprPrec x 10 ++ " : " ++ reprPrec σ 10 ++ " => " ++ e.reprPrec 10
    if n ≤ 10 then s else "(" ++ s ++ ")"

instance [Repr X] [Repr G] [Repr C] : Repr (Expression X G C) where
  reprPrec e := e.reprPrec

end Expression

namespace TypeSystem

variable (S : TypeSystem.{u, v, w})

abbrev 𝕋 := ⦗S.𝔾⦘
abbrev 𝔼 := Expression S.𝕏 S.𝔾 S.ℂ

instance : Coe S.𝔾 S.𝕋 where coe := .ground
instance : Coe S.𝔾 ⦗S.𝔾⦘ where coe := .ground

instance : DecidableEq S.𝕏 := S.vars_decidableEq
instance : DecidableEq S.𝔾 := S.grounds_decidableEq

end TypeSystem
