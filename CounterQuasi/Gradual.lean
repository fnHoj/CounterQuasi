import CounterQuasi.TypeSystem

namespace Gradual

inductive TypeConsistent {G} : ⦗G⦘ → ⦗G⦘ → Prop where
  | refl (τ : ⦗G⦘) : TypeConsistent τ τ
  | function : TypeConsistent σ₁ σ₂ → TypeConsistent τ₁ τ₂ →
    TypeConsistent (σ₁ ⟶ τ₁) (σ₂ ⟶ τ₂)
  | con_unknown {τ : ⦗G⦘} : TypeConsistent τ ??
  | unknown_con {τ : ⦗G⦘} : TypeConsistent ?? τ
infix:40 " ~ " => TypeConsistent

namespace TypeConsistent

protected abbrev rfl {τ : ⦗G⦘} : TypeConsistent τ τ := .refl τ

theorem ground_iff {γ₁ γ₂ : G} : .ground γ₁ ~ .ground γ₂ ↔ γ₁ = γ₂ where
  mpr | rfl => .rfl
  mp | .rfl => rfl

theorem function_iff {σ₁ τ₁ σ₂ τ₂ : ⦗G⦘} :
    σ₁ ⟶ τ₁ ~ σ₂ ⟶ τ₂ ↔ σ₁ ~ σ₂ ∧ τ₁ ~ τ₂ where
  mpr := And.elim .function
  mp
  | .rfl => ⟨.rfl, .rfl⟩
  | .function h₁ h₂ => ⟨h₁, h₂⟩

instance instDecidableRelTypeConsistent [inst : DecidableEq G] :
    DecidableRel (@TypeConsistent G)
  | ??, _ => isTrue .unknown_con
  | _, ?? => isTrue .con_unknown
  | .ground _, _ ⟶ _ | _ ⟶ _, .ground _ => .isFalse nofun
  | .ground γ₁, .ground γ₂ => by rw [ground_iff]; apply inst
  | σ₁ ⟶ τ₁, σ₂ ⟶ τ₂ => by
    rw [function_iff]
    have := instDecidableRelTypeConsistent σ₁ σ₂
    have := instDecidableRelTypeConsistent τ₁ τ₂
    infer_instance

protected theorem symm : σ ~ τ → τ ~ σ
  | .rfl => .rfl
  | .function hσ hτ => .function hσ.symm hτ.symm
  | .con_unknown => .unknown_con
  | .unknown_con => .con_unknown

end TypeConsistent

inductive TypedExpression (S : TypeSystem) : (S.𝕏 → Option S.𝕋) → S.𝕋 → Type where
  | const c : TypedExpression S Γ (S.Δ c)
  | var : Γ x = some τ → TypedExpression S Γ τ
  | lambda x (e : TypedExpression S (fun y ↦ if y = x then some τ else Γ y) σ) :
    TypedExpression S Γ (τ ⟶ σ)
  | apply (e₁ : TypedExpression S Γ (τ ⟶ τ')) (e₂ : TypedExpression S Γ τ) :
    TypedExpression S Γ τ'
  | cast (τ : S.𝕋) (e : TypedExpression S Γ σ) (ne : τ ≠ σ := by decide) (con : τ ~ σ := by decide) :
    TypedExpression S Γ τ

protected def TypedExpression.repr (S : TypeSystem) [Repr S.𝕏] [Repr S.𝔾] [Repr S.ℂ]
    (Γ : S.𝕏 → Option S.𝕋) (τ : S.𝕋) (e : TypedExpression S Γ τ) : Std.Format :=
  (match e with
  | .const v | .var (x := v) _ => reprPrec v 10
  | .lambda (τ := τ) x e =>
    "lambda " ++ reprPrec x 10 ++ " : " ++ reprPrec τ 10 ++ " =>" ++ .indentD ("(" ++ e.repr ++ ")")
  | .apply e₁ e₂ => "(" ++ e₁.repr ++ ")" ++ .indentD ("(" ++ e₂.repr ++ ")")
  | .cast _ e _ _ => e.repr
  ) ++ " : " ++ reprPrec τ 10

instance (S : TypeSystem) [Repr S.𝕏] [Repr S.𝔾] [Repr S.ℂ]
    (Γ : S.𝕏 → Option S.𝕋) (τ : S.𝕋) : Repr (TypedExpression S Γ τ) where
  reprPrec e _ := e.repr

def annotate (S : TypeSystem) (Γ : S.𝕏 → Option S.𝕋) :
    S.𝔼 → Option (Σ τ, TypedExpression S Γ τ)
  | .constant c => some ⟨S.Δ c, .const c⟩
  | .var x => match h : Γ x with
    | none => none
    | some τ => some ⟨τ, .var h⟩
  | lambda x : σ => e => (fun ⟨τ, e⟩ ↦ ⟨σ ⟶ τ, .lambda x e⟩) <$>
    annotate S (fun y ↦ if y = x then some σ else Γ y) e
  | .apply e₁ e₂ =>
    annotate S Γ e₂ >>= fun ⟨τ₂, e₂'⟩ ↦
    annotate S Γ e₁ >>= fun
    | ⟨.ground _, _⟩ => none
    | ⟨??, e₁'⟩ => some ⟨??, .apply (.cast (τ₂ ⟶ ??) e₁' nofun .con_unknown) e₂'⟩
    | ⟨τ ⟶ τ', e₁'⟩ => if h : τ ~ τ₂ then some ⟨τ', .apply e₁' <|
      if heq : τ = τ₂ then heq ▸ e₂' else .cast τ e₂' heq h⟩ else none

end Gradual
