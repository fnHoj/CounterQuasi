import CounterQuasi.TypeSystem

namespace Quasi

inductive SubtypeOf : ⦗G⦘ → ⦗G⦘ → Prop where
  | refl (γ : ⦗G⦘) : SubtypeOf γ γ
  | subtype_unknown {γ : ⦗G⦘} : SubtypeOf γ ??
  | function {τ₁ τ₂ σ₁ σ₂} :
    SubtypeOf σ₁ τ₁ → SubtypeOf τ₂ σ₂ →
      SubtypeOf (τ₁ ⟶ τ₂) (σ₁ ⟶ σ₂)

infix:50 " <: " => SubtypeOf

abbrev SubtypeOf.rfl {γ : ⦗G⦘} : γ <: γ := .refl γ

theorem SubtypeOf.trans : SubtypeOf σ τ → SubtypeOf τ μ → SubtypeOf σ μ
  | refl _, h | h, refl _ => h
  | _, subtype_unknown => subtype_unknown
  | function h₁ h₂, function h₃ h₄ => function (trans h₃ h₁) (trans h₂ h₄)

theorem ground_subtypeOf_ground {γ₁ γ₂ : G} : .ground γ₁ <: .ground γ₂ ↔ γ₁ = γ₂ where
  mpr | rfl => .rfl
  mp | .rfl => rfl

theorem function_subtypeOf_function {τ₁ τ₂ σ₁ σ₂ : ⦗G⦘} :
    τ₁ ⟶ τ₂ <: σ₁ ⟶ σ₂ ↔ σ₁ <: τ₁ ∧ τ₂ <: σ₂ where
  mpr := And.elim SubtypeOf.function
  mp
  | .refl (_ ⟶ _) => ⟨.rfl, .rfl⟩
  | .function h₁ h₂ => ⟨h₁, h₂⟩

instance [inst : DecidableEq G] : DecidableRel (@SubtypeOf G) := subtypeOf
where subtypeOf (σ τ : ⦗G⦘) : Decidable (σ <: τ) := match σ, τ with
  | .ground _,  _ ⟶ _
  | ??,         _ ⟶ _
  | ??,         .ground _
  | _ ⟶ _,      .ground _  => isFalse nofun
  | γ,          ??         => isTrue .subtype_unknown
  | .ground γ₁, .ground γ₂ => by rw [ground_subtypeOf_ground]; apply inst
  | σ₁ ⟶ σ₂,    τ₁ ⟶ τ₂    => by
    rw [function_subtypeOf_function]
    have := subtypeOf τ₁ σ₁
    have := subtypeOf σ₂ τ₂
    infer_instance
termination_by sizeOf σ + sizeOf τ

def joint (σ τ : ⦗G⦘) : Prop := ∃ μ, μ <: σ ∧ μ <: τ

theorem any_joint : joint ?? τ := ⟨τ, .subtype_unknown, .rfl⟩
theorem joint_any : joint σ ?? := ⟨σ, .rfl, .subtype_unknown⟩

theorem joint_ground {γ₁ γ₂ : G} : joint (.ground γ₁) (.ground γ₂) ↔ γ₁ = γ₂ where
  mpr | rfl => ⟨_, .rfl, .rfl⟩
  mp h := match γ₁, γ₂, h with | _, _, ⟨_, .rfl, .rfl⟩ => rfl

theorem joint_function {σ₁ σ₂ τ₁ τ₂ : ⦗G⦘} : joint (σ₁ ⟶ σ₂) (τ₁ ⟶ τ₂) ↔ joint σ₂ τ₂ where
  mpr | ⟨μ, hσ, hτ⟩ => ⟨?? ⟶ μ, .function .subtype_unknown hσ, .function .subtype_unknown hτ⟩
  mp h := match σ₁, σ₂, τ₁, τ₂, h with
  | _, _, _, _, ⟨_ ⟶ _, .rfl,           .rfl⟩           => ⟨_, .rfl, .rfl⟩
  | _, _, _, _, ⟨_ ⟶ _, .rfl,           .function _ h⟩  => ⟨_, .rfl, h⟩
  | _, _, _, _, ⟨_ ⟶ _, .function _ h,  .rfl⟩           => ⟨_, h, .rfl⟩
  | _, _, _, _, ⟨_ ⟶ _, .function _ hσ, .function _ hτ⟩ => ⟨_, hσ, hτ⟩

instance instDecidableRelJoint [inst : DecidableEq G] : DecidableRel (@joint G)
  | _ ⟶ _, .ground _
  | .ground _, _ ⟶ _ => .isFalse fun | ⟨.ground _, h₁, h₂⟩ => nomatch h₁, h₂
  | ??, _ => isTrue any_joint
  | _, ?? => isTrue joint_any
  | .ground γ₁, .ground γ₂ => by rw [joint_ground]; apply inst
  | σ₁ ⟶ σ₂, τ₁ ⟶ τ₂ => by rw [joint_function]; apply instDecidableRelJoint

def joint.intersect : {σ τ : ⦗G⦘} → joint σ τ → ⦗G⦘
  | ??, τ, _ => τ
  | σ, ??, _ => σ
  | .ground γ, .ground _, _ => γ
  | _ ⟶ _, _ ⟶ _, h => ?? ⟶ (joint_function.mp h).intersect
  | _ ⟶ _, .ground _, h
  | .ground _, _ ⟶ _, h => False.elim <|
    match h with | ⟨.ground _, h₁, h₂⟩ => nomatch h₁, h₂

inductive TypedExpression (S : TypeSystem) : (S.𝕏 → Option S.𝕋) → S.𝕋 → Type where
  | const c : TypedExpression S Γ (S.Δ c)
  | var : Γ x = some τ → TypedExpression S Γ τ
  | lambda x (e : TypedExpression S (fun y ↦ if y = x then some τ else Γ y) σ) :
    TypedExpression S Γ (τ ⟶ σ)
  | any_apply (e₁ : TypedExpression S Γ σ) (e₂ : TypedExpression S Γ τ)
    (h : joint σ (τ ⟶ ??) := by decide) : TypedExpression S Γ ??
  | apply_downcast (e₁ : TypedExpression S Γ (σ₁ ⟶ σ₂)) (e₂ : TypedExpression S Γ τ)
    (h : joint σ₁ τ) : TypedExpression S Γ σ₂

protected def TypedExpression.repr (S : TypeSystem) [Repr S.𝕏] [Repr S.𝔾] [Repr S.ℂ]
    (Γ : S.𝕏 → Option S.𝕋) (τ : S.𝕋) (e : TypedExpression S Γ τ) : Std.Format :=
  (match e with
  | .const v | .var (x := v) _ => reprPrec v 10
  | .lambda (τ := τ) (σ := σ) x e =>
    "(lambda " ++ reprPrec x 10 ++ " : " ++ reprPrec σ 10 ++ " =>" ++ .indentD (e.repr ++ ")")
  | .any_apply (τ := τ) e₁ e₂ h => "(" ++ e₁.repr ++ " :> " ++ reprPrec h.intersect 10 ++
    " <: " ++ reprPrec (τ ⟶ ??) 10 ++ ")" ++ .indentD ("(" ++ e₂.repr ++ ")")
  | .apply_downcast (σ₁ := σ₁) e₁ e₂ h => "(" ++ e₁.repr ++ ")" ++
    .indentD ("(" ++ e₂.repr ++ " :> " ++ reprPrec h.intersect 10 ++ " <: " ++ reprPrec σ₁ 10 ++ ")")
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
    annotate S Γ e₂ >>= fun ⟨τ, e₂'⟩ ↦
    annotate S Γ e₁ >>= fun
    | ⟨.ground _, _⟩ => none
    | ⟨??, e₁'⟩ => some ⟨??, .any_apply e₁' e₂' any_joint⟩
    | ⟨σ₁ ⟶ σ₂, e₁'⟩ => some <| if h : joint σ₁ τ
      then ⟨σ₂, .apply_downcast e₁' e₂' h⟩
      else ⟨??, .any_apply e₁' e₂' <| by rw [joint_function]; exact joint_any⟩

end Quasi
