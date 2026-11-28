-- [desk-auto instantiate] batch 20261128-122658 · template tpl16（tpl16_conp_verifier_flip.lean）
-- 题面与模板陈述逐字一致（空白规范化后比对），仅替换定理名；终验走私有 Actions 全量三行 import。
/-
模板 tpl16 — 刻画族：coNP 的 ∀-验证器刻画（翻转 NP 验证器）
来源：pvsnp-repo/PvsNP/Units/m2_conp_verifier_iff.lean（本队证明；与 drafts/m2_conp_verifier_iff_check.lean 仅差 import 头一行）
编译状态：✅ 已结算文本。
填空点：① 翻转的等价（boolNotEquiv：输出字母表经 Bool 取反重解释，按编码换）；
  ② 证书界多项式 p 的沿用/换算；③ ∀/∃ 对偶的命题陈述式（x ∈ L ↔ ∀ w, |w| ≤ p(|x|) → V (x,w) = true）。
引理链：ptc_not（同机器、同时间界、输出字母表 trans boolNotEquiv）→ 主定理双向各一次取反。
同族变体：NP 验证器正规形、coNP/NP 互刻画类题（key 含 verifier / iff / compl）优先套此模板。
-/
import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m2_conp_verifier_iff

/-- Boolean negation as an equivalence of `Bool` with itself. -/
def boolNotEquiv : Bool ≃ Bool where
  toFun := (!·)
  invFun := (!·)
  left_inv b := Bool.not_not b
  right_inv b := Bool.not_not b

/-- Flipping a pair-verifier's answers keeps it polynomial-time computable:
keep the same machine, the same time bound and the same input alphabet, and
only reinterpret the output symbols through Boolean negation. -/
theorem ptc_not {f : List Bool × List Bool → Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (fun xw => !f xw) := by
  obtain ⟨c⟩ := hf
  have hfun : ∀ a, Turing.TM2OutputsInTime c.tm
      (List.map c.inputAlphabet.invFun (PvsNP.encodePair a))
      (some (List.map (c.outputAlphabet.trans boolNotEquiv).invFun
        (PvsNP.encodeAnswer (!f a)))) (c.time.eval (PvsNP.encodePair a).length) := by
    intro a
    have h := c.outputsFun a
    have heq : List.map (c.outputAlphabet.trans boolNotEquiv).invFun
          (PvsNP.encodeAnswer (!f a))
        = List.map c.outputAlphabet.invFun (PvsNP.encodeAnswer (f a)) := by
      show [(c.outputAlphabet.trans boolNotEquiv).invFun (!f a)]
        = [c.outputAlphabet.invFun (f a)]
      congr 1
      show c.outputAlphabet.invFun (!(!f a)) = c.outputAlphabet.invFun (f a)
      rw [Bool.not_not]
    rw [heq]
    exact h
  exact ⟨{
    tm := c.tm
    inputAlphabet := c.inputAlphabet
    outputAlphabet := c.outputAlphabet.trans boolNotEquiv
    time := c.time
    outputsFun := hfun }⟩

theorem statement : ∀ L : Language Bool, L ∈ PvsNP.coNP ↔
    ∃ (V : List Bool × List Bool → Bool) (p : Polynomial ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ L ↔ ∀ w : List Bool, w.length ≤ p.eval x.length → V (x, w) = true := by
  intro L
  constructor
  · -- From the NP verifier of Lᶜ, negate it.
    intro hL
    have hL' : Lᶜ ∈ PvsNP.NP := hL
    obtain ⟨V, p, hV, hspec⟩ := hL'
    refine ⟨fun xw => !V xw, p, ptc_not hV, fun x => ?_⟩
    constructor
    · intro hx w hw
      by_contra hcon
      have hVtrue : V (x, w) = true := by
        cases hVw : V (x, w) with
        | true => exact hVw
        | false => simp [hVw] at hcon
      have hxc : x ∈ Lᶜ := (hspec x).mpr ⟨w, hw, hVtrue⟩
      exact (Set.mem_compl_iff.mp hxc) hx
    · intro hall
      by_contra hx
      have hxc : x ∈ Lᶜ := Set.mem_compl_iff.mpr hx
      obtain ⟨w, hw, hVtrue⟩ := (hspec x).mp hxc
      have h1 := hall w hw
      simp [hVtrue] at h1
  · -- From a ∀-verifier of L, negate it to get the NP verifier of Lᶜ.
    rintro ⟨V, p, hV, hspec⟩
    show Lᶜ ∈ PvsNP.NP
    refine ⟨fun xw => !V xw, p, ptc_not hV, fun x => ?_⟩
    constructor
    · intro hxc
      by_contra hcon
      have hall : ∀ w, w.length ≤ p.eval x.length → V (x, w) = true := by
        intro w hw
        by_contra hVfalse
        apply hcon
        refine ⟨w, hw, ?_⟩
        cases hVw : V (x, w) with
        | true => exact absurd hVw hVfalse
        | false => simp [hVw]
      exact (Set.mem_compl_iff.mp hxc) ((hspec x).mpr hall)
    · rintro ⟨w, hw, hVtrue⟩
      by_contra hx
      have hxL : x ∈ L := by simpa [Set.mem_compl_iff] using hx
      have h1 := (hspec x).mp hxL w hw
      simp [h1] at hVtrue

end PvsNP.Units.m2_conp_verifier_iff

/-- A language is in coNP exactly when it has a polynomial-time universal
verifier: membership is witnessed by every short certificate being accepted. -/
theorem PvsNP.Units.m2_conp_verifier_iff : ∀ L : Language Bool, L ∈ PvsNP.coNP ↔
    ∃ (V : List Bool × List Bool → Bool) (p : Polynomial ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ L ↔ ∀ w : List Bool, w.length ≤ p.eval x.length → V (x, w) = true :=
  PvsNP.Units.m2_conp_verifier_iff.statement
