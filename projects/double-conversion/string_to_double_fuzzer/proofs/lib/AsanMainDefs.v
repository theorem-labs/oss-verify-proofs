(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanLibNode AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanLibTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint ht_of (HT : list (nat * (nat * acs))) (h : nat) : option (nat * acs) :=
  match HT with [] => None | (j, e) :: HT' => if Nat.eqb j h then Some e else ht_of HT' h end.
Definition hs_of (HT : list (nat * (nat * acs))) (h : nat) : option acs :=
  match ht_of HT h with Some e => Some (snd e) | None => None end.
Definition lv_of (HT : list (nat * (nat * acs))) (h : nat) : option nat :=
  match ht_of HT h with Some e => Some (fst e) | None => None end.
Fixpoint lookupT {X : Type} (PT : list (nat * X)) (h : nat) : option X :=
  match PT with [] => None | (j, t) :: PT' => if Nat.eqb j h then Some t else lookupT PT' h end.

Lemma ht_of_In : forall HT h e, ht_of HT h = Some e -> In (h, e) HT.
Proof.
  induction HT as [|[j c] HT IH]; intros h e H; cbn [ht_of] in H; [discriminate|].
  destruct (Nat.eqb_spec j h); [injection H as <-; subst; left; reflexivity | right; apply IH; exact H].
Qed.
Lemma lookupT_In {X} : forall (PT : list (nat * X)) h t, lookupT PT h = Some t -> In (h, t) PT.
Proof.
  induction PT as [|[j c] PT IH]; intros h t H; cbn [lookupT] in H; [discriminate|].
  destruct (Nat.eqb_spec j h); [injection H as <-; subst; left; reflexivity | right; apply IH; exact H].
Qed.

(* [comment removed for export] *)
Definition HL_none (h : nat) : option nat := None.

(* [comment removed for export] *)
Definition HSA (HS_asan : nat -> option acs) (h : nat) : acs := match HS_asan h with Some cs => cs | None => asan_init end.

(* [comment removed for export] *)
Definition pay_start (ch : acs) (C : class) : acs := set_kn ch (facts_of_class C ++ kn ch).
Definition main_start (HS_asan : nat -> option acs) (h : nat) (C : class) : acs := pay_start (HSA HS_asan h) C.

(* [comment removed for export] *)
Definition ebounds (k : list kentry) (e : expr) : Z * Z :=
  match erange k e with Some p => p | None => (0, two64 - 1) end.
Definition mcase_lo (ch : acs) (e : expr) (mid : Z) : acs :=
  let b := ebounds (kn ch) e in set_kn ch (KRange e (fst b) (Z.min mid (snd b)) :: kn ch).
Definition mcase_hi (ch : acs) (e : expr) (mid : Z) : acs :=
  let b := ebounds (kn ch) e in set_kn ch (KRange e (Z.max (mid + 1) (fst b)) (snd b) :: kn ch).

(* [comment removed for export] *)
Definition all_qty : list qty := [QArgc; QL0; QL1; QLook; QFlen; QCfgLen; QCmod; QCnt; QRoom].
Definition qrange (q : qty) : Z * Z :=
  match q with
  | QArgc => (1, 1024) | QL0 => (0, 131071) | QL1 => (0, 131071) | QLook => (0, 4) | QFlen => (0, 2 ^ 26)
  | QCfgLen => (0, 32767) | QCmod => (0, 3) | QCnt => (0, 1) | QRoom => (- 32773, 2 ^ 26)
  end.
(* [comment removed for export] *)
Definition qbounds (C : class) (q : qty) : Z * Z := clamp (cbounds C q) (fst (qrange q)) (snd (qrange q)).
(* [comment removed for export] *)
Definition class_empty (C : class) : bool :=
  (existsb (fun q => let a := qbounds C q in snd a <? fst a) all_qty
   || (snd (qbounds C QFlen) - 6 - fst (qbounds C QCfgLen) <? fst (qbounds C QRoom))
   || (snd (qbounds C QRoom) <? fst (qbounds C QFlen) - 6 - snd (qbounds C QCfgLen)))%bool.
(* [comment removed for export] *)
Definition class_le (C C' : class) : bool :=
  forallb (fun q => let a := qbounds C q in let b := cbounds C' q in
                    (snd a <? fst a) || ((fst b <=? fst a) && (snd a <=? snd b)))%bool all_qty.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition XLm segs (A : atable) (nx0 : nat) : acs -> option acs := ALN.summary_lib segs LIBTAB_ASAN A nx0.

(* [comment removed for export] *)
Section Forms.
  Variable HS_asan : nat -> option acs.
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.
  Variable TTm : nat -> option (acs * plan * shape).   (* [comment removed for export] *)

  #[local] Notation CHK C HS HL cs p :=
    (check ASEGS ITm ASAN NX0 AsanInit.LIMIT (XNm ASEGS ASAN NX0 RPN.RP_ASAN (iotab_of C)) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of C)) (XLm ASEGS ASAN NX0)
           HS HL TTm KCm BFUELm FUELm None cs p).

  (* [comment removed for export] *)
  Definition main_check (h : nat) (C : class) (p : plan) : cres := CHK C HS_none HL_none (main_start HS_asan h C) p.
  Definition pre_check (h : nat) (C : class) (HT : list (nat * (nat * acs))) (p : plan) : cres := CHK C (hs_of HT) (lv_of HT) (main_start HS_asan h C) p.
  Definition pay_check (ch : acs) (C : class) (p : plan) : cres := CHK C HS_none HL_none (pay_start ch C) p.
  Definition seg_check (ch : acs) (C : class) (HT : list (nat * (nat * acs))) (p : plan) : cres := CHK C (hs_of HT) (lv_of HT) (pay_start ch C) p.
  (* [comment removed for export] *)
  Definition pre0_check (h : nat) (HT : list (nat * (nat * acs))) (p : plan) : cres := CHK [] (hs_of HT) (lv_of HT) (HSA HS_asan h) p.

  (* [comment removed for export] *)
  Definition tailf_check (T : acs) (p : plan) : cres :=
    check ASEGS ITm ASAN NX0 AsanInit.LIMIT (XNm ASEGS ASAN NX0 RPN.RP_ASAN (iotab_of [])) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of [])) (XLm ASEGS ASAN NX0)
          HS_none HL_none AP.TT_none KCm BFUELm FUELm None T p.
  Definition tailsF_ok : Prop :=
    forall t T p s, TTm t = Some (T, p, s) -> AP.is_full p = true -> tailf_check T p = COk s /\ shape_closed s = true.
  Definition tailsF_okb (TL : list (acs * plan * shape)) : bool :=
    forallb (fun e : acs * plan * shape => let '(T, p, s) := e in
               if AP.is_full p then match tailf_check T p with COk s' => shape_eqb s s' && shape_closed s | CErr _ _ _ => false end
               else true) TL.
  (* [comment removed for export] *)
  Definition tails_all_ok : Prop := AP.tails_ok ASEGS ITm ASAN NX0 AsanInit.LIMIT TTm KCm /\ tailsF_ok.
End Forms.

