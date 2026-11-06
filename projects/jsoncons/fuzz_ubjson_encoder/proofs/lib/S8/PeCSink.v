(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Heap Require Import HeIfaceS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PESK.

Record sink : Type := SK { sk_b : Z; sk_z : Z; sk_c : Z }.
Definition sink0 : sink := SK 0 0 0.

Definition sink_own (k : sink) : list (Z * Z) := if sk_c k =? 0 then [] else [(sk_b k, sk_c k)].

Definition is_cap (c : Z) : Prop := c = 0 \/ exists e, 0 <= e /\ c = 2 ^ e.

Definition cap_next (c : Z) : Z := if c =? 0 then 1 else 2 * c.

Definition sk_push (k : sink) (b' : Z) : sink :=
  if sk_z k <? sk_c k then SK (sk_b k) (sk_z k + 1) (sk_c k) else SK b' (sk_z k + 1) (cap_next (sk_c k)).

Lemma is_cap_next c : is_cap c -> is_cap (cap_next c).
Proof.
  intros [->|(e & He & ->)]; unfold cap_next; cbn; [right; exists 0; split; [lia|reflexivity]|].
  replace (2 ^ e =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (Z.pow_pos_nonneg 2 e); lia).
  right. exists (e + 1). split; [lia|]. rewrite Z.pow_add_r, Z.pow_1_r; lia.
Qed.
Lemma cap_next_pos c : 0 <= c -> 0 < cap_next c.
Proof. unfold cap_next. destruct (c =? 0) eqn:E; [lia|]. apply Z.eqb_neq in E. lia. Qed.

Record sink_policy : Type := SP {
  sp_mode : Prop;
  sp_cap : Z -> Prop;
  sp_nmax : Z;
  sp_csz : Z -> Z;
  sp_B : Z;
  sp_hb : Z -> Prop
}.

Definition sink_pot (P : sink_policy) (c : Z) : credit :=
  (if c =? 0 then 2 else 1, sp_B P - (if c =? 0 then 0 else sp_csz P c)).

Record sink_policy_ok (P : sink_policy) : Prop := SPO {
  spo_csz_nonneg : forall c, 0 <= sp_csz P c;
  spo_B : forall c, is_cap c -> 0 < c <= sp_nmax P -> sp_cap P c -> sp_csz P c <= sp_B P;
  spo_hb_mono : forall h h', sp_hb P h -> h' <= h -> sp_hb P h';

  spo_next : forall c h, is_cap c -> (0 < c -> sp_cap P c) -> sp_hb P h -> c <= h ->
             0 < cap_next c <= sp_nmax P
             /\ (if c =? 0 then 0 else sp_csz P c) + sp_csz P (cap_next c) <= sp_B P;
  spo_nmax : sp_nmax P <= NREQ;
  spo_B_nonneg : 0 <= sp_B P
}.

Section WithImage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable E : pe_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.

Definition sink_at (P : sink_policy) (M : word -> option byte) (o : Z) (k : sink) : Prop :=
  L5.u64_at segs M o (sk_b k) /\ L5.u64_at segs M (o + 8) (sk_b k + sk_z k) /\ L5.u64_at segs M (o + 16) (sk_b k + sk_c k)
  /\ L5.defined M o 24 /\ acc M o 24
  /\ 0 <= sk_z k <= sk_c k /\ is_cap (sk_c k)
  /\ (sk_c k = 0 -> sk_b k = 0)
  /\ (0 < sk_c k ->
        L5.defined M (sk_b k) (sk_c k) /\ acc M (sk_b k) (sk_z k) /\ ann M (sk_b k) (sk_z k) (sk_c k)
        /\ block_range L (sk_b k) (sk_c k) /\ sp_cap P (sk_c k)
        /\ sk_c k <= sp_nmax P).

Lemma sink_pot_fst P c : 1 <= fst (sink_pot P c).
Proof. unfold sink_pot. cbn [fst]. destruct (c =? 0); lia. Qed.
Lemma sink_pot_nonneg P M o k : sink_policy_ok P -> sink_at P M o k -> 0 <= snd (sink_pot P (sk_c k)).
Proof.
  intros PO (_ & _ & _ & _ & _ & Hz & Hc & Hc0 & HBK). pose proof (spo_B_nonneg P PO) as B0.
  unfold sink_pot. cbn [snd]. destruct (sk_c k =? 0) eqn:EQ0; [lia|]. apply Z.eqb_neq in EQ0.
  assert (Hp : 0 < sk_c k) by (destruct Hz; lia). destruct (HBK Hp) as (_ & _ & _ & _ & CAP & NM).
  pose proof (spo_B P PO (sk_c k) Hc ltac:(lia) CAP). lia.
Qed.

Definition o_sink (fb : Z) : Z := fb + pe_off_sink E.

Definition push_back_spec (P : sink_policy) : Prop :=
  sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (o pv sp r : Z) (k : sink),
    hi_heap HI (sink_own k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    PMSP.entry A L R M sp r 0 ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 pv ->
    sink_at P M o k ->
    sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->
    sp <= pv -> pv + 1 <= hl_sptop L -> (pv + 1 <= o \/ o + 24 <= pv) -> L5.defined M pv 1 ->
    (sk_z k = sk_c k -> 0 < cap_next (sk_c k) <= sp_nmax P
                        /\ (if sk_c k =? 0 then 0 else sp_csz P (sk_c k)) + sp_csz P (cap_next (sk_c k)) <= sp_B P) ->
    PMSP.credit_le (sink_pot P (sk_c k)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit) (b' : Z),
        regs_preserved R R' ->
        sink_at P M' o (sk_push k b') ->
        L5C.hpres L LBX sp (PMSP.pm_scr 0) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (sink_pot P (sk_c k)) (sink_pot P (sk_c (sk_push k b'))) ->
        model_but_vm model model' -> hi_heap HI (sink_own (sk_push k b') ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R (pe_push_back E) M model) K.

Definition push_back_ind_spec (pc : Z) (P : sink_policy) : Prop :=
  sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (q rr o pv sp r : Z) (k : sink),
    hi_heap HI (sink_own k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    PMSP.entry A L R M sp r 1 ->
    getr R 10%bv = Z_to_bv 64 q -> getr R 11%bv = Z_to_bv 64 pv ->
    L5.u64_at segs M q rr -> rr mod 8 = 0 -> 0 < rr -> L5.u64_at segs M rr o -> 0 < o ->
    sp <= q -> q + 8 <= hl_sptop L -> sp <= rr -> rr + 8 <= hl_sptop L ->
    sink_at P M o k ->
    sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->
    sp <= pv -> pv + 1 <= hl_sptop L -> L5.defined M pv 1 ->
    (sk_z k = sk_c k -> 0 < cap_next (sk_c k) <= sp_nmax P
                        /\ (if sk_c k =? 0 then 0 else sp_csz P (sk_c k)) + sp_csz P (cap_next (sk_c k)) <= sp_B P) ->
    PMSP.credit_le (sink_pot P (sk_c k)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit) (b' : Z),
        regs_preserved R R' ->
        sink_at P M' o (sk_push k b') ->
        L5C.hpres L LBX sp (PMSP.pm_scr 1) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (sink_pot P (sk_c k)) (sink_pot P (sk_c (sk_push k b'))) ->
        model_but_vm model model' -> hi_heap HI (sink_own (sk_push k b') ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.
End WithImage.

Section Policies.
Context {bmK : BMode}.

Definition SP_S (lim : Z) : sink_policy := SP (bm_on = true) (fun c => fits lim c) (2 ^ 35) (fun _ => 0) 0 (fun _ => True).

Definition SP_T (zmax hb : Z) : sink_policy := SP True (fun _ => True) zmax cszR (cszR (zmax / 2) + cszR zmax) (fun h => h <= hb).

Lemma cszR_nonneg n : 0 <= cszR n.
Proof. unfold cszR. lia. Qed.
Lemma cszR_mono n m : n <= m -> cszR n <= cszR m.
Proof.
  intros H. unfold cszR.
  assert ((n + 20 + 4095) / 4096 <= (m + 20 + 4095) / 4096) by (apply Z.div_le_mono; lia). nia.
Qed.
Lemma pow2_le_half e j : 0 <= e -> 0 <= j -> 2 ^ e < 2 ^ (j + 1) -> 2 ^ e <= 2 ^ j.
Proof.
  intros He Hj Hlt. destruct (Z_le_gt_dec (2 ^ e) (2 ^ j)) as [Hle|Hgt]; [exact Hle|exfalso].
  assert (j < e) by (apply Z.nle_gt; intros Hc; apply (Z.pow_le_mono_r 2) in Hc; lia).
  assert (2 ^ (j + 1) <= 2 ^ e) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma SP_S_ok lim : 131072 <= lim -> lim <= 2 ^ 34 + 2 ^ 30 -> sink_policy_ok (SP_S lim).
Proof.
  intros Hlo Hhi. constructor; cbn.
  - intros; lia.
  - intros; lia.
  - intros; exact I.
  - intros c h Hcap Hfit _ _. split; [|destruct (c =? 0); lia].
    destruct Hcap as [->|(e & He & ->)]; [cbn; lia|].
    unfold cap_next. replace (2 ^ e =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (Z.pow_pos_nonneg 2 e); lia).
    pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) He) as Hp.
    pose proof (fits_le lim (2 ^ e) (Hfit Hp) Hlo) as Hle.
    assert (H34 : 2 ^ e <= 2 ^ 34).
    { apply (pow2_le_half e 34 He ltac:(lia)). change (2 ^ (34 + 1)) with (2 ^ 34 + 2 ^ 34). change (2 ^ 30) with 1073741824 in Hhi.
      change (2 ^ 34) with 17179869184 in *. lia. }
    change (2 ^ 35) with (2 * 2 ^ 34). lia.
  - unfold NREQ. lia.
  - lia.
Qed.

Lemma SP_T_ok j hb : 20 <= j -> 2 * 2 ^ j <= NREQ -> hb < 2 * 2 ^ j -> sink_policy_ok (SP_T (2 * 2 ^ j) hb).
Proof.
  intros Hj Hn HHB.
  pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) ltac:(lia)) as Hpj.
  assert (Hhalf : 2 * 2 ^ j / 2 = 2 ^ j) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
  assert (E21 : 2 ^ (j + 1) = 2 * 2 ^ j) by (rewrite Z.pow_add_r, Z.pow_1_r; lia).
  constructor; cbn -[Z.pow Z.div Z.mul cszR].
  - intros; apply cszR_nonneg.
  - intros c _ Hc _. rewrite Hhalf. pose proof (cszR_mono c (2 * 2 ^ j) ltac:(lia)). pose proof (cszR_nonneg (2 ^ j)). lia.
  - intros h h' Hh Hle. lia.
  - intros c h Hcap _ Hh Hle0. assert (Hle : c <= hb) by lia. rewrite Hhalf.
    destruct Hcap as [->|(e & He & ->)].
    + cbn -[Z.pow Z.mul cszR]. pose proof (cszR_mono 1 (2 ^ j) ltac:(lia)) as H1. pose proof (cszR_nonneg (2 * 2 ^ j)) as H2.
      split; [lia|]. lia.
    + unfold cap_next. replace (2 ^ e =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (Z.pow_pos_nonneg 2 e); lia).
      pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) He) as Hpe.
      assert (Hej : 2 ^ e <= 2 ^ j) by (apply (pow2_le_half e j He ltac:(lia)); rewrite E21; lia).
      pose proof (cszR_mono (2 ^ e) (2 ^ j) Hej) as Hm1. pose proof (cszR_mono (2 * 2 ^ e) (2 * 2 ^ j) ltac:(lia)) as Hm2.
      split; [lia|]. lia.
  - exact Hn.
  - rewrite Hhalf. pose proof (cszR_nonneg (2 ^ j)). pose proof (cszR_nonneg (2 * 2 ^ j)). lia.
Qed.
End Policies.

End PESK.
