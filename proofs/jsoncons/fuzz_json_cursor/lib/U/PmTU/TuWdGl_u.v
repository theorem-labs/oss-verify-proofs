(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLayout_u.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module TWG.
Section G.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variables SP o : Z.
Hypothesis SPR : hl_sptop L - 2 ^ 23 + 9600 <= SP /\ SP <= o /\ o + 24 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Definition inreg (a : Z) : Prop := (SP - 9600 <= a < SP) \/ (o <= a < o + 24).

Lemma heap_keep : forall LB cr M M' VM, hi_heap HI LB cr M VM ->
  (forall x : word, ~ inreg (bv_unsigned x) -> M' x = M x) -> (forall a, inreg a -> M' (Z_to_bv 64 a) <> None) ->
  hi_heap HI LB cr M' VM.
Proof.
  intros LB cr M M' VM HH Hf Hd. apply (hio_frame L SCFG HI HIok LB cr M M' VM HH).
  - intros a Ha HP. apply Hf. rewrite L5.unsigned_lit by lia. intros HR. unfold inreg in HR.
    destruct HP as [(P1 & _) | P]; [lia|]. apply (PmLayout.ly_ro L LAY) in P. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in P. lia.
  - intros x Hx. destruct (classic (inreg (bv_unsigned x))) as [HR|HR].
    + rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hd. exact HR.
    + rewrite (Hf x HR). exact Hx.
Qed.

Lemma hpres_comp : forall LB M m' M'', (forall b, In b LB -> fst b + snd b <= hl_ceil L) ->
  (forall x : word, ~ inreg (bv_unsigned x) -> m' x = M x) ->
  (forall a, SP - 400 <= a < SP -> m' (Z_to_bv 64 a) <> None) -> (forall a, o <= a < o + 24 -> m' (Z_to_bv 64 a) <> None) ->
  L5C.hpres L LB (SP - 400) 9200 [(o, 24)] m' M'' ->
  L5C.hpres L LB SP 9600 [(o, 24)] M M''.
Proof.
  intros LB M m' M'' HBL Hf Hfr Ho HP.
  assert (ERR : hl_errno L = 0xd675c) by exact (PmLayout.ly_errno L LAY).
  assert (ILO : hl_img_lo L = 0x10000) by exact (PmLayout.ly_img_lo L LAY). assert (IHI : hl_img_hi L = 0xf8000) by exact (PmLayout.ly_img_hi L LAY).
  apply L5C.hpres_intro.
  - intros a (Ka & KC & KE & KW). rewrite (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
    + apply Hf. rewrite L5.unsigned_lit by lia. intros HR. unfold inreg in HR.
      assert (Hoa : ~ (o <= a < o + 24)) by (intros Hin; exact (KW (o, 24) (or_introl eq_refl) Hin)).
      destruct KC as [(b & Hb & Hr) | [(C1 & C2) | (C1 & C2)]]; [| lia | lia].
      destruct HR as [HR|HR]; [|lia].
      pose proof (HBL b Hb). lia.
    + split; [exact Ka|]. split; [|split; [exact KE | exact KW]].
      destruct KC as [Hb | [(C1 & C2) | C]]; [left; exact Hb | right; left; split; [exact C1 | lia] | right; right; exact C].
  - intros j Hj. destruct (Z_lt_dec j 9200) as [Hlt|Hge].
    + replace (SP - 9600 + j) with (SP - 400 - 9200 + j) by lia. apply (L5C.hpres_defined _ _ _ _ _ _ _ HP). lia.
    + rewrite (L5C.hpres_kept _ _ _ _ _ _ _ (SP - 9600 + j) HP); [apply Hfr; lia|].
      split; [lia|]. split; [right; left; split; lia|]. split; [unfold in_errno; lia|].
      intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
  - intros a Ha HC HE Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP Ha); [| exact HE |].
    + destruct HC as [Hb | [(C1 & C2) | C]]; [left; exact Hb | right; left; split; [exact C1 | lia] | right; right; exact C].
    + destruct (classic (inreg a)) as [HR|HR].
      * destruct HR as [HR|HR]; [destruct HC as [(b & Hb & Hr) | [(C1 & C2) | C]]; [pose proof (HBL b Hb); lia | lia | lia] | apply Ho; lia].
      * pose proof (Hf (Z_to_bv 64 a)) as X. rewrite L5.unsigned_lit in X by lia. rewrite (X HR). exact Hd.
Qed.

Lemma errno_not_private : forall LB a, in_errno L a -> ~ alloc_private L LB a.
Proof.
  intros LB a HE HP. unfold in_errno in HE. rewrite (PmLayout.ly_errno L LAY) in HE.
  assert (ILO : hl_img_lo L = 0x10000) by exact (PmLayout.ly_img_lo L LAY). assert (IHI : hl_img_hi L = 0xf8000) by exact (PmLayout.ly_img_hi L LAY).
  destruct HP as [(P1 & P2 & P3) | P].
  - apply P3. split; [lia|]. intros HS. apply (PmLayout.ly_static L LAY) in HS. lia.
  - pose proof (PmLayout.ly_ro_img L LAY a P ltac:(lia)). lia.
Qed.
Lemma heap_keep_e : forall LB cr M M' VM, hi_heap HI LB cr M VM ->
  (forall x : word, ~ inreg (bv_unsigned x) -> ~ in_errno L (bv_unsigned x) -> M' x = M x) -> (forall a, inreg a -> M' (Z_to_bv 64 a) <> None) ->
  (forall a, in_errno L a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) ->
  hi_heap HI LB cr M' VM.
Proof.
  intros LB cr M M' VM HH Hf Hd He. apply (hio_frame L SCFG HI HIok LB cr M M' VM HH).
  - intros a Ha HP. destruct (classic (in_errno L a)) as [HE|HE]; [exfalso; exact (errno_not_private LB a HE HP)|].
    apply Hf; rewrite L5.unsigned_lit by lia; [|exact HE]. intros HR. unfold inreg in HR.
    destruct HP as [(P1 & _) | P]; [lia|]. apply (PmLayout.ly_ro L LAY) in P. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in P. lia.
  - intros x Hx. destruct (classic (inreg (bv_unsigned x))) as [HR|HR].
    + rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hd. exact HR.
    + destruct (classic (in_errno L (bv_unsigned x))) as [HE|HE].
      * rewrite <- (Z_to_bv_bv_unsigned _ x). apply He; [exact HE|]. rewrite (Z_to_bv_bv_unsigned _ x). exact Hx.
      * rewrite (Hf x HR HE). exact Hx.
Qed.
Lemma hpres_comp_e : forall LB M m' M'', (forall b, In b LB -> fst b + snd b <= hl_ceil L) ->
  (forall x : word, ~ inreg (bv_unsigned x) -> ~ in_errno L (bv_unsigned x) -> m' x = M x) ->
  (forall a, SP - 400 <= a < SP -> m' (Z_to_bv 64 a) <> None) -> (forall a, o <= a < o + 24 -> m' (Z_to_bv 64 a) <> None) ->
  L5C.hpres L LB (SP - 400) 9200 [(o, 24)] m' M'' ->
  L5C.hpres L LB SP 9600 [(o, 24)] M M''.
Proof.
  intros LB M m' M'' HBL Hf Hfr Ho HP.
  assert (ERR : hl_errno L = 0xd675c) by exact (PmLayout.ly_errno L LAY).
  assert (ILO : hl_img_lo L = 0x10000) by exact (PmLayout.ly_img_lo L LAY). assert (IHI : hl_img_hi L = 0xf8000) by exact (PmLayout.ly_img_hi L LAY).
  apply L5C.hpres_intro.
  - intros a (Ka & KC & KE & KW). rewrite (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
    + apply Hf; rewrite L5.unsigned_lit by lia; [|exact KE]. intros HR. unfold inreg in HR.
      assert (Hoa : ~ (o <= a < o + 24)) by (intros Hin; exact (KW (o, 24) (or_introl eq_refl) Hin)).
      destruct KC as [(b & Hb & Hr) | [(C1 & C2) | (C1 & C2)]]; [| lia | lia].
      destruct HR as [HR|HR]; [|lia].
      pose proof (HBL b Hb). lia.
    + split; [exact Ka|]. split; [|split; [exact KE | exact KW]].
      destruct KC as [Hb | [(C1 & C2) | C]]; [left; exact Hb | right; left; split; [exact C1 | lia] | right; right; exact C].
  - intros j Hj. destruct (Z_lt_dec j 9200) as [Hlt|Hge].
    + replace (SP - 9600 + j) with (SP - 400 - 9200 + j) by lia. apply (L5C.hpres_defined _ _ _ _ _ _ _ HP). lia.
    + rewrite (L5C.hpres_kept _ _ _ _ _ _ _ (SP - 9600 + j) HP); [apply Hfr; lia|].
      split; [lia|]. split; [right; left; split; lia|]. split; [unfold in_errno; lia|].
      intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
  - intros a Ha HC HE Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP Ha); [| exact HE |].
    + destruct HC as [Hb | [(C1 & C2) | C]]; [left; exact Hb | right; left; split; [exact C1 | lia] | right; right; exact C].
    + destruct (classic (inreg a)) as [HR|HR].
      * destruct HR as [HR|HR]; [destruct HC as [(b & Hb & Hr) | [(C1 & C2) | C]]; [pose proof (HBL b Hb); lia | lia | lia] | apply Ho; lia].
      * pose proof (Hf (Z_to_bv 64 a)) as X. rewrite L5.unsigned_lit in X by lia. rewrite (X HR HE). exact Hd.
Qed.
End G.
End TWG.
