(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
Module SO_shadow.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition SSZ_LO : Z := 0x10006fef8000.
Definition SSZ_HI : Z := 0x10007fff8000.

(* [comment removed for export] *)
Lemma SSZ_LO_le : SSZ_LO <= SH alloc_ceiling.
Proof. pose proof alloc_ceiling_range as R. unfold SH, SHADOW_OFFSET, SSZ_LO. Z.div_mod_to_equations. lia. Qed.
Lemma SSZ_ceil_lt : SH alloc_ceiling < SSZ_HI.
Proof. pose proof alloc_ceiling_range as R. unfold SH, SHADOW_OFFSET, SSZ_HI. Z.div_mod_to_equations. lia. Qed.
Lemma SSZ_HI_eq : SH (2^47) = SSZ_HI.
Proof. reflexivity. Qed.
Lemma SSZ_HI_KHIGH : SSZ_HI = KHIGHMEM_BEG.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition SBUF_LO : Z := 0x5fd900.
Definition SBUF_HI : Z := 0x5fddc0.
Definition SBZ_LO : Z := 0x800b7b20.   (* [comment removed for export] *)
Definition SBZ_HI : Z := 0x800b7bb8.   (* [comment removed for export] *)
Lemma SBZ_LO_eq : SH SBUF_LO = SBZ_LO. Proof. reflexivity. Qed.
Lemma SBZ_HI_eq : SH SBUF_HI = SBZ_HI. Proof. reflexivity. Qed.

Definition stack_shadow_zero (m : word -> option byte) : Prop :=
  sh_zero m alloc_ceiling (2^47) /\ sh_zero m SBUF_LO SBUF_HI.

(* [comment removed for export] *)
Lemma stack_shadow_zero_munch : forall W m m',
  stack_shadow_zero m -> munch W m m' ->
  Forall (fun iv => (snd iv <= SSZ_LO \/ SSZ_HI <= fst iv) /\ (snd iv <= 2148236064 \/ 2148236216 <= fst iv)) W ->
  stack_shadow_zero m'.
Proof.
  intros W m m' [H HB] MU HW. unfold stack_shadow_zero.
  assert (D : disjoint_from W SSZ_LO (SSZ_HI - SSZ_LO) /\ disjoint_from W SBZ_LO (SBZ_HI - SBZ_LO)).
  { clear H HB MU. induction W as [|[u v] W IH]; cbn; [split; exact I|].
    apply Forall_cons_iff in HW as [H1 HW]. cbn [fst snd] in H1. destruct (IH HW) as [IH1 IH2].
    unfold SSZ_LO, SSZ_HI, SBZ_LO, SBZ_HI in *. split; (split; [lia| assumption]). }
  destruct D as [D DB]. split.
  - pose proof SSZ_LO_le as LE. pose proof SSZ_ceil_lt as LT.
    eapply sh_zero_munch; [exact H| exact MU| unfold SSZ_LO in LE; lia| |].
    + unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia.
    + assert (E : SH (2^47 - 1) + 1 = SSZ_HI) by reflexivity. rewrite E.
      (* [comment removed for export] *)
      clear - D LE LT. induction W as [|[u v] W IH]; cbn in *; [exact I|]. destruct D as [D1 D2]. split; [lia| exact (IH D2)].
  - eapply sh_zero_munch; [exact HB| exact MU| rewrite SBZ_LO_eq; unfold SBZ_LO; lia| |].
    + unfold SH, SHADOW_OFFSET, SBUF_HI. Z.div_mod_to_equations. lia.
    + rewrite SBZ_LO_eq.
      assert (E : SH (SBUF_HI - 1) + 1 - SBZ_LO = SBZ_HI - SBZ_LO) by reflexivity. rewrite E. exact DB.
Qed.

(* [comment removed for export] *)
Lemma stack_part_ext : forall m m',
  sh_zero m alloc_ceiling (2^47) -> (forall a, SSZ_LO <= a < SSZ_HI -> m' (wa a) = m (wa a)) -> sh_zero m' alloc_ceiling (2^47).
Proof.
  intros m m' H E a Ha. pose proof (H a Ha) as S. unfold shb in *.
  rewrite E; [exact S|]. pose proof SSZ_LO_le as LE. rewrite <- SSZ_HI_eq.
  pose proof (SH_mono alloc_ceiling a (proj1 Ha)). pose proof (SH_lt_of a (2^47) ltac:(Z.div_mod_to_equations; lia)). unfold SSZ_LO in *. lia.
Qed.

(* [comment removed for export] *)
Lemma sh_zero_shadow_ok : forall m lo hi a n,
  sh_zero m lo hi -> lo + 64 <= a -> a + n + 64 <= hi -> 0 < n -> shadow_ok m a n.
Proof.
  intros m lo hi a n H Hlo Hhi Hn. split.
  - intros i Hi. exists 0. split; [apply (H (a + i)); lia| left; reflexivity].
  - intros j Hj.
    (* [comment removed for export] *)
    set (b := 8 * (j - SHADOW_OFFSET)).
    assert (Hb : lo <= b < hi).
    { subst b. unfold SH, SHADOW_OFFSET in Hj. unfold SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    pose proof (H b Hb) as S. unfold shb in S.
    replace (SH b) with j in S by (subst b; unfold SH; Z.div_mod_to_equations; lia).
    rewrite S. discriminate.
Qed.

Lemma stack_shadow_zero_shadow_ok : forall m a n,
  stack_shadow_zero m -> alloc_ceiling + 64 <= a -> a + n + 64 <= 2^47 -> 0 < n -> shadow_ok m a n.
Proof. intros m a n [H _] H1 H2 H3. eapply sh_zero_shadow_ok; eauto. Qed.

Lemma stack_shadow_zero_sh_zero : forall m lo hi,
  stack_shadow_zero m -> alloc_ceiling <= lo -> hi <= 2^47 -> sh_zero m lo hi.
Proof. intros m lo hi [H _] H1 H2. eapply sh_zero_sub; eauto. Qed.

(* [comment removed for export] *)
Lemma stack_shadow_zero_bufsh : forall m, stack_shadow_zero m -> sh_zero m SBUF_LO SBUF_HI.
Proof. intros m [_ H]. exact H. Qed.

(* [comment removed for export] *)
Lemma stdout_buf_shadow_ok : forall m a n,
  stack_shadow_zero m -> 0x5fd960 <= a -> a + n <= 0x5fdd60 -> 0 < n -> shadow_ok m a n.
Proof. intros m a n [_ H] H1 H2 H3. eapply sh_zero_shadow_ok; [exact H| unfold SBUF_LO; lia| unfold SBUF_HI; lia| exact H3]. Qed.


End CeilWrap.
End SO_shadow.

(* [comment removed for export] *)
From Stdlib Require NArith.
From Stdlib Require Permutation.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_traces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
Module CJ_print_lemmas.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_traces OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_app_split : forall m A cs1 cs2,
  rw_cells asegs m A (cs1 ++ cs2) -> rw_cells asegs m A cs1 /\ rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf HB] (W0 & W1 & W)].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 H2].
  rewrite cells_bytes_app in HB. apply bytes_at_app in HB. destruct HB as [B1 B2].
  rewrite (cells_bytes_length cs1 H1) in B2. rewrite cells_size_app, Nat2Z.inj_add in W1, W.
  pose proof (bytes_at_bound _ _ _ _ B1) as BB1.
  split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]); intros i Hi.
  - apply W. lia.
  - replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply W. lia.
Qed.

Lemma rw_cells_app_join : forall m A cs1 cs2,
  rw_cells asegs m A cs1 -> rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells asegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[H1 B1] (W0 & W1 & W)] [[H2 B2] (V0 & V1 & V)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 H1). exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))); [apply W; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply V. lia.
Qed.

Lemma rw_cells_recast : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pv_agree_refl : forall sp0 LR LF SP PB m, pv_agree sp0 LR LF SP PB m m.
Proof. intros. apply magree_refl. Qed.

Lemma pv_agree_trans : forall sp0 LR LF SP PB m1 m2 m3,
  pv_agree sp0 LR LF SP PB m1 m2 -> pv_agree sp0 LR LF SP PB m2 m3 -> pv_agree sp0 LR LF SP PB m1 m3.
Proof. intros. eapply magree_trans; eauto. Qed.

(* [comment removed for export] *)
Lemma pv_agree_weaken : forall sp0 LR LR' LF SP SP' PB m m',
  pv_agree sp0 LR LF SP PB m m' -> SP <= SP' -> (forall b, In b LR' -> In b LR) -> pv_agree sp0 LR' LF SP' PB m m'.
Proof.
  intros sp0 LR LR' LF SP SP' PB m m' H HS HL. eapply magree_mono; [exact H|]. cbv beta.
  intros a [Hc Hn]. split; [|exact Hn].
  destruct Hc as [Hc|[Hc|[(A & n & Hb & Hr)|[Hc|Hc]]]]; [left; lia| right; left; exact Hc| right; right; left| do 3 right; left; exact Hc| do 4 right; exact Hc].
  exists A, n. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma cj_client_addr_weaken : forall sp0 L LR LF SP SP' a,
  cj_client_addr sp0 LR LF SP a -> SP' <= SP -> (forall b, In b LR -> In b L) -> cj_client_addr sp0 L LF SP' a.
Proof.
  intros sp0 L LR LF SP SP' a Hc HS HL.
  destruct Hc as [Hc|[Hc|[(A & n & Hb & Hr)|[Hc|Hc]]]]; [left; lia| right; left; exact Hc| right; right; left| do 3 right; left; exact Hc| do 4 right; exact Hc].
  exists A, n. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma pv_agree_of_cj_pres : forall sp0 L LR LF SP SP' PB m m',
  cj_pres sp0 L LF SP' m m' -> SP' <= SP -> (forall b, In b LR -> In b L) -> pv_agree sp0 LR LF SP PB m m'.
Proof.
  intros sp0 L LR LF SP SP' PB m m' H HS HL a Ha [Hc _]. apply H; [exact Ha|]. eapply cj_client_addr_weaken; eauto.
Qed.

(* [comment removed for export] *)
Lemma pv_agree_of_munch2 : forall (AI : art_iface) sp0 SPB LBX LF TRS BB m0 mo g LR SP PB lo1 hi1 lo2 hi2 m1 m2,
  ART AI sp0 SPB LBX LF TRS BB m0 mo g -> (forall b, In b LR -> In b LBX) ->
  munch [(lo1, hi1); (lo2, hi2)] m1 m2 -> wmono asegs m1 m2 ->
  (hi1 <= lo1 \/ (PB <= lo1 /\ hi1 <= PB + 64) \/ (alloc_ceiling <= lo1 /\ hi1 <= SP)) ->
  (hi2 <= lo2 \/ (PB <= lo2 /\ hi2 <= PB + 64) \/ (alloc_ceiling <= lo2 /\ hi2 <= SP)) ->
  SP <= 2^47 -> sp0 <= 2^47 ->
  pv_agree sp0 LR LF SP PB m1 m2.
Proof.
  intros AI sp0 SPB LBX LF TRS BB m0 mo g LR SP PB lo1 hi1 lo2 hi2 m1 m2 HL HLR MU WM W1 W2 HSP HS0.
  eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha [Hc Hn].
  try rewrite alloc_ceiling_eq in W1, W2.
  enough (G : forall lo hi, (hi <= lo \/ (PB <= lo /\ hi <= PB + 64) \/ (alloc_ceiling <= lo /\ hi <= SP)) -> ~ (lo <= a < hi)).
  { cbn. split; [apply G; exact W1| split; [apply G; exact W2| exact I]]. }
  intros lo hi [W|[W|W]]; [lia| lia|].
  destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]].
  - lia.
  - pose proof (aclient_image_lt a Hi). lia.
  - pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ Hin)) as (_ & _ & _ & R4). try rewrite alloc_ceiling_eq in R4. lia.
  - pose proof (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & _ & HF1 & HF2 & _). try rewrite alloc_ceiling_eq in HF2.
    assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
    unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. Z.div_mod_to_equations. lia.
  - unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma pv_agree_hole : forall sp0 LR LF SP PB lo' hi' m1 m2,
  munch [(lo', hi')] m1 m2 -> wmono asegs m1 m2 -> PB <= lo' -> hi' <= PB + 64 -> pv_agree sp0 LR LF SP PB m1 m2.
Proof.
  intros sp0 LR LF SP PB lo' hi' m1 m2 MU WM Hlo Hhi.
  eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha [_ Hn]. cbn. split; [lia| exact I].
Qed.

Lemma pv_agree_stack : forall (AI : art_iface) sp0 SPB LBX LF TRS BB m0 mo g LR SP PB lo' hi' m1 m2,
  ART AI sp0 SPB LBX LF TRS BB m0 mo g -> (forall b, In b LR -> In b LBX) ->
  munch [(lo', hi')] m1 m2 -> wmono asegs m1 m2 -> alloc_ceiling <= lo' -> hi' <= SP -> SP <= 2^47 -> sp0 <= 2^47 ->
  pv_agree sp0 LR LF SP PB m1 m2.
Proof.
  intros AI sp0 SPB LBX LF TRS BB m0 mo g LR SP PB lo' hi' m1 m2 HL HLR MU WM Hlo Hhi HSP HS0.
  eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha [Hc Hn]. try rewrite alloc_ceiling_eq in Hlo.
  enough (G : ~ (lo' <= a < hi')) by (cbn; split; [exact G| exact I]).
  destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]].
  - lia.
  - pose proof (aclient_image_lt a Hi). lia.
  - pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ Hin)) as (_ & _ & _ & R4). try rewrite alloc_ceiling_eq in R4. lia.
  - pose proof (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & _ & HF1 & HF2 & _). try rewrite alloc_ceiling_eq in HF2.
    assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
    unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. Z.div_mod_to_equations. lia.
  - unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma u8arr_of_two_CB : forall mm A n1 b1 n2 b2,
  rw_cells asegs mm A [CB n1 b1; CB n2 b2] -> u8arr asegs mm A (b1 ++ b2) /\ length b1 = n1 /\ length b2 = n2.
Proof.
  intros mm A n1 b1 n2 b2 H.
  pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (L1 & L2 & _).
  pose proof (rw_cells_merge asegs mm A [] [CB n1 b1; CB n2 b2] [] ltac:(rewrite app_nil_r; exact H)) as M.
  cbn [app cells_size cells_bytes csize cbytes] in M. rewrite app_nil_r, Nat.add_0_r in M.
  split; [| split; [exact L1| exact L2]]. eapply u8arr_of_rw_cells. exact M.
Qed.

(* [comment removed for export] *)
Lemma pv_agree_rw_cells_stack : forall sp0 LR LF SP PB m m' A cs,
  pv_agree sp0 LR LF SP PB m m' -> rw_cells asegs m A cs -> SP <= A -> A + Z.of_nat (cells_size cs) <= Z.max (sp0 + 4096) (2^47) ->
  (A + Z.of_nat (cells_size cs) <= PB \/ PB + 64 <= A) ->
  rw_cells asegs m' A cs.
Proof.
  intros sp0 LR LF SP PB m m' A cs HP H HS HA HD.
  eapply rw_cells_magree; [exact HP| exact H|]. intros a Ha. split; [left; lia| lia].
Qed.

Lemma pv_agree_bytes_at_stack : forall sp0 LR LF SP PB m m' A bs,
  pv_agree sp0 LR LF SP PB m m' -> bytes_at asegs m A bs -> SP <= A -> A + Z.of_nat (length bs) <= Z.max (sp0 + 4096) (2^47) ->
  (A + Z.of_nat (length bs) <= PB \/ PB + 64 <= A) ->
  bytes_at asegs m' A bs.
Proof.
  intros sp0 LR LF SP PB m m' A bs HP H HS HA HD.
  eapply bytes_at_magree; [exact HP| exact H|]. intros a Ha. split; [left; lia| lia].
Qed.

Lemma pv_agree_stk : forall sp0 LR LF SP PB m m' lo hi,
  pv_agree sp0 LR LF SP PB m m' -> stk asegs m lo hi -> SP <= lo -> hi <= Z.max (sp0 + 4096) (2^47) -> (hi <= PB \/ PB + 64 <= lo) -> stk asegs m' lo hi.
Proof.
  intros sp0 LR LF SP PB m m' lo hi HP ST HS Hh HD. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(split; [left; lia| lia])) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma pv_agree_rw_cells_block : forall (AI : art_iface) sp0 SPB LBX LF TRS BB m0 mo g LR SP PB m m' A cs B k,
  ART AI sp0 SPB LBX LF TRS BB m0 mo g -> In (B, k) LBX ->
  pv_agree sp0 LR LF SP PB m m' -> rw_cells asegs m A cs -> In (B, k) LR -> B <= A -> A + Z.of_nat (cells_size cs) <= B + k ->
  alloc_ceiling <= PB ->
  rw_cells asegs m' A cs.
Proof.
  intros AI sp0 SPB LBX LF TRS BB m0 mo g LR SP PB m m' A cs B k HL HinX HP H Hin H1 H2 HPB.
  pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL HinX) as (_ & _ & _ & R4).
  eapply rw_cells_magree; [exact HP| exact H|]. intros a Ha. split; [| lia].
  right; right; left. exists B, k. split; [exact Hin| lia].
Qed.

Lemma pv_agree_bytes_at_block : forall (AI : art_iface) sp0 SPB LBX LF TRS BB m0 mo g LR SP PB m m' A bs B k,
  ART AI sp0 SPB LBX LF TRS BB m0 mo g -> In (B, k) LBX ->
  pv_agree sp0 LR LF SP PB m m' -> bytes_at asegs m A bs -> In (B, k) LR -> B <= A -> A + Z.of_nat (length bs) <= B + k ->
  alloc_ceiling <= PB ->
  bytes_at asegs m' A bs.
Proof.
  intros AI sp0 SPB LBX LF TRS BB m0 mo g LR SP PB m m' A bs B k HL HinX HP H Hin H1 H2 HPB.
  pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL HinX) as (_ & _ & _ & R4).
  eapply bytes_at_magree; [exact HP| exact H|]. intros a Ha. split; [| lia].
  right; right; left. exists B, k. split; [exact Hin| lia].
Qed.

Lemma pv_agree_cj_chain : forall (AI : art_iface) sp0 SPB LBX LF TRS BB m0 mo g LR SP PB m m' T d p B,
  ART AI sp0 SPB LBX LF TRS BB m0 mo g -> (forall b, In b B -> In b LBX) ->
  pv_agree sp0 LR LF SP PB m m' -> cj_chain T m d p B -> (forall b, In b B -> In b LR) -> alloc_ceiling <= PB ->
  cj_chain T m' d p B.
Proof.
  intros AI sp0 SPB LBX LF TRS BB m0 mo g LR SP PB m m' T d p B HL HBX HP CH HB HPB.
  eapply cj_chain_magree; [exact CH| exact HP|]. intros a (A & n & Hin & Hr). split.
  - right; right; left. exists A, n. split; [apply HB; exact Hin| exact Hr].
  - pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HBX _ Hin)) as (_ & _ & _ & R4). lia.
Qed.

Lemma pv_agree_cj_str : forall (AI : art_iface) sp0 SPB LBX LF TRS BB m0 mo g LR SP PB m m' s B,
  ART AI sp0 SPB LBX LF TRS BB m0 mo g -> (forall b, In b B -> In b LBX) ->
  pv_agree sp0 LR LF SP PB m m' -> cj_str m s B -> (forall b, In b B -> In b LR) -> alloc_ceiling <= PB ->
  cj_str m' s B.
Proof.
  intros AI sp0 SPB LBX LF TRS BB m0 mo g LR SP PB m m' s B HL HBX HP CS HB HPB.
  eapply cj_str_magree; [exact HP| exact CS|]. intros a (A & n & Hin & Hr). split.
  - right; right; left. exists A, n. split; [apply HB; exact Hin| exact Hr].
  - pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HBX _ Hin)) as (_ & _ & _ & R4). lia.
Qed.

(* [comment removed for export] *)
Lemma cj_pres_of_pv_agree : forall (AI : art_iface) sp0 SPB LBX LF TRS BB m0 mo g LR SP SP' PB m m',
  ART AI sp0 SPB LBX LF TRS BB m0 mo g -> (forall b, In b LR -> In b LBX) ->
  pv_agree sp0 LR LF SP PB m m' -> SP <= SP' -> PB + 64 <= SP' -> alloc_ceiling <= PB ->
  cj_pres sp0 LR LF SP' m m'.
Proof.
  intros AI sp0 SPB LBX LF TRS BB m0 mo g LR SP SP' PB m m' HL HLR HP HS HPB HC a Ha Hc.
  apply HP; [exact Ha|]. split; [eapply cj_client_addr_weaken; [exact Hc| exact HS| intros b Hb; exact Hb]|].
  try rewrite alloc_ceiling_eq in HC.
  destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]].
  - lia.
  - pose proof (aclient_image_lt a Hi). lia.
  - pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ Hin)) as (_ & _ & _ & R4). try rewrite alloc_ceiling_eq in R4. lia.
  - pose proof (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & _ & HF1 & HF2 & _). try rewrite alloc_ceiling_eq in HF2.
    assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
    unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. Z.div_mod_to_equations. lia.
  - unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma pb_below_pv_agree : forall sp0 LR LF SP PB m m',
  pv_agree sp0 LR LF SP PB m m' -> pb_below m PB -> SP + 16 <= PB -> PB <= Z.max (sp0 + 4096) (2^47) -> pb_below m' PB.
Proof.
  intros sp0 LR LF SP PB m m' HP (w1 & w2 & BY & Hw) HS HPB. exists w1, w2. split; [| exact Hw].
  eapply pv_agree_bytes_at_stack; [exact HP| exact BY| lia| |]; rewrite length_app, !length_le8; cbn; lia.
Qed.

Lemma pb_below_munch : forall W m m' PB,
  pb_below m PB -> munch W m m' -> disjoint_from W (PB - 16) 16 -> pb_below m' PB.
Proof.
  intros W m m' PB (w1 & w2 & BY & Hw) MU HD. exists w1, w2. split; [| exact Hw].
  eapply bytes_at_transport; [exact BY| exact MU|]. rewrite length_app, !length_le8. exact HD.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sh_zero_stack_cj_pres : forall sp0 LB LF SP m m',
  cj_pres sp0 LB LF SP m m' -> sh_zero m alloc_ceiling (2^47) -> sh_zero m' alloc_ceiling (2^47).
Proof.
  intros sp0 LB LF SP m m' HP H. eapply sh_zero_ext; [exact H|]. intros j Hj.
  assert (R : SH alloc_ceiling <= j < SH (2^47)).
  { unfold SH, SHADOW_OFFSET in *. rewrite ?alloc_ceiling_eq in *. Z.div_mod_to_equations. lia. }
  pose proof R as R'. unfold SH, SHADOW_OFFSET in R'. rewrite ?alloc_ceiling_eq in R'.
  apply HP; [Z.div_mod_to_equations; lia|]. do 4 right. exact R.
Qed.

Lemma sh_zero_stack_pv_agree : forall sp0 LR LF SP PB m m',
  pv_agree sp0 LR LF SP PB m m' -> alloc_ceiling <= PB -> sh_zero m alloc_ceiling (2^47) -> sh_zero m' alloc_ceiling (2^47).
Proof.
  intros sp0 LR LF SP PB m m' HP HPB H. eapply sh_zero_ext; [exact H|]. intros j Hj.
  assert (R : SH alloc_ceiling <= j < SH (2^47)).
  { unfold SH, SHADOW_OFFSET in *. rewrite ?alloc_ceiling_eq in *. Z.div_mod_to_equations. lia. }
  pose proof R as R'. unfold SH, SHADOW_OFFSET in R'. rewrite ?alloc_ceiling_eq in R'. try rewrite alloc_ceiling_eq in HPB.
  apply HP; [Z.div_mod_to_equations; lia|]. split; [do 4 right; exact R|]. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma sh_zero_stack_munch : forall W m m',
  sh_zero m alloc_ceiling (2^47) -> munch W m m' -> Forall (fun iv => sclr (fst iv) (snd iv - fst iv)) W -> sh_zero m' alloc_ceiling (2^47).   (* [comment removed for export] *)
Proof.
  intros W m m' H MU HW.
  eapply sh_zero_munch; [exact H| exact MU| unfold SH, SHADOW_OFFSET; try rewrite alloc_ceiling_eq; Z.div_mod_to_equations; lia
                       | unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia|].
  clear H MU. induction W as [|[u v] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. cbn [fst snd] in H1.
  split; [| apply IH; exact H2]. clear IH H2. pose proof SH_ceiling_bounds as (SHC1 & SHC2 & SHC3).
  assert (E47 : SH (2 ^ 47 - 1) + 1 = KHIGHMEM_BEG) by reflexivity. rewrite E47. clear E47.
  unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. destruct H1 as [H1|H1]; [right| left]; lia.
Qed.

(* [comment removed for export] *)
Lemma stack_shb0 : forall m a, sh_zero m alloc_ceiling (2^47) -> alloc_ceiling <= a < 2^47 -> shb m a 0.
Proof. intros m a H Ha. eapply sh_zero_shb; [exact H| exact Ha]. Qed.

Lemma stack_shchk : forall m a k, sh_zero m alloc_ceiling (2^47) -> alloc_ceiling <= a < 2^47 -> shchk m a k.
Proof. intros m a k H Ha. eapply sh_zero_shchk; [exact H| exact Ha]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma KRE_eq : KRE = 2166912.   (* [comment removed for export] *)
Proof. reflexivity. Qed.
Lemma INT_MAX_eq : INT_MAX = 2147483647.
Proof. reflexivity. Qed.
Lemma PB_FAIL_eq : PB_FAIL = 2^33 + 2166912 + 64.
Proof. reflexivity. Qed.

Lemma cost_realloc_le : forall n, 0 <= n -> cost_realloc n <= 4 * n + KRE.
Proof. intros n Hn. unfold cost_realloc, KRE. rewrite cost_free_eq. pose proof (cost_malloc_le4 n Hn). lia. Qed.

Lemma log2_succ_nonneg : forall len, 0 <= Z.log2 (len + 1).
Proof. intros. apply Z.log2_nonneg. Qed.

Lemma pb_pot_mono : forall a b, 0 <= a <= b -> b <= INT_MAX -> pb_pot a <= pb_pot b.
Proof.
  intros a b Hab Hb. unfold pb_pot. rewrite KRE_eq, INT_MAX_eq in *.
  pose proof (Z.log2_le_mono (a + 1) (b + 1) ltac:(lia)).
  destruct (Z.eqb_spec a 2147483647); destruct (Z.eqb_spec b 2147483647); lia.
Qed.

Lemma pb_pot_nonneg : forall a, 0 <= a -> 0 <= pb_pot a.
Proof.
  intros a Ha. unfold pb_pot. rewrite KRE_eq, INT_MAX_eq. pose proof (Z.log2_nonneg (a + 1)).
  destruct (Z.eqb_spec a 2147483647); lia.
Qed.

(* [comment removed for export] *)
Lemma pb_pot_grow : forall len len', 0 <= len -> len < len' <= INT_MAX -> (2 * len + 2 <= len' \/ len' = INT_MAX) ->
  cost_realloc len' <= pb_pot len' - pb_pot len.
Proof.
  intros len len' H0 H1 HG. pose proof (cost_realloc_le len' ltac:(lia)) as CR. unfold pb_pot. rewrite KRE_eq, INT_MAX_eq in *.
  pose proof (Z.log2_le_mono (len + 1) (len' + 1) ltac:(lia)) as LM.
  pose proof (Z.log2_nonneg (len + 1)) as L0.
  destruct (Z.eqb_spec len 2147483647) as [E|NE]; [lia|].
  destruct HG as [HG|HG].
  - pose proof (Z.log2_le_mono (2 * (len + 1)) (len' + 1) ltac:(lia)) as LM2.
    rewrite (Z.log2_double (len + 1)) in LM2 by lia.
    destruct (Z.eqb_spec len' 2147483647); lia.
  - subst len'. rewrite Z.eqb_refl. lia.
Qed.

Lemma pb_allow_ge_fail : forall len, 0 <= len <= INT_MAX -> PB_FAIL <= pb_allow len.
Proof. intros len H. unfold pb_allow. pose proof (pb_pot_mono len INT_MAX ltac:(lia) ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma pb_allow_grow : forall len len' B B', B - (pb_pot len' - pb_pot len) <= B' -> pb_allow len <= B -> pb_allow len' <= B'.
Proof. intros len len' B B' H1 H2. unfold pb_allow in *. lia. Qed.

Lemma pb_npot_mono : forall a b, 0 <= a <= b -> b <= INT_MAX -> pb_npot a <= pb_npot b.
Proof.
  intros a b Hab Hb. unfold pb_npot. rewrite INT_MAX_eq in *.
  pose proof (Z.log2_le_mono (a + 1) (b + 1) ltac:(lia)).
  destruct (Z.eqb_spec a 2147483647); destruct (Z.eqb_spec b 2147483647); lia.
Qed.

Lemma pb_npot_grow : forall len len', 0 <= len -> len < len' <= INT_MAX -> (2 * len + 2 <= len' \/ len' = INT_MAX) ->
  1 <= pb_npot len' - pb_npot len.
Proof.
  intros len len' H0 H1 HG. unfold pb_npot. rewrite INT_MAX_eq in *.
  pose proof (Z.log2_le_mono (len + 1) (len' + 1) ltac:(lia)) as LM.
  destruct (Z.eqb_spec len 2147483647) as [E|NE]; [lia|].
  destruct HG as [HG|HG].
  - pose proof (Z.log2_le_mono (2 * (len + 1)) (len' + 1) ltac:(lia)) as LM2.
    rewrite (Z.log2_double (len + 1)) in LM2 by lia.
    destruct (Z.eqb_spec len' 2147483647); lia.
  - subst len'. rewrite Z.eqb_refl. lia.
Qed.

Lemma pb_npallow_ge2 : forall len, 0 <= len <= INT_MAX -> 2 <= pb_npallow len.
Proof. intros len H. unfold pb_npallow. pose proof (pb_npot_mono len INT_MAX ltac:(lia) ltac:(lia)). lia. Qed.

Lemma pb_npallow_grow : forall len len' np np' M,
  np' <= np + (pb_npot len' - pb_npot len) -> np + pb_npallow len <= M -> np' + pb_npallow len' <= M.
Proof. intros. unfold pb_npallow in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma uwt_frame16 : forall m lo top pc0 prev f k (w1 w2 : word),
  bytes_at asegs m (f - 16) (le8 w1 ++ le8 w2) -> bv_unsigned w1 <= f -> lo + 16 <= f -> 0 <= k ->
  exists tl, uwt m lo top pc0 prev f k tl.
Proof.
  intros m lo top pc0 prev f k w1 w2 BY Hw1 Hlo Hk.
  destruct (Z.le_gt_cases f prev) as [C1|C1]; [exists []; apply uwt_stop; left; exact C1|].
  destruct (Z.eq_dec (f mod 8) 0) as [C2|C2]; [| exists []; apply uwt_stop; right; left; exact C2].
  destruct (Z.le_gt_cases (top - 16) f) as [C3|C3]; [exists []; apply uwt_stop; right; right; left; exact C3|].
  destruct (Z.le_gt_cases TRACE_MAX_LEN k) as [C4|C4]; [exists []; apply uwt_stop; right; right; right; exact C4|].
  destruct (Z.lt_ge_cases (bv_unsigned w2) 4096) as [C5|C5].
  - exists []. eapply uwt_lowpc; [exact C1| exact C2| lia| lia| exact Hlo| exact BY| exact C5].
  - eexists. eapply uwt_hop; [exact C1| exact C2| lia| lia| exact Hlo| exact BY| lia|].
    apply uwt_stop. left. exact Hw1.
Qed.

(* [comment removed for export] *)
Lemma uwt_hook_frame16 : forall m sp top pc0 f (w1 w2 : word),
  bytes_at asegs m (f - 16) (le8 w1 ++ le8 w2) -> bv_unsigned w1 <= f -> sp + 16 <= f ->
  exists tl, uwt m sp top pc0 sp f 2 tl.
Proof. intros. eapply uwt_frame16; eauto. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cj_pres_munch_below : forall (AI : art_iface) sp0 SPB LB LF TRS BB m0 mo g (L : list cblock) SP W m1 m2,
  ART AI sp0 SPB LB LF TRS BB m0 mo g -> (forall b, In b L -> In b LB) ->
  munch W m1 m2 -> wmono asegs m1 m2 ->
  Forall (fun iv => alloc_ceiling <= fst iv /\ snd iv <= SP) W -> SP <= 2^47 -> sp0 <= 2^47 ->
  cj_pres sp0 L LF SP m1 m2.
Proof.
  intros AI sp0 SPB LB LF TRS BB m0 mo g L SP W m1 m2 HL HLB MU WM HW HSP HS0 a Ha Hc.
  split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha.
  assert (G : forall lo hi, alloc_ceiling <= lo /\ hi <= SP -> ~ (lo <= a < hi)).
  { intros lo hi [H1 H2]. try rewrite alloc_ceiling_eq in H1.
    destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]].
    - lia.
    - pose proof (aclient_image_lt a Hi). lia.
    - pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLB _ Hin)) as (_ & _ & _ & R4). try rewrite alloc_ceiling_eq in R4. lia.
    - pose proof (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & _ & HF1 & HF2 & _). try rewrite alloc_ceiling_eq in HF2.
      assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
      unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. Z.div_mod_to_equations. lia.
    - unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
  clear MU WM Hc. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. cbn [fst snd] in H1.
  cbn. split; [apply G; exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bytes_of_present : forall m E (k : nat),
  0 <= E -> E + Z.of_nat k <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat k -> m (wa (E + i)) <> None) ->
  exists bs, length bs = k /\ bytes_at asegs m E bs.
Proof.
  intros m E k HE HK H.
  assert (G : forall j, (j <= k)%nat -> exists bs, length bs = j /\ forall i, (i < j)%nat -> mrd asegs m (wa (E + Z.of_nat i)) = nth_error bs i).
  { induction j as [|j IH]; intros Hj.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (m (wa (E + Z.of_nat j))) as [b|] eqn:Eb; [| exfalso; apply (H (Z.of_nat j)); [lia| exact Eb]].
      exists (bs ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi. destruct (Nat.eqb_spec i j).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. cbn. unfold mrd. rewrite Eb. reflexivity.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G k ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [rewrite Hlen; lia|]. intros i Hi. apply Hbs. lia.
Qed.

(* [comment removed for export] *)
Lemma block_slack_bytes : forall (AI : art_iface) sp0 SPB LB LF TRS B m mo g D n E,
  ART AI sp0 SPB LB LF TRS B m mo g -> In (D, n) LB -> D <= E <= D + n ->
  exists slack, bytes_at asegs m E slack /\ Z.of_nat (length slack) = (- E) mod 8.
Proof.
  intros AI sp0 SPB LB LF TRS B m mo g D n E HL HIN HE.
  pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL HIN) as (R1 & R2 & R3 & R4). try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1.
  pose proof (art_block_wr AI _ _ _ _ _ _ _ _ _ _ _ HL HIN) as (_ & _ & WR).
  destruct (bytes_of_present m E (Z.to_nat ((- E) mod 8)) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (bs & Hlen & HB).
  2:{ exists bs. split; [exact HB| lia]. }
  intros i Hi. destruct (Z.lt_ge_cases (E + i) (D + n)) as [LT|GE].
  - intros Hm. apply (WR (E + i - D) ltac:(lia)). replace (D + (E + i - D)) with (E + i) by lia.
    unfold wview. rewrite Hm.
    rewrite (find_segment_noseg asegs (wa (E + i)) 1); [reflexivity| | lia].
    apply rt_noseg_high. rewrite wa_unsigned by lia. unfold AIMG_HI. lia.
  - replace (E + i) with (D + n + (E + i - (D + n))) by lia. eapply (art_block_slack AI); [exact HL| exact HIN| lia|].
    unfold roundup. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma first_nul : forall (bs : list byte) (off K : Z),
  0 <= off -> 0 <= K -> nth_error bs (Z.to_nat (off + K)) = Some (wb 0) ->
  exists str0 rest, skipn (Z.to_nat off) bs = str0 ++ wb 0 :: rest /\ ~ In (wb 0) str0 /\ Z.of_nat (length str0) <= K.
Proof.
  intros bs off K Hoff HK HN.
  set (tl := skipn (Z.to_nat off) bs).
  assert (HT : nth_error tl (Z.to_nat K) = Some (wb 0)). { unfold tl. rewrite nth_error_skipn. rewrite <- HN. f_equal. lia. }
  destruct (find_byte 0 tl) as [i|] eqn:FB.
  - destruct (find_byte_Some _ _ _ FB) as (Hi & (b & Hb & Hb0) & Hmin).
    destruct (nth_error_split _ _ _ Hb) as (pre & post & E & Hlen).
    exists pre, post. assert (Eb : b = wb 0) by (apply bv_eq; rewrite Hb0; reflexivity). subst b.
    split; [exact E|]. split.
    + intros Hin. apply In_nth_error in Hin. destruct Hin as [j Hj].
      assert (Hjl : (j < length pre)%nat) by (apply (proj1 (nth_error_Some pre j)); rewrite Hj; discriminate).
      apply (Hmin j (wb 0) ltac:(lia)); [| reflexivity]. rewrite E. rewrite nth_error_app1 by exact Hjl. exact Hj.
    + destruct (Nat.le_gt_cases i (Z.to_nat K)) as [LE|GT]; [subst i; lia|]. exfalso. apply (Hmin (Z.to_nat K) (wb 0) GT HT). reflexivity.
  - exfalso. exact (find_byte_None _ _ FB _ _ HT eq_refl).
Qed.

Lemma pad_reaches : forall X E, X <= E -> (- X) mod 8 <= (E - X) + (- E) mod 8.
Proof. intros X E H. Z.div_mod_to_equations. lia. Qed.

Section StrlenOff.
  Variable AI : art_iface.
  Hypothesis STRLEN : strlen_icpt_spec.

  Definition strlen_off_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (bs : list byte) (len off lo : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (k : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - ASTRFN_STACK, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ 0 <= k /\ off + k < len /\ nth_error bs (Z.to_nat (off + k)) = Some (wb 0).

  (* [comment removed for export] *)
  Lemma strlen_off_ok : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
      (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (BB : Z) (buf len off : Z) (bs : list byte) (lo : Z),
    ART AI sp0 SPB LB LF TRS BB m mo g -> In (buf, len) LB -> u8arr asegs m buf bs -> Z.of_nat (length bs) = len -> len < 2^40 ->
    0 <= off -> pb_nul bs len off -> mem_inv asegs m ->
    stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + ASTRFN_STACK <= bv_unsigned sp ->
    a0 = Z_to_bv 64 (buf + off) ->
    evt asegs (strlen_off_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bs len off lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASTRLEN_T) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros HL HIN ARR LEN L40 OFF (K & K0 & K1 & KN) MI ST CEIL LOS A0.
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL HIN) as (R1 & R2 & R3 & R4). try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1.
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'.
    destruct (first_nul bs off K OFF K0 KN) as (str0 & rest & E & NONUL & LS).
    destruct ARR as [BA WR].
    (* [comment removed for export] *)
    assert (BT : bytes_at asegs m (buf + off) (str0 ++ wb 0 :: rest)).
    { rewrite <- E. rewrite <- (firstn_skipn (Z.to_nat off) bs) in BA. apply bytes_at_app in BA. destruct BA as [_ BA].
      rewrite firstn_length_le in BA by lia. rewrite Z2Nat.id in BA by lia. exact BA. }
    assert (LT : off + Z.of_nat (length str0) + 1 + Z.of_nat (length rest) = len).
    { pose proof (f_equal (@length byte) E) as LE. rewrite length_skipn, length_app in LE. cbn [length] in LE. lia. }
    (* [comment removed for export] *)
    destruct (block_slack_bytes AI _ _ _ _ _ _ _ _ _ buf len (buf + len) HL HIN ltac:(lia)) as (pad & BP & LP).
    assert (BT2 : bytes_at asegs m (buf + off) ((str0 ++ wb 0 :: rest) ++ pad)).
    { apply bytes_at_app. split; [exact BT|]. rewrite length_app. cbn [length]. replace (buf + off + Z.of_nat (length str0 + S (length rest))) with (buf + len) by lia. exact BP. }
    rewrite <- app_assoc in BT2. cbn [app] in BT2. change (wb 0) with (Z_to_bv 8 0) in BT2, NONUL.
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL HIN) as SO.
    subst a0.
    eapply evt_cut.
    { pose proof STRLEN as SL. unfold strlen_icpt_spec in SL.
      eapply SL with (lo := lo) (s := buf + off) (str := str0) (slack := rest ++ pad); clear SL; rewrite ?unsigned_lit by lia;
        first [ lazymatch goal with |- icpt_cells _ => eapply (art_icpt_cells AI); exact HL end | exact MI | exact ST | reflexivity | exact BT2 | exact NONUL
              | rewrite length_app; pose proof (pad_reaches (buf + off + Z.of_nat (length str0) + 1) (buf + len) ltac:(lia)); lia
              | app_rng AI
              | eapply shadow_ok_sub; [exact SO| lia| lia| lia]
              | left; rewrite length_app; Z.div_mod_to_equations; lia
              | lia ]. }
    cbv beta. intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & _ & ST').
    apply evt_done. unfold strlen_off_post. exists (Z.of_nat (length str0)). do 15 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [lia|]. split; [lia|].
    rewrite <- (firstn_skipn (Z.to_nat off) bs), E. rewrite nth_error_app2 by (rewrite firstn_length_le; lia).
    rewrite firstn_length_le by lia. replace (Z.to_nat (off + Z.of_nat (length str0)) - Z.to_nat off)%nat with (length str0) by lia.
    rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
  Qed.
End StrlenOff.


End CeilWrap.
End CJ_print_lemmas.

(* [comment removed for export] *)
Module CJ_print_lemmas2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow SO_shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import Stdlib.Sorting.Permutation.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma sh_zero_shadow_ok64 : forall m lo hi a n,
  sh_zero m lo hi -> hi mod 64 = 0 -> lo + 64 <= a -> a + n <= hi -> 0 < n -> shadow_ok m a n.
Proof.
  intros m lo hi a n H H64 Hlo Hhi Hn. split.
  - intros i Hi. exists 0. split; [apply (H (a + i)); lia| left; reflexivity].
  - intros j Hj.
    set (b := 8 * (j - SHADOW_OFFSET)).
    assert (Hb : lo <= b < hi).
    { subst b. unfold SH, SHADOW_OFFSET in Hj. unfold SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    pose proof (H b Hb) as S. unfold shb in S.
    replace (SH b) with j in S by (subst b; unfold SH; Z.div_mod_to_equations; lia).
    rewrite S. discriminate.
Qed.

Lemma stack_shadow_ok : forall m a n,
  sh_zero m alloc_ceiling (2^47) -> alloc_ceiling + 64 <= a -> a + n <= 2^47 -> 0 < n -> shadow_ok m a n.
Proof. intros m a n H H1 H2 H3. apply (sh_zero_shadow_ok64 m alloc_ceiling (2^47) a n H eq_refl H1 H2 H3). Qed.

Definition pvw_ok (PB SP B k : Z) (iv : Z * Z) : Prop :=
  snd iv <= fst iv \/ (PB <= fst iv /\ snd iv <= PB + 64) \/ (alloc_ceiling <= fst iv /\ snd iv <= SP) \/ (B <= fst iv /\ snd iv <= B + k).

Lemma pv_agree_of_munchW : forall (AI : art_iface) sp0 SPB LBX LF TRS BB m0 mo g LR SP PB B k W m1 m2,
  ART AI sp0 SPB LBX LF TRS BB m0 mo g -> Permutation ((B, k) :: LR) LBX ->
  munch W m1 m2 -> wmono asegs m1 m2 -> Forall (pvw_ok PB SP B k) W ->
  alloc_ceiling <= SP -> SP <= 2^47 -> sp0 <= 2^47 ->
  pv_agree sp0 LR LF SP PB m1 m2.
Proof.
  intros AI sp0 SPB LBX LF TRS BB m0 mo g LR SP PB B k W m1 m2 HL HP MU WM HW CSP HSP HS0.
  eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha [Hc Hn].
  pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as (R1 & _ & _ & R4).
  (* [comment removed for export] *)
  pose proof (ablk_disj_band _ _ (art_block_band AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP))) as BND.
  unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in BND.
  unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. try rewrite alloc_ceiling_eq in R4.
  assert (G : forall lo hi, pvw_ok PB SP B k (lo, hi) -> ~ (lo <= a < hi)).
  { intros lo hi [W0|[W0|[W0|W0]]]; cbn [fst snd] in W0; [lia| lia| |].
    - try rewrite alloc_ceiling_eq in W0.
      destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & kk & Hin & Hr)|Hsh]]]].
      + lia.
      + pose proof (aclient_image_lt a Hi). lia.
      + pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) as (_ & _ & _ & X4).
        try rewrite alloc_ceiling_eq in X4. lia.
      + pose proof (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & _ & HF1 & HF2 & _). try rewrite alloc_ceiling_eq in HF2.
        assert (fsz kk = 128 \/ fsz kk = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
        unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. Z.div_mod_to_equations. lia.
      + unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia.
    - destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & kk & Hin & Hr)|Hsh]]]].
      + try rewrite alloc_ceiling_eq in *. lia.
      + pose proof (aclient_image_lt a Hi). lia.
      + destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. lia.
      + pose proof (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & _ & HF1 & HF2 & _ & _ & _ & FD).
        destruct (FD B k (perm_in_head _ _ _ HP)) as [X|X];
          assert (fsz kk = 128 \/ fsz kk = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity);
          unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; Z.div_mod_to_equations; lia.
      + unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
  clear MU WM Hc. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2].
  cbn. split; [apply G; exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u8arr_split3 : forall m A bs (k n : nat),
  u8arr asegs m A bs -> (k + n <= length bs)%nat ->
  u8arr asegs m A (firstn k bs)
  /\ rw_cells asegs m (A + Z.of_nat k) [CB n (firstn n (skipn k bs))]
  /\ u8arr asegs m (A + Z.of_nat k + Z.of_nat n) (skipn (k + n) bs).
Proof.
  intros m A bs k n [BA WR] Hkn.
  rewrite <- (firstn_skipn k bs) in BA. apply bytes_at_app in BA. destruct BA as [BA1 BA2].
  rewrite firstn_length_le in BA2 by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in BA2. apply bytes_at_app in BA2. destruct BA2 as [BA2 BA3].
  rewrite firstn_length_le in BA3 by (rewrite skipn_length; lia). rewrite skipn_skipn in BA3.
  destruct WR as (W0 & W1 & W).
  split; [|split].
  - split; [exact BA1|]. split; [lia|]. split; [rewrite firstn_length_le by lia; lia|]. intros i Hi. apply W. rewrite firstn_length_le in Hi by lia. lia.
  - split; [split; [cbn; rewrite firstn_length_le by (rewrite skipn_length; lia); auto|]|].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BA2.
    + cbn [cells_size Cells.csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply W. lia.
  - split; [rewrite Nat.add_comm; exact BA3|]. split; [lia|]. rewrite skipn_length. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat k + Z.of_nat n + i) with (A + (Z.of_nat k + Z.of_nat n + i)) by lia. apply W. lia.
Qed.

Lemma u8arr_join3 : forall m A pre n mid suf,
  u8arr asegs m A pre -> rw_cells asegs m (A + Z.of_nat (length pre)) [CB n mid] -> u8arr asegs m (A + Z.of_nat (length pre) + Z.of_nat n) suf ->
  u8arr asegs m A (pre ++ mid ++ suf) /\ length mid = n.
Proof.
  intros m A pre n mid suf [B1 W1] RW [B3 W3].
  pose proof RW as [[Hwf B2] W2]. cbn in Hwf. destruct Hwf as [Ln _].
  cbn [cells_bytes cbytes] in B2. rewrite app_nil_r in B2. cbn [cells_size Cells.csize] in W2. rewrite Nat.add_0_r in W2.
  split; [|exact Ln]. split.
  - apply bytes_at_app. split; [exact B1|]. apply bytes_at_app. split; [exact B2|]. rewrite Ln. exact B3.
  - destruct W1 as (X0 & X1 & X). destruct W2 as (Y0 & Y1 & Y). destruct W3 as (Z0 & Z1 & ZZ).
    rewrite !length_app, Ln. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (length pre))); [apply X; lia|].
    destruct (Z_lt_le_dec i (Z.of_nat (length pre) + Z.of_nat n)).
    + replace (A + i) with (A + Z.of_nat (length pre) + (i - Z.of_nat (length pre))) by lia. apply Y. lia.
    + replace (A + i) with (A + Z.of_nat (length pre) + Z.of_nat n + (i - Z.of_nat (length pre) - Z.of_nat n)) by lia. apply ZZ. lia.
Qed.

Lemma u8arr_join3' : forall m A pre (k : Z) n mid suf,
  u8arr asegs m A pre -> Z.of_nat (length pre) = k -> rw_cells asegs m (A + k) [CB n mid] -> u8arr asegs m (A + k + Z.of_nat n) suf ->
  u8arr asegs m A (pre ++ mid ++ suf) /\ length mid = n.
Proof. intros m A pre k n mid suf H1 <- H2 H3. eapply u8arr_join3; eauto. Qed.

(* [comment removed for export] *)
Lemma u8_store : forall m A buf (k : Z) (b : byte),
  u8arr asegs m A buf -> 0 <= k < Z.of_nat (length buf) ->
  store_ok asegs m (wa (A + k)) 1 = true /\ u8arr asegs (write_to_mem m (wa (A + k)) [b]) A (upd buf (Z.to_nat k) b).
Proof.
  intros m A buf k b ARR Hk. split.
  - eapply u8arr_store_ok; [exact ARR| exact Hk| reflexivity].
  - apply u8arr_write; [exact ARR| exact Hk].
Qed.

Lemma u8_store' : forall m A buf (a k : Z) (b : byte),
  u8arr asegs m A buf -> a = A + k -> 0 <= k < Z.of_nat (length buf) ->
  store_ok asegs m (wa a) 1 = true /\ u8arr asegs (write_to_mem m (wa a) [b]) A (upd buf (Z.to_nat k) b).
Proof. intros m A buf a k b ARR -> Hk. apply u8_store; assumption. Qed.

Lemma le1_lit8 : forall z, 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. cbn [Z_to_le_bytes]. rewrite unsigned_lit by lia. reflexivity. Qed.



End CeilWrap.
End CJ_print_lemmas2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs RT_data CJ_iface AShadow ICPT_iface RT_poison RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg ICPT_pcleaf ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcommon_x.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_x.ICPT_pcdefs2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_istrlen.
Import SO_shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma sh_zero_munch_stack : forall W m m' lo hi,
  sh_zero m lo hi -> munch W m m' -> 0 <= lo -> hi <= 2^47 ->
  Forall (fun iv => alloc_ceiling <= fst iv) W -> sh_zero m' lo hi.
Proof.
  intros W m m' lo hi SZ MU H0 H47 HW a Ha. unfold shb. rewrite MU; [apply SZ; exact Ha|].
  pose proof (SH_below_ceiling a ltac:(lia)) as B. pose proof (SH_bounds a ltac:(lia)) as B'. rewrite wa_unsigned by lia.
  clear SZ MU Ha. induction W as [|[u v] W IH]; [exact I|].
  apply Forall_cons_iff in HW as [H1 HW]. cbn [fst snd] in H1. cbn. split; [lia| apply IH; exact HW].
Qed.

(* [comment removed for export] *)
Lemma sh_zero_read8 : forall m lo hi W,
  sh_zero m lo hi -> lo mod 8 = 0 -> 0 <= lo -> hi <= 2^47 -> SH lo <= W -> W + 8 <= SH hi ->
  ov_read_bytes asegs m (wa W) 8 = Some (zbs [0; 0; 0; 0; 0; 0; 0; 0]).
Proof.
  intros m lo hi W SZ AL H0 H47 W1 W2.
  assert (G : forall j, W <= j < W + 8 -> m (wa j) = Some (zb 0)).
  { intros j Hj. set (b := 8 * (j - SHADOW_OFFSET)).
    assert (Hb : lo <= b < hi) by (subst b; unfold SH, SHADOW_OFFSET in *; Z.div_mod_to_equations; lia).
    pose proof (SZ b Hb) as E. unfold shb in E. replace (SH b) with j in E by (subst b; unfold SH, SHADOW_OFFSET in *; Z.div_mod_to_equations; lia).
    exact E. }
  assert (BA : bytes_at asegs m W (zbs [0; 0; 0; 0; 0; 0; 0; 0])).
  { split; [unfold SH, SHADOW_OFFSET in *; lia|]. split; [cbn [length zbs map]; unfold SH, SHADOW_OFFSET in *; Z.div_mod_to_equations; lia|].
    intros i Hi. cbn [length zbs map] in Hi. unfold mrd. rewrite (G (W + Z.of_nat i)) by lia.
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try reflexivity. lia. }
  pose proof (bytes_at_ov_read asegs m W _ 0 8 BA ltac:(cbn; lia)) as RD. rewrite Z.add_0_r in RD. exact RD.
Qed.

(* [comment removed for export] *)
Lemma sh_zero_shadow_ok64 : forall m lo hi a n,
  sh_zero m lo hi -> lo + 64 <= a -> hi mod 64 = 0 -> 0 <= lo -> lo <= a -> a + n <= hi -> 0 < n -> shadow_ok m a n.
Proof.
  intros m lo hi a n SZ AL AH H0 Ha Hn Hp. split.
  - intros i Hi. exists 0. split; [apply SZ; lia| left; reflexivity].
  - intros j Hj. set (b := 8 * (j - SHADOW_OFFSET)).
    assert (Hb : lo <= b < hi) by (subst b; unfold SH, SHADOW_OFFSET in *; Z.div_mod_to_equations; lia).
    pose proof (SZ b Hb) as E. unfold shb in E.
    replace (SH b) with j in E by (subst b; unfold SH, SHADOW_OFFSET in *; Z.div_mod_to_equations; lia).
    rewrite E. discriminate.
Qed.

(* [comment removed for export] *)
Lemma alloc_ceiling_mod8 : alloc_ceiling mod 8 = 0.
Proof. pose proof alloc_ceiling_al as H. Z.div_mod_to_equations. lia. Qed.

Definition APCS_STACK : Z := 2320.      (* [comment removed for export] *)

Definition pcommons_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'   (* [comment removed for export] *)
    /\ stk asegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition pcommon_s_stmt (fa : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo VA S : Z) (str slack : list byte),
    mem_inv asegs m -> shbase_cells m -> lowsh_at m -> icpt_cells m -> sh_zero m alloc_ceiling (2^47) ->
    stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + APCS_STACK <= bv_unsigned sp ->
    a1 = Z_to_bv 64 fa -> a2 = Z_to_bv 64 VA ->
    rw_cells asegs m VA [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= VA -> VA + 8 <= 2^47 ->
    bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
    bv_unsigned sp <= S -> S + Z.of_nat (length str) + 1 + 16 <= 2^47 -> Z.of_nat (length str) <= 2^20 ->
    evt asegs (pcommons_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APRINTF_COMMON) fc None m (seg_rom asegs)).


End CeilWrap.
