(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnModel BnTree BnInv BgState BgInv.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require BgSpecs.
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface RT_client_kit.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require BnKit2.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeilingF2. Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation SP0 := (@ar_SP0 AR).
Local Notation LIBW_cs := (@ar_LIBW_cs AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition pl_frames_lb (PL : placement) (LB : list block) : Prop :=
  forall iv, In iv (pl_frames PL) -> exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b.

Definition frames_ok (LB : list block) (PL : placement) (SPX BX : Z) : Prop := pl_frames_lb PL LB /\ ACEIL <= SPX /\ BX < 2^63.

Lemma pl_frames_lb_nofr : forall PL LB, pl_frames PL = [] -> pl_frames_lb PL LB.
Proof. intros PL LB E iv H. rewrite E in H. destruct H. Qed.
Lemma pl_frames_lb_incl : forall PL LB LB', pl_frames_lb PL LB -> (forall b, In b LB -> In b LB') -> pl_frames_lb PL LB'.
Proof. intros PL LB LB' H HI iv Hiv. destruct (H iv Hiv) as (b & Hb & R). exists b. split; [apply HI; exact Hb | exact R]. Qed.

Lemma frames_ok_nofr : forall LB PL SPX BX, BgLayer.frames_ok PL SPX BX -> pl_frames PL = [] -> frames_ok LB PL SPX BX.
Proof. intros LB PL SPX BX (_ & H2) E. split; [apply pl_frames_lb_nofr; exact E | exact H2]. Qed.
Lemma frames_ok_incl : forall LB LB' PL SPX BX, frames_ok LB PL SPX BX -> (forall b, In b LB -> In b LB') -> frames_ok LB' PL SPX BX.
Proof. intros LB LB' PL SPX BX (H1 & H2) HI. split; [eapply pl_frames_lb_incl; eauto | exact H2]. Qed.

Lemma frames_ok_mono : forall LB PL SPX SPX' BX, frames_ok LB PL SPX BX -> ACEIL <= SPX' <= SPX -> frames_ok LB PL SPX' BX.
Proof. intros LB PL SPX SPX' BX (H1 & H2 & H3) H. split; [exact H1 | lia]. Qed.

Lemma pl_frames_lb_in : forall PL PL' LB, (forall iv, In iv (pl_frames PL') -> In iv (pl_frames PL)) -> pl_frames_lb PL LB -> pl_frames_lb PL' LB.
Proof. intros PL PL' LB HI H iv Hiv. exact (H iv (HI iv Hiv)). Qed.

Lemma frames_ok_set_mont : forall LB PL mo SPX BX, frames_ok LB PL SPX BX -> frames_ok LB (pl_set_mont PL mo) SPX BX.
Proof. intros LB PL mo SPX BX H. exact H. Qed.

Definition heap_only (p : option place) : option place := match p with Some (PHeap a q off) => Some (PHeap a q off) | _ => None end.
Definition pl_strip (PL : placement) : placement := mkPL (fun r => heap_only (pl_bn PL r)) (pl_ctx PL) (pl_mont PL) None.

Lemma fr_ivs_heap_only : forall p, fr_ivs (heap_only p) = [].
Proof. intros [[a q off|a|a d|a]|]; reflexivity. Qed.

Lemma pl_frames_strip : forall PL, pl_frames (pl_strip PL) = [].
Proof.
  intros PL. unfold pl_frames. cbn [pl_recp pl_strip recp_ivs]. rewrite app_nil_r.
  induction NFIX as [|n IH]; cbn [pl_frames_n]; [reflexivity|]. rewrite IH. cbn [pl_bn pl_strip]. rewrite fr_ivs_heap_only. reflexivity.
Qed.

Lemma pl_bn_strip_some : forall PL r p, pl_bn (pl_strip PL) r = Some p -> pl_bn PL r = Some p /\ exists a q off, p = PHeap a q off.
Proof.
  intros PL r p E. cbn [pl_bn pl_strip] in E. destruct (pl_bn PL r) as [[a q off|a|a d|a]|]; cbn [heap_only] in E; try discriminate E.
  injection E as <-. split; [reflexivity|]. exists a, q, off. reflexivity.
Qed.

Lemma pl_of_strip_some : forall PL r p, pl_of (pl_strip PL) r = Some p -> pl_of PL r = Some p.
Proof.
  intros PL r p E. unfold pl_of in *. cbn [pl_mont pl_strip] in E.
  destruct (r =? ROne)%nat; [exact E|]. destruct (r =? RMontRR)%nat; [exact E|]. destruct (r =? RMontN)%nat; [exact E|].
  destruct (r =? RMontNi)%nat; [exact E|]. destruct (r <? NFIX)%nat; [|exact E]. exact (proj1 (pl_bn_strip_some PL r p E)).
Qed.

Lemma pl_of_strip_keep : forall PL r p, pl_of PL r = Some p -> fr_ivs (Some p) = [] -> (forall x, p <> PStatic x \/ r = ROne) -> pl_of (pl_strip PL) r = Some p.
Proof.
  intros PL r p E F NS. unfold pl_of in *. cbn [pl_mont pl_strip].
  destruct (r =? ROne)%nat eqn:E1; [exact E|]. destruct (r =? RMontRR)%nat; [exact E|]. destruct (r =? RMontN)%nat; [exact E|].
  destruct (r =? RMontNi)%nat; [exact E|]. destruct (r <? NFIX)%nat; [|exact E]. cbn [pl_bn pl_strip]. rewrite E.
  destruct p as [a q off|a|a d|a]; cbn [heap_only]; try reflexivity; try discriminate F.
  exfalso. destruct (NS a) as [N|N]; [apply N; reflexivity| apply Nat.eqb_neq in E1; contradiction].
Qed.

Lemma pl_wf_strip : forall PL, pl_wf PL -> pl_wf (pl_strip PL).
Proof.
  intros PL (W1 & W2 & W3). split; [|split].
  - intros r p E. destruct (pl_bn_strip_some PL r p E) as [E' (a & q & off & ->)]. exact (W1 r _ E').
  - intros r r' p p' iv iv' NE E E' Hiv. destruct (pl_bn_strip_some PL r p E) as [_ (a & q & off & ->)]. destruct Hiv.
  - cbn [pl_recp pl_strip]. exact I.
Qed.

Lemma pl_bn_ids_strip : forall PL n, pl_bn_ids (pl_strip PL) n = pl_bn_ids PL n.
Proof.
  intros PL n. induction n as [|n IH]; cbn [pl_bn_ids]; [reflexivity|]. rewrite IH. f_equal. cbn [pl_bn pl_strip].
  destruct (pl_bn PL n) as [[a q off|a|a d|a]|]; reflexivity.
Qed.
Lemma pl_ids_strip : forall PL, pl_ids (pl_strip PL) = pl_ids PL.
Proof. intros PL. unfold pl_ids. rewrite pl_bn_ids_strip. reflexivity. Qed.

Lemma pl_blocks_strip : forall OW PL, pl_blocks OW PL -> pl_blocks OW (pl_strip PL).
Proof.
  intros OW PL (B1 & B2 & B3). split; [|split; [exact B2 | exact B3]].
  intros r p Hr E. exact (B1 r p Hr (pl_of_strip_some PL r p E)).
Qed.

Lemma lib_parts_strip : forall st OW PL EA, lib_parts st OW PL EA -> lib_parts st OW (pl_strip PL) EA.
Proof.
  intros st OW PL EA (WFS & PWF & IDS & PLB & ERRB). split; [exact WFS|]. split; [exact (pl_wf_strip PL PWF)|].
  split; [unfold ids_ok, all_ids in *; rewrite pl_ids_strip; exact IDS|]. split; [exact (pl_blocks_strip OW PL PLB) | exact ERRB].
Qed.

Lemma frames_ok_strip : forall LB PL SPX BX, frames_ok LB PL SPX BX -> BgLayer.frames_ok (pl_strip PL) SPX BX.
Proof.
  intros LB PL SPX BX (_ & H2). split; [| exact H2]. intros iv Hiv. rewrite pl_frames_strip in Hiv. destruct Hiv.
Qed.

Lemma AH_range_in : forall Σ OW LB m p A n, AHEAP Σ OW LB m -> In (p, A, n) (OW ++ LB) -> ablock_range_gen A n.
Proof. intros Σ OW LB m p A n H Hin. exact (AH_range_gen Σ OW LB m (p, A, n) H Hin). Qed.

Inductive w_okc (OW LB : list block) (st : ST) (PL : placement) (EA : BnRepDefs.err_addrs) (SPX : Z) (cxo : bool) (hs : list bnref) (iv : Z * Z) : Prop :=
  | w_stack : ACEIL <= fst iv -> snd iv <= SPX -> w_okc OW LB st PL EA SPX cxo hs iv
  | w_struct : forall r a, In r hs -> ref_at st OW PL r a -> r <> ROne -> a <= fst iv -> snd iv <= a + 24 -> w_okc OW LB st PL EA SPX cxo hs iv
  | w_limbs : forall r p D, In r hs -> vref r st -> bn_d (getbn r st) = Some p ->
                In (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) OW -> D <= fst iv -> snd iv <= D + 8 * Z.of_nat (bn_dmax (getbn r st)) ->
                w_okc OW LB st PL EA SPX cxo hs iv
  | w_foreign : forall q A n, In (q, A, n) OW -> ~ In q (all_ids st PL EA) -> A <= fst iv -> snd iv <= A + n -> w_okc OW LB st PL EA SPX cxo hs iv
  | w_cx : cxo = true -> (forall x, fst iv <= x < snd iv -> cx_fp st OW PL x) -> w_okc OW LB st PL EA SPX cxo hs iv.

Section Disj.
  Variables (s : rts RT) (OW LB : list block) (m : mem).
  Hypothesis HEAP : AHEAP s OW LB m.

  Local Notation blk_excl := (BgLayer.blk_excl s OW LB m HEAP).
  Local Notation blk_not_libw := (BgLayer.blk_not_libw s OW LB m HEAP).
  Local Notation blk_below_ceiling := (BgLayer.blk_below_ceiling s OW LB m HEAP).
  Local Notation blk_not_image := (BgLayer.blk_not_image s OW LB m HEAP).

  Variables (st : ST) (PL : placement) (EA : BnRepDefs.err_addrs) (SPX BX : Z).
  Hypothesis PARTS : lib_parts st OW PL EA.
  Hypothesis FROK : frames_ok LB PL SPX BX.
  Local Ltac parts := pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).

  Local Notation sk_block_own := (BgLayer.sk_block_own s OW LB m HEAP st PL EA PARTS).
  Local Notation sk_block_mont := (BgLayer.sk_block_mont s OW LB m HEAP st PL EA PARTS).
  Local Notation sk_block_pool := (BgLayer.sk_block_pool s OW LB m HEAP st PL EA PARTS).
  Local Notation limbs_limbs_disj := (BgLayer.limbs_limbs_disj s OW LB m HEAP st PL EA PARTS).
  Local Notation cx_fp_block := (BgLayer.cx_fp_block OW st PL EA PARTS).
  Local Notation mont_fp_block := (BgLayer.mont_fp_block OW st PL EA PARTS).
  Local Notation own_fp_block := (BgLayer.own_fp_block OW st PL EA PARTS).
  Local Notation own_fp_blockA := (BgLayer.own_fp_blockA OW st PL EA PARTS).
  Local Notation limbs_not_cx := (BgLayer.limbs_not_cx s OW LB m HEAP st PL EA PARTS).
  Local Notation err_not_block := (BgLayer.err_not_block s OW LB m HEAP st PL EA PARTS).
  Local Notation err_below_ceiling := (BgLayer.err_below_ceiling s OW LB m HEAP st PL EA PARTS).

  Local Ltac std_lia__ := lia.
  Local Ltac clia := pose proof (AH_ceil _ _ _ _ HEAP) as CEIL_RANGE__; unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CEIL_RANGE__; std_lia__.

  Lemma frame_iv_blk : forall iv, In iv (pl_frames PL) -> exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b.
  Proof. intros iv H. exact (proj1 FROK iv H). Qed.

  Lemma frame_iv_range : forall iv, In iv (pl_frames PL) -> 0 < fst iv /\ snd iv <= ACEIL /\ (snd iv <= 0x10000 \/ 0xbf9000 <= fst iv).
  Proof.
    intros iv H. destruct (frame_iv_blk iv H) as (b & Hb & R1 & R2).
    pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; right; exact Hb)) as (B0 & _ & _ & BC & BI). lia.
  Qed.

  Lemma frame_blk_apart : forall q A n iv, In (q, A, n) OW -> In iv (pl_frames PL) -> A + n <= fst iv \/ snd iv <= A.
  Proof.
    intros q A n iv Hin H. destruct (frame_iv_blk iv H) as (b & Hb & R1 & R2).
    pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite map_app in ND.
    assert (NE : blk_id (q, A, n) <> blk_id b).
    { intros E. eapply (nodup_app_disj _ _ (blk_id b) ND); [rewrite <- E; apply in_map; exact Hin | apply in_map; exact Hb]. }
    pose proof (AH_disjoint_gen _ _ _ _ (q, A, n) b HEAP ltac:(apply in_or_app; left; exact Hin) ltac:(apply in_or_app; right; exact Hb) NE) as DJ.
    cbn [blk_addr blk_size fst snd] in DJ. lia.
  Qed.

  Lemma frame_blk_excl : forall q A n iv x, In (q, A, n) OW -> In iv (pl_frames PL) -> A <= x < A + n -> fst iv <= x < snd iv -> False.
  Proof. intros q A n iv x Hin H R1 R2. pose proof (frame_blk_apart q A n iv Hin H). lia. Qed.

  Lemma frame_not_libw : forall iv x, In iv (pl_frames PL) -> fst iv <= x < snd iv -> libw x -> False.
  Proof.
    intros iv x H Hx HL. destruct (frame_iv_range iv H) as (_ & _ & BI).
    revert HL. unfold libw, LIBW_bgr, ARun.LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. lia.
  Qed.

  Lemma sk_frame : forall a, In (a, a + BN_STRUCT_SZ) (pl_frames PL) -> a + 24 <= ACEIL /\ (a + 24 <= 0x10000 \/ 0xbf9000 <= a) /\ 0 < a.
  Proof. parts. intros a H. destruct (frame_iv_range _ H) as (H1 & H2 & H3). cbn [fst snd] in H1, H2, H3. unfold BN_STRUCT_SZ in *. lia. Qed.

  Lemma sk_blk_frame : forall q A n a a', In (q, A, n) OW -> A <= a -> a + 24 <= A + n -> In (a', a' + BN_STRUCT_SZ) (pl_frames PL) ->
    a + 24 <= a' \/ a' + 24 <= a.
  Proof. intros q A n a a' Hin R1 R2 HF. pose proof (frame_blk_apart q A n _ Hin HF) as DJ. cbn [fst snd] in DJ. unfold BN_STRUCT_SZ in *. lia. Qed.

  Let PARTS0 : lib_parts st OW (pl_strip PL) EA := lib_parts_strip st OW PL EA PARTS.
  Let FROK0 : BgLayer.frames_ok (pl_strip PL) SPX BX := frames_ok_strip LB PL SPX BX FROK.

  Inductive skF (r : bnref) (a : Z) : Prop :=
  | SKF_blk : forall q A n, ref_at st OW (pl_strip PL) r a -> r <> ROne -> In (q, A, n) OW -> A <= a -> a + 24 <= A + n -> skF r a
  | SKF_frame : forall p, stored_ref r -> pl_bn PL r = Some p -> In (a, a + BN_STRUCT_SZ) (fr_ivs (Some p)) -> In (a, a + BN_STRUCT_SZ) (pl_frames PL) -> skF r a
  | SKF_one : r = ROne -> a = CONST_ONE -> skF r a.

  Lemma ref_skF : forall r a, ref_at st OW PL r a -> skF r a.
  Proof.
    parts. intros r a HA. pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K.
    destruct K as [q n S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea].
    - apply (SKF_blk r a q a n); [| exact (proj1 (proj2 S)) | exact Hin | lia | unfold BN_STRUCT_SZ in Hn; lia].
      apply ref_at_fixed; [exact (proj1 S)|]. exists (PHeap a q 0). split; [| reflexivity].
      apply pl_of_strip_keep; [rewrite (pl_of_stored PL r S); exact Eb | reflexivity | intros x; left; discriminate].
    - assert (NR : r <> ROne) by (intros ->; discriminate M).
      apply (SKF_blk r a qm am MONT_CTX_SZ); [| exact NR | exact Hin | lia | unfold MONT_CTX_SZ; lia].
      pose proof (pl_of_mont PL r M) as E. rewrite Em in E.
      assert (Hr : (r < NFIX)%nat) by (apply mont_ref_cases in M; destruct M as [->|[->| ->]]; unfold RMontRR, RMontN, RMontNi, NFIX; lia).
      apply ref_at_fixed; [exact Hr|]. eexists. split; [apply pl_of_strip_keep; [exact E | reflexivity | intros x; left; discriminate] | cbn [place_addr]; lia].
    - assert (NR : r <> ROne) by (subst r; unfold RPool, ROne, NFIX; lia).
      apply (SKF_blk r a q H ITEM_SZ); [| exact NR | exact Hin | lia | unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; nia].
      subst r. apply ref_at_pool. exists q, H. auto.
    - exact (SKF_frame r a p S Eb Hiv HF).
    - exact (SKF_one r a Er Ea).
  Qed.

  Lemma const_one_frame : forall iv, In iv (pl_frames PL) -> snd iv <= CONST_ONE \/ CONST_ONE + 24 <= fst iv.
  Proof. intros iv H. destruct (frame_iv_range iv H) as (_ & _ & BI). unfold CONST_ONE. lia. Qed.

  Lemma struct_disj : forall r r' a a', r <> r' -> ref_at st OW PL r a -> ref_at st OW PL r' a' -> a + 24 <= a' \/ a' + 24 <= a.
  Proof.
    parts.
    intros r r' a a' NE HA HA'.
    destruct (ref_skF r a HA) as [q A n HA0 NR Hin R1 R2|p S Eb Hiv HF|Er Ea]; destruct (ref_skF r' a' HA') as [q' A' n' HA0' NR' Hin' R1' R2'|p' S' Eb' Hiv' HF'|Er' Ea'].
    - exact (BgLayer.struct_disj s OW LB m HEAP st (pl_strip PL) EA SPX BX PARTS0 FROK0 r r' a a' NE HA0 HA0').
    - exact (sk_blk_frame q A n a a' Hin R1 R2 HF').
    - subst r' a'. pose proof (blk_not_image q A n a Hin ltac:(lia)) as X. unfold CONST_ONE.
      pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & _ & BI). lia.
    - pose proof (sk_blk_frame q' A' n' a' a Hin' R1' R2' HF). lia.
    - pose proof (proj1 (proj2 PWF) r r' p p' _ _ NE Eb Eb' Hiv Hiv') as AP. unfold iv_apart, BN_STRUCT_SZ in AP. cbn [fst snd] in AP. lia.
    - subst r' a'. pose proof (const_one_frame _ HF) as X. cbn [fst snd] in X. unfold BN_STRUCT_SZ in X. lia.
    - subst r a. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin') as (_ & _ & _ & _ & BI). unfold CONST_ONE. lia.
    - subst r a. pose proof (const_one_frame _ HF') as X. cbn [fst snd] in X. unfold BN_STRUCT_SZ in X. lia.
    - exfalso. apply NE. congruence.
  Qed.

  Lemma struct_limbs_disj : forall r r' a p D n, ref_at st OW PL r a -> vref r' st -> bn_d (getbn r' st) = Some p ->
    In (p, D, n) OW -> a + 24 <= D \/ D + n <= a.
  Proof.
    parts.
    intros r r' a p D n HA HV' Ed Hin.
    destruct (ref_skF r a HA) as [q A nq HA0 NR HinA R1 R2|p0 S Eb Hiv HF|Er Ea].
    - exact (BgLayer.struct_limbs_disj s OW LB m HEAP st (pl_strip PL) EA SPX BX PARTS0 FROK0 r r' a p D n HA0 HV' Ed Hin).
    - pose proof (frame_blk_apart p D n _ Hin HF) as DJ. cbn [fst snd] in DJ. unfold BN_STRUCT_SZ in DJ. lia.
    - subst r a. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & _ & BI). unfold CONST_ONE. lia.
  Qed.

  Lemma framebuf_struct_disj : forall r ab d r' a', pl_bn PL r = Some (PFrameBuf ab d) -> ref_at st OW PL r' a' ->
    a' + 24 <= d \/ d + TMOD_BUF_SZ <= a'.
  Proof.
    parts.
    intros r ab d r' a' Eb HA'. pose proof (pl_wf_stored PL r _ PWF Eb) as S.
    assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
    { apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
    destruct (ref_skF r' a' HA') as [q' A' n' HA0' NR' Hin' R1' R2'|p' S' Eb' Hiv' HF'|Er' Ea'].
    - pose proof (frame_blk_apart q' A' n' _ Hin' HFd) as DJ. cbn [fst snd] in DJ. lia.
    - destruct (Nat.eq_dec r r') as [<-|NE].
      + rewrite Eb in Eb'. injection Eb' as <-. cbn [fr_ivs In] in Hiv'. destruct Hiv' as [E|[E|[]]].
        * injection E as <-. pose proof (proj1 PWF r _ Eb) as (_ & _ & _ & _ & _ & AP). unfold iv_apart, BN_STRUCT_SZ in AP. cbn [fst snd] in AP. lia.
        * injection E as E1 E2. unfold BN_STRUCT_SZ, TMOD_BUF_SZ in *. lia.
      + pose proof (proj1 (proj2 PWF) r r' _ _ (d, d + TMOD_BUF_SZ) (a', a' + BN_STRUCT_SZ) NE Eb Eb' ltac:(right; left; reflexivity) Hiv') as AP.
        unfold iv_apart, BN_STRUCT_SZ in AP. cbn [fst snd] in AP. lia.
    - subst r' a'. pose proof (const_one_frame _ HFd) as X. cbn [fst snd] in X. lia.
  Qed.

  Lemma bn_arr_facts_lin : forall r D, vref r st -> r <> ROne -> bn_arr m OW (pl_of PL r) D (getbn r st) ->
    u64arr bgbsegs m D (wlimbs (bn_buf (getbn r st)))
    /\ Z.of_nat (length (wlimbs (bn_buf (getbn r st)))) = Z.of_nat (bn_dmax (getbn r st))
    /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= ACEIL
    /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= 0x10000 \/ 0xbf9000 <= D \/ bn_dmax (getbn r st) = 0%nat)
    /\ (forall r' a', ref_at st OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= a').
  Proof.
    parts.
    intros r D HV HNO HArr. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR. unfold bn_arr in HArr. destruct (bn_d (getbn r st)) as [p|] eqn:Ed.
    - destruct HArr as [Hin HU]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI).
      split; [exact HU|]. split; [rewrite wlimbs_length; reflexivity|]. split; [lia|]. split; [exact BC|]. split; [lia|].
      intros r' a' HA'. eapply (struct_limbs_disj r' r); eauto.
    - assert (EMP : D = 0 /\ bn_buf (getbn r st) = [] ->
        u64arr bgbsegs m D (wlimbs (bn_buf (getbn r st))) /\ Z.of_nat (length (wlimbs (bn_buf (getbn r st)))) = Z.of_nat (bn_dmax (getbn r st))
        /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= ACEIL
        /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= 0x10000 \/ 0xbf9000 <= D \/ bn_dmax (getbn r st) = 0%nat)
        /\ (forall r' a', ref_at st OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= a')).
      { intros [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length wlimbs map].
        split. { split; [apply bytes_at_nil; lia|]. cbn [length]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
        split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; right; reflexivity|].
        intros r' a' HA'. right.
        destruct (ref_skF r' a' HA') as [q' A' n' HA0' NR' Hin' R1' R2'|p' S' Eb' Hiv' HF'|Er' Ea'].
        - pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin') as (B0 & _). lia.
        - destruct (frame_iv_range _ HF') as (X & _). cbn [fst] in X. lia.
        - subst a'. unfold CONST_ONE. lia. }
      destruct (pl_of PL r) as [[x q off|x|x d|x]|] eqn:Ep; try (apply EMP; exact HArr).
      +
        destruct HArr as (-> & HU & HL).
        destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [contradiction| discriminate E'|].
        assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
        { apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
        destruct (frame_iv_range _ HFd) as (Pd & Cd & Id). cbn [fst snd] in Pd, Cd, Id.
        unfold bn_dmax. rewrite wlimbs_length, HL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unfold TMOD_BUF_SZ in *.
        split; [exact HU|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
        intros r' a' HA'. pose proof (framebuf_struct_disj r x d r' a' Eb HA'). unfold TMOD_BUF_SZ in *. lia.
      +
        exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [contradiction| discriminate E'|].
        pose proof (proj1 PWF r _ Eb) as (_ & _ & _ & F). exact F.
  Qed.

  Lemma bn_arr_facts : forall r D, vref r st -> r <> ROne -> bn_arr m OW (pl_of PL r) D (getbn r st) ->
    u64arr bgbsegs m D (wlimbs (bn_buf (getbn r st)))
    /\ Z.of_nat (length (wlimbs (bn_buf (getbn r st)))) = Z.of_nat (bn_dmax (getbn r st))
    /\ 0 <= D /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= ACEIL \/ (SPX <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r st)) < 2^63))
    /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= 0x10000 \/ 0xbf9000 <= D \/ bn_dmax (getbn r st) = 0%nat)
    /\ (forall r' a', ref_at st OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= a').
  Proof.
    intros r D HV HNO HArr. destruct (bn_arr_facts_lin r D HV HNO HArr) as (U & LEN & D0 & DC & DI & DSEP).
    split; [exact U|]. split; [exact LEN|]. split; [exact D0|]. split; [left; exact DC|]. split; [exact DI | exact DSEP].
  Qed.

  Lemma struct_not_cx : forall r a x, ref_at st OW PL r a -> a <= x < a + 24 -> cx_fp st OW PL x -> False.
  Proof.
    parts.
    intros r a x HA Hx HC.
    destruct (ref_skF r a HA) as [q A n HA0 NR Hin R1 R2|p S Eb Hiv HF|Er Ea].
    - exact (BgLayer.struct_not_cx s OW LB m HEAP st (pl_strip PL) EA SPX BX PARTS0 FROK0 r a x HA0 Hx HC).
    - destruct (cx_fp_block x HC) as (qb & Ab & nb & Hinb & Hxb & _).
      eapply (frame_blk_excl qb Ab nb _ x Hinb HF Hxb). cbn [fst snd]. unfold BN_STRUCT_SZ. lia.
    - subst r a. destruct (cx_fp_block x HC) as (qb & Ab & nb & Hinb & Hxb & _).
      pose proof (AH_range _ _ _ _ _ _ _ HEAP Hinb) as (_ & _ & _ & _ & BI). unfold CONST_ONE in *. lia.
  Qed.

  Lemma struct_not_mont : forall r a x, ref_at st OW PL r a -> a <= x < a + 24 -> mont_fp PL x -> False.
  Proof.
    parts.
    intros r a x HA Hx [(am & qm & Em & Hm)|(c & Ec & Hm)].
    - destruct (ref_skF r a HA) as [q A n HA0 NR Hin R1 R2|p S Eb Hiv HF|Er Ea].
      + apply (BgLayer.struct_not_mont s OW LB m HEAP st (pl_strip PL) EA SPX BX PARTS0 FROK0 r a x HA0 Hx). left. exists am, qm. split; [exact Em | exact Hm].
      + destruct PLB as (_ & _ & PM). rewrite Em in PM.
        eapply (frame_blk_excl qm am MONT_CTX_SZ _ x PM HF); [unfold MONT_CTX_SZ in *; lia | cbn [fst snd]; unfold BN_STRUCT_SZ; lia].
      + subst r a. destruct PLB as (_ & _ & PM). rewrite Em in PM.
        pose proof (AH_range _ _ _ _ _ _ _ HEAP PM) as (_ & _ & _ & _ & BI). unfold CONST_ONE, MONT_CTX_SZ in *. lia.
    - pose proof (pl_frames_recp PL c Ec) as HFc.
      destruct (ref_skF r a HA) as [q A n HA0 NR Hin R1 R2|p S Eb Hiv HF|Er Ea].
      + eapply (frame_blk_excl q A n _ x Hin HFc); [lia | cbn [fst snd]; exact Hm].
      + pose proof (proj2 (proj2 PWF)) as RC. rewrite Ec in RC. destruct RC as [_ AP].
        specialize (AP r p _ Eb Hiv). unfold iv_apart, BN_STRUCT_SZ, RECP_SC_SZ in *. cbn [fst snd] in AP. lia.
      + subst r a. pose proof (const_one_frame _ HFc) as X. cbn [fst snd] in X. unfold RECP_SC_SZ in *. lia.
  Qed.

  Lemma cx_not_mont : forall x, cx_fp st OW PL x -> mont_fp PL x -> False.
  Proof.
    parts.
    intros x HC [(am & qm & Em & Hm)|(c & Ec & Hm)].
    - apply (BgLayer.cx_not_mont s OW LB m HEAP st (pl_strip PL) EA SPX BX PARTS0 FROK0 x HC). left. exists am, qm. split; [exact Em | exact Hm].
    - destruct (cx_fp_block x HC) as (q & A & n & Hin & Hxb & _).
      eapply (frame_blk_excl q A n _ x Hin (pl_frames_recp PL c Ec) Hxb). cbn [fst snd]. exact Hm.
  Qed.

  Lemma limbs_not_mont : forall r p D x, vref r st -> bn_d (getbn r st) = Some p ->
    In (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) OW -> D <= x < D + 8 * Z.of_nat (bn_dmax (getbn r st)) -> mont_fp PL x -> False.
  Proof.
    parts.
    intros r p D x HV Ed Hin Hx [(am & qm & Em & Hm)|(c & Ec & Hm)].
    - apply (BgLayer.limbs_not_mont s OW LB m HEAP st (pl_strip PL) EA SPX BX PARTS0 FROK0 r p D x HV Ed Hin Hx). left. exists am, qm. split; [exact Em | exact Hm].
    - eapply (frame_blk_excl p D _ _ x Hin (pl_frames_recp PL c Ec) Hx). cbn [fst snd]. exact Hm.
  Qed.

  Lemma framebuf_not_mont : forall r y d x, pl_bn PL r = Some (PFrameBuf y d) -> d <= x < d + TMOD_BUF_SZ -> mont_fp PL x -> False.
  Proof.
    parts.
    intros r y d x Eb Hx HM. pose proof (pl_wf_stored PL r _ PWF Eb) as S.
    assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
    { apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
    destruct HM as [(am & qm & Em & Hm)|(c & Ec & Hm)].
    - destruct PLB as (_ & _ & PM). rewrite Em in PM.
      eapply (frame_blk_excl qm am MONT_CTX_SZ _ x PM HFd); [unfold MONT_CTX_SZ in *; lia | cbn [fst snd]; exact Hx].
    - pose proof (proj2 (proj2 PWF)) as RC. rewrite Ec in RC. destruct RC as [_ AP].
      specialize (AP r _ (d, d + TMOD_BUF_SZ) Eb ltac:(right; left; reflexivity)). unfold iv_apart, TMOD_BUF_SZ, RECP_SC_SZ in *. cbn [fst snd] in AP. lia.
  Qed.

  Lemma err_not_frame : forall iv x, In iv (pl_frames PL) -> fst iv <= x < snd iv -> BnRepA.err_fp OW EA x -> False.
  Proof.
    parts. intros iv x HF Hx He. destruct ERRB as (E1 & E2 & E3 & E4). unfold BnRepA.err_fp in He.
    destruct He as [He|[He|[He|He]]];
      [eapply (frame_blk_excl _ _ _ iv x E1)| eapply (frame_blk_excl _ _ _ iv x E2)| eapply (frame_blk_excl _ _ _ iv x E3)| eapply (frame_blk_excl _ _ _ iv x E4)]; eassumption.
  Qed.

  Lemma own_fp_not_struct : forall cxo hs x r a, In r hs -> ref_at st OW PL r a -> r <> ROne -> own_fpc cxo hs st OW PL EA x -> a <= x < a + 24 -> False.
  Proof.
    parts.
    intros cxo hs x r a Hr HA HNO HO Hx.
    destruct HO as [HL|[(r' & a' & HA' & HV' & Hn' & [Hs|[(p' & D' & Ed' & Hin' & Hx')|(y & d & Ep & Hx')]])|[[_ HC]|[HMo|He]]]].
    - destruct (ref_skF r a HA) as [q A n HA0 NR Hin R1 R2|p S Eb Hiv HF|Er Ea]; [| | exact (HNO Er)].
      + eapply (blk_not_libw q A n x Hin); [lia | exact HL].
      + eapply (frame_not_libw _ x HF); [cbn [fst snd]; unfold BN_STRUCT_SZ; lia | exact HL].
    - assert (NE : r <> r') by (intros ->; contradiction). pose proof (struct_disj r r' a a' NE HA HA'). lia.
    - pose proof (struct_limbs_disj r r' a p' D' _ HA HV' Ed' Hin'). lia.
    - destruct (pl_of_cases PL r' _ Ep) as [[-> E']|[(am & qm & _ & _ & E' & _)|[S' Eb']]]; [discriminate E'| discriminate E'|].
      pose proof (framebuf_struct_disj r' y d r a Eb' HA). unfold TMOD_BUF_SZ in *. lia.
    - eapply struct_not_cx; eauto.
    - eapply struct_not_mont; eauto.
    - destruct (ref_skF r a HA) as [q A n HA0 NR Hin R1 R2|p S Eb Hiv HF|Er Ea]; [| | exact (HNO Er)].
      + apply (BgLayer.own_fp_not_struct s OW LB m HEAP st (pl_strip PL) EA SPX BX PARTS0 FROK0 cxo hs x r a Hr HA0 HNO); [| exact Hx].
        right; right; right; right. exact He.
      + eapply (err_not_frame _ x HF); [cbn [fst snd]; unfold BN_STRUCT_SZ; lia | exact He].
  Qed.

  Lemma own_fp_not_limbs : forall cxo hs x r p D, In r hs -> vref r st -> bn_d (getbn r st) = Some p ->
    In (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) OW -> own_fpc cxo hs st OW PL EA x ->
    D <= x < D + 8 * Z.of_nat (bn_dmax (getbn r st)) -> False.
  Proof.
    parts.
    intros cxo hs x r p D Hr HV Ed Hin HO Hx.
    pose proof (bn_in_m r st p HV Ed) as Hm. pose proof (ids_m_nodup _ _ _ IDS) as NDm.
    destruct HO as [HL|[(r' & a' & HA' & HV' & Hn' & [Hs|[(p' & D' & Ed' & Hin' & Hx')|(y & d & Ep & Hx')]])|[[_ HC]|[HMo|He]]]].
    - eapply blk_not_libw; eauto.
    - pose proof (struct_limbs_disj r' r a' p D _ HA' HV Ed Hin). lia.
    - assert (NE : r <> r') by (intros ->; contradiction).
      pose proof (limbs_limbs_disj r r' p D _ p' D' _ NE HV HV' Ed Ed' Hin Hin'). lia.
    - destruct (pl_of_cases PL r' _ Ep) as [[-> E']|[(am & qm & _ & _ & E' & _)|[S' Eb']]]; [discriminate E'| discriminate E'|].
      assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
      { apply pl_frames_In. left. exists r'. rewrite Eb'. split; [exact (proj1 S')| right; left; reflexivity]. }
      eapply (frame_blk_excl p D _ _ x Hin HFd Hx). cbn [fst snd]. exact Hx'.
    - eapply limbs_not_cx; eauto.
    - eapply limbs_not_mont; eauto.
    - eapply (err_not_block p D _ x Hin Hx); [|exact He]. intros q' Hq' E. subst q'. eapply (ids_ea_m st PL EA p p IDS); eauto.
  Qed.

  Lemma own_fp_not_cx : forall hs x, own_fpc true hs st OW PL EA x -> cx_fp st OW PL x -> False.
  Proof.
    parts.
    intros hs x HO HC.
    destruct HO as [HL|[(r' & a' & HA' & HV' & Hn' & [Hs|[(p' & D' & Ed' & Hin' & Hx')|(y & d & Ep & Hx')]])|[[Ec _]|[HMo|He]]]]; [| | | |discriminate| |].
    - destruct (cx_fp_block x HC) as (q & A & n & Hin & Hxb & _). eapply blk_not_libw; eauto.
    - eapply struct_not_cx; eauto.
    - eapply limbs_not_cx; eauto.
    - destruct (pl_of_cases PL r' _ Ep) as [[-> E']|[(am & qm & _ & _ & E' & _)|[S' Eb']]]; [discriminate E'| discriminate E'|].
      assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
      { apply pl_frames_In. left. exists r'. rewrite Eb'. split; [exact (proj1 S')| right; left; reflexivity]. }
      destruct (cx_fp_block x HC) as (q & A & n & Hin & Hxb & _).
      eapply (frame_blk_excl q A n _ x Hin HFd Hxb). cbn [fst snd]. exact Hx'.
    - eapply cx_not_mont; eauto.
    - apply (BgLayer.own_fp_not_cx s OW LB m HEAP st (pl_strip PL) EA SPX BX PARTS0 FROK0 hs x); [| exact HC].
      right; right; right; right. exact He.
  Qed.

  Theorem own_fp_outside : forall cxo hs W x, Forall (w_okc OW LB st PL EA SPX cxo hs) W -> own_fpc cxo hs st OW PL EA x -> outside W x.
  Proof.
    parts.
    intros cxo hs W x HW HO. induction HW as [|[lo hi] W Hiv HW IH]; [exact I|]. cbn [outside]. split; [|exact IH].
    intros Hx. cbn [fst snd] in *. destruct Hiv as [Hs Hsp|r a Hr HA HNO H1 H2|r p D Hr HV Ed Hin H1 H2|q A n Hin Hq H1 H2|Ec Hcx]; cbn [fst snd] in *.
    - destruct (own_fp_block cxo hs x HO) as [HL|[(q & A & n & Hin & Hxb & _)|(iv & Hiv & Hxi)]].
      + revert HL. unfold libw, LIBW_bgr, ARun.LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. clia.
      + pose proof (blk_below_ceiling q A n x Hin Hxb). lia.
      + destruct (frame_iv_range _ Hiv) as (_ & S2 & _). lia.
    - eapply (own_fp_not_struct cxo hs x r a); eauto. lia.
    - eapply (own_fp_not_limbs cxo hs x r p D); eauto. lia.
    - destruct (own_fp_block cxo hs x HO) as [HL|[(q' & A' & n' & Hin' & Hxb' & Hq')|(iv & Hiv & Hxi)]].
      + eapply (blk_not_libw q A n x Hin); [lia | exact HL].
      + assert (NE : q' <> q) by (intros ->; contradiction).
        pose proof (blk_excl q' A' n' q A n x Hin' Hin NE Hxb'). lia.
      + eapply (frame_blk_excl q A n iv x Hin Hiv); [lia | exact Hxi].
    - subst cxo. eapply own_fp_not_cx; [exact HO| apply Hcx; exact Hx].
  Qed.
End Disj.
End WithCeilingF2.
Notation w_ok OW LB st PL EA SPX := (w_okc OW LB st PL EA SPX false).

Section WithCeilingF3. Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation SP0 := (@ar_SP0 AR).
Local Notation LIBW_cs := (@ar_LIBW_cs AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Theorem lib_state_frame : forall s LB SPX BX cxo hs st m m' OW PL EA W,
  AHEAP s OW LB m -> lib_state_hc cxo hs st m OW PL EA -> munch W m m' -> wmono bgbsegs m m' -> frames_ok LB PL SPX BX ->
  Forall (w_okc OW LB st PL EA SPX cxo hs) W -> lib_state_hc cxo hs st m' OW PL EA.
Proof.
  intros s LB SPX BX cxo hs st m m' OW PL EA W HEAP HS MU WM FROK HW.
  pose proof (lib_state_h_parts _ _ _ _ _ _ HS) as PARTS.
  eapply lib_state_hc_agree; [exact HS|]. eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|].
  intros a Ha. eapply own_fp_outside; eauto.
Qed.

Lemma own_fp_libA : forall cxo hs s m OW LB PL EA SPX BX x, lib_state_hc cxo hs s m OW PL EA -> frames_ok LB PL SPX BX ->
  own_fpA cxo hs s OW PL EA x -> BnRepA.libw x \/ in_block OW x \/ in_block LB x.
Proof.
  intros cxo hs s m OW LB PL EA SPX BX x HS FROK HO. pose proof (lib_state_h_parts _ _ _ _ _ _ HS) as PARTS.
  destruct (BgLayer.own_fp_blockA OW s PL EA PARTS cxo hs x HO) as [HL|[(q & A & n & Hq & Hx & _)|(iv & Hiv & Hxi)]].
  - left. exact HL.
  - right; left. eapply BnRepA.in_block_intro; [exact Hq | exact Hx].
  - right; right. destruct (frame_iv_blk LB PL SPX BX FROK iv Hiv) as ([[q A] n] & Hb & R1 & R2). cbn [blk_addr blk_size fst snd] in R1, R2.
    eapply BnRepA.in_block_intro; [exact Hb | lia].
Qed.

Lemma own_fp_clientA : forall cxo hs s m OW LB PL EA SPX BX L SP x, lib_state_hc cxo hs s m OW PL EA -> frames_ok LB PL SPX BX ->
  (forall b, In b OW -> In b L) -> (forall b, In b LB -> In b L) -> own_fpA cxo hs s OW PL EA x -> aclient_addr L SP x.
Proof.
  intros cxo hs s m OW LB PL EA SPX BX L SP x HS FROK H1 H2 HO.
  destruct (own_fp_libA _ _ _ _ _ _ _ _ _ _ _ HS FROK HO) as [HL|[(b & Hb & Hr)|(b & Hb & Hr)]]; [apply libw_clientA; exact HL| |].
  - right; right. exists b. split; [apply H1; exact Hb | exact Hr].
  - right; right. exists b. split; [apply H2; exact Hb | exact Hr].
Qed.

Theorem lib_state_h_icall : forall s LB cxo hs st m m' OW PL EA SP SPX d n,
  AHEAP s OW LB m -> lib_state_hc cxo hs st m OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> SP <= SPX ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (d <= a < d + n)) m m' ->
  w_okc OW LB st PL EA SPX cxo hs (d, d + n) ->
  lib_state_hc cxo hs st m' OW PL EA.
Proof.
  intros s LB cxo hs st m m' OW PL EA SP SPX d n HEAP HS FROK LE AG HW.
  pose proof (lib_state_h_parts _ _ _ _ _ _ HS) as PARTS.
  eapply lib_state_hc_agreeA; [exact HS|]. eapply agree_on_mono; [exact AG|]. intros x Hx. split.
  - eapply (own_fp_clientA cxo hs st m OW LB PL EA SPX USTACK_TOP (OW ++ LB) SP x HS FROK); [| | exact Hx]; intros b Hb; apply in_or_app; [left | right]; exact Hb.
  - assert (FW : Forall (w_okc OW LB st PL EA SPX cxo hs) [(d, d + n)]) by (constructor; [exact HW | constructor]).
    pose proof (own_fp_outside s OW LB m HEAP st PL EA SPX USTACK_TOP PARTS FROK cxo hs [(d, d + n)] x FW (own_fpA_fpc _ _ _ _ _ _ _ Hx)) as O.
    cbn [outside] in O. tauto.
Qed.

Theorem lib_state_h_icall2 : forall s LB cxo hs st m m' OW PL EA SP SPX d1 n1 d2 n2,
  AHEAP s OW LB m -> lib_state_hc cxo hs st m OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> SP <= SPX ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (d1 <= a < d1 + n1) /\ ~ (d2 <= a < d2 + n2)) m m' ->
  w_okc OW LB st PL EA SPX cxo hs (d1, d1 + n1) -> w_okc OW LB st PL EA SPX cxo hs (d2, d2 + n2) ->
  lib_state_hc cxo hs st m' OW PL EA.
Proof.
  intros s LB cxo hs st m m' OW PL EA SP SPX d1 n1 d2 n2 HEAP HS FROK LE AG HW1 HW2.
  pose proof (lib_state_h_parts _ _ _ _ _ _ HS) as PARTS.
  eapply lib_state_hc_agreeA; [exact HS|]. eapply agree_on_mono; [exact AG|]. intros x Hx. split.
  - eapply (own_fp_clientA cxo hs st m OW LB PL EA SPX USTACK_TOP (OW ++ LB) SP x HS FROK); [| | exact Hx]; intros b Hb; apply in_or_app; [left | right]; exact Hb.
  - assert (FW : Forall (w_okc OW LB st PL EA SPX cxo hs) [(d1, d1 + n1); (d2, d2 + n2)]) by (constructor; [exact HW1 | constructor; [exact HW2 | constructor]]).
    pose proof (own_fp_outside s OW LB m HEAP st PL EA SPX USTACK_TOP PARTS FROK cxo hs _ x FW (own_fpA_fpc _ _ _ _ _ _ _ Hx)) as O.
    cbn [outside] in O. tauto.
Qed.

Theorem lib_state_h_heap_pres : forall cxo hs s m m' OW LB PL EA L SP SPX BX,
  lib_state_hc cxo hs s m OW PL EA -> frames_ok LB PL SPX BX -> SP <= SPX -> BX <= USTACK_TOP -> agree_on (aclient_addr L SP) m m' ->
  (forall b, In b OW -> In b L) -> (forall b, In b LB -> In b L) ->
  lib_state_hc cxo hs s m' OW PL EA.
Proof.
  intros cxo hs s m m' OW LB PL EA L SP SPX BX HS FROK LE BXT HP HI HI2. eapply lib_state_hc_agreeA; [exact HS|].
  eapply agree_on_mono; [exact HP|]. intros a Ha. exact (own_fp_clientA cxo hs s m OW LB PL EA SPX BX L SP a HS FROK HI HI2 Ha).
Qed.
Theorem lib_state_h_free : forall st LB cxo hs s m m' OW PL EA r p D SP SPX BX,
  AHEAP st OW LB m -> lib_state_hc cxo hs s m OW PL EA -> frames_ok LB PL SPX BX -> SP <= SPX -> BX <= USTACK_TOP ->
  In r hs -> vref r s -> bn_d (getbn r s) = Some p -> In (p, D, 8 * Z.of_nat (bn_dmax (getbn r s))) OW ->
  agree_on (aclient_addr (lb_remove p (OW ++ LB)) SP) m m' ->
  lib_state_hc cxo hs s m' (lb_remove p OW) PL EA.
Proof.
  intros st LB cxo hs s m m' OW PL EA r p D SP SPX BX HEAP HS FROK LE BXT Hr HV Ed Hin HP.
  pose proof (lib_state_h_parts _ _ _ _ _ _ HS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  assert (HS' : lib_state_hc cxo hs s m' OW PL EA).
  { eapply lib_state_hc_agreeA; [exact HS|]. eapply agree_on_mono; [exact HP|]. intros a Ha.
    destruct (BgLayer.own_fp_blockA OW s PL EA PARTS cxo hs a Ha) as [HL|[(q & A & n & Hq & Hx & _)|(iv & Hiv & Hxi)]]; [apply libw_clientA; exact HL| |].
    - right; right. exists (q, A, n). split; [|exact Hx]. apply lb_remove_In. split; [apply in_or_app; left; exact Hq|].
      cbn [blk_id fst]. intros ->. destruct (AH_addr_unique OW p A n D _ ND Hq Hin) as [-> ->].
      eapply (own_fp_not_limbs st OW LB m HEAP s PL EA SPX BX PARTS FROK cxo hs a r p D); eauto using own_fpA_fpc.
    - right; right. destruct (frame_iv_blk LB PL SPX BX FROK iv Hiv) as (b & Hb & R1 & R2). exists b. split; [| lia].
      apply lb_remove_In. split; [apply in_or_app; right; exact Hb|]. intros E.
      pose proof (AH_nodup _ _ _ _ HEAP) as NDa. rewrite map_app in NDa.
      eapply (nodup_app_disj _ _ p NDa); [change p with (blk_id (p, D, 8 * Z.of_nat (bn_dmax (getbn r s)))); apply in_map; exact Hin | rewrite <- E; apply in_map; exact Hb]. }

  pose proof HS' as (HC & (HE1 & HE2) & HO & (S1 & S2 & S3 & HM)).
  pose proof (bn_in_m r s p HV Ed) as Hpm. pose proof (ids_m_nodup _ _ _ IDS) as NDm.
  assert (KEEP : forall q A n, q <> p -> In (q, A, n) OW -> In (q, A, n) (lb_remove p OW)) by (intros q A n NE H; apply lb_remove_In; split; [exact H| exact NE]).
  assert (KPL : forall q A n, In q (pl_ids PL) -> In (q, A, n) OW -> In (q, A, n) (lb_remove p OW)).
  { intros q A n Hq H. apply KEEP; [|exact H]. intros ->. eapply (ids_pl_m s PL EA p p IDS); eauto. }
  split; [exact HC|]. split.
  { split; [exact HE1|]. eapply BnRepA.err_mem_agree; [apply agree_on_refl| intros a Ha; exact I| intros x Hx; exact I| | exact HE2].
    intros q A n Hq. apply KEEP. intros ->. eapply (ids_ea_m _ _ _ p p IDS); eauto. }
  split; [exact HO|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  eapply (gen_transport (fun _ => True)); [exact HM| apply agree_on_refl| auto| | | | | | auto|].
  - intros ac qc Ec H. apply KPL; [eapply in_pl_ids_ctx; exact Ec| exact H].
  - intros q H Hq HinH. apply KEEP; [|exact HinH]. intros ->. eapply (ids_bn_item_neq r s p p); eauto.
  - intros q Ix Eq HinI. apply KEEP; [|exact HinI]. intros ->. eapply (ids_bn_idx_neq r s p p); eauto.
  - intros am qm Em H. apply KPL; [eapply in_pl_ids_mont; exact Em| exact H].
  - intros r' p' Hr' E OK. destruct p' as [a q off|a|a d|a]; try exact OK. destruct OK as (n & Hin' & H1 & H2). exists n. split; [|lia].
    destruct (pl_of_cases PL r' _ E) as [[_ E']|[(am & qm & M & Em & E' & _)|[S Eb]]]; [discriminate E'| |].
    + injection E' as Ea Eq Eo. subst q. apply KPL; [eapply in_pl_ids_mont; exact Em| exact Hin'].
    + apply KPL; [eapply in_pl_ids_bn; [exact Hr'| exact Eb]| exact Hin'].
  - intros r' a' HA' [Hh|HR]; [left; exact Hh|]. destruct (in_dec Nat.eq_dec r' hs) as [Hi|Hni]; [left; exact Hi|]. right.
    eapply (bn_rep_transport (fun _ => True)); [apply agree_on_refl| auto| | exact HR].
    intros p' D' Ed' Hin'. apply KEEP; [|exact Hin']. intros ->. assert (NE : r <> r') by (intros ->; contradiction).
    eapply (ids_bn_neq r r' s p p); eauto. eapply gen_ref_valid; eauto.
Qed.

Lemma ref_at_range : forall st OW PL EA SPX BX s LB m r a,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX BX -> ref_at st OW PL r a -> r <> ROne ->
  0 < a /\ (a + 24 <= ACEIL \/ (SPX <= a /\ a + 24 < 2^63)) /\ (a + 24 <= 0x10000 \/ 0xbf9000 <= a).
Proof.
  intros st OW PL EA SPX BX s LB m r a HEAP PARTS FROK HA NE.
  destruct (ref_skF OW st PL EA PARTS r a HA) as [q A n HA0 NR Hin R1 R2|p S Eb Hiv HF|Er Ea]; [| | exfalso; exact (NE Er)].
  - pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI). split; [lia|]. split; [left; lia | lia].
  - destruct (sk_frame s OW LB m HEAP st PL EA SPX BX PARTS FROK a HF) as (C1 & I1 & P1). split; [exact P1|]. split; [left; exact C1 | exact I1].
Qed.

Lemma ref_at_rangeF : forall st OW PL EA SPX BX s LB m r a,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX BX -> ref_at st OW PL r a -> r <> ROne ->
  0 < a /\ a + 24 <= ACEIL /\ (a + 24 <= 0x10000 \/ 0xbf9000 <= a).
Proof.
  intros st OW PL EA SPX BX s LB m r a HEAP PARTS FROK HA NE.
  destruct (ref_skF OW st PL EA PARTS r a HA) as [q A n HA0 NR Hin R1 R2|p S Eb Hiv HF|Er Ea]; [| | exfalso; exact (NE Er)].
  - pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI). split; [lia|]. split; [lia | lia].
  - destruct (sk_frame s OW LB m HEAP st PL EA SPX BX PARTS FROK a HF) as (C1 & I1 & P1). split; [exact P1|]. split; [exact C1 | exact I1].
Qed.

Lemma ref_at_blk : forall st OW PL EA SPX BX s LB m r a,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX BX -> ref_at st OW PL r a -> r <> ROne ->
  exists q A n, In (q, A, n) (OW ++ LB) /\ A <= a /\ a + 24 <= A + n.
Proof.
  intros st OW PL EA SPX BX s LB m r a HEAP PARTS FROK HA NE.
  destruct (ref_skF OW st PL EA PARTS r a HA) as [q A n HA0 NR Hin R1 R2|p S Eb Hiv HF|Er Ea]; [| | exfalso; exact (NE Er)].
  - exists q, A, n. split; [apply in_or_app; left; exact Hin | lia].
  - destruct (frame_iv_blk LB PL SPX BX FROK _ HF) as ([[q A] n] & Hb & R1 & R2). cbn [blk_addr blk_size fst snd] in R1, R2. unfold BN_STRUCT_SZ in R2.
    exists q, A, n. split; [apply in_or_app; right; exact Hb | lia].
Qed.

Lemma ref_at_client : forall st OW PL EA SPX BX s LB m r a L SP x,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX BX -> ref_at st OW PL r a -> r <> ROne ->
  SP <= SPX -> BX <= USTACK_TOP -> (forall b, In b OW -> In b L) -> a <= x < a + 24 -> (forall b, In b LB -> In b L) -> aclient_addr L SP x.
Proof.
  intros st OW PL EA SPX BX s LB m r a L SP x HEAP PARTS FROK HA NE LE BXT HI Hx HI2.
  destruct (ref_at_blk st OW PL EA SPX BX s LB m r a HEAP PARTS FROK HA NE) as (q & A & n & Hin & R1 & R2).
  right; right. exists (q, A, n). split; [| cbn [blk_addr blk_size fst snd]; lia].
  apply in_app_or in Hin as [Hin|Hin]; [apply HI | apply HI2]; exact Hin.
Qed.

Lemma bn_arr_rclient : forall st OW PL EA SPX BX s LB m r D L SP x,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX BX -> vref r st -> r <> ROne ->
  bn_arr m OW (pl_of PL r) D (getbn r st) -> SP <= SPX -> BX <= USTACK_TOP -> (forall b, In b OW -> In b L) ->
  D <= x < D + 8 * Z.of_nat (bn_dmax (getbn r st)) -> (forall b, In b LB -> In b L) -> aclient_addr L SP x.
Proof.
  intros st OW PL EA SPX BX s LB m r D L SP x HEAP PARTS FROK HV NE ARR LE BXT HI Hx HI2.
  destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK r D HV NE ARR) as (_ & _ & _ & DC & _ & _).
  unfold bn_arr in ARR. destruct (bn_d (getbn r st)) as [p|] eqn:Ed.
  - destruct ARR as [Hin _]. right; right. exists (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))). split; [apply HI; exact Hin|]. cbn. lia.
  - destruct (pl_of PL r) as [[a q off|a|a d|a]|] eqn:Ep;
      try (destruct ARR as [-> Eb]; unfold bn_dmax in Hx; rewrite Eb in Hx; cbn in Hx; lia).
    +
      destruct ARR as (-> & _ & HL).
      destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exfalso; exact (NE eq_refl)| discriminate E'|].
      destruct (frame_iv_blk LB PL SPX BX FROK (d, d + TMOD_BUF_SZ)) as (b & Hb & X & Y).
      { apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
      cbn [fst snd] in X, Y. right; right. exists b. split; [apply HI2; exact Hb|]. unfold bn_dmax in Hx. rewrite HL in Hx. unfold TMOD_BUF_SZ in Y. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
    + exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NE eq_refl)| discriminate E'|].
      exact (proj2 (proj2 (proj2 (proj1 (proj1 (proj2 PARTS)) r _ Eb)))).
Qed.

Lemma arr_arr_disj : forall st OW PL EA SPX BX s LB m r r' p D D',
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX BX -> r <> r' -> vref r st -> vref r' st -> r' <> ROne ->
  bn_d (getbn r st) = Some p -> In (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) OW -> bn_arr m OW (pl_of PL r') D' (getbn r' st) ->
  D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= D' \/ D' + 8 * Z.of_nat (bn_dmax (getbn r' st)) <= D.
Proof.
  intros st OW PL EA SPX BX s LB m r r' p D D' HEAP PARTS FROK NE HV HV' NRO Ed Hin ARR.
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI).
  destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK r' D' HV' NRO ARR) as (_ & _ & D0 & DC & _ & _).
  pose proof ARR as ARR'. unfold bn_arr in ARR'. destruct (bn_d (getbn r' st)) as [p'|] eqn:Ed'.
  - destruct ARR' as [Hin' _]. exact (BgLayer.limbs_limbs_disj s OW LB m HEAP st PL EA PARTS r r' p D _ p' D' _ NE HV HV' Ed Ed' Hin Hin').
  - destruct (pl_of PL r') as [[a q off|a|a d|a]|] eqn:Ep; try (destruct ARR' as [E0 E]; unfold bn_dmax at 2; rewrite E; cbn; subst D'; unfold DATA_ONE; lia).
    +
      destruct ARR' as (-> & _ & HL).
      destruct (pl_of_cases PL r' _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exfalso; exact (NRO eq_refl)| discriminate E'|].
      assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
      { apply pl_frames_In. left. exists r'. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
      pose proof (frame_blk_apart s OW LB m HEAP PL SPX BX FROK p D _ _ Hin HFd) as DJ. cbn [fst snd] in DJ.
      unfold bn_dmax at 2. rewrite HL. unfold TMOD_BUF_SZ in DJ. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Theorem lib_state_set_recp : forall s LB SPX BX cxo hs st m m' OW PL EA c bits sh,
  AHEAP s OW LB m -> lib_state_hc cxo hs st m OW PL EA -> frames_ok LB PL SPX BX -> pl_recp PL = Some c ->
  munch [(c, c + RECP_SC_SZ)] m m' -> wmono bgbsegs m m' ->
  rw_cells bgbsegs m' c (recp_cells (set_recp bits sh st)) ->
  lib_state_hc cxo hs (set_recp bits sh st) m' OW PL EA.
Proof.
  intros s LB SPX BX cxo hs st m m' OW PL EA c bits sh HEAP HS FROK Ec MU WM HRC.
  pose proof (lib_state_h_parts _ _ _ _ _ _ HS) as PARTS. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
  pose proof HS as (HC & (HE1 & HE2) & HO & (S1 & S2 & S3 & HM)).
  pose proof (pl_frames_recp PL c Ec) as HFc.
  set (P := fun x => x < c \/ c + RECP_SC_SZ <= x).
  assert (AG : agree_on P m m').
  { eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|]. intros x Hx. cbn [outside fst snd]. subst P. cbn beta in Hx. split; [lia| exact I]. }
  assert (NF : forall x, (c <= x < c + RECP_SC_SZ -> False) -> P x).
  { intros x Hx. subst P. cbn beta. destruct (Z.lt_ge_cases x c); [left; lia|]. destruct (Z.le_gt_cases (c + RECP_SC_SZ) x); [right; lia|]. exfalso. apply Hx. lia. }
  assert (HL' : forall a, libw a -> P a) by (intros a Ha; apply NF; intros Hx; exact (frame_not_libw s OW LB m HEAP PL SPX BX FROK _ a HFc Hx Ha)).
  assert (HL : forall a, BnRepA.libw a -> P a) by (intros a Ha; apply HL'; apply libw_bn; exact Ha).
  assert (NM : forall x, (mont_fp PL x -> False) -> P x).
  { intros x Hx. subst P. cbn beta. destruct (Z.lt_ge_cases x c); [left; lia|]. destruct (Z.le_gt_cases (c + RECP_SC_SZ) x); [right; lia|].
    exfalso. apply Hx. right. exists c. split; [exact Ec| lia]. }
  split; [eapply BnRepA.crypto_statics_agree; eauto|].
  split. { split; [eapply BnRepA.err_statics_agree; eauto|]. eapply BnRepA.err_mem_agree; [exact AG| exact HL| | | exact HE2]; [|auto].
           intros x Hx. apply NF. intros Hc. exact (err_not_frame s OW LB m HEAP st PL EA SPX BX PARTS FROK _ x HFc Hc Hx). }
  split; [exact (lib_cells_agree _ _ _ AG HL HL' HO)|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  eapply (gen_transport2 P _ _ cxo st); [exact HM| exact AG| reflexivity| reflexivity| | auto| auto| auto| auto| auto| | |].
  - intros Ec0 x Hx. apply NM. intros HMx. eapply (cx_not_mont s OW LB m HEAP st PL EA SPX BX PARTS FROK x); eauto.
  - destruct (pl_mont PL) as [[am qm]|] eqn:Em; [|exact I]. left. split; [reflexivity|]. intros x Hx. change (P x).
    assert (PM := proj2 (proj2 (proj1 (proj2 (proj2 (proj2 PARTS)))))). rewrite Em in PM.
    apply NF. intros Hc. exact (frame_blk_excl s OW LB m HEAP PL SPX BX FROK qm am MONT_CTX_SZ _ x PM HFc ltac:(lia) Hc).
  - rewrite Ec. right. exact HRC.
  - intros r a HA [Hh|HRp]; [left; exact Hh|]. destruct (in_dec Nat.eq_dec r hs) as [Hi|Hn]; [left; exact Hi|]. right.
    pose proof (gen_ref_valid _ _ _ _ _ _ _ _ S1 HM HA) as HV.
    eapply bn_rep_transport; [exact AG| | | exact HRp]; [|auto].
    intros x Hx. apply NM. intros HMx. destruct Hx as [Hs|[(p & D & Ed & Hin & Hx)|(y & d & Ep & Hx)]].
    + eapply (struct_not_mont s OW LB m HEAP st PL EA SPX BX PARTS FROK r a x); eauto.
    + eapply (limbs_not_mont s OW LB m HEAP st PL EA SPX BX PARTS FROK r p D x); eauto.
    + destruct (pl_of_cases PL r _ Ep) as [[-> E']|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [discriminate E'| discriminate E'|].
      eapply (framebuf_not_mont s OW LB m HEAP st PL EA SPX BX PARTS FROK r y d x); eauto.
Qed.

Theorem lib_state_set_mont : forall s LB SPX BX cxo hs st m m' OW PL EA am qm ri n0,
  AHEAP s OW LB m -> lib_state_hc cxo hs st m OW PL EA -> frames_ok LB PL SPX BX -> pl_mont PL = Some (am, qm) ->
  munch [(am + 72, am + MONT_CTX_SZ)] m m' -> wmono bgbsegs m m' ->
  rw_cells bgbsegs m' (am + 72) (mont_cells (set_mont ri n0 st)) ->
  lib_state_hc cxo hs (set_mont ri n0 st) m' OW PL EA.
Proof.
  intros s LB SPX BX cxo hs st m m' OW PL EA am qm ri n0 HEAP HS FROK Em MU WM HMC.
  pose proof (lib_state_h_parts _ _ _ _ _ _ HS) as PARTS. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
  pose proof HS as (HC & (HE1 & HE2) & HO & (S1 & S2 & S3 & HM)).
  destruct PARTS as (WFS & PWF & IDS & (PB & PC & PM) & ERRB). pose proof PM as PM0. rewrite Em in PM.
  pose proof (AH_range _ _ _ _ _ _ _ HEAP PM) as (M0 & _ & _ & MC & MI).
  set (P := fun x => x < am + 72 \/ am + MONT_CTX_SZ <= x).
  assert (AG : agree_on P m m').
  { eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|]. intros x Hx. cbn [outside fst snd]. subst P. cbn beta in Hx. split; [lia| exact I]. }
  assert (NM : forall x, (mont_fp PL x -> False) -> P x).
  { intros x Hx. subst P. cbn beta. destruct (Z.lt_ge_cases x (am + 72)); [left; lia|]. destruct (Z.le_gt_cases (am + MONT_CTX_SZ) x); [right; lia|].
    exfalso. apply Hx. left. exists am, qm. split; [exact Em| lia]. }
  assert (PARTS' : lib_parts st OW PL EA) by (split; [exact WFS| split; [exact PWF| split; [exact IDS| split; [split; [exact PB| split; [exact PC| exact PM0]]| exact ERRB]]]]).
  assert (HL : forall a, BnRepA.libw a -> P a).
  { intros a Ha. subst P. cbn beta. pose proof (BgLayer.blk_not_libw s OW LB m HEAP qm am MONT_CTX_SZ a PM) as X.
    destruct (Z.lt_ge_cases a (am + 72)); [left; lia|]. destruct (Z.lt_ge_cases a (am + MONT_CTX_SZ)); [| right; lia].
    exfalso. apply X; [unfold MONT_CTX_SZ in *; lia| apply libw_bn; exact Ha]. }
  assert (HLW : forall a, libw a -> P a).
  { intros a Ha. subst P. cbn beta. pose proof (BgLayer.blk_not_libw s OW LB m HEAP qm am MONT_CTX_SZ a PM) as X.
    destruct (Z.lt_ge_cases a (am + 72)); [left; lia|]. destruct (Z.lt_ge_cases a (am + MONT_CTX_SZ)); [| right; lia].
    exfalso. apply X; [unfold MONT_CTX_SZ in *; lia| exact Ha]. }
  split; [eapply BnRepA.crypto_statics_agree; eauto|].
  split. { split; [eapply BnRepA.err_statics_agree; eauto|]. eapply BnRepA.err_mem_agree; [exact AG| exact HL| | | exact HE2]; [|auto].
           intros x Hx. apply NM. intros HMx. destruct HMx as [(am' & qm' & Em' & Hm')|(c & Ec & Hm')].
           - rewrite Em in Em'. injection Em' as <- <-.
             eapply (BgLayer.err_not_block s OW LB m HEAP st PL EA PARTS' qm am MONT_CTX_SZ x PM); [lia| | exact Hx].
             intros q' Hq'. eapply ids_pl_ea; eauto. eapply in_pl_ids_mont; exact Em.
           - exact (err_not_frame s OW LB m HEAP st PL EA SPX BX PARTS' FROK _ x (pl_frames_recp PL c Ec) Hm' Hx). }
  split; [exact (lib_cells_agree _ _ _ AG HL HLW HO)|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  eapply (gen_transport2 P _ _ cxo st); [exact HM| exact AG| reflexivity| reflexivity| | auto| auto| auto| auto| auto| | |].
  - intros Ec0 x Hx. apply NM. intros HMx. eapply (cx_not_mont s OW LB m HEAP st PL EA SPX BX PARTS' FROK x); eauto.
  - rewrite Em. right. exact HMC.
  - destruct (pl_recp PL) as [c|] eqn:Er; [|exact I]. left. split; [reflexivity|]. intros x Hx. change (P x).
    pose proof (frame_blk_apart s OW LB m HEAP PL SPX BX FROK qm am MONT_CTX_SZ _ PM (pl_frames_recp PL c Er)) as DJ. cbn [fst snd] in DJ. unfold MONT_CTX_SZ in *.
    subst P. cbn beta. lia.
  - intros r a HA [Hh|HRp]; [left; exact Hh|]. destruct (in_dec Nat.eq_dec r hs) as [Hi|Hn]; [left; exact Hi|]. right.
    pose proof (gen_ref_valid _ _ _ _ _ _ _ _ S1 HM HA) as HV.
    eapply bn_rep_transport; [exact AG| | | exact HRp]; [|auto].
    intros x Hx. apply NM. intros HMx. destruct Hx as [Hs|[(p & D & Ed & Hin & Hx)|(y & d & Ep & Hx)]].
    + eapply (struct_not_mont s OW LB m HEAP st PL EA SPX BX PARTS' FROK r a x); eauto.
    + eapply (limbs_not_mont s OW LB m HEAP st PL EA SPX BX PARTS' FROK r p D x); eauto.
    + destruct (pl_of_cases PL r _ Ep) as [[-> E']|[(am' & qm' & _ & _ & E' & _)|[S Eb]]]; [discriminate E'| discriminate E'|].
      eapply (framebuf_not_mont s OW LB m HEAP st PL EA SPX BX PARTS' FROK r y d x); eauto.
Qed.

Lemma bn_arr_facts_w : forall st OW PL EA SPX BX s LB m r D,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX BX -> vref r st -> wref PL r ->
  bn_arr m OW (pl_of PL r) D (getbn r st) ->
  u64arr bgbsegs m D (wlimbs (bn_buf (getbn r st)))
  /\ Z.of_nat (length (wlimbs (bn_buf (getbn r st)))) = Z.of_nat (bn_dmax (getbn r st))
  /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= ACEIL
  /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= 0x10000 \/ 0xbf9000 <= D \/ bn_dmax (getbn r st) = 0%nat)
  /\ (forall r' a', ref_at st OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= a').
Proof.
  intros st OW PL EA SPX BX s LB m r D HEAP PARTS FROK HV WR ARR. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
  destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK r D HV (proj1 WR) ARR) as (U & LEN & D0 & DC & DI & DSEP).
  split; [exact U|]. split; [exact LEN|]. split; [exact D0|]. split; [|split; [exact DI| exact DSEP]].
  pose proof ARR as ARR'. unfold bn_arr in ARR'. destruct (bn_d (getbn r st)) as [p|] eqn:Ed.
  - destruct ARR' as [Hin _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & BC & _). exact BC.
  - destruct (bn_arr_null PL r m OW D _ (proj1 (proj2 PARTS)) WR Ed ARR) as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn. lia.
Qed.

End WithCeilingF3.
Arguments lib_state_frame {AR} s LB SPX BX {cxo}.
Arguments lib_state_h_heap_pres {AR cxo} hs s m m' OW {LB} PL EA L SP SPX BX.
Arguments lib_state_h_free {AR} st LB {cxo}.
Arguments own_fp_libA {AR cxo}.
Arguments lib_state_h_icall {AR} s LB {cxo}.
Arguments lib_state_h_icall2 {AR} s LB {cxo}.
