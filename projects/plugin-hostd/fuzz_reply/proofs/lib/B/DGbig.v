(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGbig.v (commit 8b4ae5e9984e, the Deallocate big arm, closed at cgif; file sha256 c21a1a7787df) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 13 image addresses moved by code-verified function pairs (7 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 8 pcs named in comments; 6 hand maps (resolve-all.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); 2 model labels (YG00 mcheck / spin tags) kept; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: then from plugin-hostd/fuzz_reply lib/A (commit 29bcc0b4b8f) to image B (fuzz_reply.asan-ubsan, pin 10ffb5f9202a, unstripped twin 3389287e1d61) by alreloc 56664a20986eb62e, same unit A -> B. *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane, DeallocNmaxA): the BIG-BLOCK arm of the frame-generic Deallocate walk, over the
   interface DGbigIF.DIfaceBig: a block above the quarantine's max_size (kQuarantineMax < req_size n).

   Quarantine::Put's size test (0x35f7c, compiler-rt llvmorg-20.1.8 sanitizer_quarantine.h:96-108) is not taken:
   RecyclePassThrough (asan_allocator.cpp:255-263) runs FromPrimary's tests and FillChunk (vacuous) and calls
   QuarantineCallback::Recycle (0x35ff8 -> 0x33e88, return 0x35ffc); Put's cache-size test (0x36000) then finds the
   thread cache within its bound (Recycle leaves the queues as they were), and Put and Deallocate return. The model
   is YG00cf.free_cf's recycle side (dbg_shape): depot_put, the chunk's change, recycle_chunk, dmd.

   The walk: DGbigd.segB (entry to StackDepotPut, copied from DGgd), dbg_depot, DGbigf.segC_big (the depot's return to
   Recycle's call, joined at DGbigw.SS_Q), Recycle's contract on the big chunk [dbg_rcs] (DGbigIF: rcc_pre_sec,
   without the cache flag; its post re-hides the dead slot's shadow interior) at the call, TAILR (Recycle's return to
   Put's ret; DGg2.TAILM copied with Put's tail test moved to 0x35ffc), the leaf YGcfMallocComposeERhBase.dealloc_leaf_raw_em_rh
   (DGg2.mid_walk / MemnormDmid.dealloc_mid_em copied). The walk runs at YG0dH.amreal' over YGcfRehidePost.RZ_cf, and
   the leaf's dead set is Recycle's, read at the entry state (YGcfRehidePost.dead_shadow_new_mono_l over
   qx_secs_live). The memory at Recycle's call is
   DGbigIF.dmem_b (dmem_m without the shadow poison).
   Nothing here is a function's proof (rule 24): a walk composition over copied segments and callee contracts. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFew.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFeq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif0reply AGif0n DeallocG DGbase DGgi DGbigm DGfv DGif0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseDG DGif0reply DIfaceR DGbigIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DGfw DGbigw DGbigd DGbigf DGbig1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG ErrnoApart.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT MemnormHitG MemnormSafereply MemnormLocG MemnormLoc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MnRecycle MemnormDmid DGg2.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YFfk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH YG0dH YG0dHc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost YGcfMallocComposeERhBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
(* As DGg2.v / MemnormDmid.v: ErrnoG / ErrnoApart reach YA09, whose non-local [Ltac ::=] turns zify's euclidean-division
   conversion off; the copied scripts were written with it on.  #[local]: the setting stays in this file. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numc := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize,
kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, DFSTACK, DFSTACK_G, KSTACK_CF, TFIB_IMG_END, DEP_STK, SHADOW_OFF,
TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD, TFIB_ERRNO in *.
(* DGg2.cs_case over the big seed: a callee-saved register at Put's ret is the entry one. *)
Ltac cs_case HS HEn Htp :=
lazymatch goal with |- getr _ ?kb = _ => let RR := fresh "RR" in rreg HS kb RR; rewrite RR end;
first [ rewrite HEn by (cbv; lia); first [ refine (DGbigm.Er _ _ _ _ _ _ _ _ _ _ _ _ _); reflexivity | symmetry; refine (DGbigm.Er _ _ _ _ _ _ _ _ _ _ _ _ _); reflexivity ]
| rewrite Htp; reflexivity | symmetry; rewrite Htp; reflexivity ].

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The model: recycle_chunk leaves the thread's quarantine cache as it was.                                       *)
Lemma efa_qs : forall c need b s, apost (ensure_free_array c need b s) (fun r => st_qthread (snd r) = st_qthread s).
Proof.
intros c need b s. unfold ensure_free_array.
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; reflexivity|].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
apply apost_if; intros _.
- apply apost_bind. apply apost_set_region. cbn [fst snd]. apply apost_ret. reflexivity.
- apply apost_bind.
  apply apost_if; intros _; [apply apost_set_region | apply apost_ret]; cbn [fst snd];
  (apply apost_if; intros _; [apply apost_spin | apply apost_ret]); reflexivity.
Qed.
Lemma rta_qs : forall c offs s, apost (return_to_allocator c offs s) (fun r => st_qthread (snd r) = st_qthread s).
Proof.
intros c offs s. unfold return_to_allocator.
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_bind. eapply apost_mono; [|apply (efa_qs c _ true s)]. intros [b s1] E1. cbn [fst snd] in *.
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_set_region. cbn [snd]. transitivity (st_qthread s1); [reflexivity | exact E1].
Qed.
Lemma icin_qs : forall s, apost (init_cache_if_needed s) (fun r => st_qthread (snd r) = st_qthread s).
Proof.
intros s. unfold init_cache_if_needed. apply apost_bind. apply apost_get. cbn [fst snd].
destruct (st_cache_inited s); [apply apost_ret; reflexivity | apply apost_put; reflexivity].
Qed.
Lemma cd_qs : forall c off s, apost (cache_dealloc c off s) (fun r => st_qthread (snd r) = st_qthread s).
Proof.
intros c off s. unfold cache_dealloc.
apply apost_bind. eapply apost_mono; [|apply icin_qs]. intros [[] s1] E1. cbn [fst snd] in *.
apply apost_bind. apply apost_get_pc. cbn [fst snd].
apply apost_bind.
eapply apost_mono with (Q := fun r => st_qthread (snd r) = st_qthread s).
2:{ apply apost_if; intros _.
    - apply apost_bind. eapply apost_mono; [|apply rta_qs]. intros [[] s2] E2. cbn [fst snd] in *.
      apply apost_set_pc. cbn [snd]. transitivity (st_qthread s2); [reflexivity|]. rewrite E2. exact E1.
    - apply apost_ret. exact E1. }
intros [[] s3] E3. cbn [fst snd] in *.
apply apost_bind. apply apost_get_pc. cbn [fst snd].
apply apost_set_pc. cbn [snd]. transitivity (st_qthread s3); [reflexivity | exact E3].
Qed.
Lemma sd_qs : forall r s, apost (sec_dealloc r s) (fun x => st_qthread (snd x) = st_qthread s).
Proof.
intros r s. unfold sec_dealloc.
apply apost_bind. apply apost_get. cbn [fst snd].
destruct (nth_error (st_secs s) r) as [sm|]; [destruct (index_of (st_sec_arr s) r 0%nat) as [i|]|].
2-3: apply apost_fail.
apply apost_bind.
eapply apost_mono with (Q := fun x => st_qthread (snd x) = st_qthread s).
2:{ apply apost_if; intros _; [|apply apost_ret; reflexivity].
    apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
    apply apost_if; intros _; [apply apost_ret; reflexivity | apply apost_spin]. }
intros [[] s1] E1. cbn [fst snd] in *.
apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
apply apost_modify. cbn [snd]. transitivity (st_qthread s1); [reflexivity | exact E1].
Qed.
Lemma recycle_chunk_q : forall k X, apost (recycle_chunk k X) (fun r => st_qthread (snd r) = st_qthread X).
Proof.
intros k X. unfold recycle_chunk.
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_put. cbn [fst snd].
destruct (ck_beg k) as [|off|r o|c q]; try apply apost_fail.
- eapply apost_mono; [|apply cd_qs]. intros x E. rewrite E. reflexivity.
- eapply apost_mono; [|apply sd_qs]. intros x E. rewrite E. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The zones the depot and the seed's frame use, against the big seed's windows (DGg1's section WKm, copied over
   DGbigm without the block's shadow).                                                                               *)
Lemma IAL_transfer_b : forall (W : world tfibsegs) (m1 m2 : word -> option byte),
(forall a, DGbigm.IZONE a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) -> DGbigm.IAL_POST W m1 -> DGgi.IAL_POST W m2.
Proof.
intros W m1 m2 E I. unfold DGbigm.IAL_POST, DGgi.IAL_POST in *. cbv zeta in *. destruct I as (I1 & I2 & I3 & I4 & I5).
assert (V : forall a (w : nat) v, (forall k, (k < w)%nat -> DGbigm.IZONE (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict (w_H W) m1) a w v -> val_mem tfibsegs (mrestrict (w_H W) m2) a w v).
{ intros a w v Hz Hv. apply (YF0x.val_mem_frame (w_H W) m1 m2 a w v); [intros k Hk; apply E, Hz, Hk | exact Hv]. }
split; [apply V; [intros k Hk; unfold DGbigm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *; lia | exact I1]|].
split; [apply V; [intros k Hk; unfold DGbigm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *; lia | exact I2]|].
split; [apply V; [intros k Hk; unfold DGbigm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IAL_W in *; lia | exact I3]|].
split; [apply V; [intros k Hk; unfold DGbigm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IAL_W in *; lia | exact I4]|].
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) m1 m2 a). 2:{ apply E. unfold DGbigm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *. lia. }
exact (I5 a Ha).
Qed.

Section WKb.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (tr : list Z).
Variables (p nn hb1 : Z) (q : qcache) (j1 j2 j3 : Z).
Variable regsU : bvmap 5 word.
Hypothesis FH : DGbigm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU.
Local Notation sp0 := (bv_unsigned (getr regs0 2)).
Local Notation WIN := (DGbigm.WIN ly regs0 p).
Local Notation LYBm := (DGbigm.LYB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation LYDm := (DGbigm.LYD W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation DRm := (DGbigm.derived_ranges W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Lemma sp_facts_b : ly_stk_lo ly + DFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof.
pose proof (DGbigm.fh_Hsp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (S1 & S2 & S3). pose proof LYBm as LB.
destruct LB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L1 & L2). repeat split; assumption.
Qed.
Lemma DZONE_out_b : forall a, DGbigm.DZONE ly a ->
~ WIN a /\ ~ DGbigm.IZONE a /\ 0 <= a < 2 ^ 64 /\ ~ (sp0 - DFSTACK <= a < sp0).
Proof.
intros a Hd. pose proof LYBm as LB. pose proof DRm as DR. pose proof sp_facts_b as SPF.
pose proof LYDm as (_ & _ & (_ & _ & NBSTK) & (_ & SBSTK) & _). unfold zdisjoint in NBSTK, SBSTK. cbn [fst snd] in NBSTK, SBSTK.
unfold DGbigm.DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]].
- split; [apply (DGbigm.notWIN_img W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH); unfold TFIB_IMG_LO, TFIB_IMG_END; lia|].
  unfold DGbigm.IZONE. clear - Hd DR SPF LB. numc. repeat split; lia.
- split; [apply (DGbigm.notWIN_NB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH); exact Hd|].
  unfold DGbigm.IZONE. clear - Hd DR SPF LB NBSTK. numc. repeat split; lia.
- split; [apply (DGbigm.notWIN_SB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH); exact Hd|].
  unfold DGbigm.IZONE. clear - Hd DR SPF LB SBSTK. numc. repeat split; lia.
Qed.
Lemma CZONE_out_b : forall a, CZONE ly a -> ~ WIN a.
Proof.
intros a Hc. pose proof LYBm as LB.
unfold CZONE in Hc. destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]].
- apply (DGbigm.notWIN_img W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH). unfold TFIB_IMG_LO, TFIB_IMG_END. lia.
- apply (DGbigm.notWIN_shb W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH). unfold kLowShadowBeg, kHighMemBeg. lia.
- apply (DGbigm.notWIN_Thead W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH). lia.
- apply (DGbigm.notWIN_C W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH). lia.
- apply (DGbigm.notWIN_img W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH). unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_TSD in *. lia.
- apply (DGbigm.notWIN_D W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH). lia.
Qed.
Lemma IZONE_out_b : forall a, DGbigm.IZONE a ->
~ WIN a /\ ~ DGbigm.DZONE ly a /\ 0 <= a < 2 ^ 64 /\ ~ (sp0 - 48 - DEP_STK <= a < sp0 - 48).
Proof.
intros a Hz. pose proof LYBm as LB. pose proof DRm as DR. pose proof sp_facts_b as SPF.
split; [apply (DGbigm.notWIN_img W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH); unfold DGbigm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *; lia|].
unfold DGbigm.IZONE, DGbigm.DZONE in *. clear - Hz DR SPF LB. numc. repeat split; lia.
Qed.
(* The memory at Put's call of Recycle (DGbigf.at_RCY), composed with the depot's and the seed's frames. *)
Lemma dmem_b_ok : forall (DP : (word -> option byte) -> Prop) (msm mem4 mem' : word -> option byte),
DGbigm.MEQI W ly regs0 mem0 p msm ->
(forall x : word, ~ (sp0 - 48 - DEP_STK <= bv_unsigned x < sp0 - 48) -> ~ DGbigm.DZONE ly (bv_unsigned x) -> mem4 x = msm x) ->
(forall a, apresent (w_H W) msm a -> apresent (w_H W) mem4 a) ->
DP mem4 ->
DGbigf.EQ4a ly regs0 p mem4 mem' ->
(forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W) mem' a) ->
(forall a, DGbigm.WINT ly a \/ DGbigm.WINB p a -> apresent (w_H W) mem' a) ->
val_mem tfibsegs (mrestrict (w_H W) mem') (p - 16) 4 (3 + 256 * hb1) ->
val_mem tfibsegs (mrestrict (w_H W) mem') (p - 12) 4 nn ->
val_mem tfibsegs (mrestrict (w_H W) mem') (ly_T ly + t_unwinding) 1 0 ->
dmem_b W ly sp0 mem0 p nn hb1 DP mem'.
Proof.
intros DP msm mem4 mem' [MQ IALm] Hfr4 Hpr4 HDP EQ4 PRS PRW V1 V2 V3.
assert (W2D : forall a, DGbigm.WIN2 ly regs0 p a -> dwin_m ly sp0 p a).
{ intros a Hw. cbv beta zeta delta [DGbigm.WIN2] in Hw. unfold dwin_m.
  destruct Hw as [Hw|[Hw|[Hw|Hw]]]; [left; exact Hw | exfalso; lia | right; left; exact Hw | right; right; exact Hw]. }
assert (WD : forall a, WIN a -> dwin_m ly sp0 p a).
{ intros a Hw. cbv beta zeta delta [DGbigm.WIN] in Hw. unfold dwin_m. exact Hw. }
unfold dmem_b. split.
{ exists mem4. split; [exact HDP|]. split.
  - intros a Hz Hp. destruct (DZONE_out_b a Hz) as (NW & NI & Ra & NST). apply Hpr4.
    apply (apresent_same (w_H W) mem0 msm a); [|exact Hp]. apply MQ; rewrite unsigned_lit_small by exact Ra; assumption.
  - intros x Hz. destruct (DZONE_out_b _ Hz) as (NW & NI & Ra & NST).
    apply EQ4. intros Hw. apply NW. apply DGbigm.WIN2_WIN. exact Hw. }
split.
{ intros x Hw Hz Hi. rewrite (EQ4 x); [| intros X; apply Hw; apply W2D; exact X].
  pose proof sp_facts_b as SPF.
  rewrite (Hfr4 x); [| intros X; apply Hw; left; unfold DEP_STK, DFSTACK, DGbaseC.DFSTACK in *; lia | exact Hz].
  apply MQ; [intros X; apply Hw; apply WD; exact X | exact Hi]. }
split.
{ apply (IAL_transfer_b W msm mem'); [|exact IALm]. intros a Hz. destruct (IZONE_out_b a Hz) as (NW & ND & Ra & NST).
  rewrite (EQ4 (Z_to_bv 64 a)); rewrite ?unsigned_lit_small by exact Ra.
  2:{ intros X. apply NW. apply DGbigm.WIN2_WIN. exact X. }
  apply Hfr4; rewrite unsigned_lit_small by exact Ra; assumption. }
split; [exact PRS|]. split; [exact PRW|]. split; [exact V1|]. split; [exact V2 | exact V3].
Qed.
End WKb.

(* memnorm is kept by a memory that equals [mem0] outside dmem_b's frame zones (MemnormDmid.memnorm_dmem_m copied over
   DGbigm, without the shadow). *)
Lemma memnorm_dmem_b : forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU (sp0 : Z) (mem' : word -> option byte),
  DGbigm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU -> sp0 = bv_unsigned (getr regs0 2) ->
  (forall x : word, ~ dwin_m ly sp0 p (bv_unsigned x) -> ~ DGgi.DZONE ly (bv_unsigned x) ->
    ~ DGgi.IZONE (bv_unsigned x) -> mem' x = mem0 x) ->
  MemnormT.memnorm_keep tfibsegs mem0 mem'.
Proof.
intros W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU sp0 mem' FH E0 MEQ. subst sp0.
pose proof (DGbigm.LYB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH)
  as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & T1 & T2 & T3 & T4 & T5).
pose proof (DGbigm.derived_ranges W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & _).
pose proof (DGbigm.fh_Hsp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (S1 & S2 & S3).
pose proof (DGbigm.fh_Hp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as HP.
pose proof (ASAN_CEIL_range) as [CR _].
apply (MemnormT.memnorm_frame4 tfibsegs (dwin_m ly (bv_unsigned (getr regs0 2)) p) (DGgi.DZONE ly) DGgi.IZONE
  (fun _ => False) mem0 mem').
- intros x Hw. unfold dwin_m, DGgmC.WINT, DGgmC.WINB in Hw. cbv beta zeta in Hw.
  destruct Hw as [Hw|[[Hw|Hw]|[Hw|Hw]]].
  + apply MemnormHitG.mn_safe_high.
    unfold DGbaseC.DFSTACK, DGbase.DFSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
  + apply (MemnormLoc.mn_safe_zone3 (ly_T ly) kThreadObjSize x F1); [|exact F2].
    unfold t_unwinding, kThreadObjSize in *. lia.
  + apply (MemnormLoc.mn_safe_zone3 (ly_T ly) kThreadObjSize x F1); [|exact F2].
    unfold t_stats, kThreadObjSize in *. lia.
  + apply (MemnormLoc.mn_safe_zone3 (p - 16) (DGbigm.N8v nn + 16) x HP); lia.
  + apply (MemnormLoc.mn_safe_zone3 (p - 16) (DGbigm.N8v nn + 16) x HP); lia.
- intros x Hd. unfold DGgi.DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]].
  + apply MemnormSafereply.mn_safe_rw. unfold TASK_SIZE. lia.
  + pose proof (zone3_off_img _ _ _ F9 Hd) as O.
    apply MemnormSafereply.mn_safe_offimg; unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TASK_SIZE in *; lia.
  + pose proof (zone3_off_img _ _ _ F11 Hd) as O.
    apply MemnormSafereply.mn_safe_offimg; unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TASK_SIZE in *; lia.
- intros x Hz. unfold DGgi.IZONE in Hz. apply MemnormSafereply.mn_safe_rw.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TASK_SIZE in *. lia.
- intros x [].
- intros x H1 H2 H3 _. exact (MEQ x H1 H2 H3).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. From Deallocate's entry to Put's call of Recycle (DGg1.to_enq copied): DGbigd.segB, StackDepotPut (dbg_depot),
   the model's depot answer and the chunk's change, DGbigf.segC_big; the memory at the call is dmem_b.               *)
(* The walk runs at YG0dH.amreal' over the zone YGcfRehidePost.RZ_cf: Recycle's contract (dbg_rcs) re-hides the dead
   slot's shadow interior. The steps before and after Recycle are free-less, and lift by SRr_SRr'. *)
Local Notation SRr'b := (YA0nH.SRr' tfibsegs YGcfRehidePost.RZ_cf).
Local Notation amreal'b := (YG0dH.amreal' tfibsegs YGcfRehidePost.RZ_cf).
Lemma SRr'_bind_b : forall (W : world tfibsegs) c (R Q : world tfibsegs -> config -> Prop),
SRr'b W c R -> (forall W' c', YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf W W' -> R W' c' -> SRr'b W' c' Q) -> SRr'b W c Q.
Proof. exact (YA0nH.SRrG_bind tfibsegs (YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans tfibsegs YGcfRehidePost.RZ_cf)). Qed.
Lemma SRr'_ret_b : forall (W : world tfibsegs) c (Q : world tfibsegs -> config -> Prop), Q W c -> SRr'b W c Q.
Proof. exact (YA0nH.SRrG_ret tfibsegs (YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf) (YA0nH.wle'_refl tfibsegs YGcfRehidePost.RZ_cf)). Qed.
(* Recycle's dead set is read at its call state qx S k z tr; the leaf reads it at the entry S
   (YGcfRehidePost.dead_shadow_new_mono_l). qx keeps st_secs, so every slot live at qx S k z tr is live at S with the
   same length. *)
Lemma qx_secs_live : forall S k z tr r sm0, nth_error (st_secs (qx S k z tr)) r = Some sm0 -> sm_live sm0 = true ->
exists sm2, nth_error (st_secs S) r = Some sm2 /\ sm_live sm2 = true /\ sm_len sm2 = sm_len sm0.
Proof.
intros S k z tr r sm0 H1 H2. exists sm0.
assert (QS : st_secs (qx S k z tr) = st_secs S) by (unfold qx, dtick, YFl0C.depot_after; destruct (z =? 0); reflexivity).
rewrite QS in H1. split; [exact H1|]. split; [exact H2 | reflexivity].
Qed.
Lemma wvb_self_b : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Section e.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variables (ARX ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world tfibsegs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Hypothesis IFB : DIfaceBig B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq.
(* The image facts the copied errno scripts read (DGg2.v:602-605). *)
Hypothesis EAimg : ErrnoApart.errno_in_img.
Hypothesis EAz3 : ErrnoApart.errno_apart_zone3_d.
Hypothesis EAdz : ErrnoApart.errno_apart_dzone_d.
Hypothesis EAiz : ErrnoApart.errno_apart_izone.
Local Notation Finst := (dbg_inst B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fview := (dbg_view B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fshape := (dbg_shape B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fdepot := (dbg_depot B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fdaok := (dbg_dpost_aok B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Frq := (dbg_rq B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Freq := (dbg_requar_e B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fpost := (dbg_post B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fqsize := (dbg_qsize B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fframe := (dbg_frame B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fstack := (dbg_stack B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fown := (dbg_owned B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fown_i := (dbg_owned_i B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).

Lemma to_rcy : forall inst so bp ly S W regs mem md p n tr k hb1 j1 j2 j3 (Q : unit * astate -> world tfibsegs -> config -> Prop),
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> In (p, n) (blocks S) ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
0 <= hb1 < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
DGbigm.free_hyps W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs ->
(forall z (msE : machine_state) mat E5, aok (dtick S) (KDepot tr) z ->
  msE = mkst (ms_regs msE) (w64 0x33e88) (ms_mem msE) (seg_rom tfibsegs) ->
  (forall k0, (k0 < aHAVf)%nat ->
    ew E5 k0 = ew (DGbigm.E0 ly (dregs regs (sptr_addr B ly p) inst bp so) tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) k0) ->
  st_ok tfibsegs E5 DGbigw.SS_Q (restrict (w_H W) msE) ->
  dmem_b W ly (bv_unsigned (getr regs 2)) mem (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) (ms_mem msE) ->
  amreal'b ((recycle_chunk (qk k) ;; dmd dbody) (qx S k z tr)) W (mkCfg msE (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
amreal'b (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md) Q.
Proof using IFB TS.
intros inst so bp ly S W regs mem md p n tr k hb1 j1 j2 j3 Q PRE HBLK Hf Hst Hhb1 Hhdr FH HC.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
pose proof (dvb_nonnull B W ly inst mem S p n (Fview inst ly S W mem md p n HARX HRP HFP HBLK)) as PNN.
rewrite (Fshape inst ly W mem md p n tr S k HARX PNN HRP HBLK Hf Hst).
set (pa := sptr_addr B ly p) in *. set (nn := req_size n) in *. set (q := st_qthread S) in *.
set (regs0 := dregs regs pa inst bp so) in *.
unfold spZ, raZ in *.
assert (R2 : getr regs0 2%bv = getr regs 2%bv) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
pose proof (sp_facts_b W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as SPF. rewrite R2 in SPF. unfold DFSTACK in SPF.
assert (Usp : 0 <= bv_unsigned (getr regs 2) < 2 ^ 64) by apply u64_range.
assert (BP0 : bv_unsigned (getr regs0 12) = bp).
{ unfold regs0. rewrite dregs_12. unfold w64. apply unsigned_lit_small. clear - SPF Usp Hbp1 Hbp2. unfold kHighMemEnd, kHighMemBeg in *. lia. }
pose proof (DGbigm.LYB W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as LB.
pose proof (DGbigm.derived_ranges W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as DR.
pose proof (DGbigm.N8_ge W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as [N8a N8b].
pose proof (DGbigm.fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as ZP.
pose proof (DGbigm.fh_Hp10 _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hp10.
pose proof (DGbigm.fh_Hnn _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hnn. unfold kQuarantineMax in Hnn.
unfold depot_put. cbn [bind askz ibind]. apply YG0dHc.amreal'_ask_depot.
unfold cfg_at. rewrite <- (wvb_self_b md) at 1.
eapply SRr'_bind_b; [exact (YA0nH.SRr_SRr' tfibsegs YGcfRehidePost.RZ_cf _ _ _ (DGbigd.segB W ly regs0 mem md tr pa nn hb1 q j1 j2 j3 regs (m_vm_materialized md) FH))|].
intros W1 c1 _ (-> & msD & mat1 & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2.
rewrite (HEn3 2%nat ltac:(cbv; lia)), (DGbigm.E2 ly regs0 tr pa nn hb1 q j1 j2 j3) in Q2.
assert (SPD : bv_unsigned (getr (ms_regs msD) 2) = bv_unsigned (getr regs0 2) - 48).
{ rewrite Q2. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. rewrite R2. clear - SPF Usp. numc. lia. }
rewrite HshD. eapply SRr'_bind_b.
{ apply YA0nH.SRr_SRr'. apply (Fdepot inst ly S W mem md tr (ms_regs msD) (ms_mem msD) (with_vm_backing (m_vm_lazy md) mat1 md) bp HARX Htr).
  - intros x Hx. apply (proj1 MEQD).
    + destruct Hx as [Hd|[Hc _]]; [exact (proj1 (DZONE_out_b W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH _ Hd)) |
      exact (CZONE_out_b W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH _ Hc)].
    + destruct Hx as [Hd|[_ Hi]]; [exact (proj1 (proj2 (DZONE_out_b W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH _ Hd))) | exact Hi].
  - rreg HS (10%bv : bv 5) R. rewrite R, (HEn3 12%nat ltac:(cbv; lia)), (DGbigm.E12 ly regs0 tr pa nn hb1 q j1 j2 j3).
    unfold regs0. rewrite dregs_12. reflexivity.
  - rreg HS (11%bv : bv 5) R. rewrite R, (HEn3 36%nat ltac:(cbv; lia)), (DGbigm.EaLEN ly regs0 tr pa nn hb1 q j1 j2 j3). reflexivity.
  - rreg HS (3%bv : bv 5) R. rewrite R, (HEn3 3%nat ltac:(cbv; lia)), (DGbigm.Er ly regs0 tr pa nn hb1 q j1 j2 j3 3 3%bv eq_refl).
    unfold regs0. rewrite dregs_other by (vm_compute; discriminate). exact Hgp.
  - rreg HS (4%bv : bv 5) R. rewrite R. reflexivity.
  - rreg HS (1%bv : bv 5) R. rewrite R. apply YK0s.ret_ok_even. reflexivity.
  - intros i Hi. pose proof (TRQ i Hi) as TQ. rewrite BP0 in TQ. exact TQ.
  - exact Hbp3.
  - clear - SPF Hbp1. lia.
  - exact Hbp2.
  - right. rewrite SPD, R2. lia.
  - rewrite SPD, R2. replace (bv_unsigned (getr regs 2) - 48) with (bv_unsigned (getr regs 2) + (-3) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal.
  - rewrite SPD, R2. clear - SPF. unfold DEP_STK, YFl0C.DEP_STK in *. lia.
  - rewrite SPD, R2. lia.
  - intros a Ha. rewrite SPD in Ha. apply PRESD. unfold DEP_STK, YFl0C.DEP_STK, DFSTACK in *. lia. }
intros W2 c2 _ (-> & z & regs4 & mem4 & mat4 & -> & HP4 & Hfr4 & Hpr4 & DP4). srr_norm_model.
rewrite SPD in Hfr4.
pose proof (Fdaok _ _ _ _ _ _ _ DP4) as AOK.
rewrite Q1. eapply SRr'_bind_b.
{ apply YA0nH.SRr_SRr'. apply (DGbigf.segC_big W ly regs0 mem md tr pa nn hb1 q j1 j2 j3 regs FH msD E3 regs4 mem4 mat4).
  split; [exact HshD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact HP4|]. split; [exact Hfr4|].
  split; [exact Hpr4|]. split; [exact MEQD | exact PRESD]. }
intros W3 c3 _ (-> & msE & matE & E5 & -> & HshE & HEn5 & HS5 & EQE & PRES5).
apply SRr'_ret_b. exists z. split; [exact AOK|].
assert (BT : bv_unsigned (ew E5 32) = ly_T ly).
{ rewrite (HEn5 32%nat ltac:(cbv; lia)), (DGbigm.EaT ly regs0 tr pa nn hb1 q j1 j2 j3). unfold w64. apply unsigned_lit_small.
  destruct LB as (LB1 & LB2 & _). clear - LB1 LB2. numc. lia. }
assert (B10 : bv_unsigned (ew E5 10) = pa).
{ rewrite (HEn5 10%nat ltac:(cbv; lia)), (DGbigm.E10 ly regs0 tr pa nn hb1 q j1 j2 j3), Hp10. unfold w64. apply unsigned_lit_small.
  clear - DR N8a. numc. lia. }
assert (R38 : rho_of E5 38%nat = 2 + 256 * hb1).
{ unfold rho_of. rewrite (HEn5 38%nat ltac:(cbv; lia)), (DGbigm.EaHW ly regs0 tr pa nn hb1 q j1 j2 j3). unfold w64, DGbigm.HWv.
  apply unsigned_lit_small. lia. }
assert (T1V : zev (rho_of E5) T1term = 3 + 256 * hb1) by (apply T1_val; [exact Hhb1 | exact R38]).
assert (OT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_img a) by (intros a Ha; exact (zone3_off_img _ _ a (proj1 LB) Ha)).
assert (OP : forall a, pa - 16 <= a < pa + 8 -> off_img a) by (intros a Ha; apply (zone3_off_img _ _ a ZP); lia).
assert (DM : dmem_b W ly (bv_unsigned (getr regs0 2)) mem pa nn hb1 (dpost inst ly S W tr z) (ms_mem msE)).
{ apply (dmem_b_ok W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH (dpost inst ly S W tr z) (ms_mem msD) mem4 (ms_mem msE)
    MEQD Hfr4 Hpr4 DP4 EQE PRES5).
  - intros a [[Ha|Ha]|[Ha|Ha]].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 35 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BT; clear - Ha; unfold t_unwinding in *; lia
      | apply OT; clear - Ha; unfold kThreadObjSize, t_unwinding in *; lia].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 36 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BT; clear - Ha; unfold t_stats in *; lia
      | apply OT; clear - Ha; unfold kThreadObjSize, t_stats in *; lia].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 37 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite B10; clear - Ha; lia
      | apply OP; clear - Ha; lia].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 38 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite B10; clear - Ha; lia
      | apply OP; clear - Ha; lia].
  - memv HS5 37%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite B10; lia | apply DGbigf.denot_by_zev; [reflexivity | lia | exact T1V] | lia].
  - memv HS5 37%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite B10; lia
    | cbn [sv_denot]; rewrite (HEn5 39%nat ltac:(cbv; lia)), (DGbigm.EaN ly regs0 tr pa nn hb1 q j1 j2 j3); unfold w64; rewrite Zbv_add_unsigned; f_equal; lia
    | lia].
  - memv HS5 35%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite BT; unfold t_unwinding; lia | reflexivity | lia]. }
rewrite R2 in DM.
pose proof AOK as AOK0.
destruct AOK as [-> | [-> _]].
- cbn [Z.eqb ret ibind]. eapply YG0dHc.amreal'_pure; [reflexivity|]. exact (HC 0 msE matE E5 AOK0 HshE HEn5 HS5 DM).
- cbn [Z.eqb bind get ret ibind].
  lazymatch goal with |- context [mcheck ?b1 469488] => destruct b1 end; cbn [mcheck ret ibind]; [|exact I].
  lazymatch goal with |- context [mcheck ?b2 460508] => destruct b2 end; cbn [mcheck ret put ibind]; [|exact I].
  eapply YG0dHc.amreal'_pure; [reflexivity|]. exact (HC 1 msE matE E5 AOK0 HshE HEn5 HS5 DM).
Qed.
End e.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. Put after Recycle returns (0x35ffc). The kept regions of DGbigw.SS_Q are Put's frame above the callee's scratch
   (trimmed to Put's sp, 80 below Deallocate's entry sp), the caller's stack object, QuarantineChunk's frame and the
   seed's empty slot at the entry sp (DGg2's RS_E at DGbigw.SS_Q).                                                   *)
Definition r0Q : YP09.region := Eval vm_compute in nth 0 (ss_mem DGbigw.SS_Q) (YP09.mkRegion None 0 0 0 0 []).
Definition r1Q : YP09.region := Eval vm_compute in nth 1 (ss_mem DGbigw.SS_Q) (YP09.mkRegion None 0 0 0 0 []).
Definition r2Q : YP09.region := Eval vm_compute in nth 2 (ss_mem DGbigw.SS_Q) (YP09.mkRegion None 0 0 0 0 []).
Definition r3Q : YP09.region := Eval vm_compute in nth 3 (ss_mem DGbigw.SS_Q) (YP09.mkRegion None 0 0 0 0 []).
Definition r4Q : YP09.region := Eval vm_compute in nth 4 (ss_mem DGbigw.SS_Q) (YP09.mkRegion None 0 0 0 0 []).
Definition RS_Q : smem := [trim_lo r0Q (-80); r1Q; r2Q; r4Q].
Lemma SSQ_mem : ss_mem DGbigw.SS_Q = r0Q :: r1Q :: r2Q :: r3Q :: r4Q :: skipn 5 (ss_mem DGbigw.SS_Q).
Proof. vm_compute. reflexivity. Qed.
Lemma RS_Q_sub : submem RS_Q (ss_mem DGbigw.SS_Q).
Proof.
rewrite SSQ_mem. unfold RS_Q.
apply submem_keep; [apply subregion_trim_lo|].
apply submem_keep; [apply subregion_refl|].
apply submem_keep; [apply subregion_refl|].
apply submem_drop. apply submem_keep; [apply subregion_refl|]. apply submem_nil.
Qed.
Definition SS_TR : sstate := Eval vm_compute in ss_after_call DGbigw.SS_Q RS_Q 112 221180.
(* The thread cache's byte count, which Put reads after Recycle returns (the seed's atom 50, DGbigm.QBv). *)
Definition R_QB : YP09.region :=
YP09.mkRegion (Some 32%nat) (t_qc + 24) (t_qc + 32) 0 0 [YP09.mkChunk (t_qc + 24) (CVal 8 (SOff 50%nat 0))].

Section t.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Variables (ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Lemma TAILR : forall (W W5 : world tfibsegs) (ly : alayout) (S X X' : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (inst so bp : Z) (p : sptr) (n : Z) (tr : list Z) (hb1 j1 j2 j3 : Z)
(msE : machine_state) (mdE : Model) (E5 : env) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
DGbigm.free_hyps W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs ->
msE = mkst (ms_regs msE) (w64 0x33e88) (ms_mem msE) (seg_rom tfibsegs) ->
(forall k0, (k0 < aHAVf)%nat -> ew E5 k0 =
   ew (DGbigm.E0 ly (dregs regs (sptr_addr B ly p) inst bp so) tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) k0) ->
st_ok tfibsegs E5 DGbigw.SS_Q (restrict (w_H W) msE) ->
(forall a, bv_unsigned (getr regs 2) - DFSTACK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) (ms_mem msE) a) ->
(forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly X a /\ ~ AOX ly X' a) ->
YGcfRehidePost.acall_post_x_rh B ARXr AOX inst KSTACK_CF ly X W (ms_regs msE) (ms_mem msE) mdE (fun _ => False) ly X' W5 regs' mem' md' ->
val_mem tfibsegs (mrestrict (w_H W5) mem') (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread S)) ->
SRr tfibsegs W5 (cfg_at tfibsegs 0x35ffc regs' mem' md')
(fun Wo co => Wo = W5 /\ exists regsR memR mat',
  co = cfg_at tfibsegs (bv_unsigned (getr regs 1)) regsR memR (with_vm_backing (m_vm_lazy md') mat' md') /\
  (forall r : bv 5, In r CALLEE_SAVED -> getr regsR r = getr (dregs regs (sptr_addr B ly p) inst bp so) r) /\
  (forall x : word, ~ (bv_unsigned (getr regs 2) - 80 <= bv_unsigned x < bv_unsigned (getr regs 2)) -> memR x = mem' x) /\
  (forall a, bv_unsigned (getr regs 2) - DFSTACK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W5) memR a) /\
  (forall a, aview tfibsegs (w_H W5) mem' a <> None -> aview tfibsegs (w_H W5) memR a <> None)).
Proof.
intros W W5 ly S X X' regs mem inst so bp p n tr hb1 j1 j2 j3 msE mdE E5 regs' mem' md' FH HshE HEn5 HS PRESE NOWN POST RV.
pose proof Hwx_tfa as Hwx.
set (regs0 := dregs regs (sptr_addr B ly p) inst bp so) in *.
set (sp0 := bv_unsigned (getr regs 2)) in *.
destruct POST as (ARX' & LLE & WLE & CS & SIO & FR & PRS).
assert (R2 : getr regs0 2 = getr regs 2) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
assert (R1 : getr regs0 1 = getr regs 1) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
pose proof (DGbigm.LYB W ly regs0 mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs FH) as LB.
pose proof (DGbigm.fh_Hsp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hsp. rewrite R2 in Hsp. fold sp0 in Hsp.
pose proof (DGbigm.fh_Hso _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hso. rewrite R2 in Hso. fold sp0 in Hso.
pose proof (DGbigm.fh_Hra _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hra. rewrite R1 in Hra.
pose proof (DGbigm.fh_Hqb _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HQB.
pose proof (DGbigm.stack_ivs W ly regs0 mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs FH) as SIV.
rewrite R2 in SIV. fold sp0 in SIV.
pose proof (DGbigm.LYD W ly regs0 mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs FH) as LYD.
cbn zeta in LYD. destruct LYD as (_ & (_ & _ & _ & TSTK) & _).
unfold zdisjoint in TSTK. cbn [fst snd] in TSTK.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
(* the registers at Recycle's call *)
rreg HS (2%bv : bv 5) Q2.
rewrite (HEn5 2%nat ltac:(cbv; lia)), (DGbigm.E2 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), R2 in Q2.
assert (SPE : spZ (ms_regs msE) = sp0 - 80).
{ unfold spZ. rewrite Q2. rewrite unsigned_lit_small; [reflexivity|]. clear - Usp Hsp LB. numc. lia. }
unfold ascratch in FR. rewrite SPE in FR, PRS.
assert (BE2 : bv_unsigned (ew (DGbigm.E0 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) 2) = sp0)
  by (rewrite (DGbigm.E2 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), R2; reflexivity).
assert (BE13 : bv_unsigned (ew (DGbigm.E0 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) 13) = bv_unsigned (getr regs0 13))
  by (rewrite (DGbigm.E13 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3); reflexivity).
assert (BE32 : bv_unsigned (ew (DGbigm.E0 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) 32) = ly_T ly).
{ unfold w64. apply unsigned_lit_small.
  destruct LB as ((T1 & T2 & _) & _). clear - T1 T2. ceil. unfold ASAN_CEIL, kThreadObjSize in *. lia. }
assert (BV2 : bv_unsigned (ew E5 2) = sp0) by (rewrite (HEn5 2%nat ltac:(cbv; lia)); exact BE2).
assert (BV13 : bv_unsigned (ew E5 13) = bv_unsigned (getr regs0 13)) by (rewrite (HEn5 13%nat ltac:(cbv; lia)); exact BE13).
assert (BV32 : bv_unsigned (ew E5 32) = ly_T ly) by (rewrite (HEn5 32%nat ltac:(cbv; lia)); exact BE32).
assert (NERR : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. rewrite (ts_errno B TS). destruct LB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L5).
  clear - Ha L5. unfold TFIB_ERRNO, kHighMemBeg in *. lia. }
assert (AGS : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> sp0 - 80 <= a ->
  aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) (ms_mem msE) a).
{ intros a Ha Hge. destruct (NOWN a Ha) as [N1 N2].
  apply FR; [clear - Ha LB Usp; numc; lia | exact N1 | exact N2 | | intros [] | apply YGcfRehidePost.dead_shadow_new_high; clear - Ha LB; numc; lia].
  intros [Hs|Hs]; [clear - Hs Hge; unfold KSTACK_CF in *; lia | exact (NERR a Ha Hs)]. }
assert (HP : regs_preserved (ms_regs msE) regs') by (intros r Hr'; apply CS; exact Hr').
pose proof (st_ok_after_call tfibsegs 112 E5 DGbigw.SS_Q (restrict (w_H W) msE) regs' (mrestrict (w_H W5) mem') RS_Q 221180
  HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) RS_Q_sub ltac:(vm_compute; reflexivity) HP) as HS1.
cbn [ms_mem restrict] in HS1.
assert (KEPT : Forall (region_kept tfibsegs E5 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W5) mem')) RS_Q).
{ unfold RS_Q. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  - apply (DGg2.kept_of_aview E5 W W5); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi trim_lo r0Q]; rewrite BV2.
    + intros a Ha. apply AGS; clear - Ha Hsp LB; [numc; lia | lia].
    + intros a Ha. split; [apply AGS; clear - Ha Hsp LB; [numc; lia | lia]|].
      clear - Ha Hsp LB Usp. numc. lia.
  - apply (DGg2.kept_of_aview E5 W W5); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi r1Q]; rewrite BV13.
    + intros a Ha. apply AGS; clear - Ha Hsp Hso LB; [numc; lia | lia].
    + intros a Ha. clear - Ha. lia.
  - apply (DGg2.kept_of_aview E5 W W5); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi r2Q]; rewrite BV2.
    + intros a Ha. apply AGS; clear - Ha Hsp LB; [numc; lia | lia].
    + intros a Ha. split; [apply AGS; clear - Ha Hsp LB; [numc; lia | lia]|].
      clear - Ha Hsp LB Usp. numc. lia.
  - apply (DGg2.kept_of_aview E5 W W5); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi r4Q]; rewrite BV2.
    + intros a Ha. clear - Ha. lia.
    + intros a Ha. clear - Ha. lia. }
specialize (HS1 KEPT). clear KEPT.
change (ss_after_call DGbigw.SS_Q RS_Q 112 221180) with SS_TR in HS1.
set (En6 := havoc E5 112 (map (getr regs') CLOB)) in HS1.
assert (HEn6 : forall k0, (k0 < aHAVf)%nat -> ew En6 k0 =
  ew (DGbigm.E0 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) k0)
  by (intros k0 Hk0; subst En6; unfold aHAVf in Hk0; rewrite ew_havoc_old by lia; apply HEn5; exact Hk0).
assert (BW2 : bv_unsigned (ew En6 2) = sp0) by (rewrite (HEn6 2%nat ltac:(cbv; lia)); exact BE2).
assert (BW13 : bv_unsigned (ew En6 13) = bv_unsigned (getr regs0 13)) by (rewrite (HEn6 13%nat ltac:(cbv; lia)); exact BE13).
assert (BW32 : bv_unsigned (ew En6 32) = ly_T ly) by (rewrite (HEn6 32%nat ltac:(cbv; lia)); exact BE32).
(* the thread cache's byte count, which Put reads *)
apply (st_ok_add_region _ _ _ R_QB) in HS1;
[ | reflexivity
| unfold R_QB, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
  rewrite BW32;
  split; [destruct LB as ((T1 & _) & _); clear - T1; unfold t_qc; lia|];
  split; [destruct LB as ((T1 & T2 & _) & _); clear - T1 T2; ceil; unfold ASAN_CEIL, kThreadObjSize, t_qc in *; lia|];
  split; [intros o Ho; lia|];
  apply Forall_cons; [|apply Forall_nil];
  eapply (chunk_ok_val tfibsegs En6 _ _ _ 8 (SOff 50%nat 0) (qc_bytes (st_qthread S)));
  [ cbn [sv_denot]; rewrite (HEn6 50%nat ltac:(cbv; lia)),
      (DGbigm.EaQB ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3);
    unfold w64, DGbigm.QBv; rewrite Zbv_add_unsigned; f_equal; lia
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HQB; unfold kQuarantineCacheMax in *; lia
  | cbn; lia
  | change (N.to_nat 8) with 8%nat; eapply val_mem_addr; [exact RV | unfold t_qc; lia] ]
| unfold R_QB, RS_Q; cbn [all_disjoint ss_mem SS_TR]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val trim_lo r0Q r1Q r2Q r4Q];
  rewrite BW2, BW13, BW32;
  destruct LB as ((T1 & T2 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L1 & L2 & L3 & L4 & L5);
  clear - T1 T2 L1 L2 L3 L4 L5 Hsp Hso SIV TSTK Usp; destruct SIV as (IT & _);
  ceil; unfold ASAN_CEIL, kThreadObjSize, t_qc, DFSTACK, kHighMemBeg, kHighMemEnd in *;
  repeat split; lia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W5)) in HS1. clear HS. rename HS1 into HS.
unfold cfg_at. rewrite <- (DGg2.wvb_self md') at 1. change (w64 0x35ffc) with (Z_to_bv 64 221180).
(* Put's cache-size test (0x36000 `bgeu s6, a0`) is decided by atom 50's range (the count is within max_cache_size,
   so no drain); the run goes through Put's epilogue to its ret *)
srr_run_sh tfibtbl_rtF_ok HS.
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) => set (En7 := E) in HS; rename msx into msR end.
assert (HEn7 : forall k0, (k0 < aHAVf)%nat -> ew En7 k0 =
  ew (DGbigm.E0 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) k0)
  by (intros k0 Hk0; subst En7; unfold aHAVf in Hk0; rewrite ?ew_havoc_old by lia; apply HEn6; exact Hk0).
(* the tail writes only Put's and QuarantineChunk's frames *)
assert (FRT : forall x : word, ~ (sp0 - 80 <= bv_unsigned x < sp0) -> ms_mem msR x = mem' x).
{ intros x Hx. rewrite (HF x); [reflexivity|].
all: intros Hw; destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg);
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hrg;
  rewrite ?BW2, ?BW13, ?BW32 in Hrg; clear - Hx Hrg; lia |]);
destruct Hin. }
assert (PRES' : forall a, sp0 - DFSTACK <= a < sp0 -> ~ (sp0 - 80 <= a < sp0) -> apresent (w_H W5) mem' a).
{ intros a Ha N1. destruct (Z_lt_le_dec a (sp0 - 80 - KSTACK_CF)) as [L|L]; [|apply PRS; clear - L N1 Ha; lia].
  assert (EQa : aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) (ms_mem msE) a).
  { destruct (NOWN a ltac:(clear - Ha Hsp LB; numc; lia)) as [M1 M2].
    apply FR; [clear - Ha Hsp LB Usp; numc; lia | exact M1 | exact M2 | | intros [] | apply YGcfRehidePost.dead_shadow_new_high; clear - Ha Hsp LB; numc; lia].
    intros [Hs|Hs]; [clear - Hs L; unfold KSTACK_CF in *; lia | exact (NERR a ltac:(clear - Ha Hsp LB; numc; lia) Hs)]. }
  pose proof (PRESE a Ha) as P. apply apresent_mbyte in P as [b Hb].
  assert (A : aview tfibsegs (w_H W) (ms_mem msE) a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity).
  rewrite <- EQa in A. apply aview_some in A as (b' & Hb' & _).
  exact (mbyte_high_apresent (w_H W5) mem' a b' ltac:(clear - Ha Hsp LB Usp; numc; lia) Hb'). }
assert (PRESR : forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W5) (ms_mem msR) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 80)) as [L1|L1]; [|destruct (Z_lt_le_dec a (sp0 - 48)) as [L2|L2]].
  - apply (apresent_same (w_H W5) mem');
    [ apply FRT; rewrite unsigned_lit_small by (clear - Ha Hsp LB Usp; numc; lia); clear - L1; lia
    | apply PRES'; [exact Ha | clear - L1; lia] ].
  - eapply (st_ok_window_apresent (w_H W5) En7 _ _ 1 _ a HS);
    [ reflexivity
    | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn7 2%nat ltac:(cbv; lia)),
      (DGbigm.E2 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), R2; fold sp0; clear - L1 L2; lia
    | clear - Ha Hsp LB Usp; numc; lia ].
  - eapply (st_ok_window_apresent (w_H W5) En7 _ _ 3 _ a HS);
    [ reflexivity
    | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn7 2%nat ltac:(cbv; lia)),
      (DGbigm.E2 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), R2; fold sp0; clear - L2 Ha; lia
    | clear - Ha Hsp LB Usp; numc; lia ]. }
assert (VIS : forall a, aview tfibsegs (w_H W5) mem' a <> None -> aview tfibsegs (w_H W5) (ms_mem msR) a <> None).
{ intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
  destruct (w_H W5 x) eqn:Hx; [exact (Hv HN)|].
  destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (ms_mem msR x); discriminate|].
  destruct (ms_mem msR x) as [|] eqn:E'; [discriminate|]. clear HN.
  destruct (mem' x) as [b0|] eqn:EE0; [clear Hv | exact (Hv eq_refl)].
  set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  destruct (Z_lt_le_dec a' (sp0 - 80)) as [C1|C1]; [|destruct (Z_lt_le_dec a' sp0) as [C2|C2]].
  - rewrite (FRT x ltac:(clear - C1; lia)) in E'. congruence.
  - destruct (PRESR a' ltac:(clear - C1 C2; unfold DFSTACK; lia)) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
  - rewrite (FRT x ltac:(clear - C2; lia)) in E'. congruence. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W5 En7); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'.
rreg HS (1%bv : bv 5) Q1f.
rewrite (HEn7 1%nat ltac:(cbv; lia)), (DGbigm.E1 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), R1 in Q1f.
split; [reflexivity|]. exists (ms_regs msR), (ms_mem msR), mat'.
split.
{ unfold cfg_at, w64. rewrite Q1f, Z_to_bv_bv_unsigned. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ pose proof (DGbigm.fh_Htp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Htp.
  intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [cs_case HS HEn7 Htp|]). destruct Hr. }
split; [exact FRT|]. split; [exact PRESR | exact VIS].
Qed.
End t.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. The arm.                                                                                                       *)
Section a.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variables (ARX ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world tfibsegs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Hypothesis IFB : DIfaceBig B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq.
Hypothesis EAimg : ErrnoApart.errno_in_img.
Hypothesis EAz3 : ErrnoApart.errno_apart_zone3_d.
Hypothesis EAdz : ErrnoApart.errno_apart_dzone_d.
Hypothesis EAiz : ErrnoApart.errno_apart_izone.
Local Notation Finst := (dbg_inst B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fview := (dbg_view B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Frq := (dbg_rq B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Frcs := (dbg_rcs B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Freq := (dbg_requar_e B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fpost := (dbg_post B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fqsize := (dbg_qsize B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fframe := (dbg_frame B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fstack := (dbg_stack B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fown := (dbg_owned B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).
Local Notation Fown_i := (dbg_owned_i B U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB).

Theorem dealloc_big_em_rh : forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
In (p, n) (blocks S) ->
amreal'b (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md)
(YGcfMallocComposeERhBase.dealloc_leaf_raw_em_rh tfibsegs B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof.
intros inst so bp ly S W regs mem md p n tr PRE HBLK.
pose proof PRE as PRE0.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
pose proof (Finst _ _ _ _ _ _ HARX) as HIO.
pose proof (Fview inst ly S W mem md p n HARX HRP HFP HBLK) as DV.
pose proof DV as [DVn DVnn DVch DVhdr DVpres DVjunk DVzone DVqb].
destruct DVch as (k & Hf & Hst & Hu & Hr & Hgeo).
destruct (DGbig1.FH_m B TS U ARX rpre fpre inst so bp ly S W regs mem md p n tr PRE0 HBLK HIO DV)
  as (hb1 & j1 & j2 & j3 & Hhb1 & Hhdr & FH).
pose proof (DGbigm.derived_ranges W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p)
  (req_size n) hb1 (st_qthread S) j1 j2 j3 regs FH) as DR.
pose proof (DGbigm.LYB W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p)
  (req_size n) hb1 (st_qthread S) j1 j2 j3 regs FH) as LB.
assert (RG2 : getr (dregs regs (sptr_addr B ly p) inst bp so) 2 = getr regs 2) by (apply dregs_other; vm_compute; discriminate).
assert (RG3 : getr (dregs regs (sptr_addr B ly p) inst bp so) 3 = getr regs 3) by (apply dregs_other; vm_compute; discriminate).
assert (Upa : 0 <= sptr_addr B ly p < 2 ^ 64) by (clear - DR; ceil; unfold ASAN_CEIL in *; lia).
assert (NBLK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly ->
  ~ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)).
{ intros a Ha Hb. destruct DVzone as (_ & PST & _ & _).
  pose proof (div8_bounds (req_size n + 7) ltac:(clear - DR; lia)) as D8.
  destruct (PST a ltac:(unfold DGgi.N8v, DGgiC.N8v in *; clear - Hb D8; lia)) as [N1 _]. exact (N1 Ha). }
(* errno / memnorm facts of the copied scripts *)
destruct DVn as [LY IMG _ _ _ _ _].
destruct DVzone as (HZp & _ & _ & HNN).
assert (Hpa : 0 <= sptr_addr B ly p) by (destruct HZp as [Z0 _]; lia).
assert (HSP : ly_stk_lo ly + DGbaseC.DFSTACK <= bv_unsigned (getr regs 2))
  by (unfold DGbaseC.DFSTACK, DFSTACK_G, spZ in *; lia).
assert (EB : forall i, 0 <= i < 4 -> bv_unsigned (w64 (as_errno B + i)) = as_errno B + i)
  by (intros i Hi; rewrite (ts_errno B TS); unfold w64; apply unsigned_lit_small; unfold TFIB_ERRNO; lia).
(* the walk: to Recycle's call, Recycle, Put's tail; the leaf's post without lpost and the path *)
assert (MAIN : amreal'b (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md)
  (fun r Wo co => exists regsR memR mdR, co = cfg_at tfibsegs (raZ regs) regsR memR mdR /\
     YGcfRehidePost.dealloc_post_raw_rh tfibsegs B ARX AOX inst ly S W regs mem md
       (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly (snd r) Wo regsR memR mdR /\
     ErrnoG.errno_kept B mem memR /\ MemnormT.memnorm_keep tfibsegs mem memR)).
{ apply (to_rcy B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody DRq IFB
    inst so bp ly S W regs mem md p n tr k hb1 j1 j2 j3 _ PRE0 HBLK Hf Hst Hhb1 Hhdr FH).
  intros z msE mat E5 AOK HshE HEn5 HS5 DM.
  (* at Recycle's call *)
  pose proof DM as DM0. destruct DM as (_ & DMfr & _ & DMps & _).
  rreg HS5 (1%bv : bv 5) E1r. rreg HS5 (2%bv : bv 5) E2r. rreg HS5 (3%bv : bv 5) E3r. rreg HS5 (4%bv : bv 5) E4r.
  rreg HS5 (10%bv : bv 5) E10r. rreg HS5 (11%bv : bv 5) E11r.
  assert (BV2 : bv_unsigned (ew E5 2) = bv_unsigned (getr regs 2)).
  { rewrite (HEn5 2%nat ltac:(cbv; lia)), (DGbigm.E2 ly (dregs regs (sptr_addr B ly p) inst bp so) tr
      (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), RG2. reflexivity. }
  assert (BV32 : bv_unsigned (ew E5 32) = ly_T ly).
  { rewrite (HEn5 32%nat ltac:(cbv; lia)). unfold w64. apply unsigned_lit_small.
    destruct LB as ((T1 & T2 & _) & _). clear - T1 T2. ceil. unfold ASAN_CEIL, kThreadObjSize in *. lia. }
  assert (BV10 : bv_unsigned (ew E5 10) = sptr_addr B ly p).
  { rewrite (HEn5 10%nat ltac:(cbv; lia)), (DGbigm.E10 ly (dregs regs (sptr_addr B ly p) inst bp so) tr
      (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), dregs_10. unfold w64.
    apply unsigned_lit_small. exact Upa. }
  assert (SPE : spZ (ms_regs msE) = bv_unsigned (getr regs 2) - 80).
  { unfold spZ. rewrite E2r, BV2. apply unsigned_lit_small.
    pose proof (u64_range (getr regs 2)) as U2. unfold spZ in Hlo. clear - DR LB Hlo U2. numc. lia. }
  (* the cut relation and the recycle invariant at the call (dbg_rq) *)
  destruct (Frq inst ly S W mem md p n tr k z hb1 (bv_unsigned (getr regs 2)) (ms_mem msE) mat
    HARX HRP HFP HBLK Htr Hf Hst
    ltac:(unfold DFSTACK_G, DGbaseC.DFSTACK, spZ in *; clear - Hlo; lia)
    ltac:(unfold spZ in *; clear - Hhi; lia)
    ltac:(unfold spZ in *; clear - Hbot; lia)
    ltac:(unfold spZ in *; clear - Hal; lia)
    Hhb1 Hhdr DM0) as (HRr & HDRq & HAOXq).
  rewrite HshE at 1.
  change (mkCfg (mkst (ms_regs msE) (w64 0x33e88) (ms_mem msE) (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
    with (cfg_at tfibsegs dg_rchunk (ms_regs msE) (ms_mem msE) (with_vm_backing (m_vm_lazy md) mat md)).
  eapply YG0dH.amreal'_mbind.
  { eapply (YG0dHc.amreal'_apost tfibsegs YGcfRehidePost.RZ_cf); [exact (recycle_chunk_q (qk k) (qx S k z tr))|].
    apply (Frcs inst ly (qx S k z tr) (qk k) [] [] (bv_unsigned (getr regs 2) - 80) W (ms_regs msE) (ms_mem msE)
      (with_vm_backing (m_vm_lazy md) mat md));
      [| unfold ck_n; change (ck_req (qk k)) with (ck_req k); rewrite Hr; exact (proj1 HNN) | exact HDRq].
    unfold rcc_pre_sec.
    split; [exact HRr|].
    split; [rewrite E1r; apply YK0s.ret_ok_even; reflexivity|].
    split; [unfold raZ; rewrite E1r; rewrite unsigned_lit_small by lia; lia|].
    split; [rewrite SPE; unfold spZ in Hal; clear - Hal; replace (bv_unsigned (getr regs 2) - 80) with (bv_unsigned (getr regs 2) + (-5) * 16) by lia;
      rewrite Z_mod_plus_full; exact Hal|].
    split; [rewrite SPE; unfold spZ, DFSTACK_G, KSTACK_CF in *; clear - Hlo; lia|].
    split; [rewrite SPE; lia|].
    split; [unfold spZ in *; clear - Hhi; lia|].
    split; [unfold spZ in Hal; clear - Hal; pose proof (Z.div_mod (bv_unsigned (getr regs 2)) 16 ltac:(lia)) as D;
      rewrite Hal, Z.add_0_r in D; rewrite D;
      replace (16 * (bv_unsigned (getr regs 2) / 16) - 80) with ((2 * (bv_unsigned (getr regs 2) / 16) - 10) * 8) by lia;
      apply Z_mod_mult|].
    split; [intros a Ha; rewrite SPE in Ha; apply DMps; unfold DGbaseC.DFSTACK, KSTACK_CF in *; lia|].
    split; [intros a Ha; apply DMps; unfold DGbaseC.DFSTACK in *; lia|].
    split.
    { memv HS5 0%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite BV2; lia
      | cbn [sv_denot]; rewrite (HEn5 32%nat ltac:(cbv; lia)),
          (DGbigm.EaT ly (dregs regs (sptr_addr B ly p) inst bp so) tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3);
        unfold w64; rewrite Zbv_add_unsigned; f_equal; unfold t_cache; lia
      | try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); destruct LB as ((T1 & T2 & _) & _); clear - T1 T2; ceil;
        unfold ASAN_CEIL, kThreadObjSize, t_cache in *; lia ]. }
    split; [rewrite E3r, (HEn5 3%nat ltac:(cbv; lia)),
      (DGbigm.Er ly (dregs regs (sptr_addr B ly p) inst bp so) tr (sptr_addr B ly p) (req_size n) hb1
         (st_qthread S) j1 j2 j3 3 3%bv eq_refl), RG3; exact Hgp|].
    split; [rewrite E4r, (ts_tp B TS); reflexivity|].
    split; [rewrite E10r, BV2; unfold w64; f_equal; lia|].
    rewrite E11r, BV10. change (ck_base B ly (qk k)) with (ck_base B ly k). change (ck_rz (qk k)) with (ck_rz k).
    rewrite Hgeo. unfold w64, kChunkHeaderSize. f_equal; lia. }
  intros a s' W' c' (HQs & regsE' & memE' & mdE' & -> & POST & POSTr & ERRr & MNr & PUSr & PUMr & HDRq' & HAOXr).
  cbn [fst snd] in *.
  assert (Qsd : st_qthread (qx S k z tr) = st_qthread S).
  { unfold qx, depot_after, YFl0C.depot_after, dtick. destruct (z =? 0); reflexivity. }
  rewrite Qsd in HQs.
  pose proof POST as (ARXr' & LLE & WLE & CSe & SIO & FRv & PRSe).
  pose proof (Freq _ _ _ _ _ _ ARXr' HDRq') as ARXe.
  pose proof (Fqsize inst ly S W mem md p n s' W' memE' mdE' HARX HRP HBLK ARXe) as HQCELL.
  rewrite HQs in HQCELL.
  assert (QBY : qc_bytes (st_qthread s') <= kQuarantineCacheMax) by (rewrite HQs; exact (proj2 DVqb)).
  assert (NOWN : forall b, ly_stk_lo ly <= b < ly_stk_hi ly -> ~ AOX ly (qx S k z tr) b /\ ~ AOX ly s' b).
  { intros b Hb.
    assert (NX : ~ AOX ly (qx S k z tr) b).
    { intros O. destruct (HAOXq b O) as [O'|O'];
      [exact (Fstack inst ly S W mem md b HARX Hb O') | exact (NBLK b Hb O')]. }
    split; [exact NX | intros O; exact (NX (HAOXr b O))]. }
  unfold dmd. cbn [bind get ibind].
  replace (qc_bytes (st_qthread s') <=? kQuarantineCacheMax) with true by (symmetry; apply Z.leb_le; exact QBY).
  cbn [ret YG0dH.amreal' YG0dH.amrealG].
  assert (RA : raZ (ms_regs msE) = 221180) by (unfold raZ; rewrite E1r; apply unsigned_lit_small; lia).
  rewrite RA.
  eapply YA0nH.SRrG_mono.
  { apply (YA0nH.SRr_SRrG tfibsegs (YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf) (YA0nH.wle_wle' tfibsegs YGcfRehidePost.RZ_cf)).
    apply (TAILR B TS ARXr AOX W W' ly S (qx S k z tr) s' regs mem inst so bp p n tr hb1 j1 j2 j3 msE
      (with_vm_backing (m_vm_lazy md) mat md) E5 regsE' memE' mdE' FH HshE HEn5 HS5 DMps NOWN POST HQCELL). }
  intros Wo co _ (-> & regsR & memR & mat' & -> & RCS & FRT & PRESR & VIS).
  (* the leaf *)
  assert (NOXx : forall x : word, ~ AOX ly S (bv_unsigned x) ->
    ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) ->
    ~ AOX ly (qx S k z tr) (bv_unsigned x)).
  { intros x NO NE O. destruct (HAOXq _ O) as [O'|O']; [exact (NO O') | apply NE; split; [exact DVnn | exact O']]. }
  assert (DMx : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
    ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> ms_mem msE x = mem x).
  { intros x NO NS NE. assert (Ra : 0 <= bv_unsigned x < 2 ^ 64) by apply u64_range.
    apply DMfr.
    - intros [Hs|[Hw|Hw]].
      + apply NS. left. unfold spZ, DFSTACK_G, DFSTACK, DGbaseC.DFSTACK in *. lia.
      + destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra
          ltac:(left; unfold DGgmC.WINT in Hw; unfold DGgiC.WINT; tauto)) as [O|O];
        [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
      + unfold DGgmC.WINB in Hw. destruct Hw as [Hw|Hw].
        * destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; left; exact Hw)) as [O|O];
          [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
        * destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; right; left; exact Hw)) as [O|O];
          [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
    - intros Hd. destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; right; right; exact Hd)) as [O|O];
      [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
    - intros Hi. exact (NO (Fown_i inst ly S W mem md _ HARX Hi)). }
  assert (NSCR : forall x : word, ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
    ~ ascratch B KSTACK_CF (ms_regs msE) (bv_unsigned x)).
  { intros x NS [Hs|Hs]; [rewrite SPE in Hs; apply NS; left; unfold spZ, DFSTACK_G, KSTACK_CF in *; lia
    | apply NS; right; exact Hs]. }
  (* errno: from the entry to Recycle's call (dmem_b's frame), across Recycle (its contract), to Put's ret (Put's frame) *)
  assert (ERRC : ErrnoG.errno_kept B mem (ms_mem msE)).
  { intros i Hi. apply DMfr; rewrite (EB i Hi); intros Hw.
    - apply (ErrnoApart.errno_apart_dwin_m EAimg EAz3 B ly _ _ _ _ TS LY IMG HSP HZp ltac:(destruct HNN as [HN1 _]; unfold kQuarantineMax in HN1; lia) Hw). lia.
    - apply (EAdz B ly _ TS LY IMG Hw). lia.
    - apply (EAiz B _ TS Hw). lia. }
  assert (ERRT : ErrnoG.errno_kept B memE' memR).
  { intros i Hi. apply FRT. rewrite (EB i Hi). intros Hw.
    refine (ErrnoApart.errno_apart_stack EAimg B ly _ _ _ TS LY IMG _ Hw _); unfold DFSTACK_G, spZ in *; lia. }
  (* memnorm: dmem_b's frame, Recycle's keep, Put's 80-byte frame *)
  assert (MNC : MemnormT.memnorm_keep tfibsegs mem (ms_mem msE)).
  { refine (memnorm_dmem_b W ly _ mem tr _ _ hb1 _ j1 j2 j3 regs (bv_unsigned (getr regs 2)) (ms_mem msE) FH _ DMfr).
    rewrite RG2. reflexivity. }
  assert (MNT : MemnormT.memnorm_keep tfibsegs memE' memR).
  { apply (MemnormDmid.mn_keep_stack ly (bv_unsigned (getr regs 2) - 80) (bv_unsigned (getr regs 2)) memE' memR LY);
      [unfold DFSTACK_G, spZ in *; lia | unfold spZ in *; lia | exact FRT]. }
  exists regsR, memR, (with_vm_backing (m_vm_lazy mdE') mat' mdE').
  split; [unfold raZ; reflexivity|].
  split.
  2:{ split; [intros i Hi; rewrite (ERRT i Hi), (ERRr i Hi); exact (ERRC i Hi)|].
      exact (MemnormLocG.memnorm_keep_trans _ _ _ _ MNC (MemnormLocG.memnorm_keep_trans _ _ _ _ MNr MNT)). }
  split; [split|].
  { apply (Fframe inst ly s' W' memE' mdE' memR (with_vm_backing (m_vm_lazy mdE') mat' mdE') ARXe).
    - intros b Rb HO. apply aview_same. apply FRT. rewrite unsigned_lit_small by exact Rb.
      intros Hw.
      assert (Hstk : ly_stk_lo ly <= b < ly_stk_hi ly)
        by (clear - Hw Hlo Hhi; unfold spZ, DFSTACK_G in *; lia).
      destruct (NOWN b Hstk) as [_ N2]. exact (N2 HO).
    - exact VIS.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros b Hband Hh. apply FRT. unfold w64. rewrite unsigned_lit_small.
      + clear - Hband Hlo LB. unfold in_band_rw, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband.
        unfold spZ in Hlo. numc. lia.
      + clear - Hband. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia. }
  split; [apply layout_le_refl|].
  split; [eapply (YA0nH.wle_in_mono tfibsegs); [| exact WLE]; intros x0 Hx0;
    exact (YGcfRehidePost.dead_shadow_new_mono_l ly (qx S k z tr) S s' x0 (qx_secs_live S k z tr) Hx0)|].
  split; [exact (DGg2.aregs_of_cs regs (sptr_addr B ly p) inst bp so regsR RCS)|].
  split.
  { clear - SIO. unfold same_io in *. destruct md, mdE'. cbn in SIO |- *. intuition congruence. }
  split.
  { intros b Rb NO NO' NS NE ND.
    assert (Ex : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit_small; exact Rb).
    transitivity (aview tfibsegs (w_H W') memE' b).
    { apply aview_same. apply (FRT (Z_to_bv 64 b)). rewrite Ex. intros Hw. apply NS. left. unfold spZ, DFSTACK_G. lia. }
    transitivity (aview tfibsegs (w_H W) (ms_mem msE) b).
    { apply FRv; [exact Rb | | exact NO' | | intros [] |
        intros Hd; apply ND; exact (YGcfRehidePost.dead_shadow_new_mono_l ly (qx S k z tr) S s' b (qx_secs_live S k z tr) Hd)].
      - rewrite <- Ex. apply (NOXx (Z_to_bv 64 b)); rewrite Ex; assumption.
      - rewrite <- Ex. apply (NSCR (Z_to_bv 64 b)). rewrite Ex. exact NS. }
    apply aview_same. apply (DMx (Z_to_bv 64 b)); rewrite Ex; assumption. }
  intros b Hb. apply PRESR. unfold spZ, DFSTACK_G in Hb. unfold DFSTACK. exact Hb.
  intros x NO NO' NS NE.
  assert (NSS : ~ (bv_unsigned (getr regs 2) - 80 <= bv_unsigned x < bv_unsigned (getr regs 2)))
    by (intros Hw; apply NS; left; unfold spZ, DFSTACK_G; lia).
  rewrite (FRT x NSS). rewrite (POSTr x (NOXx x NO NE) NO' (NSCR x NS) ltac:(intros [])).
  exact (DMx x NO NS NE). }
(* lpost at the end of the granted path (dbg_post) *)
eapply YG0dH.amreal'_mono; [| exact (YG0dHc.amreal'_apath_gflag tfibsegs YGcfRehidePost.RZ_cf _ _ _ _ MAIN)].
intros r Wo co [(regsR & memR & mdR & -> & HPOST & HE & HM) HPATH].
exists ly, regsR, memR, mdR. split; [reflexivity|]. split; [exact HPOST|].
split; [exact HE|]. split; [exact HM|]. split; [|exact HPATH].
destruct r as [[] X']. cbn [snd] in *.
exact (Fpost inst ly S W mem md p n tr X' Wo memR mdR HARX HRP HBLK Htr (proj1 (proj1 HPOST)) HPATH).
Qed.
End a.
End d.
