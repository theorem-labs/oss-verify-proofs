(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGfy.v (a working branch 84ee52cd012, file sha256 b828b7ebc53a) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 4 image addresses moved by code-verified function pairs (4 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* The arm of the frame-generic Deallocate walk whose thread quarantine cache's last batch has room (no new batch,
   no drain), over the interface DGif0.DIface.

   Ported from cgif_file's released free walk (YFfy.afree_common_arm, YFfu.afree_common; the top is
   YFfs.afree_realizes_of), with the caller's frame made abstract: the run starts at Deallocate's entry (0x31be0)
   instead of the free interceptor's, the seed is DGgi.SS0 (its free_hyps record is the premise [fh_c_spec],
   which DGfu.FH_c proves from DeallocG.dealloc_pre and the interface's view), the segments are DGgc.segB (to StackDepotPut), the depot callee (di_depot) and DGge.segC (to
   Put's ret); the model tree comes from di_shape, the post (ARX and lpost of the final state) from di_post_c, the
   frame clause from the owned-set fields, the path clause from AGif0n.amreal_apath_gflag. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AE3d AFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DGbase DGgi DGfv DGgc DGge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require ErrnoG DGleafE.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
(* `Require ErrnoG` reaches YA09, whose last non-local `Ltac Zify...flag ::=` leaves the Zify euclidean-division
   conversion OFF (YA09.v:3340).  This file's existing lia calls were written with it ON, so restore it here,
   #[local] so that nothing escapes to importers (BUILD.md, 'Tactic hygiene'). *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 40. Set Printing Width 160.
Ltac numc := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize,
kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, DFSTACK, TFIB_IMG_END, DEP_STK, SHADOW_OFF,
TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma amreal_pure {A R} : forall (m : M A) (f : A -> M R) s a s' (W : world tfibsegs) c Q,
m s = IRet (a, s') -> amreal tfibsegs (f a s') W c Q -> amreal tfibsegs (bind m f s) W c Q.
Proof. intros m f s a s' W c Q E H. unfold bind. rewrite E. cbn [ibind]. exact H. Qed.
Lemma amreal_ask_depot {R} : forall trc s (k : Z -> itree astate R) (Wx : world tfibsegs) c Q,
SRr tfibsegs Wx c (fun W1 c1 => exists z, aok s (KDepot trc) z /\ amreal tfibsegs (k z) W1 c1 Q) ->
amreal tfibsegs (IAsk (KDepot trc) s k) Wx c Q.
Proof. intros trc s k Wx c Q H. exact H. Qed.

(* The callee-saved registers of the virtual regs0 are the entry registers'. *)
Lemma aregs_of_cs : forall regs pa inst bp so (regs' : bvmap 5 word),
(forall r : bv 5, In r CALLEE_SAVED -> getr regs' r = getr (dregs regs pa inst bp so) r) -> aregs_preserved regs regs'.
Proof.
intros regs pa inst bp so regs' RCS r Hr.
assert (HrZ : bv_unsigned (Z_to_bv 5 r) = r).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. unfold acallee_saved in Hr. apply Z.mod_small. lia. }
rewrite <- (dregs_other regs pa inst bp so (Z_to_bv 5 r)) by (rewrite HrZ; unfold acallee_saved in Hr; lia).
apply RCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - H18.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by lia; symmetry; exact Hb).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ rewrite (E5 2 ltac:(lia) 2%bv eq_refl) | rewrite (E5 3 ltac:(lia) 3%bv eq_refl) | rewrite (E5 4 ltac:(lia) 4%bv eq_refl)
| rewrite (E5 8 ltac:(lia) 8%bv eq_refl) | rewrite (E5 9 ltac:(lia) 9%bv eq_refl) | rewrite (E5 18 ltac:(lia) 18%bv eq_refl)
| rewrite (E5 19 ltac:(lia) 19%bv eq_refl) | rewrite (E5 20 ltac:(lia) 20%bv eq_refl) | rewrite (E5 21 ltac:(lia) 21%bv eq_refl)
| rewrite (E5 22 ltac:(lia) 22%bv eq_refl) | rewrite (E5 23 ltac:(lia) 23%bv eq_refl) | rewrite (E5 24 ltac:(lia) 24%bv eq_refl)
| rewrite (E5 25 ltac:(lia) 25%bv eq_refl) | rewrite (E5 26 ltac:(lia) 26%bv eq_refl) | rewrite (E5 27 ltac:(lia) 27%bv eq_refl) ];
cbn [In CALLEE_SAVED]; tauto.
Qed.

(* IAL_POST depends only on the internal allocator's zone. *)
Lemma IAL_transfer : forall (W : world tfibsegs) (m1 m2 : word -> option byte),
(forall a, DGgi.IZONE a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) -> DGgi.IAL_POST W m1 -> DGgi.IAL_POST W m2.
Proof.
intros W m1 m2 E I. unfold DGgi.IAL_POST in *. cbv zeta in *. destruct I as (I1 & I2 & I3 & I4 & I5).
assert (V : forall a (w : nat) v, (forall k, (k < w)%nat -> DGgi.IZONE (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict (w_H W) m1) a w v -> val_mem tfibsegs (mrestrict (w_H W) m2) a w v).
{ intros a w v Hz Hv. apply (AF0x.val_mem_frame (w_H W) m1 m2 a w v); [intros k Hk; apply E, Hz, Hk | exact Hv]. }
split; [apply V; [intros k Hk; unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *; lia | exact I1]|].
split; [apply V; [intros k Hk; unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *; lia | exact I2]|].
split; [apply V; [intros k Hk; unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IAL_W in *; lia | exact I3]|].
split; [apply V; [intros k Hk; unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IAL_W in *; lia | exact I4]|].
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) m1 m2 a). 2:{ apply E. unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *. lia. }
exact (I5 a Ha).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The memory facts over the seed's free_hyps.                                                                      *)
Section WK.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (tr : list Z).
Variables (p nn hb1 : Z) (q : qcache) (lastb : batch) (j1 j2 j3 : Z).
Variable regsU : bvmap 5 word.
Hypothesis FH : DGgi.free_hyps W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU.
Local Notation sp0 := (bv_unsigned (getr regs0 2)).
Local Notation WIN := (DGgi.WIN ly regs0 p lastb).
Local Notation WIN2 := (DGgi.WIN2 ly regs0 p lastb).
Local Notation LYB := (DGgi.LYB W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH).
Local Notation LYD := (DGgi.LYD W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH).
Local Notation derived_ranges := (DGgi.derived_ranges W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH).
Lemma sp_facts : ly_stk_lo ly + DFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof.
pose proof (DGgi.fh_Hsp _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (S1 & S2 & S3). pose proof LYB as LB.
destruct LB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L1 & L2). repeat split; assumption.
Qed.
Lemma DZONE_out : forall a, DGgi.DZONE ly a ->
~ WIN a /\ ~ DGgi.IZONE a /\ ~ (DGgi.SPv p <= a < DGgi.SPv p + DGgi.CNT8v nn) /\ 0 <= a < 2 ^ 64 /\ ~ (sp0 - DFSTACK <= a < sp0).
Proof.
intros a Hd. pose proof LYB as LB. pose proof derived_ranges as DR. pose proof sp_facts as SPF.
pose proof LYD as (_ & _ & (_ & _ & NBSTK) & (_ & SBSTK) & _). unfold zdisjoint in NBSTK, SBSTK. cbn [fst snd] in NBSTK, SBSTK.
unfold DGgi.DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]].
- split; [apply (DGgi.notWIN_img W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH); unfold TFIB_IMG_LO, TFIB_IMG_END; lia|].
  unfold DGgi.IZONE. clear - Hd DR SPF LB. numc. repeat split; lia.
- split; [apply (DGgi.notWIN_NB W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH); exact Hd|].
  unfold DGgi.IZONE. clear - Hd DR SPF LB NBSTK. numc. repeat split; lia.
- split; [apply (DGgi.notWIN_SB W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH); exact Hd|].
  unfold DGgi.IZONE. clear - Hd DR SPF LB SBSTK. numc. repeat split; lia.
Qed.
Lemma CZONE_out : forall a, CZONE ly a -> ~ WIN a.
Proof.
intros a Hc. pose proof LYB as LB.
unfold CZONE in Hc. destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]].
- apply (DGgi.notWIN_img W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH). unfold TFIB_IMG_LO, TFIB_IMG_END. lia.
- apply (DGgi.notWIN_shb W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH). unfold kLowShadowBeg, kHighMemBeg. lia.
- apply (DGgi.notWIN_Thead W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH). lia.
- apply (DGgi.notWIN_C W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH). lia.
- apply (DGgi.notWIN_img W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH). unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_TSD in *. lia.
- apply (DGgi.notWIN_D W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH). lia.
Qed.
Lemma IZONE_out : forall a, DGgi.IZONE a ->
~ WIN a /\ ~ DGgi.DZONE ly a /\ ~ (DGgi.SPv p <= a < DGgi.SPv p + DGgi.CNT8v nn) /\ 0 <= a < 2 ^ 64 /\ ~ (sp0 - 48 - DEP_STK <= a < sp0 - 48).
Proof.
intros a Hz. pose proof LYB as LB. pose proof derived_ranges as DR. pose proof sp_facts as SPF.
split; [apply (DGgi.notWIN_img W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH); unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *; lia|].
unfold DGgi.IZONE, DGgi.DZONE in *. clear - Hz DR SPF LB. numc. repeat split; lia.
Qed.
(* errno's 4 bytes (TFIB_ERRNO, in the image) are outside every zone the common arm's raw frame dmem_c excludes:
   WIN (notWIN_img), DZONE's image part (it ends below errno) and its NB / SB parts (off the image, zone3), IZONE
   (below errno), and the block's shadow (above SHADOW_OFF + 514). *)
Lemma errno_out : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 ->
~ WIN a /\ ~ DGgi.DZONE ly a /\ ~ DGgi.IZONE a /\ ~ (DGgi.SPv p <= a < DGgi.SPv p + DGgi.CNT8v nn).
Proof.
intros a Ha. pose proof LYB as (_ & _ & _ & _ & _ & _ & _ & _ & hNB & _ & hSB & _). pose proof derived_ranges as (_ & _ & DS & _).
split; [apply (DGgi.notWIN_img W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH); unfold TFIB_ERRNO, TFIB_IMG_LO, TFIB_IMG_END in *; lia|].
split.
{ unfold DGgi.DZONE. intros [Hd|[Hd|Hd]].
  - unfold TFIB_ERRNO in Ha. lia.
  - pose proof (zone3_off_img _ _ _ hNB Hd) as O. unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TFIB_ERRNO in O, Ha. lia.
  - pose proof (zone3_off_img _ _ _ hSB Hd) as O. unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TFIB_ERRNO in O, Ha. lia. }
split; [unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_ERRNO in *; lia|].
unfold SHADOW_OFF, TFIB_ERRNO in *. lia.
Qed.

(* The memory at Deallocate's return of this arm (DGge.at_RET), composed with the depot's and the seed's frames. *)
Lemma dmem_c_ok : forall (DP : (word -> option byte) -> Prop) (msm mem4 mem' : word -> option byte),
DGgi.MEQI W ly regs0 mem0 p lastb msm ->
(forall x : word, ~ (sp0 - 48 - DEP_STK <= bv_unsigned x < sp0 - 48) -> ~ DGgi.DZONE ly (bv_unsigned x) -> mem4 x = msm x) ->
(forall a, apresent (w_H W) msm a -> apresent (w_H W) mem4 a) ->
DP mem4 ->
DGge.EQS ly regs0 p nn lastb mem4 mem' ->
(forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W) mem' a) ->
(forall a, DGgi.WINT ly a \/ DGgi.WINB ly p lastb a -> apresent (w_H W) mem' a) ->
(let m := mrestrict (w_H W) mem' in
val_mem tfibsegs m (p - 16) 4 (3 + 256 * hb1) /\ val_mem tfibsegs m (p - 12) 4 nn /\
val_mem tfibsegs m (ly_T ly + t_qc) 8 (DGgi.QSv q) /\ val_mem tfibsegs m (ly_T ly + t_qc + 8) 8 (DGgi.QFv ly q) /\
val_mem tfibsegs m (ly_T ly + t_qc + 16) 8 (DGgi.Bv ly lastb) /\
val_mem tfibsegs m (ly_T ly + t_qc + 24) 8 (DGgi.QBv q + nn) /\ val_mem tfibsegs m (ly_T ly + t_unwinding) 1 0 /\
val_mem tfibsegs m (DGgi.Bv ly lastb + 8) 8 (DGgi.BBv lastb + nn) /\ val_mem tfibsegs m (DGgi.Bv ly lastb + 16) 8 (DGgi.BCv lastb + 1) /\
val_mem tfibsegs m (DGgi.SLOTv ly lastb) 8 (p - 16)) ->
dmem_c W ly sp0 mem0 p nn hb1 q lastb DP mem'.
Proof.
intros DP msm mem4 mem' [MQ IALm] Hfr4 Hpr4 HDP [EQ4 SH] PRS PRW VALS.
assert (W2D : forall a, WIN2 a -> dwin_c ly sp0 p lastb a).
{ intros a Hw. unfold DGgi.WIN2, dwin_c in *. destruct Hw as [Hw|[Hw|[Hw|Hw]]]; [left; exact Hw | lia | right; left; exact Hw | right; right; exact Hw]. }
assert (WD : forall a, WIN a -> dwin_c ly sp0 p lastb a).
{ intros a Hw. unfold DGgi.WIN, dwin_c in *. exact Hw. }
unfold dmem_c. split.
{ exists mem4. split; [exact HDP|]. split.
  - intros a Hz Hp. destruct (DZONE_out a Hz) as (NW & NI & NS & Ra & NST). apply Hpr4.
    apply (apresent_same (w_H W) mem0 msm a); [|exact Hp]. apply MQ; rewrite unsigned_lit_small by exact Ra; assumption.
  - intros x Hz. destruct (DZONE_out _ Hz) as (NW & NI & NS & Ra & NST).
    apply EQ4; [intros Hw; apply NW; apply DGgi.WIN2_WIN; exact Hw | exact NS]. }
split.
{ intros x Hw Hz Hi Hs. rewrite (EQ4 x); [| intros X; apply Hw; apply W2D; exact X | exact Hs].
  pose proof sp_facts as SPF.
  rewrite (Hfr4 x); [| intros X; apply Hw; left; unfold DEP_STK, DFSTACK, DGbaseC.DFSTACK in *; lia | exact Hz].
  apply MQ; [intros X; apply Hw; apply WD; exact X | exact Hi]. }
split.
{ apply (IAL_transfer W msm mem'); [|exact IALm]. intros a Hz. destruct (IZONE_out a Hz) as (NW & ND & NS & Ra & NST).
  rewrite (EQ4 (Z_to_bv 64 a)); rewrite ?unsigned_lit_small by exact Ra.
  2:{ intros X. apply NW. apply DGgi.WIN2_WIN. exact X. }
  2:{ exact NS. }
  apply Hfr4; rewrite unsigned_lit_small by exact Ra; assumption. }
split. { intros x Hs. apply SH. exact Hs. }
split; [exact PRS|]. split; [exact PRW|]. cbv zeta in VALS. exact VALS.
Qed.
End WK.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seed's record from the generic pre (DGfu.FH_c proves it).                                                   *)
Definition fh_c_spec (B : asyms) : Prop :=
forall U ARX rpre fpre inst so bp ly S W regs mem md p n tr lastb initr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
In (p, n) (blocks S) -> inst_ok inst -> dview B W ly inst mem S p n ->
rev (qc_list (st_qthread S)) = lastb :: initr -> Z.of_nat (length (b_items lastb)) < kBatchSlots ->
qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
exists hb1 j1 j2 j3,
0 <= hb1 < 256 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) /\
DGgi.free_hyps W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) lastb j1 j2 j3 regs.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The arm.                                                                                                         *)
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world tfibsegs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Hypothesis IF : DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq.
Local Notation Finst := (di_inst B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fview := (di_view B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fshape := (di_shape B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fdepot := (di_depot B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fdaok := (di_dpost_aok B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fpost_c := (di_post_c B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fown := (di_owned B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fown_b := (di_owned_b B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fown_i := (di_owned_i B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Hypothesis TS : TfibSyms B.
Hypothesis FHC : fh_c_spec B.

(* dealloc_common with errno kept, on the raw memory and on the view: the same walk and frame (dmem_c); errno from
   its raw frame by errno_out, the view from the raw bytes since the walk returns to the world it starts in. *)
Theorem dealloc_common_e : forall inst so bp ly S W regs mem md p n tr lastb initr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
In (p, n) (blocks S) -> rev (qc_list (st_qthread S)) = lastb :: initr -> Z.of_nat (length (b_items lastb)) < kBatchSlots ->
qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x31be0 regs mem md)
(DGleafE.dealloc_leaf_raw_ee B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof.
intros inst so bp ly S W regs mem md p n tr lastb initr PRE HBLK Hrev Hroom Hcache.
pose proof PRE as PRE0.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
pose proof (Finst _ _ _ _ _ _ HARX) as HIO.
pose proof (Fview inst ly S W mem md p n HARX HRP HFP HBLK) as DV.
pose proof DV as [DVn DVnn DVch DVhdr DVpres DVsh DVjunk DVzone DVqb DVbatch].
destruct DVch as (k & Hf & Hst & Hu & Hr).
destruct (FHC U ARX rpre fpre inst so bp ly S W regs mem md p n tr lastb initr PRE0 HBLK HIO DV Hrev Hroom Hcache)
as (hb1 & j1 & j2 & j3 & Hhb1 & Hhdr & FH).
pose proof (Fshape p n tr S k DVnn HRP HBLK Hf Hst) as ESH.
set (pa := sptr_addr B ly p) in *. set (nn := req_size n) in *. set (q := st_qthread S) in *.
set (regs0 := dregs regs pa inst bp so) in *.
unfold spZ, raZ in *.
assert (R1 : getr regs0 1%bv = getr regs 1%bv) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
assert (R2 : getr regs0 2%bv = getr regs 2%bv) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
pose proof (sp_facts W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH) as SPF. rewrite R2 in SPF. unfold DFSTACK in SPF.
assert (Usp : 0 <= bv_unsigned (getr regs 2) < 2 ^ 64) by apply u64_range.
assert (BP0 : bv_unsigned (getr regs0 12) = bp).
{ unfold regs0. rewrite dregs_12. unfold w64. apply unsigned_lit_small. unfold kHighMemEnd, kHighMemBeg in *. lia. }
(* the walk, with its machine post at Put's ret *)
assert (MAIN : amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x31be0 regs mem md)
(fun r W' c' => exists z, r = (tt, qfin_c S k z tr) /\ W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
(forall r : bv 5, In r CALLEE_SAVED -> getr regs' r = getr regs0 r) /\
dmem_c W ly (bv_unsigned (getr regs0 2)) mem pa nn hb1 q lastb (dpost inst ly S W tr z) mem')).
{ rewrite ESH. unfold depot_put. cbn [bind askz ibind]. apply amreal_ask_depot.
  unfold cfg_at. rewrite <- (wvb_self md) at 1.
  eapply SRr_bind; [exact (DGgc.segB W ly regs0 mem md tr pa nn hb1 q lastb j1 j2 j3 regs (m_vm_materialized md) FH)|].
  intros W1 c1 _ (-> & msD & mat1 & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
  rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2.
  rewrite (HEn3 2%nat ltac:(cbv; lia)), (DGgi.E2 ly regs0 tr pa nn hb1 q lastb j1 j2 j3) in Q2.
  assert (SPD : bv_unsigned (getr (ms_regs msD) 2) = bv_unsigned (getr regs0 2) - 48).
  { rewrite Q2. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. rewrite R2. clear - SPF Usp. numc. lia. }
  rewrite HshD. eapply SRr_bind.
  { apply (Fdepot inst ly S W mem md tr (ms_regs msD) (ms_mem msD) (with_vm_backing (m_vm_lazy md) mat1 md) bp HARX Htr).
    - intros x Hx. apply (proj1 MEQD).
      + destruct Hx as [Hd|[Hc _]]; [exact (proj1 (DZONE_out W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH _ Hd)) |
        exact (CZONE_out W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH _ Hc)].
      + destruct Hx as [Hd|[_ Hi]]; [exact (proj1 (proj2 (DZONE_out W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH _ Hd))) | exact Hi].
    - rreg HS (10%bv : bv 5) R. rewrite R, (HEn3 12%nat ltac:(cbv; lia)), (DGgi.E12 ly regs0 tr pa nn hb1 q lastb j1 j2 j3).
      unfold regs0. rewrite dregs_12. reflexivity.
    - rreg HS (11%bv : bv 5) R. rewrite R, (HEn3 36%nat ltac:(cbv; lia)), (DGgi.EaLEN ly regs0 tr pa nn hb1 q lastb j1 j2 j3). reflexivity.
    - rreg HS (3%bv : bv 5) R. rewrite R, (HEn3 3%nat ltac:(cbv; lia)), (DGgi.Er ly regs0 tr pa nn hb1 q lastb j1 j2 j3 3 3%bv eq_refl).
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
    - rewrite SPD, R2. clear - SPF. unfold DEP_STK, YFl0C.DEP_STK, DFSTACK in *. lia.
    - rewrite SPD, R2. lia.
    - intros a Ha. rewrite SPD in Ha. apply PRESD. unfold DEP_STK, YFl0C.DEP_STK, DFSTACK in *. lia. }
  intros W2 c2 _ (-> & z & regs4 & mem4 & mat4 & -> & HP4 & Hfr4 & Hpr4 & DP4). srr_norm_model.
  apply SRr_ret. exists z. split; [exact (Fdaok _ _ _ _ _ _ _ DP4)|].
  rewrite SPD in Hfr4.
  assert (Qsd : st_qthread (depot_after z tr (dtick S)) = q) by (unfold depot_after; destruct (z =? 0); reflexivity).
  assert (QT : st_qthread (qx S k z tr) = q).
  { unfold qx. cbn [st_qthread set_chunks]. exact Qsd. }
  assert (NNB : need_new_batch (st_qthread (qx S k z tr)) = false).
  { rewrite QT. unfold need_new_batch. rewrite Hrev. apply Z.eqb_neq. lia. }
  assert (QBY : (qc_bytes (qc_push (st_qthread (qx S k z tr)) (qk k) None) <=? kQuarantineCacheMax) = true).
  { apply Z.leb_le. rewrite QT. cbn [qc_push qc_bytes]. unfold qk, ck_n. cbn [ck_req]. rewrite Hr. exact Hcache. }
  assert (TAIL : amreal tfibsegs ((modify (fun s : astate => set_chunks (upd_chunk (st_chunks s) (qk k)) s) ;; enqueue (qk k) ;; dmd dbody)
    (depot_after z tr (dtick S))) W
    (mkCfg (mkst regs4 (getr (ms_regs msD) 1) mem4 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat4 md))
    (fun r W' c' => exists z0, r = (tt, qfin_c S k z0 tr) /\ W' = W /\ exists regs' mem' mat,
      c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
      (forall r : bv 5, In r CALLEE_SAVED -> getr regs' r = getr regs0 r) /\
      dmem_c W ly (bv_unsigned (getr regs0 2)) mem pa nn hb1 q lastb (dpost inst ly S W tr z0) mem')).
  { unfold enqueue, dmd. cbn [bind modify ibind get].
    change (set_chunks (upd_chunk (st_chunks (depot_after z tr (dtick S))) (qk k)) (depot_after z tr (dtick S))) with (qx S k z tr).
    rewrite NNB. cbn [bind ret ibind modify st_qthread set_qthread].
    rewrite QBY. cbn [ret amreal].
    rewrite Q1. eapply SRr_mono.
    { apply (DGge.segC W ly regs0 mem md tr pa nn hb1 q lastb j1 j2 j3 regs FH msD E3 regs4 mem4 mat4).
      split; [exact HshD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact HP4|]. split; [exact Hfr4|].
      split; [exact Hpr4|]. split; [exact MEQD | exact PRESD]. }
    intros W' c' _ HR. exists z. split; [reflexivity|].
    destruct HR as (-> & regs' & mem' & mat & -> & CS & EQS4 & PRS & PRW & VALS).
    split; [reflexivity|]. exists regs', mem', mat. split; [reflexivity|]. split; [exact CS|].
    exact (dmem_c_ok W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH (dpost inst ly S W tr z) (ms_mem msD) mem4 mem'
      MEQD Hfr4 Hpr4 DP4 EQS4 PRS PRW VALS). }
  pose proof (Fdaok _ _ _ _ _ _ _ DP4) as AOK.
  destruct AOK as [-> | [-> _]].
  - cbn [Z.eqb ret ibind]. exact TAIL.
  - cbn [Z.eqb bind get ret ibind].
    lazymatch goal with |- context [mcheck ?b1 14] => destruct b1 end; cbn [mcheck ret ibind]; [|exact I].
    lazymatch goal with |- context [mcheck ?b2 13] => destruct b2 end; cbn [mcheck ret put ibind]; [|exact I].
    exact TAIL. }
(* the leaf *)
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ MAIN)].
intros r W' c' [(z & -> & -> & regs' & mem' & mat & -> & RCS & DM) HPATH].
rewrite R2 in DM.
destruct (Fpost_c inst ly S W mem md p n tr k lastb initr hb1 z (bv_unsigned (getr regs 2)) mem' mat HARX HRP HFP HBLK Htr Hf Hst Hrev Hroom Hcache
  ltac:(unfold DFSTACK_G, DFSTACK, DGbaseC.DFSTACK in *; lia) Hhi Hbot Hal Hhb1 Hhdr DM HPATH) as [HARX' HLP].
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md) mat md).
split. { unfold cfg_at, raZ, w64. rewrite R1, Z_to_bv_bv_unsigned. reflexivity. }
destruct DM as (_ & DMfr & _ & _ & DMps & _).
assert (ERR : ErrnoG.errno_kept B mem mem').
{ intros i Hi.
  assert (EB : bv_unsigned (w64 (as_errno B + i)) = TFIB_ERRNO + i)
    by (rewrite (ts_errno _ TS); apply unsigned_lit_small; unfold TFIB_ERRNO; lia).
  destruct (errno_out W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH (TFIB_ERRNO + i) ltac:(lia)) as (NW & ND & NI & NS).
  apply DMfr; rewrite EB.
  - intros Hw. apply NW. unfold DGgi.WIN. unfold dwin_c in Hw. rewrite R2. exact Hw.
  - exact ND.
  - exact NI.
  - exact NS. }
split; [|split; [exact ERR | split; [|split; [exact HLP | exact HPATH]]]].
2:{ intros a Ha. apply aview_same. pose proof (ERR (a - as_errno B) ltac:(lia)) as E.
    replace (as_errno B + (a - as_errno B)) with a in E by lia. unfold w64 in E. exact E. }
split; [exact HARX'|]. split; [apply layout_le_refl|]. split; [apply wle_refl|].
split; [exact (aregs_of_cs regs pa inst bp so regs' RCS)|].
split. { unfold same_io. destruct md; cbn; repeat split; reflexivity. }
assert (FRAW : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly (qfin_c S k z tr) (bv_unsigned x) ->
  ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x).
{ intros x NO NO' NS NE. assert (Ra : 0 <= bv_unsigned x < 2 ^ 64) by apply u64_range. apply DMfr.
  - intros Hw. unfold dwin_c in Hw. destruct Hw as [Hs|[Hw|Hw]].
    + apply NS. unfold ascratch. left. unfold spZ, DFSTACK_G. unfold DFSTACK in Hs. exact Hs.
    + destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(left; exact Hw)) as [O|O];
      [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
    + unfold DGgi.WINB in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
      * destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; left; exact Hw)) as [O|O];
        [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
      * destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; right; left; exact Hw)) as [O|O];
        [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
      * exact (NO (Fown_b inst ly S W mem md lastb initr _ HARX Hrev Ra ltac:(left; exact Hw))).
      * exact (NO (Fown_b inst ly S W mem md lastb initr _ HARX Hrev Ra ltac:(right; exact Hw))).
  - intros Hd. destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; right; right; left; exact Hd)) as [O|O];
    [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
  - intros Hi. exact (NO (Fown_i inst ly S W mem md _ HARX Hi)).
  - intros Hs. destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; right; right; right; exact Hs)) as [O|O];
    [exact (NO O) | apply NE; split; [exact DVnn | exact O]]. }
split.
{ intros a Ra NO NO' NS NE. apply aview_same. apply FRAW; rewrite unsigned_lit_small by exact Ra; assumption. }
split; [exact FRAW|].
intros a Ha. unfold spZ, DFSTACK_G in Ha. apply DMps. unfold DFSTACK. exact Ha.
Qed.

(* NOTE: this proof is the frozen base's, verbatim, and it duplicates the walk that dealloc_common_e also runs.
   Reproving it from dealloc_common_e would pull TS (needed only for errno, through ts_errno) into its closed
   signature, which would break every caller - DGtop passes IF then FHC with no TS.  The statement must stay
   byte-identical AND so must the argument list, so the duplication is deliberate; factoring the shared walk
   into one exported lemma is the way to remove it. *)
Theorem dealloc_common : forall inst so bp ly S W regs mem md p n tr lastb initr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
In (p, n) (blocks S) -> rev (qc_list (st_qthread S)) = lastb :: initr -> Z.of_nat (length (b_items lastb)) < kBatchSlots ->
qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x31be0 regs mem md)
(DeallocG.dealloc_leaf_raw tfibsegs B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof.
intros inst so bp ly S W regs mem md p n tr lastb initr PRE HBLK Hrev Hroom Hcache.
pose proof PRE as PRE0.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
pose proof (Finst _ _ _ _ _ _ HARX) as HIO.
pose proof (Fview inst ly S W mem md p n HARX HRP HFP HBLK) as DV.
pose proof DV as [DVn DVnn DVch DVhdr DVpres DVsh DVjunk DVzone DVqb DVbatch].
destruct DVch as (k & Hf & Hst & Hu & Hr).
destruct (FHC U ARX rpre fpre inst so bp ly S W regs mem md p n tr lastb initr PRE0 HBLK HIO DV Hrev Hroom Hcache)
as (hb1 & j1 & j2 & j3 & Hhb1 & Hhdr & FH).
pose proof (Fshape p n tr S k DVnn HRP HBLK Hf Hst) as ESH.
set (pa := sptr_addr B ly p) in *. set (nn := req_size n) in *. set (q := st_qthread S) in *.
set (regs0 := dregs regs pa inst bp so) in *.
unfold spZ, raZ in *.
assert (R1 : getr regs0 1%bv = getr regs 1%bv) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
assert (R2 : getr regs0 2%bv = getr regs 2%bv) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
pose proof (sp_facts W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH) as SPF. rewrite R2 in SPF. unfold DFSTACK in SPF.
assert (Usp : 0 <= bv_unsigned (getr regs 2) < 2 ^ 64) by apply u64_range.
assert (BP0 : bv_unsigned (getr regs0 12) = bp).
{ unfold regs0. rewrite dregs_12. unfold w64. apply unsigned_lit_small. unfold kHighMemEnd, kHighMemBeg in *. lia. }
(* the walk, with its machine post at Put's ret *)
assert (MAIN : amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x31be0 regs mem md)
(fun r W' c' => exists z, r = (tt, qfin_c S k z tr) /\ W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
(forall r : bv 5, In r CALLEE_SAVED -> getr regs' r = getr regs0 r) /\
dmem_c W ly (bv_unsigned (getr regs0 2)) mem pa nn hb1 q lastb (dpost inst ly S W tr z) mem')).
{ rewrite ESH. unfold depot_put. cbn [bind askz ibind]. apply amreal_ask_depot.
  unfold cfg_at. rewrite <- (wvb_self md) at 1.
  eapply SRr_bind; [exact (DGgc.segB W ly regs0 mem md tr pa nn hb1 q lastb j1 j2 j3 regs (m_vm_materialized md) FH)|].
  intros W1 c1 _ (-> & msD & mat1 & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
  rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2.
  rewrite (HEn3 2%nat ltac:(cbv; lia)), (DGgi.E2 ly regs0 tr pa nn hb1 q lastb j1 j2 j3) in Q2.
  assert (SPD : bv_unsigned (getr (ms_regs msD) 2) = bv_unsigned (getr regs0 2) - 48).
  { rewrite Q2. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. rewrite R2. clear - SPF Usp. numc. lia. }
  rewrite HshD. eapply SRr_bind.
  { apply (Fdepot inst ly S W mem md tr (ms_regs msD) (ms_mem msD) (with_vm_backing (m_vm_lazy md) mat1 md) bp HARX Htr).
    - intros x Hx. apply (proj1 MEQD).
      + destruct Hx as [Hd|[Hc _]]; [exact (proj1 (DZONE_out W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH _ Hd)) |
        exact (CZONE_out W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH _ Hc)].
      + destruct Hx as [Hd|[_ Hi]]; [exact (proj1 (proj2 (DZONE_out W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH _ Hd))) | exact Hi].
    - rreg HS (10%bv : bv 5) R. rewrite R, (HEn3 12%nat ltac:(cbv; lia)), (DGgi.E12 ly regs0 tr pa nn hb1 q lastb j1 j2 j3).
      unfold regs0. rewrite dregs_12. reflexivity.
    - rreg HS (11%bv : bv 5) R. rewrite R, (HEn3 36%nat ltac:(cbv; lia)), (DGgi.EaLEN ly regs0 tr pa nn hb1 q lastb j1 j2 j3). reflexivity.
    - rreg HS (3%bv : bv 5) R. rewrite R, (HEn3 3%nat ltac:(cbv; lia)), (DGgi.Er ly regs0 tr pa nn hb1 q lastb j1 j2 j3 3 3%bv eq_refl).
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
    - rewrite SPD, R2. clear - SPF. unfold DEP_STK, YFl0C.DEP_STK, DFSTACK in *. lia.
    - rewrite SPD, R2. lia.
    - intros a Ha. rewrite SPD in Ha. apply PRESD. unfold DEP_STK, YFl0C.DEP_STK, DFSTACK in *. lia. }
  intros W2 c2 _ (-> & z & regs4 & mem4 & mat4 & -> & HP4 & Hfr4 & Hpr4 & DP4). srr_norm_model.
  apply SRr_ret. exists z. split; [exact (Fdaok _ _ _ _ _ _ _ DP4)|].
  rewrite SPD in Hfr4.
  assert (Qsd : st_qthread (depot_after z tr (dtick S)) = q) by (unfold depot_after; destruct (z =? 0); reflexivity).
  assert (QT : st_qthread (qx S k z tr) = q).
  { unfold qx. cbn [st_qthread set_chunks]. exact Qsd. }
  assert (NNB : need_new_batch (st_qthread (qx S k z tr)) = false).
  { rewrite QT. unfold need_new_batch. rewrite Hrev. apply Z.eqb_neq. lia. }
  assert (QBY : (qc_bytes (qc_push (st_qthread (qx S k z tr)) (qk k) None) <=? kQuarantineCacheMax) = true).
  { apply Z.leb_le. rewrite QT. cbn [qc_push qc_bytes]. unfold qk, ck_n. cbn [ck_req]. rewrite Hr. exact Hcache. }
  assert (TAIL : amreal tfibsegs ((modify (fun s : astate => set_chunks (upd_chunk (st_chunks s) (qk k)) s) ;; enqueue (qk k) ;; dmd dbody)
    (depot_after z tr (dtick S))) W
    (mkCfg (mkst regs4 (getr (ms_regs msD) 1) mem4 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat4 md))
    (fun r W' c' => exists z0, r = (tt, qfin_c S k z0 tr) /\ W' = W /\ exists regs' mem' mat,
      c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
      (forall r : bv 5, In r CALLEE_SAVED -> getr regs' r = getr regs0 r) /\
      dmem_c W ly (bv_unsigned (getr regs0 2)) mem pa nn hb1 q lastb (dpost inst ly S W tr z0) mem')).
  { unfold enqueue, dmd. cbn [bind modify ibind get].
    change (set_chunks (upd_chunk (st_chunks (depot_after z tr (dtick S))) (qk k)) (depot_after z tr (dtick S))) with (qx S k z tr).
    rewrite NNB. cbn [bind ret ibind modify st_qthread set_qthread].
    rewrite QBY. cbn [ret amreal].
    rewrite Q1. eapply SRr_mono.
    { apply (DGge.segC W ly regs0 mem md tr pa nn hb1 q lastb j1 j2 j3 regs FH msD E3 regs4 mem4 mat4).
      split; [exact HshD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact HP4|]. split; [exact Hfr4|].
      split; [exact Hpr4|]. split; [exact MEQD | exact PRESD]. }
    intros W' c' _ HR. exists z. split; [reflexivity|].
    destruct HR as (-> & regs' & mem' & mat & -> & CS & EQS4 & PRS & PRW & VALS).
    split; [reflexivity|]. exists regs', mem', mat. split; [reflexivity|]. split; [exact CS|].
    exact (dmem_c_ok W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH (dpost inst ly S W tr z) (ms_mem msD) mem4 mem'
      MEQD Hfr4 Hpr4 DP4 EQS4 PRS PRW VALS). }
  pose proof (Fdaok _ _ _ _ _ _ _ DP4) as AOK.
  destruct AOK as [-> | [-> _]].
  - cbn [Z.eqb ret ibind]. exact TAIL.
  - cbn [Z.eqb bind get ret ibind].
    lazymatch goal with |- context [mcheck ?b1 14] => destruct b1 end; cbn [mcheck ret ibind]; [|exact I].
    lazymatch goal with |- context [mcheck ?b2 13] => destruct b2 end; cbn [mcheck ret put ibind]; [|exact I].
    exact TAIL. }
(* the leaf *)
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ MAIN)].
intros r W' c' [(z & -> & -> & regs' & mem' & mat & -> & RCS & DM) HPATH].
rewrite R2 in DM.
destruct (Fpost_c inst ly S W mem md p n tr k lastb initr hb1 z (bv_unsigned (getr regs 2)) mem' mat HARX HRP HFP HBLK Htr Hf Hst Hrev Hroom Hcache
  ltac:(unfold DFSTACK_G, DFSTACK, DGbaseC.DFSTACK in *; lia) Hhi Hbot Hal Hhb1 Hhdr DM HPATH) as [HARX' HLP].
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md) mat md).
split. { unfold cfg_at, raZ, w64. rewrite R1, Z_to_bv_bv_unsigned. reflexivity. }
split; [|split; [exact HLP | exact HPATH]].
split; [exact HARX'|]. split; [apply layout_le_refl|]. split; [apply wle_refl|].
split; [exact (aregs_of_cs regs pa inst bp so regs' RCS)|].
split. { unfold same_io. destruct md; cbn; repeat split; reflexivity. }
destruct DM as (_ & DMfr & _ & _ & DMps & _).
assert (FRAW : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly (qfin_c S k z tr) (bv_unsigned x) ->
  ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x).
{ intros x NO NO' NS NE. assert (Ra : 0 <= bv_unsigned x < 2 ^ 64) by apply u64_range. apply DMfr.
  - intros Hw. unfold dwin_c in Hw. destruct Hw as [Hs|[Hw|Hw]].
    + apply NS. unfold ascratch. left. unfold spZ, DFSTACK_G. unfold DFSTACK in Hs. exact Hs.
    + destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(left; exact Hw)) as [O|O];
      [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
    + unfold DGgi.WINB in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
      * destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; left; exact Hw)) as [O|O];
        [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
      * destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; right; left; exact Hw)) as [O|O];
        [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
      * exact (NO (Fown_b inst ly S W mem md lastb initr _ HARX Hrev Ra ltac:(left; exact Hw))).
      * exact (NO (Fown_b inst ly S W mem md lastb initr _ HARX Hrev Ra ltac:(right; exact Hw))).
  - intros Hd. destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; right; right; left; exact Hd)) as [O|O];
    [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
  - intros Hi. exact (NO (Fown_i inst ly S W mem md _ HARX Hi)).
  - intros Hs. destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; right; right; right; exact Hs)) as [O|O];
    [exact (NO O) | apply NE; split; [exact DVnn | exact O]]. }
split.
{ intros a Ra NO NO' NS NE. apply aview_same. apply FRAW; rewrite unsigned_lit_small by exact Ra; assumption. }
split; [exact FRAW|].
intros a Ha. unfold spZ, DFSTACK_G in Ha. apply DMps. unfold DFSTACK. exact Ha.
Qed.
End b.
End d.
