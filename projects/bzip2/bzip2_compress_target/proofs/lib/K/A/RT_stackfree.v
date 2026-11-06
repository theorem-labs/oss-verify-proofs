(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow R_sizeclass.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_thread R_m2s RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit RT_facts RT_release R_fs_ok R_poison R_fsfree6 R_fsfree7 RT_stackmalloc.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow R_sizeclass.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_glue_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_sec_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_tlsgetaddr.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_intalloc.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_frame.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_trans.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts0.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_sep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_release.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_ok.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_poison.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fsfree6.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fsfree7.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_stackmalloc.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u8one_of_rw : forall (m : mem) A b, rw_cells bsegs m A [C1 b] -> u8arr bsegs m A [b].
Proof. intros m A b [[_ Hb] W]. split; [exact Hb | exact W]. Qed.

Lemma rw_of_u8one : forall (m : mem) A b, u8arr bsegs m A [b] -> rw_cells bsegs m A [C1 b].
Proof. intros m A b [Hb W]. split; [split; [exact (conj I I) | exact Hb] | exact W]. Qed.

Lemma wr_at_sub : forall (m : mem) a n a' n', wr_at bsegs m a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> wr_at bsegs m a' n'.
Proof.
  intros m a n a' n' (H0 & H1 & H) Ha Hn Hb. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma wr_at_cb : forall (m : mem) a (n : nat), wr_at bsegs m a (Z.of_nat n) -> exists junk, rw_cells bsegs m a [CB n junk].
Proof.
  intros m a n W. pose proof (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lkit.TwinB__.wr_at_stk m a _ W) as S. destruct W as (W0 & _).
  destruct (stk_carve bsegs m a (a + Z.of_nat n) n S ltac:(lia)) as [_ [junk R]]. exists junk.
  replace (a + Z.of_nat n - Z.of_nat n) with a in R by lia. exact R.
Qed.

Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

Lemma shad_add8 : forall x n, x mod 8 = 0 -> n mod 8 = 0 -> shad (x + n) = shad x + n / 8.
Proof.
  intros x n Hx Hn. unfold shad. apply Z.mod_divide in Hx; [|lia]. apply Z.mod_divide in Hn; [|lia].
  destruct Hx as [a ->]. destruct Hn as [b ->]. rewrite <- Z.mul_add_distr_r, !Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SFRel.
Variables (Σ : rtsA) (m m' : mem) (f : Z) (k : nat) (fr : list (Z * nat)) (p usp lo : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis HF : frames Σ = (f, k) :: fr.
Hypothesis Hp : 0 <= p < NF (Z.of_nat k).
Hypothesis Hf : f = frame_addr (l_FSB (lay Σ)) (Z.of_nat k) p.
Hypothesis Hlo : rtA_sp0 Σ - STACK_WIN <= lo.
Hypothesis Husp : lo + 64 <= usp.
Hypothesis Husp2 : usp <= USTACK_TOP.
Hypothesis MU : munch (sf_W (Z.of_nat k) (l_FSB (lay Σ)) p usp) m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis FLZ : u8arr bsegs m' (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + p) [Z_to_bv 8 0].
#[local] Notation FSB := (l_FSB (lay Σ)).
#[local] Notation K := (Z.of_nat k).
#[local] Notation fl := (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + p).

Lemma sf_in : In (f, k) (frames Σ).
Proof. rewrite HF. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sf_shad_end : shad f + fsz K / 8 = shad (f + fs_size k) /\ f mod 8 = 0 /\ 0 < fs_size k /\ fs_size k = fsz K.
Proof.
  pose proof (rta_frames_align Σ m HA f k sf_in) as (Al & _). pose proof (sep_frame Σ m HA f k sf_in) as (_ & _ & Hpos).
  destruct (rta_frame_in Σ m f k HA sf_in) as (Hk & _).
  assert (M8 : f mod 8 = 0).
  { apply Z.mod_divide in Al; [|lia]. destruct Al as [q ->]. replace (q * 64) with (q * 8 * 8) by ring. apply Z.mod_mul. lia. }
  assert (S8 : fs_size k mod 8 = 0) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; reflexivity).
  rewrite (shad_add8 f (fs_size k) M8 S8), <- (fs_size_fsz k). repeat split; try assumption.
Qed.

(* [comment removed for export] *)
Definition sf_m1 : mem := fun a => if Z.eqb (bv_unsigned a) fl then m a else m' a.

Lemma sf_m1_client : forall a : word, ~ aclient (live Σ) (frames Σ) (usp - 64) (bv_unsigned a) -> sf_m1 a = m a.
Proof.
  intros a Hn. unfold sf_m1. destruct (Z.eqb_spec (bv_unsigned a) fl) as [E|NE]; [reflexivity|].
  pose proof sf_shad_end as (SE & _). apply MU. unfold sf_W. cbn [outside]. rewrite <- Hf.
  split; [lia|]. split; [|split; [|exact I]].
  - intros Hx. apply Hn. right. right. right. right. exists f, k. split; [exact sf_in|]. rewrite <- SE. lia.
  - intros Hx. apply Hn. left. lia.
Qed.

Lemma sf_wm1 : wmono bsegs m sf_m1.
Proof. intros x Hx. unfold wview, sf_m1. destruct (Z.eqb (bv_unsigned x) fl); [exact Hx | exact (WM x Hx)]. Qed.

Lemma sf_art1 : ART_A Σ sf_m1.
Proof. exact (ART_client_frame Σ m sf_m1 (usp - 64) HA ltac:(lia) sf_m1_client sf_wm1). Qed.

(* [comment removed for export] *)
Theorem sf_release : ART_A (fs_release Σ k p fr) m' /\ frames (fs_release Σ k p fr) = fr /\ live (fs_release Σ k p fr) = live Σ
  /\ rtA_sp0 (fs_release Σ k p fr) = rtA_sp0 Σ /\ credit (fs_release Σ k p fr) = credit Σ
  /\ ~ aclient (live Σ) (frames Σ) USTACK_TOP fl /\ fl + 1 <= rtA_sp0 Σ - STACK_WIN.
Proof.
  destruct (rta_frame_release_at Σ sf_m1 f k fr sf_art1 HF p Hp Hf) as (_ & NC & _ & R1 & _ & REL).
  destruct (REL m') as (A' & E1 & E2 & E3 & E4 & _).
  - intros x Hx. cbn [outside] in Hx. unfold sf_m1. destruct (Z.eqb_spec (bv_unsigned x) fl) as [E|NE]; [lia | reflexivity].
  - intros x Hx. unfold wview, sf_m1 in Hx. destruct (Z.eqb (bv_unsigned x) fl); [exact (WM x Hx) | exact Hx].
  - exact (rw_of_u8one m' _ _ FLZ).
  - exact (conj A' (conj E1 (conj E2 (conj E3 (conj E4 (conj NC R1)))))).
Qed.

(* [comment removed for export] *)
Theorem sf_pres : rt_pres (live Σ) fr usp m m'.
Proof.
  destruct sf_release as (_ & _ & _ & _ & _ & NC & R1). pose proof sf_shad_end as (SE & M8 & Hpos & _).
  pose proof (rta_sp0_range Σ m HA) as SPR. pose proof (rta_sp0_win Σ m HA) as SPW.
  pose proof (rta_frames_range Σ m HA f k sf_in) as (F0 & F1 & _).
  assert (SHhi : forall z, 0 <= z -> z <= rtA_sp0 Σ - STACK_WIN -> shad z < lo).
  { intros z Hz0 Hz. unfold shad, SHB. assert (z / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold STACK_WIN, USTACK_TOP in *; lia).
    unfold STACK_WIN in *. lia. }
  assert (SUB : forall x, aclient (live Σ) fr usp x -> usp <= x \/ aclient (live Σ) (frames Σ) USTACK_TOP x).
  { intros x [H|[H|[H|[H|H]]]]; [left; lia | right; right; left; exact H | right; right; right; left; exact H | |].
    - right. right. right. right. left. destruct H as (f' & k' & Hin & Hr). exists f', k'. split; [rewrite HF; right; exact Hin | exact Hr].
    - right. right. right. right. right. destruct H as (f' & k' & Hin & Hr). exists f', k'. split; [rewrite HF; right; exact Hin | exact Hr]. }
  intros a Ha. apply MU. unfold sf_W. cbn [outside]. rewrite <- Hf. set (x := bv_unsigned a) in *.
  split; [|split; [|split; [|exact I]]].
  - (* [comment removed for export] *)
    intros Hx. assert (E : x = fl) by lia. destruct (SUB x Ha) as [H|H]; [lia | rewrite E in H; exact (NC H)].
  - (* [comment removed for export] *)
    intros Hx. rewrite SE in Hx.
    pose proof (SHhi (f + fs_size k) ltac:(lia) F1) as X.
    destruct Ha as [H|[H|[H|[H|H]]]].
    + lia.
    + assert (D : disjoint_from CS_W (shad f) (shad (f + fs_size k) - shad f)).
      { apply dsj_CS_out. right. unfold shad, SHB, SEGTOP_A. pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). lia. }
      apply (client_static_cover x H). apply (disjoint_outside _ _ _ _ D). lia.
    + destruct H as (q & n & Hin & Hr). destruct (proj1 (rta_fshadow_apart Σ m HA f k sf_in) q n Hin); lia.
    + destruct H as (f' & k' & Hin & Hr). destruct (proj2 (rta_fshadow_apart Σ m HA f k sf_in) f' k' ltac:(rewrite HF; right; exact Hin)); lia.
    + destruct H as (f' & k' & Hin & Hr).
      destruct (rta_frames_disj Σ m HA f k f' k' [] fr HF Hin) as [D|D].
      * pose proof (shad_mono _ _ D). lia.
      * pose proof (shad_mono _ _ D). lia.
  - (* [comment removed for export] *)
    intros Hx.
    destruct Ha as [H|[H|[H|[H|H]]]].
    + lia.
    + assert (D : disjoint_from CS_W (usp - 64) 64) by (apply dsj_CS_out; right; unfold SEGTOP_A, STACK_WIN in *; lia).
      apply (client_static_cover x H). apply (disjoint_outside _ _ _ _ D). lia.
    + destruct H as (q & n & Hin & Hr). destruct (rta_live_range Σ m q n HA Hin) as (_ & X & _). lia.
    + destruct H as (f' & k' & Hin & Hr). destruct (rta_frames_range Σ m HA f' k' ltac:(rewrite HF; right; exact Hin)) as (_ & X & _). lia.
    + destruct H as (f' & k' & Hin & Hr). destruct (rta_frames_range Σ m HA f' k' ltac:(rewrite HF; right; exact Hin)) as (X0 & X & _).
      pose proof (SHhi (f' + fs_size k') ltac:(unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k') ltac:(lia) ltac:(lia)); lia) X). lia.
Qed.

End SFRel.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sf_pre : forall Σ (m : mem) f k fr, ART_A Σ m -> frames Σ = (f, k) :: fr ->
  exists p, 0 <= p < NF (Z.of_nat k) /\ f = frame_addr (l_FSB (lay Σ)) (Z.of_nat k) p
    /\ u8arr bsegs m (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + p) [Z_to_bv 8 1]
    /\ wr_at bsegs m f (fs_size k) /\ wr_at bsegs m (shad f) (fs_size k / 8)
    /\ rw_cells bsegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + p))].
Proof.
  intros Σ m f k fr HA HF.
  assert (Hin : In (f, k) (frames Σ)) by (rewrite HF; left; reflexivity).
  destruct (busy_slot Σ m HA f k Hin) as (Hk & p & Hp & Hf & _).
  assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 3 \/ Z.of_nat k = 6 \/ Z.of_nat k = 7) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
  exists p. split; [exact Hp|]. split; [exact Hf|].
  destruct (rta_frame_release_at Σ m f k fr HA HF p Hp Hf) as (B & _).
  split; [exact (u8one_of_rw m _ _ B)|].
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & FB). unfold fs_busy in FB. rewrite HF in FB. apply Forall_cons_iff in FB as [FB0 _].
  destruct FB0 as (p' & Hf' & W1 & W2 & Cw). cbn [fst snd] in *. rewrite Hf in Hf'. apply (frame_addr_inj _ _ _ _ Hc) in Hf'. subst p'.
  split; [exact W1|]. split; [exact W2 | exact Cw].
Qed.

(* [comment removed for export] *)
Lemma sf_finish : forall (Σ : rtsA) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m : mem) (f : Z) (k : nat) (fr : list (Z * nat))
    (p lo : Z) (Pm : machine_state -> Prop) c1,
  ART_A Σ m -> frames Σ = (f, k) :: fr -> 0 <= p < NF (Z.of_nat k) -> f = frame_addr (l_FSB (lay Σ)) (Z.of_nat k) p ->
  rtA_sp0 Σ - STACK_WIN <= lo -> lo + RT_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  AST SEGTOP_A (rtA_allow Σ) Pm (fun mo => ARTM RTA Σ mo /\ PMc mo) c1 ->
  (forall ms, Pm ms -> exists m',
     ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
     /\ munch (sf_W (Z.of_nat k) (l_FSB (lay Σ)) p (bv_unsigned sp)) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
     /\ stk bsegs m' lo (bv_unsigned sp) /\ u8arr bsegs m' (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + p) [Z_to_bv 8 0]) ->
  exists (Σ' : rts RTA) (v' : word),
       ASTA RTA Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v' m' ms
         /\ rt_after RTA Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RTA Σ) fr (bv_unsigned sp) m m') c1
       /\ rt_frames RTA Σ' = fr /\ rt_live RTA Σ' = rt_live RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ /\ rt_credit RTA Σ' = rt_credit RTA Σ.
Proof.
  intros Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m f k fr p lo Pm c1 HA HF Hp Hf LOW LOR SPT HAST HPm.
  exists (fs_release Σ k p fr), v.
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity | reflexivity]]]].
  unfold ASTA. change (rt_allow RTA (fs_release Σ k p fr)) with (rtA_allow Σ).
  eapply AST_conseq; [exact HAST| |intros mo Hmo; exact Hmo].
  intros ms HP. destruct (HPm ms HP) as (m' & RS & MU & WM & MI & ST' & FLZ).
  assert (Husp : lo + 64 <= bv_unsigned sp) by (unfold RT_STACK in LOR; lia).
  assert (Husp2 : bv_unsigned sp <= USTACK_TOP) by lia.
  destruct (sf_release Σ m m' f k fr p (bv_unsigned sp) lo HA HF Hp Hf LOW Husp Husp2 MU WM FLZ) as (ART' & _).
  pose proof (sf_pres Σ m m' f k fr p (bv_unsigned sp) lo HA HF Hp Hf LOW Husp Husp2 MU WM FLZ) as PRES.
  exists m'. split; [exact RS|]. split; [split; [exact ART' | split; [exact MI | split; [exact WM | exact ST']]]|]. exact PRES.
Qed.

Theorem rta_stack_free_6 : stack_free_contract RTA 6.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f size fr lo
    FDO MST Hk HF -> -> Hsz Hsz8 ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 6%nat lo ART0 ltac:(lia) LOW) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2S & FSOK & HLO & FSL & _).
  destruct (sf_pre Σ m f 6%nat fr ART0 HF) as (p & Hp & Hf & FLG & W1 & W2 & Cw).
  change (NF (Z.of_nat 6)) with 256 in Hp. change (fs_size 6) with 4096 in W1, W2, Cw. change (4096 / 8) with 512 in W2.
  destruct (wr_at_cb m f 4088%nat (wr_at_sub m f 4096 f 4088 W1 ltac:(lia) ltac:(lia) ltac:(lia))) as (junkF & FRc).
  destruct (wr_at_cb m (shad f) 512%nat W2) as (junkS & SHc).
  assert (LASTc : rw_cells bsegs m f [CB 4088 junkF; C8 (Z_to_bv 64 (fl_base (l_FSB (lay Σ)) (Z.of_nat 6) + p))]).
  { apply (proj2 (rw_cells_app2 m f [CB 4088 junkF] [C8 (Z_to_bv 64 (fl_base (l_FSB (lay Σ)) (Z.of_nat 6) + p))])). split; [exact FRc|].
    cbn [cells_size csize Nat.add]. replace (f + Z.of_nat 4088) with (f + 4096 - 8) by lia. exact Cw. }
  assert (W0 : evt bsegs (sf6_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) p lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_free 6) m)).
  { unfold entry_st. rewrite Hf in *.
    exact (stack_free_6_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) p lo _ junkF junkS Hp FLG LASTc SHc M2S FSOK HLO FSL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W0 with evt bsegs _ ?X =>
    assert (W0' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W0) end.
  clear W0.
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W0') Hc).
  intros c1 Hc1. apply Hkont. unfold sf6_post in Hc1.
  apply AST_exI in Hc1 as (v & Hc2).
  apply (sf_finish Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m f 6%nat fr p lo _ c1 ART0 HF
           ltac:(change (NF (Z.of_nat 6)) with 256; exact Hp) Hf LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & FLZ).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST' | exact FLZ].
Qed.

Theorem rta_stack_free_7 : stack_free_contract RTA 7.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f size fr lo
    FDO MST Hk HF -> -> Hsz Hsz8 ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *.
  assert (HLO7 : 0x7fff00000000 <= lo).
  { destruct CALL as (_ & LOW & _). pose proof (rta_sp0_win Σ m ART0) as SPW. cbn [rt_sp0 RTA] in LOW. unfold STACK_WIN in LOW. lia. }
  unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 7%nat lo ART0 ltac:(lia) LOW) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2S & FSOK & HLO & FSL & _).
  pose proof (ART_consts Σ m ART0) as (_ & _ & _ & _ & PS & _).
  destruct (sf_pre Σ m f 7%nat fr ART0 HF) as (p & Hp & Hf & FLG & W1 & W2 & Cw).
  change (NF (Z.of_nat 7)) with 128 in Hp. change (fs_size 7) with 8192 in W1, W2, Cw, Hsz. change (8192 / 8) with 1024 in W2.
  destruct (wr_at_cb m (shad f) 1024%nat W2) as (junkS & SHc).
  replace (f + 8192 - 8) with (f + 8184) in Cw by lia.
  assert (W0 : evt bsegs (sf7_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) p lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_free 7) m)).
  { unfold entry_st. rewrite Hf in *.
    exact (stack_free_7_spec ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) p lo size _ junkS Hp Hsz Hsz8 FLG Cw SHc M2S PS FSOK HLO7 FSL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W0 with evt bsegs _ ?X =>
    assert (W0' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W0) end.
  clear W0.
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W0') Hc).
  intros c1 Hc1. apply Hkont. unfold sf7_post in Hc1.
  apply AST_exI in Hc1 as (v & Hc2).
  apply (sf_finish Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m f 7%nat fr p lo _ c1 ART0 HF
           ltac:(change (NF (Z.of_nat 7)) with 128; exact Hp) Hf LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & FLZ).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST' | exact FLZ].
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface D_defs R_sizeclass R_cache_defs R_prim_defs R_glue_defs
  R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_thread R_m2s RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit
  RT_facts RT_release R_fs_ok R_poison R_fsfree6 R_fsfree7 RT_stackmalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u8one_of_rw : forall (m : mem) A b, rw_cells asegs m A [C1 b] -> u8arr asegs m A [b].
Proof. intros m A b [[_ Hb] W]. split; [exact Hb | exact W]. Qed.

Lemma rw_of_u8one : forall (m : mem) A b, u8arr asegs m A [b] -> rw_cells asegs m A [C1 b].
Proof. intros m A b [Hb W]. split; [split; [exact (conj I I) | exact Hb] | exact W]. Qed.

Lemma wr_at_sub : forall (m : mem) a n a' n', wr_at asegs m a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (H0 & H1 & H) Ha Hn Hb. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma wr_at_cb : forall (m : mem) a (n : nat), wr_at asegs m a (Z.of_nat n) -> exists junk, rw_cells asegs m a [CB n junk].
Proof.
  intros m a n W. pose proof (I_lkit.wr_at_stk m a _ W) as S. destruct W as (W0 & _).
  destruct (stk_carve asegs m a (a + Z.of_nat n) n S ltac:(lia)) as [_ [junk R]]. exists junk.
  replace (a + Z.of_nat n - Z.of_nat n) with a in R by lia. exact R.
Qed.

Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

Lemma shad_add8 : forall x n, x mod 8 = 0 -> n mod 8 = 0 -> shad (x + n) = shad x + n / 8.
Proof.
  intros x n Hx Hn. unfold shad. apply Z.mod_divide in Hx; [|lia]. apply Z.mod_divide in Hn; [|lia].
  destruct Hx as [a ->]. destruct Hn as [b ->]. rewrite <- Z.mul_add_distr_r, !Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SFRel.
Variables (Σ : rtsA) (m m' : mem) (f : Z) (k : nat) (fr : list (Z * nat)) (p usp lo : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis HF : frames Σ = (f, k) :: fr.
Hypothesis Hp : 0 <= p < NF (Z.of_nat k).
Hypothesis Hf : f = frame_addr (l_FSB (lay Σ)) (Z.of_nat k) p.
Hypothesis Hlo : rtA_sp0 Σ - STACK_WIN <= lo.
Hypothesis Husp : lo + 64 <= usp.
Hypothesis Husp2 : usp <= USTACK_TOP.
Hypothesis MU : munch (sf_W (Z.of_nat k) (l_FSB (lay Σ)) p usp) m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis FLZ : u8arr asegs m' (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + p) [Z_to_bv 8 0].
#[local] Notation FSB := (l_FSB (lay Σ)).
#[local] Notation K := (Z.of_nat k).
#[local] Notation fl := (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + p).

Lemma sf_in : In (f, k) (frames Σ).
Proof. rewrite HF. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sf_shad_end : shad f + fsz K / 8 = shad (f + fs_size k) /\ f mod 8 = 0 /\ 0 < fs_size k /\ fs_size k = fsz K.
Proof.
  pose proof (rta_frames_align Σ m HA f k sf_in) as (Al & _). pose proof (sep_frame Σ m HA f k sf_in) as (_ & _ & Hpos).
  destruct (rta_frame_in Σ m f k HA sf_in) as (Hk & _).
  assert (M8 : f mod 8 = 0).
  { apply Z.mod_divide in Al; [|lia]. destruct Al as [q ->]. replace (q * 64) with (q * 8 * 8) by ring. apply Z.mod_mul. lia. }
  assert (S8 : fs_size k mod 8 = 0) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; reflexivity).
  rewrite (shad_add8 f (fs_size k) M8 S8), <- (fs_size_fsz k). repeat split; try assumption.
Qed.

(* [comment removed for export] *)
Definition sf_m1 : mem := fun a => if Z.eqb (bv_unsigned a) fl then m a else m' a.

Lemma sf_m1_client : forall a : word, ~ aclient (live Σ) (frames Σ) (usp - 64) (bv_unsigned a) -> sf_m1 a = m a.
Proof.
  intros a Hn. unfold sf_m1. destruct (Z.eqb_spec (bv_unsigned a) fl) as [E|NE]; [reflexivity|].
  pose proof sf_shad_end as (SE & _). apply MU. unfold sf_W. cbn [outside]. rewrite <- Hf.
  split; [lia|]. split; [|split; [|exact I]].
  - intros Hx. apply Hn. right. right. right. right. exists f, k. split; [exact sf_in|]. rewrite <- SE. lia.
  - intros Hx. apply Hn. left. lia.
Qed.

Lemma sf_wm1 : wmono asegs m sf_m1.
Proof. intros x Hx. unfold wview, sf_m1. destruct (Z.eqb (bv_unsigned x) fl); [exact Hx | exact (WM x Hx)]. Qed.

Lemma sf_art1 : ART_A Σ sf_m1.
Proof. exact (ART_client_frame Σ m sf_m1 (usp - 64) HA ltac:(lia) sf_m1_client sf_wm1). Qed.

(* [comment removed for export] *)
Theorem sf_release : ART_A (fs_release Σ k p fr) m' /\ frames (fs_release Σ k p fr) = fr /\ live (fs_release Σ k p fr) = live Σ
  /\ rtA_sp0 (fs_release Σ k p fr) = rtA_sp0 Σ /\ credit (fs_release Σ k p fr) = credit Σ
  /\ ~ aclient (live Σ) (frames Σ) USTACK_TOP fl /\ fl + 1 <= rtA_sp0 Σ - STACK_WIN.
Proof.
  destruct (rta_frame_release_at Σ sf_m1 f k fr sf_art1 HF p Hp Hf) as (_ & NC & _ & R1 & _ & REL).
  destruct (REL m') as (A' & E1 & E2 & E3 & E4 & _).
  - intros x Hx. cbn [outside] in Hx. unfold sf_m1. destruct (Z.eqb_spec (bv_unsigned x) fl) as [E|NE]; [lia | reflexivity].
  - intros x Hx. unfold wview, sf_m1 in Hx. destruct (Z.eqb (bv_unsigned x) fl); [exact (WM x Hx) | exact Hx].
  - exact (rw_of_u8one m' _ _ FLZ).
  - exact (conj A' (conj E1 (conj E2 (conj E3 (conj E4 (conj NC R1)))))).
Qed.

(* [comment removed for export] *)
Theorem sf_pres : rt_pres (live Σ) fr usp m m'.
Proof.
  destruct sf_release as (_ & _ & _ & _ & _ & NC & R1). pose proof sf_shad_end as (SE & M8 & Hpos & _).
  pose proof (rta_sp0_range Σ m HA) as SPR. pose proof (rta_sp0_win Σ m HA) as SPW.
  pose proof (rta_frames_range Σ m HA f k sf_in) as (F0 & F1 & _).
  assert (SHhi : forall z, 0 <= z -> z <= rtA_sp0 Σ - STACK_WIN -> shad z < lo).
  { intros z Hz0 Hz. unfold shad, SHB. assert (z / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold STACK_WIN, USTACK_TOP in *; lia).
    unfold STACK_WIN in *. lia. }
  assert (SUB : forall x, aclient (live Σ) fr usp x -> usp <= x \/ aclient (live Σ) (frames Σ) USTACK_TOP x).
  { intros x [H|[H|[H|[H|H]]]]; [left; lia | right; right; left; exact H | right; right; right; left; exact H | |].
    - right. right. right. right. left. destruct H as (f' & k' & Hin & Hr). exists f', k'. split; [rewrite HF; right; exact Hin | exact Hr].
    - right. right. right. right. right. destruct H as (f' & k' & Hin & Hr). exists f', k'. split; [rewrite HF; right; exact Hin | exact Hr]. }
  intros a Ha. apply MU. unfold sf_W. cbn [outside]. rewrite <- Hf. set (x := bv_unsigned a) in *.
  split; [|split; [|split; [|exact I]]].
  - (* [comment removed for export] *)
    intros Hx. assert (E : x = fl) by lia. destruct (SUB x Ha) as [H|H]; [lia | rewrite E in H; exact (NC H)].
  - (* [comment removed for export] *)
    intros Hx. rewrite SE in Hx.
    pose proof (SHhi (f + fs_size k) ltac:(lia) F1) as X.
    destruct Ha as [H|[H|[H|[H|H]]]].
    + lia.
    + assert (D : disjoint_from CS_W (shad f) (shad (f + fs_size k) - shad f)).
      { apply dsj_CS_out. right. unfold shad, SHB, SEGTOP_A. pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). lia. }
      apply (client_static_cover x H). apply (disjoint_outside _ _ _ _ D). lia.
    + destruct H as (q & n & Hin & Hr). destruct (proj1 (rta_fshadow_apart Σ m HA f k sf_in) q n Hin); lia.
    + destruct H as (f' & k' & Hin & Hr). destruct (proj2 (rta_fshadow_apart Σ m HA f k sf_in) f' k' ltac:(rewrite HF; right; exact Hin)); lia.
    + destruct H as (f' & k' & Hin & Hr).
      destruct (rta_frames_disj Σ m HA f k f' k' [] fr HF Hin) as [D|D].
      * pose proof (shad_mono _ _ D). lia.
      * pose proof (shad_mono _ _ D). lia.
  - (* [comment removed for export] *)
    intros Hx.
    destruct Ha as [H|[H|[H|[H|H]]]].
    + lia.
    + assert (D : disjoint_from CS_W (usp - 64) 64) by (apply dsj_CS_out; right; unfold SEGTOP_A, STACK_WIN in *; lia).
      apply (client_static_cover x H). apply (disjoint_outside _ _ _ _ D). lia.
    + destruct H as (q & n & Hin & Hr). destruct (rta_live_range Σ m q n HA Hin) as (_ & X & _). lia.
    + destruct H as (f' & k' & Hin & Hr). destruct (rta_frames_range Σ m HA f' k' ltac:(rewrite HF; right; exact Hin)) as (_ & X & _). lia.
    + destruct H as (f' & k' & Hin & Hr). destruct (rta_frames_range Σ m HA f' k' ltac:(rewrite HF; right; exact Hin)) as (X0 & X & _).
      pose proof (SHhi (f' + fs_size k') ltac:(unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k') ltac:(lia) ltac:(lia)); lia) X). lia.
Qed.

End SFRel.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sf_pre : forall Σ (m : mem) f k fr, ART_A Σ m -> frames Σ = (f, k) :: fr ->
  exists p, 0 <= p < NF (Z.of_nat k) /\ f = frame_addr (l_FSB (lay Σ)) (Z.of_nat k) p
    /\ u8arr asegs m (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + p) [Z_to_bv 8 1]
    /\ wr_at asegs m f (fs_size k) /\ wr_at asegs m (shad f) (fs_size k / 8)
    /\ rw_cells asegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + p))].
Proof.
  intros Σ m f k fr HA HF.
  assert (Hin : In (f, k) (frames Σ)) by (rewrite HF; left; reflexivity).
  destruct (busy_slot Σ m HA f k Hin) as (Hk & p & Hp & Hf & _).
  assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 3 \/ Z.of_nat k = 6 \/ Z.of_nat k = 7) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
  exists p. split; [exact Hp|]. split; [exact Hf|].
  destruct (rta_frame_release_at Σ m f k fr HA HF p Hp Hf) as (B & _).
  split; [exact (u8one_of_rw m _ _ B)|].
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & FB). unfold fs_busy in FB. rewrite HF in FB. apply Forall_cons_iff in FB as [FB0 _].
  destruct FB0 as (p' & Hf' & W1 & W2 & Cw). cbn [fst snd] in *. rewrite Hf in Hf'. apply (frame_addr_inj _ _ _ _ Hc) in Hf'. subst p'.
  split; [exact W1|]. split; [exact W2 | exact Cw].
Qed.

(* [comment removed for export] *)
Lemma sf_finish : forall (Σ : rtsA) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m : mem) (f : Z) (k : nat) (fr : list (Z * nat))
    (p lo : Z) (Pm : machine_state -> Prop) c1,
  ART_A Σ m -> frames Σ = (f, k) :: fr -> 0 <= p < NF (Z.of_nat k) -> f = frame_addr (l_FSB (lay Σ)) (Z.of_nat k) p ->
  rtA_sp0 Σ - STACK_WIN <= lo -> lo + RT_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  AST SEGTOP_A (rtA_allow Σ) Pm (fun mo => ARTM RTA Σ mo /\ PMc mo) c1 ->
  (forall ms, Pm ms -> exists m',
     ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
     /\ munch (sf_W (Z.of_nat k) (l_FSB (lay Σ)) p (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
     /\ stk asegs m' lo (bv_unsigned sp) /\ u8arr asegs m' (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + p) [Z_to_bv 8 0]) ->
  exists (Σ' : rts RTA) (v' : word),
       ASTA RTA Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v' m' ms
         /\ rt_after RTA Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RTA Σ) fr (bv_unsigned sp) m m') c1
       /\ rt_frames RTA Σ' = fr /\ rt_live RTA Σ' = rt_live RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ /\ rt_credit RTA Σ' = rt_credit RTA Σ.
Proof.
  intros Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m f k fr p lo Pm c1 HA HF Hp Hf LOW LOR SPT HAST HPm.
  exists (fs_release Σ k p fr), v.
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity | reflexivity]]]].
  unfold ASTA. change (rt_allow RTA (fs_release Σ k p fr)) with (rtA_allow Σ).
  eapply AST_conseq; [exact HAST| |intros mo Hmo; exact Hmo].
  intros ms HP. destruct (HPm ms HP) as (m' & RS & MU & WM & MI & ST' & FLZ).
  assert (Husp : lo + 64 <= bv_unsigned sp) by (unfold RT_STACK in LOR; lia).
  assert (Husp2 : bv_unsigned sp <= USTACK_TOP) by lia.
  destruct (sf_release Σ m m' f k fr p (bv_unsigned sp) lo HA HF Hp Hf LOW Husp Husp2 MU WM FLZ) as (ART' & _).
  pose proof (sf_pres Σ m m' f k fr p (bv_unsigned sp) lo HA HF Hp Hf LOW Husp Husp2 MU WM FLZ) as PRES.
  exists m'. split; [exact RS|]. split; [split; [exact ART' | split; [exact MI | split; [exact WM | exact ST']]]|]. exact PRES.
Qed.

Theorem rta_stack_free_6 : stack_free_contract RTA 6.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f size fr lo
    FDO MST Hk HF -> -> Hsz Hsz8 ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 6%nat lo ART0 ltac:(lia) LOW) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2S & FSOK & HLO & FSL & _).
  destruct (sf_pre Σ m f 6%nat fr ART0 HF) as (p & Hp & Hf & FLG & W1 & W2 & Cw).
  change (NF (Z.of_nat 6)) with 256 in Hp. change (fs_size 6) with 4096 in W1, W2, Cw. change (4096 / 8) with 512 in W2.
  destruct (wr_at_cb m f 4088%nat (wr_at_sub m f 4096 f 4088 W1 ltac:(lia) ltac:(lia) ltac:(lia))) as (junkF & FRc).
  destruct (wr_at_cb m (shad f) 512%nat W2) as (junkS & SHc).
  assert (LASTc : rw_cells asegs m f [CB 4088 junkF; C8 (Z_to_bv 64 (fl_base (l_FSB (lay Σ)) (Z.of_nat 6) + p))]).
  { apply (proj2 (rw_cells_app2 m f [CB 4088 junkF] [C8 (Z_to_bv 64 (fl_base (l_FSB (lay Σ)) (Z.of_nat 6) + p))])). split; [exact FRc|].
    cbn [cells_size csize Nat.add]. replace (f + Z.of_nat 4088) with (f + 4096 - 8) by lia. exact Cw. }
  assert (W0 : evt asegs (sf6_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) p lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_free 6) m)).
  { unfold entry_st. rewrite Hf in *.
    exact (stack_free_6_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) p lo _ junkF junkS Hp FLG LASTc SHc M2S FSOK HLO FSL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W0 with evt asegs _ ?X =>
    assert (W0' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W0) end.
  clear W0.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W0') Hc).
  intros c1 Hc1. apply Hkont. unfold sf6_post in Hc1.
  apply AST_exI in Hc1 as (v & Hc2).
  apply (sf_finish Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m f 6%nat fr p lo _ c1 ART0 HF
           ltac:(change (NF (Z.of_nat 6)) with 256; exact Hp) Hf LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & FLZ).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST' | exact FLZ].
Qed.

Theorem rta_stack_free_7 : stack_free_contract RTA 7.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f size fr lo
    FDO MST Hk HF -> -> Hsz Hsz8 ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *.
  assert (HLO7 : 0x7fff00000000 <= lo).
  { destruct CALL as (_ & LOW & _). pose proof (rta_sp0_win Σ m ART0) as SPW. cbn [rt_sp0 RTA] in LOW. unfold STACK_WIN in LOW. lia. }
  unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 7%nat lo ART0 ltac:(lia) LOW) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2S & FSOK & HLO & FSL & _).
  pose proof (ART_consts Σ m ART0) as (_ & _ & _ & _ & PS & _).
  destruct (sf_pre Σ m f 7%nat fr ART0 HF) as (p & Hp & Hf & FLG & W1 & W2 & Cw).
  change (NF (Z.of_nat 7)) with 128 in Hp. change (fs_size 7) with 8192 in W1, W2, Cw, Hsz. change (8192 / 8) with 1024 in W2.
  destruct (wr_at_cb m (shad f) 1024%nat W2) as (junkS & SHc).
  replace (f + 8192 - 8) with (f + 8184) in Cw by lia.
  assert (W0 : evt asegs (sf7_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) p lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_free 7) m)).
  { unfold entry_st. rewrite Hf in *.
    exact (stack_free_7_spec ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) p lo size _ junkS Hp Hsz Hsz8 FLG Cw SHc M2S PS FSOK HLO7 FSL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W0 with evt asegs _ ?X =>
    assert (W0' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W0) end.
  clear W0.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W0') Hc).
  intros c1 Hc1. apply Hkont. unfold sf7_post in Hc1.
  apply AST_exI in Hc1 as (v & Hc2).
  apply (sf_finish Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m f 7%nat fr p lo _ c1 ART0 HF
           ltac:(change (NF (Z.of_nat 7)) with 128; exact Hp) Hf LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & FLZ).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST' | exact FLZ].
Qed.
