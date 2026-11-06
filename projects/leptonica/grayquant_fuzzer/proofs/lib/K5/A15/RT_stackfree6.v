(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Exec RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface D_defs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs
  R_fs_defs16 R_fs_ok R_tlsgetaddr R_intalloc R_thread R_m2s RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit RT_facts
  RT_release RT_stackmalloc R_fsfree6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Definition e_stack_free_6 : Z := 0x4c110.

(* [comment removed for export] *)
Definition stack_free_contract_A : Prop :=
  forall (Σ : rts RTA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (f : Z) (fr : list (Z * nat)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 f -> rt_frames RTA Σ = (f, 6%nat) :: fr ->
  ART RTA Σ m -> mem_inv asegs m -> call_ok RTA Σ m sp lo ->
  cps asegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_stack_free_6 m)))
    (fun c => exists (Σ' : rts RTA) (v : word),
       ASTA RTA Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after RTA Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RTA Σ) fr (bv_unsigned sp) m m') c
       /\ rt_frames RTA Σ' = fr /\ rt_live RTA Σ' = rt_live RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ
       /\ rt_credit RTA Σ' = rt_credit RTA Σ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma c8_unique : forall (m : mem) A (x y : word), ro_cells asegs m A [C8 x] -> ro_cells asegs m A [C8 y] -> x = y.
Proof.
  intros m A x y [_ (_ & _ & Bx)] [_ (_ & _ & By)]. cbn [cells_bytes cbytes] in Bx, By. rewrite app_nil_r in Bx, By.
  rewrite <- (le_bytes_to_word_le8 x), <- (le_bytes_to_word_le8 y). f_equal.
  apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i 8) as [Hi|Hi].
  - rewrite <- (Bx i) by (rewrite length_le8; exact Hi). rewrite <- (By i) by (rewrite length_le8; exact Hi). reflexivity.
  - rewrite !(proj2 (nth_error_None _ _)) by (rewrite length_le8; exact Hi). reflexivity.
Qed.

Lemma shad_add_4096 : forall f, f mod 8 = 0 -> shad (f + 4096) = shad f + 512.
Proof. intros f Hf. unfold shad. replace (f + 4096) with (f + 512 * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

(* [comment removed for export] *)
Definition mem_keep1 (fl : Z) (m m' : mem) : mem := fun x => if Z.eqb (bv_unsigned x) fl then m x else m' x.

Lemma wview_keep1 : forall fl (m m' : mem) x,
  wview asegs (mem_keep1 fl m m') x = if Z.eqb (bv_unsigned x) fl then wview asegs m x else wview asegs m' x.
Proof. intros fl m m' x. unfold wview, mem_keep1. destruct (Z.eqb (bv_unsigned x) fl); reflexivity. Qed.

Lemma keep1_wmono_l : forall fl (m m' : mem), wmono asegs m m' -> wmono asegs m (mem_keep1 fl m m').
Proof. intros fl m m' WM x Hx. rewrite wview_keep1. destruct (Z.eqb (bv_unsigned x) fl); [exact Hx | exact (WM x Hx)]. Qed.

Lemma keep1_wmono_r : forall fl (m m' : mem), wmono asegs m m' -> wmono asegs (mem_keep1 fl m m') m'.
Proof. intros fl m m' WM x Hx. rewrite wview_keep1 in Hx. destruct (Z.eqb (bv_unsigned x) fl); [exact (WM x Hx) | exact Hx]. Qed.

Lemma keep1_munch_r : forall fl (m m' : mem), munch [(fl, fl + 1)] (mem_keep1 fl m m') m'.
Proof.
  intros fl m m' x Hx. unfold mem_keep1. destruct (Z.eqb_spec (bv_unsigned x) fl) as [E|E]; [|reflexivity].
  cbn [outside] in Hx. destruct Hx as [Hx _]. exfalso. apply Hx. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rta_stack_free_6 : stack_free_contract_A.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo
    FDO MST -> HFR ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW.
  set (usp := bv_unsigned sp) in *.
  (* [comment removed for export] *)
  assert (HIN : In (f, 6%nat) (frames Σ)) by (rewrite HFR; left; reflexivity).
  destruct (busy_slot Σ m ART0 f 6%nat HIN) as (_ & p & Hp & Hf & Hb). change (Z.of_nat 6) with 6 in Hp, Hf. rewrite NF_6 in Hp.
  destruct (sm_pre Σ m 6%nat lo ART0 ltac:(lia) LOW) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2S & FSOK & HLO & FSL & _).
  pose proof (ART_fs Σ m ART0) as FS. destruct FS as (_ & _ & _ & _ & _ & FB). unfold fs_busy in FB. rewrite HFR in FB.
  apply Forall_cons_iff in FB as [FB0 _]. destruct FB0 as (p' & Hf' & _ & FWs & Cw). cbn [fst snd] in Hf', FWs, Cw.
  change (Z.of_nat 6) with 6 in Hf', Cw.
  assert (p' = p) by (apply (frame_addr_inj (l_FSB (lay Σ)) 6 p' p ltac:(lia)); rewrite <- Hf'; exact Hf). subst p'.
  set (fl := fl_base (l_FSB (lay Σ)) 6 + p) in *. set (S := shad f).
  pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kFakeStackSize, kHighShadowEnd in *.
  assert (Hfv : f = (l_FSB (lay Σ)) + 6328320 + p * 4096) by (rewrite Hf; unfold frame_addr, fsz; cbn; lia).
  assert (Hflv : fl = (l_FSB (lay Σ)) + 36352 + p) by (unfold fl, fl_base, flags_off; cbn; lia).
  assert (Hf8 : f mod 8 = 0).
  { rewrite Hfv. assert (E : (l_FSB (lay Σ)) = 4096 * ((l_FSB (lay Σ)) / 4096)) by (apply Z.div_exact; lia). rewrite E.
    replace (4096 * ((l_FSB (lay Σ)) / 4096) + 6328320 + p * 4096) with ((512 * ((l_FSB (lay Σ)) / 4096) + 791040 + p * 512) * 8) by lia. apply Z.mod_mul. lia. }
  assert (HSv : S = (l_FSB (lay Σ)) / 8 + p * 512 + 2148241920).
  { unfold S. rewrite Hf, shad_frame by lia. rewrite fsz_6. change (4096 / 8) with 512. change (6 * 2 ^ 17) with 786432. unfold SHB. lia. }
  assert (HF8 : 0 <= (l_FSB (lay Σ)) / 8 /\ (l_FSB (lay Σ)) / 8 * 8 = (l_FSB (lay Σ))).
  { assert (E : (l_FSB (lay Σ)) = 8 * ((l_FSB (lay Σ)) / 8)) by (apply Z.div_exact; [lia|]; apply Z.mod_divide; [lia|];
      apply (Z.divide_trans 8 4096); [exists 512; reflexivity | apply Z.mod_divide; lia]). split; [apply Z.div_pos; lia | lia]. }
  change (fs_size 6) with 4096 in Cw, FWs. replace (f + 4096 - 8) with (f + 4088) in Cw by lia. change (4096 / 8) with 512 in FWs.
  destruct (wr_at_rw_CB m S 512 FWs ltac:(lia)) as (junk & SHm).
  (* [comment removed for export] *)
  destruct (rta_frame_release Σ m f 6%nat fr ART0 HFR) as (Σ0 & fl0 & FLG0 & NCL0 & Hfl00 & Hfl0lo & RO0 & _).
  change (fs_size 6) with 4096 in RO0. replace (f + 4096 - 8) with (f + 4088) in RO0 by lia.
  pose proof (rta_sp0_range Σ m ART0) as SPR. unfold rtA_sp0, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *.
  assert (Efl : fl0 = fl).
  { pose proof (c8_unique m _ _ _ RO0 (proj1 Cw)) as E. apply (f_equal bv_unsigned) in E.
    rewrite !unsigned_lit in E by lia. exact E. }
  subst fl0.
  (* [comment removed for export] *)
  assert (W1 : evt asegs (sf6_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (frm_clear fc) fl S lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc e_stack_free_6 m)).
  { unfold entry_st, e_stack_free_6.
    apply (stack_free_6_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F (frm_clear fc) m f fl S lo junk); try reflexivity; try assumption; fold usp; try lia; try exact (proj1 Cw).
    apply (fsb_in_mem (l_FSB (lay Σ)) f FSOK). unfold kFakeStackSize. lia. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont.
  destruct Hc1 as (HM1 & HP1 & HPM1 & HZ1).
  destruct HP1 as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & EMS & MU & WM & MI
    & ST' & FLG' & SH').
  (* [comment removed for export] *)
  set (ma := mem_keep1 fl m m').
  assert (ARTa : ART_A Σ ma).
  { apply (ART_client_frame Σ m ma lo ART0 LOW); [|exact (keep1_wmono_l fl m m' WM)].
    intros a Ha. unfold ma, mem_keep1. destruct (Z.eqb_spec (bv_unsigned a) fl) as [E|E]; [reflexivity|].
    apply MU. unfold sf6_W. cbn [outside]. set (x := bv_unsigned a) in *.
    split; [lia|]. split.
    - intros Hx. apply Ha. right. right. right. right. exists f, 6%nat. split; [exact HIN|].
      change (fs_size 6) with 4096. rewrite (shad_add_4096 f Hf8). fold S. lia.
    - split; [|exact I]. intros Hx. apply Ha. left. fold usp in Hx. unfold USTACK_TOP. lia. }
  (* [comment removed for export] *)
  assert (HFRa : frames Σ = (f, 6%nat) :: fr) by exact HFR.
  destruct (rta_frame_release Σ ma f 6%nat fr ARTa HFRa) as (Σ' & fl1 & FLG1 & _ & Hfl10 & Hfl1lo & RO1 & KREL).
  unfold rtA_sp0, STACK_WIN in Hfl1lo. change (fs_size 6) with 4096 in RO1. replace (f + 4096 - 8) with (f + 4088) in RO1 by lia.
  assert (Cwa : ro_cells asegs ma (f + 4088) [C8 (Z_to_bv 64 fl)]).
  { pose proof (ART_fs Σ ma ARTa) as FSa. destruct FSa as (_ & _ & _ & _ & _ & FBa). unfold fs_busy in FBa. rewrite HFR in FBa.
    apply Forall_cons_iff in FBa as [FBa0 _]. destruct FBa0 as (p2 & Hf2 & _ & _ & Cw2). cbn [fst snd] in Hf2, Cw2.
    change (Z.of_nat 6) with 6 in Hf2, Cw2.
    assert (p2 = p) by (apply (frame_addr_inj (l_FSB (lay Σ)) 6 p2 p ltac:(lia)); rewrite <- Hf2; exact Hf). subst p2.
    change (fs_size 6) with 4096 in Cw2. replace (f + 4096 - 8) with (f + 4088) in Cw2 by lia. exact (proj1 Cw2). }
  assert (Efl1 : fl1 = fl).
  { pose proof (c8_unique ma _ _ _ RO1 Cwa) as E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. exact E. }
  subst fl1.
  destruct (KREL m' (keep1_munch_r fl m m') (keep1_wmono_r fl m m' WM) FLG') as (ART' & EF & EL & ES & EC & EA & EM).
  exists Σ', a0'.
  split; [|split; [exact EF | split; [exact EL | split; [exact ES | exact EC]]]].
  unfold ASTA. cbn [rt_allow ARTM RTA]. rewrite EA.
  split; [exact HM1|]. split; [|split; [split; [apply EM; exact (proj1 HPM1) | exact (proj2 HPM1)] | exact HZ1]].
  exists m'. split; [rewrite EMS; exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split; [split; [exact ART' | split; [exact MI | split; [exact WM | exact ST']]]|].
  (* [comment removed for export] *)
  intros a Ha. apply MU. unfold sf6_W. cbn [outside]. set (x := bv_unsigned a) in *.
  assert (HaΣ : forall spx, x < usp -> aclient (live Σ) (frames Σ) spx x).
  { intros spx Hx. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; [fold usp in Ha; lia | right; left; exact Ha | right; right; left; exact Ha | |].
    - right. right. right. left. destruct Ha as (f2 & k2 & Hin & Hr). exists f2, k2. split; [rewrite HFR; right; exact Hin | exact Hr].
    - right. right. right. right. destruct Ha as (f2 & k2 & Hin & Hr). exists f2, k2. split; [rewrite HFR; right; exact Hin | exact Hr]. }
  split.
  { (* [comment removed for export] *)
    intros Hx. apply NCL0. replace fl with x by lia. apply HaΣ. lia. }
  split.
  { (* [comment removed for export] *)
    intros Hx. destruct (rta_fshadow_apart Σ m ART0 f 6%nat HIN) as (AP1 & AP2).
    change (fs_size 6) with 4096 in AP1, AP2. rewrite (shad_add_4096 f Hf8) in AP1, AP2. fold S in AP1, AP2.
    destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
    - fold usp in Ha. lia.
    - destruct Ha as ((l0 & h0 & Hin & Hr) & _). unfold CLIENT_STATIC in Hin.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
    - destruct Ha as (p2 & n2 & Hin & Hr). pose proof (AP1 p2 n2 Hin). lia.
    - destruct Ha as (f2 & k2 & Hin & Hr). pose proof (AP2 f2 k2 ltac:(rewrite HFR; right; exact Hin)). lia.
    - destruct Ha as (f2 & k2 & Hin & Hr).
      destruct (rta_frames_disj Σ m ART0 f 6%nat f2 k2 [] fr HFR Hin) as [D|D]; change (fs_size 6) with 4096 in D.
      + pose proof (shad_mono _ _ D) as M1. rewrite (shad_add_4096 f Hf8) in M1. fold S in M1. lia.
      + pose proof (shad_mono _ _ D) as M1. fold S in M1. lia. }
  split; [|exact I].
  { (* [comment removed for export] *)
    intros Hx. fold usp in Hx. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
    - fold usp in Ha. lia.
    - destruct Ha as ((l0 & h0 & Hin & Hr) & _). unfold CLIENT_STATIC in Hin.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
    - destruct Ha as (p2 & n2 & Hin & Hr). destruct (rta_live_range Σ m p2 n2 ART0 Hin) as (_ & X & _). unfold rtA_sp0, STACK_WIN in X. lia.
    - destruct Ha as (f2 & k2 & Hin & Hr).
      destruct (rta_frames_range Σ m ART0 f2 k2 ltac:(rewrite HFR; right; exact Hin)) as (_ & X & _). unfold rtA_sp0, STACK_WIN in X. lia.
    - destruct Ha as (f2 & k2 & Hin & Hr).
      destruct (rta_frames_range Σ m ART0 f2 k2 ltac:(rewrite HFR; right; exact Hin)) as (X0 & X & _). unfold rtA_sp0, STACK_WIN in X.
      assert (shad (f2 + fs_size k2) <= 2 ^ 44 + SHB).
      { unfold shad. assert ((f2 + fs_size k2) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
      unfold SHB in *. lia. }
Qed.
