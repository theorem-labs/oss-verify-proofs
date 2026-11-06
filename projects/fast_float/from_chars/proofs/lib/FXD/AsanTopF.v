(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg RealizesAbort AsanAcct FxLin FxCore FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Spec.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF AsanMainP AsanErrT AsanPhKS AsanPhKW AsanPhK0.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhKCAThm.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhKCBThm.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanPhAll.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanErrT OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhKS OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhKW OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhK0 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhKCAThm.AsanPhKCA OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhKCBThm.AsanPhKCB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPhAll.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcHA AcFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanRdErr AsanTop0 AsanTop AsanErrLeaf AsanSpecBridge AsanFileEntry.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma SHSF_wf : shp_wf (dvar H0 18) SHSF = true. Proof. vm_compute. reflexivity. Qed.
Lemma SHWF_wf : shp_wf (dvar H0 18) SHWF = true. Proof. vm_compute. reflexivity. Qed.
Lemma SHL_wf : shp_wf (dvar H0 18) SHL = true. Proof. vm_compute. reflexivity. Qed.

Section TopF.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hfs : sc_fs cfg = true.
(* [comment removed for export] *)
Hypothesis Hleaves : forall (path0 : path) (data0 : list byte) (fs0 : Fs.Fs) (argv0 : list byte),
  path_eqb path0 [] = false -> path_has_slash path0 = false -> path_is_dirref path0 = false -> (length path0 < path_max)%nat ->
  Forall (fun b => b <> Z_to_bv 8 0) path0 -> 6 <= Z.of_nat (length data0) <= PHI ->
  Forall (cont_okR cfg path0 data0 fs0 argv0) CONTSCA /\ Forall (cont_okR cfg path0 data0 fs0 argv0) CONTSCB.

#[using="Hoff Hfs Hleaves"] Theorem h_file : forall sp brk0 mb draw inp data, valid_sp sp -> valid_brk ASEGS brk0 -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> length (in_argv inp) = 2%nat ->
  (length (nth 1 (in_argv inp) []) < 4096)%nat -> path_eqb (nth 1 (in_argv inp) []) [] = false ->
  path_is_dirref (nth 1 (in_argv inp) []) = false -> fs_lookup (in_fs inp) (nth 1 (in_argv inp) []) = Some data ->
  at_main cfg sp brk0 mb draw inp (t_alt2 (t_die (msg_cannot_open (nth 1 (in_argv inp) [])) (in_fs inp)) (t_body data (in_fs inp))).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hleaves : LiaFast.U) => LiaFast.u0).
  intros sp brk0 mb draw inp data Hsp Hbrk Hfit Hva Hve Hvfs H2 Hlt Hne Hdr Hlk mem0 E ms model Hag Hd HAa Hfk.
  set (p := nth 1 (in_argv inp) []) in *. set (fs := in_fs inp) in *. set (a0 := nth 0 (in_argv inp) []).
  assert (Hsame : forall q, In q (sm_frz M1) -> forall w, uE E (fst q) <= w < uE E (fst q) + uE E (snd q) ->
                    mem0 (Z_to_bv 64 w) = m0 sp draw inp (Z_to_bv 64 w)) by (rewrite FRZ0_M1; exact Hfk).
  (* [comment removed for export] *)
  assert (Hin : In p (in_argv inp)) by (apply nth_In; lia).
  assert (Hex : exists x y, in_argv inp = [x; y]).
  { destruct (in_argv inp) as [|x [|y [|z r]]]; cbn [length] in H2; try lia. exists x, y. reflexivity. }
  destruct Hex as (x & y & Hav).
  assert (Hp2 : path_has_slash p = false).
  { destruct Hva as (_ & _ & _ & _ & Htl). rewrite Hav in Htl. cbn [tl] in Htl. apply Forall_cons_iff in Htl as [[X _] _].
    unfold p. rewrite Hav. exact X. }
  assert (Hp5 : Forall (fun b => b <> Z_to_bv 8 0) p).
  { destruct Hva as (_ & _ & _ & Hnz & _). rewrite Forall_forall in Hnz. apply Forall_forall. intros b Hb Hc. subst b. exact (Hnz p Hin Hb). }
  assert (Hp4 : (length p < path_max)%nat) by (unfold path_max; exact Hlt).
  pose proof (herr cfg Hoff Hfs p data fs a0 Hne Hp2 Hdr Hp4 Hp5) as Herr.
  (* [comment removed for export] *)
  assert (ENT : forall lo hi, lo <= flen_of (length data) <= hi ->
            let E1 := ext data p E in
            DEN ASEGS LIM (model0 sp brk0 mb LIM inp) mem0 E1 (S1c2 lo hi) MMAIN ms model /\
            INV PV p data fs false (Some H0) mem0 E1 (S1c2 lo hi) MMAIN FSClosed (model0 sp brk0 mb LIM inp) /\
            HAX awf HA E1 (S1c2 lo hi) MMAIN AMAIN mem0 /\
            uE E1 ARGC = 2 /\ uE E1 (hvar 17) = Z.of_nat (length p) /\ uE E1 (hvar 16) = flen_of (length data) /\
            (forall k, (k < 3)%nat -> uE E1 (hvar k) = bv_unsigned (nth k data (Z_to_bv 8 0)))).
  { intros lo hi HL E1. unfold E1, p, fs.
    split; [eapply den_entry; eassumption|].
    split; [eapply inv_entry; eassumption|].
    split; [eapply hax_entry; eassumption|].
    split; [eapply uARGC1; eassumption|].
    split; [eapply uL17; eassumption|].
    split; [eapply uL16; eassumption|].
    intros k Hk. eapply uByte; first [eassumption | lia]. }
  destruct (Z_le_gt_dec (Z.of_nat (length data)) 5) as [C1|C1].
  { (* [comment removed for export] *)
    destruct (ENT 0 5 ltac:(rewrite flen_of_small by (unfold GHI; lia); lia)) as (D1 & I1 & X1 & U2 & U17 & U16 & UB).
    rewrite <- (sh_short_den p fs a0 data (ext data p E) ltac:(lia)).
    rewrite <- (sh_top_den p fs a0 (ext data p E) SH_SHORT U2 U17).
    exact (short_realizes cfg Hoff Hfs p data fs a0 Hne Hp2 Hdr Hp4 Hp5 Herr ltac:(lia) _ mem0 _ ms model D1 I1 X1
             ltac:(unfold S1S2; rewrite S1c2_next; exact SHSF_wf)). }
  destruct (Z_le_gt_dec (Z.of_nat (length data)) 65535) as [C2|C2].
  { (* [comment removed for export] *)
    destruct (ENT 6 65535 ltac:(rewrite flen_of_small by (unfold GHI; lia); lia)) as (D1 & I1 & X1 & U2 & U17 & U16 & UB).
    destruct (Hleaves p data fs a0 Hne Hp2 Hdr Hp4 Hp5 ltac:(unfold PHI; lia)) as [HlA HlB].
    rewrite flen_of_small in U16 by (unfold GHI; lia).
    rewrite <- (file_w_den p fs a0 data (ext data p E) U16 UB ltac:(lia)).
    rewrite <- (sh_top_den p fs a0 (ext data p E) FILE_W U2 U17).
    exact (wide_realizes cfg Hoff Hfs p data fs a0 Hne Hp2 Hdr Hp4 Hp5 HlA HlB Herr ltac:(lia) _ mem0 _ ms model D1 I1 X1
             ltac:(unfold S1W2; rewrite S1c2_next; exact SHWF_wf)). }
  destruct (Z_le_gt_dec (Z.of_nat (length data)) PHI) as [C3|C3].
  { (* [comment removed for export] *)
    destruct (ENT 65536 GHI ltac:(split; [apply flen_of_big; [unfold GHI|]; lia | apply flen_of_range])) as (D1 & I1 & X1 & U2 & U17 & U16 & UB).
    destruct (Hleaves p data fs a0 Hne Hp2 Hdr Hp4 Hp5 ltac:(lia)) as [HlA HlB].
    rewrite flen_of_small in U16 by (unfold GHI, PHI in *; lia).
    rewrite <- (file_w_den p fs a0 data (ext data p E) U16 UB ltac:(unfold PHI in *; lia)).
    rewrite <- (sh_top_den p fs a0 (ext data p E) FILE_W U2 U17).
    exact (grow_realizes cfg Hoff Hfs p data fs a0 Hne Hp2 Hdr Hp4 Hp5 HlA HlB Herr ltac:(lia) _ mem0 _ ms model D1 I1 X1
             ltac:(unfold S1P2; rewrite S1c2_next; exact SHWF_wf)). }
  (* [comment removed for export] *)
  destruct (ENT 65536 GHI ltac:(split; [apply flen_of_big; [unfold GHI|unfold PHI in *]; lia | apply flen_of_range])) as (D1 & I1 & X1 & U2 & U17 & U16 & UB).
  rewrite <- (sh_refused_den p fs a0 data (ext data p E) ltac:(unfold PHI in *; lia)).
  rewrite <- (sh_top_den p fs a0 (ext data p E) SH_REFUSED U2 U17).
  exact (refused_realizes_R cfg Hoff Hfs p data fs a0 Hne Hp2 Hdr Hp4 Hp5 Herr ltac:(unfold FLLO, PHI in *; lia) _ mem0 _ ms model D1 I1 X1
           ltac:(unfold S1L2, S1P2; rewrite S1c2_next; exact SHL_wf)).
Qed.

(* [comment removed for export] *)
#[using="Hoff Hfs Hleaves"] Theorem asan_realizes_F : image_realizes_cfg_e cfg ASEGS Asan.M.init_pc APH LIM (fun inp => spec (in_argv inp) (in_fs inp)).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hleaves : LiaFast.U) => LiaFast.u0). exact (asan_realizes cfg Hoff Hfs h_file). Qed.
End TopF.
