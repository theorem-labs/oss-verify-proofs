(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsLibTagsLib AsLibFPLib AsLibEnv.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
(* [comment removed for export] *)
#[local] Ltac AsSymDrive.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac AsSymDrive.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.

(* [comment removed for export] *)
Ltac qlia :=
  repeat match goal with HQ : hidden ?T |- _ => let X := fresh "Q" in pose proof (unhide HQ) as X; clear HQ;
           repeat match type of X with _ /\ _ => let Y := fresh "Q" in destruct X as [Y X] end end;
  lia.

(* [comment removed for export] *)
Ltac alia := first [lia | qlia].

Ltac rewrite_getr_in H :=
  repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.
Ltac ev_simpl_goal := match goal with HK : know_ok _ ?E0 _ _ |- _ => ev_simpl E0 end.

(* [comment removed for export] *)
Ltac regions_eq :=
  repeat (lazymatch goal with
          | |- (_ :: _) = (_ :: _) => apply f_equal2; [apply f_equal2; [apply (f_equal (Z_to_bv 64)); unfold SB; alia | reflexivity] |]
          | |- [] = [] => reflexivity end).
Ltac norm_denots E0 := cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E0;
                       unfold v_addi; rewrite ?u_srl3; rewrite_getr; rewrite ?alu_add_lit; rewrite ?u_small by alia.
Ltac flats E0 := repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; unfold flat, estart, elenZ; cbn [a_base a_off];
                 rewrite ?edenot_srl3; cbn [edenot]; ev_simpl E0; rewrite_getr; rewrite ?alu_add_lit; rewrite ?u_small by alia; unfold SB; alia.

(* [comment removed for export] *)
Ltac frame_of_log RS :=
  lazymatch goal with
  | |- frame_mod ?M0 (mem_denot ?E0 ?M0 ?log) ?regions =>
      replace regions with (regions_denot E0 RS) by (norm_denots E0; regions_eq);
      apply (frame_mod_mem_denot E0 M0 log RS);
        [ lazymatch goal with H : log_flat _ log |- _ => exact H end
        | flats E0
        | vm_compute; reflexivity ]
  end.

(* [comment removed for export] *)
Ltac kframe HK Hfr RS :=
  lazymatch type of HK with know_ok ?segs ?E1 ?M0 ?kn =>
  lazymatch type of Hfr with frame_mod _ ?M' ?rs =>
    let Hrd := fresh "Hrd" in let Hrs := fresh "Hrs" in let Hfl := fresh "Hfl" in let H := fresh "HK" in
    assert (Hrd : regions_denot E1 RS = rs) by (norm_denots E1; regions_eq);
    assert (Hrs : frame_mod M0 M' (regions_denot E1 RS)) by (rewrite Hrd; exact Hfr);
    assert (Hfl : Forall (fun r => flat E1 (fst r) (snd r)) RS) by (flats E1);
    pose proof (know_ok_frame_mod segs E1 RS M0 M' kn HK Hfl Hrs) as H;
    let kn' := eval vm_compute in (kn_frames kn RS) in
    change (kn_frames kn RS) with kn' in H;
    clear Hrd Hrs Hfl HK; rename H into HK
  end end.

(* [comment removed for export] *)
Ltac kcell HK b k n v H :=
  lazymatch type of HK with know_ok ?segs ?E0 ?M0 ?kn =>
    let KR := fresh "KR" in let Hfl := fresh "Hfl" in
    assert (KR : kread segs kn b k n = Some v) by (vm_compute; reflexivity);
    pose proof (kread_rdn segs E0 M0 kn b k n v HK KR ltac:(lia) ltac:(lia)) as H; clear KR;
    lazymatch type of H with ?FL -> _ =>
      assert (Hfl : FL) by (unfold flat, estart; cbn [a_base a_off]; rewrite ?edenot_srl3; cbn [edenot]; ev_simpl E0; rewrite_getr;
                            rewrite ?alu_add_lit; rewrite ?u_small by alia; unfold SB; alia);
      specialize (H Hfl); clear Hfl end;
    unfold adenot, v_addi in H; cbn [a_base a_off] in H; cbn [edenot] in H; ev_simpl_in E0 H; rewrite ?u_srl3 in H; rewrite_getr_in H;
    rewrite ?alu_add_lit in H; rewrite ?u_small in H by alia
  end.
Ltac kcell_auto HK b k n H :=
  lazymatch type of HK with know_ok ?segs _ _ ?kn =>
    let r := eval vm_compute in (kread segs kn b k n) in
    lazymatch r with Some ?v => kcell HK b k n v H end end.

(* [comment removed for export] *)
Ltac kn_prefix HK entries :=
  lazymatch type of HK with know_ok ?segs ?E1 ?M1 ?kn1 =>
    let HK' := fresh "HK" in
    assert (HK' : know_ok segs E1 M1 (entries ++ kn1));
    [ apply know_ok_app; [| exact HK]; unfold know_ok; repeat (apply Forall_cons); try apply Forall_nil
    | clear HK; rename HK' into HK; cbn [app] in HK ]
  end.
(* [comment removed for export] *)
Ltac kn_suffix HK entries :=
  lazymatch type of HK with know_ok ?segs ?E1 ?M1 ?kn1 =>
    let HK' := fresh "HK" in
    assert (HK' : know_ok segs E1 M1 (kn1 ++ entries));
    [ apply know_ok_app; [exact HK|]; unfold know_ok; repeat (apply Forall_cons); try apply Forall_nil
    | clear HK; rename HK' into HK; let kn' := eval cbn in (kn1 ++ entries) in change (kn1 ++ entries) with kn' in HK ]
  end.

(* [comment removed for export] *)
Ltac solve_apart_x :=
  unfold apart, SB; repeat (apply Forall_cons; [cbn [fst snd]; rewrite ?u_small_frame by alia; alia |]);
  apply Forall_nil.
