(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibWP2Spec LibWP2Lib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibFrame AsLibEnv AsLibTagsLib AsLibFPSpec AsLibWP2Spec AsLibCurveSpec AsLibBswap BoLibReadA2Ba BoLibReadA2Bb BoLibSpec BoLibReadB2Aa BoLibReadB2Ab BoLibReadB2Ac AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
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
#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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

(* [comment removed for export] *)
Section RS.
  Variable ceil : Z.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T B : word) (pcs : Z) (fs : Z) (ch : chain).

  #[local] Abbreviation a := (bv_unsigned B).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation eobw := (Z_to_bv 64 (bv_unsigned data + len)).
  #[local] Abbreviation ADM := (adm ceil FPI0 regs0 mem0 ret data len bs sp T B fs ch).
  #[local] Abbreviation QP := (Qpost FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch).
  #[local] Abbreviation TAGC := (tagc data len T).
  #[local] Abbreviation curves0I := (curves0 data len B).
  #[local] Abbreviation stkI := (stk data len bs sp T B).
  #[local] Abbreviation WI := (W data bs).
  #[local] Abbreviation bbI := (bb data bs).
  #[local] Abbreviation mab_cellsI := (mab_cells B).
  #[local] Abbreviation le4wI := (le4w data bs).
  #[local] Abbreviation be4I := (be4 data bs).
  #[local] Abbreviation curves10I := (curves10 data len B).

  (* [comment removed for export] *)
  Definition m1_stmt : Prop := forall (FPI : FPState) R M sz buf oc r,
    ADM FPI R M -> TAGC 0x6d424120 sz buf M -> (32 <= sz)%Z ->
    cell32 SEGS M (a + 96) 3 -> cell32 SEGS M (a + 396) oc -> (oc = 3 \/ oc = 4)%Z -> stkI buf M ->
    getr R 10 = Z_to_bv 64 r -> (r = 0%Z \/ (r = 1%Z /\ curves0I M)) ->
    getr R 9 = WI buf 17 -> getr R 18 = WI buf 22 -> getr R 19 = Z_to_bv 64 (t + 8) ->
    getr R 20 = WI buf 23 -> getr R 21 = WI buf 18 -> getr R 22 = Z_to_bv 64 pcs -> getr R 23 = WI buf 16 ->
    getr R 24 = Z_to_bv 64 SB -> getr R 25 = WI buf 20 -> getr R 26 = WI buf 21 ->
    getr R 27 = WI buf 19 ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x85d24) M rom) QP.
  #[local] Abbreviation m1_stmtI := m1_stmt.

  (* [comment removed for export] *)
  Definition jseg_stmt : Prop := forall (FPI : FPState) R M sz buf oc mc,
    ADM FPI R M -> TAGC 0x6d424120 sz buf M -> (32 <= sz)%Z -> mab_cellsI oc mc M -> curves0I M -> stkI buf M ->
    getr R 16 = WI buf 31 -> getr R 15 = WI buf 28 -> getr R 18 = WI buf 27 -> getr R 21 = WI buf 26 ->
    getr R 22 = WI buf 30 -> getr R 20 = eobw -> getr R 25 = Z_to_bv 64 (SB + (a + 396) / 8) ->
    getr R 28 = Z_to_bv 64 (t + 16) -> getr R 29 = Z_to_bv 64 (SB + (t + 16) / 8) -> getr R 30 = Z_to_bv 64 (SB + (t + 8) / 8) ->
    getr R 31 = Z_to_bv 64 (a + 96) -> getr R 19 = Z_to_bv 64 (t + 8) -> getr R 24 = Z_to_bv 64 SB ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x8674c) M rom) QP.
  #[local] Abbreviation jseg_stmtI := jseg_stmt.

  (* [comment removed for export] *)
  Definition m3a_stmt : Prop := forall (FPI : FPState) R M sz buf oc mc r,
    ADM FPI R M -> TAGC 0x6d424120 sz buf M -> (32 <= sz)%Z -> mab_cellsI oc mc M -> stkI buf M ->
    getr R 10 = Z_to_bv 64 r -> (r = 0%Z \/ (r = 1%Z /\ curves10I M)) ->
    getr R 9 = le4wI buf 24 -> getr R 18 = WI buf 27 -> getr R 21 = WI buf 26 -> getr R 20 = eobw ->
    getr R 25 = Z_to_bv 64 (SB + (a + 396) / 8) -> getr R 19 = Z_to_bv 64 (t + 8) -> getr R 24 = Z_to_bv 64 SB ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x867dc) M rom) QP.
End RS.
