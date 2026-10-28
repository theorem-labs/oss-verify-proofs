(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SFMisc.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut DecTac.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.

Ltac gb_next_red keep Wloc IB :=
  cbv zeta;
  repeat match goal with H : dpure _ _ _ _ _ |- _ => clear H end;
  let m := fresh "m" in let bb := fresh "bb" in let bl := fresh "bl" in let ai := fresh "ai" in
  let til := fresh "til" in let tih := fresh "tih" in
  let DM := fresh "DM" in let FR := fresh "FR" in let ST := fresh "ST" in let MU := fresh "MU" in
  let WM := fresh "WM" in let MI := fresh "MI" in let DP := fresh "DP" in
  let RB := fresh "RB" in let RL := fresh "RL" in let RA := fresh "RA" in let CONS := fresh "CONS" in
  intros m bb bl ai til tih DM FR ST MU WM MI DP RB RL RA CONS; intros;
  cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k bupd
       sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
       sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
       bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque] in DM, DP, CONS;
  (* [comment removed for export] *)
  lazymatch type of DM with dmem _ _ _ _ _ _ ?v' =>
  let R := lazymatch type of IB with (in_bits _ _ <= ?R)%Z => R | (in_bits _ _ < ?R)%Z => R end in
    let IB' := fresh "IB" in
    let T := eval cbn [dv_h dv_b] in (in_bits (dv_b v') (dv_h v') <= R)%Z in
    assert (IB' : T) by
     (clear -IB CONS; unfold in_bits, consumed in *;
      cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k bupd
           sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
           sh_cbn sh_verb sh_origPtr sh_tPos sh_k0
           bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque] in *;
      lia);
    clear IB; rename IB' into IB
  end;
  unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU;
  unfold consumed in CONS; (* [comment removed for export] *)
  open_dmem DM;
  cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k bupd
       sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
       sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
       bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque] in *;
  dimg_norm;
  hide_all_but_at keep;
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl Wloc mm) as MUL; pose proof (wmono_refl segs mm) as WML
  end.
