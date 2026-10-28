(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SFMisc.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.

(* [comment removed for export] *)
Ltac cut_side DP :=
  lazymatch goal with
  | |- dmem _ _ _ _ _ _ _ => close_dmem
  | |- rw_cells _ _ (bv_unsigned (a_sp _) + _)%Z _ =>
      match goal with H : rw_cells _ _ (bv_unsigned (a_sp _) + _)%Z _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- munch _ (a_m0 _) _ => match goal with H : munch _ (a_m0 _) _ |- _ => exact H end
  | |- wmono _ (a_m0 _) _ => match goal with H : wmono _ (a_m0 _) _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  | |- dpure _ _ _ _ _ => solve [ dpure_from DP ]
  end.

(* [comment removed for export] *)
Ltac unify_mem :=
  lazymatch goal with |- ?a = ?b =>
    lazymatch a with MS _ _ _ _ _ ?m1 _ =>
    lazymatch b with MS _ _ _ _ _ ?m2 _ => unify m2 m1 end end end.

(* [comment removed for export] *)
Ltac dv_proj_cbn :=
  cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k bupd
       sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
       sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
       bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque].

Tactic Notation "enter_cut" uconstr(NEXT) constr(DP) :=
  eapply evt_eq; [ | eapply NEXT ]; only 1: unify_mem; try cut_side DP; only 1: (dv_proj_cbn; st_eq).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac dimg_norm := cbn [di_segs di_got di_stderrp di_crc di_rnums di_dec] in *.

(* [comment removed for export] *)
Ltac hide_all_but_at keep :=
  repeat match goal with
  | H : rw_cells _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : u32arr _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : u8arr _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : bytes_at _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : drest_at _ _ _ _ |- _ => hide H
  | H : blk_at _ _ _ _ |- _ => hide H
  end.

(* [comment removed for export] *)
Ltac gb_next keep Wloc IB :=
  cbv zeta;
  repeat match goal with H : dpure _ _ _ _ _ |- _ => clear H end;
  let m := fresh "m" in let bb := fresh "bb" in let bl := fresh "bl" in let ai := fresh "ai" in
  let til := fresh "til" in let tih := fresh "tih" in
  let DM := fresh "DM" in let FR := fresh "FR" in let ST := fresh "ST" in let MU := fresh "MU" in
  let WM := fresh "WM" in let MI := fresh "MI" in let DP := fresh "DP" in
  let RB := fresh "RB" in let RL := fresh "RL" in let RA := fresh "RA" in let CONS := fresh "CONS" in
  intros m bb bl ai til tih DM FR ST MU WM MI DP RB RL RA CONS; intros;
  (* [comment removed for export] *)
  lazymatch type of DM with dmem _ _ _ _ _ _ ?v' =>
  let R := lazymatch type of IB with (in_bits _ _ <= ?R)%Z => R | (in_bits _ _ < ?R)%Z => R end in
    let IB' := fresh "IB" in
    assert (IB' : (in_bits (dv_b v') (dv_h v') <= R)%Z) by
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
  (* [comment removed for export] *)
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
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lor_100000_10 : forall n, (1 <= n <= 9)%Z -> Z.lor (n * 100000) 10 = (n * 100000 + 10)%Z.
Proof.
  intros n H.
  assert (E : (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9)%Z) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; reflexivity.
Qed.
End ACeilS1.


(* [comment removed for export] *)
Ltac name_masked_reg n u :=
  let v := reg_val n in
  lazymatch v with
  | Z_to_bv 64 (Z.land ?e 255) =>
      let R := fresh "R" u in pose proof (land255_range e) as R;
      let E := fresh "E" u in remember (Z.land e 255) as u eqn:E in R |- *; clear E
  | Z_to_bv 64 (Z.land ?e 1) =>
      let R := fresh "R" u in pose proof (land_mask_range e 1 ltac:(lia)) as R;
      change ((0 <= Z.land e (2^1 - 1) < 2^1)%Z) with ((0 <= Z.land e 1 < 2)%Z) in R;
      let E := fresh "E" u in remember (Z.land e 1) as u eqn:E in R |- *; clear E
  end.

(* [comment removed for export] *)
Ltac ib_close IB :=
  unfold in_bits in IB |- *;
  cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k bupd
       sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
       sh_cbn sh_verb sh_origPtr sh_tPos sh_k0
       bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque] in IB |- *;
  lia.

(* [comment removed for export] *)
Ltac sb_step := step; rewrite ?le1_zxb', ?le1_lit; mem_after_store; zsimp; bz32l.
