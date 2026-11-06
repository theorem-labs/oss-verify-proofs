(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export DecTacFR.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export DecTacFA.      (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.

(* [comment removed for export] *)
Ltac dimg_normF := cbn [di_segs di_got di_stderrp di_crc di_rnums di_dec DI_A0] in *.

(* [comment removed for export] *)
Tactic Notation "gbF_call" uconstr(L) constr(MUL) constr(WML) constr(AOK) constr(DP) constr(FU) :=
  revive_all MUL WML AOK; kq_fold;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    enter_cutF L DP; [ dmodel_cbn; unset_Z; lia | try fuelF .. ]; [ .. | first [clear dependent m | idtac] ]
  end.

(* [comment removed for export] *)
Ltac hide_all_but_atF keep :=
  repeat match goal with
  | H : rw_cells _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : ro_cells _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : u32arr _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : u8arr _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : bytes_at _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : drest_at _ _ _ _ |- _ => hide H
  | H : blk_at _ _ _ _ |- _ => hide H
  end.

Ltac gbF_next_post keep Wloc MD FU DP CONS DM MU :=
  cbn [s_in s_out s_avail_out s_tin s_tout length] in MD, FU, DP, CONS;
  rewrite ?gbst_absorb in MD; rewrite ?gbst_absorb in FU; rewrite ?gbst_absorb in DP;
  cbn [d_bsLive gbst d_set_bsLive d_set_bsBuff d_set_state] in CONS;
  repeat match goal with H1 : (?a < ?b)%nat, H2 : (?b < ?c)%nat |- _ =>
    let H3 := fresh "LTF" in pose proof (Nat.lt_trans a b c H1 H2) as H3; clear H1 H2 end;
  unfold_W14 MU;
  open_dmemF DM; dimg_normF; chunks_normF; chunks_opaqueF;
  hide_all_but_atF keep;
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl Wloc mm) as MUL; pose proof (wmono_refl segs mm) as WML
  end;
  kq_intro;
  match goal with KQ : kq _ (drun _ _ _ _ _) |- _ => rewrite MD in KQ; clear MD end.

Ltac gbF_nextA keep Wloc :=
  gbF_next_pre;
  let F1 := fresh "F" in let bb := fresh "bb" in let bl := fresh "bl" in let inp := fresh "inp" in let tin := fresh "tin" in
  let til := fresh "til" in let tih := fresh "tih" in let m := fresh "m" in
  let MD := fresh "MD" in let FU := fresh "FU" in let LTF := fresh "LTF" in
  let DM := fresh "DM" in let AF := fresh "AF" in let ST := fresh "ST" in let MU := fresh "MU" in
  let WM := fresh "WM" in let MI := fresh "MI" in let DP := fresh "DP" in
  let RB := fresh "RB" in let RL := fresh "RL" in let CONS := fresh "CONS" in
  intros F1 bb bl inp tin til tih m MD FU LTF DM AF ST MU WM MI DP RB RL CONS; intros;
  (let FRL := fresh "FRL" in match goal with H : rw_cells _ m (a_P _) _ |- _ => rename H into FRL end);
  (let FRH := fresh "FRH" in match goal with H : rw_cells _ m (a_P _ + 496)%Z _ |- _ => rename H into FRH end);
  gbF_next_post keep Wloc MD FU DP CONS DM MU.

(* [comment removed for export] *)
Ltac DecTacFA.cut_sideF DP ::=
  lazymatch goal with
  | |- dmem _ _ _ _ _ _ _ => close_dmemF
  | |- fuel_ok _ _ _ => fuelF
  | |- rw_cells _ ?m (a_P ?A) _ => match goal with H : rw_cells _ m (a_P A) _ |- _ => first [ exact H | dmodel_cbn; exact_cells H ] end
  | |- rw_cells _ ?m (a_P ?A + ?k)%Z _ => match goal with H : rw_cells _ m (a_P A + k)%Z _ |- _ => first [ exact H | dmodel_cbn; exact_cells H ] end
  | |- aframe _ ?m => first [ match goal with H : aframe _ m |- _ => exact H end | close_aframe | aframe_revive ]
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- munch _ (a_m0 _) _ => match goal with H : munch _ (a_m0 _) _ |- _ => exact H end
  | |- wmono _ (a_m0 _) _ => match goal with H : wmono _ (a_m0 _) _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  | |- dpureF _ _ _ _ _ _ => solve [ dpureF_solve DP ]
  end.

(* [comment removed for export] *)
Ltac lwbuf r :=
  let v := reg_val r in
  lazymatch v with
  | sx32 (Z_to_bv 64 ?bb) => let w := fresh "wb" in gbword r w bb; [ apply sx32_mod32; unset_Z; lia | ]
  | _ => fail "lwbuf: register does not hold sx32 (Z_to_bv 64 _):" v
  end.

(* [comment removed for export] *)
Tactic Notation "enter_nextF" constr(H) constr(DP) :=
  kq_fold; let F1 := goal_fuel in enter_cutF (H F1 ltac:(lia) _ _ _ JK_) DP.
(* [comment removed for export] *)
Tactic Notation "enter_sameF" constr(H) constr(DP) := kq_fold; enter_cutF (H _ _ _ JK_) DP.
(* [comment removed for export] *)
Ltac ctx_fuel := match goal with FU : fuel_ok ?F1 _ _ |- _ => F1 end.
Tactic Notation "enter_nextK" constr(H) constr(DP) :=
  kq_fold; let F1 := ctx_fuel in enter_cutF (H F1 ltac:(lia) _ _ _ JK_) DP.
(* [comment removed for export] *)
Tactic Notation "enter_retF" constr(R) constr(DP) :=
  kq_fold; first [ enter_cutF (R _ _ _ JK_) DP | enter_cutF (R _ _ _ _ JK_) DP ]; [ ret_nb | ret_post ].

(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
Ltac a_find_reg_sx32 k :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let rec go n :=
      lazymatch n with
      | 0%Z => fail "no register holds sx32 (Z_to_bv 64 _)"
      | _ => let v := a_reg_val R n in
             lazymatch v with
             | sx32 (Z_to_bv 64 _) => k n
             | _ => let n' := eval vm_compute in (n - 1)%Z in go n'
             end
      end in go 31%Z
  end.
Ltac arun_lwbuf :=
  first [ a_find_reg_sx32 ltac:(fun n => lwbuf n)
        | a_pc_is_lit; astep; arun_lwbuf
        | fail 1 "arun_lwbuf: open branch / non-literal pc before a bsBuff reload" ].
Ltac a_find_reg_masked k :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let rec go n :=
      lazymatch n with
      | 0%Z => fail "no register holds a masked value"
      | _ => let v := a_reg_val R n in
             lazymatch v with
             | Z_to_bv 64 (Z.land _ _ / _)%Z => k n
             | Z_to_bv 64 (Z.land _ _) => k n
             | _ => let n' := eval vm_compute in (n - 1)%Z in go n'
             end
      end in go 31%Z
  end.
Ltac arun_gbv n v :=
  first [ a_find_reg_masked ltac:(fun r => gbv r n v)
        | a_pc_is_lit; astep; arun_gbv n v
        | fail 1 "arun_gbv: open branch / non-literal pc before the masked value" ].
