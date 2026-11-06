(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OSSVerify.Proofs.openssl.ct.lib.CtP Require Import Layout Lib_kit F_memset.
From OSSVerify.Proofs.openssl.ct.lib.CtBnP Require Import BnKit.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApWalkTac.
From OSSVerify.Proofs.openssl.ct.lib.CtPrnP Require Import MagicDiv.
From OSSVerify.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeMagic W_posix_to_tm.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.
(* [comment removed for export] *)
Tactic Notation "zrun" integer(n) := do n (zstep; try brc).

Definition OPENSSL_GMTIME_STACK : Z := 64.      (* [comment removed for export] *)

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gmtime_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) (tv D : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if p2tm_ret tv =? 0 then 0 else D)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctpsegs)
    /\ munch [(bv_unsigned sp - OPENSSL_GMTIME_STACK, bv_unsigned sp); (D, D + 56)]%Z m m' /\ wmono ctpsegs m m' /\ mem_inv ctpsegs m'
    /\ stk ctpsegs m' lo (bv_unsigned sp)
    /\ rw_cells ctpsegs m' D (p2tm_cells tv).

Lemma OPENSSL_gmtime_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo TP tv D : Z) (junk : list byte),
  stk ctpsegs m lo (bv_unsigned sp) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - OPENSSL_GMTIME_STACK)%Z ->
  (bv_unsigned sp <= D)%Z -> (D + 56 <= 2^64)%Z -> rw_cells ctpsegs m D [CB 56%nat junk] ->
  (bv_unsigned sp <= TP)%Z -> (TP + 8 <= D \/ D + 56 <= TP)%Z -> ro_cells ctpsegs m TP [C8 (Z_to_bv 64 tv)] ->
  (- 2^63 <= tv < 2^63)%Z -> a0 = Z_to_bv 64 TP -> a1 = Z_to_bv 64 D ->
  evt ctpsegs (gmtime_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m tv D)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OPENSSL_GMTIME) fc None m (seg_rom ctpsegs)).
Proof.
  intros until junk. intros ST MI GLO LO HD HD2 OUT HTP HTP2 TMR Htv -> ->. unfold GLOBALS_TOP in GLO. unfold OPENSSL_GMTIME, OPENSSL_GMTIME_STACK in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (D, D + 56)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPT : TP + 8 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= TP) by lia.
  carve_frame 32%nat ST. do 5 zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  name_mem m1. eapply evt_cut.
  { eapply (OPENSSL_posix_to_tm_spec _ (Z_to_bv 64 (bv_unsigned sp + -32))) with (lo := lo) (t := tv) (D := D) (junk := junk);
      rewrite ?ESP; [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| lia| exact OUT| lia| reflexivity| reflexivity]. }
  post_call_esp ESP m1. rename PC into ST. rewrite ESP in ST. name_mem m2. rename MI0 into MI.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  setreg 10%Z (Z_to_bv 64 (if p2tm_ret tv =? 0 then 0 else D))
    ltac:(f_equal; unfold p2tm_ret; destruct (utc_from_posix tv); cbn [Z.eqb];
          [ match goal with |- _ = Z.land ?c D => let v := eval vm_compute in c in change c with v end;
            rewrite Z.land_comm, land64; symmetry; apply Z.mod_small; lia
          | match goal with |- _ = Z.land ?c D => let v := eval vm_compute in c in change c with v end; rewrite Z.land_0_l; reflexivity ]).
  (* [comment removed for export] *)
  do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold gmtime_post.
  do 14 eexists. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.
End WithCeiling.
