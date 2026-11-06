(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib Require Import Tac.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.G Require Import G_memchr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition strnlen_prog (B B_memchr : Z) : RStep.ptree :=
  PNode 32%Z
  (PLeaf
      (PJ_OpImm_ALU_ADD_nnn 0 2 2 4064 4
      (PJ_Store_SZ8_nnn 4 2 1 24 4
      (PJ_Store_SZ8_nnn 8 2 8 16 4
      (PJ_Store_SZ8_nnn 12 2 9 8 4
      (PJ_OpImm_ALU_ADD_nnn 16 8 11 0 4
      (PJ_OpImm_ALU_ADD_nnn 20 9 10 0 4
      (PJ_OpImm_ALU_ADD_nnn 24 11 0 0 4
      (PJ_OpImm_ALU_ADD_nnn 28 12 8 0 4 nil)))))))))
  (PLeaf
      (PJ_Jal_nt 32 1 (jimm21 (B_memchr - (B + 32))) 4
      (PJ_Branch_BC_EQ_nnn 36 10 0 8 4
      (PJ_Op_ALU_SUB_nnn 40 8 10 9 4
      (PJ_OpImm_ALU_ADD_nnn 44 10 8 0 4
      (PJ_Load_SZ8_true_nnn 48 1 2 24 4
      (PJ_Load_SZ8_true_nnn 52 8 2 16 4
      (PJ_Load_SZ8_true_nnn 56 9 2 8 4
      (PJ_OpImm_ALU_ADD_nnn 60 2 2 32 4
      (PJ_Jalr_nnn 64 0 1 0 4 nil)))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_strnlen (IMG : RImg) := strnlen_prog (sym 0x21920) (sym 0x21268).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_strnlen : CodeAtT img_segs (sym 0x21920) (PROGAT_CODE_strnlen IMG)}.
  Context {RB_strnlen : RelCode (sym 0x21920) 68}.
  Context {RN_B_memchr_21920 : RelNear (sym 0x21920) (sym 0x21268)}.
  Context {SPEC_memchr : memchr_contract}.
  Collection ImgHyps := IMG CODE_strnlen RB_strnlen RN_B_memchr_21920 SPEC_memchr.



Definition strnlen_entry := (sym 0x21920)%Z.

(* [comment removed for export] *)
Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' lo (bv_unsigned sp)
    /\ bytes_at img_segs m' (bv_unsigned a0) buf.

Lemma strnlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  stk img_segs m lo (bv_unsigned sp) ->
  bytes_at img_segs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) 0 (bv_unsigned a1) buf ->
  mem_inv img_segs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a0)%Z ->
  evt img_segs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21920)) fc None m (seg_rom img_segs)).
Proof.
  intros until lo. intros ST BUF OK MI LO SEP A0.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl img_segs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ BUF) as AB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST.
  do 9 zstep.
  call SPEC_memchr.
  1:{ exact BUF. }
  1:{ rewrite unsigned_lit by lia. exact OK. }
  1:{ assumption. }
  rewrite unsigned_lit by lia. change (0 mod 256)%Z with 0%Z.
  unfold memchr_res.
  destruct (find_byte 0 (firstn (Z.to_nat (bv_unsigned a1)) buf)) as [i|] eqn:FB.
  - pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite firstn_length in Hl.
    zstep. if_cases K; zify_cond K. { exfalso. lia. }
    do 7 zstep.
    replace (bv_unsigned a0 + Z.of_nat i - bv_unsigned a0)%Z with (strnlen_res (bv_unsigned a1) buf)
      by (unfold strnlen_res; rewrite FB; lia).
    release_frame FR ST (bv_unsigned sp). finish.
  - zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    do 6 zstep.
    lazymatch goal with |- evt _ ?Q _ => set (P := Q) end.
    replace a1 with (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
      by (unfold strnlen_res; rewrite FB; apply Z_to_bv_bv_unsigned).
    release_frame FR ST (bv_unsigned sp). finish.
Qed.

(* [comment removed for export] *)
Definition strnlen_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  stk img_segs m lo (bv_unsigned sp) ->
  bytes_at img_segs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) 0 (bv_unsigned a1) buf ->
  mem_inv img_segs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a0)%Z ->
  evt img_segs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21920)) fc None m (seg_rom img_segs)).
Lemma strnlen_contract_ok : strnlen_contract.
Proof. exact strnlen_spec. Qed.


End Img.

(* [comment removed for export] *)
Existing Class strnlen_contract.
