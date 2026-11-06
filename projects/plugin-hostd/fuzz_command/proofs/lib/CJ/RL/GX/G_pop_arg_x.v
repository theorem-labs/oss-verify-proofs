(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/RL/G/G_pop_arg.v, with its module paths changed; 21 of its 87 lines of code are new or changed and 477 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Spec Require Import Prelim SoftFloat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.G Require Import G_pop_arg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.G Require Import GRoTab. From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib Require Import StoreCache. From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib Require Import NElim. From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mem_after_store ::= mem_after_store_cached. Local Ltac addr_eq_tac ::= addr_eq_tac_cached. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM. Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_pop_arg : CodeAtT img_segs (sym 0x19534) (PROGAT_CODE_pop_arg IMG)}.
  Context {RB_pop_arg : RelCode (sym 0x19534) 308}.
  Context {RO_10984 : RoB img_segs (sym 0x10984) ROT_0x10984}.
  Context {RN_B_extenddftf2_19534 : RelNear (sym 0x19534) (sym 0x1af98)}.
  Context {RS_K_10984 : RelSym (sym 0x10984)}.

Definition pop_arg_x_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ARG AP VA : Z) (slots : list word) (i : Z) (slot y : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - 16) (bv_unsigned sp)
    /\ rw_cells img_segs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
    /\ rw_cells img_segs m' ARG [C8 slot; C8 y]
    /\ va_area m' VA slots
    /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

Definition pop_arg_x_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
  rw_cells img_segs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
  va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
  rw_cells img_segs m (bv_unsigned a0) [C8 x; C8 y] ->
  stk img_segs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
  mem_inv img_segs m ->
  a1 = Z_to_bv 64 ty -> (ty = T_ULLONG \/ ty = T_SIZET) ->
  (16 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
  evt img_segs (pop_arg_x_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) (bv_unsigned a2) VA slots i slot y m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x19534)) fc None m (seg_rom img_segs)).

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma pop_arg_x_contract_ok : pop_arg_x_contract.
Proof.
  intros until y. intros APC VAA NTH Hi ARGC ST MI -> TY SPLO A2 A0 SEP1 SEP2 SEP3 SEP4.
  pose_word_ranges.
  pose proof (va_area_bound _ _ _ VAA) as VB. unfold va_area in VAA.
  assert (IL : (Z.to_nat i < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
  set (AP := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 AP) by (unfold AP; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (ARG := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 ARG) by (unfold ARG; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  destruct TY as [-> | ->]; unfold T_ULLONG, T_SIZET.
  all: zstep; zstep; zstep; if_lit; do 7 zstep.
  all: zstep; zstep; zstep.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
  all: zstep; clear RD; zstep; zstep.
  all: replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
  all: finish; intros k Hk; reflexivity.
Qed.

End Img.

Existing Class pop_arg_x_contract.
