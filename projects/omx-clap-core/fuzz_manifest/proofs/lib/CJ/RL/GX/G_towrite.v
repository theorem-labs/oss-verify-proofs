(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/F_towrite.v, with its module paths changed; 94 of its 117 lines of code are new or changed and 80 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.G Require Import G_fmt_fp_lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc Require Import RProgNotJ.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc Require Import RProgNot.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require Import StoreCache.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require Import NElim.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition towrite_prog (B : Z) : RStep.ptree :=
  PNode 40%Z
    (PLeaf
        (PJ_Load_SZ4_true_nnn 0 12 10 136 4
        (PJ_Load_SZ4_false_nnn 4 11 10 0 4
        (PJ_OpImm_ALU_ADD_nnn 8 13 12 4095 4
        (PJ_Op_ALU_OR_nnn 12 12 13 12 4
        (PJ_OpImm_ALU_AND_nnn 16 13 11 8 4
        (PJ_Store_SZ4_nnn 20 10 12 136 4
        (PJ_Branch_BC_NE_nnn 24 13 0 44 4
        (PJ_Load_SZ8_true_nnn 28 12 10 88 4
        (PJ_Load_SZ8_true_nnn 32 13 10 96 4
        (PJ_Store_SZ8_nnn 36 10 12 56 4 nil)))))))))))
    (PNode 80%Z
      (PLeaf
          (PJ_Op_ALU_ADD_nnn 40 13 12 13 4
          (PJ_Store_SZ8_nnn 44 10 0 8 4
          (PJ_Store_SZ8_nnn 48 10 0 16 4
          (PJ_Store_SZ8_nnn 52 10 13 32 4
          (PJ_Store_SZ8_nnn 56 10 12 40 4
          (PJ_OpImm_ALU_ADD_nnn 60 10 0 0 4
          (PJ_Jalr_nnn 64 0 1 0 4
          (PJ_OpImm_ALU_OR_nnn 68 11 11 32 4
          (PJ_Store_SZ4_nnn 72 10 11 0 4
          (PJ_OpImm_ALU_ADD_nnn 76 10 0 4095 4 nil)))))))))))
      (PLeaf
          (PJ_Jalr_nnn 80 0 1 0 4 nil))).
Definition towrite_size : Z := 84.

Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PROGAT_CODE_towrite (IMG : RImg) := towrite_prog (sym 0x17f40).

Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac if_lit := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_towrite : CodeAtT img_segs (sym 0x17f40) (PROGAT_CODE_towrite IMG)}.
  Context {RB_towrite : RelCode (sym 0x17f40) 84}.

Definition towrite_file (flags : word) (jp : list byte) (rpos rend : word) (jc : list byte) (wend wpos : word)
    (jz : list byte) (wbase : word) (jf : list byte) (buf bufsize : Z) (jl : list byte) (mode : word) (jt : list byte)
    : list cell :=
  [C4 flags; CB 4 jp; C8 rpos; C8 rend; CB 8 jc; C8 wend; C8 wpos; CB 8 jz; C8 wbase; CB 24 jf;
   C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize); CB 32 jl; C4 mode; CB 92 jt].

Definition towrite_x_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (flags : word) (jp : list byte) (rpos rend : word) (jc : list byte) (wend wpos : word)
         (jz : list byte) (wbase : word) (jf : list byte) (buf bufsize : Z) (jl : list byte) (mode : word) (jt : list byte),
    rw_cells img_segs m (bv_unsigned a0) (towrite_file flags jp rpos rend jc wend wpos jz wbase jf buf bufsize jl mode jt) ->
    Z.land (bv_unsigned flags) 8 = 0%Z ->
    (0 <= buf)%Z -> (buf + bufsize < 2^64)%Z -> (0 <= bufsize)%Z ->
    mem_inv img_segs m ->
    evt img_segs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : word -> option byte),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom img_segs)
                 /\ munch [(bv_unsigned a0, bv_unsigned a0 + 232)%Z] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
                 /\ rw_cells img_segs m' (bv_unsigned a0)
                      (towrite_file flags jp (Z_to_bv 64 0) (Z_to_bv 64 0) jc (Z_to_bv 64 (buf + bufsize)) (Z_to_bv 64 buf)
                                    jz (Z_to_bv 64 buf) jf buf bufsize jl mode' jt))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (sym 0x17f40)) fc None m (seg_rom img_segs)).

Theorem towrite_x_proof : towrite_x_stmt.
Proof.
  unfold towrite_x_stmt. intros until jt. intros FC NOWR B0 BHI BS0 MI.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size towrite_file csize Nat.add] in FB.
  set (Fp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl img_segs m) as WM.
  unfold towrite_file in FC.
  assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
  { unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
  do 5 zs. rewrite FL8. zs. zs. if_lit.
  do 10 zs.
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  unfold towrite_file. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.

End Img.
