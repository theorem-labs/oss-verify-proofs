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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require F_sf_helpers2.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P.F_sf_helpers2.SF_buildtac.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require Import RProgNotJ.

(* [comment removed for export] *)
Definition trunctfdf2_prog (B : Z) : RStep.ptree :=
  PNode 244%Z
  (PNode 120%Z
    (PNode 60%Z
      (PLeaf
          (PJ_Lui_nn 0 12 1048572 4
          (PJ_ShiftImm_ALU_SLL_nnn 4 14 11 1 4
          (PJ_ShiftImm_ALU_SLL_nnn 8 13 11 16 4
          (PJ_OpImm32_nnn 12 12 12 1023 4
          (PJ_ShiftImm_ALU_SRL_nnn 16 14 14 49 4
          (PJ_Op_ALU_ADD_nnn 20 12 14 12 4
          (PJ_OpImm_ALU_ADD_nnn 24 15 0 2045 4
          (PJ_ShiftImm_ALU_SRL_nnn 28 13 13 16 4
          (PJ_Branch_BC_LTU_nnn 32 15 12 52 4
          (PJ_ShiftImm_ALU_SRL_nnn 36 14 10 60 4
          (PJ_ShiftImm_ALU_SLL_nnn 40 13 13 4 4
          (PJ_ShiftImm_ALU_SLL_nnn 44 15 10 4 4
          (PJ_OpImm_ALU_ADD_nnn 48 16 0 1 4
          (PJ_Op_ALU_OR_nnn 52 10 14 13 4
          (PJ_ShiftImm_ALU_SRL_nnn 56 13 15 4 4 nil))))))))))))))))
      (PLeaf
          (PJ_ShiftImm_ALU_SLL_nnn 60 14 16 59 4
          (PJ_OpImm_ALU_ADD_nnn 64 15 14 1 4
          (PJ_OpImm_ALU_ADD_nnn 68 12 12 1 4
          (PJ_Branch_BC_LTU_nnn 72 13 15 88 4
          (PJ_OpImm_ALU_ADD_nnn 76 10 10 1 4
          (PJ_Jal_nn 80 0 92 4
          (PJ_Op_ALU_OR_nnn 84 12 10 13 4
          (PJ_Branch_BC_EQ_nnn 88 12 0 48 4
          (PJ_Lui_nn 92 12 8 4
          (PJ_OpImm32_nnn 96 12 12 4095 4
          (PJ_Branch_BC_NE_nnn 100 14 12 36 4
          (PJ_ShiftImm_ALU_SRL_nnn 104 10 10 60 4
          (PJ_ShiftImm_ALU_SLL_nnn 108 13 13 4 4
          (PJ_OpImm_ALU_ADD_nnn 112 12 0 1 4
          (PJ_ShiftImm_ALU_SLL_nnn 116 12 12 51 4 nil)))))))))))))))))
    (PNode 180%Z
      (PLeaf
          (PJ_Op_ALU_OR_nnn 120 10 10 12 4
          (PJ_Op_ALU_OR_nnn 124 10 10 13 4
          (PJ_OpImm_ALU_ADD_nnn 128 12 0 2047 4
          (PJ_Jal_nn 132 0 56 4
          (PJ_Lui_nn 136 12 4 4
          (PJ_OpImm32_nnn 140 15 12 1022 4
          (PJ_Branch_BC_GEU_nnn 144 15 14 72 4
          (PJ_OpImm_ALU_ADD_nnn 148 10 0 0 4
          (PJ_OpImm_ALU_ADD_nnn 152 12 0 2047 4
          (PJ_Jal_nn 156 0 32 4
          (PJ_Branch_BC_NE_nnn 160 13 14 12 4
          (PJ_OpImm_ALU_AND_nnn 164 13 10 1 4
          (PJ_Op_ALU_ADD_nnn 168 10 13 10 4
          (PJ_ShiftImm_ALU_SRL_nnn 172 13 10 52 4
          (PJ_OpImm_ALU_ADD_nnn 176 14 13 4095 4 nil))))))))))))))))
      (PLeaf
          (PJ_Op_ALU_AND_nnn 180 10 14 10 4
          (PJ_Op_ALU_ADD_nnn 184 12 13 12 4
          (PJ_ShiftImm_ALU_SRL_nnn 188 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 192 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 196 12 12 52 4
          (PJ_Op_ALU_OR_nnn 200 11 12 11 4
          (PJ_Op_ALU_OR_nnn 204 10 11 10 4
          (PJ_Fmv_FMV_F_X_FMT_D_nn 208 10 10 4
          (PJ_Jalr_nnn 212 0 1 0 4
          (PJ_OpImm_ALU_SLTU_nnn 216 15 14 1 4
          (PJ_OpImm32_nnn 220 12 12 3073 4
          (PJ_Op_ALU_XOR_nnn 224 15 15 12 4
          (PJ_Op_ALU_SUB_nnn 228 12 15 14 4
          (PJ_OpImm_ALU_ADD_nnn 232 16 0 112 4
          (PJ_Branch_BC_GE_nnn 236 16 12 16 4
          (PJ_OpImm_ALU_ADD_nnn 240 10 0 0 4 nil)))))))))))))))))))
  (PNode 364%Z
    (PNode 304%Z
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 244 12 0 0 4
          (PJ_Jal_nn 248 0 2097092 4
          (PJ_Op_ALU_SLTU_nnn 252 17 0 14 4
          (PJ_Op_ALU_XOR_nnn 256 14 15 14 4
          (PJ_OpImm_ALU_ADD_nnn 260 15 0 128 4
          (PJ_Op32_ALU_SUB_nnn 264 16 0 12 4
          (PJ_ShiftImm_ALU_SLL_nnn 268 17 17 48 4
          (PJ_Op_ALU_SLTU_nnn 272 14 0 14 4
          (PJ_Op32_ALU_SUB_nnn 276 15 15 12 4
          (PJ_Op_ALU_SLL_nnn 280 5 10 16 4
          (PJ_Op_ALU_OR_nnn 284 13 13 17 4
          (PJ_ShiftImm_ALU_SLL_nnn 288 15 15 32 4
          (PJ_ShiftImm_ALU_SRL_nnn 292 17 15 32 4
          (PJ_OpImm_ALU_ADD_nnn 296 6 17 4032 4
          (PJ_ShiftImm_ALU_SRA_nnn 300 15 6 63 4 nil))))))))))))))))
      (PLeaf
          (PJ_Op_ALU_AND_nnn 304 15 15 5 4
          (PJ_Branch_BC_LT_nnn 308 6 0 12 4
          (PJ_Op_ALU_SLL_nnn 312 16 10 17 4
          (PJ_Jal_nn 316 0 24 4
          (PJ_Op_ALU_SLL_nnn 320 16 13 16 4
          (PJ_OpImm_ALU_XOR_nnn 324 17 17 4095 4
          (PJ_ShiftImm_ALU_SRL_nnn 328 5 10 1 4
          (PJ_Op_ALU_SRL_nnn 332 17 5 17 4
          (PJ_Op_ALU_OR_nnn 336 16 16 17 4
          (PJ_Op_ALU_OR_nnn 340 15 15 16 4
          (PJ_ShiftImm_ALU_SLL_nnn 344 16 12 32 4
          (PJ_Op_ALU_SLTU_nnn 348 17 0 15 4
          (PJ_ShiftImm_ALU_SRL_nnn 352 16 16 32 4
          (PJ_OpImm_ALU_ADD_nnn 356 15 16 4032 4
          (PJ_Op_ALU_AND_nnn 360 14 14 17 4 nil)))))))))))))))))
    (PNode 424%Z
      (PLeaf
          (PJ_Branch_BC_LT_nnn 364 15 0 12 4
          (PJ_Op_ALU_SRL_nnn 368 10 13 16 4
          (PJ_Jal_nn 372 0 24 4
          (PJ_Op_ALU_SRL_nnn 376 10 10 12 4
          (PJ_ShiftImm_ALU_SLL_nnn 380 17 13 1 4
          (PJ_OpImm_ALU_XOR_nnn 384 16 16 4095 4
          (PJ_Op_ALU_SLL_nnn 388 16 17 16 4
          (PJ_Op_ALU_OR_nnn 392 10 10 16 4
          (PJ_Op_ALU_SRL_nnn 396 12 13 12 4
          (PJ_ShiftImm_ALU_SRA_nnn 400 15 15 63 4
          (PJ_ShiftImm_ALU_SRL_nnn 404 16 10 60 4
          (PJ_ShiftImm_ALU_SLL_nnn 408 10 10 4 4
          (PJ_Op_ALU_AND_nnn 412 15 15 12 4
          (PJ_OpImm_ALU_ADD_nnn 416 12 0 1 4
          (PJ_ShiftImm_ALU_SRL_nnn 420 10 10 4 4 nil))))))))))))))))
      (PLeaf
          (PJ_ShiftImm_ALU_SLL_nnn 424 12 12 59 4
          (PJ_ShiftImm_ALU_SLL_nnn 428 15 15 4 4
          (PJ_Op_ALU_OR_nnn 432 13 10 14 4
          (PJ_OpImm_ALU_ADD_nnn 436 14 12 1 4
          (PJ_Op_ALU_OR_nnn 440 10 16 15 4
          (PJ_Branch_BC_LTU_nnn 444 13 14 12 4
          (PJ_OpImm_ALU_ADD_nnn 448 10 10 1 4
          (PJ_Jal_nn 452 0 16 4
          (PJ_Branch_BC_NE_nnn 456 13 12 12 4
          (PJ_OpImm_ALU_AND_nnn 460 12 10 1 4
          (PJ_Op_ALU_ADD_nnn 464 10 12 10 4
          (PJ_ShiftImm_ALU_SRL_nnn 468 12 10 52 4
          (PJ_Op_ALU_SLTU_nnn 472 12 0 12 4
          (PJ_ShiftImm_ALU_SLL_nnn 476 13 12 52 4
          (PJ_Op_ALU_XOR_nnn 480 10 10 13 4
          (PJ_Jal_nn 484 0 2096856 4 nil))))))))))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_trunctfdf2 (IMG : RImg) := trunctfdf2_prog (sym 0x209ec).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_trunctfdf2 : CodeAtT img_segs (sym 0x209ec) (PROGAT_CODE_trunctfdf2 IMG)}.
  Context {RB_trunctfdf2 : RelCode (sym 0x209ec) 488}.
  Collection ImgHyps := IMG CODE_trunctfdf2 RB_trunctfdf2.



Definition trunctfdf2_entry := (sym 0x209ec)%Z.

(* [comment removed for export] *)

Open Scope bv_scope.
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition trunctfdf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             (bvmap_set 10 (Z_to_bv 64 r) F) (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'.

(* [comment removed for export] *)
Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
                                   ONES64 M32 SIGN64 IMPLICIT_HI INF_HI HALF60 DQUIET].


(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI : mem_inv img_segs m.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono img_segs m m := wmono_refl img_segs m.

  Notation a_lo := (bv_unsigned a0). Notation a_hi := (bv_unsigned a1).
  Notation POST r := (trunctfdf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m).
  (* [comment removed for export] *)
  Notation ST pc x5 x6 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 a1 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom img_segs)).

  (* [comment removed for export] *)
  Lemma trunc_Lpack : forall x5 x6 x13 x14 x15 x16 x17 (dE dS r : Z),
    (0 <= dE < 2^64)%Z -> (0 <= dS < 2^64)%Z ->
    r = to_d_pack dE dS a_hi ->
    evt img_segs (POST r) (ST (sym 0x209ec + 188) x5 x6 (Z_to_bv 64 dS) (Z_to_bv 64 dE) x13 x14 x15 x16 x17).
  Proof using MI ImgHyps.
    intros until r. intros RdE RdS HR. subst r. unfold to_d_pack. unfold_sfw.
    do 7 zstep. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma trunc_LN : forall x5 x6 x13 x14 x15 x16 x17 (sig1 exp0 r : Z),
    (0 <= sig1 < 2^64)%Z -> (0 <= exp0 < 2^64)%Z ->
    r = (let '(dE, dS) := to_d_normD sig1 exp0 in to_d_pack dE dS a_hi) ->
    evt img_segs (POST r) (ST (sym 0x209ec + 172) x5 x6 (Z_to_bv 64 sig1) (Z_to_bv 64 exp0) x13 x14 x15 x16 x17).
  Proof using MI ImgHyps.
    intros until r. intros Rs Re HR. subst r. unfold to_d_normD. unfold_sfw.
    zstep. name_reg 13%Z carry.
    zstep. model_reg 14%Z cm1 (Z.land (carry - 1) W64).
    zstep. zstep. model_reg 12%Z dE (Z.land (carry + exp0) W64).
    apply trunc_Lpack; [lia | zrange | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma trunc_L5 : forall x5 x6 x12 x13 x14 x15 x16 x17 (sig1 r : Z),
    (0 <= sig1 < 2^64)%Z ->
    r = (let '(dE, dS) := to_d_subD sig1 in to_d_pack dE dS a_hi) ->
    evt img_segs (POST r) (ST (sym 0x209ec + 468) x5 x6 (Z_to_bv 64 sig1) x12 x13 x14 x15 x16 x17).
  Proof using MI ImgHyps.
    intros until r. intros Rs HR. subst r. unfold to_d_subD. unfold_sfw. rewrite b2z_Zb2z.
    rewrite zb_negb_eqb0 by zrange_nonneg.
    zstep. zstep. name_reg 12%Z carry.
    zstep. zstep. zstep.
    apply trunc_Lpack; [lia | zrange | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma trunc_L4 : forall x5 x6 x16 x17 (srLo shift sigHi1 sticky mM64 r : Z),
    (0 <= srLo < 2^64)%Z -> (0 <= shift < 2^64)%Z -> (0 <= sigHi1 < 2^64)%Z -> (0 <= sticky < 2^64)%Z -> (0 <= mM64 < 2^64)%Z ->
    r = (let '(dE, dS) := to_d_subC srLo sigHi1 shift mM64 sticky in to_d_pack dE dS a_hi) ->
    evt img_segs (POST r) (ST (sym 0x209ec + 396) x5 x6 (Z_to_bv 64 srLo) (Z_to_bv 64 shift) (Z_to_bv 64 sigHi1) (Z_to_bv 64 sticky) (Z_to_bv 64 mM64) x16 x17).
  Proof using MI ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 HR. subst r. unfold to_d_subC. unfold trunc_round. unfold_sfw.
    rewrite (sra63_leb mM64) by lia.
    zstep. name_as_by srHi0 (Z.shiftr sigHi1 (Z.land shift 63))
      (change (inr64 (Z.shiftr sigHi1 (Z.land shift 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
    zstep. rewrite (srai63_word mM64) by lia.
    zstep. zstep. zstep. name_reg 15%Z srHi.
    do 6 zstep. name_reg 13%Z roundBits.
    zstep. name_reg 10%Z sig0.
    zstep. if_cases Kr1; zify_cond Kr1; decide_test1_try (roundBits <? 576460752303423489%Z)%Z; decide_test1_try (roundBits =? 576460752303423488%Z)%Z.
    - (* [comment removed for export] *)
      zstep. if_cases Kr2; zify_cond Kr2; decide_test1 (roundBits =? 576460752303423488%Z)%Z.
      + (* [comment removed for export] *) eapply trunc_L5; [zrange | reflexivity].
      + (* [comment removed for export] *) zstep. zstep. model_reg 10%Z sig1 (Z.land (Z.land sig0 1 + sig0) W64).
        eapply trunc_L5; [zrange | reflexivity].
    - (* [comment removed for export] *) zstep. model_reg 10%Z sig1 (Z.land (sig0 + 1) W64). zstep.
      eapply trunc_L5; [zrange | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma trunc_L3 : forall x5 x6 x17 (slHi shift sigHi1 shNZ slLo r : Z),
    (0 <= slHi < 2^64)%Z -> (0 <= shift < 2^64)%Z -> (0 <= sigHi1 < 2^64)%Z -> (0 <= shNZ < 2^64)%Z -> (0 <= slLo < 2^64)%Z ->
    r = (let '(dE, dS) := to_d_subB a_lo sigHi1 shift shNZ slLo slHi in to_d_pack dE dS a_hi) ->
    evt img_segs (POST r) (ST (sym 0x209ec + 340) x5 x6 a0 (Z_to_bv 64 shift) (Z_to_bv 64 sigHi1) (Z_to_bv 64 shNZ) (Z_to_bv 64 slLo) (Z_to_bv 64 slHi) x17).
  Proof using MI ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 HR. subst r. unfold to_d_subB. unfold_sfw. rewrite b2z_Zb2z.
    pose_word_ranges.
    zstep. name_reg 15%Z stickySrc.
    rewrite (zb_negb_eqb0 stickySrc) by zrange_nonneg.
    zstep. zstep. name_reg 17%Z sticky0.
    zstep. name_reg 16%Z mm.
    zstep. model_reg 15%Z mM64 (Z.land (mm - 64) W64).
    zstep. name_reg 14%Z sticky.
    zstep. if_cases K4; zify_cond K4; decide_test1 ((mM64 ≫ 63)%Z =? 0%Z)%Z.
    - (* [comment removed for export] *)
      zstep. name_as_by sr1 (Z.shiftr a_lo (Z.land shift 63))
        (change (inr64 (Z.shiftr a_lo (Z.land shift 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      do 4 zstep. name_reg 10%Z srLo.
      eapply trunc_L4; [zrange | zrange | zrange | zrange | zrange | reflexivity].
    - (* [comment removed for export] *)
      zstep.
      name_as_by srLo (Z.shiftr sigHi1 (Z.land mm 63))
        (change (inr64 (Z.shiftr sigHi1 (Z.land mm 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      zstep.
      eapply trunc_L4; [zrange | zrange | zrange | zrange | zrange | reflexivity].
  Qed.


  (* [comment removed for export] *)
  Lemma trunc_L0c : forall x5 x6 x12 x15 x16 x17 (sigHi srcExp r : Z),
    (0 <= sigHi < 2^64)%Z -> (0 <= srcExp < 2^64)%Z ->
    r = (let '(dE, dS) := to_d_range a_lo sigHi srcExp in to_d_pack dE dS a_hi) ->
    evt img_segs (POST r) (ST (sym 0x209ec + 136) x5 x6 a0 x12 (Z_to_bv 64 sigHi) (Z_to_bv 64 srcExp) x15 x16 x17).
  Proof using MI ImgHyps.
    intros until r. intros R1 R2 HR. subst r. unfold to_d_range. unfold_sfw. rewrite ?b2z_Zb2z.
    pose_word_ranges.
    do 3 zstep. if_cases K2; zify_cond K2; decide_test1_try (srcExp <=? 17406%Z)%Z; decide_test1_try (srcExp =? 0%Z)%Z.
    - (* [comment removed for export] *)
      zstep. rewrite (ltb1_eqb0 srcExp) by lia. name_reg 15%Z expZ.
      zstep. zstep. name_reg 15%Z k.
      zstep. model_reg 12%Z shift (Z.land (k - srcExp) W64).
      zstep. zstep. if_cases K3; try rewrite bv_lts_lxor in K3; zify_cond K3; decide_test1 (9223372036854775920%Z <? (Z.lxor shift 9223372036854775808))%Z.
      + (* [comment removed for export] *)
        unfold to_d_subA. unfold_sfw. rewrite ?b2z_Zb2z.
        rewrite (zb_negb_eqb0 srcExp) by lia.
        zstep. name_reg 17%Z expNZ.
        zstep. name_reg 14%Z shNZ0. rewrite (zb_negb_eqb0 shNZ0) by zrange_nonneg.
        zstep. zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (0 - shift)).
        name_as_by negsh (sext32 (0 - shift)) (apply sext32_range).
        zstep. zstep. name_reg 14%Z shNZ.
        zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (128 - shift)).
        name_as_by nW (sext32 (128 - shift)) (apply sext32_range).
        zstep. zstep. name_reg 13%Z sigHi1.
        zstep. zstep. name_reg 17%Z n.
        zstep. model_reg 6%Z nM64 (Z.land (n - 64) W64).
        rewrite (sra63_leb nM64) by lia.
        zstep. rewrite (srai63_word nM64) by lia.
        zstep. name_reg 15%Z slLo.
        zstep. if_cases K4; zify_cond K4; decide_test1 ((nM64 ≫ 63)%Z =? 0%Z)%Z.
        * (* [comment removed for export] *)
          zstep. zstep. zstep. zstep.
          name_as_by sr2 (Z.shiftr (Z.shiftr a_lo 1) (Z.land (Z.lxor n W64) 63))
            (change (inr64 (Z.shiftr (Z.shiftr a_lo 1) (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
          zstep. name_reg 16%Z slHi.
          eapply trunc_L3; [zrange | zrange | zrange | zrange | zrange | reflexivity].
        * (* [comment removed for export] *)
          zstep. model_reg 16%Z slHi (Z.land (Z.shiftl a_lo (Z.land n 63)) W64). zstep.
          eapply trunc_L3; [zrange | zrange | zrange | zrange | zrange | reflexivity].
      + (* [comment removed for export] *)
        do 3 zstep. apply trunc_Lpack; [lia | lia | reflexivity].
    - (* [comment removed for export] *)
      do 3 zstep. apply trunc_Lpack; [lia | lia | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma trunc_main : forall (x5 x6 x12 x13 x14 x15 x16 x17 : word) (r : Z),
    r = f128_to_d (a_lo + 2^64 * a_hi) ->
    evt img_segs (POST r) (ST (sym 0x209ec) x5 x6 a0 x12 x13 x14 x15 x16 x17).
  Proof using MI ImgHyps.
    intros until r. intros HR. pose_word_ranges.
    rewrite f128_to_d_split in HR by lia. subst r. unfold to_d_core. unfold_sfw.
    do 5 zstep. name_reg 14%Z srcExp.
    zstep. model_reg 12%Z candM1 (Z.land (srcExp + 18446744073709536255) W64).
    zstep. zstep. name_reg 13%Z sigHi.
    zstep. if_cases K0; zify_cond K0; decide_test1 (2045%Z <? candM1)%Z.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1; decide_test1 ((Z.lor a_lo sigHi) =? 0%Z)%Z.
      + (* [comment removed for export] *)
        eapply trunc_L0c; [zrange | zrange | reflexivity].
      + do 3 zstep. if_cases K3; zify_cond K3; decide_test1 (srcExp =? 32767%Z)%Z.
        * (* [comment removed for export] *) eapply trunc_L0c; [zrange | zrange | reflexivity].
        * (* [comment removed for export] *) do 8 zstep. apply trunc_Lpack; [lia | zrange | reflexivity].
    - (* [comment removed for export] *)
      unfold to_d_normal. unfold trunc_round. unfold_sfw.
      do 5 zstep. name_reg 10%Z sig0.
      zstep. name_reg 13%Z roundBits.
      do 3 zstep. model_reg 12%Z exp0 (Z.land (candM1 + 1) W64).
      zstep. if_cases Kr1; zify_cond Kr1; decide_test1_try (roundBits <? 576460752303423489%Z)%Z; decide_test1_try (roundBits =? 576460752303423488%Z)%Z.
      + (* [comment removed for export] *)
        zstep. if_cases Kr2; zify_cond Kr2; decide_test1 (roundBits =? 576460752303423488%Z)%Z.
        * (* [comment removed for export] *) eapply trunc_LN; [zrange | zrange | reflexivity].
        * (* [comment removed for export] *) zstep. zstep. model_reg 10%Z sig1 (Z.land (Z.land sig0 1 + sig0) W64).
          eapply trunc_LN; [zrange | zrange | reflexivity].
      + (* [comment removed for export] *) zstep. model_reg 10%Z sig1 (Z.land (sig0 + 1) W64). zstep.
        eapply trunc_LN; [zrange | zrange | reflexivity].
  Qed.
End Proofs.

Lemma trunctfdf2_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (trunctfdf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (f128_to_d (bv_unsigned a0 + 2^64 * bv_unsigned a1)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x209ec)) fc None m (seg_rom img_segs)).
Proof. intros until m. intros MI. eapply trunc_main; [exact MI | reflexivity]. Qed.

(* [comment removed for export] *)
Definition trunctfdf2_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (trunctfdf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (f128_to_d (bv_unsigned a0 + 2^64 * bv_unsigned a1)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x209ec)) fc None m (seg_rom img_segs)).
Lemma trunctfdf2_contract_ok : trunctfdf2_contract.
Proof. exact trunctfdf2_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
                                   ONES64 M32 SIGN64 IMPLICIT_HI INF_HI HALF60 DQUIET].
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

(* [comment removed for export] *)
Existing Class trunctfdf2_contract.
