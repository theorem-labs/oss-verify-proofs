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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_memset G_memcpy G_memchr G_fmt_fp_lib G_trunctfdf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_Scan_iface.G_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_rscan_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_rfile.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_rscan_model F_rscan_shape.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan G_vfscanf.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Import ListNotations.

(* [comment removed for export] *)
Definition sscanf_prog (B got_ssp B_1d22c B_stack_chk_fail : Z) : RStep.ptree :=
  PNode 48%Z
  (PLeaf
      (PJ_OpImm_ALU_ADD_nnn 0 2 2 4016 4
      (PJ_Store_SZ8_nnn 4 2 1 24 4
      (PJ_Store_SZ8_nnn 8 2 8 16 4
      (PJ_Store_SZ8_nnn 12 2 16 64 4
      (PJ_Store_SZ8_nnn 16 2 17 72 4
      (PJ_Auipc_nt 20 16 (hi20 (got_ssp - (B + 20))) 4
      (PJ_Load_SZ8_true_nnt 24 8 16 (lo12 (got_ssp - (B + 20))) 4
      (PJ_Store_SZ8_nnn 28 2 12 32 4
      (PJ_Store_SZ8_nnn 32 2 13 40 4
      (PJ_Store_SZ8_nnn 36 2 14 48 4
      (PJ_Store_SZ8_nnn 40 2 15 56 4
      (PJ_Load_SZ8_true_nnn 44 12 8 0 4 nil)))))))))))))
  (PLeaf
      (PJ_OpImm_ALU_ADD_nnn 48 13 2 32 4
      (PJ_Store_SZ8_nnn 52 2 12 8 4
      (PJ_Store_SZ8_nnn 56 2 13 0 4
      (PJ_OpImm_ALU_ADD_nnn 60 12 2 32 4
      (PJ_Jal_nt 64 1 (jimm21 (B_1d22c - (B + 64))) 4
      (PJ_Load_SZ8_true_nnn 68 11 8 0 4
      (PJ_Load_SZ8_true_nnn 72 12 2 8 4
      (PJ_Branch_BC_NE_nnn 76 11 12 20 4
      (PJ_Load_SZ8_true_nnn 80 1 2 24 4
      (PJ_Load_SZ8_true_nnn 84 8 2 16 4
      (PJ_OpImm_ALU_ADD_nnn 88 2 2 80 4
      (PJ_Jalr_nnn 92 0 1 0 4
      (PJ_Jal_nt 96 1 (jimm21 (B_stack_chk_fail - (B + 96))) 4 nil)))))))))))))).

(* [comment removed for export] *)
Definition sscanf_prog_r1 (B got_ssp K_1d2c8 B_memset B_vfscanf B_stack_chk_fail : Z) : RStep.ptree :=
  PNode 76%Z
  (PNode 36%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 2 2 3808 4
        (PJ_Store_SZ8_nnn 4 2 1 280 4
        (PJ_Store_SZ8_nnn 8 2 8 272 4
        (PJ_Store_SZ8_nnn 12 2 9 264 4
        (PJ_Store_SZ8_nnn 16 2 18 256 4
        (PJ_Store_SZ8_nnn 20 2 19 248 4
        (PJ_OpImm_ALU_ADD_nnn 24 8 12 0 4
        (PJ_OpImm_ALU_ADD_nnn 28 9 11 0 4
        (PJ_OpImm_ALU_ADD_nnn 32 18 10 0 4 nil))))))))))
    (PLeaf
        (PJ_Auipc_nt 36 10 (hi20 (got_ssp - (B + 36))) 4
        (PJ_Load_SZ8_true_nnt 40 19 10 (lo12 (got_ssp - (B + 36))) 4
        (PJ_Load_SZ8_true_nnn 44 10 19 0 4
        (PJ_Store_SZ8_nnn 48 2 10 240 4
        (PJ_OpImm_ALU_ADD_nnn 52 10 2 8 4
        (PJ_OpImm_ALU_ADD_nnn 56 12 0 232 4
        (PJ_OpImm_ALU_ADD_nnn 60 11 0 0 4
        (PJ_Jal_nt 64 1 (jimm21 (B_memset - (B + 64))) 4
        (PJ_Auipc_nt 68 10 (hi20 (K_1d2c8 - (B + 68))) 4
        (PJ_OpImm_ALU_ADD_nnn 72 11 0 4095 4 nil))))))))))))
  (PNode 116%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnt 76 10 10 (lo12 (K_1d2c8 - (B + 68))) 4
        (PJ_Store_SZ8_nnn 80 2 10 72 4
        (PJ_Store_SZ8_nnn 84 2 18 96 4
        (PJ_Store_SZ4_nnn 88 2 11 148 4
        (PJ_Store_SZ8_nnn 92 2 18 160 4
        (PJ_OpImm_ALU_ADD_nnn 96 10 2 8 4
        (PJ_OpImm_ALU_ADD_nnn 100 11 9 0 4
        (PJ_OpImm_ALU_ADD_nnn 104 12 8 0 4
        (PJ_Jal_nt 108 1 (jimm21 (B_vfscanf - (B + 108))) 4
        (PJ_Load_SZ8_true_nnn 112 11 19 0 4 nil)))))))))))
    (PLeaf
        (PJ_Load_SZ8_true_nnn 116 12 2 240 4
        (PJ_Branch_BC_NE_nnn 120 11 12 32 4
        (PJ_Load_SZ8_true_nnn 124 1 2 280 4
        (PJ_Load_SZ8_true_nnn 128 8 2 272 4
        (PJ_Load_SZ8_true_nnn 132 9 2 264 4
        (PJ_Load_SZ8_true_nnn 136 18 2 256 4
        (PJ_Load_SZ8_true_nnn 140 19 2 248 4
        (PJ_OpImm_ALU_ADD_nnn 144 2 2 288 4
        (PJ_Jalr_nnn 148 0 1 0 4
        (PJ_Jal_nt 152 1 (jimm21 (B_stack_chk_fail - (B + 152))) 4 nil)))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_sscanf (IMG : RImg) := sscanf_prog (sym 0x18328) (sym 0x22e18) (sym 0x1d22c) (sym 0x15f04).
Definition PROGAT_CODE_sscanf_1 (IMG : RImg) := sscanf_prog_r1 (sym 0x1d22c) (sym 0x22e18) (sym 0x1d2c8) (sym 0x21738) (sym 0x1d36c) (sym 0x15f04).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_sscanf : CodeAtT img_segs (sym 0x18328) (PROGAT_CODE_sscanf IMG)}.
  Context {RB_sscanf : RelCode (sym 0x18328) 100}.
  Context {CODE_sscanf_1 : CodeAtT img_segs (sym 0x1d22c) (PROGAT_CODE_sscanf_1 IMG)}.
  Context {RB_sscanf_1 : RelCode (sym 0x1d22c) 156}.
  Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing). Local Notation GLRS a := (RelSym (sym a)) (only parsing). Context {RN_B_1d22c_18328 : GLRN 0x18328 0x1d22c}.
  Context {RN_B_stack_chk_fail_18328 : GLRN 0x18328 0x15f04}.
  Context {RN_B_memset_1d22c : GLRN 0x1d22c 0x21738}.
  Context {RN_B_vfscanf_1d22c : GLRN 0x1d22c 0x1d36c}.
  Context {RN_B_stack_chk_fail_1d22c : GLRN 0x1d22c 0x15f04}.
  Context {RS_got_ssp : GLRS 0x22e18}.
  Context {RS_K_1d2c8 : GLRS 0x1d2c8}.
  Context {RS_34288 : GLRS 0x34288}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {RS_341f8 : GLRS 0x341f8}.
  Let rp_341f8 : (0 <= sym 0x341f8 /\ sym 0x341f8 < 2^30)%Z := @rel_sym_pf _ RS_341f8.
  Context {RS_35000 : GLRS 0x35000}.
  Let rp_35000 : (0 <= sym 0x35000 /\ sym 0x35000 < 2^30)%Z := @rel_sym_pf _ RS_35000.
  Context {RS_102a8 : GLRS 0x102a8}.
  Let rp_102a8 : (0 <= sym 0x102a8 /\ sym 0x102a8 < 2^30)%Z := @rel_sym_pf _ RS_102a8.
  Context {SPEC_memset : memset_contract}.
  Context {SPEC_L_VA : G_vfscanf.L_VA_c}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 172 <= sym 0x341f8)%Z}.
  Let rl0_0 : (sym 0x22e18 + 172 <= sym 0x341f8)%Z := @zfact_pf _ RL0_0.
  Context {RL0_1 : ZFact (sym 0x341f8 + 0 <= sym 0x34288)%Z}.
  Let rl0_1 : (sym 0x341f8 + 0 <= sym 0x34288)%Z := @zfact_pf _ RL0_1.
  Context {RL0_2 : ZFact (sym 0x34288 + 8 <= sym 0x35000)%Z}.
  Let rl0_2 : (sym 0x34288 + 8 <= sym 0x35000)%Z := @zfact_pf _ RL0_2.
  Context {RQ_22e18 : ZFact (0x20000 <= sym 0x22e18 < 2^30)%Z}.
  Let rq_22e18 : (0x20000 <= sym 0x22e18 < 2^30)%Z := @zfact_pf _ RQ_22e18.
  Collection ImgHyps := IMG CODE_sscanf RB_sscanf CODE_sscanf_1 RB_sscanf_1 RN_B_1d22c_18328 RN_B_stack_chk_fail_18328 RN_B_memset_1d22c RN_B_vfscanf_1d22c RN_B_stack_chk_fail_1d22c RS_got_ssp RS_K_1d2c8 RS_34288 rp_34288 RS_341f8 rp_341f8 RS_35000 rp_35000 RS_102a8 rp_102a8 SPEC_memset SPEC_L_VA RL0_0 rl0_0 RL0_1 rl0_1 RL0_2 rl0_2 RQ_22e18 rq_22e18.


Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
Open Scope bv_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).
Tactic Notation "callx" tactic3(tac) := callw tac; try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end).

(* [comment removed for export] *)
  (* [comment removed for export] *)
Local Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Local Ltac br10 K := brf K; [ exfalso; lia | ].
Lemma memset_callZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q D C N : Z) (junk : list byte),
  rw_cells img_segs m D [CB (Z.to_nat N) junk] ->
  mem_inv img_segs m ->
  (0 <= q < 2^64)%Z -> (0 <= D < 2^64)%Z -> (0 <= C < 2^64)%Z -> (0 <= N < 2^64)%Z ->
  evt img_segs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(D, D + N)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ rw_cells img_segs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))])
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21738)) fc None m (seg_rom img_segs)).
Proof.
  intros until junk. intros DST MI Hq HD HC HN.
  assert (Ed : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (Ec : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (SPEC_memset ra (Z_to_bv 64 q)); [|exact MI]. rewrite Ed, En. exact DST. }
  intros ms' P. unfold memset_post in P. rewrite !Ed, !Ec, !En in P. exact P.
Qed.

Lemma find_segment_none_of_bounds : forall (segs : list Segment) (l : list (Z * Z)) z n,
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z segs = l ->
  Forall (fun bt => ~ (fst bt <= z /\ z + n <= snd bt)%Z) l ->
  find_segment segs z n = None.
Proof.
  induction segs as [|s segs IH]; intros l z n E F; [reflexivity|].
  destruct l as [|[b t] l]; [discriminate|]. cbn [map] in E. injection E as El Et Eb.
  inversion F as [|bt l' Hbt Hl]; subst. cbn [fst snd] in Hbt.
  cbn [find_segment].
  destruct (Z.leb_spec0 (Z.of_N (seg_base s)) z); destruct (Z.leb_spec0 (z + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb];
    try (exfalso; apply Hbt; split; assumption).
  all: eapply IH; [reflexivity | exact Hl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Context {ASM_ref_find_segment_none : ZFact (forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ (sym 0x35000) <= z)%Z ->
  find_segment img_segs z n = None)}.
Let ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ (sym 0x35000) <= z)%Z ->
  find_segment img_segs z n = None := @zfact_pf _ ASM_ref_find_segment_none.

(* [comment removed for export] *)
Lemma stk_hi_wmono : forall (m m' : mem) lo hi, stk img_segs m lo hi -> wmono img_segs m m' -> ((sym 0x35000) <= lo)%Z -> stk img_segs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) WM Hlo. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw _]. pose proof (WM _ Hw) as Hw'. split; [exact Hw'|].
  unfold wview in Hw'. unfold mrd. destruct (m' (wa a)) as [b|]; [exists b; reflexivity|].
  rewrite ref_find_segment_none in Hw'; [congruence| lia | rewrite wa_unsigned by lia; lia].
Qed.

Definition hideP (P : Prop) := P.

Theorem rsscanf_lg_proof : rsscanf_lg_stmt.
Proof.
  unfold rsscanf_lg_stmt. intros until ev. intros BY BYT Htxt Hpre Hlen AL L256 PDC HS ST LO GT SPH HT T1 HPD HPD2 SEPD [SSP1 SSP2] ERR MI FRM Htp Ha0 Ha1 Ha2.
  idtac. idtac .
  unfold RSSCANF_DEPTH, RGLOBALS_TOP, RATP, RFMT_LG in *. unfold G_Scan_iface.RERRNO in *. unfold got_ssp, ssp_guard in SSP1, SSP2.
  subst tp a0 a1 a2.
  pose_word_ranges.
  assert (LT : length (map (Z_to_bv 8) txt) = length txt) by apply length_map.
  assert (Hp : (0 <= zlength pre < zlength txt)%Z) by (subst txt; unfold zlength; rewrite length_app; cbn; lia).
  unfold zlength in L256, SEPD, AL, Hp.
  pose proof (munch_refl [(lo, bv_unsigned sp); (PD, PD + 8); ((sym 0x341f8 - 164), (sym 0x341f8 - 164) + 4)]%Z m) as MU. pose proof (wmono_refl img_segs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ PDC) as BPD. cbn [cells_size csize Nat.add] in BPD.
  unfold RSSCANF.
  (* [comment removed for export] *)
  zs. carve_frame 80%nat ST. rename FR into FRS.
  do 16 zs.
  (* [comment removed for export] *)
  zs. carve_frame 48%nat ST. rename FR into FRV.
  carve_frame 232%nat ST. rename FR into FILE.
  destruct (stk_split _ _ _ (bv_unsigned sp + -368)%Z _ ST ltac:(lia)) as [ST8 STJ]. clear ST. rename ST8 into ST.
  do 8 zs.
  zs. zs. zs. zs.
  zs. zs. zs. zs. callx (eapply memset_callZ; [exact FILE | assumption | lia | lia | lia | lia]).
  match goal with H : rw_cells _ _ _ [CB (Z.to_nat 232) _] |- _ =>
    change (Z.to_nat 232) with 232%nat in H; change (0 mod 256)%Z with 0%Z in H;
    apply file_cells_zero in H; rename H into FC end.
  (* [comment removed for export] *)
  zs. zs. zs. zs. zs. zs. zs.
  replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 M64) in FC by (apply Z_to_bv_eqm; reflexivity).
  change (repeat (Z_to_bv 8 0) 4) with zero4 in FC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FCv : rw_cells img_segs mm (bv_unsigned sp + -368 + 8) (ss_cells T 0 0 w0 T 0 w0 w0))
      by (unfold ss_cells, w0; unfold STRING_READ; replace (bv_unsigned sp + -368 + 8)%Z with (bv_unsigned sp + -360)%Z by lia; exact FC);
    pose proof (proj2 (proj1 (G_fwritex.rw_cells_app img_segs mm _ [_; _; _; _] _) FRS)) as FRS2; cbn [cells_size csize Nat.add app] in FRS2;
    pose proof (proj1 (proj1 (G_fwritex.rw_cells_app img_segs mm _ [_] _) FRS2)) as APC; clear FRS2;
    replace (bv_unsigned sp + -80 + Z.of_nat 32)%Z with (bv_unsigned sp + -368 + 320)%Z in APC by lia end.
  clear FC.
  (* [comment removed for export] *)
  zs. zs. zs. zs.
  replace (Z_to_bv 64 (bv_unsigned sp + -360)) with (Z_to_bv 64 (bv_unsigned sp + -368 + 8)) by (f_equal; lia).
  replace (Z_to_bv 64 (bv_unsigned sp + -48)) with (Z_to_bv 64 (bv_unsigned sp + -368 + 320)) by (f_equal; lia).
  match goal with H : stk _ ?mm lo _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 9136)%Z _ H ltac:(lia)) as [STlo SThi]; clear H end.
  match goal with H : stk _ ?mm (bv_unsigned sp + -368)%Z _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of H with ?P => change P with (hideP P) in H end; rename H into STJ end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  pose proof (wmono_refl img_segs mm) as WMJ;
  pose proof (SPEC_L_VA (Z_to_bv 64 (sym 0x1d22c + 112)) (bv_unsigned sp + -368)%Z gp (Z_to_bv 64 (bv_unsigned sp + -368 + 320)) (Z_to_bv 64 (sym 0x102a8)) (Z_to_bv 64 T) (Z_to_bv 64 (sym 0x34288)) s4 s5 s6 s7 s8 s9 s10 s11 F fc mm
                T txt pre post canary PD djunk r res HS Htxt Hpre BYT Hlen ltac:(unfold zlength; lia) ltac:(unfold zlength; lia) ltac:(lia) T1
                ltac:(unfold G_vfscanf.VF_DEPTH; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold zlength; lia) FRM) as LV end.
  cbv zeta in LV. unfold G_vfscanf.VF_DEPTH, G_vfscanf.vf_post, G_vfscanf.Wvf, G_vfscanf.VF_DEPTH, G_vfscanf.FokR, G_vfscanf.resw, G_floatscan_common.RERRNO, G_floatscan_common.RATP, G_vfscanf.VFSCANF, G_vfscanf.RFMT in LV.
  callx (eapply LV; [ exact SThi | exact MI0 | exact FCv | exact APC | exact PDC | exact BY | split; [exact SSP1 | exact SSP2] | exact ERR ]).
  clear LV.
  match goal with H : ssp_cells _ canary |- _ => destruct H as [SSP3 SSP4]; unfold got_ssp, ssp_guard in SSP3, SSP4 end.
  match goal with H : wmono _ ?m1 ?m2, H2 : hideP (stk _ ?m1 _ _) |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
    unfold hideP in H2; apply (stk_hi_wmono _ _ _ _ H2) in H; [clear H2; rename H into STJ2 | lia] end.
  (* [comment removed for export] *)
  zs. zs. zs. br10 K1.
  zs. zs. zs. zs. zs. zs. zs.
  (* [comment removed for export] *)
  zs. zs. zs. br10 K2.
  zs. zs. zs. zs.
  match goal with H : stk _ ?m' lo _, H2 : mem_inv _ ?m' |- evt _ _ (MS _ _ _ _ _ ?m' _) => rename H into ST9; rename H2 into MI9 end.
  pose proof (stk_merge _ _ _ _ _ ST9 ST ltac:(lia)) as ST10. clear ST9 ST.
  pose proof (stk_merge _ _ _ _ _ ST10 STJ2 ltac:(lia)) as ST11. clear ST10 STJ2.
  replace (bv_unsigned sp + -368 + 8)%Z with (bv_unsigned sp + -360)%Z in PC0 by lia.
  release_frame PC0 ST11 (bv_unsigned sp + -128)%Z.
  release_frame FRV ST11 (bv_unsigned sp + -80)%Z.
  release_frame FRS ST11 (bv_unsigned sp).
  apply evt_done. unfold rsscanf_lg_post.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI9|]. split; [exact POST|].
  split; [exact PC5|].
  split; [exact ST11|]. split; [exact PC1|]. split; [exact BY|]. split; [split; [exact SSP3 | exact SSP4]|].
  exact PC4.
Qed.

(* [comment removed for export] *)
Definition rsscanf_lg_proof_c : Prop := rsscanf_lg_stmt.
Lemma rsscanf_lg_proof_c_ok : rsscanf_lg_proof_c.
Proof. exact rsscanf_lg_proof. Qed.


End Img.
(* [comment removed for export] *)
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).
Tactic Notation "callx" tactic3(tac) := callw tac; try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end).

(* [comment removed for export] *)
Existing Class rsscanf_lg_proof_c.
