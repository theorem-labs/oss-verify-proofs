(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Gt_shgetc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgNot.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgNotJ.
Module G_shgetc_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.Gt_shgetc. Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgNot. Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.   
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache. Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgNotJ.

(* [comment removed for export] *)
Definition shgetc_A_prog (B : Z) : RStep.ptree :=
  PNode 72%Z
  (PNode 36%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 2 2 4080 4
        (PJ_Store_SZ8_nnn 4 2 1 8 4
        (PJ_Store_SZ8_nnn 8 2 8 0 4
        (PJ_OpImm_ALU_ADD_nnn 12 8 10 0 4
        (PJ_Load_SZ4_true_nnn 16 10 10 136 4
        (PJ_Load_SZ8_true_nnn 20 11 8 40 4
        (PJ_Load_SZ8_true_nnn 24 12 8 56 4
        (PJ_OpImm_ALU_ADD_nnn 28 13 10 4095 4
        (PJ_Op_ALU_OR_nnn 32 10 13 10 4 nil))))))))))
    (PLeaf
        (PJ_Store_SZ4_nnn 36 8 10 136 4
        (PJ_Branch_BC_EQ_nnn 40 11 12 24 4
        (PJ_Load_SZ8_true_nnn 44 13 8 72 4
        (PJ_OpImm_ALU_ADD_nnn 48 10 8 0 4
        (PJ_OpImm_ALU_ADD_nnn 52 11 0 0 4
        (PJ_OpImm_ALU_ADD_nnn 56 12 0 0 4
        (PJ_Jalr_nnn 60 1 13 0 4
        (PJ_Load_SZ4_false_nnn 64 10 8 0 4
        (PJ_OpImm_ALU_AND_nnn 68 11 10 4 4 nil)))))))))))
  (PNode 108%Z
    (PLeaf
        (PJ_Store_SZ8_nnn 72 8 0 32 4
        (PJ_Store_SZ8_nnn 76 8 0 40 4
        (PJ_Store_SZ8_nnn 80 8 0 56 4
        (PJ_Branch_BC_NE_nnn 84 11 0 36 4
        (PJ_Load_SZ8_true_nnn 88 11 8 88 4
        (PJ_Load_SZ8_true_nnn 92 12 8 96 4
        (PJ_ShiftImm_ALU_SLL_nnn 96 10 10 59 4
        (PJ_Op_ALU_ADD_nnn 100 11 11 12 4
        (PJ_Store_SZ8_nnn 104 8 11 8 4 nil))))))))))
    (PLeaf
        (PJ_Store_SZ8_nnn 108 8 11 16 4
        (PJ_ShiftImm_ALU_SRA_nnn 112 10 10 63 4
        (PJ_Jal_nn 116 0 16 4
        (PJ_OpImm_ALU_OR_nnn 120 10 10 32 4
        (PJ_Store_SZ4_nnn 124 8 10 0 4
        (PJ_OpImm_ALU_ADD_nnn 128 10 0 4095 4
        (PJ_Load_SZ8_true_nnn 132 1 2 8 4
        (PJ_Load_SZ8_true_nnn 136 8 2 0 4
        (PJ_OpImm_ALU_ADD_nnn 140 2 2 16 4
        (PJ_Jalr_nnn 144 0 1 0 4 nil)))))))))))).
(* [comment removed for export] *)
Definition shgetc_A_prog_1 (B : Z) : RStep.ptree :=
  PLeaf
    (PJ_Load_SZ8_true_nnn 0 13 10 8 4
    (PJ_Load_SZ8_true_nnn 4 12 10 16 4
    (PJ_Load_SZ8_true_nnn 8 14 10 88 4
    (PJ_Op_ALU_SLTU_nnn 12 15 0 11 4
    (PJ_Op_ALU_SUB_nnn 16 16 12 13 4
    (PJ_Op_ALU_SLT_nnn 20 16 11 16 4
    (PJ_Op_ALU_AND_nnn 24 15 15 16 4
    (PJ_Op_ALU_SUB_nnn 28 14 14 13 4
    (PJ_Store_SZ8_nnn 32 10 11 192 4
    (PJ_Store_SZ8_nnn 36 10 14 200 4
    (PJ_Branch_BC_EQ_nnn 40 15 0 8 4
    (PJ_Op_ALU_ADD_nnn 44 12 13 11 4
    (PJ_Store_SZ8_nnn 48 10 12 184 4
    (PJ_Jalr_nnn 52 0 1 0 4 nil)))))))))))))).

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
Definition PROGAT_CODE_shgetc_A (IMG : RImg) := shgetc_A_prog (sym 0x1deac).
Definition PROGAT_CODE_shgetc_A_1 (IMG : RImg) := shgetc_A_prog_1 (sym 0x1df40).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_shgetc_A : CodeAtT img_segs (sym 0x1deac) (PROGAT_CODE_shgetc_A IMG)}.
  Context {RB_shgetc_A : RelCode (sym 0x1deac) 148}.
  Context {CODE_shgetc_A_1 : CodeAtT img_segs (sym 0x1df40) (PROGAT_CODE_shgetc_A_1 IMG)}.
  Context {RB_shgetc_A_1 : RelCode (sym 0x1df40) 56}.
  Context {RS_22e18 : RelSym (sym 0x22e18)}.
  Let rp_22e18 : (0 <= sym 0x22e18 /\ sym 0x22e18 < 2^30)%Z := @rel_sym_pf _ RS_22e18.
  Context {RS_34288 : RelSym (sym 0x34288)}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {RS_1df78 : RelSym (sym 0x1df78)}.
  Let rp_1df78 : (0 <= sym 0x1df78 /\ sym 0x1df78 < 2^30)%Z := @rel_sym_pf _ RS_1df78.
  Context {RS_1e040 : RelSym (sym 0x1e040)}.
  Let rp_1e040 : (0 <= sym 0x1e040 /\ sym 0x1e040 < 2^30)%Z := @rel_sym_pf _ RS_1e040.
  Context {RS_1d2c8 : RelSym (sym 0x1d2c8)}.
  Let rp_1d2c8 : (0 <= sym 0x1d2c8 /\ sym 0x1d2c8 < 2^30)%Z := @rel_sym_pf _ RS_1d2c8.
  Collection ImgHyps := IMG CODE_shgetc_A RB_shgetc_A CODE_shgetc_A_1 RB_shgetc_A_1 RS_22e18 rp_22e18 RS_34288 rp_34288 RS_1df78 rp_1df78 RS_1e040 rp_1e040 RS_1d2c8 rp_1d2c8.


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
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].

(* [comment removed for export] *)

Definition SHLIM : Z := (sym 0x1df40).
Definition SHGETC : Z := (sym 0x1df78).
Definition UFLOW : Z := (sym 0x1e040).
Definition TOREAD : Z := (sym 0x1deac).
Definition STRING_READ : Z := (sym 0x1d2c8).

(* [comment removed for export] *)
Definition got_ssp := (sym 0x22e18)%Z.
Definition ssp_guard := (sym 0x34288)%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells img_segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells img_segs m ssp_guard [C8 canary].

(* [comment removed for export] *)

Definition M64 : Z := 18446744073709551615.

(* [comment removed for export] *)
Definition rf_rend (T p : Z) (w : bool) (f : shfile) : Z :=
  if sh_stdio f then (if w then T + p else T) else M64.

Definition rf_cells (T p : Z) (w : bool) (f : shfile) (J : rfj) : list cell :=
  let rend := rf_rend T p w f in
  [C4 (j_flags J); CB 4 (j_pad0 J); C8 (Z_to_bv 64 (T + sh_rpos f)); C8 (Z_to_bv 64 rend);
   C8 (j_close J); C8 (j_wend J); C8 (j_wpos J); C8 (j_mbz1 J); C8 (j_wbase J); C8 (j_read J); C8 (j_write J); C8 (j_seek J);
   C8 (Z_to_bv 64 T); C8 (j_bufsize J); C8 (j_prev J); C8 (j_next J); C4 (j_fd J); C4 (j_ppid J); C8 (j_lockcount J);
   C4 (j_mode J); C4 (j_lock J); C4 (j_lbf J); CB 4 (j_pad1 J);
   C8 (if sh_stdio f then Z_to_bv 64 rend else j_cookie J); C8 (j_off J); C8 (j_getln J); C8 (j_mbz2 J);
   C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)); C8 (Z_to_bv 64 (- sh_cnt0 f));
   C8 (j_pl J); C8 (j_nl J); C8 (j_locale J)].

(* [comment removed for export] *)
Definition rf_cells_raw (T p : Z) (w : bool) (f : shfile) (J : rfj) (she shl shc : word) : list cell :=
  let rend := rf_rend T p w f in
  [C4 (j_flags J); CB 4 (j_pad0 J); C8 (Z_to_bv 64 (T + sh_rpos f)); C8 (Z_to_bv 64 rend);
   C8 (j_close J); C8 (j_wend J); C8 (j_wpos J); C8 (j_mbz1 J); C8 (j_wbase J); C8 (j_read J); C8 (j_write J); C8 (j_seek J);
   C8 (Z_to_bv 64 T); C8 (j_bufsize J); C8 (j_prev J); C8 (j_next J); C4 (j_fd J); C4 (j_ppid J); C8 (j_lockcount J);
   C4 (j_mode J); C4 (j_lock J); C4 (j_lbf J); CB 4 (j_pad1 J);
   C8 (if sh_stdio f then Z_to_bv 64 rend else j_cookie J); C8 (j_off J); C8 (j_getln J); C8 (j_mbz2 J);
   C8 she; C8 shl; C8 shc;
   C8 (j_pl J); C8 (j_nl J); C8 (j_locale J)].

Lemma rf_cells_raw_eq : forall T p w f J,
  rf_cells T p w f J = rf_cells_raw T p w f J (Z_to_bv 64 (rf_rend T p w f)) (Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)) (Z_to_bv 64 (- sh_cnt0 f)).
Proof. reflexivity. Qed.

Lemma rf_cells_size : forall T p w f J, length (j_pad0 J) = 4%nat -> length (j_pad1 J) = 4%nat -> cells_size (rf_cells T p w f J) = 232%nat.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition ssJ : rfj :=
  mkJ (Z_to_bv 64 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
      (Z_to_bv 64 STRING_READ) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 M64) (Z_to_bv 64 M64) (Z_to_bv 64 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0).

(* [comment removed for export] *)
Definition RFI (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
  sh_ok T txt f /\ (-1 <= c < 256)%Z /\
  (sh_shlim_neg f = false -> kmin <= sh_rpos f)%Z /\
  (sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
  (sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
                        (w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ J = ssJ /\ 0 <= sh_cnt0 f <= sh_rpos f)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shlim_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p : Z) (w : bool) (f : shfile) (J : rfj) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(Fp, Fp + 232)%Z] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ rw_cells img_segs m' Fp (rf_cells T p w (sh_lim0 f) J).

Definition shlim_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (txt : list Z) (f : shfile) (J : rfj) (she shl shc : word),
  rw_cells img_segs m Fp (rf_cells_raw T p w f J she shl shc) ->
  sh_ok T txt f -> length (j_pad0 J) = 4%nat -> length (j_pad1 J) = 4%nat ->
  (0 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= p <= zlength txt)%Z ->
  mem_inv img_segs m ->
  evt img_segs (shlim_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p w f J m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHLIM) fc None m (seg_rom img_segs)).

Ltac show_goal := match goal with |- ?g => idtac g end.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.
Lemma sx32_M64 : sx32 (Z_to_bv 64 18446744073709551615) = Z_to_bv 64 18446744073709551615.
Proof. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit by lia. vm_compute. reflexivity. Qed.
Lemma zx32_lit : forall z, (0 <= z < 2^32)%Z -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.

Lemma shlim_spec : shlim_stmt.
Proof.
  unfold shlim_stmt. intros until shc. intros FC OK L0 L1 T0 T1 Hp MI.
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl img_segs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ FC) as B. unfold rf_cells_raw in FC, B. cbn [cells_size csize Nat.add] in B.
  (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst). unfold SHLIM.
  assert (RR : (0 <= rf_rend T p w f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); [destruct w|]; lia).
  unfold M64 in RR. pose_word_ranges.
  zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
  zs. br K1; change (Z.b2z (0 <? 0)) with 0%Z in K1; rewrite Z.land_0_l in K1; [clear K1 | exfalso; apply K1; reflexivity].
  zs. zs.
  apply evt_done. unfold shlim_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold rf_cells, sh_lim0. cbn [sh_rpos sh_cnt0 sh_stdio sh_shlim_neg sh_n sh_buf].
  unfold rf_rend in *. cbn [sh_stdio].
  replace (- sh_rpos f)%Z with (T - (T + sh_rpos f))%Z by lia. hyp.
Qed.

(* [comment removed for export] *)
Definition shlim_spec_c : Prop := shlim_stmt.
Lemma shlim_spec_c_ok : shlim_spec_c.
Proof. exact shlim_spec. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zero4 : list byte := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition w0 : word := Z_to_bv 64 0.
(* [comment removed for export] *)
Definition ss_cells (T rpos rend : Z) (mode : word) (cookie shend : Z) (shl shc : word) : list cell :=
  [C4 w0; CB 4 zero4; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend);
   C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C8 (Z_to_bv 64 STRING_READ); C8 w0; C8 w0;
   C8 (Z_to_bv 64 T); C8 w0; C8 w0; C8 w0; C4 w0; C4 w0; C8 w0;
   C4 mode; C4 (Z_to_bv 64 M64); C4 w0; CB 4 zero4;
   C8 (Z_to_bv 64 cookie); C8 w0; C8 w0; C8 w0;
   C8 (Z_to_bv 64 shend); C8 shl; C8 shc;
   C8 w0; C8 w0; C8 w0].

Lemma rf_cells_ss : forall T p w f, sh_stdio f = true ->
  rf_cells T p w f ssJ = ss_cells T (T + sh_rpos f) (rf_rend T p w f) (Z_to_bv 64 M64) (rf_rend T p w f) (rf_rend T p w f)
                            (Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)) (Z_to_bv 64 (- sh_cnt0 f)).
Proof. intros T p w f ST. unfold rf_cells, ss_cells. rewrite ST. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition toread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T cookie shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(q - 16, q); (Fp, Fp + 232)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (q - 16) (q)
    /\ rw_cells img_segs m' Fp (ss_cells T T T (Z_to_bv 64 M64) cookie shend shl shc).

Definition toread_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T rpos rend cookie shend : Z) (mode shl shc : word),
  rw_cells img_segs m Fp (ss_cells T rpos rend mode cookie shend shl shc) ->
  (mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
  (0 <= T /\ T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= cookie < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  stk img_segs m (q - 16) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv img_segs m ->
  evt img_segs (toread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T cookie shend shl shc m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TOREAD) fc None m (seg_rom img_segs)).

Lemma toread_spec : toread_stmt.
Proof.
  unfold toread_stmt. intros until shc. intros FC Hmode RT Rrp Rre Rck Rsh ST SPLO SPF SPF2 Q0 Q1 MI.
  pose proof (munch_refl [(q - 16, q); (Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl img_segs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ FC) as B. unfold ss_cells, w0 in FC. cbn [cells_size csize Nat.add] in B.
  unfold TOREAD, M64 in *. pose_word_ranges.
  zs. carve_frame 16%nat ST.
  zs. zs. zs.
  destruct Hmode as [-> | ->].
  all: zs; rewrite ?(sx32_small 0), ?sx32_M64 by lia.
  all: do 6 zs.
  all: br K1.
  all: zs; rewrite (zx32_lit 0) by lia.
  all: do 5 zs.
  all: br K2.
  all: do 8 zs.
  all: zs; zs; zs; zs.
  all: release_frame FR ST q.
  all: apply evt_done; unfold toread_post; repeat (lazymatch goal with |- ex _ => eexists end).
  all: split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST|].
  all: unfold ss_cells, w0; replace (T + 0)%Z with T by lia; hyp.
Qed.

(* [comment removed for export] *)
Definition toread_spec_c : Prop := toread_stmt.
Lemma toread_spec_c_ok : toread_spec_c.
Proof. exact toread_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac show_goal := match goal with |- ?g => idtac g end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.

(* [comment removed for export] *)
Existing Class shlim_spec_c.
Existing Class toread_spec_c.
End G_shgetc_A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_memset.
Import G_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.


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
Section Img.
  Context {IMG : RImg}.
  Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing). Local Notation GLRS a := (RelSym (sym a)) (only parsing). Context {RS_211c4 : GLRS 0x211c4}.
  Let rp_211c4 : (0 <= sym 0x211c4 /\ sym 0x211c4 < 2^30)%Z := @rel_sym_pf _ RS_211c4.
  Context {RS_18328 : GLRS 0x18328}.
  Let rp_18328 : (0 <= sym 0x18328 /\ sym 0x18328 < 2^30)%Z := @rel_sym_pf _ RS_18328.
  Context {RS_102a8 : GLRS 0x102a8}.
  Let rp_102a8 : (0 <= sym 0x102a8 /\ sym 0x102a8 < 2^30)%Z := @rel_sym_pf _ RS_102a8.
  Context {RS_341f8 : GLRS 0x341f8}.
  Let rp_341f8 : (0 <= sym 0x341f8 /\ sym 0x341f8 < 2^30)%Z := @rel_sym_pf _ RS_341f8.
  Context {RS_35000 : GLRS 0x35000}.
  Let rp_35000 : (0 <= sym 0x35000 /\ sym 0x35000 < 2^30)%Z := @rel_sym_pf _ RS_35000.
  Context {RS_22e18 : GLRS 0x22e18}.
  Let rp_22e18 : (0 <= sym 0x22e18 /\ sym 0x22e18 < 2^30)%Z := @rel_sym_pf _ RS_22e18.
  Context {RS_34288 : GLRS 0x34288}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Collection ImgHyps := IMG RS_211c4 rp_211c4 RS_18328 rp_18328 RS_102a8 rp_102a8 RS_341f8 rp_341f8 RS_35000 rp_35000 RS_22e18 rp_22e18 RS_34288 rp_34288.



Notation mem := (word -> option byte).

Definition RSTRTOD : Z := (sym 0x211c4).
Definition RSSCANF : Z := (sym 0x18328).
Definition RFMT_LG : Z := (sym 0x102a8).            (* [comment removed for export] *)
Definition RATP : Z := (sym 0x341f8).               (* [comment removed for export] *)
Definition RERRNO : Z := (sym 0x341f8 - 164).             (* [comment removed for export] *)
Definition RGLOBALS_TOP : Z := (sym 0x35000).       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition RSTRTOD_DEPTH : Z := 8928.         (* [comment removed for export] *)
Definition RSSCANF_DEPTH : Z := 9504.         (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rstrtod_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (T PE : Z) (txt : list Z) (npre bits used lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ev' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom img_segs)
    /\ munch [(lo, bv_unsigned sp); (PE, PE + 8); (RERRNO, RERRNO + 4)] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ frm0 fc'
    /\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
    /\ reg_get F' 10 = Z_to_bv 64 bits
    /\ stk img_segs m' lo (bv_unsigned sp)
    /\ rw_cells img_segs m' PE [C8 (Z_to_bv 64 (T + used))]
    /\ bytes_at img_segs m' T (map (Z_to_bv 8) txt)
    /\ ssp_cells m' canary
    /\ rw_cells img_segs m' RERRNO [C4 ev']
    /\ 0 <= used <= npre.      (* [comment removed for export] *)

Definition rstrtod_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (T PE : Z) (txt pre post : list Z) (bits used : Z) (ejunk : word) (lo : Z) (canary ev : word),
    bytes_at img_segs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
    txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> (length pre <= 64)%nat -> zlength txt <= 2^40 ->
    rw_cells img_segs m PE [C8 ejunk] ->
    scan_strtod txt = Some (bits, used) ->
    stk img_segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSTRTOD_DEPTH -> RGLOBALS_TOP <= lo -> bv_unsigned sp < 2^62 ->
    bv_unsigned sp <= T -> T + 2^41 <= 2^63 -> bv_unsigned sp <= PE -> PE + 8 <= 2^63 ->
    (PE + 8 <= T \/ T + zlength txt <= PE) ->
    ssp_cells m canary -> rw_cells img_segs m RERRNO [C4 ev] ->
    mem_inv img_segs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 PE ->
    evt img_segs (rstrtod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PE txt (zlength pre) bits used lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RSTRTOD) fc None m (seg_rom img_segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rsscanf_lg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (T PD : Z) (txt : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ev' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom img_segs)
    /\ munch [(lo, bv_unsigned sp); (PD, PD + 8); (RERRNO, RERRNO + 4)] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ frm0 fc'
    /\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
    /\ stk img_segs m' lo (bv_unsigned sp)
    /\ rw_cells img_segs m' PD [C8 (match res with Some bits => Z_to_bv 64 bits | None => djunk end)]
    /\ bytes_at img_segs m' T (map (Z_to_bv 8) txt)
    /\ ssp_cells m' canary
    /\ rw_cells img_segs m' RERRNO [C4 ev'].

Definition rsscanf_lg_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (T PD : Z) (txt pre post : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary ev : word),
    bytes_at img_segs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
    txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> (length pre <= 64)%nat ->
    (T + zlength txt) mod 8 = 0 -> zlength txt <= 256 ->     (* [comment removed for export] *)
    rw_cells img_segs m PD [C8 djunk] ->
    scan_sscanf_lg txt = Some (r, res) ->
    stk img_segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSSCANF_DEPTH -> RGLOBALS_TOP <= lo -> bv_unsigned sp < 2^62 ->
    bv_unsigned sp <= T -> T + 2^41 <= 2^63 -> bv_unsigned sp <= PD -> PD + 8 <= 2^63 ->
    (PD + 8 <= T \/ T + zlength txt <= PD) ->
    ssp_cells m canary -> rw_cells img_segs m RERRNO [C4 ev] ->
    mem_inv img_segs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 RFMT_LG -> a2 = Z_to_bv 64 PD ->
    evt img_segs (rsscanf_lg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RSSCANF) fc None m (seg_rom img_segs)).

End Img.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
