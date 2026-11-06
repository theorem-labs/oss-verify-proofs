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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_memcpy G_memchr G_fmt_fp_lib G_trunctfdf2.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_floatscan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNotJ.

(* [comment removed for export] *)
Definition strtod_prog (B got_ssp B_shlim B_floatscan B_trunctfdf2 B_stack_chk_fail : Z) : RStep.ptree :=
  PNode 80%Z
  (PNode 40%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 2 2 3824 4
        (PJ_Store_SZ8_nnn 4 2 1 264 4
        (PJ_Store_SZ8_nnn 8 2 8 256 4
        (PJ_Store_SZ8_nnn 12 2 9 248 4
        (PJ_Store_SZ8_nnn 16 2 18 240 4
        (PJ_OpImm_ALU_ADD_nnn 20 8 11 0 4
        (PJ_OpImm_ALU_ADD_nnn 24 9 10 0 4
        (PJ_Auipc_nt 28 10 (hi20 (got_ssp - (B + 28))) 4
        (PJ_Load_SZ8_true_nnt 32 18 10 (lo12 (got_ssp - (B + 28))) 4
        (PJ_Load_SZ8_true_nnn 36 10 18 0 4 nil)))))))))))
    (PLeaf
        (PJ_Store_SZ8_nnn 40 2 10 232 4
        (PJ_OpImm_ALU_ADD_nnn 44 10 0 4095 4
        (PJ_Store_SZ8_nnn 48 2 9 88 4
        (PJ_Store_SZ8_nnn 52 2 9 8 4
        (PJ_Store_SZ8_nnn 56 2 10 16 4
        (PJ_OpImm_ALU_ADD_nnn 60 10 2 0 4
        (PJ_OpImm_ALU_ADD_nnn 64 11 0 0 4
        (PJ_Jal_nt 68 1 (jimm21 (B_shlim - (B + 68))) 4
        (PJ_OpImm_ALU_ADD_nnn 72 10 2 0 4
        (PJ_OpImm_ALU_ADD_nnn 76 11 0 1 4 nil))))))))))))
  (PNode 120%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 80 12 0 1 4
        (PJ_Jal_nt 84 1 (jimm21 (B_floatscan - (B + 84))) 4
        (PJ_Branch_BC_EQ_nnn 88 8 0 32 4
        (PJ_Load_SZ8_true_nnn 92 12 2 8 4
        (PJ_Load_SZ8_true_nnn 96 13 2 88 4
        (PJ_Load_SZ8_true_nnn 100 14 2 200 4
        (PJ_Op_ALU_SUB_nnn 104 12 12 13 4
        (PJ_Op_ALU_ADD_nnn 108 14 9 14 4
        (PJ_Op_ALU_ADD_nnn 112 12 14 12 4
        (PJ_Store_SZ8_nnn 116 8 12 0 4 nil)))))))))))
    (PLeaf
        (PJ_Jal_nt 120 1 (jimm21 (B_trunctfdf2 - (B + 120))) 4
        (PJ_Load_SZ8_true_nnn 124 10 18 0 4
        (PJ_Load_SZ8_true_nnn 128 11 2 232 4
        (PJ_Branch_BC_NE_nnn 132 10 11 28 4
        (PJ_Load_SZ8_true_nnn 136 1 2 264 4
        (PJ_Load_SZ8_true_nnn 140 8 2 256 4
        (PJ_Load_SZ8_true_nnn 144 9 2 248 4
        (PJ_Load_SZ8_true_nnn 148 18 2 240 4
        (PJ_OpImm_ALU_ADD_nnn 152 2 2 272 4
        (PJ_Jalr_nnn 156 0 1 0 4
        (PJ_Jal_nt 160 1 (jimm21 (B_stack_chk_fail - (B + 160))) 4 nil))))))))))))).

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
Definition PROGAT_CODE_strtod (IMG : RImg) := strtod_prog (sym 0x211c4) (sym 0x22e18) (sym 0x1df40) (sym 0x1e0cc) (sym 0x209ec) (sym 0x15f04).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_strtod : CodeAtT img_segs (sym 0x211c4) (PROGAT_CODE_strtod IMG)}.
  Context {RB_strtod : RelCode (sym 0x211c4) 164}.
  Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing). Local Notation GLRS a := (RelSym (sym a)) (only parsing). Context {RN_B_shlim_211c4 : GLRN 0x211c4 0x1df40}.
  Context {RN_B_floatscan_211c4 : GLRN 0x211c4 0x1e0cc}.
  Context {RN_B_trunctfdf2_211c4 : GLRN 0x211c4 0x209ec}.
  Context {RN_B_stack_chk_fail_211c4 : GLRN 0x211c4 0x15f04}.
  Context {RS_got_ssp : GLRS 0x22e18}.
  Context {RS_34288 : GLRS 0x34288}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {RS_341f8 : GLRS 0x341f8}.
  Let rp_341f8 : (0 <= sym 0x341f8 /\ sym 0x341f8 < 2^30)%Z := @rel_sym_pf _ RS_341f8.
  Context {RS_35000 : GLRS 0x35000}.
  Let rp_35000 : (0 <= sym 0x35000 /\ sym 0x35000 < 2^30)%Z := @rel_sym_pf _ RS_35000.
  Context {RS_102a8 : GLRS 0x102a8}.
  Let rp_102a8 : (0 <= sym 0x102a8 /\ sym 0x102a8 < 2^30)%Z := @rel_sym_pf _ RS_102a8.
  Context {SPEC_trunctfdf2 : trunctfdf2_contract}.
  Context {SPEC_shlim_spec : shlim_spec_c}.
  Context {SPEC_L_ENTRY : G_floatscan.L_ENTRY_c}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 172 <= sym 0x341f8)%Z}.
  Let rl0_0 : (sym 0x22e18 + 172 <= sym 0x341f8)%Z := @zfact_pf _ RL0_0.
  Context {RL0_1 : ZFact (sym 0x341f8 + 0 <= sym 0x34288)%Z}.
  Let rl0_1 : (sym 0x341f8 + 0 <= sym 0x34288)%Z := @zfact_pf _ RL0_1.
  Context {RL0_2 : ZFact (sym 0x34288 + 8 <= sym 0x35000)%Z}.
  Let rl0_2 : (sym 0x34288 + 8 <= sym 0x35000)%Z := @zfact_pf _ RL0_2.
  Context {RQ_22e18 : ZFact (0x20000 <= sym 0x22e18 < 2^30)%Z}.
  Let rq_22e18 : (0x20000 <= sym 0x22e18 < 2^30)%Z := @zfact_pf _ RQ_22e18.
  Collection ImgHyps := IMG CODE_strtod RB_strtod RN_B_shlim_211c4 RN_B_floatscan_211c4 RN_B_trunctfdf2_211c4 RN_B_stack_chk_fail_211c4 RS_got_ssp RS_34288 rp_34288 RS_341f8 rp_341f8 RS_35000 rp_35000 RS_102a8 rp_102a8 SPEC_trunctfdf2 SPEC_shlim_spec SPEC_L_ENTRY RL0_0 rl0_0 RL0_1 rl0_1 RL0_2 rl0_2 RQ_22e18 rq_22e18.


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
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI rp_34288 rp_341f8 rp_35000 rp_102a8 rl0_0 rl0_1 rl0_2 rq_22e18; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

Ltac hush := idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).
Tactic Notation "callx" tactic3(tac) := callw tac; try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end).

Lemma strtod_file_raw : forall T p txt (fl : word) p0 (c24 c32 c40 c48 c56 c64 c72 c80 c96 c104 c112 fd pp c128 md lk lbf : word) p1 (c152 c160 c168 c176 c184 c192 c200 c208 c216 c224 : word),
  let J := mkJ fl p0 c24 c32 c40 c48 c56 c64 c72 c80 c96 c104 c112 fd pp c128 md lk lbf p1 c152 c160 c168 c176 c208 c216 c224 in
  let f := mkSh txt 0 0 0 false false in
  rf_cells_raw T p true f J c184 c192 c200 =
  [C4 fl; CB 4 p0; C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 18446744073709551615); C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80;
   C8 (Z_to_bv 64 T); C8 c96; C8 c104; C8 c112; C4 fd; C4 pp; C8 c128; C4 md; C4 lk; C4 lbf; CB 4 p1;
   C8 c152; C8 c160; C8 c168; C8 c176; C8 c184; C8 c192; C8 c200; C8 c208; C8 c216; C8 c224].
Proof. intros. unfold rf_cells_raw, rf_rend. cbn. rewrite Z.add_0_r. reflexivity. Qed.

Theorem rstrtod_proof : rstrtod_stmt.
Proof.
  unfold rstrtod_stmt. intros until ev. intros BY BYT Htxt Hpre Hlen Hlt PEC HS ST LO GT SPH HT T1 HPE HPE2 SEPE [SSP1 SSP2] ERR MI FRM Htp Ha0 Ha1.
  idtac. idtac .
  unfold RSTRTOD_DEPTH, RGLOBALS_TOP, RATP in *. unfold G_Scan_iface.RERRNO in *. unfold got_ssp, ssp_guard in SSP1, SSP2.
  subst tp a0 a1.
  pose_word_ranges.
  assert (LT : length (map (Z_to_bv 8) txt) = length txt) by apply length_map.
  assert (Hp : (0 <= zlength pre < zlength txt)%Z) by (subst txt; unfold zlength; rewrite length_app; cbn; lia).
  unfold zlength in Hlt, SEPE.
  pose proof (munch_refl [(lo, bv_unsigned sp); (PE, PE + 8); ((sym 0x341f8 - 164), (sym 0x341f8 - 164) + 4)]%Z m) as MU. pose proof (wmono_refl img_segs m) as WM.
  (* [comment removed for export] *)
  set (f0 := mkSh txt 0 0 0 false false).
  pose proof HS as HS'. unfold scan_strtod in HS'. change (mkSh txt 0 0 0 false false) with f0 in HS'.
  destruct (floatscan (fuel_of txt) f0 1 1) as [[fR yR]|] eqn:HM; [|discriminate HS'].
  injection HS' as Ebits Eused.
  assert (Hnul : znth txt (zlength pre) = 0%Z) by (subst txt; apply znth_app_mid).
  assert (Hnum : forall i, (0 <= i < zlength pre)%Z -> is_numch (znth txt i) = true).
  { intros i Hi. subst txt. rewrite znth_app_pre by exact Hi. exact (proj1 (Forall_forall _ _) Hpre _ (znth_In' pre i Hi)). }
  assert (OK0 : sh_ok T txt f0).
  { unfold sh_ok, f0. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio]. unfold zlength in *. repeat split; try reflexivity; try lia; try (intros X; discriminate X). }
  unfold RSTRTOD.
  (* [comment removed for export] *)
  zs.
  carve_frame 40%nat ST. rename FR into FRT.
  carve_frame 232%nat ST. rename FR into FILE.
  destruct (file_cells_of_junk _ _ _ _ FILE) as (fl & p0 & w8 & w16 & c24 & c32 & c40 & c48 & c56 & c64 & c72 & c80 & w88 & c96 & c104 & c112 & fd & pp & c128 & md & lk & lbf & p1 & c152 & c160 & c168 & c176 & c184 & c192 & c200 & c208 & c216 & c224 & FC & L0 & L1).
  clear FILE. match goal with H : list byte |- _ => try clear H end.
  zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
  zs. zs. zs. zs.
  (* [comment removed for export] *)
  set (J := mkJ fl p0 c24 c32 c40 c48 c56 c64 c72 c80 c96 c104 c112 fd pp c128 md lk lbf p1 c152 c160 c168 c176 c208 c216 c224).
  rewrite <- (strtod_file_raw T (zlength pre) txt fl p0 c24 c32 c40 c48 c56 c64 c72 c80 c96 c104 c112 fd pp c128 md lk lbf p1 c152 c160 c168 c176 c184 c192 c200 c208 c216 c224) in FC.
  fold J f0 in FC.
  assert (RJ0 : RFJ T txt (zlength pre) true J 0 1 f0).
  { unfold RFJ, f0. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. split; [exact OK0|].
    repeat split; try lia; intros X; try discriminate X; try lia. }
  pose proof SPEC_shlim_spec as SL. unfold shlim_stmt in SL.
  zs. zs. zs. callx (eapply SL with (Fp := (bv_unsigned sp + -272)%Z) (T := T) (p := zlength pre) (w := true) (txt := txt) (f := f0) (J := J);
      [exact FC | exact OK0 | exact L0 | exact L1 | lia | lia | unfold zlength in *; lia | assumption]).
  clear SL.
  match goal with H : rw_cells _ _ _ (rf_cells _ _ _ (sh_lim0 f0) _) |- _ => rename H into FC1 end. change (sh_lim0 f0) with f0 in FC1.
  match goal with H : stk _ _ lo _ |- _ => rename H into STK end.
  (* [comment removed for export] *)
  zs. zs. zs. zs.
  destruct (stk_split _ _ _ (bv_unsigned sp + -272 - 8656)%Z _ STK ltac:(lia)) as [STlo SThi].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  pose proof (SPEC_L_ENTRY (Z_to_bv 64 (sym 0x211c4 + 88)) (bv_unsigned sp + -272)%Z gp (Z_to_bv 64 PE) (Z_to_bv 64 T) (Z_to_bv 64 (sym 0x34288)) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mm
                (bv_unsigned sp + -272)%Z T (zlength pre) J txt pre post canary 1%Z (fuel_of txt) f0 0%Z 1%Z fR yR) as LE end.
  specialize (LE HM ltac:(right; reflexivity) ltac:(intros X; exfalso; discriminate X) BYT Hp Hnul Hnum ltac:(unfold zlength in *; lia) ltac:(lia) T1
                 ltac:(lia) ltac:(unfold G_floatscan_common.RERRNO; lia) ltac:(unfold G_floatscan_common.FS_DEPTH; lia) ltac:(lia) ltac:(lia)
                 ltac:(unfold G_floatscan_common.FS_DEPTH; lia) ltac:(unfold G_floatscan_common.FS_DEPTH, ssp_guard; lia) ltac:(unfold got_ssp; lia) ltac:(unfold ssp_guard; lia) ltac:(lia) FRM).
  cbv zeta in LE. unfold G_floatscan_common.FS_DEPTH, G_floatscan_common.RERRNO, G_floatscan_common.FLOATSCAN, G_floatscan_common.RATP in LE.
  unfold G_floatscan_common.fs_post, G_floatscan_common.Wfs, G_floatscan_common.FS_DEPTH, G_floatscan_common.RERRNO, G_floatscan_common.FokR in LE.
  callx (eapply LE; [ exact SThi | exact MI0 | exact FC1 | exact RJ0 | lia | lia | reflexivity | exact BY | split; [exact SSP1 | exact SSP2] | exact ERR ]).
  clear LE.
  match goal with H : rw_cells _ _ _ (rf_cells _ _ _ fR _) |- _ => rename H into FC2 end.
  match goal with H : RFJ _ _ _ _ _ _ _ fR |- _ => rename H into RJ2 end.
  match goal with H : ssp_cells _ canary |- _ => destruct H as [SSP3 SSP4]; unfold got_ssp, ssp_guard in SSP3, SSP4 end.
  match goal with H : stk _ ?m' (bv_unsigned sp + -272 - 8656)%Z _ |- _ => pose proof (stk_merge _ _ _ _ _ STlo H ltac:(lia)) as STK2; clear H STlo end.
  match goal with H : bytes_at _ _ T (zbytes txt) |- _ => rename H into BY2; unfold zbytes in BY2 end.
  match goal with H : frm0 ?x |- evt _ _ (MS _ _ _ ?x _ _ _) => rename H into FRM2 end.
  match goal with H : forall k : reg, _ -> _ -> _ -> reg_get _ k = reg_get F k |- _ => rename H into FOK end.
  pose proof RJ2 as RJ3. (nelim RJ3 6%nat; intros OK2 Rc2 CC2 KM2 NS2 SS2). (nelim OK2 6%nat; intros Hbuf2 Rl2 Rr2 Rc02 Rn2 Rst2).
  assert (JRR : JR (zlength pre) fR).
  { unfold fuel_of in HM. eapply (floatscan_JR txt (zlength pre) BYT Hp Hnul Hnum _ _ _ _ _ HM).
    unfold JF, f0. cbn. repeat split; try reflexivity; try lia; intros X; try discriminate X; lia. }
  unfold JR in JRR.
  pose proof FC2 as FC3. unfold rf_cells in FC3.
  cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale J] in FC3.
  assert (RR : (0 <= rf_rend T (zlength pre) true fR <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio fR); unfold zlength in *; lia). unfold M64 in RR.
  (* [comment removed for export] *)
  zs. br K0.
  zs. zs. zs. zs. zs. zs. zs.
  match goal with H : rw_cells _ _ PE [C8 (Z_to_bv 64 ?v)] |- _ => replace v with (T + used)%Z in H by (rewrite <- Eused; unfold sh_cnt; lia) end.
  (* [comment removed for export] *)
  zs. callx (eapply SPEC_trunctfdf2; [eassumption]).
  idtac. idtac .
  rewrite !ulit_lo64, !ulit_hi64.
  change (lo64 yR + 2 ^ 64 * hi64 yR)%Z with (canon yR). rewrite F_scan_calls.f128_to_d_canon. rewrite Ebits.
  (* [comment removed for export] *)
  zs. zs. zs. br K1.
  zs. zs. zs. zs. zs. zs.
  match goal with H : stk _ ?m' lo _, H2 : mem_inv _ ?m' |- evt _ _ (MS _ _ _ _ _ ?m' _) => rename H into ST9; rename H2 into MI9 end.
  release_frame FC3 ST9 (bv_unsigned sp + -40)%Z.
  release_frame FRT ST9 (bv_unsigned sp).
  apply evt_done. unfold rstrtod_post.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [unfold G_floatscan_common.RATP; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI9|]. split; [exact FRM2|].
  split. { intros k H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity). exact (FOK k H10 H14 H15). }
  split; [rewrite freg_get_same by (vm_compute; reflexivity); reflexivity|].
  split; [exact ST9|]. split; [hyp|]. split; [exact BY2|]. split; [split; [exact SSP3 | exact SSP4]|]. split; [match goal with H : rw_cells _ _ (sym 0x341f8 - 164) _ |- _ => exact H end|].
  rewrite <- Eused. unfold sh_cnt. lia.
Qed.

(* [comment removed for export] *)
Definition rstrtod_proof_c : Prop := rstrtod_stmt.
Lemma rstrtod_proof_c_ok : rstrtod_proof_c.
Proof. exact rstrtod_proof. Qed.


End Img.
(* [comment removed for export] *)
Ltac hush := idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).
Tactic Notation "callx" tactic3(tac) := callw tac; try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end).

(* [comment removed for export] *)
Existing Class rstrtod_proof_c.
