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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Bytes PropExec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require Import G_memset G_memcpy G_memchr G_strnlen G_fwritex G_pad G_fmt_fp_lib. From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require Import G_pop_arg.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.P Require Import Printf_mlib. From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Import Printf_model Printf_zfacts.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Import G_pop_arg_x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Import G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import StoreCache.   (* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require ProgAt3.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G.ProgAt3.Prog_printf_core.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require Import GRoTab. From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import NElim. From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require ProgAt3.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G.ProgAt3.ProgAt2. From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require JunkAbs.
(* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_printf_core_conv : CodeAtT img_segs (sym 0x18704) (printf_core_prog_at IMG)}.
  Context {RB_printf_core_conv : RelCode (sym 0x18704) 3632}.
  Context {RO_10884 : RoB img_segs (sym 0x10884) ROT_0x10884}.
  Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing). Local Notation GLRS a := (RelSym (sym a)) (only parsing). Context {RN_B_fwritex_18704 : GLRN 0x18704 0x17d50}.
  Context {RN_B_pop_arg_18704 : GLRN 0x18704 0x19534}.
  Context {RN_B_fmt_fp_18704 : GLRN 0x18704 0x1973c}.
  Context {RN_B_errno_location_18704 : GLRN 0x18704 0x15f44}.
  Context {RN_B_strerror_18704 : GLRN 0x18704 0x1ae04}.
  Context {RN_B_strnlen_18704 : GLRN 0x18704 0x21920}.
  Context {RN_B_wctomb_18704 : GLRN 0x18704 0x1ae48}.
  Context {RN_B_pad_18704 : GLRN 0x18704 0x19668}.
  Context {RN_B_memset_18704 : GLRN 0x18704 0x21738}.
  Context {RN_B_stack_chk_fail_18704 : GLRN 0x18704 0x15f04}.
  Context {RS_got_ssp : GLRS 0x22e18}.
  Context {RS_K_109cc : GLRS 0x109cc}.
  Context {RS_K_10884 : GLRS 0x10884}.
  Context {RS_K_1029e : GLRS 0x1029e}.
  Context {RS_K_103b3 : GLRS 0x103b3}.
  Context {RS_K_10964 : GLRS 0x10964}.
  Context {RS_K_10b9c : GLRS 0x10b9c}.
  Context {RS_1029e : GLRS 0x1029e}.
  Let rp_1029e : (0 <= sym 0x1029e /\ sym 0x1029e < 2^30)%Z := @rel_sym_pf _ RS_1029e.
  Context {RS_34288 : GLRS 0x34288}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {RS_35000 : GLRS 0x35000}.
  Let rp_35000 : (0 <= sym 0x35000 /\ sym 0x35000 < 2^30)%Z := @rel_sym_pf _ RS_35000.
  Context {SPEC_pop_arg : pop_arg_contract}.
  Context {SPEC_strnlen : strnlen_contract}.
  Context {SPEC_memset : memset_contract}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)%Z}.
  Let rl0_1 : (sym 0x34288 + 8 <= sym 0x35000)%Z := @zfact_pf _ RL0_1.
  Context {RL1_0 : ZFact (sym 0x22e18 + 240 <= sym 0x34288)%Z}.
  Let rl1_0 : (sym 0x22e18 + 240 <= sym 0x34288)%Z := @zfact_pf _ RL1_0.
  Context {RO_states0 : RoB img_segs (sym 0x109cc) (zb STATES0)}.
  Context {RO_pfx : RoB img_segs (sym 0x1029e) (zb [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z)}.
  Context {RQ_pfx : ZFact (sym 0x1029e + 9 <= 0x14000)%Z}.
  Let rq_pfx : (sym 0x1029e + 9 <= 0x14000)%Z := @zfact_pf _ RQ_pfx.
  Context {RQ_pfx_lo : ZFact (0x10000 <= sym 0x1029e)%Z}.
  Let rq_pfx_lo : (0x10000 <= sym 0x1029e)%Z := @zfact_pf _ RQ_pfx_lo.
  Context {RQ_pfx_got : ZFact (sym 0x1029e + 9 <= sym 0x22e18)%Z}.
  Let rq_pfx_got : (sym 0x1029e + 9 <= sym 0x22e18)%Z := @zfact_pf _ RQ_pfx_got.
  Context {RO_xdigits : RoB img_segs (sym 0x10b9c) (zb XDIGITS)}.
  Context {RQ_22e18 : ZFact (0x14000 <= sym 0x22e18)%Z}.
  Let rq_22e18 : (0x14000 <= sym 0x22e18)%Z := @zfact_pf _ RQ_22e18.
  Context {SPEC_pop_arg_x : pop_arg_x_contract}.
  Collection ImgHyps := IMG CODE_printf_core_conv RB_printf_core_conv RO_10884 RN_B_fwritex_18704 RN_B_pop_arg_18704 RN_B_fmt_fp_18704 RN_B_errno_location_18704 RN_B_strerror_18704 RN_B_strnlen_18704 RN_B_wctomb_18704 RN_B_pad_18704 RN_B_memset_18704 RN_B_stack_chk_fail_18704 RS_got_ssp RS_K_109cc RS_K_10884 RS_K_1029e RS_K_103b3 RS_K_10964 RS_K_10b9c RS_1029e rp_1029e RS_34288 rp_34288 RS_35000 rp_35000 SPEC_pop_arg SPEC_strnlen SPEC_memset RL0_0 rl0_0 RL0_1 rl0_1 RL1_0 rl1_0 RO_states0 RO_pfx RQ_pfx rq_pfx RQ_pfx_lo rq_pfx_lo RQ_pfx_got rq_pfx_got RO_xdigits RQ_22e18 rq_22e18 SPEC_pop_arg_x.


Local Ltac step ::= astep2_fast. Local Ltac stepz ::= astep2_fast.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)
(* [comment removed for export] *)

Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp B BS RC RCS RE RES : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS RC RCS RE RES SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS RC RCS RE RES SINK TOPOK OUT.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q < 2^63)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (A + zlength fmt <= 0x14000)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : (((sym 0x22e18 + 8) <= Fp /\ Fp + 232 <= (sym 0x34288)) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA) \/ (0 < Fp /\ Fp + 232 <= lo /\ ((Fp + 232 <= 65536 /\ 65536 <= A) \/ (sym 0x35000) <= Fp)))%Z.
  Hypothesis SEP_B : ((AP + 8 <= B /\ B + BS <= VA) \/ (0 < B /\ B + BS <= lo /\ ((B + BS <= 65536 /\ 65536 <= A) \/ (sym 0x35000) <= B)))%Z.
  Hypothesis SEP_C : (AP + 8 <= RC /\ RC + RCS <= VA)%Z.
  Hypothesis SEP_E : (((sym 0x34288 + 8) <= RE /\ RE + RES <= lo) \/ (VA <= RE /\ VA + 8 * zlength slots <= RE /\ RE + RES <= 2^64) \/ (0 < RE /\ RE + RES <= 65536 /\ 65536 <= A) \/ (GOT_GUARD_SLOT + 8 <= RE /\ RE + RES <= STACK_GUARD))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  Hypothesis CS0 : (0 <= RCS)%Z.
  Hypothesis ES0 : (0 <= RES)%Z.

  (* [comment removed for export] *)
  Local Notation GLRUN1 f := (f ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt) (only parsing). Local Notation ctx_all := ((GLRUN1 G_printf_core_common.ctx_all)).
  Local Notation W := (G_printf_core_common.W Fp B BS RC RCS RE RES q lo AP).
  Local Notation Fok := (G_printf_core_common.Fok F).
  Local Notation Fok_refl := (G_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (G_printf_core_common.Fok_trans F).
  Local Notation GLRUN2 f := (f s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) (only parsing). Local Notation POST := ((GLRUN2 (G_printf_core_common.POST (St:=St) Fp B BS RC RCS RE RES SINK ra q gp tp)) F m0 lo canary AP).
  Local Notation hi_cells := ((GLRUN2 (G_printf_core_common.hi_cells ra)) canary).
  Local Notation lo_cells := (G_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := ((GLRUN2 (G_printf_core_common.finv Fp B BS RC RCS RE RES ra q)) m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (G_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (G_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (G_printf_core_common.sink_store (St:=St) Fp B BS RC RCS RE RES SINK SFR).
  Local Notation sink_call := (G_printf_core_common.sink_call (St:=St) Fp B BS RC RCS RE RES SINK SFR).
  Local Notation arg_ok_W := (G_printf_core_common.arg_ok_W Fp B BS RC RCS RE RES q lo fmt AP slots).
  Local Notation args_ok_W := (G_printf_core_common.args_ok_W Fp B BS RC RCS RE RES q lo fmt AP slots).
  Local Notation lo_cells14 := (G_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (G_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (G_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (G_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation pop_arg_x_callq := (G_printf_core_common.pop_arg_x_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (G_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (G_printf_core_common.out_postq (St:=St) Fp B BS RC RCS RE RES SINK q gp tp lo canary).
  Local Notation out_callq := (G_printf_core_common.out_callq (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT TOK HOUT q gp tp lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B SEP_C SEP_E HAP HVA BS0 CS0 ES0).
  Local Notation fp_postq := (G_printf_core_common.fp_postq (St:=St) Fp B BS RC RCS RE RES SINK q gp tp lo canary).
  Local Notation fp_callq := (G_printf_core_common.fp_callq (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUTFP TOK q gp tp lo canary A AP VA slots LO GLO QHI TQ SEP_F SEP_B SEP_C SEP_E HAP HVA).
  Local Notation S_EXIT := ((GLRUN1 (G_printf_core_common.S_EXIT (St:=St) Fp B BS RC RCS RE RES SINK))).
  Local Notation S_SCAN := ((GLRUN1 (G_printf_core_common.S_SCAN Fp B BS RC RCS RE RES))).
  Local Notation S_FLAGS := ((GLRUN1 (G_printf_core_common.S_FLAGS Fp B BS RC RCS RE RES))).
  Local Notation S_WLOOP := ((GLRUN1 (G_printf_core_common.S_WLOOP Fp B BS RC RCS RE RES))).
  Local Notation S_WIDTH := ((GLRUN1 (G_printf_core_common.S_WIDTH Fp B BS RC RCS RE RES))).
  Local Notation S_PLOOP := ((GLRUN1 (G_printf_core_common.S_PLOOP Fp B BS RC RCS RE RES))).
  Local Notation S_PREC := ((GLRUN1 (G_printf_core_common.S_PREC Fp B BS RC RCS RE RES))).
  Local Notation S_STATE := ((GLRUN1 (G_printf_core_common.S_STATE Fp B BS RC RCS RE RES))).
  Local Notation S_DIR := ((GLRUN1 (G_printf_core_common.S_DIR Fp B BS RC RCS RE RES))).
  Local Notation S_END := ((GLRUN1 (G_printf_core_common.S_END (St:=St) Fp B BS RC RCS RE RES SINK))).
  Local Notation S_HEAD := ((GLRUN1 (G_printf_core_common.S_HEAD (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_CONV := ((GLRUN1 (G_printf_core_common.S_CONV (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation body_loc := (G_printf_core_common.body_loc Fp B BS RC RCS RE RES q lo).
  Local Notation S_TAIL := ((GLRUN1 (G_printf_core_common.S_TAIL (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation tregs := (G_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := ((GLRUN2 (G_printf_core_common.tinv (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUTFP ra q)) m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := ((GLRUN1 (G_printf_core_common.S_T6 (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_T5 := ((GLRUN1 (G_printf_core_common.S_T5 (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_T4 := ((GLRUN1 (G_printf_core_common.S_T4 (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_T3 := ((GLRUN1 (G_printf_core_common.S_T3 (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_T2 := ((GLRUN1 (G_printf_core_common.S_T2 (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_T1 := ((GLRUN1 (G_printf_core_common.S_T1 (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_INTC2 := ((GLRUN1 (G_printf_core_common.S_INTC2 (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_INTC := ((GLRUN1 (G_printf_core_common.S_INTC (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation dloop_post := (G_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := ((GLRUN1 G_printf_core_common.S_DLOOP)).
  Local Notation S_FMTU2 := ((GLRUN1 (G_printf_core_common.S_FMTU2 (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_FMTU := ((GLRUN1 (G_printf_core_common.S_FMTU (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_CV_D := ((GLRUN1 (G_printf_core_common.S_CV_D (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_CV_U := ((GLRUN1 (G_printf_core_common.S_CV_U (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation xloop_post := (G_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := ((GLRUN1 G_printf_core_common.S_XLOOP)).
  Local Notation S_CV_X := ((GLRUN1 (G_printf_core_common.S_CV_X (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_CV_S := ((GLRUN1 (G_printf_core_common.S_CV_S (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_CV_C := ((GLRUN1 (G_printf_core_common.S_CV_C (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_CV_FP := ((GLRUN1 (G_printf_core_common.S_CV_FP (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation POST1 := ((GLRUN2 (G_printf_core_common.POST1 ra q gp tp)) F fc0 m0 lo canary).
  Local Notation S_EXIT1 := ((GLRUN1 (G_printf_core_common.S_EXIT1 Fp B BS RC RCS RE RES))).
  Local Notation S_P1 := ((GLRUN1 (G_printf_core_common.S_P1 Fp B BS RC RCS RE RES))).
  Local Notation S_PRO := ((GLRUN1 (G_printf_core_common.S_PRO Fp B BS RC RCS RE RES))).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    (nelim H 9%nat; intros MI MU WM FRhi ST BY VAA SSP1 SSP2); unfold W in MU; unfold hi_cells in FRhi;
    unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
    try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
         lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
    try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
         lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
    unfold zlength in *; hush.
  Ltac hyp :=
    lazymatch goal with
    | |- rw_cells _ ?m ?A ?cs =>
        match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
    | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
    end.
  Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
  Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
  Ltac rd_fmt idx :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl end | progress f_equal | zl ].
  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  (* [comment removed for export] *)
  Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia | rewrite Hn; tslia | rewrite Hn; tslia ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
    end.
  Local Ltac transport_call_extra segs W m m' MU WM ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ eapply (sink_call W m m' st) in H;
                [ | exact MU | exact WM
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    end.
  Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
  Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
  Local Ltac mem_after_store ::= mem_after_store_fast.
  Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
  Local Ltac mem_after_store ::= mem_after_store_cached.
  Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
  Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
  Local Ltac lia ::= lia3.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.StoreCache.LiaClosure.

(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require RPre. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RPre.rl_zify_pre_hook.
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)

Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
(* [comment removed for export] *)
Local Ltac br10 K := brf K; [ exfalso; lia | ].
Local Ltac br01 K := brf K; [ | exfalso; lia ].

Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ (sym 0x22e18) _ |- _ => exact H end
        | match goal with H : rw_cells _ _ (sym 0x34288) _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | | (try (unfold zlength in *; lia)) | (try (unfold zlength in *; lia)) ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call (@img_segs IMG) m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_sym; arel_side) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl end | progress f_equal | zl ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    (nelim H 25%nat; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp);
    pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
    pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
    let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
  Ltac mk_tinv :=
    lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      unfold tinv, body_loc;
      split; [mk_finv|];
      split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
      split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
      split; [match goal with H : SINK m _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
      split; [lia|];
      split; [assumption|];
      split; [assumption|];
      split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
      repeat (split; [first [assumption | reflexivity | (lazymatch goal with |- context [INT_MAX] => unfold INT_MAX in *; zl end) | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | (lazymatch goal with |- context [INT_MAX] => unfold INT_MAX in *; zl end) | lia | zl | unfold INT_MAX in *; zl]
    end.

  Hypothesis HS_CV_D : S_CV_D.
  Hypothesis HS_CV_U : S_CV_U.
  Hypothesis HS_CV_X : S_CV_X.
  Hypothesis HS_CV_S : S_CV_S.
  Hypothesis HS_CV_FP : S_CV_FP.
  Hypothesis HS_CV_C : S_CV_C.

  (* [comment removed for export] *)
  Lemma L_CONV : S_CONV.
  Proof using BS0 CS0 ES0 GLO HA HAP HF HS_CV_C HS_CV_D HS_CV_FP HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR VAHI ImgHyps.
    intros fuel HH x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Ht CT Hfl Hw Hp XP Hc.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
    (* [comment removed for export] *)
    cbn [args_ok] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [AOK1 AOK].
    assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
    { rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
    assert (ESK' : skipn (Z.to_nat (k + 1)) slots = slots').
    { replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
    rewrite <- ESK' in AOK.
    (nelim (lo_split _ _ _ _ _ _ _ _ _ _ LOW) 3%nat; intros LOW14 ARGC J128). unfold lo_cells14, ssp_guard in LOW14. clear LOW.
    pose proof (land_bound' (d_fl d) 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq (d_fl d)) in FLB by lia.
    unfold conv. cbv zeta. unfold LEFT_ADJ, ZERO_PAD. unfold conv_ok in CT.
    (* [comment removed for export] *)
    destruct a as [sv | iv | uv | dd | lv];
      [ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_DBL) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct ((d_ty d =? T_ULLONG) || (d_ty d =? T_SIZET))%Z eqn:ETY; [cbn [negb] | cbn [negb]; apply implM_unr_l] ].
    5: {
      apply orb_true_iff in ETY.
      assert (TY : (d_ty d = T_ULLONG \/ d_ty d = T_SIZET)%Z) by (destruct ETY as [E|E]; apply Z.eqb_eq in E; [left|right]; exact E).
      clear ETY.
      assert (T117 : d_t d = 117%Z).
      { destruct CT as [CT | (T & _)]; [|exact T]. exfalso. pose proof (conv_type_ty _ _ CT) as TT. unfold T_ULLONG, T_SIZET in TY. lia. }
      rewrite (proj2 (Z.eqb_eq _ _) T117).
      cbn [arg_ok] in AOK1.
      pose proof (bv_unsigned_in_range 64 slot) as RS. unfold bv_modulus in RS. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in RS.
      assert (PS : ty_ps (d_ty d) = 2%Z \/ ty_ps (d_ty d) = 6%Z) by (destruct TY as [E|E]; rewrite E; [left|right]; reflexivity).
      destruct PS as [PS|PS]; rewrite PS.
      all: ienter; zs; br10 K; zs; zs; zs; zs.
      all: callx (eapply pop_arg_x_callq; [lia | exact APC | exact VAA | exact NTH | lia | exact ARGC | exact ST | exact MI | exact TY]).
      all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC' end.
      all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
      all: zs.
      all: match goal with H : SINK ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => (nelim (SFL _ _ H) 3%nat; intros fb FLC FB) end; zs; zs; zs; br10 K1; clear FLC.
      all: rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
      all: zsto (sym 0x18704 + 1284)%Z.
      all: lazymatch goal with |- context [Z.land (Z.b2z (0 <? ?P)) ?X] =>
             replace (Z.land (Z.b2z (0 <? P)) X) with 0%Z by (rewrite ?T117; vm_compute; reflexivity) end.
      all: zs; br01 K2a; zsto (sym 0x18704 + 1304)%Z; rewrite (nzmask_eq (d_fl d)) by lia; zs; brf K2;
        [ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
        | assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; lia);
          rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
      all: zsto (sym 0x18704 + 1320)%Z; zs; br10 K3; zsto (sym 0x18704 + 1340)%Z.
      all: replace (Z.shiftl (d_t d + -65) 2 + (sym 0x10884))%Z with ((sym 0x10884) + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; lia).
      all: the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1).
      all: zs; zs; zs.
      all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
      all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
      all: rewrite <- (Z_to_bv_bv_unsigned slot), AOK1 in ARGC';
           pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
           stmt (HS_CV_U fuel HH) as NX;
           jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := lv));
           [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
           | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | rewrite <- AOK1; lia ]. }
    all: assert (CT' : conv_type (d_t d) = Some (d_ty d))
           by (destruct CT as [CT | (_ & E)]; [exact CT | exfalso; destruct E as [E|E]; rewrite E in ETY; unfold T_ULLONG, T_SIZET, T_PTR, T_INT, T_UINT, T_DBL in ETY; lia]).
    all: clear CT; rename CT' into CT.
    all: replace (ty_ps (d_ty d)) with 0%Z by (rewrite ETY; reflexivity).
    all: pose proof (conv_type_cases _ _ CT) as CASES; pose proof (conv_type_range _ _ CT) as TR.
    (* [comment removed for export] *)
    1: assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
    2: destruct (Z.eqb_spec (d_t d) 99) as [T99|N99].
    3: assert (TDI : (d_t d = 100 \/ d_t d = 105)%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
    4: assert (TUX : (d_t d = 117 \/ (d_t d = 120 \/ d_t d = 88))%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
    5: assert (TFP : conv_type (d_t d) = Some T_DBL) by (rewrite <- ETY; exact CT).
    5: pose proof (proj1 (conv_type_dbl _ TFP)) as TFR.
    4: destruct TUX as [T117 | TX];
         [ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t d =? 117)%Z with false by (symmetry; apply Z.eqb_neq; lia) ].
    (* [comment removed for export] *)
    all: ienter; zs; br10 K; zs; zs; zs; zs.
    all: callx (eapply pop_arg_callq; [lia | exact APC | exact VAA | exact NTH | lia | exact ARGC | exact ST | exact MI | rewrite ETY; unfold T_PTR, T_INT, T_UINT, T_DBL; lia]).
    all: idtac. (* [comment removed for export] *)
    all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC'; rewrite ETY in ARGC'; cbn [pop_arg_lo pop_arg_hi G_pop_arg.T_PTR G_pop_arg.T_INT G_pop_arg.T_UINT G_pop_arg.T_DBL T_PTR T_INT T_UINT T_DBL Z.eqb Pos.eqb] in ARGC' end.
    all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
    all: zs.
    all: match goal with H : SINK ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => (nelim (SFL _ _ H) 3%nat; intros fb FLC FB) end; zs; zs; zs; br10 K1; clear FLC.
    all: rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
    all: zsto (sym 0x18704 + 1284)%Z; change (Z.b2z (0 <? 0)) with 0%Z; rewrite Z.land_0_l; zs; br01 K2a; zsto (sym 0x18704 + 1304)%Z; rewrite (nzmask_eq (d_fl d)) by lia; zs; brf K2;
      [ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
      | assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; lia);
        rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
    all: zsto (sym 0x18704 + 1320)%Z; zs; br10 K3; zsto (sym 0x18704 + 1340)%Z.
    all: replace (Z.shiftl (d_t d + -65) 2 + (sym 0x10884))%Z with ((sym 0x10884) + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; lia).
    all: first [ the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_d _ _ M TDI) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_c _ _ M T99) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_x _ _ M TX) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_fp _ _ M TFP) as RD1) ].
    all: zs; zs; zs.
    (* [comment removed for export] *)
    all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
    all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mm _) =>
      lazymatch pc with
      | (sym 0x18704 + 1504)%Z => (* [comment removed for export] *)
          rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          match goal with MUc : munch _ m0 mm |- _ =>
            (nelim (arg_ok_W _ _ _ _ AOK1 MUc) 11%nat; intros slack STR SRNG SPAD P0 SD1 SD2 SD3 SD3c SD3e SD4) end;
          stmt (HS_CV_S fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
                                 (xp := d_xp d) (P := bv_unsigned slot) (s := sv) (slack := slack));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | exact P0 | exact SD1 | exact SD2 | exact SD3 | exact SD3c | exact SD3e
          | subst fl'; rewrite ?land_land_same; reflexivity ]
      | (sym 0x18704 + 1432)%Z => (* [comment removed for export] *)
          destruct AOK1 as [Hiv Emod];
          rewrite (sx32_int slot iv Hiv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_D fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hiv ]
      | (sym 0x18704 + 1800)%Z =>
          destruct AOK1 as [Hiv Emod];
          rewrite (sx32_int slot iv Hiv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_C fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
                                 (xp := d_xp d) (i := iv));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hiv
          | subst fl'; rewrite ?land_land_same; reflexivity ]
      | (sym 0x18704 + 1744)%Z => (* [comment removed for export] *)
          destruct AOK1 as [Huv Emod];
          rewrite (zx32_uint slot uv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_U fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ]
      | (sym 0x18704 + 1864)%Z => (* [comment removed for export] *)
          destruct AOK1 as [Huv Emod];
          rewrite (zx32_uint slot uv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_X fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv | exact TX ]
      | (sym 0x18704 + 1352)%Z => (* [comment removed for export] *)
          cbn [arg_ok] in AOK1; rewrite AOK1 in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          unfold LEFT_ADJ, ZERO_PAD in FPC1;
          first [ rewrite (proj2 (Z.eqb_eq _ _) K2) in FPC1 | rewrite (proj2 (Z.eqb_neq _ _) K2') in FPC1 ]; rewrite ?ift, ?iff in FPC1;
          stmt (HS_CV_FP fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (y := f128_of_d dd) (t := d_t d));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | subst fl'; exact FPC1 | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | apply f128_of_d_range | exact TFP ]
      end end.
  Qed.
End PrintfCore.

End Img.
