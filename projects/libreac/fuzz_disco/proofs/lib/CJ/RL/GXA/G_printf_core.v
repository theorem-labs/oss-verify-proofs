(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/CJ/RL/GX/G_printf_core.v, with its module paths changed; 107 of its 1045 lines of code are new or changed and 99 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require SFModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Arr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require SysStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require ITree.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Nodes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Decode.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require PropExec.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec Require Monad.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec Require SoftFloat.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec Require FmtFp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec Require Stdio.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P Require SFW1_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require G_memset.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require G_memcpy.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require G_memchr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require G_strnlen.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require G_fwritex.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require G_pad.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require G_fmt_fp_lib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require G_pop_arg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require Printf_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P Require Printf_mlib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require Printf_zfacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA Require Import AsanFacts SetCall StrnlenCall.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA Require G_printf_core_common.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require StoreCache.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RProgAt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require ProgAt3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require GRoTab.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require NElim.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require JunkAbs.
From Stdlib Require Zify.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RPre.
Module G_printf_core_width.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SFModel OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Arr OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Image OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.FP OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.ITree OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Nodes OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Decode.

Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec.Prelim OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec.Monad OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec.SoftFloat OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec.FmtFp OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec.Stdio OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec.StrFun.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.SFW1_lemmas.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.G_memset OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.G_memcpy OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.G_memchr OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.G_strnlen OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.G_fwritex OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.G_pad OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.G_fmt_fp_lib OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.G_pop_arg.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX.Printf_model OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.Printf_mlib OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX.Printf_zfacts.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.G_printf_core_common.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.Prog_printf_core.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.GRoTab. Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.NElim.   Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.ProgAt2. 
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_printf_core_width : CodeAtT img_segs (sym 0x18704) (printf_core_prog_at IMG)}.
  Context {RB_printf_core_width : RelCode (sym 0x18704) 3632}.
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
  Context {strn_ready : mem -> Z -> Z -> Z -> list byte -> Prop}.
  Context {SPEC_strnlen : strnlen_stack_contract strn_ready}.
  Context {set_ready : mem -> Z -> Z -> Z -> Prop}.
  Context {SPEC_memset : memset_stack_contract set_ready}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)%Z}.
  Let rl0_1 : (sym 0x34288 + 8 <= sym 0x35000)%Z := @zfact_pf _ RL0_1.
  Context {RL1_0 : ZFact (sym 0x22e18 + 240 <= sym 0x34288)%Z}.
  Let rl1_0 : (sym 0x22e18 + 240 <= sym 0x34288)%Z := @zfact_pf _ RL1_0.
  Context {RO_states0 : RoB img_segs (sym 0x109cc) (zb STATES0)}.
  Context {RO_pfx : RoB img_segs (sym 0x1029e) (zb [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z)}.
  Context {RQ_pfx_lo : ZFact (0x10000 <= sym 0x1029e)%Z}.
  Let rq_pfx_lo : (0x10000 <= sym 0x1029e)%Z := @zfact_pf _ RQ_pfx_lo.
  Context {RQ_pfx_got : ZFact (sym 0x1029e + 9 <= sym 0x22e18)%Z}.
  Let rq_pfx_got : (sym 0x1029e + 9 <= sym 0x22e18)%Z := @zfact_pf _ RQ_pfx_got.
  Context {RO_xdigits : RoB img_segs (sym 0x10b9c) (zb XDIGITS)}.
  Collection ImgHyps := IMG CODE_printf_core_width RB_printf_core_width RO_10884 RN_B_fwritex_18704 RN_B_pop_arg_18704 RN_B_fmt_fp_18704 RN_B_errno_location_18704 RN_B_strerror_18704 RN_B_strnlen_18704 RN_B_wctomb_18704 RN_B_pad_18704 RN_B_memset_18704 RN_B_stack_chk_fail_18704 RS_got_ssp RS_K_109cc RS_K_10884 RS_K_1029e RS_K_103b3 RS_K_10964 RS_K_10b9c RS_1029e rp_1029e RS_34288 rp_34288 RS_35000 rp_35000 RL0_0 rl0_0 RL0_1 rl0_1 RL1_0 rl1_0 RO_states0 RO_pfx RQ_pfx_lo rq_pfx_lo RQ_pfx_got rq_pfx_got RO_xdigits.


Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp B BS RC RCS RE RES : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS RC RCS RE RES SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Context {out_ready : mem -> Z -> Z -> Z -> Prop} {INV : mem -> Prop}.
  Hypothesis HOUT : out_a_stmt Fp B BS RC RCS RE RES SINK TOPOK OUT out_ready.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q < 2^63)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  Hypothesis HA : (A + zlength fmt <= sym 0x22e18)%Z.
  Hypothesis SEP_F : (((sym 0x22e18 + 8) <= Fp /\ Fp + 232 <= (sym 0x34288)) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : (AP + 8 <= B /\ B + BS <= VA)%Z.
  Hypothesis SEP_C : (AP + 8 <= RC /\ RC + RCS <= VA)%Z.
  Hypothesis SEP_E : (((sym 0x34288 + 8) <= RE /\ RE + RES <= lo) \/ (VA <= RE /\ VA + 8 * zlength slots <= RE /\ RE + RES <= 2^64) \/ (0 < RE /\ RE + RES <= 65536 /\ 65536 <= A))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  Hypothesis CS0 : (0 <= RCS)%Z.
  Hypothesis ES0 : (0 <= RES)%Z.
  Hypothesis RDY : pc_guard out_ready set_ready strn_ready INV m0 lo q (G_printf_core_common.W Fp B BS RC RCS RE RES q lo AP).
  Hypothesis FMTR : pf_rng m0 A (zlength fmt).
  Hypothesis PFXR : musl_prefix_addressable m0.

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
  Local Notation arg_s_W := (G_printf_core_common.arg_s_W Fp B BS RC RCS RE RES q lo fmt AP slots).
    Local Notation lo_cells14 := (G_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (G_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (G_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (G_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (G_printf_core_common.strnlen_callq Fp B BS RC RCS RE RES q gp tp m0 lo AP LO GLO QHI RDY).
  Local Notation memset_callq := (G_printf_core_common.memset_callq Fp B BS RC RCS RE RES q gp tp m0 lo AP LO GLO QHI RDY).
  Local Notation fmt_rng_sub := (G_printf_core_common.fmt_rng_sub m0 A fmt FMTR).
  Local Notation pfx_rng_sub := (G_printf_core_common.pfx_rng_sub m0 PFXR).
  Local Notation out_postq := (G_printf_core_common.out_postq (St:=St) Fp B BS RC RCS RE RES SINK q gp tp lo canary).
  Local Notation out_callq := (G_printf_core_common.out_callq (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT TOK HOUT q gp tp m0 lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B SEP_C SEP_E HAP HVA BS0 CS0 ES0 RDY).
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
  Local Notation body_loc := (G_printf_core_common.body_loc Fp B BS RC RCS RE RES q m0 lo).
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
  Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.StoreCache.LiaClosure.

Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
 Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RPre.rl_zify_pre_hook.
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].

Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].
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
      | | | | | | | (try (unfold zlength in *; lia)) | (try (unfold zlength in *; lia))
      | match goal with H : munch _ m0 _ |- _ => exact H end
      | match goal with H : wmono _ m0 _ |- _ => exact H end
      | ]
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


  Lemma L_WLOOP : S_WLOOP.
  Proof using HA HF BS0 CS0 ES0 ImgHyps.
    intros x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc w s2 pfx s2s za pl plp alo ahi j128 _
           FI LOW Hpos Hacc DG G NE HK.
    remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
    revert pos acc x5 x6 x12 x14 x15 x16 x17 Hpos Hacc DG G HK Hkk.
    induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
    pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
    pose proof (proj1 (digit_range _) DG) as DGR.
    rewrite (sfx_cons fmt pos) in G by (unfold zlength in *; lia). rewrite (getint_cons_digit _ _ _ DG) in G.
    destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
    apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.
    assert (Hnx : (pos + 1 < zlength fmt)%Z).
    { destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
      rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
    zs. zs. br K.
    zs. zs. try rewrite (swrap32_small (acc * 10)) by lia.
    zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
    rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z.
    zs. try rewrite (lxor_imax (acc * 10)) by lia.
    zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
    zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
    zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
    zs. zs. zs. try rewrite Z.lor_0_l. zs. zs. brf K2.
    -
      assert (ND : is_digit (znth fmt (pos + 1)) = false).
      { destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
      rewrite (sfx_cons fmt (pos + 1)) in G by (unfold zlength in *; lia). rewrite (getint_cons_nondigit _ _ _ ND) in G.
      injection G as Ew Es2.
      zs. br K3.
      jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
      rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
    -
      assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
      jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
      intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
  Qed.

  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
  Proof using HA HF BS0 CS0 ES0 ImgHyps.
    intros HWL x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k1 w s2 pfx s2s za pl plp alo ahi j128 _
           FI LOW Hk1 G NE HK.
    pose proof FI as FI'. dest_finv FI.
    pose proof (fmt_rng k1 ltac:(zl)) as RG1.
    zs. zs. zs. zs. brf K.
    -
      assert (ND : is_digit (znth fmt k1) = false).
      { destruct (is_digit (znth fmt k1)) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG1)) in E. lia. }
      rewrite (sfx_cons fmt k1) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G. injection G as Ew Es2.
      subst w. jump (apply (HK k1); [zl | | exact ND | unfold INT_MAX; lia]).
      rewrite (sfx_cons fmt k1) by zl. symmetry. exact Es2.
    - assert (DG : is_digit (znth fmt k1) = true) by (apply (proj1 (digit_test _ RG1)); lia).
      zs. zs.
      stmt HWL as NXL. jump (eapply NXL with (pos := k1) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact DG | exact G | exact NE | ]).
      intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
  Qed.
End PrintfCore.

End Img.
End G_printf_core_width.


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Bytes PropExec.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require Import G_memset G_memcpy G_memchr G_strnlen G_fwritex G_pad G_fmt_fp_lib. From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require Import G_pop_arg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P Require Import Printf_mlib. From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require Import Printf_model Printf_zfacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require Import G_pop_arg_x.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA Require G_printf_core_common.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA Require G_printf_core_exit G_printf_core_end G_printf_core_exit1 G_printf_core_scan G_printf_core_flags.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA Require G_printf_core_cvc.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA Require G_printf_core_precs G_printf_core_dirs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA Require G_printf_core_prec G_printf_core_state G_printf_core_dir G_printf_core_t6 G_printf_core_t5 G_printf_core_t4 G_printf_core_t3 G_printf_core_t2 G_printf_core_t1 G_printf_core_tail G_printf_core_intc2 G_printf_core_intc G_printf_core_dloop G_printf_core_fmtu2 G_printf_core_fmtu G_printf_core_cvd G_printf_core_cvu G_printf_core_xloop G_printf_core_cvx G_printf_core_cvs G_printf_core_cvfp G_printf_core_conv G_printf_core_head G_printf_core_p1 G_printf_core_pro.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA Require Export G_printf_core_common.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require ProgAt3.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.Prog_printf_core.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require Import GRoTab. From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Import NElim. From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require ProgAt3.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.ProgAt2. From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_printf_core : CodeAtT img_segs (sym 0x18704) (printf_core_prog_at IMG)}.
  Context {RB_printf_core : RelCode (sym 0x18704) 3632}.
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
  Context {strn_ready : mem -> Z -> Z -> Z -> list byte -> Prop}.
  Context {SPEC_strnlen : strnlen_stack_contract strn_ready}.
  Context {set_ready : mem -> Z -> Z -> Z -> Prop}.
  Context {SPEC_memset : memset_stack_contract set_ready}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)%Z}.
  Let rl0_1 : (sym 0x34288 + 8 <= sym 0x35000)%Z := @zfact_pf _ RL0_1.
  Context {RL1_0 : ZFact (sym 0x22e18 + 240 <= sym 0x34288)%Z}.
  Let rl1_0 : (sym 0x22e18 + 240 <= sym 0x34288)%Z := @zfact_pf _ RL1_0.
  Context {RO_states0 : RoB img_segs (sym 0x109cc) (zb STATES0)}.
  Context {RO_pfx : RoB img_segs (sym 0x1029e) (zb [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z)}.
  Context {RQ_pfx_lo : ZFact (0x10000 <= sym 0x1029e)%Z}.
  Let rq_pfx_lo : (0x10000 <= sym 0x1029e)%Z := @zfact_pf _ RQ_pfx_lo.
  Context {RQ_pfx_got : ZFact (sym 0x1029e + 9 <= sym 0x22e18)%Z}.
  Let rq_pfx_got : (sym 0x1029e + 9 <= sym 0x22e18)%Z := @zfact_pf _ RQ_pfx_got.
  Context {RO_xdigits : RoB img_segs (sym 0x10b9c) (zb XDIGITS)}.
  Context {RO_states : RoB img_segs (sym 0x109cc) (zb STATES)}.
  Context {SPEC_pop_arg_x : pop_arg_x_contract}.
  Collection ImgHyps := IMG CODE_printf_core RB_printf_core RO_10884 RN_B_fwritex_18704 RN_B_pop_arg_18704 RN_B_fmt_fp_18704 RN_B_errno_location_18704 RN_B_strerror_18704 RN_B_strnlen_18704 RN_B_wctomb_18704 RN_B_pad_18704 RN_B_memset_18704 RN_B_stack_chk_fail_18704 RS_got_ssp RS_K_109cc RS_K_10884 RS_K_1029e RS_K_103b3 RS_K_10964 RS_K_10b9c RS_1029e rp_1029e RS_34288 rp_34288 RS_35000 rp_35000 RL0_0 rl0_0 RL0_1 rl0_1 RL1_0 rl1_0 RO_states0 RO_pfx RQ_pfx_lo rq_pfx_lo RQ_pfx_got rq_pfx_got RO_xdigits RO_states.


Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp B BS RC RCS RE RES : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS RC RCS RE RES SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Context {out_ready : mem -> Z -> Z -> Z -> Prop} {INV : mem -> Prop}.
  Hypothesis HOUT : out_a_stmt Fp B BS RC RCS RE RES SINK TOPOK OUT out_ready.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q < 2^63)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  Hypothesis HA : (A + zlength fmt <= sym 0x22e18)%Z.
  Hypothesis SEP_F : (((sym 0x22e18 + 8) <= Fp /\ Fp + 232 <= (sym 0x34288)) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : (AP + 8 <= B /\ B + BS <= VA)%Z.
  Hypothesis SEP_C : (AP + 8 <= RC /\ RC + RCS <= VA)%Z.
  Hypothesis SEP_E : (((sym 0x34288 + 8) <= RE /\ RE + RES <= lo) \/ (VA <= RE /\ VA + 8 * zlength slots <= RE /\ RE + RES <= 2^64) \/ (0 < RE /\ RE + RES <= 65536 /\ 65536 <= A))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  Hypothesis CS0 : (0 <= RCS)%Z.
  Hypothesis ES0 : (0 <= RES)%Z.
  Hypothesis RDY : pc_guard out_ready set_ready strn_ready INV m0 lo q (G_printf_core_common.W Fp B BS RC RCS RE RES q lo AP).
  Hypothesis FMTR : pf_rng m0 A (zlength fmt).
  Hypothesis PFXR : musl_prefix_addressable m0.

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
  Local Notation arg_s_W := (G_printf_core_common.arg_s_W Fp B BS RC RCS RE RES q lo fmt AP slots).
    Local Notation lo_cells14 := (G_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (G_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (G_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (G_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (G_printf_core_common.strnlen_callq Fp B BS RC RCS RE RES q gp tp m0 lo AP LO GLO QHI RDY).
  Local Notation memset_callq := (G_printf_core_common.memset_callq Fp B BS RC RCS RE RES q gp tp m0 lo AP LO GLO QHI RDY).
  Local Notation fmt_rng_sub := (G_printf_core_common.fmt_rng_sub m0 A fmt FMTR).
  Local Notation pfx_rng_sub := (G_printf_core_common.pfx_rng_sub m0 PFXR).
  Local Notation out_postq := (G_printf_core_common.out_postq (St:=St) Fp B BS RC RCS RE RES SINK q gp tp lo canary).
  Local Notation out_callq := (G_printf_core_common.out_callq (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT TOK HOUT q gp tp m0 lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B SEP_C SEP_E HAP HVA BS0 CS0 ES0 RDY).
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
  Local Notation S_PRECS := ((GLRUN1 (G_printf_core_common.S_PRECS Fp B BS RC RCS RE RES))).
  Local Notation S_DIRS := ((GLRUN1 (G_printf_core_common.S_DIRS Fp B BS RC RCS RE RES))).
  Local Notation S_END := ((GLRUN1 (G_printf_core_common.S_END (St:=St) Fp B BS RC RCS RE RES SINK))).
  Local Notation S_HEAD := ((GLRUN1 (G_printf_core_common.S_HEAD (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation S_CONV := ((GLRUN1 (G_printf_core_common.S_CONV (St:=St) Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP))).
  Local Notation body_loc := (G_printf_core_common.body_loc Fp B BS RC RCS RE RES q m0 lo).
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
  Local Ltac lia ::= lia3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.StoreCache.LiaClosure.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
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
      | | | | | | | (try (unfold zlength in *; lia)) | (try (unfold zlength in *; lia))
      | match goal with H : munch _ m0 _ |- _ => exact H end
      | match goal with H : wmono _ m0 _ |- _ => exact H end
      | ]
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

  Lemma L_EXIT : S_EXIT.
  Proof using HA LO BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_exit.L_EXIT; first [eassumption]
          | intros; eapply G_printf_core_exit.L_EXIT; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_END : S_END.
  Proof using HA GLO HAP LO SEP_F VAHI BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_end.L_END; first [eassumption | eexact L_EXIT]
          | intros; eapply G_printf_core_end.L_END; first [eassumption | eexact L_EXIT] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_EXIT1 : S_EXIT1.
  Proof using HA LO BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_exit1.L_EXIT1; first [eassumption]
          | intros; eapply G_printf_core_exit1.L_EXIT1; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_SCAN : S_SCAN.
  Proof using A0 HA HF BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_scan.L_SCAN; first [eassumption]
          | intros; eapply G_printf_core_scan.L_SCAN; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FLAGS : S_FLAGS.
  Proof using HA HF BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_flags.L_FLAGS; first [eassumption]
          | intros; eapply G_printf_core_flags.L_FLAGS; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_WLOOP : S_WLOOP.
  Proof using HA HF BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_width.L_WLOOP; first [eassumption]
          | intros; eapply G_printf_core_width.L_WLOOP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
  Proof using HA HF BS0 CS0 ES0 ImgHyps.
    first [ intro; apply G_printf_core_width.L_WIDTH; first [eassumption]
          | intros; eapply G_printf_core_width.L_WIDTH; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PLOOP : S_PLOOP.
  Proof using HA HF BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_prec.L_PLOOP; first [eassumption]
          | intros; eapply G_printf_core_prec.L_PLOOP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PREC : S_PLOOP -> S_PREC.
  Proof using HA HF BS0 CS0 ES0 ImgHyps.
    first [ intro; apply G_printf_core_prec.L_PREC; first [eassumption]
          | intros; eapply G_printf_core_prec.L_PREC; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_STATE : S_STATE.
  Proof using HA HF BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_state.L_STATE; first [eassumption]
          | intros; eapply G_printf_core_state.L_STATE; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DIR : S_DIR.
  Proof using HA HF BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE]
          | intros; eapply G_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PRECS : S_PRECS.
  Proof using HA HF BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_precs.L_PRECS; first [eassumption]
          | intros; eapply G_printf_core_precs.L_PRECS; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DIRS : S_DIRS.
  Proof using HA HF BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_dirs.L_DIRS; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact L_PRECS]
          | intros; eapply G_printf_core_dirs.L_DIRS; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact L_PRECS] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T6 : S_T6.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_t6.L_T6; first [eassumption]
          | intros; eapply G_printf_core_t6.L_T6; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T5 : S_T5.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_t5.L_T5; first [eassumption | eexact L_T6]
          | intros; eapply G_printf_core_t5.L_T5; first [eassumption | eexact L_T6] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T4 : S_T4.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_t4.L_T4; first [eassumption | eexact L_T5]
          | intros; eapply G_printf_core_t4.L_T4; first [eassumption | eexact L_T5] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T3 : S_T3.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_t3.L_T3; first [eassumption | eexact L_T4]
          | intros; eapply G_printf_core_t3.L_T3; first [eassumption | eexact L_T4] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T2 : S_T2.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_t2.L_T2; first [eassumption | eexact L_T3]
          | intros; eapply G_printf_core_t2.L_T2; first [eassumption | eexact L_T3] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T1 : S_T1.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_t1.L_T1; first [eassumption | eexact L_T2]
          | intros; eapply G_printf_core_t1.L_T1; first [eassumption | eexact L_T2] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_TAIL : S_TAIL.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
          | intros; eapply G_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_INTC2 : S_INTC2.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL]
          | intros; eapply G_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_INTC : S_INTC.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2]
          | intros; eapply G_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DLOOP : S_DLOOP.
  Proof using HA GLO LO QHI BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_dloop.L_DLOOP; first [eassumption]
          | intros; eapply G_printf_core_dloop.L_DLOOP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FMTU2 : S_FMTU2.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC]
          | intros; eapply G_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FMTU : S_FMTU.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
          | intros; eapply G_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_D : S_CV_D.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU]
          | intros; eapply G_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_U : S_CV_U.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU]
          | intros; eapply G_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_XLOOP : S_XLOOP.
  Proof using HA GLO LO QHI BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_xloop.L_XLOOP; first [eassumption]
          | intros; eapply G_printf_core_xloop.L_XLOOP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_X : S_CV_X.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
          | intros; eapply G_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_S : S_CV_S.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL]
          | intros; eapply G_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_C : S_CV_C.
  Proof using BS0 CS0 ES0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_cvc.L_CV_C; first [eassumption | eexact L_TAIL]
          | intros; eapply G_printf_core_cvc.L_CV_C; first [eassumption | eexact L_TAIL] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_FP : S_CV_FP.
  Proof using GLO HA HAP HVA LO QHI SEP_B SEP_C SEP_E SEP_F TOK TQ BS0 CS0 ES0 ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_cvfp.L_CV_FP; first [eassumption]
          | intros; eapply G_printf_core_cvfp.L_CV_FP; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CONV : S_CONV.
  Proof using BS0 CS0 ES0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ apply G_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP | eexact L_CV_C]
          | intros; eapply G_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP | eexact L_CV_C] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using A0 BS0 CS0 ES0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_C SEP_E SEP_F SFL SFR TOK TQ VAHI ImgHyps RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x.
    first [ intro; apply G_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_DIRS | eexact L_STATE | eexact L_CONV | eexact L_END]
          | intros; eapply G_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_DIRS | eexact L_STATE | eexact L_CONV | eexact L_END] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_P1 : S_P1.
  Proof using A0 HA HF LO BS0 CS0 ES0 ImgHyps.
    first [ apply G_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_DIRS | eexact L_STATE | eexact L_EXIT1]
          | intros; eapply G_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_DIRS | eexact L_STATE | eexact L_EXIT1] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PRO : S_PRO.
  Proof using BS0 CS0 ES0 GLO HA HAP HVA LO QHI ImgHyps.
    first [ apply G_printf_core_pro.L_PRO; first [eassumption]
          | intros; eapply G_printf_core_pro.L_PRO; first [eassumption] ].
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.

  Let HS_PRO := L_PRO.
  Let HS_HEAD := L_HEAD.
  Let HS_P1 := L_P1.
  
  Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
      let _ := ctx_all in
      SINK m0 st -> stk img_segs m0 lo q -> mem_inv img_segs m0 -> bytes_at img_segs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      rw_cells img_segs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
      args_ok Fp B BS RC RCS RE RES m0 lo q AP (skipn (Z.to_nat i) slots) args ->
      Forall (fpcall_stmt Fp B BS RC RCS RE RES SINK TOPOK OUTFP) (fp_calls (length fmt) fmt args) ->
      (0 < Fp)%Z -> (Fp + 232 <= 2^64)%Z ->
      implM img_segs (printf_model OUT OUTFP fmt args) st POST
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 (sym 0x18704)) fc0 None m0 (seg_rom img_segs)).
  Proof using HA FRM0 HS_HEAD HS_PRO BS0 CS0 ES0 RDY FMTR PFXR SPEC_memset SPEC_strnlen SPEC_pop_arg SPEC_pop_arg_x ImgHyps.
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 st i args _ HS0 ST0 MI0 BY0 VAA0 SSP0 APC0 Hi AOK FPC HF0 HF1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    unfold printf_model. ienter.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Fp); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    pose proof FI as FI'. (nelim FI' 4%nat; intros MI MU WM _).
    assert (HS : SINK m st).
    { eapply (SFR [(q + -544, q)]%Z m0 m st HS0 MUq WM); (apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]). }
    assert (APC : rw_cells img_segs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
    { eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
    stmt (HS_HEAD (length fmt)) as NXH.
    jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
      [ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
      | exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.

  Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
      let _ := ctx_all in
      stk img_segs m0 lo q -> mem_inv img_segs m0 -> bytes_at img_segs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      pass1_ok fmt = true ->
      evt img_segs (POST1 0)
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 (sym 0x18704)) fc0 None m0 (seg_rom img_segs)).
  Proof using HA HS_P1 HS_PRO BS0 CS0 ES0 ImgHyps.
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 _ ST0 MI0 BY0 VAA0 SSP0 P1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 0%Z); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    stmt HS_P1 as NX1.
    jump (eapply NX1; [ exact FI | eapply munch_weaken; [|exact MUq]; unfold sub_fp; cbn [outside]; intros; lia | exact LOW | exact DIG | exact PAD | exact P1 ]).
  Qed.

End PrintfCore.


Theorem printf_core_a_proof : forall (St : Type) (Fp B BS RC RCS RE RES : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
    (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z) (out_ready : mem -> Z -> Z -> Z -> Prop) (INV : mem -> Prop),
  sink_frame_stmt Fp B BS RC RCS RE RES SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK ->
  out_a_stmt Fp B BS RC RCS RE RES SINK TOPOK OUT out_ready ->
  printf_core_a_stmt Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP out_ready set_ready strn_ready INV.
Proof.
  intros St Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP out_ready INV SFR SFL TOK HOUT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary fmt VA i slots args
         HS BY HF Ha0 APC VAA Hi AOK FPC ST LO GLO SPHI TQ SSP MI FRM HA BS0 SEPF SEPB CS0 ES0 SEPC SEPE HAP HVA VAHI FMR PFX GRD.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  pose proof (L_CORE2 Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) VA slots a3 a4 HF LO GLO SPHI TQ FRM HA SEPF SEPB SEPC SEPE HAP HVA (proj1 Ra1) VAHI BS0 CS0 ES0
                      GRD FMR PFX
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 st i args HS ST MI BY VAA SSP APC Hi AOK FPC) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply implM_mono.
  { apply C; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; lia. }
  cbv beta. intros r st' ms' P. unfold POST, W in P. unfold printf_core_a_post, SR.
  (nelim P 29%nat; intros x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 Ft fc' apv m' -> MU WM MI' FRM' FOK ST' HS' SSP' APC' Hr).
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', apv, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]).
  exact (proj1 (GRD m' MU WM)).
Qed.

Theorem printf_core1_a_proof : forall (INV : mem -> Prop), printf_core1_a_stmt INV.
Proof.
  intros INV ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
         BY HF P1 Ha0 ST LO GLO SPHI SSP MI HA HAP A2HI GRD.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
  unshelve epose proof (L_CORE1 0 0 0 0 0 0 0 ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) (bv_unsigned a2 + 8)%Z [] a3 a4 HF
                      _ _ SPHI HA HAP _ (proj1 Ra1) _ _ _
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ST MI BY) as C.
  1-6: (unfold PC_DEPTH, GLOBALS_TOP in *; lia).
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply evt_mono.
  { apply C; [ | exact SSP | exact P1 ]. unfold va_area. cbn [u64s map concat]. apply bytes_at_nil; lia. }
  cbv beta. intros ms' P. unfold POST1 in P. unfold printf_core1_a_post.
  (nelim P 21%nat; intros x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m' -> MU WM MI' ST' SSP').
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]).
  exact (GRD m' MU WM).
Qed.

End Img.
