(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require SFModel Arr SysStep ImageA FP ITree Nodes Decode.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Bytes PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Printf_mlib Printf_zfacts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require FX_lib F_memset F_memcpy F_memchr I_strnlen F_fwritex F_pop_arg F_printf_iface.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require PrintfModel.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require F_printf_core_common.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require IcptSpec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require R_m2s I_consts F_achk.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import SFModel Arr SysStep ImageA FP ITree Nodes Decode.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Printf_mlib Printf_zfacts.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.FX_lib.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_memset.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_memcpy.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_memchr.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_strnlen.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_fwritex.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_iface.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import PrintfModel. (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import IcptSpec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_consts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_achk.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Definition zpk (P : Prop) : Prop := P.
Local Ltac zpark H := let T := type of H in change (zpk T) in H.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
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
  Hypothesis HA : (A + zlength fmt <= 835584)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((856512 <= Fp /\ Fp + 232 <= 864256) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((6460704 <= B /\ B + BS <= lo /\ B + BS <= 6467584) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  (* [comment removed for export] *)
  Hypothesis RIP : rip_stmt.
  Hypothesis HA0 : aext m0 lo q A fmt B BS.

  (* [comment removed for export] *)
  Local Notation ctx_all := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.W Fp B BS q lo AP).
  Local Notation Fok := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.Fok F).
  Local Notation Fok_refl := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.Fok_refl F).
  Local Notation Fok_trans := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.Fok_trans F).
  Local Notation POST := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.lo_cells AP nla nlt).
  Local Notation finv := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.implM_eq_ms (St:=St)).
  Local Notation sink_store := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.arg_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
  Local Notation args_ok_W := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.args_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
  Local Notation lo_cells14 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.lo_cells14 AP nla nlt).
  Local Notation lo_split := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.lo_split q AP nla nlt).
  Local Notation lo_join := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.strnlen_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
  Local Notation out_postq := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp m0 lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0 HA0).
  Local Notation memset_callq := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.memset_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
  Local Notation memset_postq := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.memset_postq q gp tp lo).
  Local Notation chkr_W := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.chkr_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
  Local Notation ictx_W := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.ictx_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
  Local Notation hsh := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.hsh B BS q m0 lo A fmt HA0).
  Local Notation chkr_stack0 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.chkr_stack0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_fmt0 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.chkr_fmt0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_pfx0 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.chkr_pfx0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_xdig0 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.chkr_xdig0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_nulls0 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.chkr_nulls0 B BS q m0 lo A fmt HA0).
  Local Notation arg_ok_chk := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.arg_ok_chk Fp B BS).
  Local Notation chkr_buf0 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.chkr_buf0 B BS q m0 lo A fmt HA0).
  Local Notation fp_postq := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.tregs Fp q gp tp A).
  Local Notation tinv := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.dloop_post q gp tp).
  Local Notation S_DLOOP := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.xloop_post q gp tp).
  Local Notation S_XLOOP := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_printf_core_common.TwinB__.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).
  Ltac hush := idtac.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
  (* [comment removed for export] *)
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
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
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
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
        first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
    end.
  Local Ltac transport_call_extra segs W m m' MU WM ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ eapply (sink_call W m m' st) in H;
                [ | exact MU | exact WM
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    end.
  Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
  Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
  Local Ltac mem_after_store ::= mem_after_store_fast.
  Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
  Local Ltac lia ::= lia3.
  (* [comment removed for export] *)
  Local Ltac br K ::= brf K; try (exfalso; first [ zify_prune_plain; Zify.zify; xlia zchecker | revert K; sf_unhide; dj_prune; intros K; Zify.zify; xlia zchecker ]).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Hypothesis HS_CV_D : S_CV_D.
  Hypothesis HS_CV_U : S_CV_U.
  Hypothesis HS_CV_X : S_CV_X.
  Hypothesis HS_CV_S : S_CV_S.
  Hypothesis HS_CV_FP : S_CV_FP.

  (* [comment removed for export] *)
  Lemma L_CONV : S_CONV.
  Proof using BS0 GLO HA HAP HF HS_CV_D HS_CV_FP HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_F SFL SFR VAHI HA0 RIP.
    intros fuel HH x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Ht CT Hfl Hw Hp XP Hc.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
    (* [comment removed for export] *)
    assert (FpR : (0 <= Fp < 2^64)%Z) by (clear - SEP_F HVA VAHI HAP QHI LO GLO; unfold zlength, PC_DEPTH, GLOBALS_TOP in *; lia).
    (* [comment removed for export] *)
    cbn [args_ok] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [AOK1 AOK].
    assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
    { rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
    assert (ESK' : skipn (Z.to_nat (k + 1)) slots = slots').
    { replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
    rewrite <- ESK' in AOK.
    destruct (lo_split _ _ _ _ _ _ _ _ _ _ LOW) as (LOW14 & ARGC & J128). unfold lo_cells14, ssp_guard in LOW14. clear LOW.
    pose proof (dir_tyok_cases _ CT) as CASES.
    assert (TR : (65 <= d_t d <= 122)%Z) by (unfold T_PTR, T_INT, T_UINT, OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET in CASES; lia).
    pose proof (land_bound' (d_fl d) 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq (d_fl d)) in FLB by lia.
    (* [comment removed for export] *)
    pose proof (dir_ps_cases _ CT) as PSC.
    unfold conv. cbv zeta. unfold LEFT_ADJ, ZERO_PAD.
    (* [comment removed for export] *)
    destruct a as [sv | | iv | uv | zv | dd];
      [ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) PrintfModel.T_SIZET) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_DBL) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l] ].
    (* [comment removed for export] *)
    6: { exfalso. unfold T_PTR, T_INT, T_UINT, T_DBL, OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET, PrintfModel.T_DBL in CASES, ETY; lia. }
    (* [comment removed for export] *)
    1: assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET in CASES, ETY; lia).
    2: assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET in CASES, ETY; lia).
    3: assert (TDI : (d_t d = 100 \/ d_t d = 105)%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET in CASES, ETY; lia).
    4: assert (TUX : (d_t d = 117 \/ (d_t d = 120 \/ d_t d = 88))%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET in CASES, ETY; lia).
    5: assert (T117 : d_t d = 117%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET in CASES, ETY; lia).
    1-4: assert (PS0 : dir_ps d = 0%Z) by (destruct PSC as [[P _] | (P & _ & E)]; [exact P | exfalso; unfold T_PTR, T_INT, T_UINT, T_SIZET in E, ETY; lia]).
    5: assert (PS6 : dir_ps d = 6%Z) by (destruct PSC as [[P CT0] | (P & _ & _)]; [exfalso; pose proof (conv_type_ty _ _ CT0) as TY0; unfold T_SIZET in ETY; lia | rewrite P; reflexivity]).
    1-4: rewrite PS0. 5: rewrite PS6.
    5: rewrite (proj2 (Z.eqb_eq _ _) T117).
    4: destruct TUX as [T117 | TX];
         [ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t d =? 117)%Z with false by (symmetry; apply Z.eqb_neq; lia) ].
    (* [comment removed for export] *)
    all: ienter; zs; br K; zs; zs; zs; zs.
    (* [comment removed for export] *)
    all: try zpark ARGC; try zpark APC; try zpark ST.
    all: callw (eapply pop_arg_callq; [lia | exact APC | exact VAA | exact NTH | lia | exact ARGC | exact ST | exact MI | rewrite ETY; unfold T_PTR, T_INT, T_UINT, T_DBL, OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET; lia]).
    all: try clear ARGC APC ST.
    all: try fix_stk.
    all: idtac.
    all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC'; rewrite ETY in ARGC'; cbn [pop_arg_lo pop_arg_hi OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__.T_PTR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__.T_INT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__.T_UINT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_pop_arg.TwinB__.T_SIZET T_PTR T_INT T_UINT T_DBL PrintfModel.T_PTR PrintfModel.T_INT PrintfModel.T_UINT PrintfModel.T_SIZET Z.eqb Pos.eqb] in ARGC' end.
    all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
    all: zs.
    all: match goal with H : SINK ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB) end; zs; zs; zs; br K1; clear FLC.
    all: rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
    (* [comment removed for export] *)
    6: rewrite T117.
    1-5: zsto 0xc3054%Z; change (Z.b2z (0 <? 0)) with 0%Z; rewrite Z.land_0_l; zs; br K2a.
    6: zsto 0xc3054%Z;
       (let r := getreg 10%Z in lazymatch r with Z_to_bv 64 ?e => let v := eval vm_compute in e in change (Z_to_bv 64 e) with (Z_to_bv 64 v) end);
       zs; br K2a.
    all: zsto 0xc3068%Z; rewrite (nzmask_eq (d_fl d)) by lia; zs; brf K2;
      [ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
      | assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; lia);
        rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
    all: zsto 0xc3078%Z; zs; br K3; zsto 0xc308c%Z.
    1-10: replace (Z.shiftl (d_t d + -65) 2 + 143816)%Z with (143816 + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; lia).
    all: first [ the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_d _ _ M TDI) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_x _ _ M TX) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1; pose proof RD1 as RD1';
                                      rewrite T117 in RD1'; replace (143816 + 4 * (117 - 65))%Z with 144024%Z in RD1' by reflexivity) ].
    all: zs; zs; zs.
    (* [comment removed for export] *)
    all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
    all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mm _) =>
      lazymatch type of AOK1 with
      | arg_ok _ _ _ _ _ _ _ _ (PA_s _) => (* [comment removed for export] *)
            rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
            pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
            match goal with MUc : munch _ m0 mm |- _ =>
              destruct (arg_ok_W _ _ _ _ AOK1 MUc) as (slack & STR & SRNG & SPAD & P0 & SD1 & SD2 & SD3 & SD4 & CKc) end;
            stmt (HS_CV_S fuel HH) as NX;
            jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
                                   (xp := d_xp d) (PV := bv_unsigned slot) (P := bv_unsigned slot) (s := sv) (slack := slack));
            [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
            | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | left; split; [reflexivity | exact P0] | exact SD1 | exact SD2 | exact SD3
            | subst fl'; rewrite ?land_land_same; reflexivity | exact (arg_ok_chk _ _ _ _ _ _ AOK1) ]
      | arg_ok _ _ _ _ _ _ _ _ PA_sn => (* [comment removed for export] *)
            cbn [arg_ok] in AOK1;
            rewrite <- (Z_to_bv_bv_unsigned slot), AOK1 in ARGC';
            pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
            match goal with MIc : mem_inv _ mm |- _ =>
              destruct (nullstr_arg_ok mm slot MIc AOK1) as (slack & STR & SRNG & SPAD & SD1 & SD2 & SD3) end;
            stmt (HS_CV_S fuel HH) as NX;
            jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
                                   (xp := d_xp d) (PV := 0%Z) (P := A_NULLSTR) (s := NULLSTR) (slack := slack));
            [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
            | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | right; split; reflexivity | exact SD1 | exact SD2 | exact SD3
            | subst fl'; rewrite ?land_land_same; reflexivity | exact chkr_nulls0 ]
      | arg_ok _ _ _ _ _ _ _ _ (PA_i _) => (* [comment removed for export] *)
          destruct AOK1 as [Hiv Emod];
          rewrite (sx32_int slot iv Hiv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_D fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hiv ]
      | arg_ok _ _ _ _ _ _ _ _ (PA_u _) =>
        lazymatch pc with
        | 799264%Z => (* [comment removed for export] *)
            destruct AOK1 as [Huv Emod];
            rewrite (zx32_uint slot uv Emod) in ARGC';
            pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
            stmt (HS_CV_U fuel HH) as NX;
            jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
            [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
            | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ]
        | 799384%Z => (* [comment removed for export] *)
          destruct AOK1 as [Huv Emod];
          rewrite (zx32_uint slot uv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_X fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv | exact TX ]
        end
      | arg_ok _ _ _ _ _ _ _ _ (PA_z _) => (* [comment removed for export] *)
            cbn [arg_ok] in AOK1;
            pose proof (bv_unsigned_in_range 64 slot) as ZR; unfold bv_modulus in ZR;
            rewrite <- (Z_to_bv_bv_unsigned slot), AOK1 in ARGC';
            pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
            stmt (HS_CV_U fuel HH) as NX;
            jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := zv));
            [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
            | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | rewrite <- AOK1; change (2^64)%Z with 18446744073709551616%Z; cbn in ZR; lia ]
      end end.
  Qed.
End PrintfCore.
End TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import SFModel Arr SysStep ImageA FP ITree Nodes Decode.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Bytes PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Monad PrintfModel StrFun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Printf_mlib Printf_zfacts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import FX_lib F_memset F_memcpy F_memchr I_strnlen F_fwritex F_pop_arg F_printf_iface.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import PrintfModel. (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import F_printf_core_common.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import R_m2s I_consts IcptSpec F_achk.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Definition zpk (P : Prop) : Prop := P.
Local Ltac zpark H := let T := type of H in change (zpk T) in H.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
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
  Hypothesis HA : (A + zlength fmt <= 782336)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((802272 <= Fp /\ Fp + 232 <= 811008) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((6406432 <= B /\ B + BS <= lo /\ B + BS <= 6414336) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  (* [comment removed for export] *)
  Hypothesis RIP : rip_stmt.
  Hypothesis HA0 : aext m0 lo q A fmt B BS.

  (* [comment removed for export] *)
  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp m0 lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0 HA0).
  Local Notation memset_callq := (F_printf_core_common.memset_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
  Local Notation memset_postq := (F_printf_core_common.memset_postq q gp tp lo).
  Local Notation chkr_W := (F_printf_core_common.chkr_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
  Local Notation ictx_W := (F_printf_core_common.ictx_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
  Local Notation hsh := (F_printf_core_common.hsh B BS q m0 lo A fmt HA0).
  Local Notation chkr_stack0 := (F_printf_core_common.chkr_stack0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_fmt0 := (F_printf_core_common.chkr_fmt0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_pfx0 := (F_printf_core_common.chkr_pfx0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_xdig0 := (F_printf_core_common.chkr_xdig0 B BS q m0 lo A fmt HA0).
  Local Notation chkr_nulls0 := (F_printf_core_common.chkr_nulls0 B BS q m0 lo A fmt HA0).
  Local Notation arg_ok_chk := (F_printf_core_common.arg_ok_chk Fp B BS).
  Local Notation chkr_buf0 := (F_printf_core_common.chkr_buf0 B BS q m0 lo A fmt HA0).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation nullstr_arg_ok := (F_printf_core_common.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
  Local Notation S_CV_S2 := (F_printf_core_common.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).
  Ltac hush := idtac.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
  (* [comment removed for export] *)
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
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
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
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
        first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
    end.
  Local Ltac transport_call_extra segs W m m' MU WM ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ eapply (sink_call W m m' st) in H;
                [ | exact MU | exact WM
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    end.
  Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
  Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
  Local Ltac mem_after_store ::= mem_after_store_fast.
  Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
  Local Ltac lia ::= lia3.
  (* [comment removed for export] *)
  Local Ltac br K ::= brf K; try (exfalso; first [ zify_prune_plain; Zify.zify; xlia zchecker | revert K; sf_unhide; dj_prune; intros K; Zify.zify; xlia zchecker ]).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Hypothesis HS_CV_D : S_CV_D.
  Hypothesis HS_CV_U : S_CV_U.
  Hypothesis HS_CV_X : S_CV_X.
  Hypothesis HS_CV_S : S_CV_S.
  Hypothesis HS_CV_FP : S_CV_FP.

  (* [comment removed for export] *)
  Lemma L_CONV : S_CONV.
  Proof using BS0 GLO HA HAP HF HS_CV_D HS_CV_FP HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_F SFL SFR VAHI HA0 RIP.
    intros fuel HH x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Ht CT Hfl Hw Hp XP Hc.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
    (* [comment removed for export] *)
    assert (FpR : (0 <= Fp < 2^64)%Z) by (clear - SEP_F HVA VAHI HAP QHI LO GLO; unfold zlength, PC_DEPTH, GLOBALS_TOP in *; lia).
    (* [comment removed for export] *)
    cbn [args_ok] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [AOK1 AOK].
    assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
    { rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
    assert (ESK' : skipn (Z.to_nat (k + 1)) slots = slots').
    { replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
    rewrite <- ESK' in AOK.
    destruct (lo_split _ _ _ _ _ _ _ _ _ _ LOW) as (LOW14 & ARGC & J128). unfold lo_cells14, ssp_guard in LOW14. clear LOW.
    pose proof (dir_tyok_cases _ CT) as CASES.
    assert (TR : (65 <= d_t d <= 122)%Z) by (unfold T_PTR, T_INT, T_UINT, F_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET in CASES; lia).
    pose proof (land_bound' (d_fl d) 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq (d_fl d)) in FLB by lia.
    (* [comment removed for export] *)
    pose proof (dir_ps_cases _ CT) as PSC.
    unfold conv. cbv zeta. unfold LEFT_ADJ, ZERO_PAD.
    (* [comment removed for export] *)
    destruct a as [sv | | iv | uv | zv | dd];
      [ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) PrintfModel.T_SIZET) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_DBL) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l] ].
    (* [comment removed for export] *)
    6: { exfalso. unfold T_PTR, T_INT, T_UINT, T_DBL, F_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET, PrintfModel.T_DBL in CASES, ETY; lia. }
    (* [comment removed for export] *)
    1: assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, F_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET in CASES, ETY; lia).
    2: assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, F_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET in CASES, ETY; lia).
    3: assert (TDI : (d_t d = 100 \/ d_t d = 105)%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, F_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET in CASES, ETY; lia).
    4: assert (TUX : (d_t d = 117 \/ (d_t d = 120 \/ d_t d = 88))%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, F_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET in CASES, ETY; lia).
    5: assert (T117 : d_t d = 117%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL, F_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET in CASES, ETY; lia).
    1-4: assert (PS0 : dir_ps d = 0%Z) by (destruct PSC as [[P _] | (P & _ & E)]; [exact P | exfalso; unfold T_PTR, T_INT, T_UINT, T_SIZET in E, ETY; lia]).
    5: assert (PS6 : dir_ps d = 6%Z) by (destruct PSC as [[P CT0] | (P & _ & _)]; [exfalso; pose proof (conv_type_ty _ _ CT0) as TY0; unfold T_SIZET in ETY; lia | rewrite P; reflexivity]).
    1-4: rewrite PS0. 5: rewrite PS6.
    5: rewrite (proj2 (Z.eqb_eq _ _) T117).
    4: destruct TUX as [T117 | TX];
         [ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t d =? 117)%Z with false by (symmetry; apply Z.eqb_neq; lia) ].
    (* [comment removed for export] *)
    all: ienter; zs; br K; zs; zs; zs; zs.
    (* [comment removed for export] *)
    all: try zpark ARGC; try zpark APC; try zpark ST.
    all: callw (eapply pop_arg_callq; [lia | exact APC | exact VAA | exact NTH | lia | exact ARGC | exact ST | exact MI | rewrite ETY; unfold T_PTR, T_INT, T_UINT, T_DBL, F_pop_arg.T_SIZET, PrintfModel.T_PTR, PrintfModel.T_INT, PrintfModel.T_UINT, PrintfModel.T_SIZET; lia]).
    all: try clear ARGC APC ST.
    all: try fix_stk.
    all: idtac.
    all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC'; rewrite ETY in ARGC'; cbn [pop_arg_lo pop_arg_hi F_pop_arg.T_PTR F_pop_arg.T_INT F_pop_arg.T_UINT F_pop_arg.T_SIZET T_PTR T_INT T_UINT T_DBL PrintfModel.T_PTR PrintfModel.T_INT PrintfModel.T_UINT PrintfModel.T_SIZET Z.eqb Pos.eqb] in ARGC' end.
    all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
    all: zs.
    all: match goal with H : SINK ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB) end; zs; zs; zs; br K1; clear FLC.
    all: rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
    (* [comment removed for export] *)
    6: rewrite T117.
    1-5: zsto 0xb5c74%Z; change (Z.b2z (0 <? 0)) with 0%Z; rewrite Z.land_0_l; zs; br K2a.
    6: zsto 0xb5c74%Z;
       (let r := getreg 10%Z in lazymatch r with Z_to_bv 64 ?e => let v := eval vm_compute in e in change (Z_to_bv 64 e) with (Z_to_bv 64 v) end);
       zs; br K2a.
    all: zsto 0xb5c88%Z; rewrite (nzmask_eq (d_fl d)) by lia; zs; brf K2;
      [ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
      | assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; lia);
        rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
    all: zsto 0xb5c98%Z; zs; br K3; zsto 0xb5cac%Z.
    1-10: replace (Z.shiftl (d_t d + -65) 2 + 144088)%Z with (144088 + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; lia).
    all: first [ the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_d _ _ M TDI) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_x _ _ M TX) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1; pose proof RD1 as RD1';
                                      rewrite T117 in RD1'; replace (144088 + 4 * (117 - 65))%Z with 144296%Z in RD1' by reflexivity) ].
    all: zs; zs; zs.
    (* [comment removed for export] *)
    all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
    all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mm _) =>
      lazymatch type of AOK1 with
      | arg_ok _ _ _ _ _ _ _ _ (PA_s _) => (* [comment removed for export] *)
            rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
            pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
            match goal with MUc : munch _ m0 mm |- _ =>
              destruct (arg_ok_W _ _ _ _ AOK1 MUc) as (slack & STR & SRNG & SPAD & P0 & SD1 & SD2 & SD3 & SD4 & CKc) end;
            stmt (HS_CV_S fuel HH) as NX;
            jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
                                   (xp := d_xp d) (PV := bv_unsigned slot) (P := bv_unsigned slot) (s := sv) (slack := slack));
            [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
            | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | left; split; [reflexivity | exact P0] | exact SD1 | exact SD2 | exact SD3
            | subst fl'; rewrite ?land_land_same; reflexivity | exact (arg_ok_chk _ _ _ _ _ _ AOK1) ]
      | arg_ok _ _ _ _ _ _ _ _ PA_sn => (* [comment removed for export] *)
            cbn [arg_ok] in AOK1;
            rewrite <- (Z_to_bv_bv_unsigned slot), AOK1 in ARGC';
            pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
            match goal with MIc : mem_inv _ mm |- _ =>
              destruct (nullstr_arg_ok mm slot MIc AOK1) as (slack & STR & SRNG & SPAD & SD1 & SD2 & SD3) end;
            stmt (HS_CV_S fuel HH) as NX;
            jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
                                   (xp := d_xp d) (PV := 0%Z) (P := A_NULLSTR) (s := NULLSTR) (slack := slack));
            [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
            | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | right; split; reflexivity | exact SD1 | exact SD2 | exact SD3
            | subst fl'; rewrite ?land_land_same; reflexivity | exact chkr_nulls0 ]
      | arg_ok _ _ _ _ _ _ _ _ (PA_i _) => (* [comment removed for export] *)
          destruct AOK1 as [Hiv Emod];
          rewrite (sx32_int slot iv Hiv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_D fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hiv ]
      | arg_ok _ _ _ _ _ _ _ _ (PA_u _) =>
        lazymatch pc with
        | 745024%Z => (* [comment removed for export] *)
            destruct AOK1 as [Huv Emod];
            rewrite (zx32_uint slot uv Emod) in ARGC';
            pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
            stmt (HS_CV_U fuel HH) as NX;
            jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
            [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
            | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ]
        | 745144%Z => (* [comment removed for export] *)
          destruct AOK1 as [Huv Emod];
          rewrite (zx32_uint slot uv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_X fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv | exact TX ]
        end
      | arg_ok _ _ _ _ _ _ _ _ (PA_z _) => (* [comment removed for export] *)
            cbn [arg_ok] in AOK1;
            pose proof (bv_unsigned_in_range 64 slot) as ZR; unfold bv_modulus in ZR;
            rewrite <- (Z_to_bv_bv_unsigned slot), AOK1 in ARGC';
            pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
            stmt (HS_CV_U fuel HH) as NX;
            jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := zv));
            [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
            | zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | rewrite <- AOK1; change (2^64)%Z with 18446744073709551616%Z; cbn in ZR; lia ]
      end end.
  Qed.
End PrintfCore.
