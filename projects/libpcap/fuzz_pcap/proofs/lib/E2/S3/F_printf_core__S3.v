(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Walk Arr SysStep Image FP ITree Nodes Decode ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Bytes PropExec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_core_conv__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_core_end.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_core_cvx__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_core_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Printf_fsink.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sn_write__S3.
From Stdlib Require String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Fmt Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge MonadX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blk__S3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_printf_core.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep Image FP ITree Nodes Decode ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Bytes PropExec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_mlib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_zfacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memchr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strnlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface.
Import Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_zfacts.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_core_conv__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_core_end. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_core_cvx__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Export F_printf_core_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)
(* [comment removed for export] *)

Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp FS Ff B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit).
  Hypothesis SFR : sink_frame_stmt Fp FS B BS SINK.
  Hypothesis SFL : sink_flags_stmt Ff SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp FS Ff B BS SINK TOPOK OUT.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Let fany := fun f : bv 32 => f = fc0.   (* [comment removed for export] *)
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q <= 2^47)%Z.   (* [comment removed for export] *)
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : fany fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (65536 <= A /\ A + zlength fmt <= 77824)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((140840 <= Fp /\ Fp + FS <= 343304) \/ (AP + 8 <= Fp /\ Fp + FS <= VA)
                      \/ (0 < Fp /\ Fp + FS <= lo /\ (Fp + FS <= 65536 \/ 348160 <= Fp)))%Z.
  Hypothesis SEP_B : ((343312 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA)
                      \/ (0 < B /\ B + BS <= lo /\ (B + BS <= 65536 \/ 348160 <= B))
                      \/ (VA + 8 * zlength slots <= B /\ B + BS <= 2^63))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  Hypothesis FF : (Fp <= Ff /\ Ff + 232 <= Fp + FS)%Z.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Notation ctx_all := (F_printf_core_common.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp FS B BS q lo AP).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp FS B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp FS B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp FS B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp FS B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp FS B BS q lo fmt AP slots).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp FS B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp FS B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp FS Ff B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP HVA BS0 FF).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp FS B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp FS Ff B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp FS B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Ff q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp FS B BS SINK TOPOK ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Ff).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
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
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | (lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl | N => zl end end) | progress f_equal ].
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
  (* [comment removed for export] *)
  Local Ltac lia ::= pinned_lia.
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 140832 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 343304 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call ssegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | (lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl | N => zl end end) | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp);
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
      repeat (split; [fastfirst (first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]) |]); fastfirst (first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl])
    end.

  (* [comment removed for export] *)
  Lemma L_EXIT : S_EXIT.
  Proof using LO. pin_using (fun (LO : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_exit.L_EXIT; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_exit.L_EXIT; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_END : S_END.
  Proof using BS0 FF GLO HAP LO QHI SEP_F VAHI. pin_using (fun (BS0 FF GLO HAP LO QHI SEP_F VAHI : unit) => tt).
    first [ apply F_printf_core_end.L_END; first [eassumption | eexact L_EXIT]
          | intros; eapply F_printf_core_end.L_END; first [eassumption | eexact L_EXIT] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_EXIT1 : S_EXIT1.
  Proof using LO. pin_using (fun (LO : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_exit1.L_EXIT1; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_exit1.L_EXIT1; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_SCAN : S_SCAN.
  Proof using HA HF. pin_using (fun (HA HF : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_scan.L_SCAN; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_scan.L_SCAN; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FLAGS : S_FLAGS.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_flags.L_FLAGS; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_flags.L_FLAGS; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_WLOOP : S_WLOOP.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_width.L_WLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_width.L_WLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ intro; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_width.L_WIDTH; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_width.L_WIDTH; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PLOOP : S_PLOOP.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_prec.L_PLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_prec.L_PLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PREC : S_PLOOP -> S_PREC.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ intro; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_prec.L_PREC; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_prec.L_PREC; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_STATE : S_STATE.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_state.L_STATE; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_state.L_STATE; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DIR : S_DIR.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T6 : S_T6.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t6.L_T6; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t6.L_T6; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T5 : S_T5.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_t5.L_T5; first [eassumption | eexact L_T6]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_t5.L_T5; first [eassumption | eexact L_T6] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T4 : S_T4.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t4.L_T4; first [eassumption | eexact L_T5]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t4.L_T4; first [eassumption | eexact L_T5] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T3 : S_T3.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t3.L_T3; first [eassumption | eexact L_T4]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t3.L_T3; first [eassumption | eexact L_T4] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T2 : S_T2.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_t2.L_T2; first [eassumption | eexact L_T3]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_t2.L_T2; first [eassumption | eexact L_T3] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T1 : S_T1.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t1.L_T1; first [eassumption | eexact L_T2]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t1.L_T1; first [eassumption | eexact L_T2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_TAIL : S_TAIL.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_INTC2 : S_INTC2.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_INTC : S_INTC.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DLOOP : S_DLOOP.
  Proof using GLO LO QHI. pin_using (fun (GLO LO QHI : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_dloop.L_DLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_dloop.L_DLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FMTU2 : S_FMTU2.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FMTU : S_FMTU.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_D : S_CV_D.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_U : S_CV_U.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_XLOOP : S_XLOOP.
  Proof using GLO LO QHI. pin_using (fun (GLO LO QHI : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_xloop.L_XLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_xloop.L_XLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_X : S_CV_X.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_S : S_CV_S.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CONV : S_CONV.
  Proof using BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI. pin_using (fun (BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI. pin_using (fun (BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI : unit) => tt).
    first [ intro; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_P1 : S_P1.
  Proof using HA HF LO. pin_using (fun (HA HF LO : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PRO : S_PRO.
  Proof using GLO HA HAP HVA LO QHI. pin_using (fun (GLO HA HAP HVA LO QHI : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_pro.L_PRO; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_pro.L_PRO; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.

  Let HS_PRO := L_PRO.
  Let HS_HEAD := L_HEAD.
  Let HS_P1 := L_P1.
  
  (* [comment removed for export] *)
  Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
      let _ := ctx_all in
      SINK m0 st -> stk ssegs m0 lo q -> mem_inv ssegs m0 -> bytes_at ssegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      rw_cells ssegs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
      args_ok Fp FS B BS m0 lo q AP (skipn (Z.to_nat i) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK) (fp_calls (length fmt) fmt args) ->
      (0 < Ff)%Z -> (Ff + 232 <= 2^64)%Z ->
      implM ssegs (printf_model OUT fmt args) st POST
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x1bd5c) fc0 None m0 (seg_rom ssegs)).
  Proof using FRM0 HS_HEAD HS_PRO. pin_using (fun (FRM0 HS_HEAD HS_PRO : unit) => tt).
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 st i args _ HS0 ST0 MI0 BY0 VAA0 SSP0 APC0 Hi AOK FPC HF0 HF1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    unfold printf_model. ienter.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Ff); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    pose proof FI as FI'. destruct FI' as (MI & MU & WM & _).
    assert (HS : SINK m st).
    { eapply (SFR [(q + -544, q)]%Z m0 m st HS0 MUq WM); (apply Forall_cons; [cbn [fst snd]; unfold zlength in *; lia | apply Forall_nil]). }
    assert (APC : rw_cells ssegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
    { eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
    stmt (HS_HEAD (length fmt)) as NXH.
    jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
      [ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
      | exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
      let _ := ctx_all in
      stk ssegs m0 lo q -> mem_inv ssegs m0 -> bytes_at ssegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      pass1_ok fmt = true ->
      evt ssegs (POST1 0)
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x1bd5c) fc0 None m0 (seg_rom ssegs)).
  Proof using HS_P1 HS_PRO. pin_using (fun (HS_P1 HS_PRO : unit) => tt).
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 _ ST0 MI0 BY0 VAA0 SSP0 P1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 0%Z); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    stmt HS_P1 as NX1.
    jump (eapply NX1; [ exact FI | eapply munch_weaken; [|exact MUq]; unfold sub_fp; cbn [outside]; intros; lia | exact LOW | exact DIG | exact PAD | exact P1 ]).
  Qed.

End PrintfCore.


(* [comment removed for export] *)
Theorem printf_core_proof : forall (St : Type) (Fp FS Ff B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
    (OUT : list Z -> M St unit),
  sink_frame_stmt Fp FS B BS SINK -> sink_flags_stmt Ff SINK -> topok_stmt TOPOK -> out_stmt Fp FS Ff B BS SINK TOPOK OUT ->
  printf_core_stmt Fp FS Ff B BS SINK TOPOK OUT.
Proof.
  intros St Fp FS Ff B BS SINK TOPOK OUT SFR SFL TOK HOUT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary fmt VA i slots args
         HS BY HF Ha0 APC VAA Hi AOK ST LO GLO SPHI TQ SSP MI FRM HA BS0 FF SEPF SEPB HAP HVA VAHI.
  assert (FPC : Forall (fpcall_stmt Fp B BS SINK TOPOK) (fp_calls (length fmt) fmt args)) by (apply Forall_nil).
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  pose proof (L_CORE2 Fp FS Ff B BS SINK TOPOK OUT SFR SFL TOK HOUT ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) VA slots a3 a4 HF LO GLO SPHI TQ eq_refl HA SEPF SEPB HAP HVA VAHI BS0 FF
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 st i args HS ST MI BY VAA SSP APC Hi AOK FPC) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply implM_mono.
  { apply C; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; lia. }
  cbv beta. intros r st' ms' P. unfold POST, W in P. unfold printf_core_post, SR.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & apv & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & HS' & SSP' & APC' & Hr).
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', apv, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact Hr.
Qed.

Theorem printf_core1_proof : printf_core1_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
         BY HF P1 Ha0 ST LO GLO SPHI SSP MI HA HAP A2HI.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in LO, GLO, HA.
  pose proof (L_CORE1 140840 232 0 0 ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) (bv_unsigned a2 + 8)%Z [] a3 a4 HF
                      ltac:(unfold PC_DEPTH; lia) ltac:(unfold GLOBALS_TOP; lia) SPHI HA HAP ltac:(lia)
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ST MI BY) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply evt_mono.
  { apply C; [ | exact SSP | exact P1 ]. unfold va_area. cbn [u64s map concat]. apply bytes_at_nil; lia. }
  cbv beta. intros ms' P. unfold POST1 in P. unfold printf_core1_post.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & SSP').
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact SSP'.
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.FP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_mlib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_zfacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memchr.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strnlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface.TwB.
Import Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_zfacts.   (* [comment removed for export] *)
(* [comment removed for export] *)
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_common.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)
(* [comment removed for export] *)

Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp FS Ff B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit).
  Hypothesis SFR : sink_frame_stmt Fp FS B BS SINK.
  Hypothesis SFL : sink_flags_stmt Ff SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp FS Ff B BS SINK TOPOK OUT.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Let fany := fun f : bv 32 => f = fc0.   (* [comment removed for export] *)
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q <= 2^47)%Z.   (* [comment removed for export] *)
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : fany fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (65536 <= A /\ A + zlength fmt <= 77824)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((142824 <= Fp /\ Fp + FS <= 345288) \/ (AP + 8 <= Fp /\ Fp + FS <= VA)
                      \/ (0 < Fp /\ Fp + FS <= lo /\ (Fp + FS <= 65536 \/ 352256 <= Fp)))%Z.
  Hypothesis SEP_B : ((345296 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA)
                      \/ (0 < B /\ B + BS <= lo /\ (B + BS <= 65536 \/ 352256 <= B))
                      \/ (VA + 8 * zlength slots <= B /\ B + BS <= 2^63))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  Hypothesis FF : (Fp <= Ff /\ Ff + 232 <= Fp + FS)%Z.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Notation ctx_all := (S3.F_printf_core_common.TwB.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (S3.F_printf_core_common.TwB.W Fp FS B BS q lo AP).
  Local Notation Fok := (S3.F_printf_core_common.TwB.Fok F).
  Local Notation Fok_refl := (S3.F_printf_core_common.TwB.Fok_refl F).
  Local Notation Fok_trans := (S3.F_printf_core_common.TwB.Fok_trans F).
  Local Notation POST := (S3.F_printf_core_common.TwB.POST (St:=St) Fp FS B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary AP).
  Local Notation hi_cells := (S3.F_printf_core_common.TwB.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (S3.F_printf_core_common.TwB.lo_cells AP nla nlt).
  Local Notation finv := (S3.F_printf_core_common.TwB.finv Fp FS B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (S3.F_printf_core_common.TwB.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (S3.F_printf_core_common.TwB.implM_eq_ms (St:=St)).
  Local Notation sink_store := (S3.F_printf_core_common.TwB.sink_store (St:=St) Fp FS B BS SINK SFR).
  Local Notation sink_call := (S3.F_printf_core_common.TwB.sink_call (St:=St) Fp FS B BS SINK SFR).
  Local Notation arg_ok_W := (S3.F_printf_core_common.TwB.arg_ok_W Fp FS B BS q lo fmt AP slots).
  Local Notation args_ok_W := (S3.F_printf_core_common.TwB.args_ok_W Fp FS B BS q lo fmt AP slots).
  Local Notation lo_cells14 := (S3.F_printf_core_common.TwB.lo_cells14 AP nla nlt).
  Local Notation lo_split := (S3.F_printf_core_common.TwB.lo_split q AP nla nlt).
  Local Notation lo_join := (S3.F_printf_core_common.TwB.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (S3.F_printf_core_common.TwB.pop_arg_callq q gp tp lo AP VA slots LO GLO QHI HAP HVA).
  Local Notation strnlen_callq := (S3.F_printf_core_common.TwB.strnlen_callq q gp tp lo LO GLO QHI).
  Local Notation out_postq := (S3.F_printf_core_common.TwB.out_postq (St:=St) Fp FS B BS SINK q gp tp lo canary).
  Local Notation out_callq := (S3.F_printf_core_common.TwB.out_callq (St:=St) Fp FS Ff B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP HVA BS0 FF).
  Local Notation S_EXIT := (S3.F_printf_core_common.TwB.S_EXIT (St:=St) Fp FS B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (S3.F_printf_core_common.TwB.S_SCAN Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (S3.F_printf_core_common.TwB.S_FLAGS Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (S3.F_printf_core_common.TwB.S_WLOOP Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (S3.F_printf_core_common.TwB.S_WIDTH Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (S3.F_printf_core_common.TwB.S_PLOOP Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (S3.F_printf_core_common.TwB.S_PREC Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (S3.F_printf_core_common.TwB.S_STATE Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (S3.F_printf_core_common.TwB.S_DIR Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (S3.F_printf_core_common.TwB.S_END (St:=St) Fp FS Ff B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (S3.F_printf_core_common.TwB.S_HEAD (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (S3.F_printf_core_common.TwB.S_CONV (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (S3.F_printf_core_common.TwB.body_loc Fp FS B BS q lo).
  Local Notation S_TAIL := (S3.F_printf_core_common.TwB.S_TAIL (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (S3.F_printf_core_common.TwB.tregs Ff q gp tp A).
  Local Notation tinv := (S3.F_printf_core_common.TwB.tinv (St:=St) Fp FS B BS SINK TOPOK ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (S3.F_printf_core_common.TwB.S_T6 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (S3.F_printf_core_common.TwB.S_T5 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (S3.F_printf_core_common.TwB.S_T4 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (S3.F_printf_core_common.TwB.S_T3 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (S3.F_printf_core_common.TwB.S_T2 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (S3.F_printf_core_common.TwB.S_T1 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (S3.F_printf_core_common.TwB.S_INTC2 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (S3.F_printf_core_common.TwB.S_INTC (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (S3.F_printf_core_common.TwB.dloop_post q gp tp).
  Local Notation S_DLOOP := (S3.F_printf_core_common.TwB.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (S3.F_printf_core_common.TwB.S_FMTU2 (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (S3.F_printf_core_common.TwB.S_FMTU (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (S3.F_printf_core_common.TwB.S_CV_D (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (S3.F_printf_core_common.TwB.S_CV_U (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (S3.F_printf_core_common.TwB.xloop_post q gp tp).
  Local Notation S_XLOOP := (S3.F_printf_core_common.TwB.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (S3.F_printf_core_common.TwB.S_CV_X (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (S3.F_printf_core_common.TwB.S_CV_S (St:=St) Fp FS Ff B BS SINK TOPOK OUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (S3.F_printf_core_common.TwB.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (S3.F_printf_core_common.TwB.S_EXIT1 Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (S3.F_printf_core_common.TwB.S_P1 Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (S3.F_printf_core_common.TwB.S_PRO Fp FS B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Ff).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
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
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | (lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl | N => zl end end) | progress f_equal ].
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
  (* [comment removed for export] *)
  Local Ltac lia ::= pinned_lia.
  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 142816 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 345288 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call usegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | (lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl | N => zl end end) | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp);
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
      repeat (split; [fastfirst (first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]) |]); fastfirst (first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl])
    end.

  (* [comment removed for export] *)
  Lemma L_EXIT : S_EXIT.
  Proof using LO. pin_using (fun (LO : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_exit.TwB.L_EXIT; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_exit.TwB.L_EXIT; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_END : S_END.
  Proof using BS0 FF GLO HAP LO QHI SEP_F VAHI. pin_using (fun (BS0 FF GLO HAP LO QHI SEP_F VAHI : unit) => tt).
    first [ apply S3.F_printf_core_end.TwB.L_END; first [eassumption | eexact L_EXIT]
          | intros; eapply S3.F_printf_core_end.TwB.L_END; first [eassumption | eexact L_EXIT] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_EXIT1 : S_EXIT1.
  Proof using LO. pin_using (fun (LO : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_exit1.TwB.L_EXIT1; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_exit1.TwB.L_EXIT1; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_SCAN : S_SCAN.
  Proof using HA HF. pin_using (fun (HA HF : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_scan.TwB.L_SCAN; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_scan.TwB.L_SCAN; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FLAGS : S_FLAGS.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_flags.TwB.L_FLAGS; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_flags.TwB.L_FLAGS; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_WLOOP : S_WLOOP.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_width.TwB.L_WLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_width.TwB.L_WLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ intro; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_width.TwB.L_WIDTH; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_width.TwB.L_WIDTH; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PLOOP : S_PLOOP.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_prec.TwB.L_PLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_prec.TwB.L_PLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PREC : S_PLOOP -> S_PREC.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ intro; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_prec.TwB.L_PREC; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_prec.TwB.L_PREC; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_STATE : S_STATE.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_state.TwB.L_STATE; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_state.TwB.L_STATE; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DIR : S_DIR.
  Proof using HF. pin_using (fun (HF : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_dir.TwB.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_dir.TwB.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T6 : S_T6.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t6.TwB.L_T6; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t6.TwB.L_T6; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T5 : S_T5.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_t5.TwB.L_T5; first [eassumption | eexact L_T6]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_t5.TwB.L_T5; first [eassumption | eexact L_T6] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T4 : S_T4.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t4.TwB.L_T4; first [eassumption | eexact L_T5]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t4.TwB.L_T4; first [eassumption | eexact L_T5] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T3 : S_T3.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t3.TwB.L_T3; first [eassumption | eexact L_T4]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t3.TwB.L_T3; first [eassumption | eexact L_T4] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T2 : S_T2.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_t2.TwB.L_T2; first [eassumption | eexact L_T3]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_t2.TwB.L_T2; first [eassumption | eexact L_T3] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_T1 : S_T1.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t1.TwB.L_T1; first [eassumption | eexact L_T2]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_t1.TwB.L_T1; first [eassumption | eexact L_T2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_TAIL : S_TAIL.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_tail.TwB.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_tail.TwB.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_INTC2 : S_INTC2.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_intc2.TwB.L_INTC2; first [eassumption | eexact L_TAIL]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_intc2.TwB.L_INTC2; first [eassumption | eexact L_TAIL] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_INTC : S_INTC.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_intc.TwB.L_INTC; first [eassumption | eexact L_INTC2]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_intc.TwB.L_INTC; first [eassumption | eexact L_INTC2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_DLOOP : S_DLOOP.
  Proof using GLO LO QHI. pin_using (fun (GLO LO QHI : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_dloop.TwB.L_DLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_dloop.TwB.L_DLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FMTU2 : S_FMTU2.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_fmtu2.TwB.L_FMTU2; first [eassumption | eexact L_INTC]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_fmtu2.TwB.L_FMTU2; first [eassumption | eexact L_INTC] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_FMTU : S_FMTU.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_fmtu.TwB.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_fmtu.TwB.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_D : S_CV_D.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_cvd.TwB.L_CV_D; first [eassumption | eexact L_FMTU]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_cvd.TwB.L_CV_D; first [eassumption | eexact L_FMTU] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_U : S_CV_U.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_cvu.TwB.L_CV_U; first [eassumption | eexact L_FMTU]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_cvu.TwB.L_CV_U; first [eassumption | eexact L_FMTU] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_XLOOP : S_XLOOP.
  Proof using GLO LO QHI. pin_using (fun (GLO LO QHI : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_xloop.TwB.L_XLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_xloop.TwB.L_XLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_X : S_CV_X.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_cvx.TwB.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_cvx.TwB.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CV_S : S_CV_S.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_cvs.TwB.L_CV_S; first [eassumption | eexact L_TAIL]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_cvs.TwB.L_CV_S; first [eassumption | eexact L_TAIL] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_CONV : S_CONV.
  Proof using BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI. pin_using (fun (BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_conv.TwB.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_conv.TwB.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI. pin_using (fun (BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI : unit) => tt).
    first [ intro; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_head.TwB.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_head.TwB.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_P1 : S_P1.
  Proof using HA HF LO. pin_using (fun (HA HF LO : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_p1.TwB.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_conv__S3.F_printf_core_p1.TwB.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.
  Lemma L_PRO : S_PRO.
  Proof using GLO HA HAP HVA LO QHI. pin_using (fun (GLO HA HAP HVA LO QHI : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_pro.TwB.L_PRO; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_cvx__S3.F_printf_core_pro.TwB.L_PRO; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
  Qed.

  Let HS_PRO := L_PRO.
  Let HS_HEAD := L_HEAD.
  Let HS_P1 := L_P1.
  
  (* [comment removed for export] *)
  Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
      let _ := ctx_all in
      SINK m0 st -> stk usegs m0 lo q -> mem_inv usegs m0 -> bytes_at usegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      rw_cells usegs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
      args_ok Fp FS B BS m0 lo q AP (skipn (Z.to_nat i) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK) (fp_calls (length fmt) fmt args) ->
      (0 < Ff)%Z -> (Ff + 232 <= 2^64)%Z ->
      implM usegs (printf_model OUT fmt args) st POST
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x1c51c) fc0 None m0 (seg_rom usegs)).
  Proof using FRM0 HS_HEAD HS_PRO. pin_using (fun (FRM0 HS_HEAD HS_PRO : unit) => tt).
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 st i args _ HS0 ST0 MI0 BY0 VAA0 SSP0 APC0 Hi AOK FPC HF0 HF1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    unfold printf_model. ienter.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Ff); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    pose proof FI as FI'. destruct FI' as (MI & MU & WM & _).
    assert (HS : SINK m st).
    { eapply (SFR [(q + -544, q)]%Z m0 m st HS0 MUq WM); (apply Forall_cons; [cbn [fst snd]; unfold zlength in *; lia | apply Forall_nil]). }
    assert (APC : rw_cells usegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
    { eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
    stmt (HS_HEAD (length fmt)) as NXH.
    jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
      [ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
      | exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
      let _ := ctx_all in
      stk usegs m0 lo q -> mem_inv usegs m0 -> bytes_at usegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      pass1_ok fmt = true ->
      evt usegs (POST1 0)
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x1c51c) fc0 None m0 (seg_rom usegs)).
  Proof using HS_P1 HS_PRO. pin_using (fun (HS_P1 HS_PRO : unit) => tt).
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 _ ST0 MI0 BY0 VAA0 SSP0 P1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 0%Z); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    stmt HS_P1 as NX1.
    jump (eapply NX1; [ exact FI | eapply munch_weaken; [|exact MUq]; unfold sub_fp; cbn [outside]; intros; lia | exact LOW | exact DIG | exact PAD | exact P1 ]).
  Qed.

End PrintfCore.


(* [comment removed for export] *)
Theorem printf_core_proof : forall (St : Type) (Fp FS Ff B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
    (OUT : list Z -> M St unit),
  sink_frame_stmt Fp FS B BS SINK -> sink_flags_stmt Ff SINK -> topok_stmt TOPOK -> out_stmt Fp FS Ff B BS SINK TOPOK OUT ->
  printf_core_stmt Fp FS Ff B BS SINK TOPOK OUT.
Proof.
  intros St Fp FS Ff B BS SINK TOPOK OUT SFR SFL TOK HOUT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary fmt VA i slots args
         HS BY HF Ha0 APC VAA Hi AOK ST LO GLO SPHI TQ SSP MI FRM HA BS0 FF SEPF SEPB HAP HVA VAHI.
  assert (FPC : Forall (fpcall_stmt Fp B BS SINK TOPOK) (fp_calls (length fmt) fmt args)) by (apply Forall_nil).
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  pose proof (L_CORE2 Fp FS Ff B BS SINK TOPOK OUT SFR SFL TOK HOUT ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) VA slots a3 a4 HF LO GLO SPHI TQ eq_refl HA SEPF SEPB HAP HVA VAHI BS0 FF
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 st i args HS ST MI BY VAA SSP APC Hi AOK FPC) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply implM_mono.
  { apply C; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; lia. }
  cbv beta. intros r st' ms' P. unfold POST, W in P. unfold printf_core_post, SR.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & apv & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & HS' & SSP' & APC' & Hr).
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', apv, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact Hr.
Qed.

Theorem printf_core1_proof : printf_core1_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
         BY HF P1 Ha0 ST LO GLO SPHI SSP MI HA HAP A2HI.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in LO, GLO, HA.
  pose proof (L_CORE1 142824 232 0 0 ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) (bv_unsigned a2 + 8)%Z [] a3 a4 HF
                      ltac:(unfold PC_DEPTH; lia) ltac:(unfold GLOBALS_TOP; lia) SPHI HA HAP ltac:(lia)
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ST MI BY) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply evt_mono.
  { apply C; [ | exact SSP | exact P1 ]. unfold va_area. cbn [u64s map concat]. apply bytes_at_nil; lia. }
  cbv beta. intros ms' P. unfold POST1 in P. unfold printf_core1_post.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & SSP').
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact SSP'.
Qed.
End TwB.
End F_printf_core.

(* [comment removed for export] *)
Module F_vfprintf_file.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep FP ITree Nodes Decode StoreFast ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_iface F_printf_core_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Printf_fsink. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_printf_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Printf_fsink.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (bv_swrap _ (Z.add (Z.b2z (Z.ltb _ _)) (-1)%Z)) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Lemma rwc_eqA : forall m A A' cs, rw_cells ssegs m A cs -> A = A' -> rw_cells ssegs m A' cs.
Proof. intros m A A' cs H ->. exact H. Qed.
Ltac readdr H A' := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let H' := fresh in assert (H' : rw_cells ssegs m A' cs) by (eapply rwc_eqA; [exact H | lia]); clear H; rename H' into H end.

Definition VFPRINTF : Z := 0x1bbac.
Definition TOWRITE : Z := 0x1b914.
Definition VF_FRAME : Z := 368.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
  intros f c k Hk Hc. rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof. intros a. change 128 with (2^7). rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity. Qed.
Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, bv_swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
  rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296. change (2^31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.
Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

(* [comment removed for export] *)
Definition flags_ok_clr_err__stmt : Prop := forall f (flags : word),
  flags_ok f flags -> flags_ok f (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)).
Section Sz6.
Variables f flags : ltac2:(SecDiet.SzSec.tyM 'flags_ok_clr_err__stmt "vv" @f).
#[using="Type"] Lemma flags_ok_clr_err__body : ltac2:(SecDiet.SzSec.bodyP 'flags_ok_clr_err__stmt "vv").
Proof.
  intros FL.
 pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R.
  pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583) as LR.
  unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM in *. rewrite unsigned_lit by lia.
  destruct FL as (A1 & A2 & A3 & A4 & A5 & A6).
  rewrite <- !Z.land_assoc.
  change (Z.land 18446744073709551583 4) with 4. change (Z.land 18446744073709551583 8) with 8.
  change (Z.land 18446744073709551583 16) with 16. change (Z.land 18446744073709551583 32) with 0.
  change (Z.land 18446744073709551583 64) with 64. change (Z.land 18446744073709551583 1) with 1.
  rewrite Z.land_0_r.
  repeat split; try reflexivity; rewrite land_low7, sx32_mod128, <- land_low7 by lia; assumption.
Qed.
End Sz6.
Lemma flags_ok_clr_err : ltac:(let t := eval cbv delta [flags_ok_clr_err__stmt] in flags_ok_clr_err__stmt in exact t).
Proof. intros f flags. ltac2:(SecDiet.SzSec.closeP 'flags_ok_clr_err__body "vv"). Qed.

(* [comment removed for export] *)
Lemma flags_ok_relw : forall f (flags : word), flags_ok f flags -> flags_ok f (sx32 flags).
Proof.
  intros f flags FL. unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM in *.
  destruct FL as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat split; rewrite land_low7, sx32_mod128, <- land_low7 by lia; assumption.
Qed.

Lemma flags_err_clear_lw : forall f (flags : word), flags_ok f flags -> Z.land (bv_unsigned (sx32 flags)) 32 = 0.
Proof.
  intros f flags (_ & _ & _ & A4 & _). rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact A4.
Qed.
Lemma flags_nowr_clear : forall f (flags : word), flags_ok f flags -> f_nowr f = false -> Z.land (bv_unsigned flags) 8 = 0.
Proof. intros f flags (_ & A2 & _) NW. unfold F_NOWR in A2. rewrite NW in A2. exact A2. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Forall_disj_vff : forall (W : list (Z * Z)) lo sp Fp FS B BS a n,
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  (a + n <= lo \/ sp <= a) -> (a + n <= Fp \/ Fp + FS <= a) -> (a + n <= B \/ B + BS <= a) -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W lo sp Fp FS B BS a n H H1 H2 H3 Hn. induction H as [|[u1 u2] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.
Definition arg_ok_vff__stmt : Prop := forall Fp FS B BS m m' lo sp sp' ap w a (W : list (Z * Z)),
  arg_ok Fp FS B BS m lo sp ap w a -> sp' <= sp -> munch W m m' ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  arg_ok Fp FS B BS m' lo sp' ap w a.
Section Sz11.
Variables Fp FS B BS m m' lo sp sp' ap w a W : ltac2:(SecDiet.SzSec.tyM 'arg_ok_vff__stmt "vvvvvvvvvvvvv" @Fp).
#[using="Type"] Lemma arg_ok_vff__body : ltac2:(SecDiet.SzSec.bodyP 'arg_ok_vff__stmt "vvvvvvvvvvvvv").
Proof.
  intros H Hsp MU HW.
 destruct a as [s|i|u|u]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & S47). exists slack.   (* [comment removed for export] *)
  split; [|repeat (split; [fastfirst (first [assumption | lia])|]); exact S47].
  eapply bytes_at_transport; [exact BY | exact MU |].
  rewrite length_app, zb_length. cbn [length]. unfold zlength in *.
  eapply Forall_disj_vff; [exact HW | | | | lia]; lia.
Qed.
End Sz11.
Lemma arg_ok_vff : ltac:(let t := eval cbv delta [arg_ok_vff__stmt] in arg_ok_vff__stmt in exact t).
Proof. intros Fp FS B BS m m' lo sp sp' ap w a W. ltac2:(SecDiet.SzSec.closeP 'arg_ok_vff__body "vvvvvvvvvvvvv"). Qed.
Lemma args_ok_vff : forall Fp FS B BS m m' lo sp sp' ap ws args (W : list (Z * Z)),
  args_ok Fp FS B BS m lo sp ap ws args -> sp' <= sp -> munch W m m' ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  args_ok Fp FS B BS m' lo sp' ap ws args.
Proof.
  intros Fp FS B BS m m' lo sp sp' ap ws args W. revert ws. induction args as [|a args IH]; intros ws H Hsp MU HW; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vff; eassumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MonadFacts.
  Context {St : Type}.
  #[local] Notation impl := (ITree.impl ssegs (at_node ssegs) (npeek ssegs)).

  (* [comment removed for export] *)
  Lemma implM_bind_mret : forall {A} (c : M St A) s Q ms,
    implM ssegs c s Q ms -> implM ssegs (mbind c mret) s Q ms.
  Proof using Type. pin_using tt.
    intros A c s Q ms H. unfold implM, mbind, ebind in *.
    generalize dependent ms. generalize (c s) as t. induction t as [r|n k IH]; intros ms H; cbn [ITree.bind] in *.
    - destruct r as [[a s']|]; cbn in *; exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)].
      + left. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
      + right. exists g. split; [exact Hg|]. apply IH. apply Hk.
  Qed.

  Lemma implM_ms_eq : forall {A} (c : M St A) s Q ms ms', implM ssegs c s Q ms' -> ms = ms' -> implM ssegs c s Q ms.
  Proof using Type. pin_using tt. intros A c s Q ms ms' H ->. exact H. Qed.
End MonadFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section VfFile.
  Context {St : Type}.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Variables (sw0 ch0 : bool).
  Let q := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^47.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis FLOC : (140840 <= Fp /\ Fp + 232 <= 343304) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis BLOC : (343312 <= B /\ B + 1024 <= GLOBALS_TOP) \/ (0 < B /\ B + 1024 <= lo /\ (B + 1024 <= 65536 \/ GLOBALS_TOP <= B)).
  Hypothesis FB : B + 1024 <= Fp \/ Fp + 232 <= B.

  #[local] Notation SINKf rpos rend := (SINK_file (St:=St) Fp B 1024 rpos rend closefn readfn seekfn prev next tail sw0 ch0).
  #[local] Notation OUTf := (OUT_file (St:=St)).

  (* [comment removed for export] *)
  Definition vfprintf_file_post (rpos rend : Z) (m : mem) (st : St) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fsink_inv 1024 sw0 ch0 f' /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (bufbytes' : list byte) (m' : mem) (rpos' rend' : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch [(lo, q); (Fp, Fp + 232); (B, B + 1024)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo q
      /\ ssp_cells m' canary
      /\ rw_cells ssegs m' Fp (fcells flags' rpos' rend' closefn (B + 1024) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B 1024 prev next (f_fd f') mode' (lbf_of f') tail)
      /\ ((rpos' = rpos /\ rend' = rend) \/ (rpos' = 0 /\ rend' = 0))
      /\ flags_ok f' flags'
      /\ rw_cells ssegs m' B [CB 1024%nat bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= 1024.

  (* [comment removed for export] *)
  Lemma sinkfacts : 0 <= Fp /\ 0 < B /\ 0 <= 1024 <= 1024 /\ B + 1024 <= 2^47 (* [comment removed for export] *) /\ Fp + 232 < 2^63
    /\ (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) /\ (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp)
    /\ (B + 1024 <= got_ssp \/ got_ssp + 8 <= B) /\ (B + 1024 <= ssp_guard \/ ssp_guard + 8 <= B).
  Proof using BLOC FLOC HVA LO fmtz. pin_using (fun (BLOC FLOC HVA LO fmtz : unit) => tt).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold got_ssp, ssp_guard, GLOBALS_TOP, VF_FRAME, PC_DEPTH, q, zlength in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Definition vf_pass2__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m m1 : mem) (f1 : file_st) (st : St)
      (flags flags1 mode1 : word) (bufbytes1 junk : list byte) (rpos rend rpos1 rend1 : Z),
    ((rpos1 = rpos /\ rend1 = rend) \/ (rpos1 = 0 /\ rend1 = 0)) ->
    rw_cells ssegs m1 Fp (fcells flags1 rpos1 rend1 closefn (B + 1024) (B + zlength (f_wbuf f1)) B readfn (wfn_of f1) seekfn B 1024 prev next (f_fd f1) mode1 (lbf_of f1) tail) ->
    flags_ok f1 flags1 -> fsink_inv 1024 sw0 ch0 f1 ->
    rw_cells ssegs m1 B [CB 1024%nat bufbytes1] -> firstn (length (f_wbuf f1)) bufbytes1 = to_bytes (f_wbuf f1) -> zlength (f_wbuf f1) <= 1024 ->
    rw_cells ssegs m1 (q + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 248 junk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                   C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at ssegs m1 A (zb fmtz) -> va_area m1 VA slots -> args_ok Fp 232 B 1024 m1 lo q (q + -368) slots args ->
    stk ssegs m1 lo (q + -368) -> ssp_cells m1 canary -> mem_inv ssegs m1 ->
    munch [(lo, q); (Fp, Fp + 232); (B, B + 1024)] m m1 -> wmono ssegs m m1 ->
    Z.land (bv_unsigned (sx32 flags)) 32 = 0 ->
    implM ssegs (out_pieces f1 ps) st (vfprintf_file_post rpos rend m st)
      (MS (mkR x1 (Z_to_bv 64 (q + -368)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 0) (sx32 flags) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bc9c) fc None m1 (seg_rom ssegs)).
  Section Sz16.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 bufbytes1 junk rpos rend rpos1 rend1 : ltac2:(SecDiet.SzSec.tyM 'vf_pass2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma vf_pass2__body : ltac2:(SecDiet.SzSec.bodyP 'vf_pass2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BLOC FB FLOC GLO HA HF HVA LO PIECES SMALL. pin_using (fun (BLOC FB FLOC GLO HA HF HVA LO PIECES SMALL : unit) => tt).
    intros RP FC1 FL1 INV1 BUF1 BP1 WBL1 FR BY VAA AOK ST SSP MI MU WM OLDERR.
    pose proof sinkfacts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold q in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB. pose proof (rw_CB_length _ _ _ _ BUF1) as LBB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof INV1 as (WA1 & RB1 & BS1 & NW1 & CH1 & SW1 & CN1).
    (* [comment removed for export] *)
    pose proof (printf_core_proof (file_st * St) Fp 232 Fp B 1024 (SINKf rpos1 rend1 st) TOPOK_file OUTf
                  (file_sink_frame Fp B 1024 rpos1 rend1 closefn readfn seekfn prev next tail sw0 ch0 st K3 FB K6 K7 K8 K9)
                  (file_sink_flags Fp B 1024 rpos1 rend1 closefn readfn seekfn prev next tail sw0 ch0 st K1 K5)
                  file_topok
                  (file_out Fp B 1024 rpos1 rend1 closefn readfn seekfn prev next tail sw0 ch0 st K1 K2 K3 K4 FB K6 K7 K8 K9)) as PC2.
    unfold printf_core_stmt in PC2.
    set (PCQ := printf_core_post (St:=file_st * St) Fp 232 B 1024 (SINKf rpos1 rend1 st) (Z_to_bv 64 0x1bcb4) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp
                  (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 343304) (Z_to_bv 64 1) (Z_to_bv 64 0) (sx32 flags) s6 s7 s8 s9 s10 s11 F fc
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -368) : word)) lo canary m1).
    apply (implM_post_evt ssegs (out_pieces f1 ps) st (fun f' st' ms' => PCQ r (f', st') ms')).
    { apply out_pieces_bridge; [exact SMALL|].
      eapply (printf_model_outs ssegs OUTf fmtz args ps r mret); [exact PIECES|].
      apply implM_bind_mret.
      apply implM_prefix. do 5 zs. zs. apply evt_done.
      apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      replace (Z_to_bv 64 VA : word) with (Z_to_bv 64 (VA + 8 * 0) : word) in APC by (f_equal; lia).
      eapply implM_ms_eq; [eapply PC2 with (i := 0%Z) (slots := slots) | subst PCQ; ms_eq]; clear PC2; rewrite ?unsigned_lit by (keep_hyps sp A fmtz bufbytes1 HA lo LO GLO SPHI; lia);
        unfold PC_DEPTH, GLOBALS_TOP, TOPOK_file, zlength.
      all: match goal with |- ?g => fastfirst (first [ noevar_assumption |
             (* [comment removed for export] *) split; [reflexivity | split; [exact INV1 | exists flags1, mode1, bufbytes1; cbn [fst]; split; [exact FC1 | split; [exact FL1 | split; [exact BUF1 | split; [exact BP1 | exact WBL1]]]]]]
           | exact BY | exact HF | reflexivity | exact APC | exact VAA | exact I
           | cbn [skipn Z.to_nat]; eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz bufbytes1; lia) | apply (munch_refl []) | constructor]
           | exact ST | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption
           | (keep_hyps sp VA fmtz slots bufbytes1 HVA Fp lo FLOC B GLO BLOC; lia)
           | idtac "VFP2-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' PO. clear PC2. subst PCQ.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & -> & -> & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in FR. destruct FR as [_ FR]. cbn [cells_size csize Nat.add app] in FR.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
    clear BY VAA AOK BUF1 FC1.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m3 MUc WMc; clear MUc WMc end.
    fix_ret.
    destruct SNK3 as (EST3 & INV3 & flags3 & mode3 & bufbytes3 & FC3 & FL3 & BUF3 & BP3 & WBL3). cbn [fst snd] in EST3, INV3, FC3, FL3, BUF3, BP3, WBL3. subst st'.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC3.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 (sx32 flags3)) as FR3. unfold bv_modulus in FR3. cbn in FR3.
    zs. zs. rewrite (flags_err_clear_lw f' flags3 FL3). zs. rewrite OLDERR, Z.lor_0_r.
    zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FALL : rw_cells ssegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA); CB 248 junk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                   C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
      [ apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [exact APC3|]; cbn [cells_size csize Nat.add app]; eapply rwc_eqA; [exact FR | lia]
      | clear APC3 FR ] end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -368)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evt_done. unfold vfprintf_file_post, q. split; [reflexivity|]. split; [exact INV3|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [unfold fcells, file_cells; exact FC3|].
    split; [exact RP|].
    split; [apply flags_ok_relw; exact FL3|].
    split; [exact BUF3|]. split; [exact BP3| exact WBL3].
  Qed.
  End Sz16.
  Lemma vf_pass2 : ltac:(let t := eval cbv delta [vf_pass2__stmt] in vf_pass2__stmt in exact t).
  Proof using BLOC FB FLOC GLO HA HF HVA LO PIECES SMALL. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 bufbytes1 junk rpos rend rpos1 rend1. ltac2:(SecDiet.SzSec.closeP 'vf_pass2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma flags_ok_set_w : forall f fl act wb, flags_ok f fl -> flags_ok (set_w act wb (set_rbuf [] f)) fl.
  Proof using Type. pin_using tt. intros f fl act wb FL. unfold flags_ok in *. cbn. exact FL. Qed.

  Definition vfprintf_file_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells ssegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells ssegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at ssegs m A (zb fmtz) -> va_area m VA slots -> args_ok Fp 232 B 1024 m lo q (q - VF_FRAME) slots args ->
    stk ssegs m lo q -> ssp_cells m canary -> mem_inv ssegs m ->
    implM ssegs (vfprintf f ps) st (vfprintf_file_post rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF) fc None m (seg_rom ssegs)).
  Section Sz18.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend : ltac2:(SecDiet.SzSec.tyM 'vfprintf_file_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma vfprintf_file_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_file_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BLOC FB FLOC GLO HA HF HVA LO P1 PIECES SMALL. pin_using (fun (BLOC FB FLOC GLO HA HF HVA LO P1 PIECES SMALL : unit) => tt).
 intros -> -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY VAA AOK ST SSP MI.
    pose proof sinkfacts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold q in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    unfold fcells, file_cells in FC0.
    pose proof (rw_CB_length _ _ _ _ BUF0) as LBB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (wmono_refl ssegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    (* [comment removed for export] *)
    unfold vfprintf. rewrite BS. change (1024 =? 0) with false. cbv iota.
    (* [comment removed for export] *)
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash FC0. stash BUF0. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VFPRINTF.
    apply implM_prefix.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells ssegs ?mm ?A [CB 368 ?j] |- _ =>
        apply (rw_cells_split_CB ssegs mm A [] 368 j [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells ?sg _ _ _ => apply (proj1 (rw_cells_app sg _ _ [_;_;_] _)) in FR end.
    destruct FR as [FRlo FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    lazymatch type of FRhi with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -104)%Z in FRhi by lia end.
    do 12 zs. do 14 zs.
    lazymatch type of FRlo with rw_cells ?sg ?mm ?A ?cs1 => lazymatch type of FRhi with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in FRhi by (cbn [cells_size csize Nat.add]; lia);
      pose proof (proj2 (rw_cells_app sg mm A cs1 cs2) (conj FRlo FRhi)) as FR; clear FRlo FRhi end end.
    cbn [app] in FR.
    unfold hide in FC0, BUF0.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call ssegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (B, B + 1024)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; (keep_hyps sp Fp B lo x H; lia) | exact MUp]);
      unfold hide in BY, VAA;
      eapply (bytes_at_transport _ Wp ma mb) in BY; [| exact MUp | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; (keep_hyps sp A lo fmtz GLO HA; lia)];
      unfold va_area in VAA;
      eapply (bytes_at_transport _ Wp ma mb) in VAA; [| exact MUp | cbn [disjoint_from]; rewrite u64s_length; clear -HVA; (keep_hyps sp VA lo slots HVA; lia)]
    end.
    clear MUp. stash VAA.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. first [if_lit | brf Kl; [|exfalso; revert Kl; cbn; rewrite ?unsigned_lit by lia; cbn; lia]]. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. first [if_lit | brf Kb; [exfalso; revert Kb; cbn; rewrite ?unsigned_lit by lia; cbn; lia|]]. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    unfold hide in AOK, VAAm. clear BYm VAA. unfold va_area in VAAm.
    lazymatch type of MU with munch _ _ ?mc =>
      assert (VAA : va_area mc VA slots)
        by (unfold va_area; eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA FLOC BLOC GLO LO SPHI NNs; lia]) end.
    clear VAAm.
    pose proof (flags_ok_clr_err f flags FL0) as FL1.
    pose proof (flags_err_clear_lw f flags FL0) as OLDERR.
    destruct (f_wactive f) eqn:WACT.
    - (* [comment removed for export] *)
      zs. brf Kw; [| exfalso; revert Kw; rewrite ?unsigned_lit by lia; lia].
      apply evt_done. unfold ensure_w. rewrite WACT. apply implM_retb.
      eapply implM_ms_eq; [eapply (vf_pass2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) with (rpos := rpos) (rend := rend) | ms_eq].
      all: try first [ left; split; reflexivity | exact FC0 | exact FL1 | exact BUF0 | exact BP0 | exact WBL | exact FR | exact BY | exact VAA | unfold va_area; exact VAA | exact STc
                     | exact MU | exact WM | exact OLDERR | split; [exact SSP1 | exact SSP2] | assumption ].
      all: try (split; [exact WACT | split; [exact RB | split; [exact BS | split; [exact NW | split; [exact CH | split; [exact SWB | exact CHN]]]]]]).
      all: try (eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz bufbytes; lia) | exact MU | ]; repeat constructor; cbn [fst snd]; (keep_hyps sp lo fmtz bufbytes Fp B; lia)).
      all: match goal with |- ?g => idtac "VFB1-LEFT:" g end.
      all: fail.
    - (* [comment removed for export] *)
      zs. brf Kw; [exfalso; revert Kw; rewrite ?unsigned_lit by lia; lia |].
      zs. zs. zs. (* [comment removed for export] *)
      specialize (WB0 eq_refl).
      eapply evt_cut.
      { pose proof (flags_nowr_clear _ _ FL1 ltac:(cbn; exact NW)) as X8.
        eapply evt_ms_eq; [eapply towrite_specZ | ms_eq].
        all: first [ exact FC0 | exact X8 | assumption | lia | match goal with |- ?g => idtac "TW-LEFT:" g end ]. }
      cbv beta. intros ms' PO.
      destruct PO as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & mode' & m'' & -> & MUc & WMc & MIt & FCt).
      clear FC0. unfold va_area in VAA.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
      fix_ret.
      zs. if_lit. (* [comment removed for export] *)
      apply evt_done. unfold ensure_w, towrite. rewrite WACT, NW. apply implM_retb.
      eapply implM_ms_eq; [eapply (vf_pass2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) with (rpos := rpos) (rend := rend) (f1 := set_w true [] (set_rbuf [] f)) | ms_eq].
      all: try first [ right; split; reflexivity | exact FL1 | apply flags_ok_set_w; exact FL1 | exact BUF0 | exact WBL | exact FR | exact BY | exact VAA | unfold va_area; exact VAA | exact STc
                     | exact MU | exact WM | exact OLDERR | split; [exact SSP1 | exact SSP2] | assumption ].
      all: try (cbn [f_wbuf set_w set_rbuf zlength length Z.of_nat]; rewrite Z.add_0_r; unfold fcells, wfn_of, lbf_of; cbn; unfold wfn_of, lbf_of in FCt; exact FCt).
      all: try (split; [reflexivity | split; [reflexivity | split; [exact BS | split; [exact NW | split; [exact CH | split; [exact SWB | exact CHN]]]]]]).
      all: try (cbn [f_wbuf set_w set_rbuf length]; reflexivity).
      all: try (cbn [f_wbuf set_w set_rbuf]; unfold zlength; cbn [length Z.of_nat]; (keep_hyps sp fmtz bufbytes; lia)).
      all: try (eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz bufbytes; lia) | exact MU | ]; repeat constructor; cbn [fst snd]; (keep_hyps sp lo fmtz bufbytes Fp B; lia)).
      all: match goal with |- ?g => idtac "VFB2-LEFT:" g end.
      all: fail.
  Qed.
  End Sz18.
  Theorem vfprintf_file_spec : ltac:(let t := eval cbv delta [vfprintf_file_spec__stmt] in vfprintf_file_spec__stmt in exact t).
  Proof using BLOC FB FLOC GLO HA HF HVA LO P1 PIECES SMALL. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend. ltac2:(SecDiet.SzSec.closeP 'vfprintf_file_spec__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End VfFile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section VfUbf.
  Context {St : Type}.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B0 : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Let q := bv_unsigned sp.
  Let Bi := q - 352.   (* [comment removed for export] *)
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^47.   (* [comment removed for export] *)
  Hypothesis FLOC : (140840 <= Fp /\ Fp + 232 <= 343304) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis HB0 : 0 < B0 < 2^64.   (* [comment removed for export] *)

  #[local] Notation SINKu rpos rend := (SINK_file (St:=St) Fp Bi 80 rpos rend closefn readfn seekfn prev next tail false true).

  Definition vfprintf_ubf_post (m : mem) (st : St) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = [] /\ f_bufsize f' = 0 /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch [(lo, q); (Fp, Fp + 232)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo q
      /\ ssp_cells m' canary
      /\ rw_cells ssegs m' Fp (fcells flags' 0 0 closefn 0 0 0 readfn (wfn_of f') seekfn B0 0 prev next (f_fd f') mode' (lbf_of f') tail)
      /\ flags_ok f' flags'.

  Lemma sinkfacts_u : 0 <= Fp /\ 0 < Bi /\ 0 <= 80 <= 1024 /\ Bi + 80 <= 2^47 (* [comment removed for export] *) /\ Fp + 232 < 2^63 /\ (Bi + 80 <= Fp \/ Fp + 232 <= Bi)
    /\ (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) /\ (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp)
    /\ (Bi + 80 <= got_ssp \/ got_ssp + 8 <= Bi) /\ (Bi + 80 <= ssp_guard \/ ssp_guard + 8 <= Bi).
  Proof using FLOC GLO HVA LO fmtz. pin_using (fun (FLOC GLO HVA LO fmtz : unit) => tt).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold got_ssp, ssp_guard, GLOBALS_TOP, VF_FRAME, PC_DEPTH, q, Bi, zlength in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma flags_ok_ws : forall f fl act wb n, flags_ok f fl -> flags_ok (set_w act wb (set_bufsize n f)) fl.
  Proof using Type. pin_using tt. intros f fl act wb n FL. unfold flags_ok in *. cbn. exact FL. Qed.
  Lemma flags_ok_ws' : forall f fl act wb n, flags_ok (set_w act wb (set_bufsize n f)) fl -> flags_ok f fl.
  Proof using Type. pin_using tt. intros f fl act wb n FL. unfold flags_ok in *. cbn in FL. exact FL. Qed.

  (* [comment removed for export] *)
  Definition vf_pass2u__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m m1 : mem) (f1 : file_st) (st : St)
      (flags flags1 mode1 : word) (ibuf rest : list byte),
    rw_cells ssegs m1 Fp (fcells flags1 0 0 closefn (Bi + 80) (Bi + zlength (f_wbuf f1)) Bi readfn (wfn_of f1) seekfn Bi 80 prev next (f_fd f1) mode1 (lbf_of f1) tail) ->
    flags_ok f1 flags1 -> fsink_inv 80 false true f1 -> f_wbuf f1 = [] ->
    rw_cells ssegs m1 Bi [CB 80%nat ibuf] ->
    rw_cells ssegs m1 (q + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA)] ->
    rw_cells ssegs m1 (q + -272) [CB 168 rest; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                 C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at ssegs m1 A (zb fmtz) -> va_area m1 VA slots -> args_ok Fp 232 Bi 80 m1 lo q (q + -368) slots args ->
    stk ssegs m1 lo (q + -368) -> ssp_cells m1 canary -> mem_inv ssegs m1 ->
    munch [(lo, q); (Fp, Fp + 232)] m m1 -> wmono ssegs m m1 ->
    Z.land (bv_unsigned (sx32 flags)) 32 = 0 ->
    implM ssegs (f2 <- out_pieces f1 ps ;; f3 <- file_writefn f2 [] ;; mret (set_w false [] (set_bufsize 0 f3))) st (vfprintf_ubf_post m st)
      (MS (mkR x1 (Z_to_bv 64 (q + -368)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 B0) (sx32 flags) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bc9c) fc None m1 (seg_rom ssegs)).
  Section Sz22.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 ibuf rest : ltac2:(SecDiet.SzSec.tyM 'vf_pass2u__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma vf_pass2u__body : ltac2:(SecDiet.SzSec.bodyP 'vf_pass2u__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FLOC GLO HA HB0 HF HVA LO PIECES SMALL. pin_using (fun (FLOC GLO HA HB0 HF HVA LO PIECES SMALL : unit) => tt).
    intros FC1 FL1 INV1 WB1 BUF1 APC2 FR BY VAA AOK ST SSP MI MU WM OLDERR.
    pose proof sinkfacts_u as (K1 & K2 & K3 & K4 & K5 & KFB & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB. pose proof (rw_CB_length _ _ _ _ BUF1) as LBB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof INV1 as (WA1 & RB1 & BS1 & NW1 & CH1 & SW1 & CN1).
    (* [comment removed for export] *)
    pose proof (printf_core_proof (file_st * St) Fp 232 Fp Bi 80 (SINKu 0 0 st) TOPOK_file (OUT_file (St:=St))
                  (file_sink_frame Fp Bi 80 0 0 closefn readfn seekfn prev next tail false true st K3 KFB K6 K7 K8 K9)
                  (file_sink_flags Fp Bi 80 0 0 closefn readfn seekfn prev next tail false true st K1 K5)
                  file_topok
                  (file_out Fp Bi 80 0 0 closefn readfn seekfn prev next tail false true st K1 K2 K3 K4 KFB K6 K7 K8 K9)) as PC2.
    unfold printf_core_stmt in PC2.
    set (PCQ := printf_core_post (St:=file_st * St) Fp 232 Bi 80 (SINKu 0 0 st) (Z_to_bv 64 0x1bcb4) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp
                  (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 343304) (Z_to_bv 64 1) (Z_to_bv 64 B0) (sx32 flags) s6 s7 s8 s9 s10 s11 F fc
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -368) : word)) lo canary m1).
    unfold q, Bi in *.
    eapply implM_bind with (Q1 := fun f' st' ms' => PCQ r (f', st') ms').
    { { apply out_pieces_bridge; [exact SMALL|].
        eapply (printf_model_outs ssegs (OUT_file (St:=St)) fmtz args ps r mret); [exact PIECES|].
        apply implM_bind_mret.
        apply implM_prefix. do 5 zs. zs. apply evt_done.
        apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in APC2. destruct APC2 as [APC AP2]. cbn [cells_size csize Nat.add app] in AP2.
        replace (Z_to_bv 64 VA : word) with (Z_to_bv 64 (VA + 8 * 0) : word) in APC by (f_equal; lia).
        assert (SNK : SINK_file Fp (bv_unsigned sp - 352) 80 0 0 closefn readfn seekfn prev next tail false true st m1 (f1, st)).
        { split; [reflexivity|]. split; [exact INV1|]. exists flags1, mode1, ibuf. cbn [fst].
          split; [exact FC1|]. split; [exact FL1|]. split; [exact BUF1|]. rewrite WB1. split; [reflexivity| unfold zlength; cbn; lia]. }
        eapply implM_ms_eq; [eapply PC2 with (i := 0%Z) (slots := slots) | subst PCQ; ms_eq]; clear PC2; rewrite ?unsigned_lit by lia;
          unfold PC_DEPTH, GLOBALS_TOP, TOPOK_file, zlength.
        all: match goal with |- ?g => fastfirst (first [ noevar_assumption |
               exact SNK
             | exact BY | exact HF | reflexivity | exact APC | exact VAA | unfold va_area; exact VAA | exact I
             | cbn [skipn Z.to_nat]; eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz ibuf; lia) | apply (munch_refl []) | constructor]
             | exact ST | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption
             | (keep_hyps sp fmtz ibuf K4 Fp VA lo slots FLOC HVA; lia)
             | idtac "VFU2-LEFT:" g; fail ]) end. } }
    cbv beta. intros f2 st2 ms2 PO. clear PC2. subst PCQ.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & -> & -> & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    clear BY VAA AOK BUF1 FC1.
    apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in APC2. destruct APC2 as [_ AP2]. cbn [cells_size csize Nat.add app] in AP2.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in AP2 by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m3 MUc WMc; clear MUc WMc end.
    destruct SNK3 as (EST3 & INV3 & flags3 & mode3 & bufbytes3 & FC3 & FL3 & BUF3 & BP3 & WBL3). cbn [fst snd] in EST3, INV3, FC3, FL3, BUF3, BP3, WBL3. subst st2.
    pose proof INV3 as (WA3 & RB3 & BS3 & NW3 & CH3 & SW3 & CN3).
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (SWF : f_stdoutw f2 = false) by (destruct (f_stdoutw f2) eqn:E; [discriminate (SW3 eq_refl) | reflexivity]).
    assert (WFN : wfn_of f2 = F_STDIO_WRITE) by (unfold wfn_of; rewrite SWF; reflexivity).
    rewrite CN3 in CH3.
    pose proof (rw_CB_length _ _ _ _ BUF3) as LB3.
    assert (NNw : 0 <= zlength (f_wbuf f2)) by (unfold zlength; lia).
    pose proof (CB_prefix_bytes_at m3 (bv_unsigned sp - 352) (Z.to_nat 80) bufbytes3 (to_bytes (f_wbuf f2)) BUF3 ltac:(rewrite length_to_bytes; exact BP3)) as WBB.
    unfold fcells, file_cells in FC3. rewrite WFN in FC3. unfold F_STDIO_WRITE in FC3.
    apply implM_prefix. fix_ret.
    (* [comment removed for export] *)
    zs. zs. zs. brf Kb; [exfalso; revert Kb; rewrite ?unsigned_lit by lia; lia|].
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs.
    apply evt_done. unfold file_writefn. rewrite SWF.
    eapply implM_bind.
    { eapply implM_ms_eq;
        [eapply (stdio_write_spec (St:=St)) with (f := f2) (s := []) (S := 0) (lo := lo) (canary := canary) (Fp := Fp) (flags := flags3)
           (rpos := 0) (rend := 0) (closefn := closefn) (wend := bv_unsigned sp - 352 + 80) (readfn := readfn) (writefn := 111604) (seekfn := seekfn)
           (B := bv_unsigned sp - 352) (bufsize := 80) (prev := prev) (next := next) (mode := mode3) (lbf := lbf_of f2) (tail := tail)
        | unfold F_STDIO_WRITE; ms_eq].
      all: rewrite ?unsigned_lit by lia.
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | unfold fcells, file_cells; exact FC3 | exact WBB | apply bytes_at_nil; (keep_hyps sp fmtz ibuf bufbytes3; lia) | reflexivity | rewrite CN3; exact CH3 | exact ST3 | exact MI3
             | split; [exact SSP1 | exact SSP2] | left; reflexivity
             | unfold STDIO_WRITE_DEPTH, got_ssp, ssp_guard, zlength in *; cbn [length Z.of_nat] in *; (keep_hyps sp lo fmtz ibuf bufbytes3 LO K4 Fp B0 GLO FLOC K6 K7 SPHI VA slots f2 HVA WBL3 KFB; lia)
             | idtac "SWCALL-LEFT:" g; fail ]) end. }
    cbv beta. intros f3 st3 ms3 PO.
    destruct PO as (-> & -> & w5 & w6 & w7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w28 & w29 & w30 & w31 & m4 & -> & MUc & WMc & MI4 & ST4 & FC4 & SSP4).
    unfold sw_W, STDIO_WRITE_DEPTH in MUc. rewrite !unsigned_lit in MUc, ST4 by lia.
    clear FC3 WBB.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
    apply implM_ret. fix_ret.
    clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC4.
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs.
    zs. replace (0 <? bv_unsigned sp - 352)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
    zs. zs. rewrite ?Z.lor_0_l. zs.
    (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 (sx32 flags3)) as FR3. unfold bv_modulus in FR3. cbn in FR3.
    zs. zs. rewrite (flags_err_clear_lw f2 flags3 FL3). zs. rewrite OLDERR, Z.lor_0_r.
    zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with AP : rw_cells _ mm (bv_unsigned sp + -368)%Z [C8 ?apv'], B3 : rw_cells _ mm (q - 352)%Z [CB _ ?bb], R : rw_cells _ mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
      assert (FALL : rw_cells ssegs mm (bv_unsigned sp + -368) ([C8 apv'] ++ [C8 (Z_to_bv 64 VA)] ++ [CB (Z.to_nat 80) bb] ++ rest));
      [ apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact AP2 | lia]|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact B3 | unfold q; lia]|]; cbn [cells_size csize Nat.add Z.to_nat Pos.to_nat Pos.iter_op Nat.mul];
        eapply rwc_eqA; [exact R | lia]
      | clear AP AP2 B3 R ] end end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -368)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evt_done. unfold vfprintf_ubf_post, q. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [cbn; exact RB3|]. split; [reflexivity|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [unfold fcells, file_cells; cbn [f_fd set_w set_bufsize]; unfold wfn_of, lbf_of in *; cbn [f_stdoutw f_lbf_nl set_w set_bufsize]; rewrite SWF; unfold F_STDIO_WRITE; exact FC4|].
    apply flags_ok_ws. apply flags_ok_relw. exact FL3.
  Qed.
  End Sz22.
  Lemma vf_pass2u : ltac:(let t := eval cbv delta [vf_pass2u__stmt] in vf_pass2u__stmt in exact t).
  Proof using FLOC GLO HA HB0 HF HVA LO PIECES SMALL. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 ibuf rest. ltac2:(SecDiet.SzSec.closeP 'vf_pass2u__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition vfprintf_ubf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (rpos rend we wp wb : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells ssegs m Fp (fcells flags rpos rend closefn we wp wb readfn (wfn_of f) seekfn B0 0 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags -> f_bufsize f = 0 -> f_nowr f = false -> f_rbuf f = [] -> f_wbuf f = [] ->
    f_chan f = true -> (f_fd f = 1 \/ f_fd f = 2) -> f_stdoutw f = false ->
    0 <= we < 2^64 -> 0 <= wp < 2^64 -> 0 <= wb < 2^64 -> 0 <= rpos < 2^64 -> 0 <= rend < 2^64 ->
    bytes_at ssegs m A (zb fmtz) -> va_area m VA slots -> args_ok Fp 232 Bi 80 m lo q (q - VF_FRAME) slots args ->
    stk ssegs m lo q -> ssp_cells m canary -> mem_inv ssegs m ->
    implM ssegs (vfprintf f ps) st (vfprintf_ubf_post m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF) fc None m (seg_rom ssegs)).
  Section Sz23.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode rpos rend we wp wb : ltac2:(SecDiet.SzSec.tyM 'vfprintf_ubf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma vfprintf_ubf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_ubf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FLOC GLO HA HB0 HF HVA LO P1 PIECES SMALL. pin_using (fun (FLOC GLO HA HB0 HF HVA LO P1 PIECES SMALL : unit) => tt).
 intros -> -> -> FC0 FL0 BS NW RB WB CHN FD SWF Rwe Rwp Rwb Rrp Rre BY VAA AOK ST SSP MI.
    pose proof sinkfacts_u as (K1 & K2 & K3 & K4 & K5 & KFB & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold q, Bi in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    unfold fcells, file_cells in FC0.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (wmono_refl ssegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    (* [comment removed for export] *)
    unfold vfprintf. rewrite BS. change (0 =? 0) with true. cbv iota.
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash FC0. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VFPRINTF.
    apply implM_prefix.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells ssegs ?mm ?A [CB 368 ?j] |- _ =>
        apply (rw_cells_split_CB ssegs mm A [] 368 j [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells ?sg _ _ _ => apply (proj1 (rw_cells_app sg _ _ [_;_;_] _)) in FR end.
    destruct FR as [FRlo FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    lazymatch type of FRhi with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -104)%Z in FRhi by lia end.
    do 12 zs. do 14 zs.
    lazymatch type of FRlo with rw_cells ?sg ?mm ?A ?cs1 => lazymatch type of FRhi with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in FRhi by (cbn [cells_size csize Nat.add]; lia);
      pose proof (proj2 (rw_cells_app sg mm A cs1 cs2) (conj FRlo FRhi)) as FR; clear FRlo FRhi end end.
    cbn [app] in FR.
    unfold hide in FC0.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call ssegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]);
      unfold hide in BY, VAA;
      eapply (bytes_at_transport _ Wp ma mb) in BY; [| exact MUp | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; lia];
      unfold va_area in VAA;
      eapply (bytes_at_transport _ Wp ma mb) in VAA; [| exact MUp | cbn [disjoint_from]; rewrite u64s_length; clear -HVA; lia]
    end.
    clear MUp. stash VAA.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. first [if_lit | brf Kl; [|exfalso; revert Kl; cbn; rewrite ?unsigned_lit by lia; cbn; lia]]. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    do 8 zs. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    unfold hide in AOK, VAAm. clear BYm VAA. unfold va_area in VAAm.
    lazymatch type of MU with munch _ _ ?mc =>
      assert (VAA : bytes_at ssegs mc VA (u64s slots))
        by (eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA FLOC GLO LO SPHI NNs; lia]) end.
    clear VAAm.
    pose proof (flags_ok_clr_err f flags FL0) as FL1.
    pose proof (flags_err_clear_lw f flags FL0) as OLDERR.
    pose proof (flags_nowr_clear _ _ FL1 ltac:(cbn; exact NW)) as X8.
    eapply evt_cut.
    { eapply evt_ms_eq; [eapply towrite_specZ | ms_eq].
      all: first [ exact FC0 | exact X8 | assumption | lia | match goal with |- ?g => idtac "TWU-LEFT:" g end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & mode' & m'' & -> & MUc & WMc & MIt & FCt).
    clear FC0.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. (* [comment removed for export] *)
    apply evt_done. unfold towrite. cbn [f_nowr set_w set_bufsize]. rewrite NW. apply implM_retb.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ _ (bv_unsigned sp + -368)%Z (_ :: _ :: CB 248 _ :: _) |- _ => rename H into FRv end.
    apply (rw_cells_split_CB ssegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app ssegs _ _ [_; _] _)) in FRv. destruct FRv as [APC2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in FRv. destruct FRv as [IBc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr IBc (bv_unsigned sp - 352)%Z. readdr FRv (bv_unsigned sp + -272)%Z.
    eapply implM_ms_eq; [eapply (vf_pass2u _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) with (f1 := set_w true [] (set_rbuf [] (set_w false [] (set_bufsize 80 f)))) | ms_eq].
    all: try first [ exact FL1 | apply flags_ok_ws; exact FL1 | exact IBc | exact APC2 | exact FRv | exact BY | unfold va_area; exact VAA | exact STc
                   | exact MU | exact WM | exact OLDERR | split; [exact SSP1 | exact SSP2] | assumption ].
    all: try (lazymatch goal with |- rw_cells _ _ Fp ?cs1 => lazymatch type of FCt with rw_cells _ _ _ ?cs0 =>
                replace cs1 with cs0; [exact FCt|];
                unfold fcells, file_cells, wfn_of, lbf_of; cbn [f_wbuf f_fd f_stdoutw f_lbf_nl set_w set_rbuf set_bufsize]; unfold zlength; cbn [length Z.of_nat];
                rewrite ?unsigned_lit by lia; repeat fastfirst (first [reflexivity | (keep_hyps sp fmtz; lia) | progress f_equal]) end end).
    all: try (unfold fsink_inv; cbn [f_wactive f_rbuf f_bufsize f_nowr f_chan f_fd f_stdoutw set_w set_rbuf set_bufsize];
              split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact NW | split; [rewrite CHN; exact FD | split; [rewrite SWF; discriminate | exact CHN]]]]]]).
    all: try (cbn [f_wbuf set_w set_rbuf set_bufsize]; reflexivity).
    all: try (eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz; lia) | exact MU | ]; repeat constructor; cbn [fst snd]; (keep_hyps sp lo fmtz Fp; lia)).
    all: match goal with |- ?g => idtac "VFUB-LEFT:" g end.
    all: fail.
  Qed.
  End Sz23.
  Theorem vfprintf_ubf_spec : ltac:(let t := eval cbv delta [vfprintf_ubf_spec__stmt] in vfprintf_ubf_spec__stmt in exact t).
  Proof using FLOC GLO HA HB0 HF HVA LO P1 PIECES SMALL. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode rpos rend we wp wb. ltac2:(SecDiet.SzSec.closeP 'vfprintf_ubf_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End VfUbf.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.FP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_printf_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Printf_fsink.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Lemma rwc_eqA : forall m A A' cs, rw_cells usegs m A cs -> A = A' -> rw_cells usegs m A' cs.
Proof. intros m A A' cs H ->. exact H. Qed.
Ltac readdr H A' := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let H' := fresh in assert (H' : rw_cells usegs m A' cs) by (eapply rwc_eqA; [exact H | lia]); clear H; rename H' into H end.

Definition VFPRINTF : Z := 0x1c36c.
Definition TOWRITE : Z := 0x1c0d4.
Definition VF_FRAME : Z := 368.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
  intros f c k Hk Hc. rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof. intros a. change 128 with (2^7). rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity. Qed.
Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, bv_swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
  rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296. change (2^31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.
Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

(* [comment removed for export] *)
Definition flags_ok_clr_err__stmt : Prop := forall f (flags : word),
  flags_ok f flags -> flags_ok f (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)).
Section Sz6.
Variables f flags : ltac2:(SecDiet.SzSec.tyM 'flags_ok_clr_err__stmt "vv" @f).
#[using="Type"] Lemma flags_ok_clr_err__body : ltac2:(SecDiet.SzSec.bodyP 'flags_ok_clr_err__stmt "vv").
Proof.
  intros FL.
 pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R.
  pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583) as LR.
  unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM in *. rewrite unsigned_lit by lia.
  destruct FL as (A1 & A2 & A3 & A4 & A5 & A6).
  rewrite <- !Z.land_assoc.
  change (Z.land 18446744073709551583 4) with 4. change (Z.land 18446744073709551583 8) with 8.
  change (Z.land 18446744073709551583 16) with 16. change (Z.land 18446744073709551583 32) with 0.
  change (Z.land 18446744073709551583 64) with 64. change (Z.land 18446744073709551583 1) with 1.
  rewrite Z.land_0_r.
  repeat split; try reflexivity; rewrite land_low7, sx32_mod128, <- land_low7 by lia; assumption.
Qed.
End Sz6.
Lemma flags_ok_clr_err : ltac:(let t := eval cbv delta [flags_ok_clr_err__stmt] in flags_ok_clr_err__stmt in exact t).
Proof. intros f flags. ltac2:(SecDiet.SzSec.closeP 'flags_ok_clr_err__body "vv"). Qed.

(* [comment removed for export] *)
Lemma flags_ok_relw : forall f (flags : word), flags_ok f flags -> flags_ok f (sx32 flags).
Proof.
  intros f flags FL. unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM in *.
  destruct FL as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat split; rewrite land_low7, sx32_mod128, <- land_low7 by lia; assumption.
Qed.

Lemma flags_err_clear_lw : forall f (flags : word), flags_ok f flags -> Z.land (bv_unsigned (sx32 flags)) 32 = 0.
Proof.
  intros f flags (_ & _ & _ & A4 & _). rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact A4.
Qed.
Lemma flags_nowr_clear : forall f (flags : word), flags_ok f flags -> f_nowr f = false -> Z.land (bv_unsigned flags) 8 = 0.
Proof. intros f flags (_ & A2 & _) NW. unfold F_NOWR in A2. rewrite NW in A2. exact A2. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Forall_disj_vff : forall (W : list (Z * Z)) lo sp Fp FS B BS a n,
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  (a + n <= lo \/ sp <= a) -> (a + n <= Fp \/ Fp + FS <= a) -> (a + n <= B \/ B + BS <= a) -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W lo sp Fp FS B BS a n H H1 H2 H3 Hn. induction H as [|[u1 u2] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.
Definition arg_ok_vff__stmt : Prop := forall Fp FS B BS m m' lo sp sp' ap w a (W : list (Z * Z)),
  arg_ok Fp FS B BS m lo sp ap w a -> sp' <= sp -> munch W m m' ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  arg_ok Fp FS B BS m' lo sp' ap w a.
Section Sz11.
Variables Fp FS B BS m m' lo sp sp' ap w a W : ltac2:(SecDiet.SzSec.tyM 'arg_ok_vff__stmt "vvvvvvvvvvvvv" @Fp).
#[using="Type"] Lemma arg_ok_vff__body : ltac2:(SecDiet.SzSec.bodyP 'arg_ok_vff__stmt "vvvvvvvvvvvvv").
Proof.
  intros H Hsp MU HW.
 destruct a as [s|i|u|u]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & S47). exists slack.   (* [comment removed for export] *)
  split; [|repeat (split; [fastfirst (first [assumption | lia])|]); exact S47].
  eapply bytes_at_transport; [exact BY | exact MU |].
  rewrite length_app, zb_length. cbn [length]. unfold zlength in *.
  eapply Forall_disj_vff; [exact HW | | | | lia]; lia.
Qed.
End Sz11.
Lemma arg_ok_vff : ltac:(let t := eval cbv delta [arg_ok_vff__stmt] in arg_ok_vff__stmt in exact t).
Proof. intros Fp FS B BS m m' lo sp sp' ap w a W. ltac2:(SecDiet.SzSec.closeP 'arg_ok_vff__body "vvvvvvvvvvvvv"). Qed.
Lemma args_ok_vff : forall Fp FS B BS m m' lo sp sp' ap ws args (W : list (Z * Z)),
  args_ok Fp FS B BS m lo sp ap ws args -> sp' <= sp -> munch W m m' ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  args_ok Fp FS B BS m' lo sp' ap ws args.
Proof.
  intros Fp FS B BS m m' lo sp sp' ap ws args W. revert ws. induction args as [|a args IH]; intros ws H Hsp MU HW; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vff; eassumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MonadFacts.
  Context {St : Type}.
  #[local] Notation impl := (ITree.impl usegs (at_node usegs) (npeek usegs)).

  (* [comment removed for export] *)
  Lemma implM_bind_mret : forall {A} (c : M St A) s Q ms,
    implM usegs c s Q ms -> implM usegs (mbind c mret) s Q ms.
  Proof using Type. pin_using tt.
    intros A c s Q ms H. unfold implM, mbind, ebind in *.
    generalize dependent ms. generalize (c s) as t. induction t as [r|n k IH]; intros ms H; cbn [ITree.bind] in *.
    - destruct r as [[a s']|]; cbn in *; exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)].
      + left. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
      + right. exists g. split; [exact Hg|]. apply IH. apply Hk.
  Qed.

  Lemma implM_ms_eq : forall {A} (c : M St A) s Q ms ms', implM usegs c s Q ms' -> ms = ms' -> implM usegs c s Q ms.
  Proof using Type. pin_using tt. intros A c s Q ms ms' H ->. exact H. Qed.
End MonadFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section VfFile.
  Context {St : Type}.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Variables (sw0 ch0 : bool).
  Let q := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^47.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis FLOC : (142824 <= Fp /\ Fp + 232 <= 345288) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis BLOC : (345296 <= B /\ B + 1024 <= GLOBALS_TOP) \/ (0 < B /\ B + 1024 <= lo /\ (B + 1024 <= 65536 \/ GLOBALS_TOP <= B)).
  Hypothesis FB : B + 1024 <= Fp \/ Fp + 232 <= B.

  #[local] Notation SINKf rpos rend := (SINK_file (St:=St) Fp B 1024 rpos rend closefn readfn seekfn prev next tail sw0 ch0).
  #[local] Notation OUTf := (OUT_file (St:=St)).

  (* [comment removed for export] *)
  Definition vfprintf_file_post (rpos rend : Z) (m : mem) (st : St) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fsink_inv 1024 sw0 ch0 f' /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (bufbytes' : list byte) (m' : mem) (rpos' rend' : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(lo, q); (Fp, Fp + 232); (B, B + 1024)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo q
      /\ ssp_cells m' canary
      /\ rw_cells usegs m' Fp (fcells flags' rpos' rend' closefn (B + 1024) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B 1024 prev next (f_fd f') mode' (lbf_of f') tail)
      /\ ((rpos' = rpos /\ rend' = rend) \/ (rpos' = 0 /\ rend' = 0))
      /\ flags_ok f' flags'
      /\ rw_cells usegs m' B [CB 1024%nat bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= 1024.

  (* [comment removed for export] *)
  Lemma sinkfacts : 0 <= Fp /\ 0 < B /\ 0 <= 1024 <= 1024 /\ B + 1024 <= 2^47 (* [comment removed for export] *) /\ Fp + 232 < 2^63
    /\ (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) /\ (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp)
    /\ (B + 1024 <= got_ssp \/ got_ssp + 8 <= B) /\ (B + 1024 <= ssp_guard \/ ssp_guard + 8 <= B).
  Proof using BLOC FLOC HVA LO fmtz. pin_using (fun (BLOC FLOC HVA LO fmtz : unit) => tt).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold got_ssp, ssp_guard, GLOBALS_TOP, VF_FRAME, PC_DEPTH, q, zlength in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Definition vf_pass2__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m m1 : mem) (f1 : file_st) (st : St)
      (flags flags1 mode1 : word) (bufbytes1 junk : list byte) (rpos rend rpos1 rend1 : Z),
    ((rpos1 = rpos /\ rend1 = rend) \/ (rpos1 = 0 /\ rend1 = 0)) ->
    rw_cells usegs m1 Fp (fcells flags1 rpos1 rend1 closefn (B + 1024) (B + zlength (f_wbuf f1)) B readfn (wfn_of f1) seekfn B 1024 prev next (f_fd f1) mode1 (lbf_of f1) tail) ->
    flags_ok f1 flags1 -> fsink_inv 1024 sw0 ch0 f1 ->
    rw_cells usegs m1 B [CB 1024%nat bufbytes1] -> firstn (length (f_wbuf f1)) bufbytes1 = to_bytes (f_wbuf f1) -> zlength (f_wbuf f1) <= 1024 ->
    rw_cells usegs m1 (q + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 248 junk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                   C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at usegs m1 A (zb fmtz) -> va_area m1 VA slots -> args_ok Fp 232 B 1024 m1 lo q (q + -368) slots args ->
    stk usegs m1 lo (q + -368) -> ssp_cells m1 canary -> mem_inv usegs m1 ->
    munch [(lo, q); (Fp, Fp + 232); (B, B + 1024)] m m1 -> wmono usegs m m1 ->
    Z.land (bv_unsigned (sx32 flags)) 32 = 0 ->
    implM usegs (out_pieces f1 ps) st (vfprintf_file_post rpos rend m st)
      (MS (mkR x1 (Z_to_bv 64 (q + -368)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 0) (sx32 flags) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1c45c) fc None m1 (seg_rom usegs)).
  Section Sz16.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 bufbytes1 junk rpos rend rpos1 rend1 : ltac2:(SecDiet.SzSec.tyM 'vf_pass2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma vf_pass2__body : ltac2:(SecDiet.SzSec.bodyP 'vf_pass2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BLOC FB FLOC GLO HA HF HVA LO PIECES SMALL. pin_using (fun (BLOC FB FLOC GLO HA HF HVA LO PIECES SMALL : unit) => tt).
 intros RP FC1 FL1 INV1 BUF1 BP1 WBL1 FR BY VAA AOK ST SSP MI MU WM OLDERR.
    pose proof sinkfacts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold q in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB. pose proof (rw_CB_length _ _ _ _ BUF1) as LBB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof INV1 as (WA1 & RB1 & BS1 & NW1 & CH1 & SW1 & CN1).
    (* [comment removed for export] *)
    pose proof (printf_core_proof (file_st * St) Fp 232 Fp B 1024 (SINKf rpos1 rend1 st) TOPOK_file OUTf
                  (file_sink_frame Fp B 1024 rpos1 rend1 closefn readfn seekfn prev next tail sw0 ch0 st K3 FB K6 K7 K8 K9)
                  (file_sink_flags Fp B 1024 rpos1 rend1 closefn readfn seekfn prev next tail sw0 ch0 st K1 K5)
                  file_topok
                  (file_out Fp B 1024 rpos1 rend1 closefn readfn seekfn prev next tail sw0 ch0 st K1 K2 K3 K4 FB K6 K7 K8 K9)) as PC2.
    unfold printf_core_stmt in PC2.
    set (PCQ := printf_core_post (St:=file_st * St) Fp 232 B 1024 (SINKf rpos1 rend1 st) (Z_to_bv 64 0x1c474) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp
                  (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 345288) (Z_to_bv 64 1) (Z_to_bv 64 0) (sx32 flags) s6 s7 s8 s9 s10 s11 F fc
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -368) : word)) lo canary m1).
    apply (implM_post_evt usegs (out_pieces f1 ps) st (fun f' st' ms' => PCQ r (f', st') ms')).
    { apply out_pieces_bridge; [exact SMALL|].
      eapply (printf_model_outs usegs OUTf fmtz args ps r mret); [exact PIECES|].
      apply implM_bind_mret.
      apply implM_prefix. do 5 zs. zs. apply evt_done.
      apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      replace (Z_to_bv 64 VA : word) with (Z_to_bv 64 (VA + 8 * 0) : word) in APC by (f_equal; lia).
      eapply implM_ms_eq; [eapply PC2 with (i := 0%Z) (slots := slots) | subst PCQ; ms_eq]; clear PC2; rewrite ?unsigned_lit by lia;
        unfold PC_DEPTH, GLOBALS_TOP, TOPOK_file, zlength.
      all: match goal with |- ?g => fastfirst (first [ noevar_assumption |
             (* [comment removed for export] *) split; [reflexivity | split; [exact INV1 | exists flags1, mode1, bufbytes1; cbn [fst]; split; [exact FC1 | split; [exact FL1 | split; [exact BUF1 | split; [exact BP1 | exact WBL1]]]]]]
           | exact BY | exact HF | reflexivity | exact APC | exact VAA | exact I
           | cbn [skipn Z.to_nat]; eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz bufbytes1; lia) | apply (munch_refl []) | constructor]
           | exact ST | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption
           | (keep_hyps sp VA fmtz slots bufbytes1 HVA Fp lo FLOC B GLO BLOC; lia)
           | idtac "VFP2-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' PO. clear PC2. subst PCQ.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & -> & -> & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FR. destruct FR as [_ FR]. cbn [cells_size csize Nat.add app] in FR.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
    clear BY VAA AOK BUF1 FC1.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
    fix_ret.
    destruct SNK3 as (EST3 & INV3 & flags3 & mode3 & bufbytes3 & FC3 & FL3 & BUF3 & BP3 & WBL3). cbn [fst snd] in EST3, INV3, FC3, FL3, BUF3, BP3, WBL3. subst st'.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC3.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 (sx32 flags3)) as FR3. unfold bv_modulus in FR3. cbn in FR3.
    zs. zs. rewrite (flags_err_clear_lw f' flags3 FL3). zs. rewrite OLDERR, Z.lor_0_r.
    zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA); CB 248 junk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                   C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact APC3|]; cbn [cells_size csize Nat.add app]; eapply rwc_eqA; [exact FR | lia]
      | clear APC3 FR ] end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -368)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evt_done. unfold vfprintf_file_post, q. split; [reflexivity|]. split; [exact INV3|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [unfold fcells, file_cells; exact FC3|].
    split; [exact RP|].
    split; [apply flags_ok_relw; exact FL3|].
    split; [exact BUF3|]. split; [exact BP3| exact WBL3].
  Qed.
  End Sz16.
  Lemma vf_pass2 : ltac:(let t := eval cbv delta [vf_pass2__stmt] in vf_pass2__stmt in exact t).
  Proof using BLOC FB FLOC GLO HA HF HVA LO PIECES SMALL. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 bufbytes1 junk rpos rend rpos1 rend1. ltac2:(SecDiet.SzSec.closeP 'vf_pass2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma flags_ok_set_w : forall f fl act wb, flags_ok f fl -> flags_ok (set_w act wb (set_rbuf [] f)) fl.
  Proof using Type. pin_using tt. intros f fl act wb FL. unfold flags_ok in *. cbn. exact FL. Qed.

  Definition vfprintf_file_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells usegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells usegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at usegs m A (zb fmtz) -> va_area m VA slots -> args_ok Fp 232 B 1024 m lo q (q - VF_FRAME) slots args ->
    stk usegs m lo q -> ssp_cells m canary -> mem_inv usegs m ->
    implM usegs (vfprintf f ps) st (vfprintf_file_post rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF) fc None m (seg_rom usegs)).
  Section Sz18.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend : ltac2:(SecDiet.SzSec.tyM 'vfprintf_file_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma vfprintf_file_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_file_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BLOC FB FLOC GLO HA HF HVA LO P1 PIECES SMALL. pin_using (fun (BLOC FB FLOC GLO HA HF HVA LO P1 PIECES SMALL : unit) => tt).
 intros -> -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY VAA AOK ST SSP MI.
    pose proof sinkfacts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold q in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    unfold fcells, file_cells in FC0.
    pose proof (rw_CB_length _ _ _ _ BUF0) as LBB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    (* [comment removed for export] *)
    unfold vfprintf. rewrite BS. change (1024 =? 0) with false. cbv iota.
    (* [comment removed for export] *)
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash FC0. stash BUF0. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VFPRINTF.
    apply implM_prefix.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells usegs ?mm ?A [CB 368 ?j] |- _ =>
        apply (rw_cells_split_CB usegs mm A [] 368 j [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells ?sg _ _ _ => apply (proj1 (rw_cells_app sg _ _ [_;_;_] _)) in FR end.
    destruct FR as [FRlo FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    lazymatch type of FRhi with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -104)%Z in FRhi by lia end.
    do 12 zs. do 14 zs.
    lazymatch type of FRlo with rw_cells ?sg ?mm ?A ?cs1 => lazymatch type of FRhi with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in FRhi by (cbn [cells_size csize Nat.add]; lia);
      pose proof (proj2 (rw_cells_app sg mm A cs1 cs2) (conj FRlo FRhi)) as FR; clear FRlo FRhi end end.
    cbn [app] in FR.
    unfold hide in FC0, BUF0.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call usegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (B, B + 1024)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; (keep_hyps sp Fp B lo x H; lia) | exact MUp]);
      unfold hide in BY, VAA;
      eapply (bytes_at_transport _ Wp ma mb) in BY; [| exact MUp | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; (keep_hyps sp A lo fmtz GLO HA; lia)];
      unfold va_area in VAA;
      eapply (bytes_at_transport _ Wp ma mb) in VAA; [| exact MUp | cbn [disjoint_from]; rewrite u64s_length; clear -HVA; (keep_hyps sp VA lo slots HVA; lia)]
    end.
    clear MUp. stash VAA.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. first [if_lit | brf Kl; [|exfalso; revert Kl; cbn; rewrite ?unsigned_lit by lia; cbn; lia]]. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. first [if_lit | brf Kb; [exfalso; revert Kb; cbn; rewrite ?unsigned_lit by lia; cbn; lia|]]. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    unfold hide in AOK, VAAm. clear BYm VAA. unfold va_area in VAAm.
    lazymatch type of MU with munch _ _ ?mc =>
      assert (VAA : va_area mc VA slots)
        by (unfold va_area; eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA FLOC BLOC GLO LO SPHI NNs; lia]) end.
    clear VAAm.
    pose proof (flags_ok_clr_err f flags FL0) as FL1.
    pose proof (flags_err_clear_lw f flags FL0) as OLDERR.
    destruct (f_wactive f) eqn:WACT.
    - (* [comment removed for export] *)
      zs. brf Kw; [| exfalso; revert Kw; rewrite ?unsigned_lit by lia; lia].
      apply evt_done. unfold ensure_w. rewrite WACT. apply implM_retb.
      eapply implM_ms_eq; [eapply (vf_pass2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) with (rpos := rpos) (rend := rend) | ms_eq].
      all: try first [ left; split; reflexivity | exact FC0 | exact FL1 | exact BUF0 | exact BP0 | exact WBL | exact FR | exact BY | exact VAA | unfold va_area; exact VAA | exact STc
                     | exact MU | exact WM | exact OLDERR | split; [exact SSP1 | exact SSP2] | assumption ].
      all: try (split; [exact WACT | split; [exact RB | split; [exact BS | split; [exact NW | split; [exact CH | split; [exact SWB | exact CHN]]]]]]).
      all: try (eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz bufbytes; lia) | exact MU | ]; repeat constructor; cbn [fst snd]; (keep_hyps sp lo fmtz bufbytes Fp B; lia)).
      all: match goal with |- ?g => idtac "VFB1-LEFT:" g end.
      all: fail.
    - (* [comment removed for export] *)
      zs. brf Kw; [exfalso; revert Kw; rewrite ?unsigned_lit by lia; lia |].
      zs. zs. zs. (* [comment removed for export] *)
      specialize (WB0 eq_refl).
      eapply evt_cut.
      { pose proof (flags_nowr_clear _ _ FL1 ltac:(cbn; exact NW)) as X8.
        eapply evt_ms_eq; [eapply towrite_specZ | ms_eq].
        all: first [ exact FC0 | exact X8 | assumption | lia | match goal with |- ?g => idtac "TW-LEFT:" g end ]. }
      cbv beta. intros ms' PO.
      destruct PO as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & mode' & m'' & -> & MUc & WMc & MIt & FCt).
      clear FC0. unfold va_area in VAA.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
      fix_ret.
      zs. if_lit. (* [comment removed for export] *)
      apply evt_done. unfold ensure_w, towrite. rewrite WACT, NW. apply implM_retb.
      eapply implM_ms_eq; [eapply (vf_pass2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) with (rpos := rpos) (rend := rend) (f1 := set_w true [] (set_rbuf [] f)) | ms_eq].
      all: try first [ right; split; reflexivity | exact FL1 | apply flags_ok_set_w; exact FL1 | exact BUF0 | exact WBL | exact FR | exact BY | exact VAA | unfold va_area; exact VAA | exact STc
                     | exact MU | exact WM | exact OLDERR | split; [exact SSP1 | exact SSP2] | assumption ].
      all: try (cbn [f_wbuf set_w set_rbuf zlength length Z.of_nat]; rewrite Z.add_0_r; unfold fcells, wfn_of, lbf_of; cbn; unfold wfn_of, lbf_of in FCt; exact FCt).
      all: try (split; [reflexivity | split; [reflexivity | split; [exact BS | split; [exact NW | split; [exact CH | split; [exact SWB | exact CHN]]]]]]).
      all: try (cbn [f_wbuf set_w set_rbuf length]; reflexivity).
      all: try (cbn [f_wbuf set_w set_rbuf]; unfold zlength; cbn [length Z.of_nat]; (keep_hyps sp fmtz bufbytes; lia)).
      all: try (eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz bufbytes; lia) | exact MU | ]; repeat constructor; cbn [fst snd]; (keep_hyps sp lo fmtz bufbytes Fp B; lia)).
      all: match goal with |- ?g => idtac "VFB2-LEFT:" g end.
      all: fail.
  Qed.
  End Sz18.
  Theorem vfprintf_file_spec : ltac:(let t := eval cbv delta [vfprintf_file_spec__stmt] in vfprintf_file_spec__stmt in exact t).
  Proof using BLOC FB FLOC GLO HA HF HVA LO P1 PIECES SMALL. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend. ltac2:(SecDiet.SzSec.closeP 'vfprintf_file_spec__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End VfFile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section VfUbf.
  Context {St : Type}.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B0 : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Let q := bv_unsigned sp.
  Let Bi := q - 352.   (* [comment removed for export] *)
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^47.   (* [comment removed for export] *)
  Hypothesis FLOC : (142824 <= Fp /\ Fp + 232 <= 345288) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis HB0 : 0 < B0 < 2^64.   (* [comment removed for export] *)

  #[local] Notation SINKu rpos rend := (SINK_file (St:=St) Fp Bi 80 rpos rend closefn readfn seekfn prev next tail false true).

  Definition vfprintf_ubf_post (m : mem) (st : St) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = [] /\ f_bufsize f' = 0 /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(lo, q); (Fp, Fp + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo q
      /\ ssp_cells m' canary
      /\ rw_cells usegs m' Fp (fcells flags' 0 0 closefn 0 0 0 readfn (wfn_of f') seekfn B0 0 prev next (f_fd f') mode' (lbf_of f') tail)
      /\ flags_ok f' flags'.

  Lemma sinkfacts_u : 0 <= Fp /\ 0 < Bi /\ 0 <= 80 <= 1024 /\ Bi + 80 <= 2^47 (* [comment removed for export] *) /\ Fp + 232 < 2^63 /\ (Bi + 80 <= Fp \/ Fp + 232 <= Bi)
    /\ (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) /\ (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp)
    /\ (Bi + 80 <= got_ssp \/ got_ssp + 8 <= Bi) /\ (Bi + 80 <= ssp_guard \/ ssp_guard + 8 <= Bi).
  Proof using FLOC GLO HVA LO fmtz. pin_using (fun (FLOC GLO HVA LO fmtz : unit) => tt).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold got_ssp, ssp_guard, GLOBALS_TOP, VF_FRAME, PC_DEPTH, q, Bi, zlength in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma flags_ok_ws : forall f fl act wb n, flags_ok f fl -> flags_ok (set_w act wb (set_bufsize n f)) fl.
  Proof using Type. pin_using tt. intros f fl act wb n FL. unfold flags_ok in *. cbn. exact FL. Qed.
  Lemma flags_ok_ws' : forall f fl act wb n, flags_ok (set_w act wb (set_bufsize n f)) fl -> flags_ok f fl.
  Proof using Type. pin_using tt. intros f fl act wb n FL. unfold flags_ok in *. cbn in FL. exact FL. Qed.

  (* [comment removed for export] *)
  Definition vf_pass2u__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m m1 : mem) (f1 : file_st) (st : St)
      (flags flags1 mode1 : word) (ibuf rest : list byte),
    rw_cells usegs m1 Fp (fcells flags1 0 0 closefn (Bi + 80) (Bi + zlength (f_wbuf f1)) Bi readfn (wfn_of f1) seekfn Bi 80 prev next (f_fd f1) mode1 (lbf_of f1) tail) ->
    flags_ok f1 flags1 -> fsink_inv 80 false true f1 -> f_wbuf f1 = [] ->
    rw_cells usegs m1 Bi [CB 80%nat ibuf] ->
    rw_cells usegs m1 (q + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA)] ->
    rw_cells usegs m1 (q + -272) [CB 168 rest; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                 C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at usegs m1 A (zb fmtz) -> va_area m1 VA slots -> args_ok Fp 232 Bi 80 m1 lo q (q + -368) slots args ->
    stk usegs m1 lo (q + -368) -> ssp_cells m1 canary -> mem_inv usegs m1 ->
    munch [(lo, q); (Fp, Fp + 232)] m m1 -> wmono usegs m m1 ->
    Z.land (bv_unsigned (sx32 flags)) 32 = 0 ->
    implM usegs (f2 <- out_pieces f1 ps ;; f3 <- file_writefn f2 [] ;; mret (set_w false [] (set_bufsize 0 f3))) st (vfprintf_ubf_post m st)
      (MS (mkR x1 (Z_to_bv 64 (q + -368)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 B0) (sx32 flags) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1c45c) fc None m1 (seg_rom usegs)).
  Section Sz22.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 ibuf rest : ltac2:(SecDiet.SzSec.tyM 'vf_pass2u__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma vf_pass2u__body : ltac2:(SecDiet.SzSec.bodyP 'vf_pass2u__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FLOC GLO HA HB0 HF HVA LO PIECES SMALL. pin_using (fun (FLOC GLO HA HB0 HF HVA LO PIECES SMALL : unit) => tt).
 intros FC1 FL1 INV1 WB1 BUF1 APC2 FR BY VAA AOK ST SSP MI MU WM OLDERR.
    pose proof sinkfacts_u as (K1 & K2 & K3 & K4 & K5 & KFB & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB. pose proof (rw_CB_length _ _ _ _ BUF1) as LBB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof INV1 as (WA1 & RB1 & BS1 & NW1 & CH1 & SW1 & CN1).
    (* [comment removed for export] *)
    pose proof (printf_core_proof (file_st * St) Fp 232 Fp Bi 80 (SINKu 0 0 st) TOPOK_file (OUT_file (St:=St))
                  (file_sink_frame Fp Bi 80 0 0 closefn readfn seekfn prev next tail false true st K3 KFB K6 K7 K8 K9)
                  (file_sink_flags Fp Bi 80 0 0 closefn readfn seekfn prev next tail false true st K1 K5)
                  file_topok
                  (file_out Fp Bi 80 0 0 closefn readfn seekfn prev next tail false true st K1 K2 K3 K4 KFB K6 K7 K8 K9)) as PC2.
    unfold printf_core_stmt in PC2.
    set (PCQ := printf_core_post (St:=file_st * St) Fp 232 Bi 80 (SINKu 0 0 st) (Z_to_bv 64 0x1c474) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp
                  (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 345288) (Z_to_bv 64 1) (Z_to_bv 64 B0) (sx32 flags) s6 s7 s8 s9 s10 s11 F fc
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -368) : word)) lo canary m1).
    unfold q, Bi in *.
    eapply implM_bind with (Q1 := fun f' st' ms' => PCQ r (f', st') ms').
    { { apply out_pieces_bridge; [exact SMALL|].
        eapply (printf_model_outs usegs (OUT_file (St:=St)) fmtz args ps r mret); [exact PIECES|].
        apply implM_bind_mret.
        apply implM_prefix. do 5 zs. zs. apply evt_done.
        apply (proj1 (rw_cells_app usegs _ _ [_] _)) in APC2. destruct APC2 as [APC AP2]. cbn [cells_size csize Nat.add app] in AP2.
        replace (Z_to_bv 64 VA : word) with (Z_to_bv 64 (VA + 8 * 0) : word) in APC by (f_equal; lia).
        assert (SNK : SINK_file Fp (bv_unsigned sp - 352) 80 0 0 closefn readfn seekfn prev next tail false true st m1 (f1, st)).
        { split; [reflexivity|]. split; [exact INV1|]. exists flags1, mode1, ibuf. cbn [fst].
          split; [exact FC1|]. split; [exact FL1|]. split; [exact BUF1|]. rewrite WB1. split; [reflexivity| unfold zlength; cbn; lia]. }
        eapply implM_ms_eq; [eapply PC2 with (i := 0%Z) (slots := slots) | subst PCQ; ms_eq]; clear PC2; rewrite ?unsigned_lit by lia;
          unfold PC_DEPTH, GLOBALS_TOP, TOPOK_file, zlength.
        all: match goal with |- ?g => fastfirst (first [ noevar_assumption |
               exact SNK
             | exact BY | exact HF | reflexivity | exact APC | exact VAA | unfold va_area; exact VAA | exact I
             | cbn [skipn Z.to_nat]; eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz ibuf; lia) | apply (munch_refl []) | constructor]
             | exact ST | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption
             | (keep_hyps sp fmtz ibuf K4 Fp VA lo slots FLOC HVA; lia)
             | idtac "VFU2-LEFT:" g; fail ]) end. } }
    cbv beta. intros f2 st2 ms2 PO. clear PC2. subst PCQ.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & -> & -> & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    clear BY VAA AOK BUF1 FC1.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in APC2. destruct APC2 as [_ AP2]. cbn [cells_size csize Nat.add app] in AP2.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in AP2 by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
    destruct SNK3 as (EST3 & INV3 & flags3 & mode3 & bufbytes3 & FC3 & FL3 & BUF3 & BP3 & WBL3). cbn [fst snd] in EST3, INV3, FC3, FL3, BUF3, BP3, WBL3. subst st2.
    pose proof INV3 as (WA3 & RB3 & BS3 & NW3 & CH3 & SW3 & CN3).
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (SWF : f_stdoutw f2 = false) by (destruct (f_stdoutw f2) eqn:E; [discriminate (SW3 eq_refl) | reflexivity]).
    assert (WFN : wfn_of f2 = F_STDIO_WRITE) by (unfold wfn_of; rewrite SWF; reflexivity).
    rewrite CN3 in CH3.
    pose proof (rw_CB_length _ _ _ _ BUF3) as LB3.
    assert (NNw : 0 <= zlength (f_wbuf f2)) by (unfold zlength; lia).
    pose proof (CB_prefix_bytes_at m3 (bv_unsigned sp - 352) (Z.to_nat 80) bufbytes3 (to_bytes (f_wbuf f2)) BUF3 ltac:(rewrite length_to_bytes; exact BP3)) as WBB.
    unfold fcells, file_cells in FC3. rewrite WFN in FC3. unfold F_STDIO_WRITE in FC3.
    apply implM_prefix. fix_ret.
    (* [comment removed for export] *)
    zs. zs. zs. brf Kb; [exfalso; revert Kb; rewrite ?unsigned_lit by lia; lia|].
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs.
    apply evt_done. unfold file_writefn. rewrite SWF.
    eapply implM_bind.
    { eapply implM_ms_eq;
        [eapply (stdio_write_spec (St:=St)) with (f := f2) (s := []) (S := 0) (lo := lo) (canary := canary) (Fp := Fp) (flags := flags3)
           (rpos := 0) (rend := 0) (closefn := closefn) (wend := bv_unsigned sp - 352 + 80) (readfn := readfn) (writefn := 113588) (seekfn := seekfn)
           (B := bv_unsigned sp - 352) (bufsize := 80) (prev := prev) (next := next) (mode := mode3) (lbf := lbf_of f2) (tail := tail)
        | unfold F_STDIO_WRITE; ms_eq].
      all: rewrite ?unsigned_lit by lia.
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | unfold fcells, file_cells; exact FC3 | exact WBB | apply bytes_at_nil; (keep_hyps sp fmtz ibuf bufbytes3; lia) | reflexivity | rewrite CN3; exact CH3 | exact ST3 | exact MI3
             | split; [exact SSP1 | exact SSP2] | left; reflexivity
             | unfold STDIO_WRITE_DEPTH, got_ssp, ssp_guard, zlength in *; cbn [length Z.of_nat] in *; (keep_hyps sp lo fmtz ibuf bufbytes3 LO K4 Fp B0 GLO FLOC K6 K7 SPHI VA slots f2 HVA WBL3 KFB; lia)
             | idtac "SWCALL-LEFT:" g; fail ]) end. }
    cbv beta. intros f3 st3 ms3 PO.
    destruct PO as (-> & -> & w5 & w6 & w7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w28 & w29 & w30 & w31 & m4 & -> & MUc & WMc & MI4 & ST4 & FC4 & SSP4).
    unfold sw_W, STDIO_WRITE_DEPTH in MUc. rewrite !unsigned_lit in MUc, ST4 by lia.
    clear FC3 WBB.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
    apply implM_ret. fix_ret.
    clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC4.
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs.
    zs. replace (0 <? bv_unsigned sp - 352)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
    zs. zs. rewrite ?Z.lor_0_l. zs.
    (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 (sx32 flags3)) as FR3. unfold bv_modulus in FR3. cbn in FR3.
    zs. zs. rewrite (flags_err_clear_lw f2 flags3 FL3). zs. rewrite OLDERR, Z.lor_0_r.
    zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with AP : rw_cells _ mm (bv_unsigned sp + -368)%Z [C8 ?apv'], B3 : rw_cells _ mm (q - 352)%Z [CB _ ?bb], R : rw_cells _ mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -368) ([C8 apv'] ++ [C8 (Z_to_bv 64 VA)] ++ [CB (Z.to_nat 80) bb] ++ rest));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact AP2 | lia]|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact B3 | unfold q; lia]|]; cbn [cells_size csize Nat.add Z.to_nat Pos.to_nat Pos.iter_op Nat.mul];
        eapply rwc_eqA; [exact R | lia]
      | clear AP AP2 B3 R ] end end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -368)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evt_done. unfold vfprintf_ubf_post, q. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [cbn; exact RB3|]. split; [reflexivity|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [unfold fcells, file_cells; cbn [f_fd set_w set_bufsize]; unfold wfn_of, lbf_of in *; cbn [f_stdoutw f_lbf_nl set_w set_bufsize]; rewrite SWF; unfold F_STDIO_WRITE; exact FC4|].
    apply flags_ok_ws. apply flags_ok_relw. exact FL3.
  Qed.
  End Sz22.
  Lemma vf_pass2u : ltac:(let t := eval cbv delta [vf_pass2u__stmt] in vf_pass2u__stmt in exact t).
  Proof using FLOC GLO HA HB0 HF HVA LO PIECES SMALL. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 ibuf rest. ltac2:(SecDiet.SzSec.closeP 'vf_pass2u__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition vfprintf_ubf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (rpos rend we wp wb : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells usegs m Fp (fcells flags rpos rend closefn we wp wb readfn (wfn_of f) seekfn B0 0 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags -> f_bufsize f = 0 -> f_nowr f = false -> f_rbuf f = [] -> f_wbuf f = [] ->
    f_chan f = true -> (f_fd f = 1 \/ f_fd f = 2) -> f_stdoutw f = false ->
    0 <= we < 2^64 -> 0 <= wp < 2^64 -> 0 <= wb < 2^64 -> 0 <= rpos < 2^64 -> 0 <= rend < 2^64 ->
    bytes_at usegs m A (zb fmtz) -> va_area m VA slots -> args_ok Fp 232 Bi 80 m lo q (q - VF_FRAME) slots args ->
    stk usegs m lo q -> ssp_cells m canary -> mem_inv usegs m ->
    implM usegs (vfprintf f ps) st (vfprintf_ubf_post m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF) fc None m (seg_rom usegs)).
  Section Sz23.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode rpos rend we wp wb : ltac2:(SecDiet.SzSec.tyM 'vfprintf_ubf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma vfprintf_ubf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_ubf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FLOC GLO HA HB0 HF HVA LO P1 PIECES SMALL. pin_using (fun (FLOC GLO HA HB0 HF HVA LO P1 PIECES SMALL : unit) => tt).
 intros -> -> -> FC0 FL0 BS NW RB WB CHN FD SWF Rwe Rwp Rwb Rrp Rre BY VAA AOK ST SSP MI.
    pose proof sinkfacts_u as (K1 & K2 & K3 & K4 & K5 & KFB & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold q, Bi in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    unfold fcells, file_cells in FC0.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    (* [comment removed for export] *)
    unfold vfprintf. rewrite BS. change (0 =? 0) with true. cbv iota.
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash FC0. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VFPRINTF.
    apply implM_prefix.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells usegs ?mm ?A [CB 368 ?j] |- _ =>
        apply (rw_cells_split_CB usegs mm A [] 368 j [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells ?sg _ _ _ => apply (proj1 (rw_cells_app sg _ _ [_;_;_] _)) in FR end.
    destruct FR as [FRlo FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    lazymatch type of FRhi with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -104)%Z in FRhi by lia end.
    do 12 zs. do 14 zs.
    lazymatch type of FRlo with rw_cells ?sg ?mm ?A ?cs1 => lazymatch type of FRhi with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in FRhi by (cbn [cells_size csize Nat.add]; lia);
      pose proof (proj2 (rw_cells_app sg mm A cs1 cs2) (conj FRlo FRhi)) as FR; clear FRlo FRhi end end.
    cbn [app] in FR.
    unfold hide in FC0.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call usegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]);
      unfold hide in BY, VAA;
      eapply (bytes_at_transport _ Wp ma mb) in BY; [| exact MUp | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; lia];
      unfold va_area in VAA;
      eapply (bytes_at_transport _ Wp ma mb) in VAA; [| exact MUp | cbn [disjoint_from]; rewrite u64s_length; clear -HVA; lia]
    end.
    clear MUp. stash VAA.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. first [if_lit | brf Kl; [|exfalso; revert Kl; cbn; rewrite ?unsigned_lit by lia; cbn; lia]]. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    do 8 zs. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    unfold hide in AOK, VAAm. clear BYm VAA. unfold va_area in VAAm.
    lazymatch type of MU with munch _ _ ?mc =>
      assert (VAA : bytes_at usegs mc VA (u64s slots))
        by (eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA FLOC GLO LO SPHI NNs; lia]) end.
    clear VAAm.
    pose proof (flags_ok_clr_err f flags FL0) as FL1.
    pose proof (flags_err_clear_lw f flags FL0) as OLDERR.
    pose proof (flags_nowr_clear _ _ FL1 ltac:(cbn; exact NW)) as X8.
    eapply evt_cut.
    { eapply evt_ms_eq; [eapply towrite_specZ | ms_eq].
      all: first [ exact FC0 | exact X8 | assumption | lia | match goal with |- ?g => idtac "TWU-LEFT:" g end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & mode' & m'' & -> & MUc & WMc & MIt & FCt).
    clear FC0.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. (* [comment removed for export] *)
    apply evt_done. unfold towrite. cbn [f_nowr set_w set_bufsize]. rewrite NW. apply implM_retb.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ _ (bv_unsigned sp + -368)%Z (_ :: _ :: CB 248 _ :: _) |- _ => rename H into FRv end.
    apply (rw_cells_split_CB usegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_; _] _)) in FRv. destruct FRv as [APC2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [IBc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr IBc (bv_unsigned sp - 352)%Z. readdr FRv (bv_unsigned sp + -272)%Z.
    eapply implM_ms_eq; [eapply (vf_pass2u _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) with (f1 := set_w true [] (set_rbuf [] (set_w false [] (set_bufsize 80 f)))) | ms_eq].
    all: try first [ exact FL1 | apply flags_ok_ws; exact FL1 | exact IBc | exact APC2 | exact FRv | exact BY | unfold va_area; exact VAA | exact STc
                   | exact MU | exact WM | exact OLDERR | split; [exact SSP1 | exact SSP2] | assumption ].
    all: try (lazymatch goal with |- rw_cells _ _ Fp ?cs1 => lazymatch type of FCt with rw_cells _ _ _ ?cs0 =>
                replace cs1 with cs0; [exact FCt|];
                unfold fcells, file_cells, wfn_of, lbf_of; cbn [f_wbuf f_fd f_stdoutw f_lbf_nl set_w set_rbuf set_bufsize]; unfold zlength; cbn [length Z.of_nat];
                rewrite ?unsigned_lit by lia; repeat fastfirst (first [reflexivity | (keep_hyps sp fmtz; lia) | progress f_equal]) end end).
    all: try (unfold fsink_inv; cbn [f_wactive f_rbuf f_bufsize f_nowr f_chan f_fd f_stdoutw set_w set_rbuf set_bufsize];
              split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact NW | split; [rewrite CHN; exact FD | split; [rewrite SWF; discriminate | exact CHN]]]]]]).
    all: try (cbn [f_wbuf set_w set_rbuf set_bufsize]; reflexivity).
    all: try (eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz; lia) | exact MU | ]; repeat constructor; cbn [fst snd]; (keep_hyps sp lo fmtz Fp; lia)).
    all: match goal with |- ?g => idtac "VFUB-LEFT:" g end.
    all: fail.
  Qed.
  End Sz23.
  Theorem vfprintf_ubf_spec : ltac:(let t := eval cbv delta [vfprintf_ubf_spec__stmt] in vfprintf_ubf_spec__stmt in exact t).
  Proof using FLOC GLO HA HB0 HF HVA LO P1 PIECES SMALL. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode rpos rend we wp wb. ltac2:(SecDiet.SzSec.closeP 'vfprintf_ubf_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End VfUbf.
End TwB.
End F_vfprintf_file.

(* [comment removed for export] *)
Module F_fprintf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep FP ITree Nodes Decode StoreFast ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_iface F_printf_core_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Printf_fsink. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_printf_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Printf_fsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_vfprintf_file.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sbl_is_big n := lazymatch n with S _ => let b := eval vm_compute in (Nat.leb 200 n) in lazymatch b with true => idtac end end.
Local Ltac sbl_pose_in H :=
  (let T := type of H in let T' := eval hnf in T in change T' in H);
  repeat match type of H with
  | context [repeat ?b ?n] => sbl_is_big n; let z := fresh "sblz" in pose (z := repeat b n); change (repeat b n) with z in H
  | context [CB ?n _] => sbl_is_big n; let x := fresh "sblv" in pose (x := n); change n with x in H
  end.
Local Ltac sbl_subst_all :=
  repeat match goal with
  | z := repeat _ ?n |- _ => sbl_is_big n; subst z
  | x := ?n |- _ => sbl_is_big n; subst x
  end.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Definition FPRINTF : Z := 0x1b584.
Definition PRINTF : Z := 0x1b9e4.
Definition VPRINTF : Z := 0x20550.
Definition FPRINTF_DEPTH : Z := 5648.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FprintfFile.
  Context {St : Type}.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A lo : Z) (fmtz : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Variables (sw0 ch0 : bool).
  Let p := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - FPRINTF_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis PHI : p <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis FLOC : (140840 <= Fp /\ Fp + 232 <= 343304) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis BLOC : (343312 <= B /\ B + 1024 <= GLOBALS_TOP) \/ (0 < B /\ B + 1024 <= lo /\ (B + 1024 <= 65536 \/ GLOBALS_TOP <= B)).
  Hypothesis FB : B + 1024 <= Fp \/ Fp + 232 <= B.

  Definition fprintf_file_post (rpos rend : Z) (m : mem) (st : St) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fsink_inv 1024 sw0 ch0 f' /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (bufbytes' : list byte) (m' : mem) (rpos' rend' : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch [(lo, p); (Fp, Fp + 232); (B, B + 1024)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo p
      /\ ssp_cells m' canary
      /\ rw_cells ssegs m' Fp (fcells flags' rpos' rend' closefn (B + 1024) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B 1024 prev next (f_fd f') mode' (lbf_of f') tail)
      /\ ((rpos' = rpos /\ rend' = rend) \/ (rpos' = 0 /\ rend' = 0))
      /\ flags_ok f' flags'
      /\ rw_cells ssegs m' B [CB 1024%nat bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= 1024.

  Definition fprintf_file_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A ->
    rw_cells ssegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells ssegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at ssegs m A (zb fmtz) -> args_ok Fp 232 B 1024 m lo p (p - 448) [a2; a3; a4; a5; a6; a7] args ->
    stk ssegs m lo p -> ssp_cells m canary -> mem_inv ssegs m ->
    implM ssegs (vfprintf f ps) st (fprintf_file_post rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FPRINTF) fc None m (seg_rom ssegs)).
  Section Sz1.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend : ltac2:(SecDiet.SzSec.tyM 'fprintf_file_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fprintf_file_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_file_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BLOC FB FLOC GLO HA HF LO P1 PHI PIECES SMALL. pin_using (fun (BLOC FB FLOC GLO HA HF LO P1 PHI PIECES SMALL : unit) => tt).
 intros -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY AOK ST SSP MI.
    unfold FPRINTF_DEPTH, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold p in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). unfold zlength in HA, NNf.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC0.
    pose proof (wmono_refl ssegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    stash FC0. stash BUF0. stash BY. stash AOK.
    unfold FPRINTF. apply implM_prefix.
    carve_frame 80%nat ST.
    do 16 zs. zs.
    unfold hide in FC0, BUF0, BY, AOK.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call ssegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (B, B + 1024)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]) end.
    clear MUp.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app ssegs _ _ [_; _; _; _] _)) in FR. destruct FR as [FR VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -80 + Z.of_nat 32) with (bv_unsigned sp + -48) in VAc by lia.
    pose proof (rw_cells_bytes_at _ _ _ _ VAc) as VAA. cbn [cells_bytes cbytes app] in VAA. rewrite ?app_nil_r in VAA.
    apply evt_done.
    eapply implM_post_evt.
    { eapply implM_ms_eq;
        [ eapply (vfprintf_file_spec (Z_to_bv 64 0x1b5c8) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp (Z_to_bv 64 ssp_guard) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                    Fp B closefn readfn seekfn prev next tail A (bv_unsigned sp + -48) lo fmtz [a2; a3; a4; a5; a6; a7] args ps r canary sw0 ch0)
        | unfold ssp_guard; ms_eq ].
      all: rewrite ?unsigned_lit by lia.
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact FLOC | exact BLOC | exact FB
             | reflexivity | exact FC0 | exact FL0 | exact BUF0 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
             | exact BY | unfold va_area; cbn [u64s app]; rewrite ?app_nil_r; exact VAA
             | unfold VF_FRAME; replace (bv_unsigned sp + -80 - 368) with (bv_unsigned sp - 448) by lia;
               eapply args_ok_vff; [exact AOK | lia | exact MU | ]; repeat constructor; cbn [fst snd]; lia
             | exact ST | split; [exact SSP1 | exact SSP2] | assumption
             | unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, zlength in *; cbn [length Z.of_nat] in *; lia
             | idtac "FPF-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' PO. unfold vfprintf_file_post in PO. rewrite !unsigned_lit in PO by lia.
    sbl_pose_in PO. destruct PO as (-> & INV' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & bufbytes' & m3 & rpos' & rend'
                     & -> & MUc & WMc & MI3 & ST3 & SSP3 & FC3 & RP3 & FL3 & BUF3 & BP3 & WBL3). sbl_subst_all.
    clear FC0 BUF0 BY AOK VAA.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m3 MUc WMc; clear MUc WMc end.
    replace (ret_pc (Z_to_bv 64 0x1b5c8)) with (Z_to_bv 64 0x1b5c8 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    unfold ssp_guard.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of FR with rw_cells _ _ _ ?c1 => lazymatch type of VAc with rw_cells _ _ _ ?c2 =>
      assert (FALL : rw_cells ssegs mm (bv_unsigned sp + -80) (c1 ++ c2));
      [ apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add]; eapply rwc_eqA; [exact VAc | lia] | clear FR VAc ] end end end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -80)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evt_done. unfold fprintf_file_post, p. split; [reflexivity|]. split; [exact INV'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [exact FC3|]. split; [exact RP3|]. split; [exact FL3|]. split; [exact BUF3|]. split; [exact BP3| exact WBL3].
  Qed.
  End Sz1.
  Theorem fprintf_file_spec : ltac:(let t := eval cbv delta [fprintf_file_spec__stmt] in fprintf_file_spec__stmt in exact t).
  Proof using BLOC FB FLOC GLO HA HF LO P1 PHI PIECES SMALL. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend. ltac2:(SecDiet.SzSec.closeP 'fprintf_file_spec__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FprintfFile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FprintfUbf.
  Context {St : Type}.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B0 : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A lo : Z) (fmtz : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Let p := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - FPRINTF_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis PHI : p <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis FLOC : (140840 <= Fp /\ Fp + 232 <= 343304) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis HB0 : 0 < B0 < 2^64.

  Definition fprintf_ubf_post (m : mem) (st : St) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = [] /\ f_bufsize f' = 0 /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch [(lo, p); (Fp, Fp + 232)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo p
      /\ ssp_cells m' canary
      /\ rw_cells ssegs m' Fp (fcells flags' 0 0 closefn 0 0 0 readfn (wfn_of f') seekfn B0 0 prev next (f_fd f') mode' (lbf_of f') tail)
      /\ flags_ok f' flags'.

  Definition fprintf_ubf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (rpos rend we wp wb : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A ->
    rw_cells ssegs m Fp (fcells flags rpos rend closefn we wp wb readfn (wfn_of f) seekfn B0 0 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags -> f_bufsize f = 0 -> f_nowr f = false -> f_rbuf f = [] -> f_wbuf f = [] ->
    f_chan f = true -> (f_fd f = 1 \/ f_fd f = 2) -> f_stdoutw f = false ->
    0 <= we < 2^64 -> 0 <= wp < 2^64 -> 0 <= wb < 2^64 -> 0 <= rpos < 2^64 -> 0 <= rend < 2^64 ->
    bytes_at ssegs m A (zb fmtz) -> args_ok Fp 232 (p - 432) 80 m lo p (p - 448) [a2; a3; a4; a5; a6; a7] args ->
    stk ssegs m lo p -> ssp_cells m canary -> mem_inv ssegs m ->
    implM ssegs (vfprintf f ps) st (fprintf_ubf_post m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FPRINTF) fc None m (seg_rom ssegs)).
  Section Sz2.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode rpos rend we wp wb : ltac2:(SecDiet.SzSec.tyM 'fprintf_ubf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fprintf_ubf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_ubf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FLOC GLO HA HB0 HF LO P1 PHI PIECES SMALL. pin_using (fun (FLOC GLO HA HB0 HF LO P1 PHI PIECES SMALL : unit) => tt).
 intros -> -> FC0 FL0 BS NW RB WB CHN FD SWF Rwe Rwp Rwb Rrp Rre BY AOK ST SSP MI.
    unfold FPRINTF_DEPTH, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold p in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). unfold zlength in HA, NNf.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC0.
    pose proof (wmono_refl ssegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    stash FC0. stash BY. stash AOK.
    unfold FPRINTF. apply implM_prefix.
    carve_frame 80%nat ST.
    do 16 zs. zs.
    unfold hide in FC0, BY, AOK.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call ssegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]) end.
    clear MUp.
    apply (proj1 (rw_cells_app ssegs _ _ [_; _; _; _] _)) in FR. destruct FR as [FR VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -80 + Z.of_nat 32) with (bv_unsigned sp + -48) in VAc by lia.
    pose proof (rw_cells_bytes_at _ _ _ _ VAc) as VAA. cbn [cells_bytes cbytes app] in VAA. rewrite ?app_nil_r in VAA.
    apply evt_done.
    eapply implM_post_evt.
    { eapply implM_ms_eq;
        [ eapply (vfprintf_ubf_spec (Z_to_bv 64 0x1b5c8) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp (Z_to_bv 64 ssp_guard) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                    Fp B0 closefn readfn seekfn prev next tail A (bv_unsigned sp + -48) lo fmtz [a2; a3; a4; a5; a6; a7] args ps r canary)
        | unfold ssp_guard; ms_eq ].
      all: rewrite ?unsigned_lit by lia.
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact FLOC | exact HB0
             | reflexivity | exact FC0 | exact FL0 | exact BS | exact NW | exact RB | exact WB | exact CHN | exact FD | exact SWF
             | exact BY | unfold va_area; cbn [u64s app]; rewrite ?app_nil_r; exact VAA
             | unfold VF_FRAME; replace (bv_unsigned sp + -80 - 368) with (bv_unsigned sp - 448) by lia;
               replace (bv_unsigned sp + -80 - 352) with (bv_unsigned sp - 432) by lia;
               eapply args_ok_vff; [exact AOK | lia | exact MU | ]; repeat constructor; cbn [fst snd]; lia
             | exact ST | split; [exact SSP1 | exact SSP2] | assumption
             | unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, zlength in *; cbn [length Z.of_nat] in *; lia
             | idtac "FPU-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' PO. unfold vfprintf_ubf_post in PO. rewrite !unsigned_lit in PO by lia.
    sbl_pose_in PO. destruct PO as (-> & WA' & WB' & RB' & BS' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & m3
                     & -> & MUc & WMc & MI3 & ST3 & SSP3 & FC3 & FL3). sbl_subst_all.
    clear FC0 BY AOK VAA.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m3 MUc WMc; clear MUc WMc end.
    replace (ret_pc (Z_to_bv 64 0x1b5c8)) with (Z_to_bv 64 0x1b5c8 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold ssp_guard.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of FR with rw_cells _ _ _ ?c1 => lazymatch type of VAc with rw_cells _ _ _ ?c2 =>
      assert (FALL : rw_cells ssegs mm (bv_unsigned sp + -80) (c1 ++ c2));
      [ apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add]; eapply rwc_eqA; [exact VAc | lia] | clear FR VAc ] end end end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -80)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evt_done. unfold fprintf_ubf_post, p. split; [reflexivity|]. split; [exact WA'|]. split; [exact WB'|]. split; [exact RB'|]. split; [exact BS'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [exact FC3| exact FL3].
  Qed.
  End Sz2.
  Theorem fprintf_ubf_spec : ltac:(let t := eval cbv delta [fprintf_ubf_spec__stmt] in fprintf_ubf_spec__stmt in exact t).
  Proof using FLOC GLO HA HB0 HF LO P1 PHI PIECES SMALL. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode rpos rend we wp wb. ltac2:(SecDiet.SzSec.closeP 'fprintf_ubf_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FprintfUbf.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Printf.
  Context {St : Type}.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A lo : Z) (fmtz : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Variables (sw0 ch0 : bool).
  Let p := bv_unsigned sp.
  Let Fp := A_STDOUT.
  Let B := A_STDOUT_BUF.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - FPRINTF_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis PHI : p <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.

  Definition printf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 A ->
    rw_cells ssegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells ssegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at ssegs m A (zb fmtz) -> args_ok Fp 232 B 1024 m lo p (p - 464) [a1; a2; a3; a4; a5; a6; a7] args ->
    stk ssegs m lo p -> ssp_cells m canary -> mem_inv ssegs m ->
    implM ssegs (vfprintf f ps) st (fprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail lo canary sw0 ch0 rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PRINTF) fc None m (seg_rom ssegs)).
  Section Sz3.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend : ltac2:(SecDiet.SzSec.tyM 'printf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma printf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'printf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GLO HA HF LO P1 PHI PIECES SMALL. pin_using (fun (GLO HA HF LO P1 PHI PIECES SMALL : unit) => tt).
 intros -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY AOK ST SSP MI.
    unfold FPRINTF_DEPTH, GLOBALS_TOP in *. unfold Fp, B, A_STDOUT, A_STDOUT_BUF in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold p in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). unfold zlength in HA, NNf.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC0.
    pose proof (wmono_refl ssegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    stash FC0. stash BUF0. stash BY. stash AOK.
    unfold PRINTF. apply implM_prefix.
    carve_frame 96%nat ST.
    do 21 zs. zs.
    unfold hide in FC0, BUF0, BY, AOK.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call ssegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (145472, 145472 + 232); (345456, 345456 + 1024)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]) end.
    clear MUp.
    apply (proj1 (rw_cells_app ssegs _ _ [_; _; _; _; _] _)) in FR. destruct FR as [FR VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -96 + Z.of_nat 40) with (bv_unsigned sp + -56) in VAc by lia.
    pose proof (rw_cells_bytes_at _ _ _ _ VAc) as VAA. cbn [cells_bytes cbytes app] in VAA. rewrite ?app_nil_r in VAA.
    apply evt_done.
    eapply implM_post_evt.
    { eapply implM_ms_eq;
        [ eapply (vfprintf_file_spec (Z_to_bv 64 0x1ba3c) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 ssp_guard) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                    145472 345456 closefn readfn seekfn prev next tail A (bv_unsigned sp + -56) lo fmtz [a1; a2; a3; a4; a5; a6; a7] args ps r canary sw0 ch0)
        | unfold ssp_guard; ms_eq ].
      all: rewrite ?unsigned_lit by lia.
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC0 | exact FL0 | exact BUF0 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
             | exact BY | unfold va_area; cbn [u64s app]; rewrite ?app_nil_r; exact VAA
             | unfold VF_FRAME; replace (bv_unsigned sp + -96 - 368) with (bv_unsigned sp - 464) by lia;
               eapply args_ok_vff; [exact AOK | lia | exact MU | ]; repeat constructor; cbn [fst snd]; lia
             | exact ST | split; [exact SSP1 | exact SSP2] | assumption
             | unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, zlength in *; cbn [length Z.of_nat] in *; lia
             | idtac "PF-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' PO. unfold vfprintf_file_post in PO. rewrite !unsigned_lit in PO by lia.
    sbl_pose_in PO. destruct PO as (-> & INV' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & bufbytes' & m3 & rpos' & rend'
                     & -> & MUc & WMc & MI3 & ST3 & SSP3 & FC3 & RP3 & FL3 & BUF3 & BP3 & WBL3). sbl_subst_all.
    clear FC0 BUF0 BY AOK VAA.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m3 MUc WMc; clear MUc WMc end.
    replace (ret_pc (Z_to_bv 64 0x1ba3c)) with (Z_to_bv 64 0x1ba3c : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold ssp_guard.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of FR with rw_cells _ _ _ ?c1 => lazymatch type of VAc with rw_cells _ _ _ ?c2 =>
      assert (FALL : rw_cells ssegs mm (bv_unsigned sp + -96) (c1 ++ c2));
      [ apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add]; eapply rwc_eqA; [exact VAc | lia] | clear FR VAc ] end end end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -96)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evt_done. unfold fprintf_file_post. split; [reflexivity|]. split; [exact INV'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [exact FC3|]. split; [exact RP3|]. split; [exact FL3|]. split; [exact BUF3|]. split; [exact BP3| exact WBL3].
  Qed.
  End Sz3.
  Theorem printf_spec : ltac:(let t := eval cbv delta [printf_spec__stmt] in printf_spec__stmt in exact t).
  Proof using GLO HA HF LO P1 PHI PIECES SMALL. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend. ltac2:(SecDiet.SzSec.closeP 'printf_spec__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Printf.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Vprintf.
  Context {St : Type}.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Variables (sw0 ch0 : bool).
  Let q := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^47.   (* [comment removed for export] *)

  Definition vprintf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 VA ->
    rw_cells ssegs m A_STDOUT (fcells flags rpos rend closefn (if f_wactive f then A_STDOUT_BUF + 1024 else 0) (if f_wactive f then A_STDOUT_BUF + zlength (f_wbuf f) else 0) (if f_wactive f then A_STDOUT_BUF else 0)
                           readfn (wfn_of f) seekfn A_STDOUT_BUF 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells ssegs m A_STDOUT_BUF [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at ssegs m A (zb fmtz) -> va_area m VA slots -> args_ok A_STDOUT 232 A_STDOUT_BUF 1024 m lo q (q - VF_FRAME) slots args ->
    stk ssegs m lo q -> ssp_cells m canary -> mem_inv ssegs m ->
    implM ssegs (vfprintf f ps) st (vfprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_STDOUT A_STDOUT_BUF closefn readfn seekfn prev next tail lo canary sw0 ch0 rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VPRINTF) fc None m (seg_rom ssegs)).
  Section Sz4.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend : ltac2:(SecDiet.SzSec.tyM 'vprintf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma vprintf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vprintf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GLO HA HF HVA LO P1 PIECES SMALL. pin_using (fun (GLO HA HF HVA LO P1 PIECES SMALL : unit) => tt).
 intros -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY VAA AOK ST SSP MI.
    unfold A_STDOUT, A_STDOUT_BUF in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold VPRINTF. apply implM_prefix.
    do 7 zs. apply evt_done.
    eapply implM_ms_eq; [eapply vfprintf_file_spec | ms_eq].
    all: match goal with |- ?g => fastfirst (first
           [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact LO | exact GLO | exact HA | exact HVA
           | reflexivity | exact FC0 | exact FL0 | exact BUF0 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
           | exact BY | exact VAA | exact AOK | exact ST | exact SSP | exact MI
           | unfold GLOBALS_TOP in *; lia
           | idtac "VP-LEFT:" g; fail ]) end.
  Qed.
  End Sz4.
  Theorem vprintf_spec : ltac:(let t := eval cbv delta [vprintf_spec__stmt] in vprintf_spec__stmt in exact t).
  Proof using GLO HA HF HVA LO P1 PIECES SMALL. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend. ltac2:(SecDiet.SzSec.closeP 'vprintf_spec__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Vprintf.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.FP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_printf_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Printf_fsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_vfprintf_file.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sbl_is_big n := lazymatch n with S _ => let b := eval vm_compute in (Nat.leb 200 n) in lazymatch b with true => idtac end end.
Local Ltac sbl_pose_in H :=
  (let T := type of H in let T' := eval hnf in T in change T' in H);
  repeat match type of H with
  | context [repeat ?b ?n] => sbl_is_big n; let z := fresh "sblz" in pose (z := repeat b n); change (repeat b n) with z in H
  | context [CB ?n _] => sbl_is_big n; let x := fresh "sblv" in pose (x := n); change n with x in H
  end.
Local Ltac sbl_subst_all :=
  repeat match goal with
  | z := repeat _ ?n |- _ => sbl_is_big n; subst z
  | x := ?n |- _ => sbl_is_big n; subst x
  end.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Definition FPRINTF : Z := 0x1bd44.
Definition PRINTF : Z := 0x1c1a4.
Definition VPRINTF : Z := 0x20d10.
Definition FPRINTF_DEPTH : Z := 5648.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FprintfFile.
  Context {St : Type}.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A lo : Z) (fmtz : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Variables (sw0 ch0 : bool).
  Let p := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - FPRINTF_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis PHI : p <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis FLOC : (142824 <= Fp /\ Fp + 232 <= 345288) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis BLOC : (345296 <= B /\ B + 1024 <= GLOBALS_TOP) \/ (0 < B /\ B + 1024 <= lo /\ (B + 1024 <= 65536 \/ GLOBALS_TOP <= B)).
  Hypothesis FB : B + 1024 <= Fp \/ Fp + 232 <= B.

  Definition fprintf_file_post (rpos rend : Z) (m : mem) (st : St) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fsink_inv 1024 sw0 ch0 f' /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (bufbytes' : list byte) (m' : mem) (rpos' rend' : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(lo, p); (Fp, Fp + 232); (B, B + 1024)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo p
      /\ ssp_cells m' canary
      /\ rw_cells usegs m' Fp (fcells flags' rpos' rend' closefn (B + 1024) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B 1024 prev next (f_fd f') mode' (lbf_of f') tail)
      /\ ((rpos' = rpos /\ rend' = rend) \/ (rpos' = 0 /\ rend' = 0))
      /\ flags_ok f' flags'
      /\ rw_cells usegs m' B [CB 1024%nat bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= 1024.

  Definition fprintf_file_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A ->
    rw_cells usegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells usegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at usegs m A (zb fmtz) -> args_ok Fp 232 B 1024 m lo p (p - 448) [a2; a3; a4; a5; a6; a7] args ->
    stk usegs m lo p -> ssp_cells m canary -> mem_inv usegs m ->
    implM usegs (vfprintf f ps) st (fprintf_file_post rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FPRINTF) fc None m (seg_rom usegs)).
  Section Sz1.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend : ltac2:(SecDiet.SzSec.tyM 'fprintf_file_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fprintf_file_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_file_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BLOC FB FLOC GLO HA HF LO P1 PHI PIECES SMALL. pin_using (fun (BLOC FB FLOC GLO HA HF LO P1 PHI PIECES SMALL : unit) => tt).
 intros -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY AOK ST SSP MI.
    unfold FPRINTF_DEPTH, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold p in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). unfold zlength in HA, NNf.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC0.
    pose proof (wmono_refl usegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    stash FC0. stash BUF0. stash BY. stash AOK.
    unfold FPRINTF. apply implM_prefix.
    carve_frame 80%nat ST.
    do 16 zs. zs.
    unfold hide in FC0, BUF0, BY, AOK.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call usegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (B, B + 1024)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]) end.
    clear MUp.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app usegs _ _ [_; _; _; _] _)) in FR. destruct FR as [FR VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -80 + Z.of_nat 32) with (bv_unsigned sp + -48) in VAc by lia.
    pose proof (rw_cells_bytes_at _ _ _ _ VAc) as VAA. cbn [cells_bytes cbytes app] in VAA. rewrite ?app_nil_r in VAA.
    apply evt_done.
    eapply implM_post_evt.
    { eapply implM_ms_eq;
        [ eapply (vfprintf_file_spec (Z_to_bv 64 0x1bd88) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp (Z_to_bv 64 ssp_guard) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                    Fp B closefn readfn seekfn prev next tail A (bv_unsigned sp + -48) lo fmtz [a2; a3; a4; a5; a6; a7] args ps r canary sw0 ch0)
        | unfold ssp_guard; ms_eq ].
      all: rewrite ?unsigned_lit by lia.
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact FLOC | exact BLOC | exact FB
             | reflexivity | exact FC0 | exact FL0 | exact BUF0 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
             | exact BY | unfold va_area; cbn [u64s app]; rewrite ?app_nil_r; exact VAA
             | unfold VF_FRAME; replace (bv_unsigned sp + -80 - 368) with (bv_unsigned sp - 448) by lia;
               eapply args_ok_vff; [exact AOK | lia | exact MU | ]; repeat constructor; cbn [fst snd]; lia
             | exact ST | split; [exact SSP1 | exact SSP2] | assumption
             | unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, zlength in *; cbn [length Z.of_nat] in *; lia
             | idtac "FPF-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' PO. unfold vfprintf_file_post in PO. rewrite !unsigned_lit in PO by lia.
    sbl_pose_in PO. destruct PO as (-> & INV' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & bufbytes' & m3 & rpos' & rend'
                     & -> & MUc & WMc & MI3 & ST3 & SSP3 & FC3 & RP3 & FL3 & BUF3 & BP3 & WBL3). sbl_subst_all.
    clear FC0 BUF0 BY AOK VAA.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
    replace (ret_pc (Z_to_bv 64 0x1bd88)) with (Z_to_bv 64 0x1bd88 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    unfold ssp_guard.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of FR with rw_cells _ _ _ ?c1 => lazymatch type of VAc with rw_cells _ _ _ ?c2 =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -80) (c1 ++ c2));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add]; eapply rwc_eqA; [exact VAc | lia] | clear FR VAc ] end end end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -80)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evt_done. unfold fprintf_file_post, p. split; [reflexivity|]. split; [exact INV'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [exact FC3|]. split; [exact RP3|]. split; [exact FL3|]. split; [exact BUF3|]. split; [exact BP3| exact WBL3].
  Qed.
  End Sz1.
  Theorem fprintf_file_spec : ltac:(let t := eval cbv delta [fprintf_file_spec__stmt] in fprintf_file_spec__stmt in exact t).
  Proof using BLOC FB FLOC GLO HA HF LO P1 PHI PIECES SMALL. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend. ltac2:(SecDiet.SzSec.closeP 'fprintf_file_spec__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FprintfFile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FprintfUbf.
  Context {St : Type}.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B0 : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A lo : Z) (fmtz : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Let p := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - FPRINTF_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis PHI : p <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis FLOC : (142824 <= Fp /\ Fp + 232 <= 345288) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis HB0 : 0 < B0 < 2^64.

  Definition fprintf_ubf_post (m : mem) (st : St) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = [] /\ f_bufsize f' = 0 /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(lo, p); (Fp, Fp + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo p
      /\ ssp_cells m' canary
      /\ rw_cells usegs m' Fp (fcells flags' 0 0 closefn 0 0 0 readfn (wfn_of f') seekfn B0 0 prev next (f_fd f') mode' (lbf_of f') tail)
      /\ flags_ok f' flags'.

  Definition fprintf_ubf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (rpos rend we wp wb : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A ->
    rw_cells usegs m Fp (fcells flags rpos rend closefn we wp wb readfn (wfn_of f) seekfn B0 0 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags -> f_bufsize f = 0 -> f_nowr f = false -> f_rbuf f = [] -> f_wbuf f = [] ->
    f_chan f = true -> (f_fd f = 1 \/ f_fd f = 2) -> f_stdoutw f = false ->
    0 <= we < 2^64 -> 0 <= wp < 2^64 -> 0 <= wb < 2^64 -> 0 <= rpos < 2^64 -> 0 <= rend < 2^64 ->
    bytes_at usegs m A (zb fmtz) -> args_ok Fp 232 (p - 432) 80 m lo p (p - 448) [a2; a3; a4; a5; a6; a7] args ->
    stk usegs m lo p -> ssp_cells m canary -> mem_inv usegs m ->
    implM usegs (vfprintf f ps) st (fprintf_ubf_post m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FPRINTF) fc None m (seg_rom usegs)).
  Section Sz2.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode rpos rend we wp wb : ltac2:(SecDiet.SzSec.tyM 'fprintf_ubf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fprintf_ubf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_ubf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FLOC GLO HA HB0 HF LO P1 PHI PIECES SMALL. pin_using (fun (FLOC GLO HA HB0 HF LO P1 PHI PIECES SMALL : unit) => tt).
 intros -> -> FC0 FL0 BS NW RB WB CHN FD SWF Rwe Rwp Rwb Rrp Rre BY AOK ST SSP MI.
    unfold FPRINTF_DEPTH, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold p in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). unfold zlength in HA, NNf.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC0.
    pose proof (wmono_refl usegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    stash FC0. stash BY. stash AOK.
    unfold FPRINTF. apply implM_prefix.
    carve_frame 80%nat ST.
    do 16 zs. zs.
    unfold hide in FC0, BY, AOK.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call usegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]) end.
    clear MUp.
    apply (proj1 (rw_cells_app usegs _ _ [_; _; _; _] _)) in FR. destruct FR as [FR VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -80 + Z.of_nat 32) with (bv_unsigned sp + -48) in VAc by lia.
    pose proof (rw_cells_bytes_at _ _ _ _ VAc) as VAA. cbn [cells_bytes cbytes app] in VAA. rewrite ?app_nil_r in VAA.
    apply evt_done.
    eapply implM_post_evt.
    { eapply implM_ms_eq;
        [ eapply (vfprintf_ubf_spec (Z_to_bv 64 0x1bd88) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp (Z_to_bv 64 ssp_guard) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                    Fp B0 closefn readfn seekfn prev next tail A (bv_unsigned sp + -48) lo fmtz [a2; a3; a4; a5; a6; a7] args ps r canary)
        | unfold ssp_guard; ms_eq ].
      all: rewrite ?unsigned_lit by lia.
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact FLOC | exact HB0
             | reflexivity | exact FC0 | exact FL0 | exact BS | exact NW | exact RB | exact WB | exact CHN | exact FD | exact SWF
             | exact BY | unfold va_area; cbn [u64s app]; rewrite ?app_nil_r; exact VAA
             | unfold VF_FRAME; replace (bv_unsigned sp + -80 - 368) with (bv_unsigned sp - 448) by lia;
               replace (bv_unsigned sp + -80 - 352) with (bv_unsigned sp - 432) by lia;
               eapply args_ok_vff; [exact AOK | lia | exact MU | ]; repeat constructor; cbn [fst snd]; lia
             | exact ST | split; [exact SSP1 | exact SSP2] | assumption
             | unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, zlength in *; cbn [length Z.of_nat] in *; lia
             | idtac "FPU-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' PO. unfold vfprintf_ubf_post in PO. rewrite !unsigned_lit in PO by lia.
    sbl_pose_in PO. destruct PO as (-> & WA' & WB' & RB' & BS' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & m3
                     & -> & MUc & WMc & MI3 & ST3 & SSP3 & FC3 & FL3). sbl_subst_all.
    clear FC0 BY AOK VAA.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
    replace (ret_pc (Z_to_bv 64 0x1bd88)) with (Z_to_bv 64 0x1bd88 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold ssp_guard.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of FR with rw_cells _ _ _ ?c1 => lazymatch type of VAc with rw_cells _ _ _ ?c2 =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -80) (c1 ++ c2));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add]; eapply rwc_eqA; [exact VAc | lia] | clear FR VAc ] end end end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -80)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evt_done. unfold fprintf_ubf_post, p. split; [reflexivity|]. split; [exact WA'|]. split; [exact WB'|]. split; [exact RB'|]. split; [exact BS'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [exact FC3| exact FL3].
  Qed.
  End Sz2.
  Theorem fprintf_ubf_spec : ltac:(let t := eval cbv delta [fprintf_ubf_spec__stmt] in fprintf_ubf_spec__stmt in exact t).
  Proof using FLOC GLO HA HB0 HF LO P1 PHI PIECES SMALL. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode rpos rend we wp wb. ltac2:(SecDiet.SzSec.closeP 'fprintf_ubf_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FprintfUbf.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Printf.
  Context {St : Type}.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A lo : Z) (fmtz : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Variables (sw0 ch0 : bool).
  Let p := bv_unsigned sp.
  Let Fp := A_STDOUT.
  Let B := A_STDOUT_BUF.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - FPRINTF_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis PHI : p <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.

  Definition printf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 A ->
    rw_cells usegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells usegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at usegs m A (zb fmtz) -> args_ok Fp 232 B 1024 m lo p (p - 464) [a1; a2; a3; a4; a5; a6; a7] args ->
    stk usegs m lo p -> ssp_cells m canary -> mem_inv usegs m ->
    implM usegs (vfprintf f ps) st (fprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail lo canary sw0 ch0 rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PRINTF) fc None m (seg_rom usegs)).
  Section Sz3.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend : ltac2:(SecDiet.SzSec.tyM 'printf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma printf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'printf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GLO HA HF LO P1 PHI PIECES SMALL. pin_using (fun (GLO HA HF LO P1 PHI PIECES SMALL : unit) => tt).
 intros -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY AOK ST SSP MI.
    unfold FPRINTF_DEPTH, GLOBALS_TOP in *. unfold Fp, B, A_STDOUT, A_STDOUT_BUF in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold p in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). unfold zlength in HA, NNf.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC0.
    pose proof (wmono_refl usegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    stash FC0. stash BUF0. stash BY. stash AOK.
    unfold PRINTF. apply implM_prefix.
    carve_frame 96%nat ST.
    do 21 zs. zs.
    unfold hide in FC0, BUF0, BY, AOK.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call usegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (147456, 147456 + 232); (347440, 347440 + 1024)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]) end.
    clear MUp.
    apply (proj1 (rw_cells_app usegs _ _ [_; _; _; _; _] _)) in FR. destruct FR as [FR VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -96 + Z.of_nat 40) with (bv_unsigned sp + -56) in VAc by lia.
    pose proof (rw_cells_bytes_at _ _ _ _ VAc) as VAA. cbn [cells_bytes cbytes app] in VAA. rewrite ?app_nil_r in VAA.
    apply evt_done.
    eapply implM_post_evt.
    { eapply implM_ms_eq;
        [ eapply (vfprintf_file_spec (Z_to_bv 64 0x1c1fc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 ssp_guard) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                    147456 347440 closefn readfn seekfn prev next tail A (bv_unsigned sp + -56) lo fmtz [a1; a2; a3; a4; a5; a6; a7] args ps r canary sw0 ch0)
        | unfold ssp_guard; ms_eq ].
      all: rewrite ?unsigned_lit by lia.
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC0 | exact FL0 | exact BUF0 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
             | exact BY | unfold va_area; cbn [u64s app]; rewrite ?app_nil_r; exact VAA
             | unfold VF_FRAME; replace (bv_unsigned sp + -96 - 368) with (bv_unsigned sp - 464) by lia;
               eapply args_ok_vff; [exact AOK | lia | exact MU | ]; repeat constructor; cbn [fst snd]; lia
             | exact ST | split; [exact SSP1 | exact SSP2] | assumption
             | unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, zlength in *; cbn [length Z.of_nat] in *; lia
             | idtac "PF-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' PO. unfold vfprintf_file_post in PO. rewrite !unsigned_lit in PO by lia.
    sbl_pose_in PO. destruct PO as (-> & INV' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & bufbytes' & m3 & rpos' & rend'
                     & -> & MUc & WMc & MI3 & ST3 & SSP3 & FC3 & RP3 & FL3 & BUF3 & BP3 & WBL3). sbl_subst_all.
    clear FC0 BUF0 BY AOK VAA.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
    replace (ret_pc (Z_to_bv 64 0x1c1fc)) with (Z_to_bv 64 0x1c1fc : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold ssp_guard.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of FR with rw_cells _ _ _ ?c1 => lazymatch type of VAc with rw_cells _ _ _ ?c2 =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -96) (c1 ++ c2));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add]; eapply rwc_eqA; [exact VAc | lia] | clear FR VAc ] end end end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -96)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evt_done. unfold fprintf_file_post. split; [reflexivity|]. split; [exact INV'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [exact FC3|]. split; [exact RP3|]. split; [exact FL3|]. split; [exact BUF3|]. split; [exact BP3| exact WBL3].
  Qed.
  End Sz3.
  Theorem printf_spec : ltac:(let t := eval cbv delta [printf_spec__stmt] in printf_spec__stmt in exact t).
  Proof using GLO HA HF LO P1 PHI PIECES SMALL. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend. ltac2:(SecDiet.SzSec.closeP 'printf_spec__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Printf.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Vprintf.
  Context {St : Type}.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Variables (sw0 ch0 : bool).
  Let q := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^47.   (* [comment removed for export] *)

  Definition vprintf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 VA ->
    rw_cells usegs m A_STDOUT (fcells flags rpos rend closefn (if f_wactive f then A_STDOUT_BUF + 1024 else 0) (if f_wactive f then A_STDOUT_BUF + zlength (f_wbuf f) else 0) (if f_wactive f then A_STDOUT_BUF else 0)
                           readfn (wfn_of f) seekfn A_STDOUT_BUF 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells usegs m A_STDOUT_BUF [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at usegs m A (zb fmtz) -> va_area m VA slots -> args_ok A_STDOUT 232 A_STDOUT_BUF 1024 m lo q (q - VF_FRAME) slots args ->
    stk usegs m lo q -> ssp_cells m canary -> mem_inv usegs m ->
    implM usegs (vfprintf f ps) st (vfprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_STDOUT A_STDOUT_BUF closefn readfn seekfn prev next tail lo canary sw0 ch0 rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VPRINTF) fc None m (seg_rom usegs)).
  Section Sz4.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend : ltac2:(SecDiet.SzSec.tyM 'vprintf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma vprintf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vprintf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GLO HA HF HVA LO P1 PIECES SMALL. pin_using (fun (GLO HA HF HVA LO P1 PIECES SMALL : unit) => tt).
 intros -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY VAA AOK ST SSP MI.
    unfold A_STDOUT, A_STDOUT_BUF in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold VPRINTF. apply implM_prefix.
    do 7 zs. apply evt_done.
    eapply implM_ms_eq; [eapply vfprintf_file_spec | ms_eq].
    all: match goal with |- ?g => fastfirst (first
           [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact LO | exact GLO | exact HA | exact HVA
           | reflexivity | exact FC0 | exact FL0 | exact BUF0 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
           | exact BY | exact VAA | exact AOK | exact ST | exact SSP | exact MI
           | unfold GLOBALS_TOP in *; lia
           | idtac "VP-LEFT:" g; fail ]) end.
  Qed.
  End Sz4.
  Theorem vprintf_spec : ltac:(let t := eval cbv delta [vprintf_spec__stmt] in vprintf_spec__stmt in exact t).
  Proof using GLO HA HF HVA LO P1 PIECES SMALL. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend. ltac2:(SecDiet.SzSec.closeP 'vprintf_spec__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Vprintf.
End TwB.
End F_fprintf.

(* [comment removed for export] *)
Module F_vfprintf_sn.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep FP ITree Nodes Decode StoreFast ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sn_write__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_printf_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_fwritex_sn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.Printf_snsink.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
Ltac readdr H A' := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let H' := fresh in assert (H' : rw_cells ssegs m A' cs) by (eapply rwc_eqA; [exact H | lia]); clear H; rename H' into H end.

Definition VFPRINTF : Z := 0x1bbac.
Definition TOWRITE : Z := 0x1b914.
Definition VF_FRAME : Z := 368.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition towrite_sn__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Fp bufp bufsize CK : Z) (md : word) (wend wpos wbase : Z),
  a0 = Z_to_bv 64 Fp ->
  rw_cells ssegs m Fp (snfile_cells wend wpos wbase bufp bufsize md CK) ->
  (0 <= bufp) -> (bufp + bufsize < 2^64) -> (0 <= bufsize) -> mem_inv ssegs m ->
  evt ssegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (md' : word) (m' : mem),
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ssegs)
               /\ munch [(Fp, Fp + 232)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
               /\ rw_cells ssegs m' Fp (snfile_cells (bufp + bufsize) bufp bufp bufp bufsize md' CK))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TOWRITE) fc None m (seg_rom ssegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp bufp bufsize CK md wend wpos wbase : ltac2:(SecDiet.SzSec.tyM 'towrite_sn__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma towrite_sn__body : ltac2:(SecDiet.SzSec.bodyP 'towrite_sn__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros -> FC B0 BHI BS0 MI.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite snfile_cells_size in FB.
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  unfold snfile_cells in FC. unfold TOWRITE.
  do 5 zs. zs. zs. first [if_lit | brf K0; [exfalso; revert K0; cbn; rewrite ?unsigned_lit by lia; cbn; lia|]].
  do 10 zs.
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  unfold snfile_cells. match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | lazymatch type of H with ?t => idtac "TW:" t end; fail] end.
Qed.
End Sz1.
Lemma towrite_sn : ltac:(let t := eval cbv delta [towrite_sn__stmt] in towrite_sn__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp bufp bufsize CK md wend wpos wbase. ltac2:(SecDiet.SzSec.closeP 'towrite_sn__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Forall_disj_vf : forall (W : list (Z * Z)) lo sp Fp FS B BS a n,
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  (a + n <= lo \/ sp <= a) -> (a + n <= Fp \/ Fp + FS <= a) -> (a + n <= B \/ B + BS <= a) -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W lo sp Fp FS B BS a n H H1 H2 H3 Hn. induction H as [|[u1 u2] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

(* [comment removed for export] *)
Definition arg_ok_vf__stmt : Prop := forall Fp FS B BS m m' lo sp sp' ap w a (W : list (Z * Z)),
  arg_ok Fp FS B BS m lo sp ap w a -> sp' <= sp -> munch W m m' ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  arg_ok Fp FS B BS m' lo sp' ap w a.
Section Sz3.
Variables Fp FS B BS m m' lo sp sp' ap w a W : ltac2:(SecDiet.SzSec.tyM 'arg_ok_vf__stmt "vvvvvvvvvvvvv" @Fp).
#[using="Type"] Lemma arg_ok_vf__body : ltac2:(SecDiet.SzSec.bodyP 'arg_ok_vf__stmt "vvvvvvvvvvvvv").
Proof.
  intros H Hsp MU HW.
 destruct a as [s|i|u|u]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & S47). exists slack.   (* [comment removed for export] *)
  split; [|repeat (split; [fastfirst (first [assumption | lia])|]); exact S47].
  eapply bytes_at_transport; [exact BY | exact MU |].
  rewrite length_app, zb_length. cbn [length]. unfold zlength in *.
  eapply Forall_disj_vf; [exact HW | | | | lia]; lia.
Qed.
End Sz3.
Lemma arg_ok_vf : ltac:(let t := eval cbv delta [arg_ok_vf__stmt] in arg_ok_vf__stmt in exact t).
Proof. intros Fp FS B BS m m' lo sp sp' ap w a W. ltac2:(SecDiet.SzSec.closeP 'arg_ok_vf__body "vvvvvvvvvvvvv"). Qed.
Lemma args_ok_vf : forall Fp FS B BS m m' lo sp sp' ap ws args (W : list (Z * Z)),
  args_ok Fp FS B BS m lo sp ap ws args -> sp' <= sp -> munch W m m' ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  args_ok Fp FS B BS m' lo sp' ap ws args.
Proof.
  intros Fp FS B BS m m' lo sp sp' ap ws args W. revert ws. induction args as [|a args IH]; intros ws H Hsp MU HW; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vfprintf_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D cap : Z) (dn : nat) (out : list Z) (r lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fj jd' : list byte) (m' : mem),
    let q := bv_unsigned sp in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(lo, q + 248); (D, D + Z.of_nat dn)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo q
    /\ ssp_cells m' canary
    /\ rw_cells ssegs m' D [CB dn (zb (firstn (Z.to_nat cap) out) ++ Z_to_bv 8 0 :: jd')]
    /\ rw_cells ssegs m' q [CB 248 fj].

Section Vfprintf.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D cap : Z) (dn : nat) (A VA qtop lo bufp0 : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Let q := bv_unsigned sp.
  Hypothesis DN : Z.of_nat dn = cap + 1.
  Hypothesis CAP0 : 0 <= cap.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis QTOP : q + 248 <= qtop.
  Hypothesis QHI : qtop <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis HVA : qtop <= VA /\ VA + 8 * zlength slots <= 2^64.
  Hypothesis BUFP0 : 0 < bufp0 < 2^64.
  Hypothesis HD : 0 < D /\ D + Z.of_nat dn <= 2^63 /\ (D + Z.of_nat dn <= 0x10000 \/ 0x55000 <= D)
                  /\ (D + Z.of_nat dn <= lo \/ VA + 8 * zlength slots <= D \/ (qtop <= D /\ D + Z.of_nat dn <= VA)).

  Definition vfprintf_sn_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (jd : list byte) (Fp : Z),
    q = Fp ->
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells ssegs m Fp (snfile_cells 0 0 0 bufp0 0 (Z_to_bv 64 0) (Fp + 232)) ->
    rw_cells ssegs m (Fp + 232) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 cap)] ->
    rw_cells ssegs m D [CB dn jd] ->
    bytes_at ssegs m A (zb fmtz) ->
    va_area m VA slots -> args_ok (q - 352) SN_FS D (Z.of_nat dn) m lo qtop (q - 368) slots args ->
    stk ssegs m lo q -> ssp_cells m canary -> mem_inv ssegs m -> fany fc ->
    evt ssegs (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D cap dn (concat ps) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF) fc None m (seg_rom ssegs)).
  Section Sz5.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd Fp : ltac2:(SecDiet.SzSec.tyM 'vfprintf_sn_spec__stmt "vvvvvvvvvvvvvvvvvv" @t0).
  Lemma vfprintf_sn_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_sn_spec__stmt "vvvvvvvvvvvvvvvvvv").
  Proof using BUFP0 CAP0 DN GLO HA HD HF HVA LO P1 PIECES QHI QTOP. pin_using (fun (BUFP0 CAP0 DN GLO HA HD HF HVA LO P1 PIECES QHI QTOP : unit) => tt).
    intros EFP -> -> -> FC0 CKC0 DST0 BY VAA AOK ST SSP MI FRM.
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, SN_FS in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (rw_CB_length _ _ _ _ DST0) as LJD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, HD, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (DSEP : D + Z.of_nat dn <= lo \/ bv_unsigned sp + 248 <= D) by (clear -HD HVA QTOP NNs; lia).
    assert (DHI : 0 < D /\ D + Z.of_nat dn <= 2^63) by (clear -HD; lia).
    pose proof (wmono_refl ssegs m) as WM.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash HD. stash FC0. stash CKC0. stash DST0. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VFPRINTF.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells ssegs ?mm ?A [CB 368 ?j] |- _ =>
        apply (rw_cells_split_CB ssegs mm A [] 368 j [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    do 12 zs. do 14 zs.
    unfold hide in FC0, CKC0, DST0, HD.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call ssegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp + 248); (D, D + Z.of_nat dn)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]);
      assert (MU1 : munch [(lo, bv_unsigned sp + 248)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]);
      unfold hide in BY, VAA;
      eapply (bytes_at_transport _ Wp ma mb) in BY; [| exact MUp | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; lia];
      unfold va_area in VAA;
      eapply (bytes_at_transport _ Wp ma mb) in VAA; [| exact MUp | cbn [disjoint_from]; rewrite u64s_length; clear -HVA QTOP; lia]
    end.
    clear MUp. stash HD. stash VAA.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    unfold snfile_cells in FC0.
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. first [if_lit | brf Kl; [|exfalso; revert Kl; cbn; rewrite ?unsigned_lit by lia; cbn; lia]]. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) in *. zs. rewrite ?unsigned_lit by lia. change (Z.land 0 18446744073709551583) with 0.
    zs. (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    do 8 zs. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    set (Bi := bv_unsigned sp + -352) in *.
    eapply evt_cut.
    { eapply (towrite_sn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fp Bi 80 (Fp + 232) (Z_to_bv 64 0) 0 0 0);
        [ reflexivity | unfold snfile_cells; match goal with H : rw_cells _ _ Fp _ |- _ => exact H end | lia | lia | lia | assumption ]. }
    cbv beta. intros ms' PO.
    destruct PO as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & md & m'' & -> & MUc & WMc & MIt & FC1).
    match goal with H : rw_cells _ ?mm Fp (_ :: _) |- _ => clear H end.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. (* [comment removed for export] *)
    do 5 zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB ssegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in FRv. destruct FRv as [IBc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr IBc Bi. readdr FRv (Bi + 80)%Z. readdr AP2 (bv_unsigned sp + -360)%Z.
    match type of IBc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in IBc end. clearbody jb.
    match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
    pose proof (rw_CB_length _ _ _ _ IBc) as LJB.
    replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
    lazymatch type of FRv with rw_cells _ ?mm _ ?fr => set (frest := fr) in FRv end.
    unfold hide in HD.
    assert (SNK : SINK_sn Bi md frest D cap dn m'' []).
    { exists [], [], jb, jd, Bi, D, cap. cbv zeta. unfold SN_FOFF, SN_FS. rewrite !firstn_nil.
      split; [reflexivity|]. split; [change (zlength (@nil Z)) with 0; lia|].
      split; [change (zlength (@nil Z)) with 0; lia|].
      split; [change (zlength (@nil Z)) with 0; lia|]. split; [change (zlength (@nil Z)) with 0; lia|].
      split. { replace (Bi + 352) with Fp by lia. replace (Bi + 352 + 232) with (Fp + 232) by lia. exact FC1. }
      split; [cbn [zb map app]; exact IBc|].
      split; [exact FRv|]. split; [reflexivity|].
      split. { replace (Bi + 352 + 232) with (Fp + 232) by lia. exact CKC0. }
      split; [cbn [zb map app]; exact DST0|].
      clear -DN CAP0 GLO LO HD SPHI QTOP QHI HVA EFP. subst Bi. repeat (split; [lia|]). lia. }
    (* [comment removed for export] *)
    assert (PCALL : forall Q ms, implM ssegs (printf_model OUT_app fmtz args) [] Q ms -> evt ssegs (Q r (concat ps)) ms).
    { intros Q ms H. eapply (implM_eval ssegs); [| exact H]. rewrite (printf_model_app _ _ _ _ [] PIECES). reflexivity. }
    pose proof (printf_core_proof (list Z) Bi SN_FS (Bi + SN_FOFF) D (Z.of_nat dn) (SINK_sn Bi md frest D cap dn) (TOPOK_sn Bi) OUT_app
                  (sn_sink_frame Bi md frest D cap dn) (sn_sink_flags Bi md frest D cap dn) (sn_topok Bi) (sn_out Bi md frest D cap dn)) as PC2.
    unfold printf_core_stmt in PC2.
    unfold hide in AOK. try clear BY. try clear VAA.
    assert (BY : bytes_at ssegs m'' A (zb fmtz)).
    { unfold hide in BYm. eapply bytes_at_transport; [exact BYm | exact MU1 | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; lia]. }
    assert (VAA : va_area m'' VA slots).
    { unfold hide in VAAm. unfold va_area in *. eapply bytes_at_transport; [exact VAAm | exact MU1 | cbn [disjoint_from]; rewrite u64s_length; clear -HVA QTOP; lia]. }
    eapply evt_cut.
    { apply PCALL. eapply PC2 with (i := 0%Z) (slots := slots); clear PC2 PCALL; rewrite ?unsigned_lit by lia;
        unfold PC_DEPTH, GLOBALS_TOP, TOPOK_sn, SN_FS, SN_FOFF, zlength.
      - exact SNK.
      - exact BY.
      - exact HF.
      - f_equal. subst Bi. lia.
      - exact APC.
      - exact VAA.
      - lia.
      - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | subst Bi; lia | exact MU1 |].
        constructor; [cbn [fst snd]; left; lia | constructor].
      - exact STc.
      - lia.
      - lia.
      - lia.
      - subst Bi; lia.
      - unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact FRM.
      - lia.
      - lia.
      - subst Bi; lia.
      - right; left. subst Bi. clear -HVA QTOP SPHI LO GLO. lia.
      - clear -HD DHI LO GLO QTOP SPHI. destruct HD as (HD1 & HD1' & HD2 & [HD3 | [HD3 | HD3]]);
          [right; right; left; lia | right; right; right; lia | right; left; lia].
      - lia.
      - clear -HVA QTOP SPHI. lia.
      - lia. }
    cbv beta. intros ms' PO. clear PC2 PCALL.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    subst fc' Ft.
    unfold SR, SN_FS in MUc. cbn [app] in MUc.
    clear SNK APC IBc FRv FC1 CKC0 DST0 AOK VAA BY MU1.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m3 MUc WMc; clear MUc WMc; try clear MIt end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    destruct SNK3 as (P & o & jb3 & jd3 & wp & cs & cn & SNK3). cbv zeta in SNK3.
    destruct SNK3 as (ET & LO80 & Ewp & Ecs & Ecn & FC3 & IB3 & FR3 & FRL & CKC3 & DST3 & _).
    unfold SN_FOFF in FC3, CKC3. readdr FC3 Fp. readdr CKC3 (Fp + 232)%Z.
    replace (Bi + 352 + 232) with (Fp + 232) in FC3 by lia.
    pose proof (rw_CB_length _ _ _ _ IB3) as LJ3. rewrite length_app, zb_length in LJ3.
    assert (NNo : 0 <= zlength o <= 80) by (unfold zlength in *; clear -LJ3; lia).
    unfold snfile_cells in FC3.
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf Kb; [exfalso; clear -Kb BUFP0; rewrite ?unsigned_lit in Kb by lia; lia|].
    zs. (* [comment removed for export] *) zs. zs. zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 SN_WRITE)) with (Z_to_bv 64 SN_WRITE : word) by (unfold SN_WRITE; symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with H : rw_cells _ mm Fp (_ :: _) |- _ =>
        destruct (snfile_split mm Fp _ _ _ _ _ _ _ H) as (G0 & G40 & G48 & G56 & G64 & G88 & G96 & G152 & G160); clear H end end.
    cbn [firstn skipn snfile_cells] in G0, G96.
    rewrite Ewp in G40. rewrite Ecs, Ecn in CKC3.
    pose proof (rw_cells_bytes_at _ _ _ _ IB3) as BO3. cbn [cells_bytes cbytes app] in BO3. rewrite app_nil_r in BO3.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in BO3. destruct BO3 as [BO3 _].
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => rename H into ST3' end.
    eapply evt_cut.
    { eapply (sn_write_spec (Z_to_bv 64 113876) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp s6 s7 s8 s9 s10 s11 F fc Fp (Fp + 232) D cap Bi 0 Bi lo o [] dn)
        with (wr := firstn (Z.to_nat cap) P) (junk := jd3);
        rewrite ?unsigned_lit by lia; unfold zlength in *;
        fastfirst (first [ noevar_assumption | exact DN | reflexivity | eassumption
              | apply bytes_at_nil; lia
              | subst Bi; clear -CAP0 DN NNo LO GLO SPHI QTOP QHI DSEP DHI LJ3 EFP; cbn [length Z.of_nat]; rewrite ?length_firstn; lia
              | match goal with |- ?g => idtac "SNW-PREM:" g end; fail ]). }
    cbv beta. intros ms' PO.
    unfold sn_write_post in PO. cbv zeta in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (w5 & w6 & w7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w28 & w29 & w30 & w31 & m4 & junk' & -> & MUc & WMc & MI4 & ST4 & CKC4 & DST4 & F40 & F56 & BO4 & BS4 & LE4).
    clear G40 G56 CKC3 DST3 BO3 ST3'.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
    fix_ret.
    (* [comment removed for export] *)
    subst frest. readdr FR3 (bv_unsigned sp + -272)%Z. readdr IB3 (bv_unsigned sp + -352)%Z.
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (0 <? Bi)%Z with true by (symmetry; apply Z.ltb_lt; subst Bi; lia). cbn [Z.b2z].
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) rewrite ?Z.lor_0_l.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word).
    zs. zs. zs. zs. zs. (* [comment removed for export] *) rewrite ?Z.lor_0_l.
    zs. (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs. (* [comment removed for export] *)
    unfold INT_MAX in Hr. rewrite (land_W64_small r) by lia.
    (* [comment removed for export] *)
    match goal with H : stk _ _ lo (bv_unsigned sp + -368)%Z |- _ => rename H into ST5 end.
    release_frame APC3 ST5 (bv_unsigned sp + -360)%Z.
    release_frame AP2 ST5 (bv_unsigned sp + -352)%Z.
    release_frame IB3 ST5 (bv_unsigned sp + -272)%Z.
    release_frame FR3 ST5 (bv_unsigned sp).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of CKC4 with rw_cells _ _ _ ?ckc =>
      assert (FALL : rw_cells ssegs mm Fp
        ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
         ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)]
         ++ [C8 (Z_to_bv 64 bufp0)]
         ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
             C4 md; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0)]
         ++ [C8 (Z_to_bv 64 (Fp + 232))] ++ [CB 72 (repeat (Z_to_bv 8 0) 72)] ++ ckc))
    end end.
    { apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [exact G0|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact F40|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact G48|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact F56|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact G64|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact G88|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact G96|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact G152|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [eapply rwc_eqA; [exact G160|lia]|]; cbn [cells_size csize Nat.add].
      eapply rwc_eqA; [exact CKC4|lia]. }
    destruct (rw_cells_forget _ _ _ _ FALL) as [fj FJ]. cbn [cells_size csize Nat.add app length] in FJ.
    (* [comment removed for export] *)
    rewrite app_nil_r in DST4. rewrite (firstn_cap_app cap P o CAP0) in DST4. rewrite <- ET in DST4.
    rewrite <- EFP in FJ.
    apply evt_done. unfold vfprintf_sn_post. cbv zeta.
    exists w5, w6, w7. do 11 eexists. exists fj, junk', m4.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [assumption|]. split; [assumption|].
    split; [exact ST5|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [exact DST4|]. exact FJ.
  Qed.
  End Sz5.
  Theorem vfprintf_sn_spec : ltac:(let t := eval cbv delta [vfprintf_sn_spec__stmt] in vfprintf_sn_spec__stmt in exact t).
  Proof using BUFP0 CAP0 DN GLO HA HD HF HVA LO P1 PIECES QHI QTOP. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd Fp. ltac2:(SecDiet.SzSec.closeP 'vfprintf_sn_spec__body "vvvvvvvvvvvvvvvvvv"). Qed.
End Vfprintf.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.FP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_printf_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_fwritex_sn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.Printf_snsink.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
Ltac readdr H A' := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let H' := fresh in assert (H' : rw_cells usegs m A' cs) by (eapply rwc_eqA; [exact H | lia]); clear H; rename H' into H end.

Definition VFPRINTF : Z := 0x1c36c.
Definition TOWRITE : Z := 0x1c0d4.
Definition VF_FRAME : Z := 368.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition towrite_sn__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Fp bufp bufsize CK : Z) (md : word) (wend wpos wbase : Z),
  a0 = Z_to_bv 64 Fp ->
  rw_cells usegs m Fp (snfile_cells wend wpos wbase bufp bufsize md CK) ->
  (0 <= bufp) -> (bufp + bufsize < 2^64) -> (0 <= bufsize) -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (md' : word) (m' : mem),
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom usegs)
               /\ munch [(Fp, Fp + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
               /\ rw_cells usegs m' Fp (snfile_cells (bufp + bufsize) bufp bufp bufp bufsize md' CK))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TOWRITE) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp bufp bufsize CK md wend wpos wbase : ltac2:(SecDiet.SzSec.tyM 'towrite_sn__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma towrite_sn__body : ltac2:(SecDiet.SzSec.bodyP 'towrite_sn__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros -> FC B0 BHI BS0 MI.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite snfile_cells_size in FB.
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold snfile_cells in FC. unfold TOWRITE.
  do 5 zs. zs. zs. first [if_lit | brf K0; [exfalso; revert K0; cbn; rewrite ?unsigned_lit by lia; cbn; lia|]].
  do 10 zs.
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  unfold snfile_cells. match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | lazymatch type of H with ?t => idtac "TW:" t end; fail] end.
Qed.
End Sz1.
Lemma towrite_sn : ltac:(let t := eval cbv delta [towrite_sn__stmt] in towrite_sn__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp bufp bufsize CK md wend wpos wbase. ltac2:(SecDiet.SzSec.closeP 'towrite_sn__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Forall_disj_vf : forall (W : list (Z * Z)) lo sp Fp FS B BS a n,
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  (a + n <= lo \/ sp <= a) -> (a + n <= Fp \/ Fp + FS <= a) -> (a + n <= B \/ B + BS <= a) -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W lo sp Fp FS B BS a n H H1 H2 H3 Hn. induction H as [|[u1 u2] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

(* [comment removed for export] *)
Definition arg_ok_vf__stmt : Prop := forall Fp FS B BS m m' lo sp sp' ap w a (W : list (Z * Z)),
  arg_ok Fp FS B BS m lo sp ap w a -> sp' <= sp -> munch W m m' ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  arg_ok Fp FS B BS m' lo sp' ap w a.
Section Sz3.
Variables Fp FS B BS m m' lo sp sp' ap w a W : ltac2:(SecDiet.SzSec.tyM 'arg_ok_vf__stmt "vvvvvvvvvvvvv" @Fp).
#[using="Type"] Lemma arg_ok_vf__body : ltac2:(SecDiet.SzSec.bodyP 'arg_ok_vf__stmt "vvvvvvvvvvvvv").
Proof.
  intros H Hsp MU HW.
 destruct a as [s|i|u|u]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & S47). exists slack.   (* [comment removed for export] *)
  split; [|repeat (split; [fastfirst (first [assumption | lia])|]); exact S47].
  eapply bytes_at_transport; [exact BY | exact MU |].
  rewrite length_app, zb_length. cbn [length]. unfold zlength in *.
  eapply Forall_disj_vf; [exact HW | | | | lia]; lia.
Qed.
End Sz3.
Lemma arg_ok_vf : ltac:(let t := eval cbv delta [arg_ok_vf__stmt] in arg_ok_vf__stmt in exact t).
Proof. intros Fp FS B BS m m' lo sp sp' ap w a W. ltac2:(SecDiet.SzSec.closeP 'arg_ok_vf__body "vvvvvvvvvvvvv"). Qed.
Lemma args_ok_vf : forall Fp FS B BS m m' lo sp sp' ap ws args (W : list (Z * Z)),
  args_ok Fp FS B BS m lo sp ap ws args -> sp' <= sp -> munch W m m' ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  args_ok Fp FS B BS m' lo sp' ap ws args.
Proof.
  intros Fp FS B BS m m' lo sp sp' ap ws args W. revert ws. induction args as [|a args IH]; intros ws H Hsp MU HW; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vfprintf_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D cap : Z) (dn : nat) (out : list Z) (r lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fj jd' : list byte) (m' : mem),
    let q := bv_unsigned sp in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, q + 248); (D, D + Z.of_nat dn)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo q
    /\ ssp_cells m' canary
    /\ rw_cells usegs m' D [CB dn (zb (firstn (Z.to_nat cap) out) ++ Z_to_bv 8 0 :: jd')]
    /\ rw_cells usegs m' q [CB 248 fj].

Section Vfprintf.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D cap : Z) (dn : nat) (A VA qtop lo bufp0 : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Let q := bv_unsigned sp.
  Hypothesis DN : Z.of_nat dn = cap + 1.
  Hypothesis CAP0 : 0 <= cap.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis QTOP : q + 248 <= qtop.
  Hypothesis QHI : qtop <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis HVA : qtop <= VA /\ VA + 8 * zlength slots <= 2^64.
  Hypothesis BUFP0 : 0 < bufp0 < 2^64.
  Hypothesis HD : 0 < D /\ D + Z.of_nat dn <= 2^63 /\ (D + Z.of_nat dn <= 0x10000 \/ 0x56000 <= D)
                  /\ (D + Z.of_nat dn <= lo \/ VA + 8 * zlength slots <= D \/ (qtop <= D /\ D + Z.of_nat dn <= VA)).

  Definition vfprintf_sn_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (jd : list byte) (Fp : Z),
    q = Fp ->
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells usegs m Fp (snfile_cells 0 0 0 bufp0 0 (Z_to_bv 64 0) (Fp + 232)) ->
    rw_cells usegs m (Fp + 232) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 cap)] ->
    rw_cells usegs m D [CB dn jd] ->
    bytes_at usegs m A (zb fmtz) ->
    va_area m VA slots -> args_ok (q - 352) SN_FS D (Z.of_nat dn) m lo qtop (q - 368) slots args ->
    stk usegs m lo q -> ssp_cells m canary -> mem_inv usegs m -> fany fc ->
    evt usegs (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D cap dn (concat ps) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF) fc None m (seg_rom usegs)).
  Section Sz5.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd Fp : ltac2:(SecDiet.SzSec.tyM 'vfprintf_sn_spec__stmt "vvvvvvvvvvvvvvvvvv" @t0).
  Lemma vfprintf_sn_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_sn_spec__stmt "vvvvvvvvvvvvvvvvvv").
  Proof using BUFP0 CAP0 DN GLO HA HD HF HVA LO P1 PIECES QHI QTOP. pin_using (fun (BUFP0 CAP0 DN GLO HA HD HF HVA LO P1 PIECES QHI QTOP : unit) => tt).
 intros EFP -> -> -> FC0 CKC0 DST0 BY VAA AOK ST SSP MI FRM.
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, SN_FS in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (rw_CB_length _ _ _ _ DST0) as LJD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, HD, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (DSEP : D + Z.of_nat dn <= lo \/ bv_unsigned sp + 248 <= D) by (clear -HD HVA QTOP NNs; lia).
    assert (DHI : 0 < D /\ D + Z.of_nat dn <= 2^63) by (clear -HD; lia).
    pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash HD. stash FC0. stash CKC0. stash DST0. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VFPRINTF.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells usegs ?mm ?A [CB 368 ?j] |- _ =>
        apply (rw_cells_split_CB usegs mm A [] 368 j [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    do 12 zs. do 14 zs.
    unfold hide in FC0, CKC0, DST0, HD.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call usegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp + 248); (D, D + Z.of_nat dn)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]);
      assert (MU1 : munch [(lo, bv_unsigned sp + 248)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]);
      unfold hide in BY, VAA;
      eapply (bytes_at_transport _ Wp ma mb) in BY; [| exact MUp | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; lia];
      unfold va_area in VAA;
      eapply (bytes_at_transport _ Wp ma mb) in VAA; [| exact MUp | cbn [disjoint_from]; rewrite u64s_length; clear -HVA QTOP; lia]
    end.
    clear MUp. stash HD. stash VAA.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    unfold snfile_cells in FC0.
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. first [if_lit | brf Kl; [|exfalso; revert Kl; cbn; rewrite ?unsigned_lit by lia; cbn; lia]]. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) in *. zs. rewrite ?unsigned_lit by lia. change (Z.land 0 18446744073709551583) with 0.
    zs. (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    do 8 zs. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    set (Bi := bv_unsigned sp + -352) in *.
    eapply evt_cut.
    { eapply (towrite_sn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fp Bi 80 (Fp + 232) (Z_to_bv 64 0) 0 0 0);
        [ reflexivity | unfold snfile_cells; match goal with H : rw_cells _ _ Fp _ |- _ => exact H end | lia | lia | lia | assumption ]. }
    cbv beta. intros ms' PO.
    destruct PO as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & md & m'' & -> & MUc & WMc & MIt & FC1).
    match goal with H : rw_cells _ ?mm Fp (_ :: _) |- _ => clear H end.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. (* [comment removed for export] *)
    do 5 zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB usegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [IBc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr IBc Bi. readdr FRv (Bi + 80)%Z. readdr AP2 (bv_unsigned sp + -360)%Z.
    match type of IBc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in IBc end. clearbody jb.
    match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
    pose proof (rw_CB_length _ _ _ _ IBc) as LJB.
    replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
    lazymatch type of FRv with rw_cells _ ?mm _ ?fr => set (frest := fr) in FRv end.
    unfold hide in HD.
    assert (SNK : SINK_sn Bi md frest D cap dn m'' []).
    { exists [], [], jb, jd, Bi, D, cap. cbv zeta. unfold SN_FOFF, SN_FS. rewrite !firstn_nil.
      split; [reflexivity|]. split; [change (zlength (@nil Z)) with 0; lia|].
      split; [change (zlength (@nil Z)) with 0; lia|].
      split; [change (zlength (@nil Z)) with 0; lia|]. split; [change (zlength (@nil Z)) with 0; lia|].
      split. { replace (Bi + 352) with Fp by lia. replace (Bi + 352 + 232) with (Fp + 232) by lia. exact FC1. }
      split; [cbn [zb map app]; exact IBc|].
      split; [exact FRv|]. split; [reflexivity|].
      split. { replace (Bi + 352 + 232) with (Fp + 232) by lia. exact CKC0. }
      split; [cbn [zb map app]; exact DST0|].
      clear -DN CAP0 GLO LO HD SPHI QTOP QHI HVA EFP. subst Bi. repeat (split; [lia|]). lia. }
    (* [comment removed for export] *)
    assert (PCALL : forall Q ms, implM usegs (printf_model OUT_app fmtz args) [] Q ms -> evt usegs (Q r (concat ps)) ms).
    { intros Q ms H. eapply (implM_eval usegs); [| exact H]. rewrite (printf_model_app _ _ _ _ [] PIECES). reflexivity. }
    pose proof (printf_core_proof (list Z) Bi SN_FS (Bi + SN_FOFF) D (Z.of_nat dn) (SINK_sn Bi md frest D cap dn) (TOPOK_sn Bi) OUT_app
                  (sn_sink_frame Bi md frest D cap dn) (sn_sink_flags Bi md frest D cap dn) (sn_topok Bi) (sn_out Bi md frest D cap dn)) as PC2.
    unfold printf_core_stmt in PC2.
    unfold hide in AOK. try clear BY. try clear VAA.
    assert (BY : bytes_at usegs m'' A (zb fmtz)).
    { unfold hide in BYm. eapply bytes_at_transport; [exact BYm | exact MU1 | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; lia]. }
    assert (VAA : va_area m'' VA slots).
    { unfold hide in VAAm. unfold va_area in *. eapply bytes_at_transport; [exact VAAm | exact MU1 | cbn [disjoint_from]; rewrite u64s_length; clear -HVA QTOP; lia]. }
    eapply evt_cut.
    { apply PCALL. eapply PC2 with (i := 0%Z) (slots := slots); clear PC2 PCALL; rewrite ?unsigned_lit by lia;
        unfold PC_DEPTH, GLOBALS_TOP, TOPOK_sn, SN_FS, SN_FOFF, zlength.
      - exact SNK.
      - exact BY.
      - exact HF.
      - f_equal. subst Bi. lia.
      - exact APC.
      - exact VAA.
      - lia.
      - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | subst Bi; lia | exact MU1 |].
        constructor; [cbn [fst snd]; left; lia | constructor].
      - exact STc.
      - lia.
      - lia.
      - lia.
      - subst Bi; lia.
      - unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact FRM.
      - lia.
      - lia.
      - subst Bi; lia.
      - right; left. subst Bi. clear -HVA QTOP SPHI LO GLO. lia.
      - clear -HD DHI LO GLO QTOP SPHI. destruct HD as (HD1 & HD1' & HD2 & [HD3 | [HD3 | HD3]]);
          [right; right; left; lia | right; right; right; lia | right; left; lia].
      - lia.
      - clear -HVA QTOP SPHI. lia.
      - lia. }
    cbv beta. intros ms' PO. clear PC2 PCALL.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    subst fc' Ft.
    unfold SR, SN_FS in MUc. cbn [app] in MUc.
    clear SNK APC IBc FRv FC1 CKC0 DST0 AOK VAA BY MU1.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc; try clear MIt end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    destruct SNK3 as (P & o & jb3 & jd3 & wp & cs & cn & SNK3). cbv zeta in SNK3.
    destruct SNK3 as (ET & LO80 & Ewp & Ecs & Ecn & FC3 & IB3 & FR3 & FRL & CKC3 & DST3 & _).
    unfold SN_FOFF in FC3, CKC3. readdr FC3 Fp. readdr CKC3 (Fp + 232)%Z.
    replace (Bi + 352 + 232) with (Fp + 232) in FC3 by lia.
    pose proof (rw_CB_length _ _ _ _ IB3) as LJ3. rewrite length_app, zb_length in LJ3.
    assert (NNo : 0 <= zlength o <= 80) by (unfold zlength in *; clear -LJ3; lia).
    unfold snfile_cells in FC3.
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf Kb; [exfalso; clear -Kb BUFP0; rewrite ?unsigned_lit in Kb by lia; lia|].
    zs. (* [comment removed for export] *) zs. zs. zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 SN_WRITE)) with (Z_to_bv 64 SN_WRITE : word) by (unfold SN_WRITE; symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with H : rw_cells _ mm Fp (_ :: _) |- _ =>
        destruct (snfile_split mm Fp _ _ _ _ _ _ _ H) as (G0 & G40 & G48 & G56 & G64 & G88 & G96 & G152 & G160); clear H end end.
    cbn [firstn skipn snfile_cells] in G0, G96.
    rewrite Ewp in G40. rewrite Ecs, Ecn in CKC3.
    pose proof (rw_cells_bytes_at _ _ _ _ IB3) as BO3. cbn [cells_bytes cbytes app] in BO3. rewrite app_nil_r in BO3.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in BO3. destruct BO3 as [BO3 _].
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => rename H into ST3' end.
    eapply evt_cut.
    { eapply (sn_write_spec (Z_to_bv 64 115860) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp s6 s7 s8 s9 s10 s11 F fc Fp (Fp + 232) D cap Bi 0 Bi lo o [] dn)
        with (wr := firstn (Z.to_nat cap) P) (junk := jd3);
        rewrite ?unsigned_lit by lia; unfold zlength in *;
        fastfirst (first [ noevar_assumption | exact DN | reflexivity | eassumption
              | apply bytes_at_nil; lia
              | subst Bi; clear -CAP0 DN NNo LO GLO SPHI QTOP QHI DSEP DHI LJ3 EFP; cbn [length Z.of_nat]; rewrite ?length_firstn; lia
              | match goal with |- ?g => idtac "SNW-PREM:" g end; fail ]). }
    cbv beta. intros ms' PO.
    unfold sn_write_post in PO. cbv zeta in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (w5 & w6 & w7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w28 & w29 & w30 & w31 & m4 & junk' & -> & MUc & WMc & MI4 & ST4 & CKC4 & DST4 & F40 & F56 & BO4 & BS4 & LE4).
    clear G40 G56 CKC3 DST3 BO3 ST3'.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
    fix_ret.
    (* [comment removed for export] *)
    subst frest. readdr FR3 (bv_unsigned sp + -272)%Z. readdr IB3 (bv_unsigned sp + -352)%Z.
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (0 <? Bi)%Z with true by (symmetry; apply Z.ltb_lt; subst Bi; lia). cbn [Z.b2z].
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) rewrite ?Z.lor_0_l.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word).
    zs. zs. zs. zs. zs. (* [comment removed for export] *) rewrite ?Z.lor_0_l.
    zs. (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs. (* [comment removed for export] *)
    unfold INT_MAX in Hr. rewrite (land_W64_small r) by lia.
    (* [comment removed for export] *)
    match goal with H : stk _ _ lo (bv_unsigned sp + -368)%Z |- _ => rename H into ST5 end.
    release_frame APC3 ST5 (bv_unsigned sp + -360)%Z.
    release_frame AP2 ST5 (bv_unsigned sp + -352)%Z.
    release_frame IB3 ST5 (bv_unsigned sp + -272)%Z.
    release_frame FR3 ST5 (bv_unsigned sp).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of CKC4 with rw_cells _ _ _ ?ckc =>
      assert (FALL : rw_cells usegs mm Fp
        ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
         ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)]
         ++ [C8 (Z_to_bv 64 bufp0)]
         ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
             C4 md; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0)]
         ++ [C8 (Z_to_bv 64 (Fp + 232))] ++ [CB 72 (repeat (Z_to_bv 8 0) 72)] ++ ckc))
    end end.
    { apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact G0|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact F40|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact G48|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact F56|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact G64|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact G88|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact G96|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact G152|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [eapply rwc_eqA; [exact G160|lia]|]; cbn [cells_size csize Nat.add].
      eapply rwc_eqA; [exact CKC4|lia]. }
    destruct (rw_cells_forget _ _ _ _ FALL) as [fj FJ]. cbn [cells_size csize Nat.add app length] in FJ.
    (* [comment removed for export] *)
    rewrite app_nil_r in DST4. rewrite (firstn_cap_app cap P o CAP0) in DST4. rewrite <- ET in DST4.
    rewrite <- EFP in FJ.
    apply evt_done. unfold vfprintf_sn_post. cbv zeta.
    exists w5, w6, w7. do 11 eexists. exists fj, junk', m4.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [assumption|]. split; [assumption|].
    split; [exact ST5|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [exact DST4|]. exact FJ.
  Qed.
  End Sz5.
  Theorem vfprintf_sn_spec : ltac:(let t := eval cbv delta [vfprintf_sn_spec__stmt] in vfprintf_sn_spec__stmt in exact t).
  Proof using BUFP0 CAP0 DN GLO HA HD HF HVA LO P1 PIECES QHI QTOP. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd Fp. ltac2:(SecDiet.SzSec.closeP 'vfprintf_sn_spec__body "vvvvvvvvvvvvvvvvvv"). Qed.
End Vfprintf.
End TwB.
End F_vfprintf_sn.

(* [comment removed for export] *)
Module F_vsnprintf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep FP ITree Nodes Decode StoreFast ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sn_write__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_printf_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_fwritex_sn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.Printf_snsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_vfprintf_sn.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Definition VSNPRINTF : Z := 0x2056c.
Definition VSN_FRAME : Z := 304.
Definition VSN_DEPTH : Z := 5856.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs', rw_cells ssegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells ssegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.
Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells ssegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells ssegs m A (pre ++ C4 v' :: post).
Proof.
  intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 [_ W2]]. apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac c4_eqv H k v' :=
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
    lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
      let H' := fresh in
      pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
      specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
    end end.

(* [comment removed for export] *)
Definition zfile_cells : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0);
   CB 72 (repeat (Z_to_bv 8 0) 72)].

Definition vsnprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D n : Z) (out : list Z) (r lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jd' : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + n)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells ssegs m' D [CB (Z.to_nat n) (zb (firstn (Z.to_nat (n - 1)) out) ++ Z_to_bv 8 0 :: jd')].

Section Vsnprintf.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D n A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Let q := bv_unsigned sp.
  Hypothesis HN : 1 <= n < 2^31.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis LO : lo <= q - VSN_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis QHI : q <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^64.
  Hypothesis HD : 0 < D /\ D + n <= 2^63 /\ (D + n <= 0x10000 \/ 0x55000 <= D)
                  /\ (D + n <= lo \/ VA + 8 * zlength slots <= D \/ (q <= D /\ D + n <= VA)).

  Definition vsnprintf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (jd : list byte),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells ssegs m D [CB (Z.to_nat n) jd] ->
    bytes_at ssegs m A (zb fmtz) ->
    va_area m VA slots -> args_ok (q - 656) SN_FS D n m lo q (q - 672) slots args ->
    stk ssegs m lo q -> ssp_cells m canary -> mem_inv ssegs m -> fany fc ->
    evt ssegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n (concat ps) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VSNPRINTF) fc None m (seg_rom ssegs)).
  Section Sz3.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd : ltac2:(SecDiet.SzSec.tyM 'vsnprintf_spec__stmt "vvvvvvvvvvvvvvvvv" @t0).
  Lemma vsnprintf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vsnprintf_spec__stmt "vvvvvvvvvvvvvvvvv").
  Proof using GLO HA HD HF HN HVA LO P1 PIECES QHI. pin_using (fun (GLO HA HD HF HN HVA LO P1 PIECES QHI : unit) => tt).
 intros -> -> -> -> DST BY VAA AOK ST SSP MI FRM.
    unfold VSN_DEPTH, GLOBALS_TOP, SN_FS in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (rw_CB_length _ _ _ _ DST) as LJD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, HD, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (DSEP : D + n <= lo \/ bv_unsigned sp <= D) by (clear -HD HVA NNs; lia).
    assert (DHI : 0 < D /\ D + n <= 2^63) by (clear -HD; lia).
    pose proof (wmono_refl ssegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + n)]%Z m) as MU.
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash HD. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VSNPRINTF.
    carve_frame 304%nat ST.
    do 12 zs.
    zs. zs. brf K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. clear -HN. lia. }
    zs. zs. zs. zs. zs.
    (* [comment removed for export] *)
    replace (n <? n + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
    change (Z.land (-1) 18446744073709551615) with 18446744073709551615.
    replace (Z.land 18446744073709551615 (n + -1)) with (n + -1)
      by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zs. zs. zs. zs. zs.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -304)%Z (CB 232 ?j :: _) |- _ => rename H into FRv; set (j0 := j) in FRv; clearbody j0 end.
    match type of FRv with rw_cells _ _ _ [_; _; _; CB 8 ?j; _; _; _; _; _; _] => set (j8 := j) in FRv; clearbody j8 end.
    apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in FRv. destruct FRv as [FZ FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr FRv (bv_unsigned sp + -72)%Z.
    (* [comment removed for export] *)
    zs. eapply evt_cut.
    { eapply memset_callZ; [ cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact FZ | assumption | lia | lia | lia | lia ]. }
    cbv beta. intros ms' PO. unfold memset_postZ in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m2 & -> & MUc & WMc & MI2 & FZ').
    clear FZ.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    (* [comment removed for export] *)
    pose proof (rw_cells_recast _ _ _ zfile_cells FZ' ltac:(cbn [cells_wf cell_wf zfile_cells]; repeat split) ltac:(vm_compute; reflexivity)) as FC. clear FZ'.
    unfold zfile_cells in FC.
    do 10 zs.
    c4_eqv FC 20%nat (Z_to_bv 64 4294967295). c4_eqv FC 21%nat (Z_to_bv 64 4294967295).
    (* [comment removed for export] *)
    unfold hide in HD.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
    pose proof (u8arr_store_ok ssegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJD; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_zero. replace (Z_to_bv 64 D : word) with (wa (D + 0)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write ssegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJD; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJD in DST. clear DA2.
    zs. zs. zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app ssegs _ _ [_;_] _)) in FRv. destruct FRv as [CKC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr FRv (bv_unsigned sp + -56)%Z. readdr CKC (bv_unsigned sp + -304 + 232)%Z.
    unfold hide in BY, VAA, AOK, BYm, VAAm.
    assert (BY2 : bytes_at ssegs m2 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BYm | exact MU | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO HD; lia]. }
    assert (VAA2 : va_area m2 VA slots).
    { unfold va_area in *. eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA HD LO; lia]. }
    assert (AOK2 : args_ok (bv_unsigned sp + -304 - 352) 600 D (Z.of_nat (Z.to_nat n)) m2 lo (bv_unsigned sp) (bv_unsigned sp + -304 - 368) slots args).
    { replace (bv_unsigned sp + -304 - 352) with (bv_unsigned sp - 656) by lia. replace (bv_unsigned sp + -304 - 368) with (bv_unsigned sp - 672) by lia.
      replace (Z.of_nat (Z.to_nat n)) with n by lia.
      eapply args_ok_vf; [exact AOK | lia | exact MU |]. constructor; [cbn [fst snd]; left; lia|]. constructor; [cbn [fst snd]; right; right; lia | constructor]. }
    clear BY VAA AOK.
    replace (bv_unsigned sp + -72) with (bv_unsigned sp + -304 + 232) in FC by lia.
    replace (n + -1) with (n - 1) in CKC by lia.
    try replace (Z.land 18446744073709551615 (n - 1)) with (n - 1) in CKC
      by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    change (Z_to_bv 64 132664) with (Z_to_bv 64 SN_WRITE) in FC.
    eapply evt_cut.
    { eapply (vfprintf_sn_spec _ _ gp tp _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 F fc D (n - 1) (Z.to_nat n) A VA (bv_unsigned sp) lo (bv_unsigned sp + -49)
                fmtz slots args ps r canary) with (Fp := bv_unsigned sp + -304);
        rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, SN_FS, zlength;
        fastfirst (first [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact FRM | reflexivity | eassumption
              | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2]
              | clear -HN LO GLO QHI HA HVA HD SPHI; lia
              | match goal with |- ?g => idtac "VF-PREM:" g end; match type of CKC with ?t => idtac "CKC:" t end; match type of DST with ?t => idtac "DST:" t end; fail ]). }
    cbv beta. intros ms' PO.
    unfold vfprintf_sn_post in PO. cbv zeta in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & fj & jd' & m3 & -> & MUc & WMc & MI3 & ST3 & SSP3 & DST3 & FJ3).
    clear FC CKC DST BY2 VAA2 AOK2.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m3 MUc WMc; clear MUc WMc; try clear MI2 end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 7 zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FALL : rw_cells ssegs mm (bv_unsigned sp + -304) ([CB 248 fj] ++ [CB 8 j8; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
      [ apply (proj2 (rw_cells_app ssegs _ _ _ _)); split; [exact FJ3|]; cbn [cells_size csize Nat.add]; eapply rwc_eqA; [exact FRv | lia]
      | clear FJ3 FRv ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. clear -SPHI. intros; lia. }
    split; [exact WM|]. split; [exact MI3|].
    split; [exact ST3|].
    split; [split; [exact SSP1 | exact SSP2]|].
    replace (Z.to_nat (n - 1)) with (Z.to_nat (n - 1)) in DST3 by reflexivity. exact DST3.
  Qed.
  End Sz3.
  Theorem vsnprintf_spec : ltac:(let t := eval cbv delta [vsnprintf_spec__stmt] in vsnprintf_spec__stmt in exact t).
  Proof using GLO HA HD HF HN HVA LO P1 PIECES QHI. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd. ltac2:(SecDiet.SzSec.closeP 'vsnprintf_spec__body "vvvvvvvvvvvvvvvvv"). Qed.
End Vsnprintf.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.FP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_printf_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_fwritex_sn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.Printf_snsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_vfprintf_sn.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Definition VSNPRINTF : Z := 0x20d2c.
Definition VSN_FRAME : Z := 304.
Definition VSN_DEPTH : Z := 5856.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs', rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells usegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.
Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells usegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells usegs m A (pre ++ C4 v' :: post).
Proof.
  intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 [_ W2]]. apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac c4_eqv H k v' :=
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
    lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
      let H' := fresh in
      pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
      specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
    end end.

(* [comment removed for export] *)
Definition zfile_cells : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0);
   CB 72 (repeat (Z_to_bv 8 0) 72)].

Definition vsnprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D n : Z) (out : list Z) (r lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jd' : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + n)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells usegs m' D [CB (Z.to_nat n) (zb (firstn (Z.to_nat (n - 1)) out) ++ Z_to_bv 8 0 :: jd')].

Section Vsnprintf.
  Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D n A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Let q := bv_unsigned sp.
  Hypothesis HN : 1 <= n < 2^31.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis LO : lo <= q - VSN_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis QHI : q <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 77824.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^64.
  Hypothesis HD : 0 < D /\ D + n <= 2^63 /\ (D + n <= 0x10000 \/ 0x56000 <= D)
                  /\ (D + n <= lo \/ VA + 8 * zlength slots <= D \/ (q <= D /\ D + n <= VA)).

  Definition vsnprintf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (jd : list byte),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells usegs m D [CB (Z.to_nat n) jd] ->
    bytes_at usegs m A (zb fmtz) ->
    va_area m VA slots -> args_ok (q - 656) SN_FS D n m lo q (q - 672) slots args ->
    stk usegs m lo q -> ssp_cells m canary -> mem_inv usegs m -> fany fc ->
    evt usegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n (concat ps) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VSNPRINTF) fc None m (seg_rom usegs)).
  Section Sz3.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd : ltac2:(SecDiet.SzSec.tyM 'vsnprintf_spec__stmt "vvvvvvvvvvvvvvvvv" @t0).
  Lemma vsnprintf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vsnprintf_spec__stmt "vvvvvvvvvvvvvvvvv").
  Proof using GLO HA HD HF HN HVA LO P1 PIECES QHI. pin_using (fun (GLO HA HD HF HN HVA LO P1 PIECES QHI : unit) => tt).
 intros -> -> -> -> DST BY VAA AOK ST SSP MI FRM.
    unfold VSN_DEPTH, GLOBALS_TOP, SN_FS in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (rw_CB_length _ _ _ _ DST) as LJD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, HD, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (DSEP : D + n <= lo \/ bv_unsigned sp <= D) by (clear -HD HVA NNs; lia).
    assert (DHI : 0 < D /\ D + n <= 2^63) by (clear -HD; lia).
    pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + n)]%Z m) as MU.
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash HD. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VSNPRINTF.
    carve_frame 304%nat ST.
    do 12 zs.
    zs. zs. brf K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. clear -HN. lia. }
    zs. zs. zs. zs. zs.
    (* [comment removed for export] *)
    replace (n <? n + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
    change (Z.land (-1) 18446744073709551615) with 18446744073709551615.
    replace (Z.land 18446744073709551615 (n + -1)) with (n + -1)
      by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zs. zs. zs. zs. zs.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -304)%Z (CB 232 ?j :: _) |- _ => rename H into FRv; set (j0 := j) in FRv; clearbody j0 end.
    match type of FRv with rw_cells _ _ _ [_; _; _; CB 8 ?j; _; _; _; _; _; _] => set (j8 := j) in FRv; clearbody j8 end.
    apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRv. destruct FRv as [FZ FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr FRv (bv_unsigned sp + -72)%Z.
    (* [comment removed for export] *)
    zs. eapply evt_cut.
    { eapply memset_callZ; [ cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact FZ | assumption | lia | lia | lia | lia ]. }
    cbv beta. intros ms' PO. unfold memset_postZ in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m2 & -> & MUc & WMc & MI2 & FZ').
    clear FZ.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    (* [comment removed for export] *)
    pose proof (rw_cells_recast _ _ _ zfile_cells FZ' ltac:(cbn [cells_wf cell_wf zfile_cells]; repeat split) ltac:(vm_compute; reflexivity)) as FC. clear FZ'.
    unfold zfile_cells in FC.
    do 10 zs.
    c4_eqv FC 20%nat (Z_to_bv 64 4294967295). c4_eqv FC 21%nat (Z_to_bv 64 4294967295).
    (* [comment removed for export] *)
    unfold hide in HD.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
    pose proof (u8arr_store_ok usegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJD; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_zero. replace (Z_to_bv 64 D : word) with (wa (D + 0)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write usegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJD; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJD in DST. clear DA2.
    zs. zs. zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app usegs _ _ [_;_] _)) in FRv. destruct FRv as [CKC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr FRv (bv_unsigned sp + -56)%Z. readdr CKC (bv_unsigned sp + -304 + 232)%Z.
    unfold hide in BY, VAA, AOK, BYm, VAAm.
    assert (BY2 : bytes_at usegs m2 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BYm | exact MU | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO HD; lia]. }
    assert (VAA2 : va_area m2 VA slots).
    { unfold va_area in *. eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA HD LO; lia]. }
    assert (AOK2 : args_ok (bv_unsigned sp + -304 - 352) 600 D (Z.of_nat (Z.to_nat n)) m2 lo (bv_unsigned sp) (bv_unsigned sp + -304 - 368) slots args).
    { replace (bv_unsigned sp + -304 - 352) with (bv_unsigned sp - 656) by lia. replace (bv_unsigned sp + -304 - 368) with (bv_unsigned sp - 672) by lia.
      replace (Z.of_nat (Z.to_nat n)) with n by lia.
      eapply args_ok_vf; [exact AOK | lia | exact MU |]. constructor; [cbn [fst snd]; left; lia|]. constructor; [cbn [fst snd]; right; right; lia | constructor]. }
    clear BY VAA AOK.
    replace (bv_unsigned sp + -72) with (bv_unsigned sp + -304 + 232) in FC by lia.
    replace (n + -1) with (n - 1) in CKC by lia.
    try replace (Z.land 18446744073709551615 (n - 1)) with (n - 1) in CKC
      by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    change (Z_to_bv 64 134648) with (Z_to_bv 64 SN_WRITE) in FC.
    eapply evt_cut.
    { eapply (vfprintf_sn_spec _ _ gp tp _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 F fc D (n - 1) (Z.to_nat n) A VA (bv_unsigned sp) lo (bv_unsigned sp + -49)
                fmtz slots args ps r canary) with (Fp := bv_unsigned sp + -304);
        rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, SN_FS, zlength;
        fastfirst (first [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact FRM | reflexivity | eassumption
              | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2]
              | clear -HN LO GLO QHI HA HVA HD SPHI; lia
              | match goal with |- ?g => idtac "VF-PREM:" g end; match type of CKC with ?t => idtac "CKC:" t end; match type of DST with ?t => idtac "DST:" t end; fail ]). }
    cbv beta. intros ms' PO.
    unfold vfprintf_sn_post in PO. cbv zeta in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & fj & jd' & m3 & -> & MUc & WMc & MI3 & ST3 & SSP3 & DST3 & FJ3).
    clear FC CKC DST BY2 VAA2 AOK2.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc; try clear MI2 end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 7 zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FALL : rw_cells usegs mm (bv_unsigned sp + -304) ([CB 248 fj] ++ [CB 8 j8; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
      [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FJ3|]; cbn [cells_size csize Nat.add]; eapply rwc_eqA; [exact FRv | lia]
      | clear FJ3 FRv ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. clear -SPHI. intros; lia. }
    split; [exact WM|]. split; [exact MI3|].
    split; [exact ST3|].
    split; [split; [exact SSP1 | exact SSP2]|].
    replace (Z.to_nat (n - 1)) with (Z.to_nat (n - 1)) in DST3 by reflexivity. exact DST3.
  Qed.
  End Sz3.
  Theorem vsnprintf_spec : ltac:(let t := eval cbv delta [vsnprintf_spec__stmt] in vsnprintf_spec__stmt in exact t).
  Proof using GLO HA HD HF HN HVA LO P1 PIECES QHI. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd. ltac2:(SecDiet.SzSec.closeP 'vsnprintf_spec__body "vvvvvvvvvvvvvvvvv"). Qed.
End Vsnprintf.
End TwB.
End F_vsnprintf.

(* [comment removed for export] *)
Module Stdio_glue_sn.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr Bytes ITree Nodes Decode SysStep FP StoreFast ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sn_write__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Vsn_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_printf_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_fwritex_sn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.Printf_snsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_vfprintf_sn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_vsnprintf.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma str_bytes : forall fs,
  map (fun c => Z_to_bv 8 (Z.of_nat (nat_of_ascii c))) (list_ascii_of_string fs) ++ [Z_to_bv 8 0] = zb (str fs ++ [0]).
Proof using Type. pin_using tt.
  intros fs. unfold zb, str. rewrite map_app, map_map. cbn [map]. f_equal.
  apply map_ext. intros a. f_equal. unfold nat_of_ascii. rewrite N_nat_Z. reflexivity.
Qed.

Lemma str_range : forall fs, Forall (fun c => 0 <= c < 256) (str fs ++ [0]).
Proof using Type. pin_using tt.
  intros fs. apply Forall_app. split; [| constructor; [lia | constructor]].
  unfold str. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (a & <- & _).
  pose proof (N_ascii_bounded a). lia.
Qed.

Lemma length_list_ascii_of_string : forall s, length (list_ascii_of_string s) = String.length s.
Proof using Type. pin_using tt. induction s as [|c s IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma str_length : forall fs, zlength (str fs) = Z.of_nat (String.length fs).
Proof using Type. pin_using tt. intros fs. unfold zlength, str. rewrite length_map, length_list_ascii_of_string. reflexivity. Qed.

(* [comment removed for export] *)
Lemma items_ok_eq : forall its args, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.items_ok its args = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok its args.
Proof using Type. pin_using tt.
  induction its as [|[l|c|b] its IH]; intros args; cbn; [reflexivity| | |reflexivity].
  - rewrite IH. reflexivity.
  - destruct args as [|a args]; [reflexivity|]. rewrite IH. destruct c, a; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma udigits_aux_length : forall f b n acc, (length (udigits_aux f b n acc) <= f + length acc)%nat.
Proof using Type. pin_using tt.
  induction f as [|f IH]; intros b n acc; cbn; [lia|].
  destruct (n <=? 0); [cbn; lia|]. eapply Nat.le_trans; [apply IH|]. cbn. lia.
Qed.
Lemma udigits_zlength : forall b n, zlength (udigits b n) <= 64.
Proof using Type. pin_using tt.
  intros. unfold zlength, udigits. pose proof (udigits_aux_length 64 b n []) as L.
  remember (udigits_aux 64 b n []) as d eqn:E. clear E. cbn [length Nat.add] in L. lia.
Qed.

Lemma int_pieces_bound : forall neg d, zlength d <= 64 -> zlength (List.concat (Fmt.int_pieces neg d)) <= 65.
Proof using Type. pin_using tt. intros neg d Hd. rewrite int_pieces_len. destruct neg; lia. Qed.

Definition farg_len (a : farg) : Z := match a with AStr s => zlength s | AInt _ => 0 end.

Definition conv_len_bound__stmt : Prop := forall c a, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.conv_ok c a = true -> conv_len c a <= 80 + farg_len a.
Section Sz9.
Variables c a : ltac2:(SecDiet.SzSec.tyM 'conv_len_bound__stmt "vv" @c).
Lemma conv_len_bound__body : ltac2:(SecDiet.SzSec.bodyP 'conv_len_bound__stmt "vv").
Proof using Type. pin_using tt.
  intros OK.
 unfold conv_len, farg_len. destruct c; destruct a as [v|sv]; try discriminate OK; cbn [Fmt.conv_pieces].
  - pose proof (int_pieces_bound (s32 v <? 0) (dec_udigits (Z.abs (s32 v))) (udigits_zlength _ _)). lia.
  - pose proof (int_pieces_bound false (dec_udigits (u32 v)) (udigits_zlength _ _)). lia.
  - pose proof (udigits_zlength 16 (u32 v)) as L. unfold hex_udigits.
    remember (udigits 16 (u32 v)) as d eqn:Ed. clear Ed. pose proof (zlength_nonneg d) as L0.
    cbn [List.concat]. rewrite concat_app, !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app. change (zlength (@nil Z)) with 0.
    assert (A1 : zlength (List.concat (if zlength d + (if u32 v =? 0 then 1 else 0) <? 8
                                        then [zeros (8 - (zlength d + (if u32 v =? 0 then 1 else 0)))] else [])) <= 8).
    { destruct (Z.ltb_spec (zlength d + (if u32 v =? 0 then 1 else 0)) 8); cbn [List.concat].
      - rewrite app_nil_r. unfold zeros. rewrite zlength_zrepeat; [| destruct (u32 v =? 0); lia]. destruct (u32 v =? 0); lia.
      - change (zlength (@nil Z)) with 0. lia. }
    assert (A2 : zlength (List.concat match d with [] => [[48]; []] | _ :: _ => [d] end) <= 64).
    { destruct d; cbn [List.concat]; rewrite ?app_nil_r; [change (zlength [48]) with 1; lia | exact L]. }
    lia.
  - cbn [List.concat]. rewrite app_nil_r. cbn [app]. lia.
  - pose proof (int_pieces_bound false (dec_udigits (u64 v)) (udigits_zlength _ _)). lia.
Qed.
End Sz9.
Lemma conv_len_bound : ltac:(let t := eval cbv delta [conv_len_bound__stmt] in conv_len_bound__stmt in exact t).
Proof using Type. intros c a. ltac2:(SecDiet.SzSec.closeP 'conv_len_bound__body "vv"). Qed.

Fixpoint fargs_len (args : list farg) : Z :=
  match args with [] => 0 | a :: args' => 80 + farg_len a + fargs_len args' end.
Lemma fargs_len_nonneg : forall args, 0 <= fargs_len args.
Proof using Type. pin_using tt. induction args as [|a args IH]; cbn; [lia|]. destruct a as [z|cs]; cbn; [| pose proof (zlength_nonneg cs)]; lia. Qed.

(* [comment removed for export] *)
Lemma fmt_output_bound_aux : forall fuel s args,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true ->
  zlength (fmt_output (parse_fmt_aux fuel s) args) <= zlength s + fargs_len args.
Proof using Type. pin_using tt.
  induction fuel as [|f IH]; intros s args Hlen OK.
  - destruct s as [|c s0]; [| cbn in Hlen; lia]. cbn in OK. destruct args; [| discriminate]. cbn. lia.
  - destruct s as [|c s0].
    { cbn in OK. destruct args; [| discriminate]. cbn. lia. }
    cbn in Hlen. destruct (Z.eqb_spec c 37) as [E37|N37].
    + subst c. rewrite parse_pct_shape in *.
      destruct (parse_conv s0) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. destruct args as [|a args']; [discriminate|]. apply andb_prop in OK as [OKc OK].
      unfold fmt_output. cbn [fmt_pieces hd tl]. rewrite zlength_concat_cons, zlength_concat_app. change (zlength (@nil Z)) with 0.
      fold (fmt_output (parse_fmt_aux f r') args'). fold (conv_len cv a).
      pose proof (conv_len_bound cv a OKc) as CB.
      assert (LR : (List.length r' < S (List.length s0))%nat).
      { pose proof (parse_conv_cases _ _ _ PC) as SH. destruct cv;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; cbn [List.length]; lia. }
      pose proof (IH r' args' ltac:(lia) OK) as IHr.
      cbn [fargs_len]. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
    + rewrite (parse_lit_shape f c s0 N37) in *.
      destruct (take_lit (c :: s0)) as [l r] eqn:TL. destruct (take_lit_spec _ _ _ TL) as (E1 & N1 & R1).
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. apply andb_prop in OK as [OKl OK].
      unfold fmt_output. cbn [fmt_pieces]. rewrite zlength_concat_cons. fold (fmt_output (parse_fmt_aux f r) args).
      pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
      assert (Hl : (1 <= List.length l)%nat).
      { destruct l as [|c' l0]; [| cbn; lia]. exfalso. cbn in E1. destruct R1 as [->|[r'' ->]]; [discriminate E1|]. injection E1 as E _. exact (N37 E). }
      pose proof (IH r args ltac:(lia) OK) as IHr. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
Qed.

Lemma fmt_output_bound : forall fs args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> zlength (fmt_output (fmt fs) args) <= zlength (str fs) + fargs_len args.
Proof using Type. pin_using tt. intros fs args OK. unfold fmt, parse_fmt in *. apply fmt_output_bound_aux; [lia | exact OK]. Qed.

(* [comment removed for export] *)
Lemma cells_bytes_C8 : forall ws, cells_bytes (map C8 ws) = u64s ws.
Proof using Type. pin_using tt. induction ws as [|w ws IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma cells_size_map_C8 : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof using Type. pin_using tt. induction ws as [|w ws IH]; cbn; [reflexivity|]. rewrite IH. lia. Qed.
Lemma va_area_of_cells : forall m A ws, rw_cells ssegs m A (map C8 ws) -> va_area m A ws.
Proof using Type. pin_using tt. intros m A ws H. unfold va_area. rewrite <- cells_bytes_C8. apply rw_cells_bytes_at. exact H. Qed.

(* [comment removed for export] *)
Lemma mod32_of_mod64 : forall z, (z mod 2^64) mod 2^32 = z mod 2^32.
Proof using Type. pin_using tt. intros z. apply Z.mod_mod_divide. exists (2^32). reflexivity. Qed.
Lemma s32_facts : forall z, -2^31 <= s32 z < 2^31 /\ bv_unsigned (Z_to_bv 64 z : word) mod 2^32 = s32 z mod 2^32.
Proof using Type. pin_using tt.
  intros z. unfold s32. rewrite unsigned_lit_wrap, mod32_of_mod64.
  split; [Z.div_mod_to_equations; lia|].
  replace ((z + 2^31) mod 2^32 - 2^31) with (z - ((z + 2^31) / 2^32) * 2^32) by (Z.div_mod_to_equations; lia).
  rewrite <- Zminus_mod_idemp_r. rewrite Z_mod_mult. rewrite Z.sub_0_r. reflexivity.
Qed.
Lemma u32_facts : forall z, 0 <= u32 z < 2^32 /\ bv_unsigned (Z_to_bv 64 z : word) mod 2^32 = u32 z.
Proof using Type. pin_using tt. intros z. unfold u32. rewrite unsigned_lit_wrap, mod32_of_mod64. split; [Z.div_mod_to_equations; lia| reflexivity]. Qed.
Lemma u64_facts : forall z, 0 <= u64 z < 2^64 /\ bv_unsigned (Z_to_bv 64 z : word) = u64 z.
Proof using Type. pin_using tt. intros z. unfold u64. rewrite unsigned_lit_wrap. split; [Z.div_mod_to_equations; lia| reflexivity]. Qed.

(* [comment removed for export] *)
Definition pad8 (x : Z) : Z := (- x) mod 8.
Lemma pad8_range : forall x, 0 <= pad8 x < 8.
Proof using Type. pin_using tt. intros. unfold pad8. Z.div_mod_to_equations. lia. Qed.
Lemma pad8_align : forall x b, 0 <= x -> x <= b -> b mod 8 = 0 -> x + pad8 x <= b.
Proof using Type. pin_using tt.
  intros x b Hx Hb Hal. unfold pad8.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod b 8 ltac:(lia)) as E2.
  set (q1 := - x / 8) in *. set (r1 := (- x) mod 8) in *. set (q2 := b / 8) in *. clearbody q1 r1 q2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Glue.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Notation cblk := (@cblock hptr).
  Notation PS := (PState H hptr).

  Definition client_range_facts__stmt : Prop := forall R (s : PS) (CL FB : list cblk) m SP S len,
    GIo K R s CL FB m -> client_range R CL SP S len -> 0 < len -> CEILZ <= SP ->
    0 < S /\ (S + len <= CEILZ \/ SP <= S) /\ S + len <= 2^47
    /\ (S + len <= 0x10000 \/ 0x55000 <= S \/ SP <= S)
    /\ (S + len <= utp R - 200 \/ utp R - 200 + 4096 <= S \/ SP <= S)
    /\ (SP <= S -> S + len <= rc_spmain R).
  Section Sz22.
  Variables R s CL FB m SP S len : ltac2:(SecDiet.SzSec.tyM 'client_range_facts__stmt "vvvvvvvv" @R).
  Lemma client_range_facts__body : ltac2:(SecDiet.SzSec.bodyP 'client_range_facts__stmt "vvvvvvvv").
  Proof using Type. pin_using tt.
    intros G CR LEN HSP0.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    destruct CR as [CR | CR]; unfold rc_lo, rc_spmain in *.
    - destruct (in_block_facts _ _ S BO1 (CR S ltac:(lia))) as (X1 & X2 & X3 & X4).
      destruct (in_block_facts _ _ (S + len - 1) BO1 (CR (S + len - 1) ltac:(lia))) as (Y1 & Y2 & Y3 & Y4).
      split; [lia|]. split; [left; lia|]. split; [lia|].
      split. { destruct (Z_le_gt_dec (S + len) 0x10000); [left; lia|]. destruct (Z_le_gt_dec 0x55000 S); [right; left; lia|]. exfalso.
               destruct (in_block_facts _ _ (Z.max S 0x10000) BO1 (CR (Z.max S 0x10000) ltac:(lia))) as (W1 & W2 & W3 & W4). lia. }
      split. { destruct (Z_le_gt_dec (S + len) (utp R - 200)); [left; lia|]. destruct (Z_le_gt_dec (utp R - 200 + 4096) S); [right; left; lia|]. exfalso.
               destruct (in_block_facts _ _ (Z.max S (utp R - 200)) BO1 (CR (Z.max S (utp R - 200)) ltac:(lia))) as (W1 & W2 & W3 & W4). lia. }
      intros HSP. lia.
    - split; [lia|]. split; [right; lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|]. intros; lia.
  Qed.
  End Sz22.
  Lemma client_range_facts : ltac:(let t := eval cbv delta [client_range_facts__stmt] in client_range_facts__stmt in exact t).
  Proof using Type. intros R s CL FB m SP S len. ltac2:(SecDiet.SzSec.closeP 'client_range_facts__body "vvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition spo_pure__stmt : Prop := forall sp tp R (s : PS) CL FB lo budget m,
    std_pre_o K sp tp R s CL FB lo budget m ->
    GIo K R s CL FB m /\ stk ssegs m lo (bv_unsigned sp) /\ mem_inv ssegs m /\ ssp_cells m (rc_canary R)
    /\ rc_lo R <= lo /\ lo + budget <= bv_unsigned sp /\ bv_unsigned sp <= rc_spmain R
    /\ CEILZ <= rc_lo R /\ rc_spmain R + 48 <= 2^47 /\ tls_block_ok (utp R - 200).
  Section Sz23.
  Variables sp tp R s CL FB lo budget m : ltac2:(SecDiet.SzSec.tyM 'spo_pure__stmt "vvvvvvvvv" @sp).
  Lemma spo_pure__body : ltac2:(SecDiet.SzSec.bodyP 'spo_pure__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros (G & ST & LOR & LOB & SPM & MI & Etp & AL).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    split; [exact G|]. split; [exact ST|]. split; [exact MI|].
    split. { destruct CLI as (_ & G1 & G2 & _). split; [exact G1 | exact G2]. }
    split; [exact LOR|]. split; [exact LOB|]. split; [exact SPM|].
    unfold rc_lo, rc_spmain in *. split; [lia|]. split; [lia|]. exact TB.
  Qed.
  End Sz23.
  Lemma spo_pure : ltac:(let t := eval cbv delta [spo_pure__stmt] in spo_pure__stmt in exact t).
  Proof using Type. intros sp tp R s CL FB lo budget m. ltac2:(SecDiet.SzSec.closeP 'spo_pure__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma zb_unsigned : forall (bs : list byte), zb (map bv_unsigned bs) = bs.
  Proof using Type. pin_using tt. induction bs as [|b bs IH]; cbn; [reflexivity|]. unfold zb in *. cbn. rewrite definitions.Z_to_bv_bv_unsigned, IH. reflexivity. Qed.

  Definition arg_ok_str__stmt : Prop := forall R (s : PS) CL FB m SP SPa D dn lo Fp FS ap (w : word) cs,
    GIo K R s CL FB m -> CEILZ <= lo -> lo <= SPa -> SPa <= SP -> lo <= Fp -> Fp + FS <= SP -> lo <= ap -> ap + 8 <= SP ->
    farg_word R CL SP D dn m (AStr cs) w ->
    arg_ok Fp FS D dn m lo SPa ap w (PA_s cs).
  Section Sz25.
  Variables R s CL FB m SP SPa D dn lo Fp FS ap w cs : ltac2:(SecDiet.SzSec.tyM 'arg_ok_str__stmt "vvvvvvvvvvvvvvv" @R).
  Lemma arg_ok_str__body : ltac2:(SecDiet.SzSec.bodyP 'arg_ok_str__stmt "vvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G CLO LSP SPA LF FSP LAP APSP FW.
    cbn in FW. destruct FW as (P & bs & slack & -> & BY & NZ & -> & LB & PAD & DD & LOC).
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof (pad8_range (P + Z.of_nat (length bs) + 1)) as PR. unfold pad8 in PR.
    set (pd := (- (P + Z.of_nat (length bs) + 1)) mod 8) in *.
    assert (EP : bv_unsigned (Z_to_bv 64 P : word) = P) by (apply unsigned_lit; lia).
    cbn [arg_ok]. rewrite EP. exists (firstn (Z.to_nat pd) slack).
    assert (LS : length (firstn (Z.to_nat pd) slack) = Z.to_nat pd) by (rewrite length_firstn; lia).
    unfold zlength. rewrite length_map, LS.
    split. { rewrite zb_unsigned. rewrite <- (firstn_skipn (Z.to_nat pd) slack) in BY.
             change (bs ++ Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack ++ skipn (Z.to_nat pd) slack)
               with (bs ++ (Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack) ++ skipn (Z.to_nat pd) slack) in BY.
             rewrite app_assoc in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
    split. { apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
             pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
             destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE]; [|lia]. exfalso. apply NZ.
             replace (Z_to_bv 8 0) with b; [exact Hb|]. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b), E. reflexivity. }
    split; [lia|].
    (* [comment removed for export] *)
    pose proof (proj2 (GIo_tls K _ _ _ _ _ G)) as (TBal & TB0 & TBhi & TBimg).
    assert (LOCF : 0 < P /\ (P + Z.of_nat (length bs) + 1 + pd <= lo \/ SP <= P) /\ P + Z.of_nat (length bs) <= 2^47).   (* [comment removed for export] *)
    { destruct LOC as [CR | [RO | TLS]].
      - destruct (client_range_facts R s CL FB m SP P (Z.of_nat (length bs) + 1) G CR ltac:(lia) ltac:(lia)) as (P0 & PC & P47 & _).
        split; [exact P0|]. split; [|lia]. destruct PC as [PC | PC]; [left | right; exact PC].
        assert (C8 : CEILZ mod 8 = 0).   (* [comment removed for export] *)
        { ceil_facts. replace alloc_ceiling with (512 * (alloc_ceiling / 4096) * 8) by (pose proof (Z_div_mod_eq_full alloc_ceiling 4096); lia). apply Z_mod_mult. }
        pose proof (pad8_align (P + Z.of_nat (length bs) + 1) CEILZ ltac:(lia) ltac:(lia) C8). subst pd. unfold pad8 in *. lia.
      - split; [lia|]. split; [|lia]. left. pose proof (pad8_align (P + Z.of_nat (length bs) + 1) 0x13000 ltac:(lia) ltac:(lia) eq_refl). subst pd. unfold pad8 in *. lia.
      - split; [lia|]. split; [|lia]. left. lia. }
    destruct LOCF as (P0 & SEP & P47).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
  Qed.
  End Sz25.
  Lemma arg_ok_str : ltac:(let t := eval cbv delta [arg_ok_str__stmt] in arg_ok_str__stmt in exact t).
  Proof using Type. intros R s CL FB m SP SPa D dn lo Fp FS ap w cs. ltac2:(SecDiet.SzSec.closeP 'arg_ok_str__body "vvvvvvvvvvvvvvv"). Qed.

  Definition args_ok_of_fargs__stmt : Prop := forall R (s : PS) CL FB m SP SPa D dn lo Fp FS ap,
    GIo K R s CL FB m -> CEILZ <= lo -> lo <= SPa -> SPa <= SP -> lo <= Fp -> Fp + FS <= SP -> lo <= ap -> ap + 8 <= SP ->
    forall its args ws, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok its args = true ->
    Forall2 (farg_word R CL SP D dn m) args ws ->
    args_ok Fp FS D dn m lo SPa ap ws (to_pargs its args).
  Section Sz26.
  Variables R s CL FB m SP SPa D dn lo Fp FS ap : ltac2:(SecDiet.SzSec.tyM 'args_ok_of_fargs__stmt "vvvvvvvvvvvvv" @R).
  Lemma args_ok_of_fargs__body : ltac2:(SecDiet.SzSec.bodyP 'args_ok_of_fargs__stmt "vvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G CLO LSP SPA LF FSP LAP APSP.
    induction its as [|[l|c|b] its IH]; intros args ws OK FW.
    - cbn in OK. destruct args; [|discriminate]. inversion FW; subst. cbn. exact I.
    - cbn in OK |- *. apply andb_prop in OK as [_ OK]. apply IH; assumption.
    - cbn in OK |- *. destruct args as [|a args]; [discriminate|]. apply andb_prop in OK as [OKc OK].
      inversion FW as [|a' w args' ws' FA FW']; subst. cbn [args_ok]. split; [| apply IH; assumption].
      destruct c; destruct a as [v|sv]; try discriminate OKc; cbn [conv_parg].
      + cbn in FA |- *. subst w. exact (s32_facts v).
      + cbn in FA |- *. subst w. exact (u32_facts v).
      + cbn in FA |- *. subst w. exact (u32_facts v).
      + eapply arg_ok_str; eassumption.
      + cbn in FA |- *. subst w. exact (u64_facts v).
    - cbn in OK. discriminate.
  Qed.
  End Sz26.
  Lemma args_ok_of_fargs : ltac:(let t := eval cbv delta [args_ok_of_fargs__stmt] in args_ok_of_fargs__stmt in exact t).
  Proof using Type. intros R s CL FB m SP SPa D dn lo Fp FS ap. ltac2:(SecDiet.SzSec.closeP 'args_ok_of_fargs__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma stdio_stack_big : VSN_DEPTH + 80 <= STDIO_STACK.
  Proof using Type. pin_using tt. unfold VSN_DEPTH, STDIO_STACK. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vsnprintf4_proof__stmt : Prop := vsnprintf_spec4_stmt K.
  Section Sz28.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo DST n FMTA AP fs ws junk : ltac2:(SecDiet.SzSec.tyM 'vsnprintf4_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkvv" @ra).
  Lemma vsnprintf4_proof__body : ltac2:(SecDiet.SzSec.bodyP 'vsnprintf4_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkvv").
  Proof using Type. pin_using tt.
    intros args PRE -> -> -> -> HN FAT FOK LWS L4 FW APC SPAP APHI APD DSTC CR.
    destruct (spo_pure _ _ _ _ _ _ _ _ _ PRE) as (G & ST & MI & SSP & LOR & LOB & SPM & CEILLO & SP47 & TB).
    unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct FAT as (FBY & FLO & FHI).
    unfold fmt_ok in FOK. apply andb_prop in FOK as [IOK FLEN]. rewrite items_ok_eq in IOK. apply Z.ltb_lt in FLEN.
    pose proof (fmt_output_bound fs args IOK) as OB. rewrite str_length in OB.
    assert (FLn : fargs_len args <= Z.of_nat (length args) * (80 + 2^24)).
    { clear -FW. revert ws FW. induction args as [|a args IH]; intros ws FW; [cbn; lia|].
      inversion FW as [|a' w args' ws' FA FW']; subst.
      assert (Ha : farg_len a <= 2^24). { destruct a as [z|cs]; cbn; [lia|]. cbn in FA. destruct FA as (P & bs & slack & _ & _ & _ & -> & LB & _).
                                         unfold zlength. rewrite length_map. lia. }
      specialize (IH ws' FW'). cbn [fargs_len length]. lia. }
    assert (FL4 : fargs_len args <= 4 * (80 + 2^24)) by (clear -FLn L4; pose proof (fargs_len_nonneg args); nia).
    destruct (client_range_facts R s CL FB m _ DST n G CR ltac:(lia) ltac:(lia)) as (D0 & DC & D47 & DIMG & DTLS & DSPM).
    (* [comment removed for export] *)
    destruct (stk_split _ _ _ (bv_unsigned sp - 65536) _ ST ltac:(lia)) as [ST1 ST2].
    eapply evt_mono.
    { eapply (vsnprintf_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST n FMTA AP (bv_unsigned sp - 65536)
                (str fs ++ [0]) ws (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args) (zlength (fmt_output (fmt fs) args)) (rc_canary R))
        with (jd := junk).
      - exact HN.
      - apply str_range.
      - apply (fmt_pass1 fs args IOK). rewrite str_length. unfold INT_MAX. lia.
      - apply fmt_bridge; [exact IOK|]. unfold INT_MAX. lia.
      - unfold VSN_DEPTH. lia.
      - unfold GLOBALS_TOP. lia.
      - lia.
      - rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app, str_length. change (zlength [0]) with 1. lia.
      - pose proof (rw_cells_bound _ _ _ _ APC) as AB. rewrite cells_size_map_C8 in AB. unfold zlength. lia.
      - split; [lia|]. split; [lia|]. split; [lia|].
        destruct DC as [DC|DC]; [left; lia|]. right. destruct APD as [APD|APD]; [left; unfold zlength; lia | right; lia].
      - reflexivity. - reflexivity. - reflexivity. - reflexivity.
      - exact DSTC.
      - rewrite <- str_bytes. exact FBY.
      - apply va_area_of_cells. exact APC.
      - eapply (args_ok_of_fargs R s CL FB m (bv_unsigned sp) (bv_unsigned sp) DST n (bv_unsigned sp - 65536) (bv_unsigned sp - 656) SN_FS (bv_unsigned sp - 672));
          [exact G | lia | lia | lia | lia | unfold SN_FS; lia | lia | lia | exact IOK | exact FW].
      - exact ST2.
      - exact SSP.
      - exact MI.
      - exact I. }
    cbv beta. intros ms' PO. unfold vsnprintf_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & jd' & m' & -> & MU & WM & MI' & ST' & SSP' & DST').
    set (out := Fmt.snprintf n fs args) in *.
    change (firstn (Z.to_nat (n - 1)) (List.concat (fmt_pieces (fmt fs) args))) with out in DST'.
    pose proof (rw_CB_length _ _ _ _ DST') as LJ. rewrite length_app, zb_length in LJ. cbn [length] in LJ.
    exists (Z_to_bv 64 (zlength (fmt_output (fmt fs) args))), m', (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')).
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ]. }
    split; [reflexivity|].
    apply (rw_cells_split_CB ssegs _ _ [] (Z.to_nat n) _ [] [length out + 1; Z.to_nat n - length out - 1]%nat) in DST'; [| cbn; lia].
    cbn [mk_CB_cells app] in DST'.
    replace (firstn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')) with (map b8 out ++ [Z_to_bv 8 0]) in DST'.
    2:{ rewrite firstn_app, zb_length, (firstn_all2 (zb out)) by (rewrite zb_length; lia).
        replace (length out + 1 - length out)%nat with 1%nat by lia. reflexivity. }
    rewrite (firstn_all2 (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd'))) in DST' by (rewrite length_skipn, length_app, zb_length; cbn [length]; lia).
    exact DST'.
  Qed.
  End Sz28.
  Theorem vsnprintf4_proof : ltac:(let t := eval cbv delta [vsnprintf4_proof__stmt] in vsnprintf4_proof__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo DST n FMTA AP fs args ws junk. ltac2:(SecDiet.SzSec.closeP 'vsnprintf4_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma args_ok_more : forall Fp FS B BS m lo sp ap ws more pargs,
    args_ok Fp FS B BS m lo sp ap ws pargs -> args_ok Fp FS B BS m lo sp ap (ws ++ more) pargs.
  Proof using Type. pin_using tt.
    intros Fp FS B BS m lo sp ap ws more pargs. revert ws.
    induction pargs as [|a pargs IH]; intros ws AOK; [destruct (ws ++ more); exact I|].
    destruct ws as [|w ws]; [destruct AOK|]. cbn in AOK |- *. destruct AOK as [H1 H2]. split; [exact H1 | apply IH; exact H2].
  Qed.

  Definition snprintf_proof__stmt : Prop := snprintf_spec_stmt K.
  Section Sz30.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo DST n FMTA fs junk : ltac2:(SecDiet.SzSec.tyM 'snprintf_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv" @ra).
  Lemma snprintf_proof__body : ltac2:(SecDiet.SzSec.bodyP 'snprintf_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv").
  Proof using Type. pin_using tt.
    intros args PRE -> -> -> HN FAT FOK L3 FW DSTC CR.
    destruct (spo_pure _ _ _ _ _ _ _ _ _ PRE) as (G & ST & MI & SSP & LOR & LOB & SPM & CEILLO & SP47 & TB).
    unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct FAT as (FBY & FLO & FHI).
    unfold fmt_ok in FOK. apply andb_prop in FOK as [IOK FLEN]. rewrite items_ok_eq in IOK. apply Z.ltb_lt in FLEN.
    pose proof (fmt_output_bound fs args IOK) as OB. rewrite str_length in OB.
    assert (FLn : fargs_len args <= Z.of_nat (length args) * (80 + 2^24)).
    { clear -FW. remember (firstn (length args) [a3; a4; a5]) as ws eqn:Ews. clear Ews. revert ws FW. induction args as [|a args IH]; intros ws FW; [cbn; lia|].
      inversion FW as [|a' w args' ws' FA FW']; subst.
      assert (Ha : farg_len a <= 2^24). { destruct a as [z|cs]; cbn; [lia|]. cbn in FA. destruct FA as (P & bs & slack & _ & _ & _ & -> & LB & _).
                                         unfold zlength. rewrite length_map. lia. }
      specialize (IH ws' FW'). cbn [fargs_len length]. lia. }
    assert (FL4 : fargs_len args <= 3 * (80 + 2^24)) by (clear -FLn L3; pose proof (fargs_len_nonneg args); nia).
    destruct (client_range_facts R s CL FB m _ DST n G CR ltac:(lia) ltac:(lia)) as (D0 & DC & D47 & DIMG & DTLS & DSPM).
    pose proof (rw_CB_length _ _ _ _ DSTC) as LJD.
    (* [comment removed for export] *)
    pose proof (args_ok_of_fargs R s CL FB m (bv_unsigned sp) (bv_unsigned sp) DST n (bv_unsigned sp - 65536)
                  (bv_unsigned sp - 80 - 656) SN_FS (bv_unsigned sp - 80 - 672) G ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(unfold SN_FS; lia) ltac:(lia) ltac:(lia) (fmt fs) args _ IOK FW) as AOK0.
    apply (args_ok_more _ _ _ _ _ _ _ _ _ (skipn (length args) [a3; a4; a5] ++ [a6; a7])) in AOK0.
    assert (EWS : firstn (length args) [a3; a4; a5] ++ (skipn (length args) [a3; a4; a5] ++ [a6; a7]) = [a3; a4; a5; a6; a7]).
    { rewrite app_assoc, firstn_skipn. reflexivity. }
    rewrite EWS in AOK0. clear EWS.
    assert (GLO__ : 0x55000 <= lo) by (unfold rc_lo in *; lia).   (* [comment removed for export] *)
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (wmono_refl ssegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 65536, bv_unsigned sp)]%Z m) as MUp.
    pose proof (munch_refl [(bv_unsigned sp - 65536, bv_unsigned sp); (DST, DST + n)]%Z m) as MU.
    stash FBY. stash DSTC. stash AOK0. stash DC. stash DIMG. stash DTLS.
    destruct (stk_split _ _ _ (bv_unsigned sp - 65536) _ ST ltac:(lia)) as [ST1 ST2]. clear ST. rename ST2 into ST.
    unfold SNPRINTF_ENTRY.
    carve_frame 80%nat ST.
    do 15 zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    match goal with X : rw_cells _ _ (bv_unsigned sp + -80)%Z (_ :: _) |- _ => rename X into FRv end.
    pose proof FRv as FRc.
    apply (proj1 (rw_cells_app ssegs _ _ [_;_;_;_;_] _)) in FRc. destruct FRc as [FRlo VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -80 + Z.of_nat 40) with (bv_unsigned sp + -40) in VAc by lia. clear FRlo.
    unfold hide in FBY, DSTC, AOK0, DC, DIMG, DTLS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (BY1 : bytes_at ssegs mm FMTA (zb (str fs ++ [0])))
        by (rewrite <- str_bytes; eapply bytes_at_transport; [exact FBY | exact MUp | cbn [disjoint_from]; rewrite length_app, length_map, length_list_ascii_of_string; cbn [length]; lia]);
      assert (DST1 : rw_cells ssegs mm DST [CB (Z.to_nat n) junk])
        by (eapply rw_cells_transport; [exact DSTC | exact MUp | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]);
      assert (AOK1 : args_ok (bv_unsigned sp + -80 - 656) SN_FS DST n mm (bv_unsigned sp - 65536) (bv_unsigned sp + -80) (bv_unsigned sp + -80 - 672)
                        [a3; a4; a5; a6; a7] (to_pargs (fmt fs) args))
        by (replace (bv_unsigned sp + -80 - 656) with (bv_unsigned sp - 80 - 656) by lia;
            replace (bv_unsigned sp + -80 - 672) with (bv_unsigned sp - 80 - 672) by lia;
            eapply args_ok_vf; [exact AOK0 | lia | exact MUp | constructor; [cbn [fst snd]; left; lia | constructor]])
    end.
    clear FBY DSTC AOK0 MUp.
    eapply evt_cut.
    { eapply (vsnprintf_spec _ _ gp tp _ s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST n FMTA (bv_unsigned sp + -40) (bv_unsigned sp - 65536)
                (str fs ++ [0]) [a3; a4; a5; a6; a7] (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args) (zlength (fmt_output (fmt fs) args)) (rc_canary R))
        with (jd := junk);
        rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP, SN_FS, zlength in *.
      - exact HN.
      - apply str_range.
      - apply (fmt_pass1 fs args IOK). rewrite str_length. unfold INT_MAX. lia.
      - apply fmt_bridge; [exact IOK|]. unfold INT_MAX. unfold zlength. lia.
      - lia.
      - lia.
      - lia.
      - rewrite length_app. cbn [length]. pose proof (str_length fs) as SL. unfold zlength in SL. lia.
      - cbn [length]. lia.
      - cbn [length]. clear -D0 D47 DC DIMG LOR LOB CEILLO SPHI. lia.
      - reflexivity. - reflexivity. - reflexivity. - reflexivity.
      - exact DST1.
      - exact BY1.
      - apply va_area_of_cells. exact VAc.
      - exact AOK1.
      - exact ST.
      - unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact I. }
    cbv beta. intros ms' PO. unfold vsnprintf_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & jd' & m' & -> & MUc & WMc & MI' & ST' & SSP' & DST').
    clear VAc DST1 BY1 AOK1.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ssegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP' as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    release_frame FRv ST' (bv_unsigned sp).
    set (out := Fmt.snprintf n fs args) in *.
    change (firstn (Z.to_nat (n - 1)) (List.concat (fmt_pieces (fmt fs) args))) with out in DST'.
    pose proof (rw_CB_length _ _ _ _ DST') as LJ. rewrite length_app, zb_length in LJ. cbn [length] in LJ.
    apply evt_done.
    exists (Z_to_bv 64 (zlength (fmt_output (fmt fs) args))), m', (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')).
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). cbv delta [mkR]. reflexivity. }
    split. { first [exact MU | match goal with |- ?g => idtac "MUGOAL" g end; match type of MU with ?t => idtac "MU:" t end]. }
    split; [exact WM|]. split; [assumption|].
    split. { eapply stk_merge; [ | exact ST' | lia ]. exact ST1. }
    split; [reflexivity|].
    apply (rw_cells_split_CB ssegs _ _ [] (Z.to_nat n) _ [] [length out + 1; Z.to_nat n - length out - 1]%nat) in DST'; [| cbn; lia].
    cbn [mk_CB_cells app] in DST'.
    replace (firstn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')) with (map b8 out ++ [Z_to_bv 8 0]) in DST'.
    2:{ rewrite firstn_app, zb_length, (firstn_all2 (zb out)) by (rewrite zb_length; lia).
        replace (length out + 1 - length out)%nat with 1%nat by lia. reflexivity. }
    rewrite (firstn_all2 (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd'))) in DST' by (rewrite length_skipn, length_app, zb_length; cbn [length]; lia).
    exact DST'.
  Qed.
  End Sz30.
  Theorem snprintf_proof : ltac:(let t := eval cbv delta [snprintf_proof__stmt] in snprintf_proof__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo DST n FMTA fs args junk. ltac2:(SecDiet.SzSec.closeP 'snprintf_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv"). Qed.
End Glue.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.FP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Vsn_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_printf_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.F_fwritex_sn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sn_write__S3.Printf_snsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_vfprintf_sn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_vsnprintf.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma str_bytes : forall fs,
  map (fun c => Z_to_bv 8 (Z.of_nat (nat_of_ascii c))) (list_ascii_of_string fs) ++ [Z_to_bv 8 0] = zb (str fs ++ [0]).
Proof using Type. pin_using tt.
  intros fs. unfold zb, str. rewrite map_app, map_map. cbn [map]. f_equal.
  apply map_ext. intros a. f_equal. unfold nat_of_ascii. rewrite N_nat_Z. reflexivity.
Qed.

Lemma str_range : forall fs, Forall (fun c => 0 <= c < 256) (str fs ++ [0]).
Proof using Type. pin_using tt.
  intros fs. apply Forall_app. split; [| constructor; [lia | constructor]].
  unfold str. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (a & <- & _).
  pose proof (N_ascii_bounded a). lia.
Qed.

Lemma length_list_ascii_of_string : forall s, length (list_ascii_of_string s) = String.length s.
Proof using Type. pin_using tt. induction s as [|c s IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma str_length : forall fs, zlength (str fs) = Z.of_nat (String.length fs).
Proof using Type. pin_using tt. intros fs. unfold zlength, str. rewrite length_map, length_list_ascii_of_string. reflexivity. Qed.

(* [comment removed for export] *)
Lemma items_ok_eq : forall its args, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.items_ok its args = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok its args.
Proof using Type. pin_using tt.
  induction its as [|[l|c|b] its IH]; intros args; cbn; [reflexivity| | |reflexivity].
  - rewrite IH. reflexivity.
  - destruct args as [|a args]; [reflexivity|]. rewrite IH. destruct c, a; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma udigits_aux_length : forall f b n acc, (length (udigits_aux f b n acc) <= f + length acc)%nat.
Proof using Type. pin_using tt.
  induction f as [|f IH]; intros b n acc; cbn; [lia|].
  destruct (n <=? 0); [cbn; lia|]. eapply Nat.le_trans; [apply IH|]. cbn. lia.
Qed.
Lemma udigits_zlength : forall b n, zlength (udigits b n) <= 64.
Proof using Type. pin_using tt.
  intros. unfold zlength, udigits. pose proof (udigits_aux_length 64 b n []) as L.
  remember (udigits_aux 64 b n []) as d eqn:E. clear E. cbn [length Nat.add] in L. lia.
Qed.

Lemma int_pieces_bound : forall neg d, zlength d <= 64 -> zlength (List.concat (Fmt.int_pieces neg d)) <= 65.
Proof using Type. pin_using tt. intros neg d Hd. rewrite int_pieces_len. destruct neg; lia. Qed.

Definition farg_len (a : farg) : Z := match a with AStr s => zlength s | AInt _ => 0 end.

Definition conv_len_bound__stmt : Prop := forall c a, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.conv_ok c a = true -> conv_len c a <= 80 + farg_len a.
Section Sz9.
Variables c a : ltac2:(SecDiet.SzSec.tyM 'conv_len_bound__stmt "vv" @c).
Lemma conv_len_bound__body : ltac2:(SecDiet.SzSec.bodyP 'conv_len_bound__stmt "vv").
Proof using Type. pin_using tt.
  intros OK.
 unfold conv_len, farg_len. destruct c; destruct a as [v|sv]; try discriminate OK; cbn [Fmt.conv_pieces].
  - pose proof (int_pieces_bound (s32 v <? 0) (dec_udigits (Z.abs (s32 v))) (udigits_zlength _ _)). lia.
  - pose proof (int_pieces_bound false (dec_udigits (u32 v)) (udigits_zlength _ _)). lia.
  - pose proof (udigits_zlength 16 (u32 v)) as L. unfold hex_udigits.
    remember (udigits 16 (u32 v)) as d eqn:Ed. clear Ed. pose proof (zlength_nonneg d) as L0.
    cbn [List.concat]. rewrite concat_app, !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app. change (zlength (@nil Z)) with 0.
    assert (A1 : zlength (List.concat (if zlength d + (if u32 v =? 0 then 1 else 0) <? 8
                                        then [zeros (8 - (zlength d + (if u32 v =? 0 then 1 else 0)))] else [])) <= 8).
    { destruct (Z.ltb_spec (zlength d + (if u32 v =? 0 then 1 else 0)) 8); cbn [List.concat].
      - rewrite app_nil_r. unfold zeros. rewrite zlength_zrepeat; [| destruct (u32 v =? 0); lia]. destruct (u32 v =? 0); lia.
      - change (zlength (@nil Z)) with 0. lia. }
    assert (A2 : zlength (List.concat match d with [] => [[48]; []] | _ :: _ => [d] end) <= 64).
    { destruct d; cbn [List.concat]; rewrite ?app_nil_r; [change (zlength [48]) with 1; lia | exact L]. }
    lia.
  - cbn [List.concat]. rewrite app_nil_r. cbn [app]. lia.
  - pose proof (int_pieces_bound false (dec_udigits (u64 v)) (udigits_zlength _ _)). lia.
Qed.
End Sz9.
Lemma conv_len_bound : ltac:(let t := eval cbv delta [conv_len_bound__stmt] in conv_len_bound__stmt in exact t).
Proof using Type. intros c a. ltac2:(SecDiet.SzSec.closeP 'conv_len_bound__body "vv"). Qed.

Fixpoint fargs_len (args : list farg) : Z :=
  match args with [] => 0 | a :: args' => 80 + farg_len a + fargs_len args' end.
Lemma fargs_len_nonneg : forall args, 0 <= fargs_len args.
Proof using Type. pin_using tt. induction args as [|a args IH]; cbn; [lia|]. destruct a as [z|cs]; cbn; [| pose proof (zlength_nonneg cs)]; lia. Qed.

(* [comment removed for export] *)
Lemma fmt_output_bound_aux : forall fuel s args,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true ->
  zlength (fmt_output (parse_fmt_aux fuel s) args) <= zlength s + fargs_len args.
Proof using Type. pin_using tt.
  induction fuel as [|f IH]; intros s args Hlen OK.
  - destruct s as [|c s0]; [| cbn in Hlen; lia]. cbn in OK. destruct args; [| discriminate]. cbn. lia.
  - destruct s as [|c s0].
    { cbn in OK. destruct args; [| discriminate]. cbn. lia. }
    cbn in Hlen. destruct (Z.eqb_spec c 37) as [E37|N37].
    + subst c. rewrite parse_pct_shape in *.
      destruct (parse_conv s0) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. destruct args as [|a args']; [discriminate|]. apply andb_prop in OK as [OKc OK].
      unfold fmt_output. cbn [fmt_pieces hd tl]. rewrite zlength_concat_cons, zlength_concat_app. change (zlength (@nil Z)) with 0.
      fold (fmt_output (parse_fmt_aux f r') args'). fold (conv_len cv a).
      pose proof (conv_len_bound cv a OKc) as CB.
      assert (LR : (List.length r' < S (List.length s0))%nat).
      { pose proof (parse_conv_cases _ _ _ PC) as SH. destruct cv;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; cbn [List.length]; lia. }
      pose proof (IH r' args' ltac:(lia) OK) as IHr.
      cbn [fargs_len]. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
    + rewrite (parse_lit_shape f c s0 N37) in *.
      destruct (take_lit (c :: s0)) as [l r] eqn:TL. destruct (take_lit_spec _ _ _ TL) as (E1 & N1 & R1).
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. apply andb_prop in OK as [OKl OK].
      unfold fmt_output. cbn [fmt_pieces]. rewrite zlength_concat_cons. fold (fmt_output (parse_fmt_aux f r) args).
      pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
      assert (Hl : (1 <= List.length l)%nat).
      { destruct l as [|c' l0]; [| cbn; lia]. exfalso. cbn in E1. destruct R1 as [->|[r'' ->]]; [discriminate E1|]. injection E1 as E _. exact (N37 E). }
      pose proof (IH r args ltac:(lia) OK) as IHr. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
Qed.

Lemma fmt_output_bound : forall fs args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> zlength (fmt_output (fmt fs) args) <= zlength (str fs) + fargs_len args.
Proof using Type. pin_using tt. intros fs args OK. unfold fmt, parse_fmt in *. apply fmt_output_bound_aux; [lia | exact OK]. Qed.

(* [comment removed for export] *)
Lemma cells_bytes_C8 : forall ws, cells_bytes (map C8 ws) = u64s ws.
Proof using Type. pin_using tt. induction ws as [|w ws IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma cells_size_map_C8 : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof using Type. pin_using tt. induction ws as [|w ws IH]; cbn; [reflexivity|]. rewrite IH. lia. Qed.
Lemma va_area_of_cells : forall m A ws, rw_cells usegs m A (map C8 ws) -> va_area m A ws.
Proof using Type. pin_using tt. intros m A ws H. unfold va_area. rewrite <- cells_bytes_C8. apply rw_cells_bytes_at. exact H. Qed.

(* [comment removed for export] *)
Lemma mod32_of_mod64 : forall z, (z mod 2^64) mod 2^32 = z mod 2^32.
Proof using Type. pin_using tt. intros z. apply Z.mod_mod_divide. exists (2^32). reflexivity. Qed.
Lemma s32_facts : forall z, -2^31 <= s32 z < 2^31 /\ bv_unsigned (Z_to_bv 64 z : word) mod 2^32 = s32 z mod 2^32.
Proof using Type. pin_using tt.
  intros z. unfold s32. rewrite unsigned_lit_wrap, mod32_of_mod64.
  split; [Z.div_mod_to_equations; lia|].
  replace ((z + 2^31) mod 2^32 - 2^31) with (z - ((z + 2^31) / 2^32) * 2^32) by (Z.div_mod_to_equations; lia).
  rewrite <- Zminus_mod_idemp_r. rewrite Z_mod_mult. rewrite Z.sub_0_r. reflexivity.
Qed.
Lemma u32_facts : forall z, 0 <= u32 z < 2^32 /\ bv_unsigned (Z_to_bv 64 z : word) mod 2^32 = u32 z.
Proof using Type. pin_using tt. intros z. unfold u32. rewrite unsigned_lit_wrap, mod32_of_mod64. split; [Z.div_mod_to_equations; lia| reflexivity]. Qed.
Lemma u64_facts : forall z, 0 <= u64 z < 2^64 /\ bv_unsigned (Z_to_bv 64 z : word) = u64 z.
Proof using Type. pin_using tt. intros z. unfold u64. rewrite unsigned_lit_wrap. split; [Z.div_mod_to_equations; lia| reflexivity]. Qed.

(* [comment removed for export] *)
Definition pad8 (x : Z) : Z := (- x) mod 8.
Lemma pad8_range : forall x, 0 <= pad8 x < 8.
Proof using Type. pin_using tt. intros. unfold pad8. Z.div_mod_to_equations. lia. Qed.
Lemma pad8_align : forall x b, 0 <= x -> x <= b -> b mod 8 = 0 -> x + pad8 x <= b.
Proof using Type. pin_using tt.
  intros x b Hx Hb Hal. unfold pad8.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod b 8 ltac:(lia)) as E2.
  set (q1 := - x / 8) in *. set (r1 := (- x) mod 8) in *. set (q2 := b / 8) in *. clearbody q1 r1 q2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Glue.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Notation cblk := (@cblock hptr).
  Notation PS := (PState H hptr).

  Definition client_range_facts__stmt : Prop := forall R (s : PS) (CL FB : list cblk) m SP S len,
    GIo K R s CL FB m -> client_range R CL SP S len -> 0 < len -> CEILZ <= SP ->
    0 < S /\ (S + len <= CEILZ \/ SP <= S) /\ S + len <= 2^47
    /\ (S + len <= 0x10000 \/ 0x56000 <= S \/ SP <= S)
    /\ (S + len <= utp R - 200 \/ utp R - 200 + 4096 <= S \/ SP <= S)
    /\ (SP <= S -> S + len <= rc_spmain R).
  Section Sz22.
  Variables R s CL FB m SP S len : ltac2:(SecDiet.SzSec.tyM 'client_range_facts__stmt "vvvvvvvv" @R).
  Lemma client_range_facts__body : ltac2:(SecDiet.SzSec.bodyP 'client_range_facts__stmt "vvvvvvvv").
  Proof using Type. pin_using tt.
    intros G CR LEN HSP0.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    destruct CR as [CR | CR]; unfold rc_lo, rc_spmain in *.
    - destruct (in_block_facts _ _ S BO1 (CR S ltac:(lia))) as (X1 & X2 & X3 & X4).
      destruct (in_block_facts _ _ (S + len - 1) BO1 (CR (S + len - 1) ltac:(lia))) as (Y1 & Y2 & Y3 & Y4).
      split; [lia|]. split; [left; lia|]. split; [lia|].
      split. { destruct (Z_le_gt_dec (S + len) 0x10000); [left; lia|]. destruct (Z_le_gt_dec 0x56000 S); [right; left; lia|]. exfalso.
               destruct (in_block_facts _ _ (Z.max S 0x10000) BO1 (CR (Z.max S 0x10000) ltac:(lia))) as (W1 & W2 & W3 & W4). lia. }
      split. { destruct (Z_le_gt_dec (S + len) (utp R - 200)); [left; lia|]. destruct (Z_le_gt_dec (utp R - 200 + 4096) S); [right; left; lia|]. exfalso.
               destruct (in_block_facts _ _ (Z.max S (utp R - 200)) BO1 (CR (Z.max S (utp R - 200)) ltac:(lia))) as (W1 & W2 & W3 & W4). lia. }
      intros HSP. lia.
    - split; [lia|]. split; [right; lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|]. intros; lia.
  Qed.
  End Sz22.
  Lemma client_range_facts : ltac:(let t := eval cbv delta [client_range_facts__stmt] in client_range_facts__stmt in exact t).
  Proof using Type. intros R s CL FB m SP S len. ltac2:(SecDiet.SzSec.closeP 'client_range_facts__body "vvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition spo_pure__stmt : Prop := forall sp tp R (s : PS) CL FB lo budget m,
    std_pre_o K sp tp R s CL FB lo budget m ->
    GIo K R s CL FB m /\ stk usegs m lo (bv_unsigned sp) /\ mem_inv usegs m /\ ssp_cells m (rc_canary R)
    /\ rc_lo R <= lo /\ lo + budget <= bv_unsigned sp /\ bv_unsigned sp <= rc_spmain R
    /\ CEILZ <= rc_lo R /\ rc_spmain R + 48 <= 2^47 /\ tls_block_ok_u (utp R - 200).
  Section Sz23.
  Variables sp tp R s CL FB lo budget m : ltac2:(SecDiet.SzSec.tyM 'spo_pure__stmt "vvvvvvvvv" @sp).
  Lemma spo_pure__body : ltac2:(SecDiet.SzSec.bodyP 'spo_pure__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros (G & ST & LOR & LOB & SPM & MI & Etp & AL).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    split; [exact G|]. split; [exact ST|]. split; [exact MI|].
    split. { destruct CLI as (_ & G1 & G2 & _). split; [exact G1 | exact G2]. }
    split; [exact LOR|]. split; [exact LOB|]. split; [exact SPM|].
    unfold rc_lo, rc_spmain in *. split; [lia|]. split; [lia|]. exact TB.
  Qed.
  End Sz23.
  Lemma spo_pure : ltac:(let t := eval cbv delta [spo_pure__stmt] in spo_pure__stmt in exact t).
  Proof using Type. intros sp tp R s CL FB lo budget m. ltac2:(SecDiet.SzSec.closeP 'spo_pure__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma zb_unsigned : forall (bs : list byte), zb (map bv_unsigned bs) = bs.
  Proof using Type. pin_using tt. induction bs as [|b bs IH]; cbn; [reflexivity|]. unfold zb in *. cbn. rewrite definitions.Z_to_bv_bv_unsigned, IH. reflexivity. Qed.

  Definition arg_ok_str__stmt : Prop := forall R (s : PS) CL FB m SP SPa D dn lo Fp FS ap (w : word) cs,
    GIo K R s CL FB m -> CEILZ <= lo -> lo <= SPa -> SPa <= SP -> lo <= Fp -> Fp + FS <= SP -> lo <= ap -> ap + 8 <= SP ->
    farg_word R CL SP D dn m (AStr cs) w ->
    arg_ok Fp FS D dn m lo SPa ap w (PA_s cs).
  Section Sz25.
  Variables R s CL FB m SP SPa D dn lo Fp FS ap w cs : ltac2:(SecDiet.SzSec.tyM 'arg_ok_str__stmt "vvvvvvvvvvvvvvv" @R).
  Lemma arg_ok_str__body : ltac2:(SecDiet.SzSec.bodyP 'arg_ok_str__stmt "vvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G CLO LSP SPA LF FSP LAP APSP FW.
    cbn in FW. destruct FW as (P & bs & slack & -> & BY & NZ & -> & LB & PAD & DD & LOC).
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof (pad8_range (P + Z.of_nat (length bs) + 1)) as PR. unfold pad8 in PR.
    set (pd := (- (P + Z.of_nat (length bs) + 1)) mod 8) in *.
    assert (EP : bv_unsigned (Z_to_bv 64 P : word) = P) by (apply unsigned_lit; lia).
    cbn [arg_ok]. rewrite EP. exists (firstn (Z.to_nat pd) slack).
    assert (LS : length (firstn (Z.to_nat pd) slack) = Z.to_nat pd) by (rewrite length_firstn; lia).
    unfold zlength. rewrite length_map, LS.
    split. { rewrite zb_unsigned. rewrite <- (firstn_skipn (Z.to_nat pd) slack) in BY.
             change (bs ++ Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack ++ skipn (Z.to_nat pd) slack)
               with (bs ++ (Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack) ++ skipn (Z.to_nat pd) slack) in BY.
             rewrite app_assoc in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
    split. { apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
             pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
             destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE]; [|lia]. exfalso. apply NZ.
             replace (Z_to_bv 8 0) with b; [exact Hb|]. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b), E. reflexivity. }
    split; [lia|].
    (* [comment removed for export] *)
    pose proof (proj2 (GIo_tls K _ _ _ _ _ G)) as (TBal & TB0 & TBhi & TBimg).
    assert (LOCF : 0 < P /\ (P + Z.of_nat (length bs) + 1 + pd <= lo \/ SP <= P) /\ P + Z.of_nat (length bs) <= 2^47).   (* [comment removed for export] *)
    { destruct LOC as [CR | [RO | TLS]].
      - destruct (client_range_facts R s CL FB m SP P (Z.of_nat (length bs) + 1) G CR ltac:(lia) ltac:(lia)) as (P0 & PC & P47 & _).
        split; [exact P0|]. split; [|lia]. destruct PC as [PC | PC]; [left | right; exact PC].
        assert (C8 : CEILZ mod 8 = 0).   (* [comment removed for export] *)
        { ceil_facts. replace alloc_ceiling with (512 * (alloc_ceiling / 4096) * 8) by (pose proof (Z_div_mod_eq_full alloc_ceiling 4096); lia). apply Z_mod_mult. }
        pose proof (pad8_align (P + Z.of_nat (length bs) + 1) CEILZ ltac:(lia) ltac:(lia) C8). subst pd. unfold pad8 in *. lia.
      - split; [lia|]. split; [|lia]. left. pose proof (pad8_align (P + Z.of_nat (length bs) + 1) 0x13000 ltac:(lia) ltac:(lia) eq_refl). subst pd. unfold pad8 in *. lia.
      - split; [lia|]. split; [|lia]. left. lia. }
    destruct LOCF as (P0 & SEP & P47).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
  Qed.
  End Sz25.
  Lemma arg_ok_str : ltac:(let t := eval cbv delta [arg_ok_str__stmt] in arg_ok_str__stmt in exact t).
  Proof using Type. intros R s CL FB m SP SPa D dn lo Fp FS ap w cs. ltac2:(SecDiet.SzSec.closeP 'arg_ok_str__body "vvvvvvvvvvvvvvv"). Qed.

  Definition args_ok_of_fargs__stmt : Prop := forall R (s : PS) CL FB m SP SPa D dn lo Fp FS ap,
    GIo K R s CL FB m -> CEILZ <= lo -> lo <= SPa -> SPa <= SP -> lo <= Fp -> Fp + FS <= SP -> lo <= ap -> ap + 8 <= SP ->
    forall its args ws, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok its args = true ->
    Forall2 (farg_word R CL SP D dn m) args ws ->
    args_ok Fp FS D dn m lo SPa ap ws (to_pargs its args).
  Section Sz26.
  Variables R s CL FB m SP SPa D dn lo Fp FS ap : ltac2:(SecDiet.SzSec.tyM 'args_ok_of_fargs__stmt "vvvvvvvvvvvvv" @R).
  Lemma args_ok_of_fargs__body : ltac2:(SecDiet.SzSec.bodyP 'args_ok_of_fargs__stmt "vvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G CLO LSP SPA LF FSP LAP APSP.
    induction its as [|[l|c|b] its IH]; intros args ws OK FW.
    - cbn in OK. destruct args; [|discriminate]. inversion FW; subst. cbn. exact I.
    - cbn in OK |- *. apply andb_prop in OK as [_ OK]. apply IH; assumption.
    - cbn in OK |- *. destruct args as [|a args]; [discriminate|]. apply andb_prop in OK as [OKc OK].
      inversion FW as [|a' w args' ws' FA FW']; subst. cbn [args_ok]. split; [| apply IH; assumption].
      destruct c; destruct a as [v|sv]; try discriminate OKc; cbn [conv_parg].
      + cbn in FA |- *. subst w. exact (s32_facts v).
      + cbn in FA |- *. subst w. exact (u32_facts v).
      + cbn in FA |- *. subst w. exact (u32_facts v).
      + eapply arg_ok_str; eassumption.
      + cbn in FA |- *. subst w. exact (u64_facts v).
    - cbn in OK. discriminate.
  Qed.
  End Sz26.
  Lemma args_ok_of_fargs : ltac:(let t := eval cbv delta [args_ok_of_fargs__stmt] in args_ok_of_fargs__stmt in exact t).
  Proof using Type. intros R s CL FB m SP SPa D dn lo Fp FS ap. ltac2:(SecDiet.SzSec.closeP 'args_ok_of_fargs__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma stdio_stack_big : VSN_DEPTH + 80 <= STDIO_STACK.
  Proof using Type. pin_using tt. unfold VSN_DEPTH, STDIO_STACK. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vsnprintf4_proof__stmt : Prop := vsnprintf_spec4_stmt K.
  Section Sz28.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo DST n FMTA AP fs ws junk : ltac2:(SecDiet.SzSec.tyM 'vsnprintf4_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkvv" @ra).
  Lemma vsnprintf4_proof__body : ltac2:(SecDiet.SzSec.bodyP 'vsnprintf4_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkvv").
  Proof using Type. pin_using tt.
    intros args PRE -> -> -> -> HN FAT FOK LWS L4 FW APC SPAP APHI APD DSTC CR.
    destruct (spo_pure _ _ _ _ _ _ _ _ _ PRE) as (G & ST & MI & SSP & LOR & LOB & SPM & CEILLO & SP47 & TB).
    unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct FAT as (FBY & FLO & FHI).
    unfold fmt_ok in FOK. apply andb_prop in FOK as [IOK FLEN]. rewrite items_ok_eq in IOK. apply Z.ltb_lt in FLEN.
    pose proof (fmt_output_bound fs args IOK) as OB. rewrite str_length in OB.
    assert (FLn : fargs_len args <= Z.of_nat (length args) * (80 + 2^24)).
    { clear -FW. revert ws FW. induction args as [|a args IH]; intros ws FW; [cbn; lia|].
      inversion FW as [|a' w args' ws' FA FW']; subst.
      assert (Ha : farg_len a <= 2^24). { destruct a as [z|cs]; cbn; [lia|]. cbn in FA. destruct FA as (P & bs & slack & _ & _ & _ & -> & LB & _).
                                         unfold zlength. rewrite length_map. lia. }
      specialize (IH ws' FW'). cbn [fargs_len length]. lia. }
    assert (FL4 : fargs_len args <= 4 * (80 + 2^24)) by (clear -FLn L4; pose proof (fargs_len_nonneg args); nia).
    destruct (client_range_facts R s CL FB m _ DST n G CR ltac:(lia) ltac:(lia)) as (D0 & DC & D47 & DIMG & DTLS & DSPM).
    (* [comment removed for export] *)
    destruct (stk_split _ _ _ (bv_unsigned sp - 65536) _ ST ltac:(lia)) as [ST1 ST2].
    eapply evt_mono.
    { eapply (vsnprintf_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST n FMTA AP (bv_unsigned sp - 65536)
                (str fs ++ [0]) ws (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args) (zlength (fmt_output (fmt fs) args)) (rc_canary R))
        with (jd := junk).
      - exact HN.
      - apply str_range.
      - apply (fmt_pass1 fs args IOK). rewrite str_length. unfold INT_MAX. lia.
      - apply fmt_bridge; [exact IOK|]. unfold INT_MAX. lia.
      - unfold VSN_DEPTH. lia.
      - unfold GLOBALS_TOP. lia.
      - lia.
      - rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app, str_length. change (zlength [0]) with 1. lia.
      - pose proof (rw_cells_bound _ _ _ _ APC) as AB. rewrite cells_size_map_C8 in AB. unfold zlength. lia.
      - split; [lia|]. split; [lia|]. split; [lia|].
        destruct DC as [DC|DC]; [left; lia|]. right. destruct APD as [APD|APD]; [left; unfold zlength; lia | right; lia].
      - reflexivity. - reflexivity. - reflexivity. - reflexivity.
      - exact DSTC.
      - rewrite <- str_bytes. exact FBY.
      - apply va_area_of_cells. exact APC.
      - eapply (args_ok_of_fargs R s CL FB m (bv_unsigned sp) (bv_unsigned sp) DST n (bv_unsigned sp - 65536) (bv_unsigned sp - 656) SN_FS (bv_unsigned sp - 672));
          [exact G | lia | lia | lia | lia | unfold SN_FS; lia | lia | lia | exact IOK | exact FW].
      - exact ST2.
      - exact SSP.
      - exact MI.
      - exact I. }
    cbv beta. intros ms' PO. unfold vsnprintf_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & jd' & m' & -> & MU & WM & MI' & ST' & SSP' & DST').
    set (out := Fmt.snprintf n fs args) in *.
    change (firstn (Z.to_nat (n - 1)) (List.concat (fmt_pieces (fmt fs) args))) with out in DST'.
    pose proof (rw_CB_length _ _ _ _ DST') as LJ. rewrite length_app, zb_length in LJ. cbn [length] in LJ.
    exists (Z_to_bv 64 (zlength (fmt_output (fmt fs) args))), m', (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')).
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ]. }
    split; [reflexivity|].
    apply (rw_cells_split_CB usegs _ _ [] (Z.to_nat n) _ [] [length out + 1; Z.to_nat n - length out - 1]%nat) in DST'; [| cbn; lia].
    cbn [mk_CB_cells app] in DST'.
    replace (firstn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')) with (map b8 out ++ [Z_to_bv 8 0]) in DST'.
    2:{ rewrite firstn_app, zb_length, (firstn_all2 (zb out)) by (rewrite zb_length; lia).
        replace (length out + 1 - length out)%nat with 1%nat by lia. reflexivity. }
    rewrite (firstn_all2 (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd'))) in DST' by (rewrite length_skipn, length_app, zb_length; cbn [length]; lia).
    exact DST'.
  Qed.
  End Sz28.
  Theorem vsnprintf4_proof : ltac:(let t := eval cbv delta [vsnprintf4_proof__stmt] in vsnprintf4_proof__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo DST n FMTA AP fs args ws junk. ltac2:(SecDiet.SzSec.closeP 'vsnprintf4_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma args_ok_more : forall Fp FS B BS m lo sp ap ws more pargs,
    args_ok Fp FS B BS m lo sp ap ws pargs -> args_ok Fp FS B BS m lo sp ap (ws ++ more) pargs.
  Proof using Type. pin_using tt.
    intros Fp FS B BS m lo sp ap ws more pargs. revert ws.
    induction pargs as [|a pargs IH]; intros ws AOK; [destruct (ws ++ more); exact I|].
    destruct ws as [|w ws]; [destruct AOK|]. cbn in AOK |- *. destruct AOK as [H1 H2]. split; [exact H1 | apply IH; exact H2].
  Qed.

  Definition snprintf_proof__stmt : Prop := snprintf_spec_stmt K.
  Section Sz30.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo DST n FMTA fs junk : ltac2:(SecDiet.SzSec.tyM 'snprintf_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv" @ra).
  Lemma snprintf_proof__body : ltac2:(SecDiet.SzSec.bodyP 'snprintf_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv").
  Proof using Type. pin_using tt.
    intros args PRE -> -> -> HN FAT FOK L3 FW DSTC CR.
    destruct (spo_pure _ _ _ _ _ _ _ _ _ PRE) as (G & ST & MI & SSP & LOR & LOB & SPM & CEILLO & SP47 & TB).
    unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct FAT as (FBY & FLO & FHI).
    unfold fmt_ok in FOK. apply andb_prop in FOK as [IOK FLEN]. rewrite items_ok_eq in IOK. apply Z.ltb_lt in FLEN.
    pose proof (fmt_output_bound fs args IOK) as OB. rewrite str_length in OB.
    assert (FLn : fargs_len args <= Z.of_nat (length args) * (80 + 2^24)).
    { clear -FW. remember (firstn (length args) [a3; a4; a5]) as ws eqn:Ews. clear Ews. revert ws FW. induction args as [|a args IH]; intros ws FW; [cbn; lia|].
      inversion FW as [|a' w args' ws' FA FW']; subst.
      assert (Ha : farg_len a <= 2^24). { destruct a as [z|cs]; cbn; [lia|]. cbn in FA. destruct FA as (P & bs & slack & _ & _ & _ & -> & LB & _).
                                         unfold zlength. rewrite length_map. lia. }
      specialize (IH ws' FW'). cbn [fargs_len length]. lia. }
    assert (FL4 : fargs_len args <= 3 * (80 + 2^24)) by (clear -FLn L3; pose proof (fargs_len_nonneg args); nia).
    destruct (client_range_facts R s CL FB m _ DST n G CR ltac:(lia) ltac:(lia)) as (D0 & DC & D47 & DIMG & DTLS & DSPM).
    pose proof (rw_CB_length _ _ _ _ DSTC) as LJD.
    (* [comment removed for export] *)
    pose proof (args_ok_of_fargs R s CL FB m (bv_unsigned sp) (bv_unsigned sp) DST n (bv_unsigned sp - 65536)
                  (bv_unsigned sp - 80 - 656) SN_FS (bv_unsigned sp - 80 - 672) G ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(unfold SN_FS; lia) ltac:(lia) ltac:(lia) (fmt fs) args _ IOK FW) as AOK0.
    apply (args_ok_more _ _ _ _ _ _ _ _ _ (skipn (length args) [a3; a4; a5] ++ [a6; a7])) in AOK0.
    assert (EWS : firstn (length args) [a3; a4; a5] ++ (skipn (length args) [a3; a4; a5] ++ [a6; a7]) = [a3; a4; a5; a6; a7]).
    { rewrite app_assoc, firstn_skipn. reflexivity. }
    rewrite EWS in AOK0. clear EWS.
    assert (GLO__ : 0x56000 <= lo) by (unfold rc_lo in *; lia).   (* [comment removed for export] *)
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 65536, bv_unsigned sp)]%Z m) as MUp.
    pose proof (munch_refl [(bv_unsigned sp - 65536, bv_unsigned sp); (DST, DST + n)]%Z m) as MU.
    stash FBY. stash DSTC. stash AOK0. stash DC. stash DIMG. stash DTLS.
    destruct (stk_split _ _ _ (bv_unsigned sp - 65536) _ ST ltac:(lia)) as [ST1 ST2]. clear ST. rename ST2 into ST.
    unfold SNPRINTF_ENTRY.
    carve_frame 80%nat ST.
    do 15 zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    match goal with X : rw_cells _ _ (bv_unsigned sp + -80)%Z (_ :: _) |- _ => rename X into FRv end.
    pose proof FRv as FRc.
    apply (proj1 (rw_cells_app usegs _ _ [_;_;_;_;_] _)) in FRc. destruct FRc as [FRlo VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -80 + Z.of_nat 40) with (bv_unsigned sp + -40) in VAc by lia. clear FRlo.
    unfold hide in FBY, DSTC, AOK0, DC, DIMG, DTLS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (BY1 : bytes_at usegs mm FMTA (zb (str fs ++ [0])))
        by (rewrite <- str_bytes; eapply bytes_at_transport; [exact FBY | exact MUp | cbn [disjoint_from]; rewrite length_app, length_map, length_list_ascii_of_string; cbn [length]; lia]);
      assert (DST1 : rw_cells usegs mm DST [CB (Z.to_nat n) junk])
        by (eapply rw_cells_transport; [exact DSTC | exact MUp | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]);
      assert (AOK1 : args_ok (bv_unsigned sp + -80 - 656) SN_FS DST n mm (bv_unsigned sp - 65536) (bv_unsigned sp + -80) (bv_unsigned sp + -80 - 672)
                        [a3; a4; a5; a6; a7] (to_pargs (fmt fs) args))
        by (replace (bv_unsigned sp + -80 - 656) with (bv_unsigned sp - 80 - 656) by lia;
            replace (bv_unsigned sp + -80 - 672) with (bv_unsigned sp - 80 - 672) by lia;
            eapply args_ok_vf; [exact AOK0 | lia | exact MUp | constructor; [cbn [fst snd]; left; lia | constructor]])
    end.
    clear FBY DSTC AOK0 MUp.
    eapply evt_cut.
    { eapply (vsnprintf_spec _ _ gp tp _ s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST n FMTA (bv_unsigned sp + -40) (bv_unsigned sp - 65536)
                (str fs ++ [0]) [a3; a4; a5; a6; a7] (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args) (zlength (fmt_output (fmt fs) args)) (rc_canary R))
        with (jd := junk);
        rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP, SN_FS, zlength in *.
      - exact HN.
      - apply str_range.
      - apply (fmt_pass1 fs args IOK). rewrite str_length. unfold INT_MAX. lia.
      - apply fmt_bridge; [exact IOK|]. unfold INT_MAX. unfold zlength. lia.
      - lia.
      - lia.
      - lia.
      - rewrite length_app. cbn [length]. pose proof (str_length fs) as SL. unfold zlength in SL. lia.
      - cbn [length]. lia.
      - cbn [length]. clear -D0 D47 DC DIMG LOR LOB CEILLO SPHI. lia.
      - reflexivity. - reflexivity. - reflexivity. - reflexivity.
      - exact DST1.
      - exact BY1.
      - apply va_area_of_cells. exact VAc.
      - exact AOK1.
      - exact ST.
      - unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact I. }
    cbv beta. intros ms' PO. unfold vsnprintf_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & jd' & m' & -> & MUc & WMc & MI' & ST' & SSP' & DST').
    clear VAc DST1 BY1 AOK1.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP' as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    zs. zs. zs. zs.
    release_frame FRv ST' (bv_unsigned sp).
    set (out := Fmt.snprintf n fs args) in *.
    change (firstn (Z.to_nat (n - 1)) (List.concat (fmt_pieces (fmt fs) args))) with out in DST'.
    pose proof (rw_CB_length _ _ _ _ DST') as LJ. rewrite length_app, zb_length in LJ. cbn [length] in LJ.
    apply evt_done.
    exists (Z_to_bv 64 (zlength (fmt_output (fmt fs) args))), m', (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')).
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). cbv delta [mkR]. reflexivity. }
    split. { first [exact MU | match goal with |- ?g => idtac "MUGOAL" g end; match type of MU with ?t => idtac "MU:" t end]. }
    split; [exact WM|]. split; [assumption|].
    split. { eapply stk_merge; [ | exact ST' | lia ]. exact ST1. }
    split; [reflexivity|].
    apply (rw_cells_split_CB usegs _ _ [] (Z.to_nat n) _ [] [length out + 1; Z.to_nat n - length out - 1]%nat) in DST'; [| cbn; lia].
    cbn [mk_CB_cells app] in DST'.
    replace (firstn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')) with (map b8 out ++ [Z_to_bv 8 0]) in DST'.
    2:{ rewrite firstn_app, zb_length, (firstn_all2 (zb out)) by (rewrite zb_length; lia).
        replace (length out + 1 - length out)%nat with 1%nat by lia. reflexivity. }
    rewrite (firstn_all2 (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd'))) in DST' by (rewrite length_skipn, length_app, zb_length; cbn [length]; lia).
    exact DST'.
  Qed.
  End Sz30.
  Theorem snprintf_proof : ltac:(let t := eval cbv delta [snprintf_proof__stmt] in snprintf_proof__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo DST n FMTA fs args junk. ltac2:(SecDiet.SzSec.closeP 'snprintf_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv"). Qed.
End Glue.

End WithCeil.
End TwB.
End Stdio_glue_sn.

(* [comment removed for export] *)
Module Stdio_glue_pf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import String Ascii ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_iface F_printf_core_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blk__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Printf_fsink. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_printf_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.Stdio_glue_sn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Printf_fsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_vfprintf_file OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_fprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Vfprintf_leaf.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sbl_is_big n := lazymatch n with S _ => let b := eval vm_compute in (Nat.leb 200 n) in lazymatch b with true => idtac end end.
Local Ltac sbl_pose_in H :=
  (let T := type of H in let T' := eval hnf in T in change T' in H);
  repeat match type of H with
  | context [repeat ?b ?n] => sbl_is_big n; let z := fresh "sblz" in pose (z := repeat b n); change (repeat b n) with z in H
  | context [CB ?n _] => sbl_is_big n; let x := fresh "sblv" in pose (x := n); change n with x in H
  end.
Local Ltac sbl_subst_all :=
  repeat match goal with
  | z := repeat _ ?n |- _ => sbl_is_big n; subst z
  | x := ?n |- _ => sbl_is_big n; subst x
  end.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma fmt_pieces_small_aux : forall fuel s args,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true ->
  Forall (fun p => zlength p <= zlength s + 80 + fargs_len args) (fmt_pieces (parse_fmt_aux fuel s) args).
Proof using Type. pin_using tt.
  induction fuel as [|f IH]; intros s args Hlen OK.
  - destruct s as [|c s0]; [| cbn in Hlen; lia]. cbn. constructor.
  - destruct s as [|c s0]. { cbn. constructor. }
    cbn in Hlen. pose proof (fargs_len_nonneg args) as AN. destruct (Z.eqb_spec c 37) as [E37|N37].
    + subst c. rewrite parse_pct_shape in *.
      destruct (parse_conv s0) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. destruct args as [|a args']; [discriminate|]. apply andb_prop in OK as [OKc OK].
      cbn [fmt_pieces hd tl]. pose proof (conv_len_bound cv a OKc) as CB. unfold conv_len in CB.
      assert (LR : (List.length r' < S (List.length s0))%nat).
      { pose proof (parse_conv_cases _ _ _ PC) as SH. destruct cv;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; cbn [List.length]; lia. }
      pose proof (IH r' args' ltac:(lia) OK) as IHr. pose proof (fargs_len_nonneg args') as AN'.
      constructor; [change (zlength (@nil Z)) with 0; cbn [fargs_len]; destruct a as [z|cs]; cbn; [| pose proof (zlength_nonneg cs)]; unfold zlength in *; cbn [length]; lia|].
      apply Forall_app. split.
      * apply Forall_forall. intros pc Hpc. pose proof (in_split _ _ Hpc) as (l1 & l2 & E).
        assert (zlength pc <= zlength (List.concat (Fmt.conv_pieces cv a))).
        { rewrite E, concat_app. cbn [List.concat]. rewrite !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app. pose proof (zlength_nonneg (List.concat l1)). pose proof (zlength_nonneg (List.concat l2)). lia. }
        cbn [fargs_len]. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
      * eapply Forall_impl; [| exact IHr]. cbv beta. intros pc Hpc. cbn [fargs_len]. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons.
        pose proof (zlength_nonneg r'). destruct a as [z|cs]; cbn; [| pose proof (zlength_nonneg cs)]; unfold zlength in *; lia.
    + rewrite (parse_lit_shape f c s0 N37) in *.
      destruct (take_lit (c :: s0)) as [l r] eqn:TL. destruct (take_lit_spec _ _ _ TL) as (E1 & N1 & R1).
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. apply andb_prop in OK as [OKl OK].
      cbn [fmt_pieces]. pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
      assert (Hl : (1 <= List.length l)%nat).
      { destruct l as [|c' l0]; [| cbn; lia]. exfalso. cbn in E1. destruct R1 as [->|[r'' ->]]; [discriminate E1|]. injection E1 as E _. exact (N37 E). }
      pose proof (IH r args ltac:(lia) OK) as IHr.
      constructor; [rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons; unfold zlength in *; lia|].
      eapply Forall_impl; [| exact IHr]. cbv beta. intros pc Hpc. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
Qed.

Lemma fmt_pieces_small : forall fs args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> zlength (str fs) + 80 + fargs_len args <= PIECE_MAX -> pieces_small (fmt_pieces (fmt fs) args).
Proof using Type. pin_using tt.
  intros fs args OK B. unfold pieces_small. eapply Forall_impl; [| apply fmt_pieces_small_aux; [unfold fmt, parse_fmt; lia | exact OK]].
  cbv beta. intros p Hp. unfold fmt, parse_fmt in B. lia.
Qed.

(* [comment removed for export] *)
Definition fmt_facts__stmt : Prop := forall fs args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> (length args <= 2)%nat -> Forall (fun a => farg_len a <= 2^24) args ->
  zlength (str fs) < 4096 ->
  Forall (fun c => 0 <= c < 256) (str fs ++ [0])
  /\ pass1_ok (str fs ++ [0]) = true
  /\ printf_pieces (str fs ++ [0]) (to_pargs (fmt fs) args) = Some (fmt_pieces (fmt fs) args, zlength (fmt_output (fmt fs) args))
  /\ pieces_small (fmt_pieces (fmt fs) args)
  /\ 0 <= zlength (fmt_output (fmt fs) args) < 2^31 - 1.
Section Sz3.
Variables fs : ltac2:(SecDiet.SzSec.tyM 'fmt_facts__stmt "vk" @fs).
Lemma fmt_facts__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_facts__stmt "vk").
Proof using Type. pin_using tt.
  intros args OK L2 SM FL.
  assert (FL4 : fargs_len args <= 2 * (80 + 2^24)).
  { clear -SM L2. destruct args as [|a [|b [|c args]]]; cbn [length] in L2; [cbn; lia| | |lia].
    - inversion SM; subst. cbn [fargs_len]. lia.
    - inversion SM as [|a' l Ha SM']; subst. inversion SM'; subst. cbn [fargs_len]. lia. }
  pose proof (fmt_output_bound fs args OK) as OB. pose proof (fmt_output_nonneg (fmt fs) args) as ON.
  split; [apply str_range|]. split; [apply (fmt_pass1 fs args OK); unfold INT_MAX; lia|].
  split; [apply fmt_bridge; [exact OK| unfold INT_MAX; lia]|].
  split; [apply fmt_pieces_small; [exact OK| unfold PIECE_MAX; lia]|]. lia.
Qed.
End Sz3.
Lemma fmt_facts : ltac:(let t := eval cbv delta [fmt_facts__stmt] in fmt_facts__stmt in exact t).
Proof using Type. intros fs args. ltac2:(SecDiet.SzSec.closeP 'fmt_facts__body "vk"). Qed.

(* [comment removed for export] *)
Definition fmt_static (fs : string) (A : Z) : Prop :=
  ro_bytes_b ssegs A (zb (str fs ++ [0])) = true /\ 65536 <= A /\ A + zlength (str fs ++ [0]) <= 77824.
Lemma fmt_bytes : forall m fs A, mem_inv ssegs m -> fmt_static fs A -> bytes_at ssegs m A (zb (str fs ++ [0])).
Proof using Type. pin_using tt.
  intros m fs A MI (RO & LO & HI). unfold zlength in HI.
  pose proof (ro_cells_image ssegs m A _ MI RO ltac:(lia)) as X. rewrite zb_length in X.
  pose proof (ro_cells_bytes_at _ _ _ _ (X ltac:(lia))) as Y. cbn [cells_bytes cbytes] in Y. rewrite app_nil_r in Y. exact Y.
Qed.

(* [comment removed for export] *)
Lemma s32_facts_sx : forall v, 0 <= v < 2^32 ->
  -2^31 <= s32 v < 2^31 /\ bv_unsigned (sx32 (Z_to_bv 64 v)) mod 2^32 = s32 v mod 2^32.
Proof using Type. pin_using tt.
  intros v Hv. pose proof (s32_facts v) as [R E]. split; [exact R|]. rewrite <- E.
  unfold sx32. rewrite (unsigned_lit v) by lia. rewrite unsigned_lit_wrap, mod32_of_mod64.
  rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.bv_swrap32_eq.
  replace ((v + 2^31) mod 2^32 - 2^31) with (v - ((v + 2^31) / 2^32) * 2^32) by (Z.div_mod_to_equations; lia).
  rewrite <- Zminus_mod_idemp_r, Z_mod_mult, Z.sub_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fmt_call_ok (FMT : Z) (fmtz : list Z) (pargs : list parg) (ps : list (list Z)) (r : Z) : Prop :=
  Forall (fun c => 0 <= c < 256) fmtz /\ pass1_ok fmtz = true /\ printf_pieces fmtz pargs = Some (ps, r) /\ pieces_small ps
  /\ 0 <= r < 2^31 - 1 /\ (65536 <= FMT /\ FMT + zlength fmtz <= 77824)
  /\ (forall m, mem_inv ssegs m -> bytes_at ssegs m FMT (zb fmtz)).

Lemma fmt_call_ok_intro : forall fs FMT args,
  fmt_static fs FMT -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> (length args <= 2)%nat ->
  Forall (fun a => farg_len a <= 2^24) args -> zlength (str fs) < 4096 ->
  fmt_call_ok FMT (str fs ++ [0]) (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args) (zlength (fmt_output (fmt fs) args)).
Proof using Type. pin_using tt.
  intros fs FMT args FS OK L2 SM FL.
  destruct (fmt_facts fs args OK L2 SM FL) as (HF & P1 & PIECES & SMALL & RB).
  pose proof FS as (RO & LO & HI).
  split; [exact HF|]. split; [exact P1|]. split; [exact PIECES|]. split; [exact SMALL|]. split; [exact RB|].
  split; [split; [exact LO| exact HI]|]. intros m MI. exact (fmt_bytes m fs FMT MI FS).
Qed.
End WithCeil.


Local Open Scope string_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Definition FS_EMIT_D : string := "%d
".
Definition FS_FAILED_REMOVE : string := "failed remove, errno=%d
".
Definition FS_FAILED_OPEN : string := "failed open, errno=%d
".
Definition FS_COULDNT_OPEN : string := "Couldn't open pcap file %s
".
Definition FS_PACKET_LENGTH : string := "packet length=%d/%d
".
Definition FS_USAGE : string := "usage: %s INPUT
".
Definition FS_CANNOT_OPEN : string := "cli: cannot open %s
".
Definition FS_READ_ERROR : string := "cli: read error on %s
".
Definition FS_TOO_BIG : string := "cli: input >= %u bytes, refused
".
End WithCeil.

Local Close Scope string_scope.

Local Ltac fmt_call fs args :=
  lazymatch goal with |- fmt_call_ok ?FMT ?fz _ _ _ =>
    change (fmt_call_ok FMT fz (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args) (zlength (fmt_output (fmt fs) args)))
  end;
  apply fmt_call_ok_intro;
    [ split; [vm_compute; reflexivity | vm_compute; split; intros HH; discriminate HH]
    | vm_compute; reflexivity
    | cbn [length]; lia
    | repeat constructor; cbn [farg_len]; try assumption; try lia
    | vm_compute; reflexivity ].

Section WithCeil.
Context {CEILV : CEIL}.
Lemma call_emit_d : forall v,
  fmt_call_ok FMT_D (str FS_EMIT_D ++ [0]) [PA_i (s32 v)] (pieces_emit_d v) (zlength (fmt_output (fmt FS_EMIT_D) [AInt v])).
Proof using Type. pin_using tt. intros v. fmt_call FS_EMIT_D [AInt v]. Qed.
Lemma call_failed_remove : forall v,
  fmt_call_ok FMT_FAILED_REMOVE (str FS_FAILED_REMOVE ++ [0]) [PA_i (s32 v)] (pieces_failed_remove v) (zlength (fmt_output (fmt FS_FAILED_REMOVE) [AInt v])).
Proof using Type. pin_using tt. intros v. fmt_call FS_FAILED_REMOVE [AInt v]. Qed.
Lemma call_failed_open : forall v,
  fmt_call_ok FMT_FAILED_OPEN (str FS_FAILED_OPEN ++ [0]) [PA_i (s32 v)] (pieces_failed_open v) (zlength (fmt_output (fmt FS_FAILED_OPEN) [AInt v])).
Proof using Type. pin_using tt. intros v. fmt_call FS_FAILED_OPEN [AInt v]. Qed.
Lemma call_packet_length : forall v1 v2,
  fmt_call_ok FMT_PACKET_LENGTH (str FS_PACKET_LENGTH ++ [0]) [PA_i (s32 v1); PA_i (s32 v2)] (pieces_packet_length v1 v2)
              (zlength (fmt_output (fmt FS_PACKET_LENGTH) [AInt v1; AInt v2])).
Proof using Type. pin_using tt. intros v1 v2. fmt_call FS_PACKET_LENGTH [AInt v1; AInt v2]. Qed.
Lemma call_too_big :
  fmt_call_ok FMT_TOO_BIG (str FS_TOO_BIG ++ [0]) [PA_u (u32 0x4000000)] pieces_too_big (zlength (fmt_output (fmt FS_TOO_BIG) [AInt 0x4000000])).
Proof using Type. pin_using tt. fmt_call FS_TOO_BIG [AInt 0x4000000]. Qed.
Lemma call_couldnt_open : forall s, zlength s <= 2^24 ->
  fmt_call_ok FMT_COULDNT_OPEN (str FS_COULDNT_OPEN ++ [0]) [PA_s s] (pieces_couldnt_open s) (zlength (fmt_output (fmt FS_COULDNT_OPEN) [AStr s])).
Proof using Type. pin_using tt. intros s Hs. fmt_call FS_COULDNT_OPEN [AStr s]. Qed.
Lemma call_usage : forall s, zlength s <= 2^24 ->
  fmt_call_ok FMT_USAGE (str FS_USAGE ++ [0]) [PA_s s] (pieces_usage s) (zlength (fmt_output (fmt FS_USAGE) [AStr s])).
Proof using Type. pin_using tt. intros s Hs. fmt_call FS_USAGE [AStr s]. Qed.
Lemma call_cannot_open : forall s, zlength s <= 2^24 ->
  fmt_call_ok FMT_CANNOT_OPEN (str FS_CANNOT_OPEN ++ [0]) [PA_s s] (pieces_cannot_open s) (zlength (fmt_output (fmt FS_CANNOT_OPEN) [AStr s])).
Proof using Type. pin_using tt. intros s Hs. fmt_call FS_CANNOT_OPEN [AStr s]. Qed.
Lemma call_read_error : forall s, zlength s <= 2^24 ->
  fmt_call_ok FMT_READ_ERROR (str FS_READ_ERROR ++ [0]) [PA_s s] (pieces_read_error s) (zlength (fmt_output (fmt FS_READ_ERROR) [AStr s])).
Proof using Type. pin_using tt. intros s Hs. fmt_call FS_READ_ERROR [AStr s]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Glue.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Notation cblk := (@cblock hptr).
  Notation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.

  #[local] Notation spo_facts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.spo_facts K KST).
  #[local] Notation files_R_focus := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.files_R_focus (ho_eqb HO) EQB).
  #[local] Notation GIo_stdio_step := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.GIo_stdio_step K KST HFL).
  #[local] Notation keeps_of_stdio := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.keeps_of_stdio K).
  #[local] Notation implM_lookup_file := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.implM_lookup_file HO).
  #[local] Notation client_range_lo := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.client_range_lo K).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma stdout_finish :
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (m : mem) (lo : Z) (ps : list (list Z)) (tail : list byte) (rp : Z)
           (f' : file_st) (st' : PS) (ms' : machine_state),
      GIo K R s CL FB m -> STDIOR (ps_libc s) FB m ->
      CEILZ <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp <= rc_spmain R ->
      0 <= rp -> rp + zlength (f_rbuf (lc_stdout (ps_libc s))) < 2^63 -> firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
      fprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail lo (rc_canary R) true true
                        rp (rp + zlength (f_rbuf (lc_stdout (ps_libc s)))) m s f' st' ms' ->
      mleaf (vfprintf (lc_stdout (ps_libc s)) ps) s f' st' ->
      st' = s /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom ssegs)
        /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
        /\ GIo K R (set_libc (set_stdout f' (ps_libc s)) s) CL FB m'.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros until ms'. intros G SR CLO LOS SPM RP0 RP1 GLN PO LF.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof SOI as (CH1 & FD1 & BS1 & NRD1 & NWR1 & EOF1 & RB1 & LBF1).
    sbl_pose_in PO. destruct PO as (-> & INV' & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & flags' & mode' & bufbytes' & m' & rpos' & rend'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & RP' & FL' & BUF' & BP' & WBL'). sbl_subst_all.
    assert (BSnz : f_bufsize (lc_stdout (ps_libc s)) <> 0) by (rewrite BS1; unfold BUFSIZ; lia).
    pose proof (vfprintf_leaf_buffered _ _ _ _ _ BSnz LF) as [FX _].
    pose proof (vfprintf_leaf_buffered_wl _ _ _ _ _ BSnz LF) as WL.
    split; [reflexivity|].
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    unfold A_STDOUT, A_STDOUT_BUF in *.
    assert (HW : Forall (stdio_iv R CL FB (bv_unsigned sp)) [(lo, bv_unsigned sp); (145472, 145472 + 232); (345456, 345456 + 1024)]).
    { unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd]; [left; lia| right; right; left; lia| right; right; right; lia]. }
    split.
    { eapply agrees_on_weaken; [eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia]|].
      - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd]; [left; lia| right; right; left; lia| right; right; right; left; lia].
      - intros a Ha. split; [exact Ha| intros X; exact X]. }
    eapply (GIo_stdio_step R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| exact SPM|].
    cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_stdout].
    pose proof (GIo_blocks K _ _ _ _ _ G) as BOK. pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof SEI as (_ & _ & SEbs & _).
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    Ltac trw MU WM A := eapply rw_cells_transport; [exact A | exact MU | exact WM | cbn; lia].
    pose proof INV' as (WA' & RB' & BS' & NW' & FDC' & _ & CHN').
    rewrite RB1 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    split.
    { exists flags', mode', rpos', tail, bufbytes'.
      rewrite WA', RB', BS'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      assert (Erend : rend' = rpos') by (rewrite RB1 in RP'; change (zlength (@nil Z)) with 0 in RP'; lia).
      rewrite Erend in FC'.
      split; [exact FC'|]. split; [exact FL'|]. split; [exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [exact WBL'|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN]. }
    split.
    { pose proof FX as (E1 & E2 & E3 & E4 & E5 & E6 & _ & _ & SW' & LB').
      unfold stdout_inv. rewrite E1, E2, E4, E5, E6.
      split; [exact CH1|]. split; [exact FD1|]. split; [exact BS'|]. split; [exact NRD1|]. split; [exact NWR1|]. split; [exact EOF1|]. split; [exact RB'|].
      destruct WL as [[W1 W2]|[W1 W2]]; rewrite W1, ?W2; [exact LBF1| intros X; discriminate X]. }
    split. { eapply FILE_R_transport; [exact SE| exact MU| exact WM| | | rewrite SEbs; lia].
             - repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
             - rewrite SEbs. repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil. }
    split; [exact SEI|].
    split. { eapply rw_cells_transport; [exact SIN | exact MU | exact WM |]. unfold stdin_cells. rewrite file_cells_size. cbn. lia. }
    split; [trw MU WM U1|]. split; [trw MU WM U2|]. split; [trw MU WM U3|]. split; [trw MU WM OL|]. split; [trw MU WM OH|].
    split; [| exact ND].
    eapply files_R_transport; [exact FS| exact MU| exact WM|].
    apply Forall_forall. intros [lo' hi'] Hiv. apply Forall_forall. intros [[q' A'] n'] Hb. cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) BO2 _ Hb) as (K1 & K2 & K3 & K4 & K5 & K6). unfold cb_addr, cb_size in *. cbn [fst snd] in *.
    cbn in Hiv. destruct Hiv as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vprintf_d_proof__stmt : Prop := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.vprintf_d_stmt K.
  Section Sz16.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo AP v rest : ltac2:(SecDiet.SzSec.tyM 'vprintf_d_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma vprintf_d_proof__body : ltac2:(SecDiet.SzSec.bodyP 'vprintf_d_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
 intros ([FB G] & ST & LOR & LOB & SPM & MI & Etp & AL) -> -> HV APC APLO APHI.
    assert (SPO : std_pre_o K sp tp R s CL FB lo STDIO_STACK m) by (split; [exact G|]; split; [exact ST|]; split; [exact LOR|]; split; [exact LOB|]; split; [exact SPM|]; split; [exact MI|]; split; [exact Etp| exact AL]).
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (_ & SR & _ & _ & SSP & BOK & _ & _ & _ & _ & _ & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK in *.
    sbl_pose_in SO. destruct SO as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SOI as (CH1 & FD1 & BS1 & NRD1 & NWR1 & EOF1 & RB1 & LBF1).
    pose proof (call_emit_d v) as (HF & P1 & PIECES & SMALL & RBD & HA & BYf).
    pose proof (s32_facts v) as [S32a S32b].
    pose proof (rw_cells_bound _ _ _ _ APC) as APB. cbn [cells_size csize Nat.add] in APB.
    apply (proj1 (rw_cells_app ssegs _ _ [_] [_])) in APC. destruct APC as [APC _].
    rewrite BS1 in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    unfold printf. apply implM_rd_lc.
    eapply implM_bind.
    { eapply implM_leaf.
      unfold VPRINTF_ENTRY.
      eapply (vprintf_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail FMT_D AP lo
                (str FS_EMIT_D ++ [0]) [Z_to_bv 64 v] [PA_i (s32 v)] (pieces_emit_d v) _ (rc_canary R) true true)
        with (rpos := rp) (rend := rp + zlength (f_rbuf (lc_stdout (ps_libc s)))) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC | exact FL | exact BUF | exact BP | exact WB0
             | exact BS1 | exact WBL | exact NWR1 | exact RB1
             | rewrite CH1; left; exact FD1 | exact CH1
             | apply BYf; exact MI
             | apply va_area_of_cells; exact APC
             | cbn [args_ok]; split; [split; [exact S32a | exact S32b] | exact I]
             | exact ST | exact SSP | exact MI
             | unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP in *; cbv [zlength Datatypes.length Z.of_nat Pos.of_succ_nat Pos.succ]; unfold rc_spmain in *; lia
             | idtac "VPD-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' [PO LF].
    assert (CLO : CEILZ <= lo) by (unfold rc_lo in *; lia). assert (LOS : lo <= bv_unsigned sp) by lia.
    destruct (stdout_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB m lo _ tail rp f' st' ms' G SR CLO LOS SPM RP0 RP1 GLN PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    apply implM_upd_lc_last. apply evt_done. unfold out_post.
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. eapply GIo_close. exact G'.
  Qed.
  End Sz16.
  Theorem vprintf_d_proof : ltac:(let t := eval cbv delta [vprintf_d_proof__stmt] in vprintf_d_proof__stmt in exact t).
  Proof using HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo AP v rest. ltac2:(SecDiet.SzSec.closeP 'vprintf_d_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition printf_d_gen__stmt : Prop := forall FMT (mk : Z -> list (list Z)) fs,
    (forall v, fmt_call_ok FMT (str fs ++ [0]) [PA_i (s32 v)] (mk v) (zlength (fmt_output (fmt fs) [AInt v]))) ->
    printf_d_stmt_o K FMT mk.
  Section Sz17.
  Variables FMT mk fs ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo v : ltac2:(SecDiet.SzSec.tyM 'printf_d_gen__stmt "vvvhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @FMT).
  Lemma printf_d_gen__body : ltac2:(SecDiet.SzSec.bodyP 'printf_d_gen__stmt "vvvhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros CALL SPO -> -> HV.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK in *.
    sbl_pose_in SO. destruct SO as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SOI as (CH1 & FD1 & BS1 & NRD1 & NWR1 & EOF1 & RB1 & LBF1).
    pose proof (CALL v) as (HF & P1 & PIECES & SMALL & RBD & HA & BYf).
    pose proof (s32_facts v) as [S32a S32b].
    rewrite BS1 in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    unfold s_printf, printf. apply implM_rd_lc.
    eapply implM_bind.
    { eapply implM_leaf.
      unfold PRINTF_ENTRY.
      eapply (printf_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail FMT lo
                (str fs ++ [0]) [PA_i (s32 v)] (mk v) _ (rc_canary R) true true)
        with (rpos := rp) (rend := rp + zlength (f_rbuf (lc_stdout (ps_libc s)))) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC | exact FL | exact BUF | exact BP | exact WB0
             | exact BS1 | exact WBL | exact NWR1 | exact RB1
             | rewrite CH1; left; exact FD1 | exact CH1
             | apply BYf; exact MI
             | cbn [args_ok]; split; [split; [exact S32a | exact S32b] | exact I]
             | exact ST | exact SSP | exact MI
             | unfold FPRINTF_DEPTH, GLOBALS_TOP in *; unfold rc_spmain, rc_lo in *; lia
             | idtac "PFD-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' [PO LF].
    assert (CLO : CEILZ <= lo) by (unfold rc_lo in *; lia). assert (LOS : lo <= bv_unsigned sp) by lia.
    destruct (stdout_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB m lo _ tail rp f' st' ms' G SR CLO LOS SPM RP0 RP1 GLN PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    apply implM_upd_lc_last. apply evt_done.
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz17.
  Lemma printf_d_gen : ltac:(let t := eval cbv delta [printf_d_gen__stmt] in printf_d_gen__stmt in exact t).
  Proof using HFL KST. intros FMT mk fs CALL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo v. ltac2:(SecDiet.SzSec.closeP 'printf_d_gen__body "vvvhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Theorem printf_failed_remove_proof : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt). exact (printf_d_gen _ _ _ call_failed_remove). Qed.
  Theorem printf_failed_open_proof : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt). exact (printf_d_gen _ _ _ call_failed_open). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition str_parg_bytes__stmt : Prop := forall m P (str slack : list byte),
    bytes_at ssegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
    (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
    let s := map bv_unsigned str in
    bytes_at ssegs m P (zb s ++ Z_to_bv 8 0 :: firstn (Z.to_nat (pad8 (P + zlength s + 1))) slack)
    /\ Forall (fun c => 0 < c < 256) s
    /\ (- (P + zlength s + 1)) mod 8 <= zlength (firstn (Z.to_nat (pad8 (P + zlength s + 1))) slack)
    /\ zlength (firstn (Z.to_nat (pad8 (P + zlength s + 1))) slack) = pad8 (P + zlength s + 1)
    /\ zlength s = Z.of_nat (length str).
  Section Sz20.
  Variables m P str slack : ltac2:(SecDiet.SzSec.tyM 'str_parg_bytes__stmt "vvvv" @m).
  Lemma str_parg_bytes__body : ltac2:(SecDiet.SzSec.bodyP 'str_parg_bytes__stmt "vvvv").
  Proof using Type. pin_using tt.
    intros BY NZ PAD.
 cbv zeta.
    assert (EL : zlength (map bv_unsigned str) = Z.of_nat (length str)) by (unfold zlength; rewrite length_map; reflexivity).
    rewrite EL. pose proof (pad8_range (P + Z.of_nat (length str) + 1)) as PR. unfold pad8 in PR |- *.
    remember ((- (P + Z.of_nat (length str) + 1)) mod 8) as pd eqn:Epd.
    assert (LS : zlength (firstn (Z.to_nat pd) slack) = pd) by (unfold zlength; rewrite length_firstn; lia).
    rewrite LS. split.
    { rewrite zb_unsigned. rewrite <- (firstn_skipn (Z.to_nat pd) slack) in BY.
      change (str ++ Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack ++ skipn (Z.to_nat pd) slack)
        with (str ++ (Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack) ++ skipn (Z.to_nat pd) slack) in BY.
      rewrite app_assoc in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
    split.
    { apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
      destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE]; [|lia]. exfalso. apply NZ.
      replace (Z_to_bv 8 0) with b; [exact Hb|]. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b), E. reflexivity. }
    split; [lia|]. split; [reflexivity| reflexivity].
  Qed.
  End Sz20.
  Lemma str_parg_bytes : ltac:(let t := eval cbv delta [str_parg_bytes__stmt] in str_parg_bytes__stmt in exact t).
  Proof using Type. intros m P str slack. ltac2:(SecDiet.SzSec.closeP 'str_parg_bytes__body "vvvv"). Qed.

  (* [comment removed for export] *)
  Definition str_arg_place__stmt : Prop := forall R (s : PS) (CL FB : list cblk) m SP P L lo,
    GIo K R s CL FB m -> (forall a, P <= a < P + L -> client_keeps CL SP a) -> 0 < L ->
    rc_lo R <= lo -> lo < SP ->
    0 < P /\
    ((P + L + pad8 (P + L) <= lo /\ (P + L + pad8 (P + L) <= 0x10000 \/ 0x55000 <= P)
      /\ (forall q A n, In (q, A, n) FB -> 0 < n -> P + L + pad8 (P + L) <= A \/ A + n <= P))
     \/ SP <= P).
  Section Sz21.
  Variables R s CL FB m SP P L lo : ltac2:(SecDiet.SzSec.tyM 'str_arg_place__stmt "vvvvvvvvv" @R).
  Lemma str_arg_place__body : ltac2:(SecDiet.SzSec.bodyP 'str_arg_place__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G KEEP LPOS LOR LOS.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    unfold rc_lo in LOR. pose proof (pad8_range (P + L)) as PR.
    destruct (Z_le_gt_dec SP P) as [HSP|HSP]; [split; [lia| right; exact HSP]|].
    assert (CRL : forall a, P <= a < P + L -> in_block CL a).
    { intros a Ha. destruct (KEEP a Ha) as [X|X]; [exfalso| exact X].
      destruct (KEEP P ltac:(lia)) as [Y|Y]; [lia|]. destruct (in_block_facts _ _ P BO1 Y) as (_ & Y2 & _).
      destruct (KEEP CEILZ ltac:(lia)) as [W|W]; [lia|]. destruct (in_block_facts _ _ CEILZ BO1 W) as (_ & W2 & _). lia. }
    assert (CR : client_range R CL SP P L) by (left; exact CRL).
    destruct (client_range_lo R s CL FB m SP P L lo G CR LPOS ltac:(unfold rc_lo; lia) ltac:(lia)) as (P0 & PC & P47 & PIMG).
    destruct (in_block_facts _ _ (P + L - 1) BO1 (CRL (P + L - 1) ltac:(lia))) as (_ & E2 & E3 & _).
    split; [exact P0|]. left.
    assert (C8 : CEILZ mod 8 = 0).   (* [comment removed for export] *)
    { ceil_facts. replace alloc_ceiling with (512 * (alloc_ceiling / 4096) * 8) by (pose proof (Z_div_mod_eq_full alloc_ceiling 4096); lia). apply Z_mod_mult. }
    pose proof (pad8_align (P + L) CEILZ ltac:(lia) ltac:(lia) C8) as A1.
    split; [lia|]. split.
    { destruct PIMG as [X|[X|X]]; [| right; exact X| lia]. left. pose proof (pad8_align (P + L) 0x10000 ltac:(lia) X eq_refl). lia. }
    intros q A n HIN NPOS.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.file_block_facts R CL FB q A n BOK HIN) as (B1 & B2 & B3 & B4 & B5 & B6).
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.client_range_apart R CL FB SP P L q A n BOK HIN CR LPOS ltac:(lia) NPOS) as [X|X]; [left| right; exact X].
    assert (A8 : A mod 8 = 0) by (clear -B2; Z.div_mod_to_equations; lia).
    pose proof (pad8_align (P + L) A ltac:(lia) X A8). lia.
  Qed.
  End Sz21.
  Lemma str_arg_place : ltac:(let t := eval cbv delta [str_arg_place__stmt] in str_arg_place__stmt in exact t).
  Proof using Type. intros R s CL FB m SP P L lo. ltac2:(SecDiet.SzSec.closeP 'str_arg_place__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma stderr_finish :
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (m : mem) (lo : Z) (ps : list (list Z)) (tail bufbytes : list byte)
           (f' : file_st) (st' : PS) (ms' : machine_state),
      GIo K R s CL FB m -> STDIOR (ps_libc s) FB m ->
      CEILZ <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp <= rc_spmain R ->
      firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
      rw_cells ssegs m A_STDERR_BUF [CB 0 bufbytes] ->
      fprintf_ubf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail lo (rc_canary R)
                       m s f' st' ms' ->
      mleaf (vfprintf (lc_stderr (ps_libc s)) ps) s f' st' ->
      st' = s /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom ssegs)
        /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
        /\ GIo K R (set_libc (set_stderr f' (ps_libc s)) s) CL FB m'.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros until ms'. intros G SR CLO LOS SPM GLN BUF PO LF.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    sbl_pose_in PO. destruct PO as (-> & WA' & WB' & RB' & BS' & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & flags' & mode' & m'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & FL'). sbl_subst_all.
    destruct (vfprintf_leaf_unbuffered _ _ _ _ _ BS2 LF) as [(E1 & E2 & E3 & E4 & E5 & E6 & _ & _ & _ & SW' & LB') _].
    split; [reflexivity|].
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    unfold A_STDERR, A_STDERR_BUF in *.
    assert (HW : Forall (stdio_iv R CL FB (bv_unsigned sp)) [(lo, bv_unsigned sp); (144992, 144992 + 232)]).
    { unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; [left; lia| right; right; left; lia]. }
    split.
    { eapply agrees_on_weaken; [eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia]|].
      - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; [left; lia| right; right; left; lia].
      - intros a Ha. split; [exact Ha| intros X; exact X]. }
    eapply (GIo_stdio_step R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| exact SPM|].
    cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_stderr].
    pose proof (GIo_blocks K _ _ _ _ _ G) as BOK. pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof SOI as (_ & _ & SObs & _).
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    Ltac trw2 MU WM A := eapply rw_cells_transport; [exact A | exact MU | exact WM | cbn; lia].
    split. { eapply FILE_R_transport; [exact SO| exact MU| exact WM| | | rewrite SObs; unfold BUFSIZ; lia].
             - repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
             - rewrite SObs. unfold BUFSIZ. repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil. }
    split; [exact SOI|].
    split.
    { exists flags', mode', 0, tail, bufbytes.
      rewrite WA', RB', BS', WB'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      split; [exact FC'|]. split; [exact FL'|]. split; [trw2 MU WM BUF|]. split; [reflexivity|]. split; [intros _; reflexivity|]. split; [lia|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN]. }
    split.
    { unfold stderr_inv. rewrite E1, E2, E3, E4, E5, E6, RB'.
      split; [exact CH2|]. split; [exact FD2|]. split; [reflexivity|]. split; [exact ND2|]. split; [exact NW2|]. split; [exact EOF2|]. split; [reflexivity|].
      split.
      - destruct (f_stdoutw f'); [| reflexivity]. exfalso. pose proof (SW' eq_refl) as X. rewrite SW2 in X. discriminate X.
      - destruct (f_lbf_nl f'); [| reflexivity]. exfalso. pose proof (LB' eq_refl) as X. rewrite LB2 in X. discriminate X. }
    split. { eapply rw_cells_transport; [exact SIN | exact MU | exact WM |]. unfold stdin_cells. rewrite file_cells_size. cbn. lia. }
    split; [trw2 MU WM U1|]. split; [trw2 MU WM U2|]. split; [trw2 MU WM U3|]. split; [trw2 MU WM OL|]. split; [trw2 MU WM OH|].
    split; [| exact ND].
    eapply files_R_transport; [exact FS| exact MU| exact WM|].
    apply Forall_forall. intros [lo' hi'] Hiv. apply Forall_forall. intros [[q' A'] n'] Hb. cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) BO2 _ Hb) as (K1 & K2 & K3 & K4 & K5 & K6). unfold cb_addr, cb_size in *. cbn [fst snd] in *.
    cbn in Hiv. destruct Hiv as [E|[E|[]]]; injection E as <- <-; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition eprintf_too_big_proof__stmt : Prop := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.eprintf_i_stmt K FMT_TOO_BIG 0x4000000 pieces_too_big.
  Section Sz22.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo : ltac2:(SecDiet.SzSec.tyM 'eprintf_too_big_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma eprintf_too_big_proof__body : ltac2:(SecDiet.SzSec.bodyP 'eprintf_too_big_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
 intros ([FB G] & ST & LOR & LOB & SPM & MI & Etp & AL) -> -> ->.
    assert (SPO : std_pre_o K sp tp R s CL FB lo STDIO_STACK m) by (split; [exact G|]; split; [exact ST|]; split; [exact LOR|]; split; [exact LOB|]; split; [exact SPM|]; split; [exact MI|]; split; [exact Etp| exact AL]).
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (_ & SR & _ & _ & SSP & BOK & _ & _ & _ & _ & _ & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK, STDERR_FILE in *.
    sbl_pose_in SE. destruct SE as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    assert (WBN : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. rewrite BS2 in WBL. unfold zlength in WBL. cbn [Datatypes.length] in WBL. lia. }
    rewrite BS2, RB2, WBN in FC. rewrite BS2 in BUF. change (zlength (@nil Z)) with 0 in FC. rewrite RB2 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    pose proof call_too_big as (HF & P1 & PIECES & SMALL & RBD & HA & BYf).
    pose proof (u32_facts 0x4000000) as U32.
    assert (CLO : CEILZ <= lo) by (unfold rc_lo in *; lia). assert (LOS : lo <= bv_unsigned sp) by lia.
    unfold eprintf. apply implM_rd_lc.
    eapply implM_bind.
    { eapply implM_leaf.
      unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.FPRINTF_ENTRY. change A_STDERR with 144992 in FC.
      eapply (fprintf_ubf_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 144992 A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail FMT_TOO_BIG lo
                (str FS_TOO_BIG ++ [0]) [PA_u (u32 0x4000000)] pieces_too_big _ (rc_canary R))
        with (rpos := rp) (flags := flags) (mode := mode).
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC | exact FL
             | exact BS2 | exact NW2 | exact RB2 | exact WBN | exact CH2 | right; exact FD2 | exact SW2
             | apply BYf; exact MI
             | cbn [args_ok]; split; [exact U32 | exact I]
             | exact ST | exact SSP | exact MI
             | unfold FPRINTF_DEPTH, GLOBALS_TOP, A_STDERR_BUF in *; unfold rc_spmain, rc_lo in *;
               try destruct (f_wactive (lc_stderr (ps_libc s))); (keep_hyps CEILV sp lo LOB CLO R SPM SP47 rp RP0 RP1; lia)
             | idtac "EPI-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' [PO LF].
    destruct (stderr_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB m lo _ tail bufbytes f' st' ms' G SR CLO LOS SPM GLN BUF PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    apply implM_upd_lc_last. apply evt_done. unfold out_post.
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. eapply GIo_close. exact G'.
  Qed.
  End Sz22.
  Theorem eprintf_too_big_proof : ltac:(let t := eval cbv delta [eprintf_too_big_proof__stmt] in eprintf_too_big_proof__stmt in exact t).
  Proof using HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo. ltac2:(SecDiet.SzSec.closeP 'eprintf_too_big_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Lemma eprintf_s_gen : forall FMT (mk : list Z -> list (list Z)) fs,
    (forall sv, zlength sv <= 2^24 -> fmt_call_ok FMT (str fs ++ [0]) [PA_s sv] (mk sv) (zlength (fmt_output (fmt fs) [AStr sv]))) ->
    OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47.eprintf_s_stmt47 K FMT mk.   (* [comment removed for export] *)
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros FMT mk fs CALL.
    intros until slack. intros ([FB G] & ST & LOR & LOB & SPM & MI & Etp & AL) -> -> -> BY NZ LEN PAD KEEP S47.   (* [comment removed for export] *)
    assert (SPO : std_pre_o K sp tp R s CL FB lo STDIO_STACK m) by (split; [exact G|]; split; [exact ST|]; split; [exact LOR|]; split; [exact LOB|]; split; [exact SPM|]; split; [exact MI|]; split; [exact Etp| exact AL]).
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (_ & SR & _ & _ & SSP & BOK & _ & _ & _ & _ & _ & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK, STDERR_FILE in *.
    sbl_pose_in SE. destruct SE as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    assert (WBN : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. rewrite BS2 in WBL. unfold zlength in WBL. cbn [Datatypes.length] in WBL. lia. }
    rewrite BS2, RB2, WBN in FC. rewrite BS2 in BUF. change (zlength (@nil Z)) with 0 in FC. rewrite RB2 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_app in PB. cbn [Datatypes.length] in PB.
    pose proof (str_parg_bytes m P str slack BY NZ PAD) as SPB. cbv zeta in SPB. sbl_pose_in SPB. destruct SPB as (BY' & FA & PAD' & LS & EL). sbl_subst_all.
    rewrite EL in *.
    pose proof (CALL (map bv_unsigned str) ltac:(rewrite EL; lia)) as (HF & P1 & PIECES & SMALL & RBD & HA & BYf).
    assert (CLO : CEILZ <= lo) by (unfold rc_lo in *; lia). assert (LOS : lo <= bv_unsigned sp) by lia.
    assert (KEEP' : forall a, P <= a < P + (Z.of_nat (length str) + 1) -> client_keeps CL (bv_unsigned sp) a) by (intros a Ha; apply KEEP; lia).
    destruct (str_arg_place R s CL FB m (bv_unsigned sp) P (Z.of_nat (length str) + 1) lo G KEEP' ltac:(lia) LOR ltac:(lia)) as [P0 PLACE].
    assert (EPD : pad8 (P + Z.of_nat (length str) + 1) = pad8 (P + (Z.of_nat (length str) + 1))) by (f_equal; lia).
    rewrite EPD in *. pose proof (pad8_range (P + (Z.of_nat (length str) + 1))) as PR.
    unfold eprintf. apply implM_rd_lc.
    eapply implM_bind.
    { eapply implM_leaf.
      unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.FPRINTF_ENTRY. change A_STDERR with 144992 in FC.
      eapply (fprintf_ubf_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 144992 A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail FMT lo
                (Fmt.str fs ++ [0]) [PA_s (map bv_unsigned str)] (mk (map bv_unsigned str)) _ (rc_canary R))
        with (rpos := rp) (flags := flags) (mode := mode).
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC | exact FL
             | exact BS2 | exact NW2 | exact RB2 | exact WBN | exact CH2 | right; exact FD2 | exact SW2
             | apply BYf; exact MI
             | cbn [args_ok]; split; [| exact I]; cbn [arg_ok]; rewrite (unsigned_lit P) by (keep_hyps CEILV sp P str slack S47 P0; lia); rewrite ?EL;
               eexists; split; [exact BY'|]; split; [exact FA|]; split; [exact PAD'|]; split; [exact P0|]; rewrite LS;
               unfold GLOBALS_TOP in *; unfold rc_spmain, rc_lo in *;
               destruct PLACE as [(Q1 & Q2 & Q3) | Q]; [| repeat split; first [right; (keep_hyps CEILV sp P str slack Q lo LOB CLO; lia) | (keep_hyps CEILV sp P str slack S47; lia)]];
               split; [left; (keep_hyps CEILV sp lo P str slack Q1; lia)|]; split; [clear -Q2 PR; destruct Q2; [left; (keep_hyps P str H; lia)| right; (keep_hyps P H; lia)] |]; split; [left; (keep_hyps CEILV sp lo P str slack LOB Q1; lia)|]; split; [left; (keep_hyps CEILV sp lo P str slack LOB Q1; lia) | (keep_hyps CEILV sp P str slack S47; lia)]
             | exact ST | exact SSP | exact MI
             | unfold FPRINTF_DEPTH, GLOBALS_TOP, A_STDERR_BUF in *; unfold rc_spmain, rc_lo in *;
               try destruct (f_wactive (lc_stderr (ps_libc s))); (keep_hyps CEILV sp lo P str slack LOB CLO R SPM SP47 rp RP0 RP1; lia)
             | idtac "EPS-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' [PO LF].
    destruct (stderr_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB m lo _ tail bufbytes f' st' ms' G SR CLO LOS SPM GLN BUF PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    apply implM_upd_lc_last. apply evt_done. unfold out_post.
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. eapply GIo_close. exact G'.
  Qed.

  Theorem eprintf_usage_proof : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47.eprintf_s_stmt47 K FMT_USAGE pieces_usage.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt). exact (eprintf_s_gen _ _ _ call_usage). Qed.
  Theorem eprintf_cannot_open_proof : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47.eprintf_s_stmt47 K FMT_CANNOT_OPEN pieces_cannot_open.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt). exact (eprintf_s_gen _ _ _ call_cannot_open). Qed.
  Theorem eprintf_read_error_proof : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47.eprintf_s_stmt47 K FMT_READ_ERROR pieces_read_error.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt). exact (eprintf_s_gen _ _ _ call_read_error). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Notation eqb := (ho_eqb HO).

  Lemma hfile_finish :
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (m : mem) (lo : Z) (ps : list (list Z)) (q : hptr) (Af : Z) (f : file_st) (pv nx : Z)
           (tail : list byte) (rp : Z) (f' : file_st) (st' : PS) (ms' : machine_state),
      GIo K R s CL FB m -> STDIOR (ps_libc s) FB m -> In (q, Af, FILE_BLOCK) FB ->
      heap_file_inv f -> f_nowr f = false ->
      (forall m' f', FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
         (forall q2 A2 n2 f2 pv2 nx2, In (q2, A2, n2) FB -> q2 <> q ->
            FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2 -> heap_file_inv f2 ->
            FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2) ->
         files_R m' 0 (files_update eqb (lc_files (ps_libc s)) q f') FB) ->
      CEILZ <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp <= rc_spmain R ->
      0 <= rp -> rp + zlength (f_rbuf f) < 2^63 -> firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
      fprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx tail lo
                        (rc_canary R) true false rp (rp + zlength (f_rbuf f)) m s f' st' ms' ->
      mleaf (vfprintf f ps) s f' st' ->
      st' = s /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom ssegs)
        /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
        /\ GIo K R (set_libc (set_files (files_update eqb (lc_files (ps_libc s)) q f') (ps_libc s)) s) CL FB m'.
  Proof using EQB HFL KST. pin_using (fun (EQB HFL KST : unit) => tt).
    intros until ms'. intros G SR HIN INV NOWR UPD CLO LOS SPM RP0 RP1 GLN PO LF.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    assert (RBN : f_rbuf f = []) by (apply NORDi; rewrite NRW, NOWR; reflexivity).
    rewrite RBN in RP1. change (zlength (@nil Z)) with 0 in RP1.
    sbl_pose_in PO. destruct PO as (-> & INV' & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & flags' & mode' & bufbytes' & m' & rpos' & rend'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & RP' & FL' & BUF' & BP' & WBL'). sbl_subst_all.
    assert (BSnz : f_bufsize f <> 0) by (rewrite BS; unfold BUFSIZ; lia).
    pose proof (vfprintf_leaf_buffered _ _ _ _ _ BSnz LF) as [FX _].
    pose proof INV' as (WA' & RB' & BS' & NW' & FDC' & _ & CHN').
    pose proof (GIo_blocks K _ _ _ _ _ G) as BOK.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.file_block_facts R CL FB q Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold FILE_BLOCK, FILE_BUF_OFF in *.
    split; [reflexivity|].
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    assert (HW : Forall (stdio_iv R CL FB (bv_unsigned sp)) [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]).
    { unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
      - left. lia.
      - right; left. unfold iv_in_block. apply Exists_exists. exists (q, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
      - right; left. unfold iv_in_block. apply Exists_exists. exists (q, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia]. }
    split.
    { eapply agrees_on_weaken.
      - eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
        + left. lia.
        + right; left. unfold iv_in_block. apply Exists_exists. exists (q, Af, 1264). split; [exact HIN| cbn; lia].
        + right; left. unfold iv_in_block. apply Exists_exists. exists (q, Af, 1264). split; [exact HIN| cbn; lia].
      - intros a Ha. split; [exact Ha| intros X; exact X]. }
    eapply (GIo_stdio_step R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| exact SPM|].
    cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
    assert (AGS : agrees_on (fun a => GI.stdio_static a) m m').
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. unfold GI.stdio_static in Hs. cbn [outside]. lia. }
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
    Ltac trs3 AGS A := eapply agrees_rw_cells; [exact AGS | exact A | intros a Ha; unfold GI.stdio_static; cbn in Ha; lia].
    split. { eapply FILE_R_agree; [exact SO | exact AGS | intros a Ha; unfold GI.stdio_static; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; unfold GI.stdio_static; lia]. }
    split; [exact SOI|].
    split. { eapply FILE_R_agree; [exact SE | exact AGS | intros a Ha; unfold GI.stdio_static; lia | rewrite SEbs; intros a Ha; unfold GI.stdio_static; lia]. }
    split; [exact SEI|].
    split. { eapply agrees_rw_cells; [exact AGS | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; unfold GI.stdio_static; lia. }
    split; [trs3 AGS U1|]. split; [trs3 AGS U2|]. split; [trs3 AGS U3|]. split; [trs3 AGS OL|]. split; [trs3 AGS OH|].
    split.
    2:{ rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.files_update_keys. exact ND. }
    apply UPD.
    - (* [comment removed for export] *)
      exists flags', mode', rpos', tail, bufbytes'.
      rewrite WA', RB', BS'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      assert (Erend : rend' = rpos') by (rewrite RBN in RP'; change (zlength (@nil Z)) with 0 in RP'; lia).
      rewrite Erend in FC'.
      split; [exact FC'|]. split; [exact FL'|]. split; [exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [exact WBL'|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN].
    - exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.heap_file_inv_fx f f' INV NOWR FX).
    - (* [comment removed for export] *)
      intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2 FR2 INV2.
      pose proof INV2 as (_ & _ & BS2 & _).
      destruct (files_R_focus m 0 (lc_files (ps_libc s)) FB q2 A2 n2 FS ND HIN2) as (f2' & pv2' & nx2' & _ & En2 & _). subst n2.
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.file_block_facts R CL FB q2 A2 FILE_ALLOC BOK HIN2) as (B1 & B2 & B3 & B4 & B5 & B6). unfold FILE_ALLOC in B3, B4, B5, B6.
      assert (AP : A2 + 1264 <= Af \/ Af + 1264 <= A2).
      { destruct (GIo_apart K R s CL FB m (q2, A2, FILE_ALLOC) (q, Af, 1264) G ltac:(apply in_or_app; right; exact HIN2) ltac:(apply in_or_app; right; exact HIN)) as [E|AP].
        - exfalso. apply NE2. congruence.
        - unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
      eapply (FILE_R_agree (fun a => A2 <= a < A2 + 1264)); [exact FR2| | intros a Ha; lia | intros a Ha; rewrite BS2 in Ha; unfold BUFSIZ in Ha; lia].
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hb. cbn [outside]. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vfprintf_nowr_unr : forall (fs0 : file_st) ps (s : PS) (Q : unit -> PS -> machine_state -> Prop) ms h,
    heap_file_inv fs0 -> f_nowr fs0 = true ->
    implM ssegs (mbind (vfprintf fs0 ps) (store_file ps_libc set_libc eqb h)) s Q ms.
  Proof using Type. pin_using tt.
    intros fs0 ps s Q ms h INV NOWR. pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    destruct (NOWRi NOWR) as [WACT _].
    unfold vfprintf. rewrite BS. change (BUFSIZ =? 0) with false. cbv iota.
    unfold ensure_w. rewrite WACT. unfold towrite. rewrite NOWR.
    apply implM_bind_assoc. cbn [mbind munr ebind bind]. apply implM_unr.
  Qed.

  Definition fprintf_packet_length_proof__stmt : Prop := fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Section Sz26.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo v1 v2 : ltac2:(SecDiet.SzSec.tyM 'fprintf_packet_length_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fprintf_packet_length_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_packet_length_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB HFL KST. pin_using (fun (EQB HFL KST : unit) => tt).
    intros SPO HIN -> -> -> -> HV1 HV2.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs0 & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.file_block_facts R CL FB f Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold STDIO_STACK in *. unfold FILE_BLOCK in FA3, FA4, FA5, FA6.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    unfold s_fprintf, Stdio.fprintf, with_file_.
    eapply implM_lookup_file; [exact LK|].
    destruct (f_nowr fs0) eqn:NOWR; [apply vfprintf_nowr_unr; [exact INV| exact NOWR]|].
    assert (RBN : f_rbuf fs0 = []) by (apply NORDi; rewrite NRW; reflexivity).
    sbl_pose_in FR. destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    rewrite BS in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    pose proof (call_packet_length v1 v2) as (HF & P1 & PIECES & SMALL & RBD & HA & BYf).
    pose proof (s32_facts_sx v1 HV1) as [S1a S1b]. pose proof (s32_facts_sx v2 HV2) as [S2a S2b].
    assert (CLO : CEILZ <= lo) by (unfold rc_lo in *; lia). assert (LOS : lo <= bv_unsigned sp) by lia.
    eapply implM_bind.
    { eapply implM_leaf. unfold FPRINTF_ENTRY.
      eapply (fprintf_file_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx tail
                FMT_PACKET_LENGTH lo (str FS_PACKET_LENGTH ++ [0]) [PA_i (s32 v1); PA_i (s32 v2)] (pieces_packet_length v1 v2) _ (rc_canary R) true false)
        with (rpos := rp) (rend := rp + zlength (f_rbuf fs0)) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC | exact FL | exact BUF | exact BP | exact WB0
             | exact BS | exact WBL | exact NOWR | exact RBN
             | rewrite NCH; exact FD | exact NCH | intros _; reflexivity
             | apply BYf; exact MI
             | cbn [args_ok]; split; [split; [exact S1a | exact S1b] |]; split; [split; [exact S2a | exact S2b] | exact I]
             | exact ST | exact SSP | exact MI
             | unfold FPRINTF_DEPTH, GLOBALS_TOP, FILE_BUF_OFF in *; unfold rc_spmain, rc_lo in *; (keep_hyps CEILV sp Af lo v1 v2 LOB CLO R SPM SP47 A0 FA4 FA5; lia)
             | idtac "FPL-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' [PO LF].
    destruct (hfile_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB m lo _ f Af fs0 pv nx tail rp f' st' ms' G SR HIN INV NOWR UPD CLO LOS SPM RP0 RP1 GLN PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    unfold store_file. apply implM_upd_lc_last. apply evt_done.
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz26.
  Theorem fprintf_packet_length_proof : ltac:(let t := eval cbv delta [fprintf_packet_length_proof__stmt] in fprintf_packet_length_proof__stmt in exact t).
  Proof using EQB HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo v1 v2. ltac2:(SecDiet.SzSec.closeP 'fprintf_packet_length_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fprintf_couldnt_open_proof__stmt : Prop := fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Section Sz27.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo P str slack : ltac2:(SecDiet.SzSec.tyM 'fprintf_couldnt_open_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fprintf_couldnt_open_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_couldnt_open_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB HFL KST. pin_using (fun (EQB HFL KST : unit) => tt).
    intros SPO HIN -> -> -> BY NZ LEN PAD CR.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs0 & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.file_block_facts R CL FB f Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold STDIO_STACK in *. unfold FILE_BLOCK in FA3, FA4, FA5, FA6.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    unfold s_fprintf, Stdio.fprintf, with_file_.
    eapply implM_lookup_file; [exact LK|].
    destruct (f_nowr fs0) eqn:NOWR; [apply vfprintf_nowr_unr; [exact INV| exact NOWR]|].
    assert (RBN : f_rbuf fs0 = []) by (apply NORDi; rewrite NRW; reflexivity).
    sbl_pose_in FR. destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    rewrite BS in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_app in PB. cbn [Datatypes.length] in PB.
    pose proof (str_parg_bytes m P str slack BY NZ PAD) as SPB. cbv zeta in SPB. sbl_pose_in SPB. destruct SPB as (BY' & FA & PAD' & LS & EL). sbl_subst_all.
    rewrite EL in *.
    pose proof (call_couldnt_open (map bv_unsigned str) ltac:(rewrite EL; lia)) as (HF & P1 & PIECES & SMALL & RBD & HA & BYf).
    assert (CLO : CEILZ <= lo) by (unfold rc_lo in *; lia). assert (LOS : lo <= bv_unsigned sp) by lia.
    assert (KEEP' : forall a, P <= a < P + (Z.of_nat (length str) + 1) -> client_keeps CL (bv_unsigned sp) a).
    { intros a Ha. destruct CR as [CR1|[CR1 CR2]]; [right; apply CR1; lia | left; lia]. }
    destruct (str_arg_place R s CL FB m (bv_unsigned sp) P (Z.of_nat (length str) + 1) lo G KEEP' ltac:(lia) LOR ltac:(lia)) as [P0 PLACE].
    assert (EPD : pad8 (P + Z.of_nat (length str) + 1) = pad8 (P + (Z.of_nat (length str) + 1))) by (f_equal; lia).
    rewrite EPD in *. pose proof (pad8_range (P + (Z.of_nat (length str) + 1))) as PR.
    assert (AOK : args_ok Af 232 (Af + FILE_BUF_OFF) 1024 m lo (bv_unsigned sp) (bv_unsigned sp - 448) [Z_to_bv 64 P; a3; a4; a5; a6; a7] [PA_s (map bv_unsigned str)]).
    { cbn [args_ok]. split; [| exact I]. cbn [arg_ok]. rewrite (unsigned_lit P) by lia. rewrite ?EL.
      eexists. split; [exact BY'|]. split; [exact FA|]. split; [exact PAD'|]. split; [exact P0|]. rewrite LS.
      unfold GLOBALS_TOP, FILE_BUF_OFF in *. unfold rc_spmain, rc_lo in *.
      assert (P47 : P + Z.of_nat (length str) <= 2^47).   (* [comment removed for export] *)
      { destruct CR as [CR1|[CR1 CR2]]; [| unfold rc_spmain in *; lia].
        destruct (client_range_lo R s CL FB m (bv_unsigned sp) P (Z.of_nat (length str) + 1) lo G (or_introl CR1) ltac:(lia) LOR ltac:(lia)) as (_ & _ & C3 & _). lia. }
      destruct PLACE as [(Q1 & Q2 & Q3) | Q]; [| repeat split; fastfirst (first [right; lia | lia])].
      pose proof (Q3 f Af FILE_BLOCK HIN ltac:(unfold FILE_BLOCK; lia)) as Q4. unfold FILE_BLOCK in Q4.
      destruct Q4 as [Q4|Q4].
      - split; [left; lia|]. split; [left; lia|]. split; [left; lia|]. split; [left; lia | lia].
      - split; [left; lia|]. split; [right; lia|]. split; [right; lia|]. split; [left; lia | lia]. }
    eapply implM_bind.
    { eapply implM_leaf. unfold FPRINTF_ENTRY.
      eapply (fprintf_file_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx tail
                FMT_COULDNT_OPEN lo (Fmt.str FS_COULDNT_OPEN ++ [0]) [PA_s (map bv_unsigned str)] (pieces_couldnt_open (map bv_unsigned str)) _ (rc_canary R) true false)
        with (rpos := rp) (rend := rp + zlength (f_rbuf fs0)) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC | exact FL | exact BUF | exact BP | exact WB0
             | exact BS | exact WBL | exact NOWR | exact RBN
             | rewrite NCH; exact FD | exact NCH | intros _; reflexivity
             | apply BYf; exact MI
             | exact AOK
             | exact ST | exact SSP | exact MI
             | unfold FPRINTF_DEPTH, GLOBALS_TOP, FILE_BUF_OFF in *; unfold rc_spmain, rc_lo in *; (keep_hyps CEILV sp Af lo P str slack LOB CLO R SPM SP47 A0 FA4 FA5; lia)
             | idtac "FCO-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' [PO LF].
    destruct (hfile_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB m lo _ f Af fs0 pv nx tail rp f' st' ms' G SR HIN INV NOWR UPD CLO LOS SPM RP0 RP1 GLN PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    unfold store_file. apply implM_upd_lc_last. apply evt_done.
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz27.
  Theorem fprintf_couldnt_open_proof : ltac:(let t := eval cbv delta [fprintf_couldnt_open_proof__stmt] in fprintf_couldnt_open_proof__stmt in exact t).
  Proof using EQB HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo P str slack. ltac2:(SecDiet.SzSec.closeP 'fprintf_couldnt_open_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Glue.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.Strings.String Stdlib.Strings.Ascii Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_printf_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.Stdio_glue_sn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Printf_fsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_vfprintf_file.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.F_fprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Vfprintf_leaf.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sbl_is_big n := lazymatch n with S _ => let b := eval vm_compute in (Nat.leb 200 n) in lazymatch b with true => idtac end end.
Local Ltac sbl_pose_in H :=
  (let T := type of H in let T' := eval hnf in T in change T' in H);
  repeat match type of H with
  | context [repeat ?b ?n] => sbl_is_big n; let z := fresh "sblz" in pose (z := repeat b n); change (repeat b n) with z in H
  | context [CB ?n _] => sbl_is_big n; let x := fresh "sblv" in pose (x := n); change n with x in H
  end.
Local Ltac sbl_subst_all :=
  repeat match goal with
  | z := repeat _ ?n |- _ => sbl_is_big n; subst z
  | x := ?n |- _ => sbl_is_big n; subst x
  end.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma fmt_pieces_small_aux : forall fuel s args,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true ->
  Forall (fun p => zlength p <= zlength s + 80 + fargs_len args) (fmt_pieces (parse_fmt_aux fuel s) args).
Proof using Type. pin_using tt.
  induction fuel as [|f IH]; intros s args Hlen OK.
  - destruct s as [|c s0]; [| cbn in Hlen; lia]. cbn. constructor.
  - destruct s as [|c s0]. { cbn. constructor. }
    cbn in Hlen. pose proof (fargs_len_nonneg args) as AN. destruct (Z.eqb_spec c 37) as [E37|N37].
    + subst c. rewrite parse_pct_shape in *.
      destruct (parse_conv s0) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. destruct args as [|a args']; [discriminate|]. apply andb_prop in OK as [OKc OK].
      cbn [fmt_pieces hd tl]. pose proof (conv_len_bound cv a OKc) as CB. unfold conv_len in CB.
      assert (LR : (List.length r' < S (List.length s0))%nat).
      { pose proof (parse_conv_cases _ _ _ PC) as SH. destruct cv;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; cbn [List.length]; lia. }
      pose proof (IH r' args' ltac:(lia) OK) as IHr. pose proof (fargs_len_nonneg args') as AN'.
      constructor; [change (zlength (@nil Z)) with 0; cbn [fargs_len]; destruct a as [z|cs]; cbn; [| pose proof (zlength_nonneg cs)]; unfold zlength in *; cbn [length]; lia|].
      apply Forall_app. split.
      * apply Forall_forall. intros pc Hpc. pose proof (in_split _ _ Hpc) as (l1 & l2 & E).
        assert (zlength pc <= zlength (List.concat (Fmt.conv_pieces cv a))).
        { rewrite E, concat_app. cbn [List.concat]. rewrite !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app. pose proof (zlength_nonneg (List.concat l1)). pose proof (zlength_nonneg (List.concat l2)). lia. }
        cbn [fargs_len]. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
      * eapply Forall_impl; [| exact IHr]. cbv beta. intros pc Hpc. cbn [fargs_len]. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons.
        pose proof (zlength_nonneg r'). destruct a as [z|cs]; cbn; [| pose proof (zlength_nonneg cs)]; unfold zlength in *; lia.
    + rewrite (parse_lit_shape f c s0 N37) in *.
      destruct (take_lit (c :: s0)) as [l r] eqn:TL. destruct (take_lit_spec _ _ _ TL) as (E1 & N1 & R1).
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. apply andb_prop in OK as [OKl OK].
      cbn [fmt_pieces]. pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
      assert (Hl : (1 <= List.length l)%nat).
      { destruct l as [|c' l0]; [| cbn; lia]. exfalso. cbn in E1. destruct R1 as [->|[r'' ->]]; [discriminate E1|]. injection E1 as E _. exact (N37 E). }
      pose proof (IH r args ltac:(lia) OK) as IHr.
      constructor; [rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons; unfold zlength in *; lia|].
      eapply Forall_impl; [| exact IHr]. cbv beta. intros pc Hpc. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
Qed.

Lemma fmt_pieces_small : forall fs args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> zlength (str fs) + 80 + fargs_len args <= PIECE_MAX -> pieces_small (fmt_pieces (fmt fs) args).
Proof using Type. pin_using tt.
  intros fs args OK B. unfold pieces_small. eapply Forall_impl; [| apply fmt_pieces_small_aux; [unfold fmt, parse_fmt; lia | exact OK]].
  cbv beta. intros p Hp. unfold fmt, parse_fmt in B. lia.
Qed.

(* [comment removed for export] *)
Definition fmt_facts__stmt : Prop := forall fs args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> (length args <= 2)%nat -> Forall (fun a => farg_len a <= 2^24) args ->
  zlength (str fs) < 4096 ->
  Forall (fun c => 0 <= c < 256) (str fs ++ [0])
  /\ pass1_ok (str fs ++ [0]) = true
  /\ printf_pieces (str fs ++ [0]) (to_pargs (fmt fs) args) = Some (fmt_pieces (fmt fs) args, zlength (fmt_output (fmt fs) args))
  /\ pieces_small (fmt_pieces (fmt fs) args)
  /\ 0 <= zlength (fmt_output (fmt fs) args) < 2^31 - 1.
Section Sz3.
Variables fs : ltac2:(SecDiet.SzSec.tyM 'fmt_facts__stmt "vk" @fs).
Lemma fmt_facts__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_facts__stmt "vk").
Proof using Type. pin_using tt.
  intros args OK L2 SM FL.
  assert (FL4 : fargs_len args <= 2 * (80 + 2^24)).
  { clear -SM L2. destruct args as [|a [|b [|c args]]]; cbn [length] in L2; [cbn; lia| | |lia].
    - inversion SM; subst. cbn [fargs_len]. lia.
    - inversion SM as [|a' l Ha SM']; subst. inversion SM'; subst. cbn [fargs_len]. lia. }
  pose proof (fmt_output_bound fs args OK) as OB. pose proof (fmt_output_nonneg (fmt fs) args) as ON.
  split; [apply str_range|]. split; [apply (fmt_pass1 fs args OK); unfold INT_MAX; lia|].
  split; [apply fmt_bridge; [exact OK| unfold INT_MAX; lia]|].
  split; [apply fmt_pieces_small; [exact OK| unfold PIECE_MAX; lia]|]. lia.
Qed.
End Sz3.
Lemma fmt_facts : ltac:(let t := eval cbv delta [fmt_facts__stmt] in fmt_facts__stmt in exact t).
Proof using Type. intros fs args. ltac2:(SecDiet.SzSec.closeP 'fmt_facts__body "vk"). Qed.

(* [comment removed for export] *)
Definition fmt_static (fs : string) (A : Z) : Prop :=
  ro_bytes_b usegs A (zb (str fs ++ [0])) = true /\ 65536 <= A /\ A + zlength (str fs ++ [0]) <= 77824.
Lemma fmt_bytes : forall m fs A, mem_inv usegs m -> fmt_static fs A -> bytes_at usegs m A (zb (str fs ++ [0])).
Proof using Type. pin_using tt.
  intros m fs A MI (RO & LO & HI). unfold zlength in HI.
  pose proof (ro_cells_image usegs m A _ MI RO ltac:(lia)) as X. rewrite zb_length in X.
  pose proof (ro_cells_bytes_at _ _ _ _ (X ltac:(lia))) as Y. cbn [cells_bytes cbytes] in Y. rewrite app_nil_r in Y. exact Y.
Qed.

(* [comment removed for export] *)
Lemma s32_facts_sx : forall v, 0 <= v < 2^32 ->
  -2^31 <= s32 v < 2^31 /\ bv_unsigned (sx32 (Z_to_bv 64 v)) mod 2^32 = s32 v mod 2^32.
Proof using Type. pin_using tt.
  intros v Hv. pose proof (s32_facts v) as [R E]. split; [exact R|]. rewrite <- E.
  unfold sx32. rewrite (unsigned_lit v) by lia. rewrite unsigned_lit_wrap, mod32_of_mod64.
  rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB.bv_swrap32_eq.
  replace ((v + 2^31) mod 2^32 - 2^31) with (v - ((v + 2^31) / 2^32) * 2^32) by (Z.div_mod_to_equations; lia).
  rewrite <- Zminus_mod_idemp_r, Z_mod_mult, Z.sub_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fmt_call_ok (FMT : Z) (fmtz : list Z) (pargs : list parg) (ps : list (list Z)) (r : Z) : Prop :=
  Forall (fun c => 0 <= c < 256) fmtz /\ pass1_ok fmtz = true /\ printf_pieces fmtz pargs = Some (ps, r) /\ pieces_small ps
  /\ 0 <= r < 2^31 - 1 /\ (65536 <= FMT /\ FMT + zlength fmtz <= 77824)
  /\ (forall m, mem_inv usegs m -> bytes_at usegs m FMT (zb fmtz)).

Lemma fmt_call_ok_intro : forall fs FMT args,
  fmt_static fs FMT -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> (length args <= 2)%nat ->
  Forall (fun a => farg_len a <= 2^24) args -> zlength (str fs) < 4096 ->
  fmt_call_ok FMT (str fs ++ [0]) (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args) (zlength (fmt_output (fmt fs) args)).
Proof using Type. pin_using tt.
  intros fs FMT args FS OK L2 SM FL.
  destruct (fmt_facts fs args OK L2 SM FL) as (HF & P1 & PIECES & SMALL & RB).
  pose proof FS as (RO & LO & HI).
  split; [exact HF|]. split; [exact P1|]. split; [exact PIECES|]. split; [exact SMALL|]. split; [exact RB|].
  split; [split; [exact LO| exact HI]|]. intros m MI. exact (fmt_bytes m fs FMT MI FS).
Qed.
End WithCeil.


Local Open Scope string_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Definition FS_EMIT_D : string := "%d
".
Definition FS_FAILED_REMOVE : string := "failed remove, errno=%d
".
Definition FS_FAILED_OPEN : string := "failed open, errno=%d
".
Definition FS_COULDNT_OPEN : string := "Couldn't open pcap file %s
".
Definition FS_PACKET_LENGTH : string := "packet length=%d/%d
".
Definition FS_USAGE : string := "usage: %s INPUT
".
Definition FS_CANNOT_OPEN : string := "cli: cannot open %s
".
Definition FS_READ_ERROR : string := "cli: read error on %s
".
Definition FS_TOO_BIG : string := "cli: input >= %u bytes, refused
".
End WithCeil.

Local Close Scope string_scope.

Local Ltac fmt_call fs args :=
  lazymatch goal with |- fmt_call_ok ?FMT ?fz _ _ _ =>
    change (fmt_call_ok FMT fz (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args) (zlength (fmt_output (fmt fs) args)))
  end;
  apply fmt_call_ok_intro;
    [ split; [vm_compute; reflexivity | vm_compute; split; intros HH; discriminate HH]
    | vm_compute; reflexivity
    | cbn [length]; lia
    | repeat constructor; cbn [farg_len]; try assumption; try lia
    | vm_compute; reflexivity ].

Section WithCeil.
Context {CEILV : CEIL}.
Lemma call_emit_d : forall v,
  fmt_call_ok FMT_D (str FS_EMIT_D ++ [0]) [PA_i (s32 v)] (pieces_emit_d v) (zlength (fmt_output (fmt FS_EMIT_D) [AInt v])).
Proof using Type. pin_using tt. intros v. fmt_call FS_EMIT_D [AInt v]. Qed.
Lemma call_failed_remove : forall v,
  fmt_call_ok FMT_FAILED_REMOVE (str FS_FAILED_REMOVE ++ [0]) [PA_i (s32 v)] (pieces_failed_remove v) (zlength (fmt_output (fmt FS_FAILED_REMOVE) [AInt v])).
Proof using Type. pin_using tt. intros v. fmt_call FS_FAILED_REMOVE [AInt v]. Qed.
Lemma call_failed_open : forall v,
  fmt_call_ok FMT_FAILED_OPEN (str FS_FAILED_OPEN ++ [0]) [PA_i (s32 v)] (pieces_failed_open v) (zlength (fmt_output (fmt FS_FAILED_OPEN) [AInt v])).
Proof using Type. pin_using tt. intros v. fmt_call FS_FAILED_OPEN [AInt v]. Qed.
Lemma call_packet_length : forall v1 v2,
  fmt_call_ok FMT_PACKET_LENGTH (str FS_PACKET_LENGTH ++ [0]) [PA_i (s32 v1); PA_i (s32 v2)] (pieces_packet_length v1 v2)
              (zlength (fmt_output (fmt FS_PACKET_LENGTH) [AInt v1; AInt v2])).
Proof using Type. pin_using tt. intros v1 v2. fmt_call FS_PACKET_LENGTH [AInt v1; AInt v2]. Qed.
Lemma call_too_big :
  fmt_call_ok FMT_TOO_BIG (str FS_TOO_BIG ++ [0]) [PA_u (u32 0x4000000)] pieces_too_big (zlength (fmt_output (fmt FS_TOO_BIG) [AInt 0x4000000])).
Proof using Type. pin_using tt. fmt_call FS_TOO_BIG [AInt 0x4000000]. Qed.
Lemma call_couldnt_open : forall s, zlength s <= 2^24 ->
  fmt_call_ok FMT_COULDNT_OPEN (str FS_COULDNT_OPEN ++ [0]) [PA_s s] (pieces_couldnt_open s) (zlength (fmt_output (fmt FS_COULDNT_OPEN) [AStr s])).
Proof using Type. pin_using tt. intros s Hs. fmt_call FS_COULDNT_OPEN [AStr s]. Qed.
Lemma call_usage : forall s, zlength s <= 2^24 ->
  fmt_call_ok FMT_USAGE (str FS_USAGE ++ [0]) [PA_s s] (pieces_usage s) (zlength (fmt_output (fmt FS_USAGE) [AStr s])).
Proof using Type. pin_using tt. intros s Hs. fmt_call FS_USAGE [AStr s]. Qed.
Lemma call_cannot_open : forall s, zlength s <= 2^24 ->
  fmt_call_ok FMT_CANNOT_OPEN (str FS_CANNOT_OPEN ++ [0]) [PA_s s] (pieces_cannot_open s) (zlength (fmt_output (fmt FS_CANNOT_OPEN) [AStr s])).
Proof using Type. pin_using tt. intros s Hs. fmt_call FS_CANNOT_OPEN [AStr s]. Qed.
Lemma call_read_error : forall s, zlength s <= 2^24 ->
  fmt_call_ok FMT_READ_ERROR (str FS_READ_ERROR ++ [0]) [PA_s s] (pieces_read_error s) (zlength (fmt_output (fmt FS_READ_ERROR) [AStr s])).
Proof using Type. pin_using tt. intros s Hs. fmt_call FS_READ_ERROR [AStr s]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Glue.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Notation cblk := (@cblock hptr).
  Notation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.

  #[local] Notation spo_facts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.spo_facts K KST).
  #[local] Notation files_R_focus := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.files_R_focus (ho_eqb HO) EQB).
  #[local] Notation GIo_stdio_step := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.GIo_stdio_step K KST HFL).
  #[local] Notation keeps_of_stdio := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.keeps_of_stdio K).
  #[local] Notation implM_lookup_file := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.implM_lookup_file HO).
  #[local] Notation client_range_lo := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.client_range_lo K).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma stdout_finish :
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (m : mem) (lo : Z) (ps : list (list Z)) (tail : list byte) (rp : Z)
           (f' : file_st) (st' : PS) (ms' : machine_state),
      GIo K R s CL FB m -> STDIOR (ps_libc s) FB m ->
      CEILZ <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp <= rc_spmain R ->
      0 <= rp -> rp + zlength (f_rbuf (lc_stdout (ps_libc s))) < 2^63 -> firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
      fprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail lo (rc_canary R) true true
                        rp (rp + zlength (f_rbuf (lc_stdout (ps_libc s)))) m s f' st' ms' ->
      mleaf (vfprintf (lc_stdout (ps_libc s)) ps) s f' st' ->
      st' = s /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
        /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
        /\ GIo K R (set_libc (set_stdout f' (ps_libc s)) s) CL FB m'.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros until ms'. intros G SR CLO LOS SPM RP0 RP1 GLN PO LF.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof SOI as (CH1 & FD1 & BS1 & NRD1 & NWR1 & EOF1 & RB1 & LBF1).
    sbl_pose_in PO. destruct PO as (-> & INV' & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & flags' & mode' & bufbytes' & m' & rpos' & rend'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & RP' & FL' & BUF' & BP' & WBL'). sbl_subst_all.
    assert (BSnz : f_bufsize (lc_stdout (ps_libc s)) <> 0) by (rewrite BS1; unfold BUFSIZ; lia).
    pose proof (vfprintf_leaf_buffered _ _ _ _ _ BSnz LF) as [FX _].
    pose proof (vfprintf_leaf_buffered_wl _ _ _ _ _ BSnz LF) as WL.
    split; [reflexivity|].
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    unfold A_STDOUT, A_STDOUT_BUF in *.
    assert (HW : Forall (stdio_iv R CL FB (bv_unsigned sp)) [(lo, bv_unsigned sp); (147456, 147456 + 232); (347440, 347440 + 1024)]).
    { unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd]; [left; lia| right; right; left; lia| right; right; right; lia]. }
    split.
    { eapply agrees_on_weaken; [eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia]|].
      - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd]; [left; lia| right; right; left; lia| right; right; right; left; lia].
      - intros a Ha. split; [exact Ha| intros X; exact X]. }
    eapply (GIo_stdio_step R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| exact SPM|].
    cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_stdout].
    pose proof (GIo_blocks K _ _ _ _ _ G) as BOK. pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof SEI as (_ & _ & SEbs & _).
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    Ltac trw MU WM A := eapply rw_cells_transport; [exact A | exact MU | exact WM | cbn; lia].
    pose proof INV' as (WA' & RB' & BS' & NW' & FDC' & _ & CHN').
    rewrite RB1 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    split.
    { exists flags', mode', rpos', tail, bufbytes'.
      rewrite WA', RB', BS'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      assert (Erend : rend' = rpos') by (rewrite RB1 in RP'; change (zlength (@nil Z)) with 0 in RP'; lia).
      rewrite Erend in FC'.
      split; [exact FC'|]. split; [exact FL'|]. split; [exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [exact WBL'|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN]. }
    split.
    { pose proof FX as (E1 & E2 & E3 & E4 & E5 & E6 & _ & _ & SW' & LB').
      unfold stdout_inv. rewrite E1, E2, E4, E5, E6.
      split; [exact CH1|]. split; [exact FD1|]. split; [exact BS'|]. split; [exact NRD1|]. split; [exact NWR1|]. split; [exact EOF1|]. split; [exact RB'|].
      destruct WL as [[W1 W2]|[W1 W2]]; rewrite W1, ?W2; [exact LBF1| intros X; discriminate X]. }
    split. { eapply FILE_R_transport; [exact SE| exact MU| exact WM| | | rewrite SEbs; lia].
             - repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
             - rewrite SEbs. repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil. }
    split; [exact SEI|].
    split. { eapply rw_cells_transport; [exact SIN | exact MU | exact WM |]. unfold stdin_cells. rewrite file_cells_size. cbn. lia. }
    split; [trw MU WM U1|]. split; [trw MU WM U2|]. split; [trw MU WM U3|]. split; [trw MU WM OL|]. split; [trw MU WM OH|].
    split; [| exact ND].
    eapply files_R_transport; [exact FS| exact MU| exact WM|].
    apply Forall_forall. intros [lo' hi'] Hiv. apply Forall_forall. intros [[q' A'] n'] Hb. cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) BO2 _ Hb) as (K1 & K2 & K3 & K4 & K5 & K6). unfold cb_addr, cb_size in *. cbn [fst snd] in *.
    cbn in Hiv. destruct Hiv as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vprintf_d_proof__stmt : Prop := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB.vprintf_d_stmt K.
  Section Sz16.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo AP v rest : ltac2:(SecDiet.SzSec.tyM 'vprintf_d_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma vprintf_d_proof__body : ltac2:(SecDiet.SzSec.bodyP 'vprintf_d_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
 intros ([FB G] & ST & LOR & LOB & SPM & MI & Etp & AL) -> -> HV APC APLO APHI.
    assert (SPO : std_pre_o K sp tp R s CL FB lo STDIO_STACK m) by (split; [exact G|]; split; [exact ST|]; split; [exact LOR|]; split; [exact LOB|]; split; [exact SPM|]; split; [exact MI|]; split; [exact Etp| exact AL]).
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (_ & SR & _ & _ & SSP & BOK & _ & _ & _ & _ & _ & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK in *.
    sbl_pose_in SO. destruct SO as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SOI as (CH1 & FD1 & BS1 & NRD1 & NWR1 & EOF1 & RB1 & LBF1).
    pose proof (call_emit_d v) as (HF & P1 & PIECES & SMALL & RBD & HA & BYf).
    pose proof (s32_facts v) as [S32a S32b].
    pose proof (rw_cells_bound _ _ _ _ APC) as APB. cbn [cells_size csize Nat.add] in APB.
    apply (proj1 (rw_cells_app usegs _ _ [_] [_])) in APC. destruct APC as [APC _].
    rewrite BS1 in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    unfold printf. apply implM_rd_lc.
    eapply implM_bind.
    { eapply implM_leaf.
      unfold VPRINTF_ENTRY.
      eapply (vprintf_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail FMT_D AP lo
                (str FS_EMIT_D ++ [0]) [Z_to_bv 64 v] [PA_i (s32 v)] (pieces_emit_d v) _ (rc_canary R) true true)
        with (rpos := rp) (rend := rp + zlength (f_rbuf (lc_stdout (ps_libc s)))) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC | exact FL | exact BUF | exact BP | exact WB0
             | exact BS1 | exact WBL | exact NWR1 | exact RB1
             | rewrite CH1; left; exact FD1 | exact CH1
             | apply BYf; exact MI
             | apply va_area_of_cells; exact APC
             | cbn [args_ok]; split; [split; [exact S32a | exact S32b] | exact I]
             | exact ST | exact SSP | exact MI
             | unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP in *; cbv [zlength Datatypes.length Z.of_nat Pos.of_succ_nat Pos.succ]; unfold rc_spmain in *; lia
             | idtac "VPD-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' [PO LF].
    assert (CLO : CEILZ <= lo) by (unfold rc_lo in *; lia). assert (LOS : lo <= bv_unsigned sp) by lia.
    destruct (stdout_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB m lo _ tail rp f' st' ms' G SR CLO LOS SPM RP0 RP1 GLN PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    apply implM_upd_lc_last. apply evt_done. unfold out_post.
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. eapply GIo_close. exact G'.
  Qed.
  End Sz16.
  Theorem vprintf_d_proof : ltac:(let t := eval cbv delta [vprintf_d_proof__stmt] in vprintf_d_proof__stmt in exact t).
  Proof using HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo AP v rest. ltac2:(SecDiet.SzSec.closeP 'vprintf_d_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition printf_d_gen__stmt : Prop := forall FMT (mk : Z -> list (list Z)) fs,
    (forall v, fmt_call_ok FMT (str fs ++ [0]) [PA_i (s32 v)] (mk v) (zlength (fmt_output (fmt fs) [AInt v]))) ->
    printf_d_stmt_o K FMT mk.
  Section Sz17.
  Variables FMT mk fs ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo v : ltac2:(SecDiet.SzSec.tyM 'printf_d_gen__stmt "vvvhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @FMT).
  Lemma printf_d_gen__body : ltac2:(SecDiet.SzSec.bodyP 'printf_d_gen__stmt "vvvhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros CALL.
 intros SPO -> -> HV.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK in *.
    sbl_pose_in SO. destruct SO as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SOI as (CH1 & FD1 & BS1 & NRD1 & NWR1 & EOF1 & RB1 & LBF1).
    pose proof (CALL v) as (HF & P1 & PIECES & SMALL & RBD & HA & BYf).
    pose proof (s32_facts v) as [S32a S32b].
    rewrite BS1 in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    unfold s_printf, printf. apply implM_rd_lc.
    eapply implM_bind.
    { eapply implM_leaf.
      unfold PRINTF_ENTRY.
      eapply (printf_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail FMT lo
                (str fs ++ [0]) [PA_i (s32 v)] (mk v) _ (rc_canary R) true true)
        with (rpos := rp) (rend := rp + zlength (f_rbuf (lc_stdout (ps_libc s)))) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC | exact FL | exact BUF | exact BP | exact WB0
             | exact BS1 | exact WBL | exact NWR1 | exact RB1
             | rewrite CH1; left; exact FD1 | exact CH1
             | apply BYf; exact MI
             | cbn [args_ok]; split; [split; [exact S32a | exact S32b] | exact I]
             | exact ST | exact SSP | exact MI
             | unfold FPRINTF_DEPTH, GLOBALS_TOP in *; unfold rc_spmain, rc_lo in *; lia
             | idtac "PFD-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' [PO LF].
    assert (CLO : CEILZ <= lo) by (unfold rc_lo in *; lia). assert (LOS : lo <= bv_unsigned sp) by lia.
    destruct (stdout_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB m lo _ tail rp f' st' ms' G SR CLO LOS SPM RP0 RP1 GLN PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    apply implM_upd_lc_last. apply evt_done.
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz17.
  Lemma printf_d_gen : ltac:(let t := eval cbv delta [printf_d_gen__stmt] in printf_d_gen__stmt in exact t).
  Proof using HFL KST. intros FMT mk fs CALL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo v. ltac2:(SecDiet.SzSec.closeP 'printf_d_gen__body "vvvhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Theorem printf_failed_remove_proof : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt). exact (printf_d_gen _ _ _ call_failed_remove). Qed.
  Theorem printf_failed_open_proof : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt). exact (printf_d_gen _ _ _ call_failed_open). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition str_parg_bytes__stmt : Prop := forall m P (str slack : list byte),
    bytes_at usegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
    (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
    let s := map bv_unsigned str in
    bytes_at usegs m P (zb s ++ Z_to_bv 8 0 :: firstn (Z.to_nat (pad8 (P + zlength s + 1))) slack)
    /\ Forall (fun c => 0 < c < 256) s
    /\ (- (P + zlength s + 1)) mod 8 <= zlength (firstn (Z.to_nat (pad8 (P + zlength s + 1))) slack)
    /\ zlength (firstn (Z.to_nat (pad8 (P + zlength s + 1))) slack) = pad8 (P + zlength s + 1)
    /\ zlength s = Z.of_nat (length str).
  Section Sz20.
  Variables m P str slack : ltac2:(SecDiet.SzSec.tyM 'str_parg_bytes__stmt "vvvv" @m).
  Lemma str_parg_bytes__body : ltac2:(SecDiet.SzSec.bodyP 'str_parg_bytes__stmt "vvvv").
  Proof using Type. pin_using tt.
    intros BY NZ PAD.
 cbv zeta.
    assert (EL : zlength (map bv_unsigned str) = Z.of_nat (length str)) by (unfold zlength; rewrite length_map; reflexivity).
    rewrite EL. pose proof (pad8_range (P + Z.of_nat (length str) + 1)) as PR. unfold pad8 in PR |- *.
    remember ((- (P + Z.of_nat (length str) + 1)) mod 8) as pd eqn:Epd.
    assert (LS : zlength (firstn (Z.to_nat pd) slack) = pd) by (unfold zlength; rewrite length_firstn; lia).
    rewrite LS. split.
    { rewrite zb_unsigned. rewrite <- (firstn_skipn (Z.to_nat pd) slack) in BY.
      change (str ++ Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack ++ skipn (Z.to_nat pd) slack)
        with (str ++ (Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack) ++ skipn (Z.to_nat pd) slack) in BY.
      rewrite app_assoc in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
    split.
    { apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
      destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE]; [|lia]. exfalso. apply NZ.
      replace (Z_to_bv 8 0) with b; [exact Hb|]. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b), E. reflexivity. }
    split; [lia|]. split; [reflexivity| reflexivity].
  Qed.
  End Sz20.
  Lemma str_parg_bytes : ltac:(let t := eval cbv delta [str_parg_bytes__stmt] in str_parg_bytes__stmt in exact t).
  Proof using Type. intros m P str slack. ltac2:(SecDiet.SzSec.closeP 'str_parg_bytes__body "vvvv"). Qed.

  (* [comment removed for export] *)
  Definition str_arg_place__stmt : Prop := forall R (s : PS) (CL FB : list cblk) m SP P L lo,
    GIo K R s CL FB m -> (forall a, P <= a < P + L -> client_keeps CL SP a) -> 0 < L ->
    rc_lo R <= lo -> lo < SP ->
    0 < P /\
    ((P + L + pad8 (P + L) <= lo /\ (P + L + pad8 (P + L) <= 0x10000 \/ 0x56000 <= P)
      /\ (forall q A n, In (q, A, n) FB -> 0 < n -> P + L + pad8 (P + L) <= A \/ A + n <= P))
     \/ SP <= P).
  Section Sz21.
  Variables R s CL FB m SP P L lo : ltac2:(SecDiet.SzSec.tyM 'str_arg_place__stmt "vvvvvvvvv" @R).
  Lemma str_arg_place__body : ltac2:(SecDiet.SzSec.bodyP 'str_arg_place__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G KEEP LPOS LOR LOS.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    unfold rc_lo in LOR. pose proof (pad8_range (P + L)) as PR.
    destruct (Z_le_gt_dec SP P) as [HSP|HSP]; [split; [lia| right; exact HSP]|].
    assert (CRL : forall a, P <= a < P + L -> in_block CL a).
    { intros a Ha. destruct (KEEP a Ha) as [X|X]; [exfalso| exact X].
      destruct (KEEP P ltac:(lia)) as [Y|Y]; [lia|]. destruct (in_block_facts _ _ P BO1 Y) as (_ & Y2 & _).
      destruct (KEEP CEILZ ltac:(lia)) as [W|W]; [lia|]. destruct (in_block_facts _ _ CEILZ BO1 W) as (_ & W2 & _). lia. }
    assert (CR : client_range R CL SP P L) by (left; exact CRL).
    destruct (client_range_lo R s CL FB m SP P L lo G CR LPOS ltac:(unfold rc_lo; lia) ltac:(lia)) as (P0 & PC & P47 & PIMG).
    destruct (in_block_facts _ _ (P + L - 1) BO1 (CRL (P + L - 1) ltac:(lia))) as (_ & E2 & E3 & _).
    split; [exact P0|]. left.
    assert (C8 : CEILZ mod 8 = 0).   (* [comment removed for export] *)
    { ceil_facts. replace alloc_ceiling with (512 * (alloc_ceiling / 4096) * 8) by (pose proof (Z_div_mod_eq_full alloc_ceiling 4096); lia). apply Z_mod_mult. }
    pose proof (pad8_align (P + L) CEILZ ltac:(lia) ltac:(lia) C8) as A1.
    split; [lia|]. split.
    { destruct PIMG as [X|[X|X]]; [| right; exact X| lia]. left. pose proof (pad8_align (P + L) 0x10000 ltac:(lia) X eq_refl). lia. }
    intros q A n HIN NPOS.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.file_block_facts R CL FB q A n BOK HIN) as (B1 & B2 & B3 & B4 & B5 & B6).
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.client_range_apart R CL FB SP P L q A n BOK HIN CR LPOS ltac:(lia) NPOS) as [X|X]; [left| right; exact X].
    assert (A8 : A mod 8 = 0) by (clear -B2; Z.div_mod_to_equations; lia).
    pose proof (pad8_align (P + L) A ltac:(lia) X A8). lia.
  Qed.
  End Sz21.
  Lemma str_arg_place : ltac:(let t := eval cbv delta [str_arg_place__stmt] in str_arg_place__stmt in exact t).
  Proof using Type. intros R s CL FB m SP P L lo. ltac2:(SecDiet.SzSec.closeP 'str_arg_place__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma stderr_finish :
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (m : mem) (lo : Z) (ps : list (list Z)) (tail bufbytes : list byte)
           (f' : file_st) (st' : PS) (ms' : machine_state),
      GIo K R s CL FB m -> STDIOR (ps_libc s) FB m ->
      CEILZ <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp <= rc_spmain R ->
      firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
      rw_cells usegs m A_STDERR_BUF [CB 0 bufbytes] ->
      fprintf_ubf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail lo (rc_canary R)
                       m s f' st' ms' ->
      mleaf (vfprintf (lc_stderr (ps_libc s)) ps) s f' st' ->
      st' = s /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
        /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
        /\ GIo K R (set_libc (set_stderr f' (ps_libc s)) s) CL FB m'.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros until ms'. intros G SR CLO LOS SPM GLN BUF PO LF.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    sbl_pose_in PO. destruct PO as (-> & WA' & WB' & RB' & BS' & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & flags' & mode' & m'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & FL'). sbl_subst_all.
    destruct (vfprintf_leaf_unbuffered _ _ _ _ _ BS2 LF) as [(E1 & E2 & E3 & E4 & E5 & E6 & _ & _ & _ & SW' & LB') _].
    split; [reflexivity|].
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    unfold A_STDERR, A_STDERR_BUF in *.
    assert (HW : Forall (stdio_iv R CL FB (bv_unsigned sp)) [(lo, bv_unsigned sp); (146976, 146976 + 232)]).
    { unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; [left; lia| right; right; left; lia]. }
    split.
    { eapply agrees_on_weaken; [eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia]|].
      - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; [left; lia| right; right; left; lia].
      - intros a Ha. split; [exact Ha| intros X; exact X]. }
    eapply (GIo_stdio_step R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| exact SPM|].
    cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_stderr].
    pose proof (GIo_blocks K _ _ _ _ _ G) as BOK. pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof SOI as (_ & _ & SObs & _).
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    Ltac trw2 MU WM A := eapply rw_cells_transport; [exact A | exact MU | exact WM | cbn; lia].
    split. { eapply FILE_R_transport; [exact SO| exact MU| exact WM| | | rewrite SObs; unfold BUFSIZ; lia].
             - repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
             - rewrite SObs. unfold BUFSIZ. repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil. }
    split; [exact SOI|].
    split.
    { exists flags', mode', 0, tail, bufbytes.
      rewrite WA', RB', BS', WB'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      split; [exact FC'|]. split; [exact FL'|]. split; [trw2 MU WM BUF|]. split; [reflexivity|]. split; [intros _; reflexivity|]. split; [lia|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN]. }
    split.
    { unfold stderr_inv. rewrite E1, E2, E3, E4, E5, E6, RB'.
      split; [exact CH2|]. split; [exact FD2|]. split; [reflexivity|]. split; [exact ND2|]. split; [exact NW2|]. split; [exact EOF2|]. split; [reflexivity|].
      split.
      - destruct (f_stdoutw f'); [| reflexivity]. exfalso. pose proof (SW' eq_refl) as X. rewrite SW2 in X. discriminate X.
      - destruct (f_lbf_nl f'); [| reflexivity]. exfalso. pose proof (LB' eq_refl) as X. rewrite LB2 in X. discriminate X. }
    split. { eapply rw_cells_transport; [exact SIN | exact MU | exact WM |]. unfold stdin_cells. rewrite file_cells_size. cbn. lia. }
    split; [trw2 MU WM U1|]. split; [trw2 MU WM U2|]. split; [trw2 MU WM U3|]. split; [trw2 MU WM OL|]. split; [trw2 MU WM OH|].
    split; [| exact ND].
    eapply files_R_transport; [exact FS| exact MU| exact WM|].
    apply Forall_forall. intros [lo' hi'] Hiv. apply Forall_forall. intros [[q' A'] n'] Hb. cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) BO2 _ Hb) as (K1 & K2 & K3 & K4 & K5 & K6). unfold cb_addr, cb_size in *. cbn [fst snd] in *.
    cbn in Hiv. destruct Hiv as [E|[E|[]]]; injection E as <- <-; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition eprintf_too_big_proof__stmt : Prop := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB.eprintf_i_stmt K FMT_TOO_BIG 0x4000000 pieces_too_big.
  Section Sz22.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo : ltac2:(SecDiet.SzSec.tyM 'eprintf_too_big_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma eprintf_too_big_proof__body : ltac2:(SecDiet.SzSec.bodyP 'eprintf_too_big_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
 intros ([FB G] & ST & LOR & LOB & SPM & MI & Etp & AL) -> -> ->.
    assert (SPO : std_pre_o K sp tp R s CL FB lo STDIO_STACK m) by (split; [exact G|]; split; [exact ST|]; split; [exact LOR|]; split; [exact LOB|]; split; [exact SPM|]; split; [exact MI|]; split; [exact Etp| exact AL]).
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (_ & SR & _ & _ & SSP & BOK & _ & _ & _ & _ & _ & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK, STDERR_FILE in *.
    sbl_pose_in SE. destruct SE as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    assert (WBN : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. rewrite BS2 in WBL. unfold zlength in WBL. cbn [Datatypes.length] in WBL. lia. }
    rewrite BS2, RB2, WBN in FC. rewrite BS2 in BUF. change (zlength (@nil Z)) with 0 in FC. rewrite RB2 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    pose proof call_too_big as (HF & P1 & PIECES & SMALL & RBD & HA & BYf).
    pose proof (u32_facts 0x4000000) as U32.
    assert (CLO : CEILZ <= lo) by (unfold rc_lo in *; lia). assert (LOS : lo <= bv_unsigned sp) by lia.
    unfold eprintf. apply implM_rd_lc.
    eapply implM_bind.
    { eapply implM_leaf.
      unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB.FPRINTF_ENTRY. change A_STDERR with 146976 in FC.
      eapply (fprintf_ubf_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 146976 A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail FMT_TOO_BIG lo
                (str FS_TOO_BIG ++ [0]) [PA_u (u32 0x4000000)] pieces_too_big _ (rc_canary R))
        with (rpos := rp) (flags := flags) (mode := mode).
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC | exact FL
             | exact BS2 | exact NW2 | exact RB2 | exact WBN | exact CH2 | right; exact FD2 | exact SW2
             | apply BYf; exact MI
             | cbn [args_ok]; split; [exact U32 | exact I]
             | exact ST | exact SSP | exact MI
             | unfold FPRINTF_DEPTH, GLOBALS_TOP, A_STDERR_BUF in *; unfold rc_spmain, rc_lo in *;
               try destruct (f_wactive (lc_stderr (ps_libc s))); (keep_hyps CEILV sp lo LOB CLO R SPM SP47 rp RP0 RP1; lia)
             | idtac "EPI-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' [PO LF].
    destruct (stderr_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB m lo _ tail bufbytes f' st' ms' G SR CLO LOS SPM GLN BUF PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    apply implM_upd_lc_last. apply evt_done. unfold out_post.
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. eapply GIo_close. exact G'.
  Qed.
  End Sz22.
  Theorem eprintf_too_big_proof : ltac:(let t := eval cbv delta [eprintf_too_big_proof__stmt] in eprintf_too_big_proof__stmt in exact t).
  Proof using HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo. ltac2:(SecDiet.SzSec.closeP 'eprintf_too_big_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Lemma eprintf_s_gen : forall FMT (mk : list Z -> list (list Z)) fs,
    (forall sv, zlength sv <= 2^24 -> fmt_call_ok FMT (str fs ++ [0]) [PA_s sv] (mk sv) (zlength (fmt_output (fmt fs) [AStr sv]))) ->
    OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47.TwB.eprintf_s_stmt47 K FMT mk.   (* [comment removed for export] *)
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros FMT mk fs CALL.
    intros until slack. intros ([FB G] & ST & LOR & LOB & SPM & MI & Etp & AL) -> -> -> BY NZ LEN PAD KEEP S47.   (* [comment removed for export] *)
    assert (SPO : std_pre_o K sp tp R s CL FB lo STDIO_STACK m) by (split; [exact G|]; split; [exact ST|]; split; [exact LOR|]; split; [exact LOB|]; split; [exact SPM|]; split; [exact MI|]; split; [exact Etp| exact AL]).
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (_ & SR & _ & _ & SSP & BOK & _ & _ & _ & _ & _ & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK, STDERR_FILE in *.
    sbl_pose_in SE. destruct SE as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    assert (WBN : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. rewrite BS2 in WBL. unfold zlength in WBL. cbn [Datatypes.length] in WBL. lia. }
    rewrite BS2, RB2, WBN in FC. rewrite BS2 in BUF. change (zlength (@nil Z)) with 0 in FC. rewrite RB2 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_app in PB. cbn [Datatypes.length] in PB.
    pose proof (str_parg_bytes m P str slack BY NZ PAD) as SPB. cbv zeta in SPB. sbl_pose_in SPB. destruct SPB as (BY' & FA & PAD' & LS & EL). sbl_subst_all.
    rewrite EL in *.
    pose proof (CALL (map bv_unsigned str) ltac:(rewrite EL; lia)) as (HF & P1 & PIECES & SMALL & RBD & HA & BYf).
    assert (CLO : CEILZ <= lo) by (unfold rc_lo in *; lia). assert (LOS : lo <= bv_unsigned sp) by lia.
    assert (KEEP' : forall a, P <= a < P + (Z.of_nat (length str) + 1) -> client_keeps CL (bv_unsigned sp) a) by (intros a Ha; apply KEEP; lia).
    destruct (str_arg_place R s CL FB m (bv_unsigned sp) P (Z.of_nat (length str) + 1) lo G KEEP' ltac:(lia) LOR ltac:(lia)) as [P0 PLACE].
    assert (EPD : pad8 (P + Z.of_nat (length str) + 1) = pad8 (P + (Z.of_nat (length str) + 1))) by (f_equal; lia).
    rewrite EPD in *. pose proof (pad8_range (P + (Z.of_nat (length str) + 1))) as PR.
    unfold eprintf. apply implM_rd_lc.
    eapply implM_bind.
    { eapply implM_leaf.
      unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB.FPRINTF_ENTRY. change A_STDERR with 146976 in FC.
      eapply (fprintf_ubf_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 146976 A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail FMT lo
                (Fmt.str fs ++ [0]) [PA_s (map bv_unsigned str)] (mk (map bv_unsigned str)) _ (rc_canary R))
        with (rpos := rp) (flags := flags) (mode := mode).
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC | exact FL
             | exact BS2 | exact NW2 | exact RB2 | exact WBN | exact CH2 | right; exact FD2 | exact SW2
             | apply BYf; exact MI
             | cbn [args_ok]; split; [| exact I]; cbn [arg_ok]; rewrite (unsigned_lit P) by (keep_hyps CEILV sp P str slack S47 P0; lia); rewrite ?EL;
               eexists; split; [exact BY'|]; split; [exact FA|]; split; [exact PAD'|]; split; [exact P0|]; rewrite LS;
               unfold GLOBALS_TOP in *; unfold rc_spmain, rc_lo in *;
               destruct PLACE as [(Q1 & Q2 & Q3) | Q]; [| repeat split; first [right; (keep_hyps CEILV sp P str slack Q lo LOB CLO; lia) | (keep_hyps CEILV sp P str slack S47; lia)]];
               split; [left; (keep_hyps CEILV sp lo P str slack Q1; lia)|]; split; [clear -Q2 PR; destruct Q2; [left; (keep_hyps P str H; lia)| right; (keep_hyps P H; lia)] |]; split; [left; (keep_hyps CEILV sp lo P str slack LOB Q1; lia)|]; split; [left; (keep_hyps CEILV sp lo P str slack LOB Q1; lia) | (keep_hyps CEILV sp P str slack S47; lia)]
             | exact ST | exact SSP | exact MI
             | unfold FPRINTF_DEPTH, GLOBALS_TOP, A_STDERR_BUF in *; unfold rc_spmain, rc_lo in *;
               try destruct (f_wactive (lc_stderr (ps_libc s))); (keep_hyps CEILV sp lo P str slack LOB CLO R SPM SP47 rp RP0 RP1; lia)
             | idtac "EPS-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' [PO LF].
    destruct (stderr_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB m lo _ tail bufbytes f' st' ms' G SR CLO LOS SPM GLN BUF PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    apply implM_upd_lc_last. apply evt_done. unfold out_post.
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. eapply GIo_close. exact G'.
  Qed.

  Theorem eprintf_usage_proof : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47.TwB.eprintf_s_stmt47 K FMT_USAGE pieces_usage.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt). exact (eprintf_s_gen _ _ _ call_usage). Qed.
  Theorem eprintf_cannot_open_proof : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47.TwB.eprintf_s_stmt47 K FMT_CANNOT_OPEN pieces_cannot_open.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt). exact (eprintf_s_gen _ _ _ call_cannot_open). Qed.
  Theorem eprintf_read_error_proof : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47.TwB.eprintf_s_stmt47 K FMT_READ_ERROR pieces_read_error.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt). exact (eprintf_s_gen _ _ _ call_read_error). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Notation eqb := (ho_eqb HO).

  Lemma hfile_finish :
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (m : mem) (lo : Z) (ps : list (list Z)) (q : hptr) (Af : Z) (f : file_st) (pv nx : Z)
           (tail : list byte) (rp : Z) (f' : file_st) (st' : PS) (ms' : machine_state),
      GIo K R s CL FB m -> STDIOR (ps_libc s) FB m -> In (q, Af, FILE_BLOCK) FB ->
      heap_file_inv f -> f_nowr f = false ->
      (forall m' f', FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
         (forall q2 A2 n2 f2 pv2 nx2, In (q2, A2, n2) FB -> q2 <> q ->
            FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2 -> heap_file_inv f2 ->
            FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2) ->
         files_R m' 0 (files_update eqb (lc_files (ps_libc s)) q f') FB) ->
      CEILZ <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp <= rc_spmain R ->
      0 <= rp -> rp + zlength (f_rbuf f) < 2^63 -> firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
      fprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx tail lo
                        (rc_canary R) true false rp (rp + zlength (f_rbuf f)) m s f' st' ms' ->
      mleaf (vfprintf f ps) s f' st' ->
      st' = s /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
        /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
        /\ GIo K R (set_libc (set_files (files_update eqb (lc_files (ps_libc s)) q f') (ps_libc s)) s) CL FB m'.
  Proof using EQB HFL KST. pin_using (fun (EQB HFL KST : unit) => tt).
    intros until ms'. intros G SR HIN INV NOWR UPD CLO LOS SPM RP0 RP1 GLN PO LF.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    assert (RBN : f_rbuf f = []) by (apply NORDi; rewrite NRW, NOWR; reflexivity).
    rewrite RBN in RP1. change (zlength (@nil Z)) with 0 in RP1.
    sbl_pose_in PO. destruct PO as (-> & INV' & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & flags' & mode' & bufbytes' & m' & rpos' & rend'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & RP' & FL' & BUF' & BP' & WBL'). sbl_subst_all.
    assert (BSnz : f_bufsize f <> 0) by (rewrite BS; unfold BUFSIZ; lia).
    pose proof (vfprintf_leaf_buffered _ _ _ _ _ BSnz LF) as [FX _].
    pose proof INV' as (WA' & RB' & BS' & NW' & FDC' & _ & CHN').
    pose proof (GIo_blocks K _ _ _ _ _ G) as BOK.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.file_block_facts R CL FB q Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold FILE_BLOCK, FILE_BUF_OFF in *.
    split; [reflexivity|].
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    assert (HW : Forall (stdio_iv R CL FB (bv_unsigned sp)) [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]).
    { unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
      - left. lia.
      - right; left. unfold iv_in_block. apply Exists_exists. exists (q, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
      - right; left. unfold iv_in_block. apply Exists_exists. exists (q, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia]. }
    split.
    { eapply agrees_on_weaken.
      - eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
        + left. lia.
        + right; left. unfold iv_in_block. apply Exists_exists. exists (q, Af, 1264). split; [exact HIN| cbn; lia].
        + right; left. unfold iv_in_block. apply Exists_exists. exists (q, Af, 1264). split; [exact HIN| cbn; lia].
      - intros a Ha. split; [exact Ha| intros X; exact X]. }
    eapply (GIo_stdio_step R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| exact SPM|].
    cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
    assert (AGS : agrees_on (fun a => S3.GI.TwB.stdio_static a) m m').
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. unfold S3.GI.TwB.stdio_static in Hs. cbn [outside]. lia. }
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
    Ltac trs3 AGS A := eapply agrees_rw_cells; [exact AGS | exact A | intros a Ha; unfold S3.GI.TwB.stdio_static; cbn in Ha; lia].
    split. { eapply FILE_R_agree; [exact SO | exact AGS | intros a Ha; unfold S3.GI.TwB.stdio_static; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; unfold S3.GI.TwB.stdio_static; lia]. }
    split; [exact SOI|].
    split. { eapply FILE_R_agree; [exact SE | exact AGS | intros a Ha; unfold S3.GI.TwB.stdio_static; lia | rewrite SEbs; intros a Ha; unfold S3.GI.TwB.stdio_static; lia]. }
    split; [exact SEI|].
    split. { eapply agrees_rw_cells; [exact AGS | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; unfold S3.GI.TwB.stdio_static; lia. }
    split; [trs3 AGS U1|]. split; [trs3 AGS U2|]. split; [trs3 AGS U3|]. split; [trs3 AGS OL|]. split; [trs3 AGS OH|].
    split.
    2:{ rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.files_update_keys. exact ND. }
    apply UPD.
    - (* [comment removed for export] *)
      exists flags', mode', rpos', tail, bufbytes'.
      rewrite WA', RB', BS'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      assert (Erend : rend' = rpos') by (rewrite RBN in RP'; change (zlength (@nil Z)) with 0 in RP'; lia).
      rewrite Erend in FC'.
      split; [exact FC'|]. split; [exact FL'|]. split; [exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [exact WBL'|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN].
    - exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.heap_file_inv_fx f f' INV NOWR FX).
    - (* [comment removed for export] *)
      intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2 FR2 INV2.
      pose proof INV2 as (_ & _ & BS2 & _).
      destruct (files_R_focus m 0 (lc_files (ps_libc s)) FB q2 A2 n2 FS ND HIN2) as (f2' & pv2' & nx2' & _ & En2 & _). subst n2.
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.file_block_facts R CL FB q2 A2 FILE_ALLOC BOK HIN2) as (B1 & B2 & B3 & B4 & B5 & B6). unfold FILE_ALLOC in B3, B4, B5, B6.
      assert (AP : A2 + 1264 <= Af \/ Af + 1264 <= A2).
      { destruct (GIo_apart K R s CL FB m (q2, A2, FILE_ALLOC) (q, Af, 1264) G ltac:(apply in_or_app; right; exact HIN2) ltac:(apply in_or_app; right; exact HIN)) as [E|AP].
        - exfalso. apply NE2. congruence.
        - unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
      eapply (FILE_R_agree (fun a => A2 <= a < A2 + 1264)); [exact FR2| | intros a Ha; lia | intros a Ha; rewrite BS2 in Ha; unfold BUFSIZ in Ha; lia].
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hb. cbn [outside]. (keep_hyps CEILV sp lo Af A2 a CLO B4 AP Hb; lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vfprintf_nowr_unr : forall (fs0 : file_st) ps (s : PS) (Q : unit -> PS -> machine_state -> Prop) ms h,
    heap_file_inv fs0 -> f_nowr fs0 = true ->
    implM usegs (mbind (vfprintf fs0 ps) (store_file ps_libc set_libc eqb h)) s Q ms.
  Proof using Type. pin_using tt.
    intros fs0 ps s Q ms h INV NOWR. pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    destruct (NOWRi NOWR) as [WACT _].
    unfold vfprintf. rewrite BS. change (BUFSIZ =? 0) with false. cbv iota.
    unfold ensure_w. rewrite WACT. unfold towrite. rewrite NOWR.
    apply implM_bind_assoc. cbn [mbind munr ebind bind]. apply implM_unr.
  Qed.

  Definition fprintf_packet_length_proof__stmt : Prop := fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Section Sz26.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo v1 v2 : ltac2:(SecDiet.SzSec.tyM 'fprintf_packet_length_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fprintf_packet_length_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_packet_length_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB HFL KST. pin_using (fun (EQB HFL KST : unit) => tt).
 intros SPO HIN -> -> -> -> HV1 HV2.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs0 & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.file_block_facts R CL FB f Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold STDIO_STACK in *. unfold FILE_BLOCK in FA3, FA4, FA5, FA6.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    unfold s_fprintf, Stdio.fprintf, with_file_.
    eapply implM_lookup_file; [exact LK|].
    destruct (f_nowr fs0) eqn:NOWR; [apply vfprintf_nowr_unr; [exact INV| exact NOWR]|].
    assert (RBN : f_rbuf fs0 = []) by (apply NORDi; rewrite NRW; reflexivity).
    sbl_pose_in FR. destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    rewrite BS in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    pose proof (call_packet_length v1 v2) as (HF & P1 & PIECES & SMALL & RBD & HA & BYf).
    pose proof (s32_facts_sx v1 HV1) as [S1a S1b]. pose proof (s32_facts_sx v2 HV2) as [S2a S2b].
    assert (CLO : CEILZ <= lo) by (unfold rc_lo in *; lia). assert (LOS : lo <= bv_unsigned sp) by lia.
    eapply implM_bind.
    { eapply implM_leaf. unfold FPRINTF_ENTRY.
      eapply (fprintf_file_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx tail
                FMT_PACKET_LENGTH lo (str FS_PACKET_LENGTH ++ [0]) [PA_i (s32 v1); PA_i (s32 v2)] (pieces_packet_length v1 v2) _ (rc_canary R) true false)
        with (rpos := rp) (rend := rp + zlength (f_rbuf fs0)) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC | exact FL | exact BUF | exact BP | exact WB0
             | exact BS | exact WBL | exact NOWR | exact RBN
             | rewrite NCH; exact FD | exact NCH | intros _; reflexivity
             | apply BYf; exact MI
             | cbn [args_ok]; split; [split; [exact S1a | exact S1b] |]; split; [split; [exact S2a | exact S2b] | exact I]
             | exact ST | exact SSP | exact MI
             | unfold FPRINTF_DEPTH, GLOBALS_TOP, FILE_BUF_OFF in *; unfold rc_spmain, rc_lo in *; (keep_hyps CEILV sp Af lo v1 v2 LOB CLO R SPM SP47 fs0 A0 FA4 FA5; lia)
             | idtac "FPL-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' [PO LF].
    destruct (hfile_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB m lo _ f Af fs0 pv nx tail rp f' st' ms' G SR HIN INV NOWR UPD CLO LOS SPM RP0 RP1 GLN PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    unfold store_file. apply implM_upd_lc_last. apply evt_done.
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz26.
  Theorem fprintf_packet_length_proof : ltac:(let t := eval cbv delta [fprintf_packet_length_proof__stmt] in fprintf_packet_length_proof__stmt in exact t).
  Proof using EQB HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo v1 v2. ltac2:(SecDiet.SzSec.closeP 'fprintf_packet_length_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fprintf_couldnt_open_proof__stmt : Prop := fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Section Sz27.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo P str slack : ltac2:(SecDiet.SzSec.tyM 'fprintf_couldnt_open_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fprintf_couldnt_open_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_couldnt_open_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB HFL KST. pin_using (fun (EQB HFL KST : unit) => tt).
 intros SPO HIN -> -> -> BY NZ LEN PAD CR.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs0 & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.file_block_facts R CL FB f Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold STDIO_STACK in *. unfold FILE_BLOCK in FA3, FA4, FA5, FA6.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    unfold s_fprintf, Stdio.fprintf, with_file_.
    eapply implM_lookup_file; [exact LK|].
    destruct (f_nowr fs0) eqn:NOWR; [apply vfprintf_nowr_unr; [exact INV| exact NOWR]|].
    assert (RBN : f_rbuf fs0 = []) by (apply NORDi; rewrite NRW; reflexivity).
    sbl_pose_in FR. destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    rewrite BS in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_app in PB. cbn [Datatypes.length] in PB.
    pose proof (str_parg_bytes m P str slack BY NZ PAD) as SPB. cbv zeta in SPB. sbl_pose_in SPB. destruct SPB as (BY' & FA & PAD' & LS & EL). sbl_subst_all.
    rewrite EL in *.
    pose proof (call_couldnt_open (map bv_unsigned str) ltac:(rewrite EL; lia)) as (HF & P1 & PIECES & SMALL & RBD & HA & BYf).
    assert (CLO : CEILZ <= lo) by (unfold rc_lo in *; lia). assert (LOS : lo <= bv_unsigned sp) by lia.
    assert (KEEP' : forall a, P <= a < P + (Z.of_nat (length str) + 1) -> client_keeps CL (bv_unsigned sp) a).
    { intros a Ha. destruct CR as [CR1|[CR1 CR2]]; [right; apply CR1; lia | left; lia]. }
    destruct (str_arg_place R s CL FB m (bv_unsigned sp) P (Z.of_nat (length str) + 1) lo G KEEP' ltac:(lia) LOR ltac:(lia)) as [P0 PLACE].
    assert (EPD : pad8 (P + Z.of_nat (length str) + 1) = pad8 (P + (Z.of_nat (length str) + 1))) by (f_equal; lia).
    rewrite EPD in *. pose proof (pad8_range (P + (Z.of_nat (length str) + 1))) as PR.
    assert (AOK : args_ok Af 232 (Af + FILE_BUF_OFF) 1024 m lo (bv_unsigned sp) (bv_unsigned sp - 448) [Z_to_bv 64 P; a3; a4; a5; a6; a7] [PA_s (map bv_unsigned str)]).
    { cbn [args_ok]. split; [| exact I]. cbn [arg_ok]. rewrite (unsigned_lit P) by lia. rewrite ?EL.
      eexists. split; [exact BY'|]. split; [exact FA|]. split; [exact PAD'|]. split; [exact P0|]. rewrite LS.
      unfold GLOBALS_TOP, FILE_BUF_OFF in *. unfold rc_spmain, rc_lo in *.
      assert (P47 : P + Z.of_nat (length str) <= 2^47).   (* [comment removed for export] *)
      { destruct CR as [CR1|[CR1 CR2]]; [| unfold rc_spmain in *; lia].
        destruct (client_range_lo R s CL FB m (bv_unsigned sp) P (Z.of_nat (length str) + 1) lo G (or_introl CR1) ltac:(lia) LOR ltac:(lia)) as (_ & _ & C3 & _). lia. }
      destruct PLACE as [(Q1 & Q2 & Q3) | Q]; [| repeat split; fastfirst (first [right; lia | lia])].
      pose proof (Q3 f Af FILE_BLOCK HIN ltac:(unfold FILE_BLOCK; lia)) as Q4. unfold FILE_BLOCK in Q4.
      destruct Q4 as [Q4|Q4].
      - split; [left; lia|]. split; [left; lia|]. split; [left; lia|]. split; [left; lia | lia].
      - split; [left; lia|]. split; [right; lia|]. split; [right; lia|]. split; [left; lia | lia]. }
    eapply implM_bind.
    { eapply implM_leaf. unfold FPRINTF_ENTRY.
      eapply (fprintf_file_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx tail
                FMT_COULDNT_OPEN lo (Fmt.str FS_COULDNT_OPEN ++ [0]) [PA_s (map bv_unsigned str)] (pieces_couldnt_open (map bv_unsigned str)) _ (rc_canary R) true false)
        with (rpos := rp) (rend := rp + zlength (f_rbuf fs0)) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact SMALL | exact HA
             | reflexivity | exact FC | exact FL | exact BUF | exact BP | exact WB0
             | exact BS | exact WBL | exact NOWR | exact RBN
             | rewrite NCH; exact FD | exact NCH | intros _; reflexivity
             | apply BYf; exact MI
             | exact AOK
             | exact ST | exact SSP | exact MI
             | unfold FPRINTF_DEPTH, GLOBALS_TOP, FILE_BUF_OFF in *; unfold rc_spmain, rc_lo in *; (keep_hyps CEILV sp Af lo P str slack LOB CLO R SPM SP47 fs0 A0 FA4 FA5; lia)
             | idtac "FCO-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' [PO LF].
    destruct (hfile_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB m lo _ f Af fs0 pv nx tail rp f' st' ms' G SR HIN INV NOWR UPD CLO LOS SPM RP0 RP1 GLN PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    unfold store_file. apply implM_upd_lc_last. apply evt_done.
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz27.
  Theorem fprintf_couldnt_open_proof : ltac:(let t := eval cbv delta [fprintf_couldnt_open_proof__stmt] in fprintf_couldnt_open_proof__stmt in exact t).
  Proof using EQB HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo P str slack. ltac2:(SecDiet.SzSec.closeP 'fprintf_couldnt_open_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Glue.

End WithCeil.
End TwB.
End Stdio_glue_pf.
