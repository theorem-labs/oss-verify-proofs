(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Bytes PropExec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_mlib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_zfacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_kit__A3W.MonadF2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require MonadX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.Strnlen_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.
Import Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_zfacts.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_core_cvu__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_core_conv__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_core_cvs__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Export F_printf_core_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  Variable atn : node -> footprint -> machine_state -> Prop.
  Variable sil_ : footprint -> machine_state -> machine_state -> Prop.
  Variable npk_ : node -> option (machine_state -> resp).
  Variable fst_ : node -> resp -> footprint -> footprint -> Prop.
  Local Notation implAM := (implXM atn sil_ npk_ fst_).
  Local Notation implAM_bind := (implXM_bind atn sil_ npk_ fst_).
  Local Notation implAM_mono := (implXM_mono atn sil_ npk_ fst_).
  Local Notation implAM_ret := (implXM_ret atn sil_ npk_ fst_).
  Local Notation implAM_ret_l := (implXM_ret_l atn sil_ npk_ fst_).
  Local Notation implAM_teq := (implXM_teq atn sil_ npk_ fst_).
  Local Notation implAM_unr := (implXM_unr atn sil_ npk_ fst_).
  Local Notation implAM_unr_l := (implXM_unr_l atn sil_ npk_ fst_).
  Variables (Fp FS Ff B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit).
  Hypothesis SFR : sink_frame_stmt Fp FS B BS SINK.
  Hypothesis SFL : sink_flags_stmt Ff SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT.
  Variable RNG : footprint.
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
  Hypothesis HA : (65536 <= A /\ A + zlength fmt <= 204800)%Z.         (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((684904 <= Fp /\ Fp + FS <= 714232) \/ (AP + 8 <= Fp /\ Fp + FS <= VA)
                      \/ (0 < Fp /\ Fp + FS <= lo /\ (Fp + FS <= 65536 \/ 6303744 <= Fp)))%Z.
  Hypothesis SEP_B : ((6297088 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA)
                      \/ (0 < B /\ B + BS <= lo /\ (B + BS <= 65536 \/ 6303744 <= B))
                      \/ (VA + 8 * zlength slots <= B /\ B + BS <= 2^63))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  Hypothesis FF : (Fp <= Ff /\ Ff + 232 <= Fp + FS)%Z.   (* [comment removed for export] *)
  Hypothesis KH : (KHIGH <= lo)%Z.
  Hypothesis RG_stk : rng RNG lo (q - lo).
  Hypothesis RG_img : rng_aimg RNG.
  Hypothesis RG_ap : rng RNG AP 8.
  Hypothesis RG_va : rng RNG VA (8 * zlength slots).
  Hypothesis RG_F : rng RNG Fp FS.
  Hypothesis RG_B : rng RNG B BS.
  Hypothesis RG_fmt : rng RNG A (zlength fmt).
  Hypothesis ENV0 : icptenv m0.
  Hypothesis SO_stk : sobj RNG m0 lo q.
  Hypothesis SO_fmt : sobj RNG m0 A (A + zlength fmt).
  Hypothesis SO_pfx : sobj RNG m0 68460 68469.
  Hypothesis SO_F : sobj RNG m0 Fp (Fp + FS).
  Hypothesis SO_B : sobj RNG m0 B (B + BS).

  (* [comment removed for export] *)
  Local Notation ctx_all := (F_printf_core_common.ctx_all RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp FS B BS q lo AP).
  Local Notation appW_W := (F_printf_core_common.appW_W Fp FS B BS RNG q m0 lo AP LO HAP KH SO_F SO_B).
  Local Notation iesafe_W := (F_printf_core_common.iesafe_W Fp FS Ff B BS q lo AP VA slots LO GLO SEP_F SEP_B HAP HVA BS0 FF KH).
  Local Notation env_now := (F_printf_core_common.env_now Fp FS Ff B BS q m0 lo AP VA slots LO GLO SEP_F SEP_B HAP HVA BS0 FF KH ENV0).
  Local Notation so_now := (F_printf_core_common.so_now Fp FS B BS RNG q m0 lo AP LO HAP KH SO_F SO_B).
  Local Notation arg_ok_s_W := (F_printf_core_common.arg_ok_s_W Fp FS B BS RNG q lo fmt AP slots).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp FS B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp FS B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St) atn sil_ npk_ fst_ RNG).
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp FS B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp FS B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp FS B BS RNG q m0 lo fmt AP slots LO HAP KH SO_F SO_B).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp FS B BS RNG q m0 lo fmt AP slots LO HAP KH SO_F SO_B).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq RNG q gp tp lo AP VA slots LO GLO QHI HAP HVA RG_stk RG_img RG_ap RG_va).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq Fp FS Ff B BS RNG q gp tp m0 lo AP VA slots LO GLO QHI SEP_F SEP_B HAP HVA BS0 FF KH RG_stk RG_img ENV0 SO_F SO_B).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp FS B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT TOK HOUT RNG q gp tp m0 lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP HVA BS0 FF KH RG_stk RG_img RG_F RG_B ENV0 SO_F SO_B).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp FS B BS SINK RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp FS Ff B BS SINK RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp FS B BS RNG q m0 lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Ff q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp FS B BS SINK TOPOK RNG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Ff).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
  (* [comment removed for export] *)
  Ltac len_norm := unfold zlength, zrepeat; rewrite ?repeat_length, ?zb_length, ?length_map, ?length_firstn, ?length_skipn, ?length_app; cbn [length]; try rewrite !Z2Nat.id by lia.
  Ltac rng_side :=
    lazymatch goal with |- rng ?RNG0 ?lo' ?len' =>
      first [ assumption
            | match goal with H : rng RNG0 ?lo ?len |- _ => apply (rng_sub' RNG0 lo len lo' len' H); solve [len_norm; unfold zlength in *; lia] end ]
    end.
  Ltac sobj_side :=
    lazymatch goal with |- sobj ?RNG0 ?m ?a ?b =>
      first [ assumption
            | match goal with H : sobj RNG0 m ?lo' ?hi' |- _ => apply (sobj_sub RNG0 m lo' hi' a b H); solve [len_norm; unfold zlength in *; lia] end ]
    end.
  Ltac hypMU := match goal with H : munch _ m0 _ |- _ => exact H end.
  Ltac hypWM := match goal with H : wmono _ m0 _ |- _ => exact H end.
  (* [comment removed for export] *)
  Local Ltac acc_hint ::=
    first [ lazymatch goal with
            | |- acc_in _ (wa ?e, ?n) => change (wa e) with (Z_to_bv 64 e : word)
            | |- _ => idtac
            end;
            lazymatch goal with
            | |- acc_in _ (Z_to_bv 64 ?E, _) =>
                let X := leftmost E in
                first [ is_Zlit X; solve_acc_with RG_img
                      | constr_eq X Ff; solve_acc_with RG_F
                      | (* [comment removed for export] *)
                        match E with context [Zpos ?p] => let b := eval cbv in (Pos.leb 65536 p) in lazymatch b with true => solve_acc_with RG_img end end ]
            end
          | progress (unfold wa); solve_acc1 ].
  Ltac body_loc_side := unfold body_loc; split; [ zl | split; [ sobj_side | rng_side ] ].
  (* [comment removed for export] *)
  Ltac memset_pad PADa :=
    eapply (memset_wb_spec RNG) with (lo := lo);
    [ exact PADa | match goal with H : mem_inv _ _ |- _ => exact H end | lia | lia | lia | lia
    | match goal with H : stk _ _ _ _ |- _ => exact H end | lia | exact KH
    | eapply env_now; [ hypMU | hypWM ]
    | eapply so_now; [ eapply (sobj_sub _ _ _ _ _ _ SO_stk); lia | hypMU | hypWM ]
    | lia | exact RG_img | rng_side | rng_side ].
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
  Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
  Ltac rd_fmt idx :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | (lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl | N => zl end end) | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evtF_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
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
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
  Ltac out_call :=
    ileave; eapply implAM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 680288 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 6297080 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | |
      | hypMU | hypWM
      | first [ sobj_side | idtac ]
      | first [ rng_side | idtac ] ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call asegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | (lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl | N => zl end end) | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp);
    pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; destruct BLOC as (BLOC & SOb & RGb); unfold INT_MAX in *;
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
      repeat (split; [fastfirst (first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl | (split; [first [assumption | lia | zl] | split; [sobj_side | rng_side]])]) |]); fastfirst (first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl])
    end.

  (* [comment removed for export] *)
  Lemma L_EXIT : S_EXIT.
  Proof using LO HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (LO KH HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_exit.L_EXIT; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_exit.L_EXIT; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_END : S_END.
  Proof using BS0 FF GLO HAP LO QHI SEP_F VAHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HAP LO QHI SEP_F VAHI KH HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_end.L_END; first [eassumption | eexact L_EXIT]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_end.L_END; first [eassumption | eexact L_EXIT] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_EXIT1 : S_EXIT1.
  Proof using LO HA RG_stk RG_img RG_fmt. pin_using (fun (LO KH HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_exit1.L_EXIT1; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_exit1.L_EXIT1; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_SCAN : S_SCAN.
  Proof using HA HF LO RG_stk RG_img RG_fmt. pin_using (fun (HA HF KH LO : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_scan.L_SCAN; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_scan.L_SCAN; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_FLAGS : S_FLAGS.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_flags.L_FLAGS; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_flags.L_FLAGS; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_WLOOP : S_WLOOP.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_width.L_WLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_width.L_WLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ intro; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_width.L_WIDTH; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_width.L_WIDTH; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_PLOOP : S_PLOOP.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_prec.L_PLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_prec.L_PLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_PREC : S_PLOOP -> S_PREC.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ intro; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_prec.L_PREC; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_prec.L_PREC; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_STATE : S_STATE.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_state.L_STATE; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_state.L_STATE; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_DIR : S_DIR.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_dir.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T6 : S_T6.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_t6.L_T6; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_t6.L_T6; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T5 : S_T5.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_t5.L_T5; first [eassumption | eexact L_T6]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_t5.L_T5; first [eassumption | eexact L_T6] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T4 : S_T4.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_t4.L_T4; first [eassumption | eexact L_T5]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_t4.L_T4; first [eassumption | eexact L_T5] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T3 : S_T3.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_t3.L_T3; first [eassumption | eexact L_T4]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_t3.L_T3; first [eassumption | eexact L_T4] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T2 : S_T2.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_t2.L_T2; first [eassumption | eexact L_T3]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_t2.L_T2; first [eassumption | eexact L_T3] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T1 : S_T1.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_t1.L_T1; first [eassumption | eexact L_T2]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_t1.L_T1; first [eassumption | eexact L_T2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_TAIL : S_TAIL.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_tail.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_INTC2 : S_INTC2.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_intc2.L_INTC2; first [eassumption | eexact L_TAIL] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_INTC : S_INTC.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_intc.L_INTC; first [eassumption | eexact L_INTC2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_DLOOP : S_DLOOP.
  Proof using GLO LO QHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (GLO LO QHI KH HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_dloop.L_DLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_dloop.L_DLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_FMTU2 : S_FMTU2.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_fmtu2.L_FMTU2; first [eassumption | eexact L_INTC] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_FMTU : S_FMTU.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_fmtu.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_D : S_CV_D.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_cvd.L_CV_D; first [eassumption | eexact L_FMTU] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_U : S_CV_U.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_cvu.L_CV_U; first [eassumption | eexact L_FMTU] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_XLOOP : S_XLOOP.
  Proof using GLO LO QHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (GLO LO QHI KH HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_xloop.L_XLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_xloop.L_XLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_X : S_CV_X.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_cvx.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_S : S_CV_S.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_cvs.L_CV_S; first [eassumption | eexact L_TAIL] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CONV : S_CONV.
  Proof using BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_conv.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI KH : unit) => tt).
    first [ intro; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_head.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_P1 : S_P1.
  Proof using HA HF LO RG_stk RG_img RG_fmt. pin_using (fun (HA HF LO KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_p1.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_PRO : S_PRO.
  Proof using GLO HA HAP HVA LO QHI RG_stk RG_img RG_fmt. pin_using (fun (GLO HA HAP HVA LO QHI KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_pro.L_PRO; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_pro.L_PRO; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.

  Let HS_PRO := L_PRO.
  Let HS_HEAD := L_HEAD.
  Let HS_P1 := L_P1.
  
  (* [comment removed for export] *)
  Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
      let _ := ctx_all in
      SINK m0 st -> stk asegs m0 lo q -> mem_inv asegs m0 -> bytes_at asegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      rw_cells asegs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
      args_ok Fp FS B BS RNG m0 lo q AP (skipn (Z.to_nat i) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK) (fp_calls (length fmt) fmt args) ->
      (0 < Ff)%Z -> (Ff + 232 <= 2^64)%Z ->
      implAM RNG (printf_model OUT fmt args) st POST
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x9b090) fc0 None m0 (seg_rom asegs)).
  Proof using FRM0 HS_HEAD HS_PRO LO HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (FRM0 HS_HEAD HS_PRO KH LO HA : unit) => tt).
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 st i args _ HS0 ST0 MI0 BY0 VAA0 SSP0 APC0 Hi AOK FPC HF0 HF1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    unfold printf_model. ienter.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Ff); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    pose proof FI as FI'. destruct FI' as (MI & MU & WM & _).
    assert (HS : SINK m st).
    { eapply (SFR [(q + -544, q)]%Z m0 m st HS0 MUq WM); (apply Forall_cons; [cbn [fst snd]; unfold zlength in *; lia | apply Forall_nil]). }
    assert (APC : rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
    { eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
    stmt (HS_HEAD (length fmt)) as NXH.
    jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
      [ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
      | exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
      let _ := ctx_all in
      stk asegs m0 lo q -> mem_inv asegs m0 -> bytes_at asegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      pass1_ok fmt = true ->
      evtF asegs RNG (POST1 0)
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x9b090) fc0 None m0 (seg_rom asegs)).
  Proof using HS_P1 HS_PRO LO HA RG_stk RG_img RG_fmt. pin_using (fun (HS_P1 HS_PRO KH LO HA : unit) => tt).
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
Theorem printf_core_proof : forall atn sil_ npk_ fst_ (St : Type) (Fp FS Ff B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
    (OUT : list Z -> M St unit),
  sink_frame_stmt Fp FS B BS SINK -> sink_flags_stmt Ff SINK -> topok_stmt TOPOK -> out_stmt atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT ->
  printf_core_stmt atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT.
Proof.
  intros atn sil_ npk_ fst_ St Fp FS Ff B BS SINK TOPOK OUT SFR SFL TOK HOUT.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary fmt VA i slots args
         HS BY HF Ha0 APC VAA Hi AOK ST LO GLO SPHI TQ SSP MI FRM HA BS0 FF SEPF SEPB HAP HVA VAHI
         KH ENV SOSTK SOFMT SOPFX SOF SOB RGSTK RGIMG RGAP RGVA RGF RGB RGFMT.
  assert (FPC : Forall (fpcall_stmt Fp B BS SINK TOPOK) (fp_calls (length fmt) fmt args)) by (apply Forall_nil).
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  pose proof (L_CORE2 atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT SFR SFL TOK HOUT RNG ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) VA slots a3 a4 HF LO GLO SPHI TQ eq_refl HA SEPF SEPB HAP HVA VAHI BS0 FF
                      KH RGSTK RGIMG RGAP RGVA RGF RGB RGFMT ENV SOSTK SOFMT SOPFX SOF SOB
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 st i args HS ST MI BY VAA SSP APC Hi AOK FPC) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply (implXM_mono atn sil_ npk_ fst_).
  { apply C; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; lia. }
  cbv beta. intros r st' ms' P. unfold POST, W in P. unfold printf_core_post, SR.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & apv & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & HS' & SSP' & APC' & Hr).
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', apv, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact Hr.
Qed.

Theorem printf_core1_proof : printf_core1_stmt.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
         BY HF P1 Ha0 ST LO GLO SPHI SSP MI HA HAP A2HI RGSTK RGIMG RGFMT.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in LO, GLO, HA.
  pose proof (L_CORE1 684904 232 0 0 RNG ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) (bv_unsigned a2 + 8)%Z [] a3 a4 HF
                      ltac:(unfold PC_DEPTH; lia) ltac:(unfold GLOBALS_TOP; lia) SPHI HA HAP ltac:(lia) RGSTK RGIMG RGFMT
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ST MI BY) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply evtF_mono.
  { apply C; [ | exact SSP | exact P1 ]. unfold va_area. cbn [u64s map concat]. apply bytes_at_nil; lia. }
  cbv beta. intros ms' P. unfold POST1 in P. unfold printf_core1_post.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & SSP').
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact SSP'.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.FP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_mlib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_zfacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_kit__A3W.MonadF2.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.MonadX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.Strnlen_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Import Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_zfacts.   (* [comment removed for export] *)
(* [comment removed for export] *)
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  Variable atn : node -> footprint -> machine_state -> Prop.
  Variable sil_ : footprint -> machine_state -> machine_state -> Prop.
  Variable npk_ : node -> option (machine_state -> resp).
  Variable fst_ : node -> resp -> footprint -> footprint -> Prop.
  Local Notation implAM := (implXM atn sil_ npk_ fst_).
  Local Notation implAM_bind := (implXM_bind atn sil_ npk_ fst_).
  Local Notation implAM_mono := (implXM_mono atn sil_ npk_ fst_).
  Local Notation implAM_ret := (implXM_ret atn sil_ npk_ fst_).
  Local Notation implAM_ret_l := (implXM_ret_l atn sil_ npk_ fst_).
  Local Notation implAM_teq := (implXM_teq atn sil_ npk_ fst_).
  Local Notation implAM_unr := (implXM_unr atn sil_ npk_ fst_).
  Local Notation implAM_unr_l := (implXM_unr_l atn sil_ npk_ fst_).
  Variables (Fp FS Ff B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit).
  Hypothesis SFR : sink_frame_stmt Fp FS B BS SINK.
  Hypothesis SFL : sink_flags_stmt Ff SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT.
  Variable RNG : footprint.
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
  Hypothesis HA : (65536 <= A /\ A + zlength fmt <= 204800)%Z.         (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((685896 <= Fp /\ Fp + FS <= 715256) \/ (AP + 8 <= Fp /\ Fp + FS <= VA)
                      \/ (0 < Fp /\ Fp + FS <= lo /\ (Fp + FS <= 65536 \/ 6307840 <= Fp)))%Z.
  Hypothesis SEP_B : ((6298112 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA)
                      \/ (0 < B /\ B + BS <= lo /\ (B + BS <= 65536 \/ 6307840 <= B))
                      \/ (VA + 8 * zlength slots <= B /\ B + BS <= 2^63))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  Hypothesis FF : (Fp <= Ff /\ Ff + 232 <= Fp + FS)%Z.   (* [comment removed for export] *)
  Hypothesis KH : (KHIGH <= lo)%Z.
  Hypothesis RG_stk : rng RNG lo (q - lo).
  Hypothesis RG_img : rng_aimg RNG.
  Hypothesis RG_ap : rng RNG AP 8.
  Hypothesis RG_va : rng RNG VA (8 * zlength slots).
  Hypothesis RG_F : rng RNG Fp FS.
  Hypothesis RG_B : rng RNG B BS.
  Hypothesis RG_fmt : rng RNG A (zlength fmt).
  Hypothesis ENV0 : icptenv m0.
  Hypothesis SO_stk : sobj RNG m0 lo q.
  Hypothesis SO_fmt : sobj RNG m0 A (A + zlength fmt).
  Hypothesis SO_pfx : sobj RNG m0 68460 68469.
  Hypothesis SO_F : sobj RNG m0 Fp (Fp + FS).
  Hypothesis SO_B : sobj RNG m0 B (B + BS).

  (* [comment removed for export] *)
  Local Notation ctx_all := (A3S.F_printf_core_common.TwB.ctx_all RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (A3S.F_printf_core_common.TwB.W Fp FS B BS q lo AP).
  Local Notation appW_W := (A3S.F_printf_core_common.TwB.appW_W Fp FS B BS RNG q m0 lo AP LO HAP KH SO_F SO_B).
  Local Notation iesafe_W := (A3S.F_printf_core_common.TwB.iesafe_W Fp FS Ff B BS q lo AP VA slots LO GLO SEP_F SEP_B HAP HVA BS0 FF KH).
  Local Notation env_now := (A3S.F_printf_core_common.TwB.env_now Fp FS Ff B BS q m0 lo AP VA slots LO GLO SEP_F SEP_B HAP HVA BS0 FF KH ENV0).
  Local Notation so_now := (A3S.F_printf_core_common.TwB.so_now Fp FS B BS RNG q m0 lo AP LO HAP KH SO_F SO_B).
  Local Notation arg_ok_s_W := (A3S.F_printf_core_common.TwB.arg_ok_s_W Fp FS B BS RNG q lo fmt AP slots).
  Local Notation Fok := (A3S.F_printf_core_common.TwB.Fok F).
  Local Notation Fok_refl := (A3S.F_printf_core_common.TwB.Fok_refl F).
  Local Notation Fok_trans := (A3S.F_printf_core_common.TwB.Fok_trans F).
  Local Notation POST := (A3S.F_printf_core_common.TwB.POST (St:=St) Fp FS B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary AP).
  Local Notation hi_cells := (A3S.F_printf_core_common.TwB.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (A3S.F_printf_core_common.TwB.lo_cells AP nla nlt).
  Local Notation finv := (A3S.F_printf_core_common.TwB.finv Fp FS B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (A3S.F_printf_core_common.TwB.fmt_rng fmt HF).
  Local Notation implM_eq_ms := (A3S.F_printf_core_common.TwB.implM_eq_ms (St:=St) atn sil_ npk_ fst_ RNG).
  Local Notation sink_store := (A3S.F_printf_core_common.TwB.sink_store (St:=St) Fp FS B BS SINK SFR).
  Local Notation sink_call := (A3S.F_printf_core_common.TwB.sink_call (St:=St) Fp FS B BS SINK SFR).
  Local Notation arg_ok_W := (A3S.F_printf_core_common.TwB.arg_ok_W Fp FS B BS RNG q m0 lo fmt AP slots LO HAP KH SO_F SO_B).
  Local Notation args_ok_W := (A3S.F_printf_core_common.TwB.args_ok_W Fp FS B BS RNG q m0 lo fmt AP slots LO HAP KH SO_F SO_B).
  Local Notation lo_cells14 := (A3S.F_printf_core_common.TwB.lo_cells14 AP nla nlt).
  Local Notation lo_split := (A3S.F_printf_core_common.TwB.lo_split q AP nla nlt).
  Local Notation lo_join := (A3S.F_printf_core_common.TwB.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (A3S.F_printf_core_common.TwB.pop_arg_callq RNG q gp tp lo AP VA slots LO GLO QHI HAP HVA RG_stk RG_img RG_ap RG_va).
  Local Notation strnlen_callq := (A3S.F_printf_core_common.TwB.strnlen_callq Fp FS Ff B BS RNG q gp tp m0 lo AP VA slots LO GLO QHI SEP_F SEP_B HAP HVA BS0 FF KH RG_stk RG_img ENV0 SO_F SO_B).
  Local Notation out_postq := (A3S.F_printf_core_common.TwB.out_postq (St:=St) Fp FS B BS SINK q gp tp lo canary).
  Local Notation out_callq := (A3S.F_printf_core_common.TwB.out_callq (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT TOK HOUT RNG q gp tp m0 lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP HVA BS0 FF KH RG_stk RG_img RG_F RG_B ENV0 SO_F SO_B).
  Local Notation S_EXIT := (A3S.F_printf_core_common.TwB.S_EXIT (St:=St) Fp FS B BS SINK RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (A3S.F_printf_core_common.TwB.S_SCAN Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (A3S.F_printf_core_common.TwB.S_FLAGS Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (A3S.F_printf_core_common.TwB.S_WLOOP Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (A3S.F_printf_core_common.TwB.S_WIDTH Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (A3S.F_printf_core_common.TwB.S_PLOOP Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (A3S.F_printf_core_common.TwB.S_PREC Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (A3S.F_printf_core_common.TwB.S_STATE Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (A3S.F_printf_core_common.TwB.S_DIR Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (A3S.F_printf_core_common.TwB.S_END (St:=St) Fp FS Ff B BS SINK RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (A3S.F_printf_core_common.TwB.S_HEAD (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (A3S.F_printf_core_common.TwB.S_CONV (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (A3S.F_printf_core_common.TwB.body_loc Fp FS B BS RNG q m0 lo).
  Local Notation S_TAIL := (A3S.F_printf_core_common.TwB.S_TAIL (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (A3S.F_printf_core_common.TwB.tregs Ff q gp tp A).
  Local Notation tinv := (A3S.F_printf_core_common.TwB.tinv (St:=St) Fp FS B BS SINK TOPOK RNG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (A3S.F_printf_core_common.TwB.S_T6 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (A3S.F_printf_core_common.TwB.S_T5 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (A3S.F_printf_core_common.TwB.S_T4 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (A3S.F_printf_core_common.TwB.S_T3 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (A3S.F_printf_core_common.TwB.S_T2 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (A3S.F_printf_core_common.TwB.S_T1 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (A3S.F_printf_core_common.TwB.S_INTC2 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (A3S.F_printf_core_common.TwB.S_INTC (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (A3S.F_printf_core_common.TwB.dloop_post q gp tp).
  Local Notation S_DLOOP := (A3S.F_printf_core_common.TwB.S_DLOOP RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (A3S.F_printf_core_common.TwB.S_FMTU2 (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (A3S.F_printf_core_common.TwB.S_FMTU (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (A3S.F_printf_core_common.TwB.S_CV_D (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (A3S.F_printf_core_common.TwB.S_CV_U (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (A3S.F_printf_core_common.TwB.xloop_post q gp tp).
  Local Notation S_XLOOP := (A3S.F_printf_core_common.TwB.S_XLOOP RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (A3S.F_printf_core_common.TwB.S_CV_X (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (A3S.F_printf_core_common.TwB.S_CV_S (St:=St) atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (A3S.F_printf_core_common.TwB.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (A3S.F_printf_core_common.TwB.S_EXIT1 Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (A3S.F_printf_core_common.TwB.S_P1 Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (A3S.F_printf_core_common.TwB.S_PRO Fp FS B BS RNG ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Ff).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
  (* [comment removed for export] *)
  Ltac len_norm := unfold zlength, zrepeat; rewrite ?repeat_length, ?zb_length, ?length_map, ?length_firstn, ?length_skipn, ?length_app; cbn [length]; try rewrite !Z2Nat.id by lia.
  Ltac rng_side :=
    lazymatch goal with |- rng ?RNG0 ?lo' ?len' =>
      first [ assumption
            | match goal with H : rng RNG0 ?lo ?len |- _ => apply (rng_sub' RNG0 lo len lo' len' H); solve [len_norm; unfold zlength in *; lia] end ]
    end.
  Ltac sobj_side :=
    lazymatch goal with |- sobj ?RNG0 ?m ?a ?b =>
      first [ assumption
            | match goal with H : sobj RNG0 m ?lo' ?hi' |- _ => apply (sobj_sub RNG0 m lo' hi' a b H); solve [len_norm; unfold zlength in *; lia] end ]
    end.
  Ltac hypMU := match goal with H : munch _ m0 _ |- _ => exact H end.
  Ltac hypWM := match goal with H : wmono _ m0 _ |- _ => exact H end.
  (* [comment removed for export] *)
  Local Ltac acc_hint ::=
    first [ lazymatch goal with
            | |- acc_in _ (wa ?e, ?n) => change (wa e) with (Z_to_bv 64 e : word)
            | |- _ => idtac
            end;
            lazymatch goal with
            | |- acc_in _ (Z_to_bv 64 ?E, _) =>
                let X := leftmost E in
                first [ is_Zlit X; solve_acc_with RG_img
                      | constr_eq X Ff; solve_acc_with RG_F
                      | (* [comment removed for export] *)
                        match E with context [Zpos ?p] => let b := eval cbv in (Pos.leb 65536 p) in lazymatch b with true => solve_acc_with RG_img end end ]
            end
          | progress (unfold wa); solve_acc1 ].
  Ltac body_loc_side := unfold body_loc; split; [ zl | split; [ sobj_side | rng_side ] ].
  (* [comment removed for export] *)
  Ltac memset_pad PADa :=
    eapply (memset_wb_spec RNG) with (lo := lo);
    [ exact PADa | match goal with H : mem_inv _ _ |- _ => exact H end | lia | lia | lia | lia
    | match goal with H : stk _ _ _ _ |- _ => exact H end | lia | exact KH
    | eapply env_now; [ hypMU | hypWM ]
    | eapply so_now; [ eapply (sobj_sub _ _ _ _ _ _ SO_stk); lia | hypMU | hypWM ]
    | lia | exact RG_img | rng_side | rng_side ].
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
  Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
  Ltac rd_fmt idx :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | (lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl | N => zl end end) | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evtF_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
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
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
  Ltac out_call :=
    ileave; eapply implAM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 681280 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 6298104 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | |
      | hypMU | hypWM
      | first [ sobj_side | idtac ]
      | first [ rng_side | idtac ] ]
    | cbv beta ].
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call asegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | (lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl | N => zl end end) | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp);
    pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; destruct BLOC as (BLOC & SOb & RGb); unfold INT_MAX in *;
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
      repeat (split; [fastfirst (first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl | (split; [first [assumption | lia | zl] | split; [sobj_side | rng_side]])]) |]); fastfirst (first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl])
    end.

  (* [comment removed for export] *)
  Lemma L_EXIT : S_EXIT.
  Proof using LO HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (LO KH HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_exit.TwB.L_EXIT; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_exit.TwB.L_EXIT; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_END : S_END.
  Proof using BS0 FF GLO HAP LO QHI SEP_F VAHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HAP LO QHI SEP_F VAHI KH HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_end.TwB.L_END; first [eassumption | eexact L_EXIT]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_end.TwB.L_END; first [eassumption | eexact L_EXIT] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_EXIT1 : S_EXIT1.
  Proof using LO HA RG_stk RG_img RG_fmt. pin_using (fun (LO KH HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_exit1.TwB.L_EXIT1; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_exit1.TwB.L_EXIT1; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_SCAN : S_SCAN.
  Proof using HA HF LO RG_stk RG_img RG_fmt. pin_using (fun (HA HF KH LO : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_scan.TwB.L_SCAN; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_scan.TwB.L_SCAN; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_FLAGS : S_FLAGS.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_flags.TwB.L_FLAGS; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_flags.TwB.L_FLAGS; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_WLOOP : S_WLOOP.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_width.TwB.L_WLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_width.TwB.L_WLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ intro; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_width.TwB.L_WIDTH; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_width.TwB.L_WIDTH; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_PLOOP : S_PLOOP.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_prec.TwB.L_PLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_prec.TwB.L_PLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_PREC : S_PLOOP -> S_PREC.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ intro; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_prec.TwB.L_PREC; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_prec.TwB.L_PREC; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_STATE : S_STATE.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_state.TwB.L_STATE; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_state.TwB.L_STATE; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_DIR : S_DIR.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_dir.TwB.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_dir.TwB.L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T6 : S_T6.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_t6.TwB.L_T6; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_t6.TwB.L_T6; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T5 : S_T5.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_t5.TwB.L_T5; first [eassumption | eexact L_T6]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_t5.TwB.L_T5; first [eassumption | eexact L_T6] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T4 : S_T4.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_t4.TwB.L_T4; first [eassumption | eexact L_T5]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_t4.TwB.L_T4; first [eassumption | eexact L_T5] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T3 : S_T3.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_t3.TwB.L_T3; first [eassumption | eexact L_T4]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_t3.TwB.L_T3; first [eassumption | eexact L_T4] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T2 : S_T2.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_t2.TwB.L_T2; first [eassumption | eexact L_T3]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_t2.TwB.L_T2; first [eassumption | eexact L_T3] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_T1 : S_T1.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_t1.TwB.L_T1; first [eassumption | eexact L_T2]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_t1.TwB.L_T1; first [eassumption | eexact L_T2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_TAIL : S_TAIL.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_tail.TwB.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_tail.TwB.L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_INTC2 : S_INTC2.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_intc2.TwB.L_INTC2; first [eassumption | eexact L_TAIL]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_intc2.TwB.L_INTC2; first [eassumption | eexact L_TAIL] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_INTC : S_INTC.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_intc.TwB.L_INTC; first [eassumption | eexact L_INTC2]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_intc.TwB.L_INTC; first [eassumption | eexact L_INTC2] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_DLOOP : S_DLOOP.
  Proof using GLO LO QHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (GLO LO QHI KH HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_dloop.TwB.L_DLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_dloop.TwB.L_DLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_FMTU2 : S_FMTU2.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_fmtu2.TwB.L_FMTU2; first [eassumption | eexact L_INTC]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_fmtu2.TwB.L_FMTU2; first [eassumption | eexact L_INTC] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_FMTU : S_FMTU.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_fmtu.TwB.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_fmtu.TwB.L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_D : S_CV_D.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_cvd.TwB.L_CV_D; first [eassumption | eexact L_FMTU]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_cvd.TwB.L_CV_D; first [eassumption | eexact L_FMTU] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_U : S_CV_U.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_cvu.TwB.L_CV_U; first [eassumption | eexact L_FMTU]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_cvu.TwB.L_CV_U; first [eassumption | eexact L_FMTU] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_XLOOP : S_XLOOP.
  Proof using GLO LO QHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (GLO LO QHI KH HA : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_xloop.TwB.L_XLOOP; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_xloop.TwB.L_XLOOP; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_X : S_CV_X.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_cvx.TwB.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_cvx.TwB.L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CV_S : S_CV_S.
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_cvs.TwB.L_CV_S; first [eassumption | eexact L_TAIL]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvs__A3S.F_printf_core_cvs.TwB.L_CV_S; first [eassumption | eexact L_TAIL] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_CONV : S_CONV.
  Proof using BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_conv.TwB.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_conv.TwB.L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI KH : unit) => tt).
    first [ intro; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_head.TwB.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_head.TwB.L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_P1 : S_P1.
  Proof using HA HF LO RG_stk RG_img RG_fmt. pin_using (fun (HA HF LO KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_p1.TwB.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_conv__A3S.F_printf_core_p1.TwB.L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.
  Lemma L_PRO : S_PRO.
  Proof using GLO HA HAP HVA LO QHI RG_stk RG_img RG_fmt. pin_using (fun (GLO HA HAP HVA LO QHI KH : unit) => tt).
    first [ apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_pro.TwB.L_PRO; first [eassumption]
          | intros; eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_cvu__A3S.F_printf_core_pro.TwB.L_PRO; first [eassumption] ].
    (* [comment removed for export] *)
    Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots | exact RNG | exact gp | exact tp | exact canary | exact A | exact AP | exact VA | exact nla | exact nlt | exact s0e | exact lo].
  Qed.

  Let HS_PRO := L_PRO.
  Let HS_HEAD := L_HEAD.
  Let HS_P1 := L_P1.
  
  (* [comment removed for export] *)
  Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
      let _ := ctx_all in
      SINK m0 st -> stk asegs m0 lo q -> mem_inv asegs m0 -> bytes_at asegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      rw_cells asegs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
      args_ok Fp FS B BS RNG m0 lo q AP (skipn (Z.to_nat i) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK) (fp_calls (length fmt) fmt args) ->
      (0 < Ff)%Z -> (Ff + 232 <= 2^64)%Z ->
      implAM RNG (printf_model OUT fmt args) st POST
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x9b474) fc0 None m0 (seg_rom asegs)).
  Proof using FRM0 HS_HEAD HS_PRO LO HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (FRM0 HS_HEAD HS_PRO KH LO HA : unit) => tt).
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 st i args _ HS0 ST0 MI0 BY0 VAA0 SSP0 APC0 Hi AOK FPC HF0 HF1.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    unfold printf_model. ienter.
    stmt HS_PRO as NXP.
    eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Ff); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
    intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
    pose proof FI as FI'. destruct FI' as (MI & MU & WM & _).
    assert (HS : SINK m st).
    { eapply (SFR [(q + -544, q)]%Z m0 m st HS0 MUq WM); (apply Forall_cons; [cbn [fst snd]; unfold zlength in *; lia | apply Forall_nil]). }
    assert (APC : rw_cells asegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
    { eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
    stmt (HS_HEAD (length fmt)) as NXH.
    jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
      [ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
      | exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
      let _ := ctx_all in
      stk asegs m0 lo q -> mem_inv asegs m0 -> bytes_at asegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      pass1_ok fmt = true ->
      evtF asegs RNG (POST1 0)
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x9b474) fc0 None m0 (seg_rom asegs)).
  Proof using HS_P1 HS_PRO LO HA RG_stk RG_img RG_fmt. pin_using (fun (HS_P1 HS_PRO KH LO HA : unit) => tt).
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
Theorem printf_core_proof : forall atn sil_ npk_ fst_ (St : Type) (Fp FS Ff B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
    (OUT : list Z -> M St unit),
  sink_frame_stmt Fp FS B BS SINK -> sink_flags_stmt Ff SINK -> topok_stmt TOPOK -> out_stmt atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT ->
  printf_core_stmt atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT.
Proof.
  intros atn sil_ npk_ fst_ St Fp FS Ff B BS SINK TOPOK OUT SFR SFL TOK HOUT.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary fmt VA i slots args
         HS BY HF Ha0 APC VAA Hi AOK ST LO GLO SPHI TQ SSP MI FRM HA BS0 FF SEPF SEPB HAP HVA VAHI
         KH ENV SOSTK SOFMT SOPFX SOF SOB RGSTK RGIMG RGAP RGVA RGF RGB RGFMT.
  assert (FPC : Forall (fpcall_stmt Fp B BS SINK TOPOK) (fp_calls (length fmt) fmt args)) by (apply Forall_nil).
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  pose proof (L_CORE2 atn sil_ npk_ fst_ Fp FS Ff B BS SINK TOPOK OUT SFR SFL TOK HOUT RNG ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) VA slots a3 a4 HF LO GLO SPHI TQ eq_refl HA SEPF SEPB HAP HVA VAHI BS0 FF
                      KH RGSTK RGIMG RGAP RGVA RGF RGB RGFMT ENV SOSTK SOFMT SOPFX SOF SOB
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 st i args HS ST MI BY VAA SSP APC Hi AOK FPC) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply (implXM_mono atn sil_ npk_ fst_).
  { apply C; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; lia. }
  cbv beta. intros r st' ms' P. unfold POST, W in P. unfold printf_core_post, SR.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & apv & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & HS' & SSP' & APC' & Hr).
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', apv, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact Hr.
Qed.

Theorem printf_core1_proof : printf_core1_stmt.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
         BY HF P1 Ha0 ST LO GLO SPHI SSP MI HA HAP A2HI RGSTK RGIMG RGFMT.
  subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
  unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in LO, GLO, HA.
  pose proof (L_CORE1 685896 232 0 0 RNG ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
                      (bv_unsigned a1) fmt (bv_unsigned a2) (bv_unsigned a2 + 8)%Z [] a3 a4 HF
                      ltac:(unfold PC_DEPTH; lia) ltac:(unfold GLOBALS_TOP; lia) SPHI HA HAP ltac:(lia) RGSTK RGIMG RGFMT
                      t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ST MI BY) as C.
  cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
  eapply evtF_mono.
  { apply C; [ | exact SSP | exact P1 ]. unfold va_area. cbn [u64s map concat]. apply bytes_at_nil; lia. }
  cbv beta. intros ms' P. unfold POST1 in P. unfold printf_core1_post.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & SSP').
  exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
  rewrite Z_to_bv_bv_unsigned.
  repeat (split; [assumption || reflexivity|]). exact SSP'.
Qed.
End TwB.
