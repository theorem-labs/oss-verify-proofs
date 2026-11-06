(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Walk Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Bytes PropExec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_kit__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require MonadX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_core_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_printf_core_cvu.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import F_printf_core_common.
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

  Hypothesis HS_FMTU : S_FMTU.

  (* [comment removed for export] *)
  Lemma L_CV_U : S_CV_U.
  Proof using BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR KH : unit) => tt).
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u pfx s2s za pl plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    stmt (HS_FMTU fuel HH) as NX.
    ienter.
    zs. zs. zs. zs. zs. zs.
    jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := u) (prefix := []) (PFXA := 68460%Z));
      [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
      | intros m' MI'; exact (pfx_sub m' 0 0 MI' ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
  Qed.
End PrintfCore.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
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

  Hypothesis HS_FMTU : S_FMTU.

  (* [comment removed for export] *)
  Lemma L_CV_U : S_CV_U.
  Proof using BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR KH : unit) => tt).
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u pfx s2s za pl plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    stmt (HS_FMTU fuel HH) as NX.
    ienter.
    zs. zs. zs. zs. zs. zs.
    jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := u) (prefix := []) (PFXA := 68460%Z));
      [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
      | intros m' MI'; exact (pfx_sub m' 0 0 MI' ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_cvu.

(* [comment removed for export] *)
Module F_printf_core_dir.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import F_printf_core_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
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

  Hypothesis HS_FLAGS : S_FLAGS.
  Hypothesis HS_WIDTH : S_WIDTH.
  Hypothesis HS_PREC : S_PREC.
  Hypothesis HS_STATE : S_STATE.

  (* [comment removed for export] *)
  Definition L_DIR__stmt : Prop := S_DIR.
  Section Sz1.
  Variables x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q i d rest pfx s2s za pl plp alo ahi j128 : ltac2:(SecDiet.SzSec.tyM 'L_DIR__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma L_DIR__body : ltac2:(SecDiet.SzSec.bodyP 'L_DIR__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HF HS_FLAGS HS_PREC HS_STATE HS_WIDTH LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF HS_FLAGS HS_PREC HS_STATE HS_WIDTH KH LO HA : unit) => tt).
    intros _
           FI LOW Hi Hi1 PD HK.
    pose proof FI as FI'. dest_finv FI. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
    pose proof (parse_dir_shape _ _ _ PD) as (POSN & SH).
    destruct (parse_flags (sfx (i + 1)) 0) as [fl s1] eqn:PF.
    destruct SH as (Efl & c1' & s1b & Es1 & N42 & s2 & G & c2 & s2b & Es2 & PX).
    (* [comment removed for export] *)
    destruct (parse_flags_suffix _ _ _ _ PF) as (n1 & Hs1 & Hn1). rewrite sfx_skipn in Hs1 by lia. set (k1 := (i + 1 + Z.of_nat n1)%Z) in Hs1.
    rewrite Hs1 in Es1. destruct (sfx_cons_inv fmt k1 c1' s1b ltac:(lia) Es1) as (Hk1 & Ec1' & Es1b).
    destruct (getint_suffix _ _ _ _ G) as (n2 & Hs2 & Hn2). rewrite Hs1, sfx_skipn in Hs2 by lia. set (k2 := (k1 + Z.of_nat n2)%Z) in Hs2.
    rewrite Hs2 in Es2. destruct (sfx_cons_inv fmt k2 c2 s2b ltac:(lia) Es2) as (Hk2 & Ec2 & Es2b).
    assert (Hi1' : (i + 1 < zlength fmt)%Z) by zl.
    rewrite (sfx_cons fmt (i + 1)) in POSN, PF by zl.
    (* [comment removed for export] *)
    assert (POSTFLAGS : forall (t0 t1 a3 a4 a5 a6 a7 : word),
      evtF asegs RNG Q
        (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) a3 a4 a5 a6 a7
                 x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x9b2b8) fc None m (seg_rom asegs))).
    { intros t0 t1 a3 a4 a5 a6 a7.
      pose proof (parse_flags_range (sfx (i + 1)) 0 ltac:(lia)) as FLR. rewrite (sfx_cons fmt (i + 1)), PF in FLR by zl. cbn [fst] in FLR.
      stmt HS_WIDTH as NXW. jump (eapply NXW with (k1 := k1) (w := d_w d) (s2 := s2); [exact FI' | exact LOW' | lia | rewrite <- Hs1; exact G | rewrite Hs2, Es2; discriminate | ]).
      intros k2' t0' t1' a1' a3' a4' a5' a6' a7' Hk2' Hs2' Hnd Hw.
      assert (k2' = k2).
      { pose proof (sfx_length fmt k2 ltac:(zl)) as L1. pose proof (sfx_length fmt k2' ltac:(zl)) as L2. rewrite <- Hs2', Hs2 in L2. lia. }
      subst k2'.
      stmt HS_PREC as NXP. stmt HS_STATE as NXS.
      (* [comment removed for export] *)
      assert (STATEK : forall (k3 t : Z) (s4 : list Z) (t1w a1w a3w a4w : word),
        (0 <= k3 < zlength fmt)%Z -> (i + 1 <= k3)%Z -> (-1 <= d_p d <= INT_MAX)%Z -> sfx k3 = t :: s4 -> dir_type d t s4 rest ->
        evtF asegs RNG Q
          (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) t1w x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) a1w (Z_to_bv 64 (A + k3)) a3w a4w (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                   x18 x19 x20 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 fl) (Z_to_bv 64 (d_p d)) x26 x27 x28 x29 x30 x31)
              Ft (Z_to_bv 64 0x9b4d8) fc None m (seg_rom asegs))).
      { intros k3 t s4 t1w a1w a3w a4w Hk3 Hik3 Hp Es3k DT.
        destruct (sfx_cons_inv fmt k3 t s4 ltac:(lia) Es3k) as (_ & Et & Es4).
        destruct DT as [(N122 & Hdt & Hps & Hrest & CT) | (E122 & Hps & t2 & s5 & Es45 & Hdt & Hrest & CT)].
        - jump (eapply NXS with (k3 := k3) (kn := (k3 + 1)%Z) (ty := d_ty d) (ps := 0%Z);
                [exact FI' | lia | left; rewrite <- Et; repeat split; fastfirst (first [lia | exact CT | reflexivity]) | ]).
          intros a2q a3q2.
          jump (apply (HK (k3 + 1)%Z); [zl | rewrite Hrest, Es4; reflexivity | replace (k3 + 1 - 1)%Z with k3 by lia; rewrite <- Et, Hdt; reflexivity | lia | lia | lia]).
        - rewrite Es4 in Es45. destruct (sfx_cons_inv fmt (k3 + 1) t2 s5 ltac:(lia) Es45) as (Hk31 & Et2 & Es5).
          jump (eapply NXS with (k3 := k3) (kn := (k3 + 2)%Z) (ty := d_ty d) (ps := ST_ZTPRE);
                [exact FI' | lia | right; rewrite <- Et, <- Et2; repeat split; first [zl | exact E122 | exact CT | reflexivity] | ]).
          intros a2q a3q2.
          jump (apply (HK (k3 + 2)%Z); [zl | rewrite Hrest, Es5; f_equal; lia | replace (k3 + 2 - 1)%Z with (k3 + 1)%Z by lia; rewrite <- Et2, Hdt; reflexivity | lia | lia | lia]). }
      destruct PX as [(N46 & Hpq & Hxp & DT) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & t & s4 & Es3 & DT)].
      - (* [comment removed for export] *)
        jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := k2); [exact FI' | exact LOW' | lia | | ]).
        { left. rewrite <- Ec2, Hxp. repeat split; try assumption; reflexivity. }
        intros a1q a3q a4q Hp.
        jump (eapply (STATEK k2 c2 s2b); [lia | lia | exact Hp | exact Es2 | exact DT]).
      - (* [comment removed for export] *)
        rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
        destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
        rewrite Hs3 in Es3.
        assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
        destruct (sfx_cons_inv fmt (k2 + 1 + Z.of_nat n3) t s4 Hk30 Es3) as (Hk3 & Et & Es4).
        jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := (k2 + 1 + Z.of_nat n3)%Z); [exact FI' | exact LOW' | lia | | ]).
        { right. rewrite Hxp. split; [congruence|]. split; [reflexivity|]. split; [zl|]. split; [rewrite <- Ec3; exact N42q|].
          split; [rewrite <- Es2b, <- Hs3; exact G2 | zl]. }
        intros a1q a3q a4q Hp.
        jump (eapply (STATEK (k2 + 1 + Z.of_nat n3)%Z t s4); [lia | lia | exact Hp | exact Es3 | exact DT]). }
    (* [comment removed for export] *)
    assert (FL34 : forall (a3 a4 a5 : word), evtF asegs RNG Q
      (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt (i + 1))) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 (Z_to_bv 64 1) x17
               x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x9b228) fc None m (seg_rom asegs))).
    { intros a3q a4q a5q. pose proof (fmt_rng (i + 1) ltac:(zl)) as RG.
      (* [comment removed for export] *)
      assert (NOFLAG : flag_bit (znth fmt (i + 1)) = None -> fl = 0%Z /\ k1 = (i + 1)%Z).
      { intros NF. rewrite (parse_flags_cons_none _ _ _ NF) in PF. injection PF as Efl0 Es1q. split; [congruence|].
        pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt (i + 1) ltac:(zl)) as L2.
        rewrite (sfx_cons fmt (i + 1)) in L2 by zl. rewrite Es1q, Hs1 in L2. lia. }
      zs. zs. zs. brf K2.
      - (* [comment removed for export] *)
        assert (NF : flag_bit (znth fmt (i + 1)) = None).
        { destruct (flag_bit (znth fmt (i + 1))) eqn:E; [|reflexivity]. exfalso.
          pose proof (flag_bit_range (znth fmt (i + 1)) ltac:(congruence)) as R. rewrite land_M64_id in K2 by lia. lia. }
        destruct (NOFLAG NF) as [Efl0 Ek1].
        zs. zs. zs. brf K3. { exfalso. apply N42. rewrite Ec1', Ek1. exact K3. }
        jump (apply POSTFLAGS).
      - assert (Hc : (32 <= znth fmt (i + 1) < 64)%Z) by (apply (proj1 (sp_test _ RG)); lia).
        rewrite (land_M64_id (znth fmt (i + 1) + -32)) in * by lia.
        zs. zs. zs. zs. zs. brf K3.
        + (* [comment removed for export] *)
          change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
          assert (NF : flag_bit (znth fmt (i + 1)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
          destruct (NOFLAG NF) as [Efl0 Ek1].
          zs. zs. brf K4; [ jump (apply POSTFLAGS) | exfalso; apply N42; rewrite Ec1', Ek1; exact K4 ].
        + (* [comment removed for export] *)
          change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
          destruct (flag_bit (znth fmt (i + 1))) as [b|] eqn:E.
          2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
          pose proof (flag_some _ _ Hc E) as [Hfw Hb].
          rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
          zs.
          stmt HS_FLAGS as NXF. jump (eapply NXF with (p := (i + 1)%Z) (k := 1%Z) (fl := 0%Z) (b := b) (FL := fl) (s1 := s1);
                 [exact FI' | lia | lia | zl | rewrite unsigned_lit_land; exact Hfw | lia | lia | rewrite Z.lor_0_l; exact PF | rewrite Hs1, Es1; discriminate | ]).
          intros k' c' a3' a4' a5' Hk' Hs1' Hc' HN HFL.
          assert (Ek1 : k' = k1).
          { pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt k' ltac:(zl)) as L2. rewrite <- Hs1', Hs1 in L2. lia. }
          subst k'. subst c'. pose proof (fmt_rng k1 ltac:(zl)) as RGk.
          zs. zs. brf K4; [ | exfalso; apply N42; rewrite Ec1'; exact K4 ].
          jump (apply POSTFLAGS). }
    (* [comment removed for export] *)
    rd_fmt (i + 1)%Z. zs. fix_u8 (i + 1)%Z. zs. zs. zs. zs. zs. brf K.
    - (* [comment removed for export] *) zs. zs. apply FL34.
    - assert (DG : is_digit (znth fmt (i + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
      assert (Hi2 : (i + 2 < zlength fmt)%Z).
      { destruct (Z.lt_ge_cases (i + 2) (zlength fmt)); [assumption|]. exfalso.
        rewrite (sfx_nil fmt (i + 1 + 1)) in POSN by lia. rewrite DG in POSN. discriminate. }
      replace (i + 1 + 1)%Z with (i + 2)%Z in POSN by lia.
      rewrite (sfx_cons fmt (i + 2)) in POSN by zl. rewrite DG in POSN. cbn [andb] in POSN. apply Z.eqb_neq in POSN.
      rd_fmt (i + 2)%Z. zs. fix_u8 (i + 2)%Z. zs. zs. zs. zs. br K1. apply FL34.
  Qed.
  End Sz1.
  Lemma L_DIR : ltac:(let t := eval cbv delta [L_DIR__stmt] in L_DIR__stmt in exact t).
  Proof using HF HS_FLAGS HS_PREC HS_STATE HS_WIDTH LO HA RG_stk RG_img RG_fmt. intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q i d rest pfx s2s za pl plp alo ahi j128. ltac2:(SecDiet.SzSec.closeP 'L_DIR__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
(* [comment removed for export] *)
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

  Hypothesis HS_FLAGS : S_FLAGS.
  Hypothesis HS_WIDTH : S_WIDTH.
  Hypothesis HS_PREC : S_PREC.
  Hypothesis HS_STATE : S_STATE.

  (* [comment removed for export] *)
  Definition L_DIR__stmt : Prop := S_DIR.
  Section Sz1.
  Variables x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q i d rest pfx s2s za pl plp alo ahi j128 : ltac2:(SecDiet.SzSec.tyM 'L_DIR__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma L_DIR__body : ltac2:(SecDiet.SzSec.bodyP 'L_DIR__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HF HS_FLAGS HS_PREC HS_STATE HS_WIDTH LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF HS_FLAGS HS_PREC HS_STATE HS_WIDTH KH LO HA : unit) => tt).
    intros _
           FI LOW Hi Hi1 PD HK.
    pose proof FI as FI'. dest_finv FI. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
    pose proof (parse_dir_shape _ _ _ PD) as (POSN & SH).
    destruct (parse_flags (sfx (i + 1)) 0) as [fl s1] eqn:PF.
    destruct SH as (Efl & c1' & s1b & Es1 & N42 & s2 & G & c2 & s2b & Es2 & PX).
    (* [comment removed for export] *)
    destruct (parse_flags_suffix _ _ _ _ PF) as (n1 & Hs1 & Hn1). rewrite sfx_skipn in Hs1 by lia. set (k1 := (i + 1 + Z.of_nat n1)%Z) in Hs1.
    rewrite Hs1 in Es1. destruct (sfx_cons_inv fmt k1 c1' s1b ltac:(lia) Es1) as (Hk1 & Ec1' & Es1b).
    destruct (getint_suffix _ _ _ _ G) as (n2 & Hs2 & Hn2). rewrite Hs1, sfx_skipn in Hs2 by lia. set (k2 := (k1 + Z.of_nat n2)%Z) in Hs2.
    rewrite Hs2 in Es2. destruct (sfx_cons_inv fmt k2 c2 s2b ltac:(lia) Es2) as (Hk2 & Ec2 & Es2b).
    assert (Hi1' : (i + 1 < zlength fmt)%Z) by zl.
    rewrite (sfx_cons fmt (i + 1)) in POSN, PF by zl.
    (* [comment removed for export] *)
    assert (POSTFLAGS : forall (t0 t1 a3 a4 a5 a6 a7 : word),
      evtF asegs RNG Q
        (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) a3 a4 a5 a6 a7
                 x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x9b69c) fc None m (seg_rom asegs))).
    { intros t0 t1 a3 a4 a5 a6 a7.
      pose proof (parse_flags_range (sfx (i + 1)) 0 ltac:(lia)) as FLR. rewrite (sfx_cons fmt (i + 1)), PF in FLR by zl. cbn [fst] in FLR.
      stmt HS_WIDTH as NXW. jump (eapply NXW with (k1 := k1) (w := d_w d) (s2 := s2); [exact FI' | exact LOW' | lia | rewrite <- Hs1; exact G | rewrite Hs2, Es2; discriminate | ]).
      intros k2' t0' t1' a1' a3' a4' a5' a6' a7' Hk2' Hs2' Hnd Hw.
      assert (k2' = k2).
      { pose proof (sfx_length fmt k2 ltac:(zl)) as L1. pose proof (sfx_length fmt k2' ltac:(zl)) as L2. rewrite <- Hs2', Hs2 in L2. lia. }
      subst k2'.
      stmt HS_PREC as NXP. stmt HS_STATE as NXS.
      (* [comment removed for export] *)
      assert (STATEK : forall (k3 t : Z) (s4 : list Z) (t1w a1w a3w a4w : word),
        (0 <= k3 < zlength fmt)%Z -> (i + 1 <= k3)%Z -> (-1 <= d_p d <= INT_MAX)%Z -> sfx k3 = t :: s4 -> dir_type d t s4 rest ->
        evtF asegs RNG Q
          (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) t1w x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) a1w (Z_to_bv 64 (A + k3)) a3w a4w (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                   x18 x19 x20 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 fl) (Z_to_bv 64 (d_p d)) x26 x27 x28 x29 x30 x31)
              Ft (Z_to_bv 64 0x9b8bc) fc None m (seg_rom asegs))).
      { intros k3 t s4 t1w a1w a3w a4w Hk3 Hik3 Hp Es3k DT.
        destruct (sfx_cons_inv fmt k3 t s4 ltac:(lia) Es3k) as (_ & Et & Es4).
        destruct DT as [(N122 & Hdt & Hps & Hrest & CT) | (E122 & Hps & t2 & s5 & Es45 & Hdt & Hrest & CT)].
        - jump (eapply NXS with (k3 := k3) (kn := (k3 + 1)%Z) (ty := d_ty d) (ps := 0%Z);
                [exact FI' | lia | left; rewrite <- Et; repeat split; fastfirst (first [lia | exact CT | reflexivity]) | ]).
          intros a2q a3q2.
          jump (apply (HK (k3 + 1)%Z); [zl | rewrite Hrest, Es4; reflexivity | replace (k3 + 1 - 1)%Z with k3 by lia; rewrite <- Et, Hdt; reflexivity | lia | lia | lia]).
        - rewrite Es4 in Es45. destruct (sfx_cons_inv fmt (k3 + 1) t2 s5 ltac:(lia) Es45) as (Hk31 & Et2 & Es5).
          jump (eapply NXS with (k3 := k3) (kn := (k3 + 2)%Z) (ty := d_ty d) (ps := ST_ZTPRE);
                [exact FI' | lia | right; rewrite <- Et, <- Et2; repeat split; first [zl | exact E122 | exact CT | reflexivity] | ]).
          intros a2q a3q2.
          jump (apply (HK (k3 + 2)%Z); [zl | rewrite Hrest, Es5; f_equal; lia | replace (k3 + 2 - 1)%Z with (k3 + 1)%Z by lia; rewrite <- Et2, Hdt; reflexivity | lia | lia | lia]). }
      destruct PX as [(N46 & Hpq & Hxp & DT) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & t & s4 & Es3 & DT)].
      - (* [comment removed for export] *)
        jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := k2); [exact FI' | exact LOW' | lia | | ]).
        { left. rewrite <- Ec2, Hxp. repeat split; try assumption; reflexivity. }
        intros a1q a3q a4q Hp.
        jump (eapply (STATEK k2 c2 s2b); [lia | lia | exact Hp | exact Es2 | exact DT]).
      - (* [comment removed for export] *)
        rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
        destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
        rewrite Hs3 in Es3.
        assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
        destruct (sfx_cons_inv fmt (k2 + 1 + Z.of_nat n3) t s4 Hk30 Es3) as (Hk3 & Et & Es4).
        jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := (k2 + 1 + Z.of_nat n3)%Z); [exact FI' | exact LOW' | lia | | ]).
        { right. rewrite Hxp. split; [congruence|]. split; [reflexivity|]. split; [zl|]. split; [rewrite <- Ec3; exact N42q|].
          split; [rewrite <- Es2b, <- Hs3; exact G2 | zl]. }
        intros a1q a3q a4q Hp.
        jump (eapply (STATEK (k2 + 1 + Z.of_nat n3)%Z t s4); [lia | lia | exact Hp | exact Es3 | exact DT]). }
    (* [comment removed for export] *)
    assert (FL34 : forall (a3 a4 a5 : word), evtF asegs RNG Q
      (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt (i + 1))) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 (Z_to_bv 64 1) x17
               x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x9b60c) fc None m (seg_rom asegs))).
    { intros a3q a4q a5q. pose proof (fmt_rng (i + 1) ltac:(zl)) as RG.
      (* [comment removed for export] *)
      assert (NOFLAG : flag_bit (znth fmt (i + 1)) = None -> fl = 0%Z /\ k1 = (i + 1)%Z).
      { intros NF. rewrite (parse_flags_cons_none _ _ _ NF) in PF. injection PF as Efl0 Es1q. split; [congruence|].
        pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt (i + 1) ltac:(zl)) as L2.
        rewrite (sfx_cons fmt (i + 1)) in L2 by zl. rewrite Es1q, Hs1 in L2. lia. }
      zs. zs. zs. brf K2.
      - (* [comment removed for export] *)
        assert (NF : flag_bit (znth fmt (i + 1)) = None).
        { destruct (flag_bit (znth fmt (i + 1))) eqn:E; [|reflexivity]. exfalso.
          pose proof (flag_bit_range (znth fmt (i + 1)) ltac:(congruence)) as R. rewrite land_M64_id in K2 by lia. lia. }
        destruct (NOFLAG NF) as [Efl0 Ek1].
        zs. zs. zs. brf K3. { exfalso. apply N42. rewrite Ec1', Ek1. exact K3. }
        jump (apply POSTFLAGS).
      - assert (Hc : (32 <= znth fmt (i + 1) < 64)%Z) by (apply (proj1 (sp_test _ RG)); lia).
        rewrite (land_M64_id (znth fmt (i + 1) + -32)) in * by lia.
        zs. zs. zs. zs. zs. brf K3.
        + (* [comment removed for export] *)
          change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
          assert (NF : flag_bit (znth fmt (i + 1)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
          destruct (NOFLAG NF) as [Efl0 Ek1].
          zs. zs. brf K4; [ jump (apply POSTFLAGS) | exfalso; apply N42; rewrite Ec1', Ek1; exact K4 ].
        + (* [comment removed for export] *)
          change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
          destruct (flag_bit (znth fmt (i + 1))) as [b|] eqn:E.
          2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
          pose proof (flag_some _ _ Hc E) as [Hfw Hb].
          rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
          zs.
          stmt HS_FLAGS as NXF. jump (eapply NXF with (p := (i + 1)%Z) (k := 1%Z) (fl := 0%Z) (b := b) (FL := fl) (s1 := s1);
                 [exact FI' | lia | lia | zl | rewrite unsigned_lit_land; exact Hfw | lia | lia | rewrite Z.lor_0_l; exact PF | rewrite Hs1, Es1; discriminate | ]).
          intros k' c' a3' a4' a5' Hk' Hs1' Hc' HN HFL.
          assert (Ek1 : k' = k1).
          { pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt k' ltac:(zl)) as L2. rewrite <- Hs1', Hs1 in L2. lia. }
          subst k'. subst c'. pose proof (fmt_rng k1 ltac:(zl)) as RGk.
          zs. zs. brf K4; [ | exfalso; apply N42; rewrite Ec1'; exact K4 ].
          jump (apply POSTFLAGS). }
    (* [comment removed for export] *)
    rd_fmt (i + 1)%Z. zs. fix_u8 (i + 1)%Z. zs. zs. zs. zs. zs. brf K.
    - (* [comment removed for export] *) zs. zs. apply FL34.
    - assert (DG : is_digit (znth fmt (i + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
      assert (Hi2 : (i + 2 < zlength fmt)%Z).
      { destruct (Z.lt_ge_cases (i + 2) (zlength fmt)); [assumption|]. exfalso.
        rewrite (sfx_nil fmt (i + 1 + 1)) in POSN by lia. rewrite DG in POSN. discriminate. }
      replace (i + 1 + 1)%Z with (i + 2)%Z in POSN by lia.
      rewrite (sfx_cons fmt (i + 2)) in POSN by zl. rewrite DG in POSN. cbn [andb] in POSN. apply Z.eqb_neq in POSN.
      rd_fmt (i + 2)%Z. zs. fix_u8 (i + 2)%Z. zs. zs. zs. zs. br K1. apply FL34.
  Qed.
  End Sz1.
  Lemma L_DIR : ltac:(let t := eval cbv delta [L_DIR__stmt] in L_DIR__stmt in exact t).
  Proof using HF HS_FLAGS HS_PREC HS_STATE HS_WIDTH LO HA RG_stk RG_img RG_fmt. intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q i d rest pfx s2s za pl plp alo ahi j128. ltac2:(SecDiet.SzSec.closeP 'L_DIR__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.
End TwB.
End F_printf_core_dir.

(* [comment removed for export] *)
Module F_printf_core_end.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import F_printf_core_common.
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

  Hypothesis HS_EXIT : S_EXIT.

  (* [comment removed for export] *)
  Lemma L_END : S_END.
  Proof using BS0 FF GLO HAP HS_EXIT LO QHI SEP_F VAHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HAP HS_EXIT LO QHI SEP_F VAHI KH HA : unit) => tt).
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _
           FI LOW DIG PAD HS APC FRM FOK Hr.
    pose proof FI as FI'. dest_finv FI.
    zs. br K.
    stmt HS_EXIT as NX. jump (eapply NX; [exact FI' | exact LOW | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | exact Hr]).
  Qed.
End PrintfCore.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
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

  Hypothesis HS_EXIT : S_EXIT.

  (* [comment removed for export] *)
  Lemma L_END : S_END.
  Proof using BS0 FF GLO HAP HS_EXIT LO QHI SEP_F VAHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HAP HS_EXIT LO QHI SEP_F VAHI KH HA : unit) => tt).
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _
           FI LOW DIG PAD HS APC FRM FOK Hr.
    pose proof FI as FI'. dest_finv FI.
    zs. br K.
    stmt HS_EXIT as NX. jump (eapply NX; [exact FI' | exact LOW | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | exact Hr]).
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_end.

(* [comment removed for export] *)
Module F_printf_core_exit.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import F_printf_core_common.
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
    intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _ FI LOW DIG PAD HS APC FRM FOK Hr.
    dest_finv FI. unfold lo_cells, ssp_guard in LOW.
    zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 14 zstep.
    zstep. zstep.
    (* [comment removed for export] *)
    release_frame LOW ST (q + -392)%Z.
    release_frame DIG ST (q + -368)%Z.
    release_frame PAD ST (q + -112)%Z.
    release_frame FRhi ST q.
    apply evtF_done. unfold POST.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact FOK|].
    split; [exact ST|]. split; [exact HS|]. split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2]|]. split; [exact APC|]. exact Hr.
  Qed.
End PrintfCore.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
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
    intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _ FI LOW DIG PAD HS APC FRM FOK Hr.
    dest_finv FI. unfold lo_cells, ssp_guard in LOW.
    zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 14 zstep.
    zstep. zstep.
    (* [comment removed for export] *)
    release_frame LOW ST (q + -392)%Z.
    release_frame DIG ST (q + -368)%Z.
    release_frame PAD ST (q + -112)%Z.
    release_frame FRhi ST q.
    apply evtF_done. unfold POST.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact FOK|].
    split; [exact ST|]. split; [exact HS|]. split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2]|]. split; [exact APC|]. exact Hr.
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_exit.

(* [comment removed for export] *)
Module F_printf_core_exit1.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import F_printf_core_common.
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
  Lemma L_EXIT1 : S_EXIT1.
  Proof using LO HA RG_stk RG_img RG_fmt. pin_using (fun (LO KH HA : unit) => tt).
    intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           m r pfx s2s za pl plp l10n alo ahi j128 digs pad _ FI MU1 LOW DIG PAD Hr.
    dest_finv FI. unfold lo_cells, ssp_guard in LOW.
    zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 14 zstep.
    zstep. zstep.
    release_frame LOW ST (q + -392)%Z.
    release_frame DIG ST (q + -368)%Z.
    release_frame PAD ST (q + -112)%Z.
    release_frame FRhi ST q.
    apply evtF_done. unfold POST1.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU1|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ST|]. unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2].
  Qed.
End PrintfCore.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
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
  Lemma L_EXIT1 : S_EXIT1.
  Proof using LO HA RG_stk RG_img RG_fmt. pin_using (fun (LO KH HA : unit) => tt).
    intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           m r pfx s2s za pl plp l10n alo ahi j128 digs pad _ FI MU1 LOW DIG PAD Hr.
    dest_finv FI. unfold lo_cells, ssp_guard in LOW.
    zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 14 zstep.
    zstep. zstep.
    release_frame LOW ST (q + -392)%Z.
    release_frame DIG ST (q + -368)%Z.
    release_frame PAD ST (q + -112)%Z.
    release_frame FRhi ST q.
    apply evtF_done. unfold POST1.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU1|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ST|]. unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2].
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_exit1.

(* [comment removed for export] *)
Module F_printf_core_flags.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import F_printf_core_common.
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
  Lemma L_FLAGS : S_FLAGS.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    intros x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q p k fl b w3 FL s1 _
           FI Hp Hk Hpk Hw3 Hfl Hb PF NE HK.
    remember (Z.to_nat (zlength fmt - (p + k))) as kk eqn:Hkk.
    revert k fl b w3 x11 x12 x15 Hk Hpk Hw3 Hfl Hb PF HK Hkk.
    induction kk as [|kk IH]; intros.
    { (* [comment removed for export] *) rewrite sfx_nil in PF by (unfold zlength in *; lia). cbn in PF. injection PF as _ <-. exfalso. apply NE. reflexivity. }
    assert (Hlt : (p + k < zlength fmt)%Z) by (unfold zlength in *; lia).
    pose proof FI as FI'. dest_finv FI.
    zs. rd_fmt (p + k)%Z. zs. fix_u8 (p + k)%Z. zs. zs. rewrite Hw3. zs. brf K.
    - (* [comment removed for export] *)
      assert (NF : flag_bit (znth fmt (p + k)) = None).
      { destruct (flag_bit (znth fmt (p + k))) eqn:E; [|reflexivity]. exfalso.
        pose proof (flag_bit_range (znth fmt (p + k)) ltac:(congruence)) as R.
        pose proof (proj2 (sp_test (znth fmt (p + k)) RG) R). lia. }
      rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
      injection PF as EFL Es1.
      rewrite Z.lor_comm, EFL.
      jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
      { rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
      rewrite <- EFL. apply lor_bound17; lia.
    - assert (Hc : (32 <= znth fmt (p + k) < 64)%Z) by (apply (proj1 (sp_test _ RG)); exact K).
      rewrite (land_M64_id (znth fmt (p + k) + -32)) in * by lia.
      zs. zs. zs. zs. brf K2.
      + (* [comment removed for export] *)
        change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
        destruct (flag_bit (znth fmt (p + k))) as [b'|] eqn:E.
        2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
        pose proof (flag_some _ _ Hc E) as [Hfw Hb'].
        rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
        replace (A + p + k + 1)%Z with (A + p + (k + 1))%Z by lia.
        rewrite Z.lor_comm.
        eapply (IH (k + 1)%Z (Z.lor fl b) b'); try lia.
        { rewrite unsigned_lit_land. exact Hfw. }
        { apply lor_bound17; lia. }
        { replace (p + (k + 1))%Z with (p + k + 1)%Z by lia. exact PF. }
        { intros k' c' a3 a4 a5 Hk' Hs1 Hc' HN HFL. eapply HK; try eassumption; lia. }
        all: unfold zlength in *; lia.
      + (* [comment removed for export] *)
        change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
        assert (NF : flag_bit (znth fmt (p + k)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
        rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
        injection PF as EFL Es1.
        rewrite Z.lor_comm, EFL.
        jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
        { rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
        rewrite <- EFL. apply lor_bound17; lia.
  Qed.
End PrintfCore.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
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
  Lemma L_FLAGS : S_FLAGS.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    intros x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q p k fl b w3 FL s1 _
           FI Hp Hk Hpk Hw3 Hfl Hb PF NE HK.
    remember (Z.to_nat (zlength fmt - (p + k))) as kk eqn:Hkk.
    revert k fl b w3 x11 x12 x15 Hk Hpk Hw3 Hfl Hb PF HK Hkk.
    induction kk as [|kk IH]; intros.
    { (* [comment removed for export] *) rewrite sfx_nil in PF by (unfold zlength in *; lia). cbn in PF. injection PF as _ <-. exfalso. apply NE. reflexivity. }
    assert (Hlt : (p + k < zlength fmt)%Z) by (unfold zlength in *; lia).
    pose proof FI as FI'. dest_finv FI.
    zs. rd_fmt (p + k)%Z. zs. fix_u8 (p + k)%Z. zs. zs. rewrite Hw3. zs. brf K.
    - (* [comment removed for export] *)
      assert (NF : flag_bit (znth fmt (p + k)) = None).
      { destruct (flag_bit (znth fmt (p + k))) eqn:E; [|reflexivity]. exfalso.
        pose proof (flag_bit_range (znth fmt (p + k)) ltac:(congruence)) as R.
        pose proof (proj2 (sp_test (znth fmt (p + k)) RG) R). lia. }
      rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
      injection PF as EFL Es1.
      rewrite Z.lor_comm, EFL.
      jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
      { rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
      rewrite <- EFL. apply lor_bound17; lia.
    - assert (Hc : (32 <= znth fmt (p + k) < 64)%Z) by (apply (proj1 (sp_test _ RG)); exact K).
      rewrite (land_M64_id (znth fmt (p + k) + -32)) in * by lia.
      zs. zs. zs. zs. brf K2.
      + (* [comment removed for export] *)
        change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
        destruct (flag_bit (znth fmt (p + k))) as [b'|] eqn:E.
        2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
        pose proof (flag_some _ _ Hc E) as [Hfw Hb'].
        rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
        replace (A + p + k + 1)%Z with (A + p + (k + 1))%Z by lia.
        rewrite Z.lor_comm.
        eapply (IH (k + 1)%Z (Z.lor fl b) b'); try lia.
        { rewrite unsigned_lit_land. exact Hfw. }
        { apply lor_bound17; lia. }
        { replace (p + (k + 1))%Z with (p + k + 1)%Z by lia. exact PF. }
        { intros k' c' a3 a4 a5 Hk' Hs1 Hc' HN HFL. eapply HK; try eassumption; lia. }
        all: unfold zlength in *; lia.
      + (* [comment removed for export] *)
        change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
        assert (NF : flag_bit (znth fmt (p + k)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
        rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
        injection PF as EFL Es1.
        rewrite Z.lor_comm, EFL.
        jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
        { rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
        rewrite <- EFL. apply lor_bound17; lia.
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_flags.

(* [comment removed for export] *)
Module F_printf_core_fmtu.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import F_printf_core_common.
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

  Hypothesis HS_FMTU2 : S_FMTU2.
  Hypothesis HS_DLOOP : S_DLOOP.

  (* [comment removed for export] *)
  Lemma L_FMTU : S_FMTU.
  Proof using BS0 GLO HA HAP HS_DLOOP HS_FMTU2 HVA LO SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 GLO HA HAP HS_DLOOP HS_FMTU2 HVA LO SEP_B SEP_F SFR KH : unit) => tt).
    intros fuel HH x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x prefix PFXA pfx s2s za plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    pose proof (dec_digits_length x) as LDX.
    stmt (HS_FMTU2 fuel HH) as NX.
    ienter.
    zs. zs. zs. brf K.
    - (* [comment removed for export] *)
      zs.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (d := x) (jj := 24%Z) (W := []) (prefix := prefix) (PFXA := PFXA) (pre := digs));
        [ mk_finv | exact LOW | rewrite app_nil_r; exact DIG | zl | lia
        | destruct (Z.eq_dec x 0) as [-> | NZ]; [left; split; [reflexivity|]; split; [reflexivity|]; apply dec_digits_0 | right; split; [lia|]; apply dec_digits_small; lia]
        | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    - (* [comment removed for export] *)
      zs.
      stmt HS_DLOOP as NL.
      callx (eapply NL with (j := 24%Z) (ds := digs); [ exact MI | exact DIG | lia | unfold zlength; lia | f_equal; lia ]).
      destruct_ands POST.
      match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ => rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (prefix := prefix) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG' | unfold zlength in *; rewrite length_firstn, LDS; lia | unfold zlength in *; lia
        | right; split; [assumption | assumption]
        | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
      match goal with H : SINK _ _ |- _ => exact H end.
  Qed.
End PrintfCore.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
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

  Hypothesis HS_FMTU2 : S_FMTU2.
  Hypothesis HS_DLOOP : S_DLOOP.

  (* [comment removed for export] *)
  Lemma L_FMTU : S_FMTU.
  Proof using BS0 GLO HA HAP HS_DLOOP HS_FMTU2 HVA LO SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 GLO HA HAP HS_DLOOP HS_FMTU2 HVA LO SEP_B SEP_F SFR KH : unit) => tt).
    intros fuel HH x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x prefix PFXA pfx s2s za plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    pose proof (dec_digits_length x) as LDX.
    stmt (HS_FMTU2 fuel HH) as NX.
    ienter.
    zs. zs. zs. brf K.
    - (* [comment removed for export] *)
      zs.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (d := x) (jj := 24%Z) (W := []) (prefix := prefix) (PFXA := PFXA) (pre := digs));
        [ mk_finv | exact LOW | rewrite app_nil_r; exact DIG | zl | lia
        | destruct (Z.eq_dec x 0) as [-> | NZ]; [left; split; [reflexivity|]; split; [reflexivity|]; apply dec_digits_0 | right; split; [lia|]; apply dec_digits_small; lia]
        | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    - (* [comment removed for export] *)
      zs.
      stmt HS_DLOOP as NL.
      callx (eapply NL with (j := 24%Z) (ds := digs); [ exact MI | exact DIG | lia | unfold zlength; lia | f_equal; lia ]).
      destruct_ands POST.
      match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ => rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (prefix := prefix) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG' | unfold zlength in *; rewrite length_firstn, LDS; lia | unfold zlength in *; lia
        | right; split; [assumption | assumption]
        | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
      match goal with H : SINK _ _ |- _ => exact H end.
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_fmtu.

(* [comment removed for export] *)
Module F_printf_core_intc.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import F_printf_core_common.
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

  Hypothesis HS_INTC2 : S_INTC2.

  (* [comment removed for export] *)
  Lemma L_INTC : S_INTC.
  Proof using HS_INTC2 LO HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (HS_INTC2 KH LO HA : unit) => tt).
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hargi.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    stmt (HS_INTC2 fuel HH) as NX.
    unfold conv_int.
    ienter.
    destruct XP as [[-> ->] | [-> Hp]]; cbn [Z.b2z].
    - (* [comment removed for export] *)
      replace (false && (-1 <? 0))%bool with false by reflexivity.
      zs. zs. rewrite Z.land_0_l. zs. if_lit. zs. if_lit.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := (-1)%Z) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
    - (* [comment removed for export] *)
      replace (true && (p <? 0))%bool with false by (cbn; symmetry; apply Z.ltb_ge; lia).
      zs. zs.
      replace (Z.lxor p 9223372036854775808 <? 9223372036854775808)%Z with false
        by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia).
      cbn [Z.b2z Z.land]. zs. if_lit. zs. if_lit. zs. zs.
      pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB.
      rewrite (nzmask_eq fl) in FLB |- * by lia.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := p) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
  Qed.
End PrintfCore.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
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

  Hypothesis HS_INTC2 : S_INTC2.

  (* [comment removed for export] *)
  Lemma L_INTC : S_INTC.
  Proof using HS_INTC2 LO HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (HS_INTC2 KH LO HA : unit) => tt).
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hargi.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    stmt (HS_INTC2 fuel HH) as NX.
    unfold conv_int.
    ienter.
    destruct XP as [[-> ->] | [-> Hp]]; cbn [Z.b2z].
    - (* [comment removed for export] *)
      replace (false && (-1 <? 0))%bool with false by reflexivity.
      zs. zs. rewrite Z.land_0_l. zs. if_lit. zs. if_lit.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := (-1)%Z) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
    - (* [comment removed for export] *)
      replace (true && (p <? 0))%bool with false by (cbn; symmetry; apply Z.ltb_ge; lia).
      zs. zs.
      replace (Z.lxor p 9223372036854775808 <? 9223372036854775808)%Z with false
        by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia).
      cbn [Z.b2z Z.land]. zs. if_lit. zs. if_lit. zs. zs.
      pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB.
      rewrite (nzmask_eq fl) in FLB |- * by lia.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := p) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_intc.

(* [comment removed for export] *)
Module F_printf_core_pro.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import F_printf_core_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
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
  Definition L_PRO__stmt : Prop := S_PRO.
  Section Sz1.
  Variables x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f Q : ltac2:(SecDiet.SzSec.tyM 'L_PRO__stmt "vvvvvvvvvvvv" @x5).
  Lemma L_PRO__body : ltac2:(SecDiet.SzSec.bodyP 'L_PRO__stmt "vvvvvvvvvvvv").
  Proof using GLO HA HAP HVA LO QHI RG_stk RG_img RG_fmt. pin_using (fun (GLO HA HAP HVA LO QHI KH : unit) => tt).
    intros _ ST0 MI0 BY0 VAA0 SSP0 Hf CONT.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO. unfold zlength in *.
    destruct SSP0 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. fix_rsegs.
    pose proof (zb_length fmt) as LZB. pose proof (u64s_length slots) as LU. unfold va_area in VAA0.
    pose proof (munch_refl [(q + -544, q)]%Z m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    pose proof ST0 as ST.
    carve_frame 544%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs ?mm ?A [CB 544 ?j] |- _ =>
        apply (rw_cells_split_CB asegs mm A [] 544 j [] [40; 8; 8; 8; 8; 8; 8; 8; 8; 8; 320; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [LOWa FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    replace (q + -544 + Z.of_nat 432)%Z with (q + -112)%Z in FRhi by lia.
    do 43 zs.
    (* [comment removed for export] *)
    lazymatch type of LOWa with rw_cells _ _ _ (CB 40 ?ja :: _) => set (jA := ja) in LOWa; clearbody jA end.
    lazymatch type of LOWa with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 320 ?jb :: _) => set (jB := jb) in LOWa; clearbody jB end.
    apply (rw_cells_split_CB asegs _ _ [_;_;_;_;_;_;_;_;_;_] 320 _ [] [16; 24; 24; 256]%nat) in LOWa; [ | cbn; lia ].
    cbn [mk_CB_cells app] in LOWa.
    apply (rw_cells_split_CB asegs _ _ [] 40 _ _ [8; 8; 8; 8; 8]%nat) in LOWa; [ | cbn; lia ].
    cbn [mk_CB_cells app] in LOWa.
    apply (rw_cells_split_CB asegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] 16 _ _ [8; 8]%nat) in LOWa; [ | cbn; lia ].
    cbn [mk_CB_cells app] in LOWa.
    do 7 c8ify LOWa.
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in LOWa. destruct LOWa as [LOW DP]. cbn [cells_size csize Nat.add app] in DP.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DP. destruct DP as [DIG PAD]. cbn [cells_size csize Nat.add app] in PAD.
    replace (q + -544 + Z.of_nat 152)%Z with (q + -392)%Z in DIG by lia.
    replace (q + -544 + Z.of_nat 152 + Z.of_nat 24)%Z with (q + -368)%Z in PAD by lia.
    eapply CONT; [ | exact MU | exact LOW | exact DIG | exact PAD ].
    unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area.
    split; [assumption|]. split; [eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|].
    split; [exact FRhi|]. split; [exact ST|]. split; [exact BY0|]. split; [exact VAA0|]. split; [exact SSP1|exact SSP2].
  Qed.
  End Sz1.
  Lemma L_PRO : ltac:(let t := eval cbv delta [L_PRO__stmt] in L_PRO__stmt in exact t).
  Proof using GLO HA HAP HVA LO QHI RG_stk RG_img RG_fmt. intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f Q. ltac2:(SecDiet.SzSec.closeP 'L_PRO__body "vvvvvvvvvvvv"). Qed.
End PrintfCore.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
(* [comment removed for export] *)
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
  Definition L_PRO__stmt : Prop := S_PRO.
  Section Sz1.
  Variables x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f Q : ltac2:(SecDiet.SzSec.tyM 'L_PRO__stmt "vvvvvvvvvvvv" @x5).
  Lemma L_PRO__body : ltac2:(SecDiet.SzSec.bodyP 'L_PRO__stmt "vvvvvvvvvvvv").
  Proof using GLO HA HAP HVA LO QHI RG_stk RG_img RG_fmt. pin_using (fun (GLO HA HAP HVA LO QHI KH : unit) => tt).
    intros _ ST0 MI0 BY0 VAA0 SSP0 Hf CONT.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO. unfold zlength in *.
    destruct SSP0 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. fix_rsegs.
    pose proof (zb_length fmt) as LZB. pose proof (u64s_length slots) as LU. unfold va_area in VAA0.
    pose proof (munch_refl [(q + -544, q)]%Z m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    pose proof ST0 as ST.
    carve_frame 544%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs ?mm ?A [CB 544 ?j] |- _ =>
        apply (rw_cells_split_CB asegs mm A [] 544 j [] [40; 8; 8; 8; 8; 8; 8; 8; 8; 8; 320; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [LOWa FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    replace (q + -544 + Z.of_nat 432)%Z with (q + -112)%Z in FRhi by lia.
    do 43 zs.
    (* [comment removed for export] *)
    lazymatch type of LOWa with rw_cells _ _ _ (CB 40 ?ja :: _) => set (jA := ja) in LOWa; clearbody jA end.
    lazymatch type of LOWa with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 320 ?jb :: _) => set (jB := jb) in LOWa; clearbody jB end.
    apply (rw_cells_split_CB asegs _ _ [_;_;_;_;_;_;_;_;_;_] 320 _ [] [16; 24; 24; 256]%nat) in LOWa; [ | cbn; lia ].
    cbn [mk_CB_cells app] in LOWa.
    apply (rw_cells_split_CB asegs _ _ [] 40 _ _ [8; 8; 8; 8; 8]%nat) in LOWa; [ | cbn; lia ].
    cbn [mk_CB_cells app] in LOWa.
    apply (rw_cells_split_CB asegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] 16 _ _ [8; 8]%nat) in LOWa; [ | cbn; lia ].
    cbn [mk_CB_cells app] in LOWa.
    do 7 c8ify LOWa.
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in LOWa. destruct LOWa as [LOW DP]. cbn [cells_size csize Nat.add app] in DP.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DP. destruct DP as [DIG PAD]. cbn [cells_size csize Nat.add app] in PAD.
    replace (q + -544 + Z.of_nat 152)%Z with (q + -392)%Z in DIG by lia.
    replace (q + -544 + Z.of_nat 152 + Z.of_nat 24)%Z with (q + -368)%Z in PAD by lia.
    eapply CONT; [ | exact MU | exact LOW | exact DIG | exact PAD ].
    unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area.
    split; [assumption|]. split; [eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|].
    split; [exact FRhi|]. split; [exact ST|]. split; [exact BY0|]. split; [exact VAA0|]. split; [exact SSP1|exact SSP2].
  Qed.
  End Sz1.
  Lemma L_PRO : ltac:(let t := eval cbv delta [L_PRO__stmt] in L_PRO__stmt in exact t).
  Proof using GLO HA HAP HVA LO QHI RG_stk RG_img RG_fmt. intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f Q. ltac2:(SecDiet.SzSec.closeP 'L_PRO__body "vvvvvvvvvvvv"). Qed.
End PrintfCore.
End TwB.
End F_printf_core_pro.

(* [comment removed for export] *)
Module F_printf_core_state.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import F_printf_core_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
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
  Definition L_STATE__stmt : Prop := S_STATE.
  Section Sz1.
  Variables x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k3 kn ty ps : ltac2:(SecDiet.SzSec.tyM 'L_STATE__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma L_STATE__body : ltac2:(SecDiet.SzSec.bodyP 'L_STATE__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    intros _ FI Hk3 CASES HK.
    pose proof FI as FI'. dest_finv FI.
    destruct CASES as [(Hk3b & CT & -> & ->) | (Hk3b & E122 & CT & -> & ->)].
    - (* [comment removed for export] *)
      pose proof (conv_type_range _ _ CT) as TR. pose proof (conv_type_ty _ _ CT) as TY.
      zs. zs. rd_fmt k3. zs. fix_u8 k3. zs. zs. brf K.
      { exfalso. rewrite land_M64_neg in K by lia. lia. }
      clear K. zs. zs. zs. zs. zs. zs.
      pose proof (states0_read m _ _ MI CT) as RD2. zs. cbv beta. rewrite (u8_lit ty) by lia.
      zs. zs. zs. brf K2. { exfalso. try rewrite land_M64_id in K2 by lia. lia. }
      clear K2. zs. zs. brf K3. { exfalso. try rewrite land_M64_id in K3 by lia. lia. }
      clear K3. zs. brf K4. { exfalso. try rewrite land_M64_id in K4 by lia. lia. }
      clear K4. zs. br K5.
      jump (apply HK).
    - (* [comment removed for export] *)
      pose proof (conv_type_z_ty _ _ CT) as TY.
      assert (E117 : znth fmt (k3 + 1) = 117%Z).
      { unfold conv_type_z in CT. destruct (Z.eqb_spec (znth fmt (k3 + 1)) 117); [assumption | discriminate]. }
      subst ty.
      zs. zs. rd_fmt k3. zs. fix_u8 k3. rewrite E122. zs. zs. brf K.
      { exfalso. try rewrite land_M64_neg in K by lia. try rewrite land_M64_id in K by lia. lia. }
      clear K. zs. zs. zs. zs. zs. zs.
      (* [comment removed for export] *)
      zs. zs. zs. zs. try if_lit.
      (* [comment removed for export] *)
      rd_fmt (k3 + 1)%Z. zs. fix_u8 (k3 + 1)%Z. rewrite E117. zs. zs. brf K.
      { exfalso. try rewrite land_M64_neg in K by lia. try rewrite land_M64_id in K by lia. lia. }
      clear K. zs. zs. zs. zs. zs. zs.
      (* [comment removed for export] *)
      zs. zs. zs. zs. try if_lit.
      (* [comment removed for export] *)
      repeat (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 636248) _ _ _ _) => fail | _ => first [if_lit | zs] end).
      jump (apply HK).
  Qed.
  End Sz1.
  Lemma L_STATE : ltac:(let t := eval cbv delta [L_STATE__stmt] in L_STATE__stmt in exact t).
  Proof using HF LO HA RG_stk RG_img RG_fmt. intros x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k3 kn ty ps. ltac2:(SecDiet.SzSec.closeP 'L_STATE__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
(* [comment removed for export] *)
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
  Definition L_STATE__stmt : Prop := S_STATE.
  Section Sz1.
  Variables x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k3 kn ty ps : ltac2:(SecDiet.SzSec.tyM 'L_STATE__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma L_STATE__body : ltac2:(SecDiet.SzSec.bodyP 'L_STATE__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    intros _ FI Hk3 CASES HK.
    pose proof FI as FI'. dest_finv FI.
    destruct CASES as [(Hk3b & CT & -> & ->) | (Hk3b & E122 & CT & -> & ->)].
    - (* [comment removed for export] *)
      pose proof (conv_type_range _ _ CT) as TR. pose proof (conv_type_ty _ _ CT) as TY.
      zs. zs. rd_fmt k3. zs. fix_u8 k3. zs. zs. brf K.
      { exfalso. rewrite land_M64_neg in K by lia. lia. }
      clear K. zs. zs. zs. zs. zs. zs.
      pose proof (states0_read m _ _ MI CT) as RD2. zs. cbv beta. rewrite (u8_lit ty) by lia.
      zs. zs. zs. brf K2. { exfalso. try rewrite land_M64_id in K2 by lia. lia. }
      clear K2. zs. zs. brf K3. { exfalso. try rewrite land_M64_id in K3 by lia. lia. }
      clear K3. zs. brf K4. { exfalso. try rewrite land_M64_id in K4 by lia. lia. }
      clear K4. zs. br K5.
      jump (apply HK).
    - (* [comment removed for export] *)
      pose proof (conv_type_z_ty _ _ CT) as TY.
      assert (E117 : znth fmt (k3 + 1) = 117%Z).
      { unfold conv_type_z in CT. destruct (Z.eqb_spec (znth fmt (k3 + 1)) 117); [assumption | discriminate]. }
      subst ty.
      zs. zs. rd_fmt k3. zs. fix_u8 k3. rewrite E122. zs. zs. brf K.
      { exfalso. try rewrite land_M64_neg in K by lia. try rewrite land_M64_id in K by lia. lia. }
      clear K. zs. zs. zs. zs. zs. zs.
      (* [comment removed for export] *)
      zs. zs. zs. zs. try if_lit.
      (* [comment removed for export] *)
      rd_fmt (k3 + 1)%Z. zs. fix_u8 (k3 + 1)%Z. rewrite E117. zs. zs. brf K.
      { exfalso. try rewrite land_M64_neg in K by lia. try rewrite land_M64_id in K by lia. lia. }
      clear K. zs. zs. zs. zs. zs. zs.
      (* [comment removed for export] *)
      zs. zs. zs. zs. try if_lit.
      (* [comment removed for export] *)
      repeat (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 637244) _ _ _ _) => fail | _ => first [if_lit | zs] end).
      jump (apply HK).
  Qed.
  End Sz1.
  Lemma L_STATE : ltac:(let t := eval cbv delta [L_STATE__stmt] in L_STATE__stmt in exact t).
  Proof using HF LO HA RG_stk RG_img RG_fmt. intros x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k3 kn ty ps. ltac2:(SecDiet.SzSec.closeP 'L_STATE__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.
End TwB.
End F_printf_core_state.

(* [comment removed for export] *)
Module F_printf_core_t4.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import F_printf_core_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
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

  Hypothesis HS_T5 : S_T5.

  (* [comment removed for export] *)
  Definition L_T4__stmt : Prop := S_T4.
  Section Sz1.
  Variables fuel xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_T4__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_T4__body : ltac2:(SecDiet.SzSec.bodyP 'L_T4__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 FF GLO HA HAP HOUT HS_T5 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HS_T5 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    intros HH _
           TI FRM FOK Hc Hw Hwq Hcw.
    pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
    unfold mpad at 1. change (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z with true. cbn [negb orb].
    ienter.
    pose proof (c8_read4 _ _ [C8 (Z_to_bv 64 PFXA); C8 (Z_to_bv 64 (Z.land fl 73728))] (Z_to_bv 64 n) _ _ LOW eq_refl) as RD4. cbn [cells_size csize Nat.add] in RD4.
    zs. rewrite (sx32_lit n) by lia. zs. brf K2.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.leb_le _ _)) by lia.
      stmt (HS_T5 fuel HH) as NX5.
      jumpM (eapply NX5 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
        [ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
    - rewrite (proj2 (Z.leb_gt _ _)) by lia.
      destruct (Z.leb_spec0 256 (pq - n)) as [|N256]; [ileave; apply implAM_unr_l|].
      set (n4 := (pq - n)%Z) in *.
      zs. zs. zs. try rewrite (swrap32_small (pq - n)) by lia. fold n4.
      zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
      zs. zs.
      apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
      cbn [mk_CB_cells app] in PAD.
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
      cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
      zs. callx (memset_pad PADa).
      fix_rsegs. rename MI0 into MI.
      match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
      rewrite (Z.mod_small 48 256) in PADa by lia.
      zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
      destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. zs. br K5. clear FLC.
      zs. zs. zs. zs.
      pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
      out_call.
      1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
      1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
      1:{ lia. } 1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }   (* [comment removed for export] *)
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      try clear SRC; try clear HS; (match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end).
      (* [comment removed for export] *)
      match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
        assert (PAD : rw_cells asegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
        [ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
        | apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
          replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
      end.
      stmt (HS_T5 fuel HH) as NX5.
      jumpM (eapply NX5 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
        [ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.
  End Sz1.
  Lemma L_T4 : ltac:(let t := eval cbv delta [L_T4__stmt] in L_T4__stmt in exact t).
  Proof using BS0 FF GLO HA HAP HOUT HS_T5 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_T4__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
(* [comment removed for export] *)
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

  Hypothesis HS_T5 : S_T5.

  (* [comment removed for export] *)
  Definition L_T4__stmt : Prop := S_T4.
  Section Sz1.
  Variables fuel xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_T4__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_T4__body : ltac2:(SecDiet.SzSec.bodyP 'L_T4__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 FF GLO HA HAP HOUT HS_T5 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HS_T5 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    intros HH _
           TI FRM FOK Hc Hw Hwq Hcw.
    pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
    unfold mpad at 1. change (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z with true. cbn [negb orb].
    ienter.
    pose proof (c8_read4 _ _ [C8 (Z_to_bv 64 PFXA); C8 (Z_to_bv 64 (Z.land fl 73728))] (Z_to_bv 64 n) _ _ LOW eq_refl) as RD4. cbn [cells_size csize Nat.add] in RD4.
    zs. rewrite (sx32_lit n) by lia. zs. brf K2.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.leb_le _ _)) by lia.
      stmt (HS_T5 fuel HH) as NX5.
      jumpM (eapply NX5 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
        [ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
    - rewrite (proj2 (Z.leb_gt _ _)) by lia.
      destruct (Z.leb_spec0 256 (pq - n)) as [|N256]; [ileave; apply implAM_unr_l|].
      set (n4 := (pq - n)%Z) in *.
      zs. zs. zs. try rewrite (swrap32_small (pq - n)) by lia. fold n4.
      zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
      zs. zs.
      apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
      cbn [mk_CB_cells app] in PAD.
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
      cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
      zs. callx (memset_pad PADa).
      fix_rsegs. rename MI0 into MI.
      match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
      rewrite (Z.mod_small 48 256) in PADa by lia.
      zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
      destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. zs. br K5. clear FLC.
      zs. zs. zs. zs.
      pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
      out_call.
      1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
      1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
      1:{ lia. } 1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }   (* [comment removed for export] *)
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
      try clear SRC; try clear HS; (match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end).
      (* [comment removed for export] *)
      match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
        assert (PAD : rw_cells asegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
        [ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
        | apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
          replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
      end.
      stmt (HS_T5 fuel HH) as NX5.
      jumpM (eapply NX5 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
        [ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.
  End Sz1.
  Lemma L_T4 : ltac:(let t := eval cbv delta [L_T4__stmt] in L_T4__stmt in exact t).
  Proof using BS0 FF GLO HA HAP HOUT HS_T5 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_T4__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.
End TwB.
End F_printf_core_t4.

(* [comment removed for export] *)
Module F_printf_core_t6.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import F_printf_core_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
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
  Definition L_T6__stmt : Prop := S_T6.
  Section Sz1.
  Variables fuel xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_T6__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_T6__body : ltac2:(SecDiet.SzSec.bodyP 'L_T6__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    intros HH _
           TI FRM FOK Hc Hw Hwq Hcw.
    dest_tinv TI body prefix. cbv delta [tregs].
    unfold mpad, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 8192) by reflexivity.
    ienter. zs. zs. brf K1.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) K1). cbn [negb orb].
      stmt HH as NXH.
      jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
        [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
        | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
    - rewrite K1, Z.eqb_refl. cbn [negb orb].
      zs. zs. brf K2.
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.leb_le _ _)) by lia.
        stmt HH as NXH.
        jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
          [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
          | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
      + rewrite (proj2 (Z.leb_gt _ _)) by lia.
        destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implAM_unr_l|].
        set (n4 := (wq - (pl + pq))%Z) in *.
        zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
        zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
        zs. zs.
        (* [comment removed for export] *)
        apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
        cbn [mk_CB_cells app] in PAD.
        apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
        cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
        zs. callx (memset_pad PADa).
        fix_rsegs. rename MI0 into MI.
        match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
        rewrite (Z.mod_small 32 256) in PADa by lia.
        zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
        destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K5. clear FLC.
        zs. zs. zs. zs.
        pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
        out_call.
        1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
        1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
        1:{ lia. } 1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }   (* [comment removed for export] *)
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        lazymatch goal with |- forall _ _ _, _ -> _ => idtac end.
        match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
        zs.
        (* [comment removed for export] *)
        match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
          assert (PAD : rw_cells asegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
          [ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
          | apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
            replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
        end.
        stmt HH as NXH.
        jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
          [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC
          | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
        match goal with H : SINK _ _ |- _ => exact H end.
  Qed.
  End Sz1.
  Lemma L_T6 : ltac:(let t := eval cbv delta [L_T6__stmt] in L_T6__stmt in exact t).
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_T6__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
(* [comment removed for export] *)
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
  Definition L_T6__stmt : Prop := S_T6.
  Section Sz1.
  Variables fuel xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_T6__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_T6__body : ltac2:(SecDiet.SzSec.bodyP 'L_T6__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH : unit) => tt).
    intros HH _
           TI FRM FOK Hc Hw Hwq Hcw.
    dest_tinv TI body prefix. cbv delta [tregs].
    unfold mpad, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 8192) by reflexivity.
    ienter. zs. zs. brf K1.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) K1). cbn [negb orb].
      stmt HH as NXH.
      jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
        [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
        | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
    - rewrite K1, Z.eqb_refl. cbn [negb orb].
      zs. zs. brf K2.
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.leb_le _ _)) by lia.
        stmt HH as NXH.
        jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
          [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
          | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
      + rewrite (proj2 (Z.leb_gt _ _)) by lia.
        destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implAM_unr_l|].
        set (n4 := (wq - (pl + pq))%Z) in *.
        zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
        zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
        zs. zs.
        (* [comment removed for export] *)
        apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
        cbn [mk_CB_cells app] in PAD.
        apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
        cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
        zs. callx (memset_pad PADa).
        fix_rsegs. rename MI0 into MI.
        match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
        rewrite (Z.mod_small 32 256) in PADa by lia.
        zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
        destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K5. clear FLC.
        zs. zs. zs. zs.
        pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
        out_call.
        1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
        1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
        1:{ lia. } 1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }   (* [comment removed for export] *)
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
        lazymatch goal with |- forall _ _ _, _ -> _ => idtac end.
        match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
        zs.
        (* [comment removed for export] *)
        match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
          assert (PAD : rw_cells asegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
          [ cbn [app]; apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
          | apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
            replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
        end.
        stmt HH as NXH.
        jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
          [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC
          | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
        match goal with H : SINK _ _ |- _ => exact H end.
  Qed.
  End Sz1.
  Lemma L_T6 : ltac:(let t := eval cbv delta [L_T6__stmt] in L_T6__stmt in exact t).
  Proof using BS0 FF GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_T6__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.
End TwB.
End F_printf_core_t6.
