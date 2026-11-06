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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_printf_core_conv.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
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
(* [comment removed for export] *)
Local Ltac zrange_pc0 :=
  lazymatch goal with
  | |- inr64 ?e =>
      lazymatch e with
      | bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
      | Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
                              | apply zr_land_l; [zrange | zrange_nonneg] | apply zr_land_r; [zrange_nonneg | zrange] ]
      | Z.lor _ _ => apply zr_lor; [zrange | zrange]
      | Z.lxor _ _ => apply zr_lxor; [zrange | zrange]
      | Z.shiftr _ _ => apply zr_shiftr; [zrange | flia]
      | Z.modulo _ (2^64)%Z => apply zr_mod64
      | Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
      | Z.div _ _ => apply zr_div; [zrange | flia]
      | Z.b2z _ => apply zr_b2z
      | (if _ then _ else _) => apply zr_ite; [zrange | zrange]
      | _ => first [ apply zr_lit; flia
                   | is_var e; progress (unfold e); zrange ]   (* [comment removed for export] *)
      end
  | |- (0 <= ?e < _)%Z => change (inr64 e); zrange
  end.
Local Ltac zrange ::=
  lazymatch goal with
  | |- inr64 Ff => first [ apply zr_lit; solve [ clear - FF SEP_F HAP HVA VAHI LO QHI GLO; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; Lia.lia ]
                         | zrange_pc0 ]
  | |- inr64 (Z.shiftl (d_fl _) 50) => fail        (* [comment removed for export] *)
  | |- inr64 (Z.land (d_t _) 15 + -3)%Z => fail    (* [comment removed for export] *)
  | |- _ => zrange_pc0
  end.
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

  Hypothesis HS_CV_D : S_CV_D.
  Hypothesis HS_CV_U : S_CV_U.
  Hypothesis HS_CV_X : S_CV_X.
  Hypothesis HS_CV_S : S_CV_S.

  (* [comment removed for export] *)
  Definition L_CONV__stmt : Prop := S_CONV.
  Section Sz1.
  Variables fuel x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_CONV__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_CONV__body : ltac2:(SecDiet.SzSec.bodyP 'L_CONV__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 FF GLO HA HAP HF HS_CV_D HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_F SFL SFR VAHI KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HF HS_CV_D HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_F SFL SFR VAHI KH : unit) => tt).
    intros HH _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Ht DT Hfl Hw Hp XP Hc.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
    (* [comment removed for export] *)
    cbn [args_ok] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [AOK1 AOK].
    assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
    { rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
    assert (ESK' : skipn (Z.to_nat (k + 1)) slots = slots').
    { replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
    rewrite <- ESK' in AOK.
    destruct (lo_split _ _ _ _ _ _ _ _ _ _ LOW) as (LOW14 & ARGC & J128). unfold lo_cells14, ssp_guard in LOW14. clear LOW.
    pose proof (land_bound' (d_fl d) 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq (d_fl d)) in FLB by lia.
    unfold conv. cbv zeta. unfold LEFT_ADJ, ZERO_PAD.
    (* [comment removed for export] *)
    destruct a as [sv | iv | uv | zv];
      [ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implAM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implAM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implAM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_SIZET) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implAM_unr_l] ].
    (* [comment removed for export] *)
    1-3: assert (CT : conv_type (d_t d) = Some (d_ty d)) by (destruct DT as [[_ CT] | [_ CT]]; [exact CT | exfalso; pose proof (conv_type_z_ty _ _ CT) as E; rewrite ETY in E; discriminate E]).
    1-3: assert (PS0 : d_ps d = 0%Z) by (destruct DT as [[P _] | [_ CT']]; [exact P | exfalso; pose proof (conv_type_z_ty _ _ CT') as E; rewrite ETY in E; discriminate E]).
    1-3: pose proof (conv_type_cases _ _ CT) as CASES; pose proof (conv_type_range _ _ CT) as TR.
    4: assert (CTZ : conv_type_z (d_t d) = Some (d_ty d)) by (destruct DT as [[_ CT] | [_ CT]]; [exfalso; pose proof (conv_type_ty _ _ CT) as E; rewrite ETY in E; unfold T_SIZET in E; lia | exact CT]).
    4: assert (PS6 : d_ps d = ST_ZTPRE) by (destruct DT as [[_ CT] | [P _]]; [exfalso; pose proof (conv_type_ty _ _ CT) as E; rewrite ETY in E; unfold T_SIZET in E; lia | exact P]).
    4: assert (T117 : d_t d = 117%Z) by (unfold conv_type_z in CTZ; destruct (Z.eqb_spec (d_t d) 117); [assumption | discriminate]).
    4: assert (TR : (65 <= d_t d <= 122)%Z) by lia.
    (* [comment removed for export] *)
    1: assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT in CASES, ETY; lia).
    2: assert (TDI : (d_t d = 100 \/ d_t d = 105)%Z) by (unfold T_PTR, T_INT, T_UINT in CASES, ETY; lia).
    3: assert (TUX : (d_t d = 117 \/ (d_t d = 120 \/ d_t d = 88))%Z) by (unfold T_PTR, T_INT, T_UINT in CASES, ETY; lia).
    3: destruct TUX as [T117 | TX];
         [ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t d =? 117)%Z with false by (symmetry; apply Z.eqb_neq; lia) ].
    5: rewrite (proj2 (Z.eqb_eq _ _) T117).
    1-4: rewrite PS0. 5: rewrite PS6.
    (* [comment removed for export] *)
    all: ienter; zs; (brf K; try (exfalso; (keep_hyps Fp FS Ff q lo fmt AP VA slots d LO GLO SEP_F HAP FF K; lia))); zs; zs; zs; zs.
    all: callx (eapply pop_arg_callq; [(keep_hyps q fmt slots; lia) | exact APC | exact VAA | exact NTH | (keep_hyps fmt slots k Hk; lia) | exact ARGC | exact ST | exact MI | rewrite ETY; unfold T_PTR, T_INT, T_UINT, T_SIZET; (keep_hyps fmt slots; lia)]).
    all: idtac.
    all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC'; rewrite ETY in ARGC'; cbn [pop_arg_lo pop_arg_hi OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.T_PTR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.T_INT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.T_UINT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.T_SIZET T_PTR T_INT T_UINT T_SIZET Z.eqb Pos.eqb] in ARGC' end.
    all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
    all: zs.
    all: match goal with H : SINK ?mm _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB) end; zs; zs; zs; (brf K1; try (exfalso; (keep_hyps FB K1; lia))); clear FLC.
    all: rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
    (* [comment removed for export] *)
    1-4: zsto 0x9b594%Z; change (Z.b2z (0 <? 0)) with 0%Z; rewrite Z.land_0_l; zs; (brf K2a; try (exfalso; (keep_hyps fmt slots K2a; lia))).
    5: rewrite T117; unfold ST_ZTPRE; zsto 0x9b594%Z; zs; first [if_lit | br K2a].
    all: zsto 0x9b5a8%Z; rewrite (nzmask_eq (d_fl d)) by (keep_hyps fmt slots d Hfl; lia); zs; brf K2;
      [ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
      | assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; (keep_hyps fmt slots d K2 E; lia));
        rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
    all: try rewrite <- T117.
    all: zsto 0x9b5b8%Z; zs; (brf K3; try (exfalso; (keep_hyps fmt slots d T115 K3 TDI T117 TX; lia))); zsto 0x9b5cc%Z.
    all: replace (Z.shiftl (d_t d + -65) 2 + 147048)%Z with (147048 + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; (keep_hyps fmt slots d; lia)).
    all: first [ the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_d _ _ M TDI) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_x _ _ M TX) as RD1) ].
    all: match type of RD1 with context [jt1_entry ?t] => let v := eval vm_compute in (jt1_entry t) in change (jt1_entry t) with v in RD1 end.
    all: zs; zs; zs.
    (* [comment removed for export] *)
    all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
    all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mm _) =>
      lazymatch pc with
      | 636528%Z => (* [comment removed for export] *)
          rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          match goal with MUc : munch _ m0 mm |- _ =>
            destruct (arg_ok_s_W _ _ _ _ AOK1 MUc) as (slack & STR & SRNG & SPAD & P0 & SD1 & SD2 & SD3 & SD4 & S47 & RGS & SOS) end;   (* [comment removed for export] *)
          stmt (HS_CV_S fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
                                 (xp := d_xp d) (P := bv_unsigned slot) (s := sv) (slack := slack));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (keep_hyps fmt slots k d slot sv Hk; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; (keep_hyps fmt slots d slot sv Hw; lia) | unfold INT_MAX; (keep_hyps fmt slots c d slot sv Hc; lia) | exact XP | exact STR | exact SRNG | exact SPAD | exact P0 | exact S47 | exact SD1 | exact SD2 | exact SD3 | exact RGS | exact SOS
          | subst fl'; rewrite ?land_land_same; reflexivity ]
      | 636456%Z => (* [comment removed for export] *)
          destruct AOK1 as [Hiv Emod];
          rewrite (sx32_int slot iv Hiv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_D fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (keep_hyps fmt slots k d slot iv Hk; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; (keep_hyps fmt slots d slot iv Hw; lia) | unfold INT_MAX; (keep_hyps fmt slots c d slot iv Hc; lia) | exact XP | exact Hiv ]
      | 636768%Z => (* [comment removed for export] *)
          destruct AOK1 as [Huv Emod];
          first [ rewrite (zx32_uint slot uv Emod) in ARGC'
                | rewrite <- (Z_to_bv_bv_unsigned slot), Emod in ARGC' ];
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_U fuel HH) as NX;
          fastfirst (first
          [ noevar_assumption | jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
            [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (keep_hyps fmt slots k d slot Hk; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
            | zl | exact Hfl' | unfold INT_MAX; (keep_hyps fmt slots d slot Hw; lia) | unfold INT_MAX; (keep_hyps fmt slots c d slot Hc; lia) | exact XP | (keep_hyps fmt slots d slot uv Huv; lia) ]
          | jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := zv));
            [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (keep_hyps fmt slots k d Hk; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
            | zl | exact Hfl' | unfold INT_MAX; (keep_hyps fmt slots d Hw; lia) | unfold INT_MAX; (keep_hyps fmt slots c d Hc; lia) | exact XP | (keep_hyps fmt slots d zv Huv; lia) ] ])
      | 636888%Z => (* [comment removed for export] *)
          destruct AOK1 as [Huv Emod];
          rewrite (zx32_uint slot uv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_X fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (keep_hyps fmt slots k d slot Hk; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; (keep_hyps fmt slots d slot Hw; lia) | unfold INT_MAX; (keep_hyps fmt slots c d slot Hc; lia) | exact XP | exact Huv | exact TX ]
      | ?other => idtac "UNHANDLED PC" other
      end end.
  Qed.
  End Sz1.
  Lemma L_CONV : ltac:(let t := eval cbv delta [L_CONV__stmt] in L_CONV__stmt in exact t).
  Proof using BS0 FF GLO HA HAP HF HS_CV_D HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_F SFL SFR VAHI KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_CONV__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
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
(* [comment removed for export] *)
Local Ltac zrange_pc0 :=
  lazymatch goal with
  | |- inr64 ?e =>
      lazymatch e with
      | bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
      | Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
                              | apply zr_land_l; [zrange | zrange_nonneg] | apply zr_land_r; [zrange_nonneg | zrange] ]
      | Z.lor _ _ => apply zr_lor; [zrange | zrange]
      | Z.lxor _ _ => apply zr_lxor; [zrange | zrange]
      | Z.shiftr _ _ => apply zr_shiftr; [zrange | flia]
      | Z.modulo _ (2^64)%Z => apply zr_mod64
      | Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
      | Z.div _ _ => apply zr_div; [zrange | flia]
      | Z.b2z _ => apply zr_b2z
      | (if _ then _ else _) => apply zr_ite; [zrange | zrange]
      | _ => first [ apply zr_lit; flia
                   | is_var e; progress (unfold e); zrange ]   (* [comment removed for export] *)
      end
  | |- (0 <= ?e < _)%Z => change (inr64 e); zrange
  end.
Local Ltac zrange ::=
  lazymatch goal with
  | |- inr64 Ff => first [ apply zr_lit; solve [ clear - FF SEP_F HAP HVA VAHI LO QHI GLO; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; Lia.lia ]
                         | zrange_pc0 ]
  | |- inr64 (Z.shiftl (d_fl _) 50) => fail        (* [comment removed for export] *)
  | |- inr64 (Z.land (d_t _) 15 + -3)%Z => fail    (* [comment removed for export] *)
  | |- _ => zrange_pc0
  end.
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

  Hypothesis HS_CV_D : S_CV_D.
  Hypothesis HS_CV_U : S_CV_U.
  Hypothesis HS_CV_X : S_CV_X.
  Hypothesis HS_CV_S : S_CV_S.

  (* [comment removed for export] *)
  Definition L_CONV__stmt : Prop := S_CONV.
  Section Sz1.
  Variables fuel x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_CONV__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_CONV__body : ltac2:(SecDiet.SzSec.bodyP 'L_CONV__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 FF GLO HA HAP HF HS_CV_D HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_F SFL SFR VAHI KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HF HS_CV_D HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_F SFL SFR VAHI KH : unit) => tt).
    intros HH _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Ht DT Hfl Hw Hp XP Hc.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
    (* [comment removed for export] *)
    cbn [args_ok] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [AOK1 AOK].
    assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
    { rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
    assert (ESK' : skipn (Z.to_nat (k + 1)) slots = slots').
    { replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
    rewrite <- ESK' in AOK.
    destruct (lo_split _ _ _ _ _ _ _ _ _ _ LOW) as (LOW14 & ARGC & J128). unfold lo_cells14, ssp_guard in LOW14. clear LOW.
    pose proof (land_bound' (d_fl d) 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq (d_fl d)) in FLB by lia.
    unfold conv. cbv zeta. unfold LEFT_ADJ, ZERO_PAD.
    (* [comment removed for export] *)
    destruct a as [sv | iv | uv | zv];
      [ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implAM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implAM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implAM_unr_l]
      | destruct (Z.eqb_spec (d_ty d) T_SIZET) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implAM_unr_l] ].
    (* [comment removed for export] *)
    1-3: assert (CT : conv_type (d_t d) = Some (d_ty d)) by (destruct DT as [[_ CT] | [_ CT]]; [exact CT | exfalso; pose proof (conv_type_z_ty _ _ CT) as E; rewrite ETY in E; discriminate E]).
    1-3: assert (PS0 : d_ps d = 0%Z) by (destruct DT as [[P _] | [_ CT']]; [exact P | exfalso; pose proof (conv_type_z_ty _ _ CT') as E; rewrite ETY in E; discriminate E]).
    1-3: pose proof (conv_type_cases _ _ CT) as CASES; pose proof (conv_type_range _ _ CT) as TR.
    4: assert (CTZ : conv_type_z (d_t d) = Some (d_ty d)) by (destruct DT as [[_ CT] | [_ CT]]; [exfalso; pose proof (conv_type_ty _ _ CT) as E; rewrite ETY in E; unfold T_SIZET in E; lia | exact CT]).
    4: assert (PS6 : d_ps d = ST_ZTPRE) by (destruct DT as [[_ CT] | [P _]]; [exfalso; pose proof (conv_type_ty _ _ CT) as E; rewrite ETY in E; unfold T_SIZET in E; lia | exact P]).
    4: assert (T117 : d_t d = 117%Z) by (unfold conv_type_z in CTZ; destruct (Z.eqb_spec (d_t d) 117); [assumption | discriminate]).
    4: assert (TR : (65 <= d_t d <= 122)%Z) by lia.
    (* [comment removed for export] *)
    1: assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT in CASES, ETY; lia).
    2: assert (TDI : (d_t d = 100 \/ d_t d = 105)%Z) by (unfold T_PTR, T_INT, T_UINT in CASES, ETY; lia).
    3: assert (TUX : (d_t d = 117 \/ (d_t d = 120 \/ d_t d = 88))%Z) by (unfold T_PTR, T_INT, T_UINT in CASES, ETY; lia).
    3: destruct TUX as [T117 | TX];
         [ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t d =? 117)%Z with false by (symmetry; apply Z.eqb_neq; lia) ].
    5: rewrite (proj2 (Z.eqb_eq _ _) T117).
    1-4: rewrite PS0. 5: rewrite PS6.
    (* [comment removed for export] *)
    all: ienter; zs; (brf K; try (exfalso; (keep_hyps Fp FS Ff q lo fmt AP VA slots d LO GLO SEP_F HAP FF K; lia))); zs; zs; zs; zs.
    all: callx (eapply pop_arg_callq; [(keep_hyps q fmt slots; lia) | exact APC | exact VAA | exact NTH | (keep_hyps fmt slots k Hk; lia) | exact ARGC | exact ST | exact MI | rewrite ETY; unfold T_PTR, T_INT, T_UINT, T_SIZET; (keep_hyps fmt slots; lia)]).
    all: idtac.
    all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC'; rewrite ETY in ARGC'; cbn [pop_arg_lo pop_arg_hi OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB.T_PTR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB.T_INT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB.T_UINT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB.T_SIZET T_PTR T_INT T_UINT T_SIZET Z.eqb Pos.eqb] in ARGC' end.
    all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
    all: zs.
    all: match goal with H : SINK ?mm _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB) end; zs; zs; zs; (brf K1; try (exfalso; (keep_hyps FB K1; lia))); clear FLC.
    all: rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
    (* [comment removed for export] *)
    1-4: zsto 0x9b978%Z; change (Z.b2z (0 <? 0)) with 0%Z; rewrite Z.land_0_l; zs; (brf K2a; try (exfalso; (keep_hyps fmt slots K2a; lia))).
    5: rewrite T117; unfold ST_ZTPRE; zsto 0x9b978%Z; zs; first [if_lit | br K2a].
    all: zsto 0x9b98c%Z; rewrite (nzmask_eq (d_fl d)) by (keep_hyps fmt slots d Hfl; lia); zs; brf K2;
      [ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
      | assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; (keep_hyps fmt slots d K2 E; lia));
        rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
    all: try rewrite <- T117.
    all: zsto 0x9b99c%Z; zs; (brf K3; try (exfalso; (keep_hyps fmt slots d T115 K3 TDI T117 TX; lia))); zsto 0x9b9b0%Z.
    all: replace (Z.shiftl (d_t d + -65) 2 + 147048)%Z with (147048 + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; (keep_hyps fmt slots d; lia)).
    all: first [ the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_d _ _ M TDI) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1)
               | the_mi ltac:(fun M => pose proof (jt1_read_x _ _ M TX) as RD1) ].
    all: match type of RD1 with context [jt1_entry ?t] => let v := eval vm_compute in (jt1_entry t) in change (jt1_entry t) with v in RD1 end.
    all: zs; zs; zs.
    (* [comment removed for export] *)
    all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
    all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mm _) =>
      lazymatch pc with
      | 637524%Z => (* [comment removed for export] *)
          rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          match goal with MUc : munch _ m0 mm |- _ =>
            destruct (arg_ok_s_W _ _ _ _ AOK1 MUc) as (slack & STR & SRNG & SPAD & P0 & SD1 & SD2 & SD3 & SD4 & S47 & RGS & SOS) end;   (* [comment removed for export] *)
          stmt (HS_CV_S fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
                                 (xp := d_xp d) (P := bv_unsigned slot) (s := sv) (slack := slack));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (keep_hyps fmt slots k d slot sv Hk; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; (keep_hyps fmt slots d slot sv Hw; lia) | unfold INT_MAX; (keep_hyps fmt slots c d slot sv Hc; lia) | exact XP | exact STR | exact SRNG | exact SPAD | exact P0 | exact S47 | exact SD1 | exact SD2 | exact SD3 | exact RGS | exact SOS
          | subst fl'; rewrite ?land_land_same; reflexivity ]
      | 637452%Z => (* [comment removed for export] *)
          destruct AOK1 as [Hiv Emod];
          rewrite (sx32_int slot iv Hiv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_D fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (keep_hyps fmt slots k d slot iv Hk; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; (keep_hyps fmt slots d slot iv Hw; lia) | unfold INT_MAX; (keep_hyps fmt slots c d slot iv Hc; lia) | exact XP | exact Hiv ]
      | 637764%Z => (* [comment removed for export] *)
          destruct AOK1 as [Huv Emod];
          first [ rewrite (zx32_uint slot uv Emod) in ARGC'
                | rewrite <- (Z_to_bv_bv_unsigned slot), Emod in ARGC' ];
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_U fuel HH) as NX;
          fastfirst (first
          [ noevar_assumption | jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
            [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (keep_hyps fmt slots k d slot Hk; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
            | zl | exact Hfl' | unfold INT_MAX; (keep_hyps fmt slots d slot Hw; lia) | unfold INT_MAX; (keep_hyps fmt slots c d slot Hc; lia) | exact XP | (keep_hyps fmt slots d slot uv Huv; lia) ]
          | jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := zv));
            [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (keep_hyps fmt slots k d Hk; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
            | zl | exact Hfl' | unfold INT_MAX; (keep_hyps fmt slots d Hw; lia) | unfold INT_MAX; (keep_hyps fmt slots c d Hc; lia) | exact XP | (keep_hyps fmt slots d zv Huv; lia) ] ])
      | 637884%Z => (* [comment removed for export] *)
          destruct AOK1 as [Huv Emod];
          rewrite (zx32_uint slot uv Emod) in ARGC';
          pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
          stmt (HS_CV_X fuel HH) as NX;
          jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
          [ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (keep_hyps fmt slots k d slot Hk; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
          | zl | exact Hfl' | unfold INT_MAX; (keep_hyps fmt slots d slot Hw; lia) | unfold INT_MAX; (keep_hyps fmt slots c d slot Hc; lia) | exact XP | exact Huv | exact TX ]
      | ?other => idtac "UNHANDLED PC" other
      end end.
  Qed.
  End Sz1.
  Lemma L_CONV : ltac:(let t := eval cbv delta [L_CONV__stmt] in L_CONV__stmt in exact t).
  Proof using BS0 FF GLO HA HAP HF HS_CV_D HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_F SFL SFR VAHI KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_CONV__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.
End TwB.
End F_printf_core_conv.

(* [comment removed for export] *)
Module F_printf_core_cvd.
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

  Hypothesis HS_FMTU : S_FMTU.

  (* [comment removed for export] *)
  Lemma fl_shl52 : forall fl, (0 <= fl < 131072)%Z ->
    (Z.land (Z.shiftl fl 52) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 2048 = 0)%Z.
  Proof using Type. pin_using tt.
    clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
    change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia.
    change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    split; intros H; Z.div_mod_to_equations; nia.
  Qed.

  Definition L_CV_D__stmt : Prop := S_CV_D.
  Section Sz2.
  Variables fuel x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp i pfx s2s za pl plp ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_CV_D__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_CV_D__body : ltac2:(SecDiet.SzSec.bodyP 'L_CV_D__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR KH : unit) => tt).
    intros HH _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hi.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    stmt (HS_FMTU fuel HH) as NX.
    pose proof (Z.mod_pos_bound i (2^64) ltac:(lia)) as RA.
    set (argi := (i mod 2^64)%Z) in *.
    unfold INTMAX_MAX, MARK_POS, PAD_POS.
    ienter.
    zs. zs. brf K1.
    - (* [comment removed for export] *)
      zs. zs. zs. zs. zs. zs. zs. zs.
      replace (Z_to_bv 64 (0 - argi)) with (Z_to_bv 64 ((- argi) mod 2 ^ 64)) in * by (apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; f_equal; lia).
      replace (9223372036854775807 <? argi)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      pose proof (Z.mod_pos_bound (- argi) (2^64) ltac:(lia)) as RB.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := ((- argi) mod 2 ^ 64)%Z) (prefix := [45%Z]) (PFXA := 68460%Z));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | intros mq MIq; exact (pfx_sub mq 0 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    - replace (9223372036854775807 <? argi)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      zs. zs. zs. zs. zs. brf K2.
      + (* [comment removed for export] *)
        assert (HM : Z.land fl 2048 <> 0%Z) by (intros E; apply (proj2 (fl_shl52 fl Hfl)) in E; lia).
        replace (Z.land fl 2048 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact HM). cbn [negb].
        zs. zs. zs.
        jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [43%Z]) (PFXA := 68461%Z));
          [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
          | intros mq MIq; exact (pfx_sub mq 1 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
      + assert (HM : Z.land fl 2048 = 0%Z) by (apply (proj1 (fl_shl52 fl Hfl)); lia).
        replace (Z.land fl 2048 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact HM). cbn [negb].
        zs. zs. zs. zs. zs.
        pose proof (land_bound' fl 1 ltac:(lia) ltac:(lia)) as B1.
        assert (C1 : (Z.land fl 1 = 0 \/ Z.land fl 1 = 1)%Z).
        { pose proof (Z.land_ones fl 1 ltac:(lia)) as E. change (Z.ones 1) with 1%Z in E. change (2^1)%Z with 2%Z in E. rewrite E.
          pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia. }
        destruct C1 as [E1 | E1]; rewrite E1 in *.
        * (* [comment removed for export] *)
          cbn [Z.eqb negb Z.mul Z.add].
          jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := []) (PFXA := 68460%Z));
            [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
        * (* [comment removed for export] *)
          cbn [Z.eqb negb Z.mul Z.add].
          jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [32%Z]) (PFXA := 68462%Z));
            [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | intros mq MIq; exact (pfx_sub mq 2 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
  Qed.
  End Sz2.
  Lemma L_CV_D : ltac:(let t := eval cbv delta [L_CV_D__stmt] in L_CV_D__stmt in exact t).
  Proof using BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp i pfx s2s za pl plp ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_CV_D__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
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

  Hypothesis HS_FMTU : S_FMTU.

  (* [comment removed for export] *)
  Lemma fl_shl52 : forall fl, (0 <= fl < 131072)%Z ->
    (Z.land (Z.shiftl fl 52) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 2048 = 0)%Z.
  Proof using Type. pin_using tt.
    clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
    change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia.
    change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    split; intros H; Z.div_mod_to_equations; nia.
  Qed.

  Definition L_CV_D__stmt : Prop := S_CV_D.
  Section Sz2.
  Variables fuel x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp i pfx s2s za pl plp ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_CV_D__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_CV_D__body : ltac2:(SecDiet.SzSec.bodyP 'L_CV_D__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR KH : unit) => tt).
    intros HH _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hi.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    stmt (HS_FMTU fuel HH) as NX.
    pose proof (Z.mod_pos_bound i (2^64) ltac:(lia)) as RA.
    set (argi := (i mod 2^64)%Z) in *.
    unfold INTMAX_MAX, MARK_POS, PAD_POS.
    ienter.
    zs. zs. brf K1.
    - (* [comment removed for export] *)
      zs. zs. zs. zs. zs. zs. zs. zs.
      replace (Z_to_bv 64 (0 - argi)) with (Z_to_bv 64 ((- argi) mod 2 ^ 64)) in * by (apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; f_equal; lia).
      replace (9223372036854775807 <? argi)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      pose proof (Z.mod_pos_bound (- argi) (2^64) ltac:(lia)) as RB.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := ((- argi) mod 2 ^ 64)%Z) (prefix := [45%Z]) (PFXA := 68460%Z));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | intros mq MIq; exact (pfx_sub mq 0 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    - replace (9223372036854775807 <? argi)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      zs. zs. zs. zs. zs. brf K2.
      + (* [comment removed for export] *)
        assert (HM : Z.land fl 2048 <> 0%Z) by (intros E; apply (proj2 (fl_shl52 fl Hfl)) in E; lia).
        replace (Z.land fl 2048 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact HM). cbn [negb].
        zs. zs. zs.
        jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [43%Z]) (PFXA := 68461%Z));
          [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
          | intros mq MIq; exact (pfx_sub mq 1 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
      + assert (HM : Z.land fl 2048 = 0%Z) by (apply (proj1 (fl_shl52 fl Hfl)); lia).
        replace (Z.land fl 2048 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact HM). cbn [negb].
        zs. zs. zs. zs. zs.
        pose proof (land_bound' fl 1 ltac:(lia) ltac:(lia)) as B1.
        assert (C1 : (Z.land fl 1 = 0 \/ Z.land fl 1 = 1)%Z).
        { pose proof (Z.land_ones fl 1 ltac:(lia)) as E. change (Z.ones 1) with 1%Z in E. change (2^1)%Z with 2%Z in E. rewrite E.
          pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia. }
        destruct C1 as [E1 | E1]; rewrite E1 in *.
        * (* [comment removed for export] *)
          cbn [Z.eqb negb Z.mul Z.add].
          jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := []) (PFXA := 68460%Z));
            [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
        * (* [comment removed for export] *)
          cbn [Z.eqb negb Z.mul Z.add].
          jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [32%Z]) (PFXA := 68462%Z));
            [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | intros mq MIq; exact (pfx_sub mq 2 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
  Qed.
  End Sz2.
  Lemma L_CV_D : ltac:(let t := eval cbv delta [L_CV_D__stmt] in L_CV_D__stmt in exact t).
  Proof using BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp i pfx s2s za pl plp ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_CV_D__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.
End TwB.
End F_printf_core_cvd.

(* [comment removed for export] *)
Module F_printf_core_cvx.
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

  Hypothesis HS_INTC : S_INTC.
  Hypothesis HS_XLOOP : S_XLOOP.

  (* [comment removed for export] *)
  Definition L_CV_X__stmt : Prop := S_CV_X.
  Section Sz1.
  Variables fuel x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u t pfx s2s za pl plp ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_CV_X__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_CV_X__body : ltac2:(SecDiet.SzSec.bodyP 'L_CV_X__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 GLO HA HAP HS_INTC HS_XLOOP HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 GLO HA HAP HS_INTC HS_XLOOP HVA LO QHI SEP_B SEP_F SFR KH : unit) => tt).
    intros HH _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu Ht.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    stmt (HS_INTC fuel HH) as NX.
    unfold ALT_FORM.
    assert (Hl : (Z.land t 32 = 0 \/ Z.land t 32 = 32)%Z) by (destruct Ht as [-> | ->]; [right | left]; reflexivity).
    pose proof (hex_digits_length (Z.land t 32) u) as LH.
    assert (HRNG : Forall (fun c0 => 0 <= c0 < 256)%Z (hex_digits (Z.land t 32) u)).
    { eapply Forall_impl; [|apply hex_digits_range; exact Hl]. cbv beta. intros. lia. }
    ienter.
    zs. zs. zs. zs. brf K0.
    - (* [comment removed for export] *)
      replace (u =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K0). cbn [negb andb].
      zs. zs. zs. zs.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := []) (BA := (q + -368)%Z) (PFXA := 68460%Z));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | rewrite K0, hex_digits_0; apply bytes_at_nil; lia | exact HRNG | rewrite K0, hex_digits_0; zl | zl
        | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    - replace (u =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K0). cbn [negb andb].
      zs. zs.
      replace (Z.land t 32) with (Z.land t 32) by reflexivity.
      stmt HS_XLOOP as NL.
      callx (eapply NL with (l := Z.land t 32) (x := u) (j := 24%Z) (ds := digs);
             [ exact MI | exact DIG | lia | exact Hl | unfold zlength; lia | f_equal; lia ]).
      destruct_ands POST. cbv zeta in *.
      match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ =>
        rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
      pose proof (rw_cells_bytes_at' _ _ _ _ DIG') as BODY. cbn [cells_bytes cbytes app] in BODY. rewrite app_nil_r in BODY.
      apply bytes_at_app in BODY. destruct BODY as [_ BODY]. rewrite length_firstn, LDS in BODY.
      replace (Z.of_nat (Nat.min (Z.to_nat (24 - zlength (hex_digits (Z.land t 32) u))) 24)) with (24 - zlength (hex_digits (Z.land t 32) u))%Z in BODY by (unfold zlength in *; lia).
      zs. zs. brf K1.
      + (* [comment removed for export] *)
        replace (Z.land fl 8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K1). cbn [negb andb].
        zs. zs. zs. zs. zs. zs. zs. zs.
        destruct Ht as [-> | ->]; cbn [Z.eqb Pos.eqb].
        * jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 120]%Z)
                                 (BA := (q + -392 + (24 - zlength (hex_digits (Z.land 120 32) u)))%Z) (PFXA := 68467%Z));
            [ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | exact BODY | exact HRNG | unfold zlength in *; lia | zl
            | intros mq MIq; exact (pfx_sub mq 7 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
          match goal with H : SINK _ _ |- _ => exact H end.
        * jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 88]%Z)
                                 (BA := (q + -392 + (24 - zlength (hex_digits (Z.land 88 32) u)))%Z) (PFXA := 68465%Z));
            [ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | exact BODY | exact HRNG | unfold zlength in *; lia | zl
            | intros mq MIq; exact (pfx_sub mq 5 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
          match goal with H : SINK _ _ |- _ => exact H end.
      + (* [comment removed for export] *)
        replace (Z.land fl 8 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K1). cbn [negb andb].
        zs. zs. zs.
        jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [])
                               (BA := (q + -392 + (24 - zlength (hex_digits (Z.land t 32) u)))%Z) (PFXA := 68460%Z));
          [ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
          | exact BODY | exact HRNG | unfold zlength in *; lia | zl
          | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
        match goal with H : SINK _ _ |- _ => exact H end.
  Qed.
  End Sz1.
  Lemma L_CV_X : ltac:(let t := eval cbv delta [L_CV_X__stmt] in L_CV_X__stmt in exact t).
  Proof using BS0 GLO HA HAP HS_INTC HS_XLOOP HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u t pfx s2s za pl plp ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_CV_X__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
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

  Hypothesis HS_INTC : S_INTC.
  Hypothesis HS_XLOOP : S_XLOOP.

  (* [comment removed for export] *)
  Definition L_CV_X__stmt : Prop := S_CV_X.
  Section Sz1.
  Variables fuel x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u t pfx s2s za pl plp ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_CV_X__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_CV_X__body : ltac2:(SecDiet.SzSec.bodyP 'L_CV_X__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 GLO HA HAP HS_INTC HS_XLOOP HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 GLO HA HAP HS_INTC HS_XLOOP HVA LO QHI SEP_B SEP_F SFR KH : unit) => tt).
    intros HH _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu Ht.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    stmt (HS_INTC fuel HH) as NX.
    unfold ALT_FORM.
    assert (Hl : (Z.land t 32 = 0 \/ Z.land t 32 = 32)%Z) by (destruct Ht as [-> | ->]; [right | left]; reflexivity).
    pose proof (hex_digits_length (Z.land t 32) u) as LH.
    assert (HRNG : Forall (fun c0 => 0 <= c0 < 256)%Z (hex_digits (Z.land t 32) u)).
    { eapply Forall_impl; [|apply hex_digits_range; exact Hl]. cbv beta. intros. lia. }
    ienter.
    zs. zs. zs. zs. brf K0.
    - (* [comment removed for export] *)
      replace (u =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K0). cbn [negb andb].
      zs. zs. zs. zs.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := []) (BA := (q + -368)%Z) (PFXA := 68460%Z));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | rewrite K0, hex_digits_0; apply bytes_at_nil; lia | exact HRNG | rewrite K0, hex_digits_0; zl | zl
        | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    - replace (u =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K0). cbn [negb andb].
      zs. zs.
      replace (Z.land t 32) with (Z.land t 32) by reflexivity.
      stmt HS_XLOOP as NL.
      callx (eapply NL with (l := Z.land t 32) (x := u) (j := 24%Z) (ds := digs);
             [ exact MI | exact DIG | lia | exact Hl | unfold zlength; lia | f_equal; lia ]).
      destruct_ands POST. cbv zeta in *.
      match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ =>
        rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
      pose proof (rw_cells_bytes_at' _ _ _ _ DIG') as BODY. cbn [cells_bytes cbytes app] in BODY. rewrite app_nil_r in BODY.
      apply bytes_at_app in BODY. destruct BODY as [_ BODY]. rewrite length_firstn, LDS in BODY.
      replace (Z.of_nat (Nat.min (Z.to_nat (24 - zlength (hex_digits (Z.land t 32) u))) 24)) with (24 - zlength (hex_digits (Z.land t 32) u))%Z in BODY by (unfold zlength in *; lia).
      zs. zs. brf K1.
      + (* [comment removed for export] *)
        replace (Z.land fl 8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K1). cbn [negb andb].
        zs. zs. zs. zs. zs. zs. zs. zs.
        destruct Ht as [-> | ->]; cbn [Z.eqb Pos.eqb].
        * jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 120]%Z)
                                 (BA := (q + -392 + (24 - zlength (hex_digits (Z.land 120 32) u)))%Z) (PFXA := 68467%Z));
            [ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | exact BODY | exact HRNG | unfold zlength in *; lia | zl
            | intros mq MIq; exact (pfx_sub mq 7 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
          match goal with H : SINK _ _ |- _ => exact H end.
        * jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 88]%Z)
                                 (BA := (q + -392 + (24 - zlength (hex_digits (Z.land 88 32) u)))%Z) (PFXA := 68465%Z));
            [ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | exact BODY | exact HRNG | unfold zlength in *; lia | zl
            | intros mq MIq; exact (pfx_sub mq 5 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
          match goal with H : SINK _ _ |- _ => exact H end.
      + (* [comment removed for export] *)
        replace (Z.land fl 8 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K1). cbn [negb andb].
        zs. zs. zs.
        jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [])
                               (BA := (q + -392 + (24 - zlength (hex_digits (Z.land t 32) u)))%Z) (PFXA := 68460%Z));
          [ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
          | exact BODY | exact HRNG | unfold zlength in *; lia | zl
          | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
        match goal with H : SINK _ _ |- _ => exact H end.
  Qed.
  End Sz1.
  Lemma L_CV_X : ltac:(let t := eval cbv delta [L_CV_X__stmt] in L_CV_X__stmt in exact t).
  Proof using BS0 GLO HA HAP HS_INTC HS_XLOOP HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u t pfx s2s za pl plp ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_CV_X__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.
End TwB.
End F_printf_core_cvx.

(* [comment removed for export] *)
Module F_printf_core_dloop.
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
  Lemma L_DLOOP : S_DLOOP.
  Proof using GLO LO QHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (GLO LO QHI KH HA : unit) => tt).
    intros x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m x.
    remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x11 x12 x13 x23 m.
    induction nx as [nx IH] using lt_wf_ind.
    intros x Enx x11 x12 x13 x23 m j ds _ MI DIG Hx Hj ->.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (dec_digits_step x ltac:(lia)) as DS.
    pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)) as Q0.
    pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as R0.
    assert (Q1 : (x / 10 < 1844674407370955162)%Z) by (apply Z.div_lt_upper_bound; lia).
    assert (LD : (2 <= zlength (dec_digits x))%Z).
    { rewrite DS. unfold zlength. rewrite length_app. cbn [length].
      destruct (Z.lt_ge_cases (x / 10) 10).
      - rewrite dec_digits_small by lia. cbn. lia.
      - rewrite (dec_digits_step (x / 10)) by lia. rewrite length_app. cbn [length]. lia. }
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    zs. zs. zs. zs. zs.
    rewrite (land_W64_small (Z.shiftr (x * 14757395258967641293) 64)) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite div10_magic by lia. zs. zs. zs.
    replace (bv_swrap 32 (x - x / 10 * 10)) with (x mod 10)%Z by (rewrite swrap32_small by lia; lia).
    rewrite (land_W64_small (x mod 10)) by lia. rewrite lor48_digit by lia.
    set (c := (48 + x mod 10)%Z) in *.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
    pose proof (u8arr_store_ok asegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
    zs. zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
    pose proof (u8arr_write asegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
    zs. zs. brf K.
    - (* [comment removed for export] *)
      eapply evtF_mono.
      { eapply (IH (Z.to_nat (x / 10)) ltac:(lia) (x / 10)%Z eq_refl); [ exact MI | exact DIG1 | lia | | reflexivity ].
        rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
      cbv beta. intros ms' P. destruct P as (a2' & a3' & xq & W' & m' & -> & MU' & WM' & MI' & DIG' & Hxq & HD & HW).
      unfold dloop_post. exists a2', a3', xq, (W' ++ [c]), m'.
      assert (EL : zlength (W' ++ [c]) = (zlength W' + 1)%Z) by (unfold zlength; rewrite length_app; cbn [length]; lia).
      rewrite EL.
      split; [ mseq | ].
      split; [ eapply munch_trans; [exact MU | exact MU'] | ].
      split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
      split; [ exact MI' | ].
      split.
      { replace (firstn (Z.to_nat (j - (zlength W' + 1))) ds ++ zb (W' ++ [c]) ++ skipn (Z.to_nat j) ds)
          with (firstn (Z.to_nat (j - 1 - zlength W')) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb W' ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
        rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
        replace (Z.to_nat (j - 1 - zlength W')) with (Z.to_nat (j - (zlength W' + 1))) by lia.
        replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
        rewrite zb_app, <- !app_assoc. reflexivity. }
      split; [ exact Hxq | ]. split; [ rewrite DS, HD; reflexivity | ]. unfold zlength in *. lia.
    - (* [comment removed for export] *)
      zs. apply evtF_done.
      unfold dloop_post. eexists (Z_to_bv 64 x), (Z_to_bv 64 c), (x / 10)%Z, [c], _.
      split; [ mseq | ].
      split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
      split.
      { replace (firstn (Z.to_nat (j - zlength [c])) ds ++ zb [c] ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
        rewrite upd_firstn_skipn by (rewrite LDS; lia). cbn [zb map app zlength length Z.of_nat Pos.of_succ_nat].
        replace (Z.to_nat (j - 1)) with (Z.to_nat (j - 1)) by reflexivity.
        replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
      split; [ lia | ]. split; [ rewrite DS, dec_digits_small by lia; reflexivity | ]. zl.
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
  Lemma L_DLOOP : S_DLOOP.
  Proof using GLO LO QHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (GLO LO QHI KH HA : unit) => tt).
    intros x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m x.
    remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x11 x12 x13 x23 m.
    induction nx as [nx IH] using lt_wf_ind.
    intros x Enx x11 x12 x13 x23 m j ds _ MI DIG Hx Hj ->.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (dec_digits_step x ltac:(lia)) as DS.
    pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)) as Q0.
    pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as R0.
    assert (Q1 : (x / 10 < 1844674407370955162)%Z) by (apply Z.div_lt_upper_bound; lia).
    assert (LD : (2 <= zlength (dec_digits x))%Z).
    { rewrite DS. unfold zlength. rewrite length_app. cbn [length].
      destruct (Z.lt_ge_cases (x / 10) 10).
      - rewrite dec_digits_small by lia. cbn. lia.
      - rewrite (dec_digits_step (x / 10)) by lia. rewrite length_app. cbn [length]. lia. }
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    zs. zs. zs. zs. zs.
    rewrite (land_W64_small (Z.shiftr (x * 14757395258967641293) 64)) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite div10_magic by lia. zs. zs. zs.
    replace (bv_swrap 32 (x - x / 10 * 10)) with (x mod 10)%Z by (rewrite swrap32_small by lia; lia).
    rewrite (land_W64_small (x mod 10)) by lia. rewrite lor48_digit by lia.
    set (c := (48 + x mod 10)%Z) in *.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
    pose proof (u8arr_store_ok asegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
    zs. zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
    pose proof (u8arr_write asegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
    zs. zs. brf K.
    - (* [comment removed for export] *)
      eapply evtF_mono.
      { eapply (IH (Z.to_nat (x / 10)) ltac:(lia) (x / 10)%Z eq_refl); [ exact MI | exact DIG1 | lia | | reflexivity ].
        rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
      cbv beta. intros ms' P. destruct P as (a2' & a3' & xq & W' & m' & -> & MU' & WM' & MI' & DIG' & Hxq & HD & HW).
      unfold dloop_post. exists a2', a3', xq, (W' ++ [c]), m'.
      assert (EL : zlength (W' ++ [c]) = (zlength W' + 1)%Z) by (unfold zlength; rewrite length_app; cbn [length]; lia).
      rewrite EL.
      split; [ mseq | ].
      split; [ eapply munch_trans; [exact MU | exact MU'] | ].
      split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
      split; [ exact MI' | ].
      split.
      { replace (firstn (Z.to_nat (j - (zlength W' + 1))) ds ++ zb (W' ++ [c]) ++ skipn (Z.to_nat j) ds)
          with (firstn (Z.to_nat (j - 1 - zlength W')) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb W' ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
        rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
        replace (Z.to_nat (j - 1 - zlength W')) with (Z.to_nat (j - (zlength W' + 1))) by lia.
        replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
        rewrite zb_app, <- !app_assoc. reflexivity. }
      split; [ exact Hxq | ]. split; [ rewrite DS, HD; reflexivity | ]. unfold zlength in *. lia.
    - (* [comment removed for export] *)
      zs. apply evtF_done.
      unfold dloop_post. eexists (Z_to_bv 64 x), (Z_to_bv 64 c), (x / 10)%Z, [c], _.
      split; [ mseq | ].
      split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
      split.
      { replace (firstn (Z.to_nat (j - zlength [c])) ds ++ zb [c] ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
        rewrite upd_firstn_skipn by (rewrite LDS; lia). cbn [zb map app zlength length Z.of_nat Pos.of_succ_nat].
        replace (Z.to_nat (j - 1)) with (Z.to_nat (j - 1)) by reflexivity.
        replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
      split; [ lia | ]. split; [ rewrite DS, dec_digits_small by lia; reflexivity | ]. zl.
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_dloop.

(* [comment removed for export] *)
Module F_printf_core_fmtu2.
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

  Hypothesis HS_INTC : S_INTC.

  (* [comment removed for export] *)
  Definition L_FMTU2__stmt : Prop := S_FMTU2.
  Section Sz1.
  Variables fuel x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x d jj W prefix PFXA pfx s2s za plp ahi j128 pre pad : ltac2:(SecDiet.SzSec.tyM 'L_FMTU2__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_FMTU2__body : ltac2:(SecDiet.SzSec.bodyP 'L_FMTU2__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 GLO HA HAP HS_INTC HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 GLO HA HAP HS_INTC HVA LO QHI SEP_B SEP_F SFR KH : unit) => tt).
    intros HH _
           FI LOW DIG Hjj Hjj1 HD PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS. rewrite length_app, zb_length in LDS.
    pose proof (dec_digits_length x) as LDX.
    stmt (HS_INTC fuel HH) as NX.
    ienter.
    zs. zs. brf K1.
    - (* [comment removed for export] *)
      destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [|exfalso; lia].
      rewrite app_nil_r in DIG.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -368)%Z) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | rewrite DX; apply bytes_at_nil; lia | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    - (* [comment removed for export] *)
      destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [exfalso; lia|].
      assert (LW : (Z.of_nat (length W) + 1 <= 20)%Z) by (rewrite DX in LDX; cbn [length] in LDX; lia).
      zs. rewrite lor48_digit by lia. zs.
      pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA. clear DIG.
      pose proof (u8arr_store_ok asegs _ _ _ (jj - 1)%Z (wa (q + -392 + jj + -1)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia) ltac:(f_equal; lia)) as SOK.
      zs. rewrite le1_small by lia. replace (q + -392 + jj + -1)%Z with (q + -392 + (jj - 1))%Z by lia.
      pose proof (u8arr_write asegs _ _ _ (jj - 1)%Z (Z_to_bv 8 (48 + d)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia)) as DA2. clear DA. store_done.
      assert (EU : upd (pre ++ zb W) (Z.to_nat (jj - 1)) (Z_to_bv 8 (48 + d)) = firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W)).
      { rewrite upd_firstn_skipn by (rewrite length_app, zb_length; unfold zlength in *; lia).
        rewrite firstn_app. replace (Z.to_nat (jj - 1) - length pre)%nat with 0%nat by (unfold zlength in *; lia). cbn [firstn]. rewrite app_nil_r.
        replace (S (Z.to_nat (jj - 1))) with (length pre) by (unfold zlength in *; lia). rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
      rewrite EU in DA2.
      pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG.
      replace (length (firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W))) with 24%nat in DIG
        by (rewrite length_app, length_firstn, zb_length; cbn [length]; unfold zlength in *; lia).
      pose proof (proj1 DA2) as BODY. apply bytes_at_app in BODY. destruct BODY as [_ BODY].
      rewrite length_firstn in BODY. replace (Z.of_nat (Nat.min (Z.to_nat (jj - 1)) (length pre))) with (jj - 1)%Z in BODY by (unfold zlength in *; lia).
      zs.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -392 + (jj - 1))%Z) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | rewrite DX; exact BODY | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
  Qed.
  End Sz1.
  Lemma L_FMTU2 : ltac:(let t := eval cbv delta [L_FMTU2__stmt] in L_FMTU2__stmt in exact t).
  Proof using BS0 GLO HA HAP HS_INTC HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x d jj W prefix PFXA pfx s2s za plp ahi j128 pre pad. ltac2:(SecDiet.SzSec.closeP 'L_FMTU2__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
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

  Hypothesis HS_INTC : S_INTC.

  (* [comment removed for export] *)
  Definition L_FMTU2__stmt : Prop := S_FMTU2.
  Section Sz1.
  Variables fuel x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x d jj W prefix PFXA pfx s2s za plp ahi j128 pre pad : ltac2:(SecDiet.SzSec.tyM 'L_FMTU2__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_FMTU2__body : ltac2:(SecDiet.SzSec.bodyP 'L_FMTU2__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 GLO HA HAP HS_INTC HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 GLO HA HAP HS_INTC HVA LO QHI SEP_B SEP_F SFR KH : unit) => tt).
    intros HH _
           FI LOW DIG Hjj Hjj1 HD PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS. rewrite length_app, zb_length in LDS.
    pose proof (dec_digits_length x) as LDX.
    stmt (HS_INTC fuel HH) as NX.
    ienter.
    zs. zs. brf K1.
    - (* [comment removed for export] *)
      destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [|exfalso; lia].
      rewrite app_nil_r in DIG.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -368)%Z) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | rewrite DX; apply bytes_at_nil; lia | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    - (* [comment removed for export] *)
      destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [exfalso; lia|].
      assert (LW : (Z.of_nat (length W) + 1 <= 20)%Z) by (rewrite DX in LDX; cbn [length] in LDX; lia).
      zs. rewrite lor48_digit by lia. zs.
      pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA. clear DIG.
      pose proof (u8arr_store_ok asegs _ _ _ (jj - 1)%Z (wa (q + -392 + jj + -1)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia) ltac:(f_equal; lia)) as SOK.
      zs. rewrite le1_small by lia. replace (q + -392 + jj + -1)%Z with (q + -392 + (jj - 1))%Z by lia.
      pose proof (u8arr_write asegs _ _ _ (jj - 1)%Z (Z_to_bv 8 (48 + d)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia)) as DA2. clear DA. store_done.
      assert (EU : upd (pre ++ zb W) (Z.to_nat (jj - 1)) (Z_to_bv 8 (48 + d)) = firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W)).
      { rewrite upd_firstn_skipn by (rewrite length_app, zb_length; unfold zlength in *; lia).
        rewrite firstn_app. replace (Z.to_nat (jj - 1) - length pre)%nat with 0%nat by (unfold zlength in *; lia). cbn [firstn]. rewrite app_nil_r.
        replace (S (Z.to_nat (jj - 1))) with (length pre) by (unfold zlength in *; lia). rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
      rewrite EU in DA2.
      pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG.
      replace (length (firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W))) with 24%nat in DIG
        by (rewrite length_app, length_firstn, zb_length; cbn [length]; unfold zlength in *; lia).
      pose proof (proj1 DA2) as BODY. apply bytes_at_app in BODY. destruct BODY as [_ BODY].
      rewrite length_firstn in BODY. replace (Z.of_nat (Nat.min (Z.to_nat (jj - 1)) (length pre))) with (jj - 1)%Z in BODY by (unfold zlength in *; lia).
      zs.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -392 + (jj - 1))%Z) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | rewrite DX; exact BODY | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
        | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
  Qed.
  End Sz1.
  Lemma L_FMTU2 : ltac:(let t := eval cbv delta [L_FMTU2__stmt] in L_FMTU2__stmt in exact t).
  Proof using BS0 GLO HA HAP HS_INTC HVA LO QHI SEP_B SEP_F SFR KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x d jj W prefix PFXA pfx s2s za plp ahi j128 pre pad. ltac2:(SecDiet.SzSec.closeP 'L_FMTU2__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.
End TwB.
End F_printf_core_fmtu2.

(* [comment removed for export] *)
Module F_printf_core_head.
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
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
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
(* [comment removed for export] *)
Local Ltac zrange_pc0 :=
  lazymatch goal with
  | |- inr64 ?e =>
      lazymatch e with
      | bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
      | Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
                              | apply zr_land_l; [zrange | zrange_nonneg] | apply zr_land_r; [zrange_nonneg | zrange] ]
      | Z.lor _ _ => apply zr_lor; [zrange | zrange]
      | Z.lxor _ _ => apply zr_lxor; [zrange | zrange]
      | Z.shiftr _ _ => apply zr_shiftr; [zrange | flia]
      | Z.modulo _ (2^64)%Z => apply zr_mod64
      | Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
      | Z.div _ _ => apply zr_div; [zrange | flia]
      | Z.b2z _ => apply zr_b2z
      | (if _ then _ else _) => apply zr_ite; [zrange | zrange]
      | _ => first [ apply zr_lit; flia
                   | is_var e; progress (unfold e); zrange ]   (* [comment removed for export] *)
      end
  | |- (0 <= ?e < _)%Z => change (inr64 e); zrange
  end.
Local Ltac zrange ::=
  lazymatch goal with
  | |- inr64 Ff => first [ apply zr_lit; solve [ clear - FF SEP_F HAP HVA VAHI LO QHI GLO; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; Lia.lia ]
                         | zrange_pc0 ]
  | |- _ => zrange_pc0
  end.
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

  Hypothesis HS_SCAN : S_SCAN.
  Hypothesis HS_DIR : S_DIR.
  Hypothesis HS_CONV : S_CONV.
  Hypothesis HS_END : S_END.

  (* [comment removed for export] *)
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using BS0 FF GLO HA HAP HF HOUT HS_CONV HS_DIR HS_END HS_SCAN HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HF HOUT HS_CONV HS_DIR HS_END HS_SCAN HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI KH : unit) => tt).
    induction fuel as [|fuel IH]; intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 Ft fc m st i cnt l k args pfx s2s za pl plp alo ahi j128 digs pad _
        FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi Hcnt Hl Hcl.
    { cbn [printf_loop]. apply implAM_unr. }
    rewrite printf_loop_S.
    destruct (sfx i) as [|c s'] eqn:Es. { apply implAM_unr. }
    destruct (sfx_cons_inv fmt i c s' Hi Es) as (Hilt & Ec & Es').
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
    pose proof (fmt_rng i ltac:(zl)) as RGi.
    destruct (Z.eqb_spec c 0) as [C0|C0].
    { (* [comment removed for export] *)
      apply implAM_ret.
      zs. zs. zs. (brf K; try (exfalso; (keep_hyps fmt slots cnt l Hcl K; lia))). zs. rd_fmt i. zs. fix_u8 i. rewrite <- Ec, C0. zs. fixr. zs. if_lit.
      stmt HS_END as NX. jump (eapply NX; [exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | unfold INT_MAX; lia]). }
    rewrite <- Es in *. cbv zeta.
    pose proof (lit_run_sfx fmt i Hi) as (Hn & Hs1 & LIT & Hlit). cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
    set (lit := lit_run (sfx i)) in *. set (n := Z.of_nat (length lit)) in *.
    rewrite Hs1.
    assert (Hn0 : (0 <= n)%Z) by (unfold n; lia).
    destruct (sfx (i + n)) as [|c1 s2] eqn:Es1. { apply implAM_unr. }
    destruct (sfx_cons_inv fmt (i + n) c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
    match goal with |- context [if ?b then munr else _] => destruct b eqn:PCT; [apply implAM_unr|] end.
    (* [comment removed for export] *)
    assert (TERM : (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z).
    { pose proof (lit_run_stop (sfx i) c1 s2 Hs1) as ST12. rewrite <- Ec1.
      destruct ST12 as [E0|E37]; [left; exact E0 | right]. split; [exact E37|].
      rewrite E37, Z.eqb_refl in PCT. cbn [andb] in PCT. destruct s2 as [|c2 s2q]; [discriminate|].
      destruct (sfx_cons_inv fmt (i + n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
      split; [exact Hin1|]. rewrite <- Ec2. apply Z.eqb_neq. exact PCT. }
    stmt HS_SCAN as NXS.
    destruct (0 <? n) eqn:En; try rewrite En in FPC; [apply Z.ltb_lt in En; rename En into Npos | apply Z.ltb_ge in En; rename En into Nz].
    - (* [comment removed for export] *)
      destruct (Z.ltb_spec0 (2147483647 - (cnt + l)) n) as [|Hncl]; [apply implAM_unr|].
      ienter.
      zs. zs. zs. (brf K; try (exfalso; (keep_hyps fmt slots i cnt l Hcl K; lia))). zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
      jump (eapply NXS with (i := i) (n := n) (cnt' := (cnt + l)%Z); [exact FI' | (keep_hyps fmt slots i Hi; lia) | (keep_hyps fmt slots i; lia) | zl | exact LIT | exact TERM | left; exact Npos | unfold INT_MAX; (keep_hyps fmt slots i cnt l Hcnt Hl Hcl; lia) | unfold INT_MAX; (keep_hyps fmt slots i cnt l Hncl; lia) | ]).
      intros a1 a2.
      (* [comment removed for export] *)
      zs. (brf K1; try (exfalso; (keep_hyps Fp FS Ff q lo fmt AP VA slots i c LO GLO SEP_F HAP FF K1; lia))).
      destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K2. clear FLC.
      zs. zs. zs. zs.
      ileave. eapply implAM_bind.
      { eapply out_callq; try exact HS; try exact ST; try exact MI;
          try match goal with |- munch _ m0 _ => hypMU | |- wmono _ m0 _ => hypWM end.
        - rewrite Hlit, zb_firstn. unfold sfx. rewrite zb_skipn. replace (A + i)%Z with (A + Z.of_nat (Z.to_nat i))%Z by lia. apply bytes_at_sub; [exact BY | zl].
        - rewrite Hlit. unfold sfx. apply Forall_sub. exact HF.
        - unfold n, zlength. reflexivity.
        - unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
        - lia. - zl. - zl. - zl. - zl. - unfold INT_MAX in *; zl.
        - eapply sobj_sub; [exact SO_fmt | zl | zl | zl]. - eapply rng_sub'; [exact RG_fmt | zl]. }
      cbv beta. intros [] st'. try clear LOW'; try clear HS; (post_call asegs m). rename MI0 into MI.
      ienter. replace (ret_pc (Z_to_bv 64 635352)) with (Z_to_bv 64 635352) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      zs. zs. br K3.
      (* [comment removed for export] *)
      rewrite <- Es1.
      stmt IH as NXH.
      jumpM (eapply NXH with (i := (i + n)%Z) (cnt := (cnt + l)%Z) (l := n) (k := k));
        [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK | exact FPC
        | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
    - (* [comment removed for export] *)
      assert (En0 : n = 0%Z) by lia. rewrite En0 in *.
      assert (C37 : znth fmt i = 37%Z).
      { destruct TERM as [E0 | [E37 _]]; rewrite Z.add_0_r in *; [|exact E37]. exfalso. apply C0. rewrite Ec. exact E0. }
      replace (i + 0 + 1)%Z with (i + 1)%Z in Es2 by lia.
      destruct (parse_dir s2) as [[d s3]|] eqn:PD; [|apply implAM_unr].
      destruct args as [|a args']; [apply implAM_unr|].
      ienter.
      zs. zs. zs. (brf K; try (exfalso; (keep_hyps fmt slots i cnt l Hcl K; lia))). zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
      jump (eapply NXS with (i := i) (n := 0%Z) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | intros j Hj; lia | rewrite !Z.add_0_r in TERM |- *; exact TERM | right; exact C37 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
      intros a1 a2.
      (* [comment removed for export] *)
      zs. (brf K1; try (exfalso; (keep_hyps Fp FS Ff q lo fmt AP VA slots i c LO GLO SEP_F HAP FF K1; lia))).
      destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K2. clear FLC.
      zs. zs. zs. zs.
      ileave. eapply implAM_bind.
      { eapply out_callq; try exact HS; try exact ST; try exact MI;
          try match goal with |- munch _ m0 _ => hypMU | |- wmono _ m0 _ => hypWM end.
        - apply bytes_at_nil; zl.
        - constructor.
        - reflexivity.
        - unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
        - lia. - zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; lia.
        - change (zlength (@nil Z)) with 0%Z. eapply sobj_sub; [exact SO_fmt | zl | zl | zl]. - change (zlength (@nil Z)) with 0%Z. eapply rng_sub'; [exact RG_fmt | zl]. }
      cbv beta. intros [] st'. try clear LOW'; try clear HS; (post_call asegs m). rename MI0 into MI.
      ienter. replace (ret_pc (Z_to_bv 64 635352)) with (Z_to_bv 64 635352) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      zs. zs. (brf K3; try (exfalso; (keep_hyps fmt slots i K3; lia))).
      (* [comment removed for export] *)
      stmt HS_DIR as NXD.
      jump (eapply NXD with (i := i) (d := d) (rest := s3)); [mk_finv | unfold lo_cells, ssp_guard; exact LOW | lia | zl | rewrite <- Es2; exact PD | ].
      intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp. subst s3.
      (* [comment removed for export] *)
      stmt (HS_CONV fuel IH) as NXC.
      jumpM (eapply NXC with (i4 := k4) (k := k) (c := (cnt + l)%Z) (d := d) (a := a) (args := args'));
        [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK
        | exact FPC | exact FRM | exact FOK | lia | exact Ht | exact (parse_dir_conv_type _ _ _ PD) | lia | exact Hw | exact Hp | exact (parse_dir_xp _ _ _ PD) | unfold INT_MAX; lia ].
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
(* [comment removed for export] *)
Local Ltac zrange_pc0 :=
  lazymatch goal with
  | |- inr64 ?e =>
      lazymatch e with
      | bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
      | Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
                              | apply zr_land_l; [zrange | zrange_nonneg] | apply zr_land_r; [zrange_nonneg | zrange] ]
      | Z.lor _ _ => apply zr_lor; [zrange | zrange]
      | Z.lxor _ _ => apply zr_lxor; [zrange | zrange]
      | Z.shiftr _ _ => apply zr_shiftr; [zrange | flia]
      | Z.modulo _ (2^64)%Z => apply zr_mod64
      | Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
      | Z.div _ _ => apply zr_div; [zrange | flia]
      | Z.b2z _ => apply zr_b2z
      | (if _ then _ else _) => apply zr_ite; [zrange | zrange]
      | _ => first [ apply zr_lit; flia
                   | is_var e; progress (unfold e); zrange ]   (* [comment removed for export] *)
      end
  | |- (0 <= ?e < _)%Z => change (inr64 e); zrange
  end.
Local Ltac zrange ::=
  lazymatch goal with
  | |- inr64 Ff => first [ apply zr_lit; solve [ clear - FF SEP_F HAP HVA VAHI LO QHI GLO; unfold PC_DEPTH, GLOBALS_TOP, zlength in *; Lia.lia ]
                         | zrange_pc0 ]
  | |- _ => zrange_pc0
  end.
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

  Hypothesis HS_SCAN : S_SCAN.
  Hypothesis HS_DIR : S_DIR.
  Hypothesis HS_CONV : S_CONV.
  Hypothesis HS_END : S_END.

  (* [comment removed for export] *)
  Lemma L_HEAD : forall fuel, S_HEAD fuel.
  Proof using BS0 FF GLO HA HAP HF HOUT HS_CONV HS_DIR HS_END HS_SCAN HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HF HOUT HS_CONV HS_DIR HS_END HS_SCAN HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI KH : unit) => tt).
    induction fuel as [|fuel IH]; intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 Ft fc m st i cnt l k args pfx s2s za pl plp alo ahi j128 digs pad _
        FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi Hcnt Hl Hcl.
    { cbn [printf_loop]. apply implAM_unr. }
    rewrite printf_loop_S.
    destruct (sfx i) as [|c s'] eqn:Es. { apply implAM_unr. }
    destruct (sfx_cons_inv fmt i c s' Hi Es) as (Hilt & Ec & Es').
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
    pose proof (fmt_rng i ltac:(zl)) as RGi.
    destruct (Z.eqb_spec c 0) as [C0|C0].
    { (* [comment removed for export] *)
      apply implAM_ret.
      zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. rewrite <- Ec, C0. zs. fixr. zs. if_lit.
      stmt HS_END as NX. jump (eapply NX; [exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | unfold INT_MAX; lia]). }
    rewrite <- Es in *. cbv zeta.
    pose proof (lit_run_sfx fmt i Hi) as (Hn & Hs1 & LIT & Hlit). cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
    set (lit := lit_run (sfx i)) in *. set (n := Z.of_nat (length lit)) in *.
    rewrite Hs1.
    assert (Hn0 : (0 <= n)%Z) by (unfold n; lia).
    destruct (sfx (i + n)) as [|c1 s2] eqn:Es1. { apply implAM_unr. }
    destruct (sfx_cons_inv fmt (i + n) c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
    match goal with |- context [if ?b then munr else _] => destruct b eqn:PCT; [apply implAM_unr|] end.
    (* [comment removed for export] *)
    assert (TERM : (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z).
    { pose proof (lit_run_stop (sfx i) c1 s2 Hs1) as ST12. rewrite <- Ec1.
      destruct ST12 as [E0|E37]; [left; exact E0 | right]. split; [exact E37|].
      rewrite E37, Z.eqb_refl in PCT. cbn [andb] in PCT. destruct s2 as [|c2 s2q]; [discriminate|].
      destruct (sfx_cons_inv fmt (i + n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
      split; [exact Hin1|]. rewrite <- Ec2. apply Z.eqb_neq. exact PCT. }
    stmt HS_SCAN as NXS.
    destruct (0 <? n) eqn:En; try rewrite En in FPC; [apply Z.ltb_lt in En; rename En into Npos | apply Z.ltb_ge in En; rename En into Nz].
    - (* [comment removed for export] *)
      destruct (Z.ltb_spec0 (2147483647 - (cnt + l)) n) as [|Hncl]; [apply implAM_unr|].
      ienter.
      zs. zs. zs. (brf K; try (exfalso; (keep_hyps fmt slots i cnt l Hcl K; lia))). zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
      jump (eapply NXS with (i := i) (n := n) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | exact LIT | exact TERM | left; exact Npos | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
      intros a1 a2.
      (* [comment removed for export] *)
      zs. (brf K1; try (exfalso; (keep_hyps Fp FS Ff q lo fmt AP VA slots i c LO GLO SEP_F HAP FF K1; lia))).
      destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K2. clear FLC.
      zs. zs. zs. zs.
      ileave. eapply implAM_bind.
      { eapply out_callq; try exact HS; try exact ST; try exact MI;
          try match goal with |- munch _ m0 _ => hypMU | |- wmono _ m0 _ => hypWM end.
        - rewrite Hlit, zb_firstn. unfold sfx. rewrite zb_skipn. replace (A + i)%Z with (A + Z.of_nat (Z.to_nat i))%Z by lia. apply bytes_at_sub; [exact BY | zl].
        - rewrite Hlit. unfold sfx. apply Forall_sub. exact HF.
        - unfold n, zlength. reflexivity.
        - unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
        - lia. - zl. - zl. - zl. - zl. - unfold INT_MAX in *; zl.
        - eapply sobj_sub; [exact SO_fmt | zl | zl | zl]. - eapply rng_sub'; [exact RG_fmt | zl]. }
      cbv beta. intros [] st'. try clear LOW'; try clear HS; (post_call asegs m). rename MI0 into MI.
      ienter. replace (ret_pc (Z_to_bv 64 636348)) with (Z_to_bv 64 636348) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      zs. zs. (brf K3; try (exfalso; (keep_hyps fmt slots i Npos K3; lia))).
      (* [comment removed for export] *)
      rewrite <- Es1.
      stmt IH as NXH.
      jumpM (eapply NXH with (i := (i + n)%Z) (cnt := (cnt + l)%Z) (l := n) (k := k));
        [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | (keep_hyps fmt slots i k Hk; lia) | exact AOK | exact FPC
        | exact FRM | exact FOK | (keep_hyps fmt slots i Hi; lia) | (keep_hyps fmt slots i cnt l Hcnt Hl; lia) | (keep_hyps fmt slots i; lia) | unfold INT_MAX; (keep_hyps fmt slots i cnt l Hncl; lia) ].
    - (* [comment removed for export] *)
      assert (En0 : n = 0%Z) by lia. rewrite En0 in *.
      assert (C37 : znth fmt i = 37%Z).
      { destruct TERM as [E0 | [E37 _]]; rewrite Z.add_0_r in *; [|exact E37]. exfalso. apply C0. rewrite Ec. exact E0. }
      replace (i + 0 + 1)%Z with (i + 1)%Z in Es2 by lia.
      destruct (parse_dir s2) as [[d s3]|] eqn:PD; [|apply implAM_unr].
      destruct args as [|a args']; [apply implAM_unr|].
      ienter.
      zs. zs. zs. (brf K; try (exfalso; (keep_hyps fmt slots i cnt l Hcl K; lia))). zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. (brf K0; try (exfalso; (keep_hyps fmt slots i c Ec C37 K0; lia))). rewrite Ec.
      jump (eapply NXS with (i := i) (n := 0%Z) (cnt' := (cnt + l)%Z); [exact FI' | (keep_hyps fmt slots i Hi; lia) | (keep_hyps fmt slots i; lia) | zl | intros j Hj; (keep_hyps fmt slots i j Hj; lia) | rewrite !Z.add_0_r in TERM |- *; exact TERM | right; exact C37 | unfold INT_MAX; (keep_hyps fmt slots i cnt l Hcnt Hl Hcl; lia) | unfold INT_MAX; (keep_hyps fmt slots i cnt l Hcl; lia) | ]).
      intros a1 a2.
      (* [comment removed for export] *)
      zs. (brf K1; try (exfalso; (keep_hyps Fp FS Ff q lo fmt AP VA slots i c LO GLO SEP_F HAP FF K1; lia))).
      destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. (brf K2; try (exfalso; (keep_hyps FB K2; lia))). clear FLC.
      zs. zs. zs. zs.
      ileave. eapply implAM_bind.
      { eapply out_callq; try exact HS; try exact ST; try exact MI;
          try match goal with |- munch _ m0 _ => hypMU | |- wmono _ m0 _ => hypWM end.
        - apply bytes_at_nil; zl.
        - constructor.
        - reflexivity.
        - unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
        - lia. - zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; lia.
        - change (zlength (@nil Z)) with 0%Z. eapply sobj_sub; [exact SO_fmt | zl | zl | zl]. - change (zlength (@nil Z)) with 0%Z. eapply rng_sub'; [exact RG_fmt | zl]. }
      cbv beta. intros [] st'. try clear LOW'; try clear HS; (post_call asegs m). rename MI0 into MI.
      ienter. replace (ret_pc (Z_to_bv 64 636348)) with (Z_to_bv 64 636348) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      zs. zs. (brf K3; try (exfalso; (keep_hyps fmt slots i K3; lia))).
      (* [comment removed for export] *)
      stmt HS_DIR as NXD.
      jump (eapply NXD with (i := i) (d := d) (rest := s3)); [mk_finv | unfold lo_cells, ssp_guard; exact LOW | (keep_hyps fmt slots i Hi; lia) | zl | rewrite <- Es2; exact PD | ].
      intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp. subst s3.
      (* [comment removed for export] *)
      stmt (HS_CONV fuel IH) as NXC.
      jumpM (eapply NXC with (i4 := k4) (k := k) (c := (cnt + l)%Z) (d := d) (a := a) (args := args'));
        [ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | (keep_hyps fmt slots i k Hk; lia) | exact AOK
        | exact FPC | exact FRM | exact FOK | (keep_hyps fmt slots i k4 Hi Hk4; lia) | exact Ht | exact (parse_dir_conv_type _ _ _ PD) | (keep_hyps fmt slots i d Hfl; lia) | exact Hw | exact Hp | exact (parse_dir_xp _ _ _ PD) | unfold INT_MAX; (keep_hyps fmt slots i cnt l Hcnt Hl Hcl; lia) ].
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_head.

(* [comment removed for export] *)
Module F_printf_core_intc2.
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

  Hypothesis HS_TAIL : S_TAIL.

  (* [comment removed for export] *)
  Lemma L_INTC2 : S_INTC2.
  Proof using GLO HS_TAIL LO QHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (GLO HS_TAIL LO QHI KH HA : unit) => tt).
    intros fuel HH x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hp Hc Hargi.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (zb_length body) as LB.
    set (n := Z.of_nat (length body)) in *.
    stmt (HS_TAIL fuel HH) as NX.
    ienter.
    zs. zs. brf K1.
    - (* [comment removed for export] *)
      replace (argi =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. rewrite ?if_false_Z, ?Z.add_0_r.
      zs. zs. zs. zs. replace (argi <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite ?Z.add_0_r.
      zs. brf K2; [ | zs ]; zs; zs.
      all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p n) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
        | body_loc_side | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
    - (* [comment removed for export] *)
      replace (argi =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb]. rewrite ?if_true_Z.
      zs. brf K3.
      + (* [comment removed for export] *)
        assert (Hp0 : p <> 0%Z) by (intros E; apply K3; apply (proj2 (landM64_zero p ltac:(lia))); exact E).
        replace (p =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Hp0).
        zs. zs. zs. zs. replace (argi <? 1)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
        zs. brf K2; [ | zs ]; zs; zs.
        all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p (n + 1)) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
          [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
          | body_loc_side | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
      + (* [comment removed for export] *)
        assert (Hp0 : p = 0%Z) by (apply (proj1 (landM64_zero p ltac:(lia))); exact K3).
        replace (p =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact Hp0).
        zs. zs. zs.
        jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (prefix := prefix) (body := []) (BA := (q + -368)%Z) (PFXA := PFXA));
          [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
          | apply bytes_at_nil; lia | apply Forall_nil
          | body_loc_side | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
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

  Hypothesis HS_TAIL : S_TAIL.

  (* [comment removed for export] *)
  Lemma L_INTC2 : S_INTC2.
  Proof using GLO HS_TAIL LO QHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (GLO HS_TAIL LO QHI KH HA : unit) => tt).
    intros fuel HH x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hp Hc Hargi.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (zb_length body) as LB.
    set (n := Z.of_nat (length body)) in *.
    stmt (HS_TAIL fuel HH) as NX.
    ienter.
    zs. zs. brf K1.
    - (* [comment removed for export] *)
      replace (argi =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. rewrite ?if_false_Z, ?Z.add_0_r.
      zs. zs. zs. zs. replace (argi <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite ?Z.add_0_r.
      zs. brf K2; [ | zs ]; zs; zs.
      all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p n) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
        | body_loc_side | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
    - (* [comment removed for export] *)
      replace (argi =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb]. rewrite ?if_true_Z.
      zs. brf K3.
      + (* [comment removed for export] *)
        assert (Hp0 : p <> 0%Z) by (intros E; apply K3; apply (proj2 (landM64_zero p ltac:(lia))); exact E).
        replace (p =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Hp0).
        zs. zs. zs. zs. replace (argi <? 1)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
        zs. brf K2; [ | zs ]; zs; zs.
        all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p (n + 1)) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
          [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
          | body_loc_side | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
      + (* [comment removed for export] *)
        assert (Hp0 : p = 0%Z) by (apply (proj1 (landM64_zero p ltac:(lia))); exact K3).
        replace (p =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact Hp0).
        zs. zs. zs.
        jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (prefix := prefix) (body := []) (BA := (q + -368)%Z) (PFXA := PFXA));
          [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
          | apply bytes_at_nil; lia | apply Forall_nil
          | body_loc_side | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_intc2.

(* [comment removed for export] *)
Module F_printf_core_p1.
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

  Hypothesis HS_SCAN : S_SCAN.
  Hypothesis HS_DIR : S_DIR.
  Hypothesis HS_EXIT1 : S_EXIT1.

  (* [comment removed for export] *)
  Lemma L_P1 : S_P1.
  Proof using HF HS_DIR HS_EXIT1 HS_SCAN LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF HS_DIR HS_EXIT1 HS_SCAN KH LO HA : unit) => tt).
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 m pfx s2s za pl plp alo ahi j128 digs pad _
           FI MU1 LOW DIG PAD P1.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
    stmt HS_EXIT1 as NXE. stmt HS_SCAN as NXS. stmt HS_DIR as NXD.
    unfold pass1_ok in P1. apply andb_true_iff in P1. destruct P1 as [LITB P1]. apply Z.leb_le in LITB. unfold INT_MAX in LITB.
    pose proof (lit_run_sfx fmt 0 ltac:(lia)) as (Hn & Hs1 & LIT & Hlit). change (sfx 0) with fmt in Hn, Hs1, LIT, Hlit.
    cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
    set (n := Z.of_nat (length (lit_run fmt))) in *.
    rewrite Hs1 in P1. rewrite !Z.add_0_l in *.
    destruct (sfx n) as [|c1 s2] eqn:Es1; [discriminate|].
    destruct (sfx_cons_inv fmt n c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
    pose proof (lit_run_stop fmt c1 s2 Hs1) as C1.
    assert (TERM : (znth fmt n = 0 \/ (znth fmt n = 37 /\ n + 1 < Z.of_nat (length fmt) /\ znth fmt (n + 1) <> 37))%Z
            /\ (znth fmt n <> 0%Z -> exists d rest, parse_dir (sfx (n + 1)) = Some (d, rest))).
    { rewrite <- Ec1. destruct (Z.eqb_spec c1 0) as [E0|E0]; [split; [left; exact E0 | intros X; exfalso; exact (X E0)]|].
      destruct s2 as [|c2 s2q]; [discriminate|].
      destruct (sfx_cons_inv fmt (n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
      apply andb_true_iff in P1. destruct P1 as [P37 PD]. destruct (Z.eqb_spec c2 37) as [|N37]; [discriminate|].
      split. { right. split; [lia|]. split; [unfold zlength in Hin1; exact Hin1|]. rewrite <- Ec2. exact N37. }
      intros _. rewrite <- Es2. destruct (parse_dir (c2 :: s2q)) as [[d rest]|]; [|discriminate]. exists d, rest. reflexivity. }
    destruct TERM as [TERM PDX].
    (* [comment removed for export] *)
    zs. zs. zs. br K. zs. rd_fmt 0%Z. rewrite Z.add_0_r in RD. zs. fix_u8 0%Z. zs. fixr. zs. brf K0.
    - (* [comment removed for export] *)
      assert (n = 0)%Z as N0. { destruct (Z.eq_dec n 0); [assumption|]. exfalso. destruct (LIT 0%Z ltac:(lia)) as [X _]. apply X. exact K0. }
      zs. if_lit. zs. zs. if_lit. zs. zs.
      jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
    - (* [comment removed for export] *)
      jump (eapply NXS with (i := 0%Z) (n := n) (cnt' := 0%Z);
              [ exact FI' | lia | lia | zl | intros j Hj; rewrite Z.add_0_l; apply LIT; exact Hj | rewrite Z.add_0_l; exact TERM
              | destruct (Z.lt_ge_cases 0 n); [left; assumption | right; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1 | exact C1]]
              | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
      intros a1 a2. rewrite !Z.add_0_r.
      zs. if_lit. zs. brf K1.
      + (* [comment removed for export] *)
        assert (N0 : n = 0%Z) by lia.
        destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1|].
        destruct (PDX ltac:(rewrite <- Ec1, C1; lia)) as (d & rest & PD).
        rewrite N0 in PD.
        jump (eapply NXD with (i := 0%Z) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
        intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
        zs. if_lit. zs. zs.
        jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
      + (* [comment removed for export] *)
        zs. zs. zs. br K2. zs. rd_fmt n. zs. fix_u8 n. zs. fixr. zs. brf K3.
        * (* [comment removed for export] *)
          zs. if_lit. zs. zs. if_lit. zs. zs.
          jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
        * (* [comment removed for export] *)
          destruct C1 as [C1|C1]; [exfalso; apply K3; rewrite <- Ec1, C1; reflexivity|].
          destruct (PDX K3) as (d & rest & PD).
          jump (eapply NXS with (i := n) (n := 0%Z) (cnt' := n);
                  [ exact FI' | lia | lia | zl | intros j Hj; exfalso; lia | rewrite Z.add_0_r; exact TERM
                  | right; rewrite <- Ec1; exact C1 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
          intros a1' a2''. rewrite !Z.add_0_r.
          zs. if_lit. zs. if_lit.
          jump (eapply NXD with (i := n) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
          intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
          zs. if_lit. zs. zs.
          jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
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

  Hypothesis HS_SCAN : S_SCAN.
  Hypothesis HS_DIR : S_DIR.
  Hypothesis HS_EXIT1 : S_EXIT1.

  (* [comment removed for export] *)
  Lemma L_P1 : S_P1.
  Proof using HF HS_DIR HS_EXIT1 HS_SCAN LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF HS_DIR HS_EXIT1 HS_SCAN KH LO HA : unit) => tt).
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 m pfx s2s za pl plp alo ahi j128 digs pad _
           FI MU1 LOW DIG PAD P1.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
    stmt HS_EXIT1 as NXE. stmt HS_SCAN as NXS. stmt HS_DIR as NXD.
    unfold pass1_ok in P1. apply andb_true_iff in P1. destruct P1 as [LITB P1]. apply Z.leb_le in LITB. unfold INT_MAX in LITB.
    pose proof (lit_run_sfx fmt 0 ltac:(lia)) as (Hn & Hs1 & LIT & Hlit). change (sfx 0) with fmt in Hn, Hs1, LIT, Hlit.
    cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
    set (n := Z.of_nat (length (lit_run fmt))) in *.
    rewrite Hs1 in P1. rewrite !Z.add_0_l in *.
    destruct (sfx n) as [|c1 s2] eqn:Es1; [discriminate|].
    destruct (sfx_cons_inv fmt n c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
    pose proof (lit_run_stop fmt c1 s2 Hs1) as C1.
    assert (TERM : (znth fmt n = 0 \/ (znth fmt n = 37 /\ n + 1 < Z.of_nat (length fmt) /\ znth fmt (n + 1) <> 37))%Z
            /\ (znth fmt n <> 0%Z -> exists d rest, parse_dir (sfx (n + 1)) = Some (d, rest))).
    { rewrite <- Ec1. destruct (Z.eqb_spec c1 0) as [E0|E0]; [split; [left; exact E0 | intros X; exfalso; exact (X E0)]|].
      destruct s2 as [|c2 s2q]; [discriminate|].
      destruct (sfx_cons_inv fmt (n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
      apply andb_true_iff in P1. destruct P1 as [P37 PD]. destruct (Z.eqb_spec c2 37) as [|N37]; [discriminate|].
      split. { right. split; [lia|]. split; [unfold zlength in Hin1; exact Hin1|]. rewrite <- Ec2. exact N37. }
      intros _. rewrite <- Es2. destruct (parse_dir (c2 :: s2q)) as [[d rest]|]; [|discriminate]. exists d, rest. reflexivity. }
    destruct TERM as [TERM PDX].
    (* [comment removed for export] *)
    zs. zs. zs. br K. zs. rd_fmt 0%Z. rewrite Z.add_0_r in RD. zs. fix_u8 0%Z. zs. fixr. zs. brf K0.
    - (* [comment removed for export] *)
      assert (n = 0)%Z as N0. { destruct (Z.eq_dec n 0); [assumption|]. exfalso. destruct (LIT 0%Z ltac:(lia)) as [X _]. apply X. exact K0. }
      zs. if_lit. zs. zs. if_lit. zs. zs.
      jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
    - (* [comment removed for export] *)
      jump (eapply NXS with (i := 0%Z) (n := n) (cnt' := 0%Z);
              [ exact FI' | lia | lia | zl | intros j Hj; rewrite Z.add_0_l; apply LIT; exact Hj | rewrite Z.add_0_l; exact TERM
              | destruct (Z.lt_ge_cases 0 n); [left; assumption | right; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1 | exact C1]]
              | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
      intros a1 a2. rewrite !Z.add_0_r.
      zs. if_lit. zs. brf K1.
      + (* [comment removed for export] *)
        assert (N0 : n = 0%Z) by lia.
        destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1|].
        destruct (PDX ltac:(rewrite <- Ec1, C1; lia)) as (d & rest & PD).
        rewrite N0 in PD.
        jump (eapply NXD with (i := 0%Z) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
        intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
        zs. if_lit. zs. zs.
        jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
      + (* [comment removed for export] *)
        zs. zs. zs. br K2. zs. rd_fmt n. zs. fix_u8 n. zs. fixr. zs. brf K3.
        * (* [comment removed for export] *)
          zs. if_lit. zs. zs. if_lit. zs. zs.
          jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
        * (* [comment removed for export] *)
          destruct C1 as [C1|C1]; [exfalso; apply K3; rewrite <- Ec1, C1; reflexivity|].
          destruct (PDX K3) as (d & rest & PD).
          jump (eapply NXS with (i := n) (n := 0%Z) (cnt' := n);
                  [ exact FI' | lia | lia | zl | intros j Hj; exfalso; lia | rewrite Z.add_0_r; exact TERM
                  | right; rewrite <- Ec1; exact C1 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
          intros a1' a2''. rewrite !Z.add_0_r.
          zs. if_lit. zs. if_lit.
          jump (eapply NXD with (i := n) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
          intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
          zs. if_lit. zs. zs.
          jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_p1.

(* [comment removed for export] *)
Module F_printf_core_prec.
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
  Lemma L_PLOOP : S_PLOOP.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    intros x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc p s3 pfx s2s za pl plp alo ahi j128 _
           FI LOW Hpos Hacc DG G NE HK.
    remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
    revert pos acc x13 x14 x15 Hpos Hacc DG G HK Hkk.
    induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
    pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
    pose proof (proj1 (digit_range _) DG) as DGR.
    rewrite (sfx_cons fmt pos) in G by zl. rewrite (getint_cons_digit _ _ _ DG) in G.
    destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
    apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.
    assert (Hnx : (pos + 1 < zlength fmt)%Z).
    { destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
      rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
    zs. zs. br K.
    zs. try rewrite (swrap32_small (acc * 10)) by lia.
    zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
    zs. try rewrite (lxor_imax (acc * 10)) by lia.
    zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
    zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
    zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
    zs. try rewrite Z.lor_0_l.
    rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z. zs. zs. zs. zs. brf K2.
    - (* [comment removed for export] *)
      assert (ND : is_digit (znth fmt (pos + 1)) = false).
      { destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
      rewrite (sfx_cons fmt (pos + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
      injection G as Ew Es2.
      zs. zs. zs. zs.
      jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
      rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
    - assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
      jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
      intros k3 a1' a3' a4' Hk3 Hs3 Hnd Hp. apply HK; try assumption. zl.
  Qed.

  Lemma L_PREC : S_PLOOP -> S_PREC.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    intros HPL x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k2 k3 p xp pfx s2s za pl plp alo ahi j128 _
           FI LOW Hk2 PX HK.
    pose proof FI as FI'. dest_finv FI.
    rd_fmt k2. zs. fix_u8 k2. zs. zs.
    destruct PX as [(N46 & Hp & Hxp & Hk3) | (E46 & Hxp & Hk21 & N42 & G & Hk3)].
    - br K. subst p xp k3. do 6 zs. jump (apply HK; unfold INT_MAX; lia).
    - br K. rd_fmt (k2 + 1)%Z. zs. fix_u8 (k2 + 1)%Z. zs. zs. br K1.
      subst xp. zsto 0x9b428%Z.
      pose proof (fmt_rng (k2 + 1) ltac:(zl)) as RG3.
      zs. brf K3.
      + (* [comment removed for export] *)
        assert (ND : is_digit (znth fmt (k2 + 1)) = false).
        { destruct (is_digit (znth fmt (k2 + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG3)) in E. lia. }
        rewrite (sfx_cons fmt (k2 + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
        injection G as Ep Es. subst p.
        assert (k3 = k2 + 1)%Z.
        { pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)) as L2.
          rewrite (sfx_cons fmt (k2 + 1)) in L2 by zl. rewrite Es in L2. lia. }
        subst k3. zs. zs. zs. jump (apply HK; unfold INT_MAX; lia).
      + assert (D3 : is_digit (znth fmt (k2 + 1)) = true) by (apply (proj1 (digit_test _ RG3)); lia).
        zs. zs.
        stmt HPL as NXL. jump (eapply NXL with (pos := (k2 + 1)%Z) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact D3 | exact G | | ]).
        { intros E. pose proof (sfx_length fmt k3 ltac:(zl)) as L. rewrite E in L. change (zlength (@nil Z)) with 0%Z in L. zl. }
        intros k3' a1' a3' a4' Hk3' Hs3 Hnd Hp.
        assert (k3' = k3)%Z.
        { pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt k3' ltac:(zl)) as L2. rewrite <- Hs3 in L2. lia. }
        subst k3'. apply HK. lia.
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
  Lemma L_PLOOP : S_PLOOP.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    intros x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc p s3 pfx s2s za pl plp alo ahi j128 _
           FI LOW Hpos Hacc DG G NE HK.
    remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
    revert pos acc x13 x14 x15 Hpos Hacc DG G HK Hkk.
    induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
    pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
    pose proof (proj1 (digit_range _) DG) as DGR.
    rewrite (sfx_cons fmt pos) in G by zl. rewrite (getint_cons_digit _ _ _ DG) in G.
    destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
    apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.
    assert (Hnx : (pos + 1 < zlength fmt)%Z).
    { destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
      rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
    zs. zs. br K.
    zs. try rewrite (swrap32_small (acc * 10)) by lia.
    zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
    zs. try rewrite (lxor_imax (acc * 10)) by lia.
    zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
    zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
    zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
    zs. try rewrite Z.lor_0_l.
    rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z. zs. zs. zs. zs. brf K2.
    - (* [comment removed for export] *)
      assert (ND : is_digit (znth fmt (pos + 1)) = false).
      { destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
      rewrite (sfx_cons fmt (pos + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
      injection G as Ew Es2.
      zs. zs. zs. zs.
      jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
      rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
    - assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
      jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
      intros k3 a1' a3' a4' Hk3 Hs3 Hnd Hp. apply HK; try assumption. zl.
  Qed.

  Lemma L_PREC : S_PLOOP -> S_PREC.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    intros HPL x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k2 k3 p xp pfx s2s za pl plp alo ahi j128 _
           FI LOW Hk2 PX HK.
    pose proof FI as FI'. dest_finv FI.
    rd_fmt k2. zs. fix_u8 k2. zs. zs.
    destruct PX as [(N46 & Hp & Hxp & Hk3) | (E46 & Hxp & Hk21 & N42 & G & Hk3)].
    - br K. subst p xp k3. do 6 zs. jump (apply HK; unfold INT_MAX; lia).
    - br K. rd_fmt (k2 + 1)%Z. zs. fix_u8 (k2 + 1)%Z. zs. zs. br K1.
      subst xp. zsto 0x9b80c%Z.
      pose proof (fmt_rng (k2 + 1) ltac:(zl)) as RG3.
      zs. brf K3.
      + (* [comment removed for export] *)
        assert (ND : is_digit (znth fmt (k2 + 1)) = false).
        { destruct (is_digit (znth fmt (k2 + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG3)) in E. lia. }
        rewrite (sfx_cons fmt (k2 + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
        injection G as Ep Es. subst p.
        assert (k3 = k2 + 1)%Z.
        { pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)) as L2.
          rewrite (sfx_cons fmt (k2 + 1)) in L2 by zl. rewrite Es in L2. lia. }
        subst k3. zs. zs. zs. jump (apply HK; unfold INT_MAX; lia).
      + assert (D3 : is_digit (znth fmt (k2 + 1)) = true) by (apply (proj1 (digit_test _ RG3)); lia).
        zs. zs.
        stmt HPL as NXL. jump (eapply NXL with (pos := (k2 + 1)%Z) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact D3 | exact G | | ]).
        { intros E. pose proof (sfx_length fmt k3 ltac:(zl)) as L. rewrite E in L. change (zlength (@nil Z)) with 0%Z in L. zl. }
        intros k3' a1' a3' a4' Hk3' Hs3 Hnd Hp.
        assert (k3' = k3)%Z.
        { pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt k3' ltac:(zl)) as L2. rewrite <- Hs3 in L2. lia. }
        subst k3'. apply HK. lia.
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_prec.

(* [comment removed for export] *)
Module F_printf_core_scan.
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
  (* [comment removed for export] *)
  Lemma L_LOOP1 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n : Z) (Q : machine_state -> Prop) (k : nat) (j : Z),
      finv m ->
      k = Z.to_nat (n - j) -> (0 <= j)%Z -> (j < n \/ (j = n /\ znth fmt (i + n) = 37))%Z ->
      (0 <= i)%Z -> (i + n < zlength fmt)%Z ->
      (forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
      (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->
      (* [comment removed for export] *)
      (forall a0, evtF asegs RNG Q
           (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 x11 x12 x13 x14 x15 x16 x17
                    x18 x19 x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 (if (znth fmt (i + n) =? 0)%Z then 0x9b174 else 0x9b17c)) fc None m (seg_rom asegs))) ->
      evtF asegs RNG Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt (i + j))) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 (Z_to_bv 64 (A + i + j)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x9b164) fc None m (seg_rom asegs)).
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    intros until k. induction k as [|k IH]; intros j FI Hk Hj Hjn Hi Hin LIT TERM HK.
    - (* [comment removed for export] *)
      assert (j = n) by lia. subst j. destruct Hjn as [|[_ T37]]; [lia|].
      dest_finv FI. unfold INT_MAX in *.
      zs. rewrite T37. if_lit. specialize (HK (Z_to_bv 64 37)). rewrite T37, (proj2 (Z.eqb_neq 37 0)) in HK by lia. exact HK.
    - destruct Hjn as [Hjn|[Hjn _]]; [|exfalso; lia].
      pose proof (LIT j ltac:(lia)) as [NZ N37].
      pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
      pose proof (fmt_rng (i + j) ltac:(unfold zlength in *; lia)) as RG0.
      zs. br K.
      rd_fmt (i + j + 1)%Z. zs. fix_u8 (i + j + 1)%Z. zs. zs.
      destruct (Z.lt_ge_cases (j + 1) n) as [Hlt|Hge].
      + (* [comment removed for export] *)
        pose proof (LIT (j + 1)%Z ltac:(lia)) as [NZ1 _]. replace (i + j + 1)%Z with (i + (j + 1))%Z in * by lia.
        br K1. replace (A + i + j + 1)%Z with (A + i + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z FI'); try lia; try assumption.
      + assert (j + 1 = n)%Z by lia. replace (i + j + 1)%Z with (i + n)%Z in * by lia.
        replace (A + i + j + 1)%Z with (A + i + n)%Z by lia.
        destruct TERM as [T0 | (T37 & Hn1 & T1)].
        * rewrite T0. if_lit. specialize (HK (Z_to_bv 64 0)). rewrite T0, Z.eqb_refl in HK. exact HK.
        * br K1. eapply (IH n FI'); try lia; try assumption.
  Qed.

  Lemma L_SCAN : S_SCAN.
  Proof using HA HF LO RG_stk RG_img RG_fmt. pin_using (fun (HA HF KH LO : unit) => tt).
    intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m i n cnt' Q _
           FI Hi Hn Hin LIT TERM Hnz Hc Hnc HK.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
    assert (NZ0 : znth fmt i <> 0%Z).
    { destruct Hnz as [Hp|H37]; [|rewrite H37; lia]. pose proof (LIT 0%Z ltac:(lia)) as [X _]. rewrite Z.add_0_r in X. exact X. }
    pose proof (fmt_rng i ltac:(unfold zlength in *; lia)) as RGi.
    zs. zs. br K.
    eapply evtF_eq; [ | eapply L_LOOP1 with (i := i) (n := n) (k := Z.to_nat (n - 0)) (j := 0%Z); try exact FI'; try lia; try assumption ].
    { cbv delta [mkR]. rewrite !Z.add_0_r. reflexivity. }
    { destruct Hnz as [Hp|H37]; [left; lia|]. destruct (Z.lt_ge_cases 0 n); [left; lia|]. right. split; [lia|]. replace (i + n)%Z with i by lia. exact H37. }
    intros a0.
    (* [comment removed for export] *)
    assert (TL : forall a1 a2, evtF asegs RNG Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x9b1a8) fc None m (seg_rom asegs))).
    { intros a1 a2. zs. replace (A + i + n - (A + i))%Z with n by lia. zs. fixr. zs. br K1. zs. fixr. apply HK. }
    destruct TERM as [T0 | (T37 & Hn1 & T1)].
    - rewrite T0, Z.eqb_refl. zs. zs. apply TL.
    - rewrite T37. cbn [Z.eqb Pos.eqb]. zs. zs. rd_fmt (i + n + 1)%Z. zs. fix_u8 (i + n + 1)%Z. zs. br K1. zs. apply TL.
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
  (* [comment removed for export] *)
  Lemma L_LOOP1 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n : Z) (Q : machine_state -> Prop) (k : nat) (j : Z),
      finv m ->
      k = Z.to_nat (n - j) -> (0 <= j)%Z -> (j < n \/ (j = n /\ znth fmt (i + n) = 37))%Z ->
      (0 <= i)%Z -> (i + n < zlength fmt)%Z ->
      (forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
      (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->
      (* [comment removed for export] *)
      (forall a0, evtF asegs RNG Q
           (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 x11 x12 x13 x14 x15 x16 x17
                    x18 x19 x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 (if (znth fmt (i + n) =? 0)%Z then 0x9b558 else 0x9b560)) fc None m (seg_rom asegs))) ->
      evtF asegs RNG Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt (i + j))) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 (Z_to_bv 64 (A + i + j)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x9b548) fc None m (seg_rom asegs)).
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    intros until k. induction k as [|k IH]; intros j FI Hk Hj Hjn Hi Hin LIT TERM HK.
    - (* [comment removed for export] *)
      assert (j = n) by lia. subst j. destruct Hjn as [|[_ T37]]; [lia|].
      dest_finv FI. unfold INT_MAX in *.
      zs. rewrite T37. if_lit. specialize (HK (Z_to_bv 64 37)). rewrite T37, (proj2 (Z.eqb_neq 37 0)) in HK by lia. exact HK.
    - destruct Hjn as [Hjn|[Hjn _]]; [|exfalso; lia].
      pose proof (LIT j ltac:(lia)) as [NZ N37].
      pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
      pose proof (fmt_rng (i + j) ltac:(unfold zlength in *; lia)) as RG0.
      zs. br K.
      rd_fmt (i + j + 1)%Z. zs. fix_u8 (i + j + 1)%Z. zs. zs.
      destruct (Z.lt_ge_cases (j + 1) n) as [Hlt|Hge].
      + (* [comment removed for export] *)
        pose proof (LIT (j + 1)%Z ltac:(lia)) as [NZ1 _]. replace (i + j + 1)%Z with (i + (j + 1))%Z in * by lia.
        br K1. replace (A + i + j + 1)%Z with (A + i + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z FI'); try lia; try assumption.
      + assert (j + 1 = n)%Z by lia. replace (i + j + 1)%Z with (i + n)%Z in * by lia.
        replace (A + i + j + 1)%Z with (A + i + n)%Z by lia.
        destruct TERM as [T0 | (T37 & Hn1 & T1)].
        * rewrite T0. if_lit. specialize (HK (Z_to_bv 64 0)). rewrite T0, Z.eqb_refl in HK. exact HK.
        * br K1. eapply (IH n FI'); try lia; try assumption.
  Qed.

  Lemma L_SCAN : S_SCAN.
  Proof using HA HF LO RG_stk RG_img RG_fmt. pin_using (fun (HA HF KH LO : unit) => tt).
    intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m i n cnt' Q _
           FI Hi Hn Hin LIT TERM Hnz Hc Hnc HK.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
    assert (NZ0 : znth fmt i <> 0%Z).
    { destruct Hnz as [Hp|H37]; [|rewrite H37; lia]. pose proof (LIT 0%Z ltac:(lia)) as [X _]. rewrite Z.add_0_r in X. exact X. }
    pose proof (fmt_rng i ltac:(unfold zlength in *; lia)) as RGi.
    zs. zs. br K.
    eapply evtF_eq; [ | eapply L_LOOP1 with (i := i) (n := n) (k := Z.to_nat (n - 0)) (j := 0%Z); try exact FI'; try lia; try assumption ].
    { cbv delta [mkR]. rewrite !Z.add_0_r. reflexivity. }
    { destruct Hnz as [Hp|H37]; [left; lia|]. destruct (Z.lt_ge_cases 0 n); [left; lia|]. right. split; [lia|]. replace (i + n)%Z with i by lia. exact H37. }
    intros a0.
    (* [comment removed for export] *)
    assert (TL : forall a1 a2, evtF asegs RNG Q
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x9b58c) fc None m (seg_rom asegs))).
    { intros a1 a2. zs. replace (A + i + n - (A + i))%Z with n by lia. zs. fixr. zs. br K1. zs. fixr. apply HK. }
    destruct TERM as [T0 | (T37 & Hn1 & T1)].
    - rewrite T0, Z.eqb_refl. zs. zs. apply TL.
    - rewrite T37. cbn [Z.eqb Pos.eqb]. zs. zs. rd_fmt (i + n + 1)%Z. zs. fix_u8 (i + n + 1)%Z. zs. br K1. zs. apply TL.
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_scan.

(* [comment removed for export] *)
Module F_printf_core_t2.
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

  Hypothesis HS_T3 : S_T3.

  (* [comment removed for export] *)
  Definition L_T2__stmt : Prop := S_T2.
  Section Sz1.
  Variables fuel xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_T2__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_T2__body : ltac2:(SecDiet.SzSec.bodyP 'L_T2__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 FF GLO HA HAP HOUT HS_T3 HVA LO QHI SEP_B SEP_F SFL TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HS_T3 HVA LO QHI SEP_B SEP_F SFL TOK TQ KH : unit) => tt).
    intros HH _
           TI FRM FOK Hc Hw Hwq Hcw.
    pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
    ienter.
    destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K5. clear FLC.
    zs. zs. zs. zs.
    out_call.
    1:{ apply HPFX. exact MI. }
    1:{ exact PRNG. }
    1:{ rewrite Hpl. reflexivity. }
    1:{ lia. } 1:{ zl. } (* [comment removed for export] *) 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
    match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
    stmt (HS_T3 fuel HH) as NX3.
    jumpM (eapply NX3 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
      [ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.
  End Sz1.
  Lemma L_T2 : ltac:(let t := eval cbv delta [L_T2__stmt] in L_T2__stmt in exact t).
  Proof using BS0 FF GLO HA HAP HOUT HS_T3 HVA LO QHI SEP_B SEP_F SFL TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_T2__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
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

  Hypothesis HS_T3 : S_T3.

  (* [comment removed for export] *)
  Definition L_T2__stmt : Prop := S_T2.
  Section Sz1.
  Variables fuel xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_T2__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_T2__body : ltac2:(SecDiet.SzSec.bodyP 'L_T2__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 FF GLO HA HAP HOUT HS_T3 HVA LO QHI SEP_B SEP_F SFL TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HS_T3 HVA LO QHI SEP_B SEP_F SFL TOK TQ KH : unit) => tt).
    intros HH _
           TI FRM FOK Hc Hw Hwq Hcw.
    pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
    ienter.
    destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K5. clear FLC.
    zs. zs. zs. zs.
    out_call.
    1:{ apply HPFX. exact MI. }
    1:{ exact PRNG. }
    1:{ rewrite Hpl. reflexivity. }
    1:{ lia. } 1:{ zl. } (* [comment removed for export] *) 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
    match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
    stmt (HS_T3 fuel HH) as NX3.
    jumpM (eapply NX3 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
      [ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.
  End Sz1.
  Lemma L_T2 : ltac:(let t := eval cbv delta [L_T2__stmt] in L_T2__stmt in exact t).
  Proof using BS0 FF GLO HA HAP HOUT HS_T3 HVA LO QHI SEP_B SEP_F SFL TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_T2__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.
End TwB.
End F_printf_core_t2.

(* [comment removed for export] *)
Module F_printf_core_t5.
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

  Hypothesis HS_T6 : S_T6.

  (* [comment removed for export] *)
  Definition L_T5__stmt : Prop := S_T5.
  Section Sz1.
  Variables fuel xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_T5__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_T5__body : ltac2:(SecDiet.SzSec.bodyP 'L_T5__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 FF GLO HA HAP HOUT HS_T6 HVA LO QHI SEP_B SEP_F SFL TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HS_T6 HVA LO QHI SEP_B SEP_F SFL TOK TQ KH : unit) => tt).
    intros HH _
           TI FRM FOK Hc Hw Hwq Hcw.
    pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
    ienter.
    destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K5. clear FLC.
    zs. zs. zs. zs.
    out_call.
    1:{ exact BODY. }
    1:{ exact BRNG. }
    1:{ rewrite Hn. reflexivity. }
    1:{ lia. } 1:{ zl. } (* [comment removed for export] *) 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
    match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
    stmt (HS_T6 fuel HH) as NX6.
    jumpM (eapply NX6 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
      [ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.
  End Sz1.
  Lemma L_T5 : ltac:(let t := eval cbv delta [L_T5__stmt] in L_T5__stmt in exact t).
  Proof using BS0 FF GLO HA HAP HOUT HS_T6 HVA LO QHI SEP_B SEP_F SFL TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_T5__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
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

  Hypothesis HS_T6 : S_T6.

  (* [comment removed for export] *)
  Definition L_T5__stmt : Prop := S_T5.
  Section Sz1.
  Variables fuel xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad : ltac2:(SecDiet.SzSec.tyM 'L_T5__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma L_T5__body : ltac2:(SecDiet.SzSec.bodyP 'L_T5__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0 FF GLO HA HAP HOUT HS_T6 HVA LO QHI SEP_B SEP_F SFL TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (BS0 FF GLO HA HAP HOUT HS_T6 HVA LO QHI SEP_B SEP_F SFL TOK TQ KH : unit) => tt).
    intros HH _
           TI FRM FOK Hc Hw Hwq Hcw.
    pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
    ienter.
    destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K5. clear FLC.
    zs. zs. zs. zs.
    out_call.
    1:{ exact BODY. }
    1:{ exact BRNG. }
    1:{ rewrite Hn. reflexivity. }
    1:{ lia. } 1:{ zl. } (* [comment removed for export] *) 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
    match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
    stmt (HS_T6 fuel HH) as NX6.
    jumpM (eapply NX6 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
      [ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
  Qed.
  End Sz1.
  Lemma L_T5 : ltac:(let t := eval cbv delta [L_T5__stmt] in L_T5__stmt in exact t).
  Proof using BS0 FF GLO HA HAP HOUT HS_T6 HVA LO QHI SEP_B SEP_F SFL TOK TQ KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad. ltac2:(SecDiet.SzSec.closeP 'L_T5__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PrintfCore.
End TwB.
End F_printf_core_t5.

(* [comment removed for export] *)
Module F_printf_core_width.
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
  Lemma L_WLOOP : S_WLOOP.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
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
    (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
      assert (ND : is_digit (znth fmt (pos + 1)) = false).
      { destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
      rewrite (sfx_cons fmt (pos + 1)) in G by (unfold zlength in *; lia). rewrite (getint_cons_nondigit _ _ _ ND) in G.
      injection G as Ew Es2.
      zs. br K3.
      jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
      rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
    - (* [comment removed for export] *)
      assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
      jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
      intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
  Qed.

  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    intros HWL x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k1 w s2 pfx s2s za pl plp alo ahi j128 _
           FI LOW Hk1 G NE HK.
    pose proof FI as FI'. dest_finv FI.
    pose proof (fmt_rng k1 ltac:(zl)) as RG1.
    zs. zs. zs. zs. brf K.
    - (* [comment removed for export] *)
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
  Lemma L_WLOOP : S_WLOOP.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
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
    (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
      assert (ND : is_digit (znth fmt (pos + 1)) = false).
      { destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
      rewrite (sfx_cons fmt (pos + 1)) in G by (unfold zlength in *; lia). rewrite (getint_cons_nondigit _ _ _ ND) in G.
      injection G as Ew Es2.
      zs. br K3.
      jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
      rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
    - (* [comment removed for export] *)
      assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
      jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
      intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
  Qed.

  Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
  Proof using HF LO HA RG_stk RG_img RG_fmt. pin_using (fun (HF KH LO HA : unit) => tt).
    intros HWL x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k1 w s2 pfx s2s za pl plp alo ahi j128 _
           FI LOW Hk1 G NE HK.
    pose proof FI as FI'. dest_finv FI.
    pose proof (fmt_rng k1 ltac:(zl)) as RG1.
    zs. zs. zs. zs. brf K.
    - (* [comment removed for export] *)
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
End TwB.
End F_printf_core_width.

(* [comment removed for export] *)
Module F_printf_core_xloop.
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
  Lemma L_XLOOP : S_XLOOP.
  Proof using GLO LO QHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (GLO LO QHI KH HA : unit) => tt).
    intros x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m l x.
    remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x12 x13 x23 m.
    induction nx as [nx IH] using lt_wf_ind.
    intros x Enx x12 x13 x23 m j ds _ MI DIG Hx Hl Hj ->.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (hex_digits_step l x ltac:(lia)) as DS.
    pose proof (Z.div_pos x 16 ltac:(lia) ltac:(lia)) as Q0.
    pose proof (Z.mod_pos_bound x 16 ltac:(lia)) as R0.
    assert (Q1 : (x / 16 < 1152921504606846976)%Z) by (apply Z.div_lt_upper_bound; lia).
    assert (LD : (1 <= zlength (hex_digits l x))%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    pose proof (hexchar_range 0 (x mod 16)%Z ltac:(lia) ltac:(lia)) as XR. rewrite Z.lor_0_r in XR.
    pose proof (hexchar_range l (x mod 16)%Z Hl ltac:(lia)) as HR.
    zs. zs. zs. zs.
    replace (Z.land x 15) with (x mod 16)%Z in * by (change 15%Z with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
    pose proof (xdigits_read _ (x mod 16)%Z MI ltac:(lia)) as RD.
    zs. cbv beta. rewrite (u8_lit (znth XDIGITS (x mod 16))) by lia.
    zs. replace (Z.shiftr x 4) with (x / 16)%Z by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    zs. try rewrite (land_W64_small (znth XDIGITS (x mod 16))) by lia.
    set (c := Z.lor (znth XDIGITS (x mod 16)) l) in *.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
    pose proof (u8arr_store_ok asegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
    pose proof (u8arr_write asegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
    zs. zs. brf K.
    - (* [comment removed for export] *)
      eapply evtF_mono.
      { eapply (IH (Z.to_nat (x / 16)) ltac:(lia) (x / 16)%Z eq_refl) with (j := (j - 1)%Z); [ exact MI | exact DIG1 | lia | exact Hl | | f_equal; lia ].
        rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
      cbv beta. intros ms' P. destruct P as (a2' & a3' & m' & -> & MU' & WM' & MI' & DIG' & HW).
      unfold xloop_post. exists a2', a3', m'. cbv zeta.
      assert (EL : zlength (hex_digits l x) = (zlength (hex_digits l (x / 16)) + 1)%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
      rewrite EL.
      split; [ mseq | ].
      split; [ eapply munch_trans; [exact MU | exact MU'] | ].
      split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
      split; [ exact MI' | ].
      split.
      { replace (firstn (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds)
          with (firstn (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb (hex_digits l (x / 16)) ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
        rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
        replace (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) with (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) by lia.
        replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
        rewrite DS, zb_app, <- !app_assoc. reflexivity. }
      unfold zlength in *. lia.
    - (* [comment removed for export] *)
      apply evtF_done. unfold xloop_post. eexists _, _, _. cbv zeta.
      assert (E0 : hex_digits l (x / 16) = []) by (replace (x / 16)%Z with 0%Z by lia; apply hex_digits_0).
      assert (EL : zlength (hex_digits l x) = 1%Z) by (rewrite DS, E0; reflexivity).
      rewrite EL.
      split; [ mseq | ].
      split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
      split.
      { replace (firstn (Z.to_nat (j - 1)) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
        rewrite upd_firstn_skipn by (rewrite LDS; lia). rewrite DS, E0. cbn [zb map app].
        replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
      lia.
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
  Lemma L_XLOOP : S_XLOOP.
  Proof using GLO LO QHI HA KH RG_stk RG_img RG_ap RG_va RG_F RG_B RG_fmt ENV0 SO_stk SO_fmt SO_pfx SO_F SO_B. pin_using (fun (GLO LO QHI KH HA : unit) => tt).
    intros x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m l x.
    remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x12 x13 x23 m.
    induction nx as [nx IH] using lt_wf_ind.
    intros x Enx x12 x13 x23 m j ds _ MI DIG Hx Hl Hj ->.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
    pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (hex_digits_step l x ltac:(lia)) as DS.
    pose proof (Z.div_pos x 16 ltac:(lia) ltac:(lia)) as Q0.
    pose proof (Z.mod_pos_bound x 16 ltac:(lia)) as R0.
    assert (Q1 : (x / 16 < 1152921504606846976)%Z) by (apply Z.div_lt_upper_bound; lia).
    assert (LD : (1 <= zlength (hex_digits l x))%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    pose proof (hexchar_range 0 (x mod 16)%Z ltac:(lia) ltac:(lia)) as XR. rewrite Z.lor_0_r in XR.
    pose proof (hexchar_range l (x mod 16)%Z Hl ltac:(lia)) as HR.
    zs. zs. zs. zs.
    replace (Z.land x 15) with (x mod 16)%Z in * by (change 15%Z with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
    pose proof (xdigits_read _ (x mod 16)%Z MI ltac:(lia)) as RD.
    zs. cbv beta. rewrite (u8_lit (znth XDIGITS (x mod 16))) by lia.
    zs. replace (Z.shiftr x 4) with (x / 16)%Z by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    zs. try rewrite (land_W64_small (znth XDIGITS (x mod 16))) by lia.
    set (c := Z.lor (znth XDIGITS (x mod 16)) l) in *.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
    pose proof (u8arr_store_ok asegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
    pose proof (u8arr_write asegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
    zs. zs. brf K.
    - (* [comment removed for export] *)
      eapply evtF_mono.
      { eapply (IH (Z.to_nat (x / 16)) ltac:(lia) (x / 16)%Z eq_refl) with (j := (j - 1)%Z); [ exact MI | exact DIG1 | lia | exact Hl | | f_equal; lia ].
        rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
      cbv beta. intros ms' P. destruct P as (a2' & a3' & m' & -> & MU' & WM' & MI' & DIG' & HW).
      unfold xloop_post. exists a2', a3', m'. cbv zeta.
      assert (EL : zlength (hex_digits l x) = (zlength (hex_digits l (x / 16)) + 1)%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
      rewrite EL.
      split; [ mseq | ].
      split; [ eapply munch_trans; [exact MU | exact MU'] | ].
      split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
      split; [ exact MI' | ].
      split.
      { replace (firstn (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds)
          with (firstn (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb (hex_digits l (x / 16)) ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
        rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
        replace (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) with (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) by lia.
        replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
        rewrite DS, zb_app, <- !app_assoc. reflexivity. }
      unfold zlength in *. lia.
    - (* [comment removed for export] *)
      apply evtF_done. unfold xloop_post. eexists _, _, _. cbv zeta.
      assert (E0 : hex_digits l (x / 16) = []) by (replace (x / 16)%Z with 0%Z by lia; apply hex_digits_0).
      assert (EL : zlength (hex_digits l x) = 1%Z) by (rewrite DS, E0; reflexivity).
      rewrite EL.
      split; [ mseq | ].
      split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
      split.
      { replace (firstn (Z.to_nat (j - 1)) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
        rewrite upd_firstn_skipn by (rewrite LDS; lia). rewrite DS, E0. cbn [zb map app].
        replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
      lia.
  Qed.
End PrintfCore.
End TwB.
End F_printf_core_xloop.
