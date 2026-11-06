(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module HW := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU RU_mkfg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Mallkgx Mall1es Mall79j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KInv MI_Inv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KNodes RzImpl KLink KLinkC MSafe KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RzAux.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.RzBridge.RzEvt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require W_ge3a6 W_redqm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require W_rejt8 W_retp0 RF_m8yt Instfes Inst8ld InstDefs InstFree Instjhg Instffk Instrcx Instjk7 Instqy7 Inst41h Instbrv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_redqm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_rejt8.W_re997 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_rejt8.W_reagh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_rejt8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_retp0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Instfes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Inst8ld OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.InstDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.InstFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Instjhg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Instffk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Instrcx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Instjk7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Instqy7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Inst41h OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Instbrv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls6g Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Instr3v Instfdk Inste5w.
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem p0_realloc_cps_top :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : mem) (md : Model) (A : ias) (p n old : Z) (T : TSet),
    p0_ainv A m md -> mem_inv rsegs m ->
    a0 = wz p -> a1 = wz n -> 0 <= n < 2^32 -> p <> 0 -> p0_live A p = Some old ->
    n <= NREQ_CAP -> p0_livebytes A + n <= LIVE_MAX -> p0_nlive A + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
    tp = al_tp LayoutPU -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
    alloc_ceiling <= bv_unsigned sp - AllocSpec.REALLOC_STACK ->
    mapped m (bv_unsigned sp - AllocSpec.REALLOC_STACK) AllocSpec.REALLOC_STACK ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : ias) (m' : mem) (md' : Model),
        p0_ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
        (* [comment removed for export] *)
        (r <> 0 /\ p0_live A' r = Some n /\ (r = p \/ (p0_live A r = None /\ p0_live A' p = None)) /\
             (forall q, q <> r -> q <> p -> p0_live A' q = p0_live A q) /\
             (forall i, 0 <= i < Z.min n old -> m' (wz (r + i)) = m (wz (p + i))) /\
             p0_livebytes A' = p0_livebytes A + n - old /\ p0_nlive A' = p0_nlive A /\
             frame_ok LayoutPU (p0_owned A) (p0_owned A') (bv_unsigned sp) AllocSpec.REALLOC_STACK (blk p old) (blk r n) m m') ->
        realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' (seg_rom rsegs)) md') T) ->
    realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_realloc_pc LayoutPU) m (seg_rom rsegs)) md) T.
Proof. exact (p0_realloc_cps (@slot_private_proof _) (@stride_small_proof _) (@mremap_path_rz_proof _)).   (* [comment removed for export] *) Qed.

End CEIL.
