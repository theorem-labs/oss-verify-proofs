(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "iff"; "@Corelib.Init.Datatypes"; "prod"; "cons"; "pair"; "nat"; "nil"; "list"; "option"; "length"; "Some"; "app"; "false"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "rm"; "sv"; "agree_below"; "valuation"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "div"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "ag_spacebeg"; "aa_live"; "aa_sec"; "aa_q_thread"; "ag_ctx"; "ag_pab"; "ag_thread"; "AA"; "cs_allocated_user"; "sc_map_beg"; "sc_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap"; "DUZh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "in_rangesZ"; "mkACell"; "view"; "@Stdlib.Lists.List"; "In"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kSpaceSize"; "IMG_HI"; "PG"; "kQuarantineCacheMax"; "kQuarantineMin"; "kUserSpaceSize"; "round_up"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "client_addrA"; "UStopLe"; "client_shadowA"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"; "AInvA"; "SEC_INST"; "fs_inv"; "geom_ok"; "inv3"; "live_sep"; "primary_repr"; "secondary_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QRD"; "cls_of"; "q_pure"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_in_view"; "rd_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env"; "hbenv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_exit"; "EXPIN"; "ROSh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_leaf"; "hbleaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "j_min"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b"; "RZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11"; "freeBigA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue"; "spec_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundW SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv ReprGlue Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 RebuildM InvLaws SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2 SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_blind SegQS_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert F0A_hbN_env.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_rebuildW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.F0A_rzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_pure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_scand OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.F0A_hbN_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_exit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma DUZh_RZ : ltac2:(tb__ "0|0|
S29SaS21S0S6S2fR4R3R2R1A4S60R4R3R2R1A4A2Fz;Fch;Fi;FA;").
Proof. intros A i ch z. unfold DUZh, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b.RZ. tauto. Qed.

Record hbleaf (CST XGL : list (Z * Z)) (nW : nat) (A : AA) (rho1 : valuation) (p n : Z) (i : nat) (ch : sec_chunk) : Prop := mkHBL {
  lf_pr : is_primary n = false;
  lf_hi : nth_error (aa_sec A) i = Some ch;
  lf_hu : p = sc_map_beg ch + PG + 2048;
  lf_hsz : sc_size ch = round_up n 8 + 4096;
  lf_hn : 1 <= n;
  lf_hnb : 6144 + N8 n <= sc_map_size ch;
  lf_chf : CHFh ch;
  lf_band : sc_map_beg ch + sc_map_size ch <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= sc_map_beg ch;
  lf_pab : ag_pab (aa_geom A) + kPtrArrayReserve <= sc_map_beg ch \/ sc_map_beg ch + sc_map_size ch <= ag_pab (aa_geom A);
  lf_ncb : 8 * Z.of_nat (length (aa_sec A)) <= kPtrArrayReserve;
  lf_fam : exists f, (f <= 2)%nat /\ fam_ok f (ag_spacebeg (aa_geom A)) (sc_map_beg ch) (sc_map_size ch);
  lf_lst : forall lst, nth_error (aa_sec A) (length (aa_sec A) - 1) = Some lst -> (i < length (aa_sec A) - 1)%nat ->
             sc_map_beg lst + 32 <= sc_map_beg ch \/ sc_map_beg ch + sc_map_size ch <= sc_map_beg lst;
  lf_pins : rw rho1 151%positive = Z_to_bv 64 (ag_thread (aa_geom A)) /\ rw rho1 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))
            /\ rw rho1 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A)) /\ rw rho1 12%positive = Z_to_bv 64 p
            /\ rw rho1 105%positive = Z_to_bv 64 (N8 n) /\ rw rho1 106%positive = Z_to_bv 64 (N8 n / 8)
            /\ rw rho1 123%positive = Z_to_bv 64 (qsize (aa_q_thread A)) /\ 0 <= p < 2 ^ 47;
  lf_zT : forall z, ag_thread (aa_geom A) <= z < ag_thread (aa_geom A) + 0x1000 -> ~ DUZh A i ch z;
  lf_zC : forall z, ag_ctx (aa_geom A) <= z < ag_ctx (aa_geom A) + 0x1000 -> ~ DUZh A i ch z;
  lf_zL : forall z, 0 <= z < IMG_HI -> ~ (SEC_INST + 56 <= z < 0xee070) -> ~ DUZh A i ch z;
  lf_nq : forall a, client_addrA CST A a -> ~ QRD A a;
  lf_nqs : forall a, client_shadowA CST XGL A a -> ~ QRD A a;
  lf_noc : forall l1 l2, aa_live A = l1 ++ (p, n) :: l2 -> forall y, client_addrA CST (freeBigA A l1 l2 i) y -> ~ chunk_zone ch y;
  lf_ro : forall r, EXPIN A rho1 r -> forall k, In k ROSh ->
            cells_in_view r (rd_of segsA (rm rho1)) (fst (spec_range r k) - (let '(_, lo, _, _) := k in lo)) (let '(_, _, _, cs) := k in cs);
  lf_q : cell_ok (view segsA (rm rho1)) (mkACell (ag_thread (aa_geom A) + 104) 8 (qsize (aa_q_thread A))) /\ 0 <= qsize (aa_q_thread A) <= kQuarantineCacheMax;
  lf_sb : HIGH_SHADOW_END <= ag_spacebeg (aa_geom A)
}.

Section Leaf.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S0S32VCST;R1A2S4S62R2A1A1F_;Fa;").
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho : valuation) (p n t : Z) (jv : junkF) (keep : Z -> Prop) (A : AA) (rho1' : valuation).
Let rho1 : valuation := ltac2:(tb__ "0|0|
S5cVA0;Vrho;Vp;Vn;Vt;Vjv;A6").
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S3S0S1aQ40S13Vrho;PcA2A2Vp;A3").
Hypothesis HL0 : ltac2:(tb__ "0|0|
S35S7S0S0A2S9S0S0Vp;Vn;A4S23VA0;A1A3").
Hypothesis HCL : blk_cls p n.
Hypothesis Hii : aa_internal_inited A0 = true.
Hypothesis HBIG : kQuarantineMax < n.
Hypothesis HJMIN : ltac2:(tb__ "0|0|
S3S0S5bVjv;A1S3cA3").
Hypothesis HDO : depot_onlyKf A0 A.
Hypothesis HLK : ltac2:(tb__ "0|0|
S66Vkeep;Vrho1;Vrho1';A3").
Variables (E : axst) (rhoE : valuation) (tpE : list word) (tr : list event) (ms : machine_state) (md : Model).
Hypothesis H : ltac2:(tb__ "0|0|
S54S2dS5eVnW;S41S11VA;VKc;Vrho1';A6VE;VrhoE;VtpE;S9ScS53A1S51Vtr;S52Vms;Vmd;A2A4A6").
Let G : ageom := aa_geom A.

Lemma LJ : ltac2:(tb__ "0|0|
S2S16S2eVrho1';VrhoE;A3S2S46S2dVA;VrhoE;VtpE;Vmd;A5S2VKc;Vtr;Vmd;A2S2S44VA;VrhoE;A2S43VA;VrhoE;A2A2A2A2A2").
Proof. destruct H as [_ [Hag HJ]]. destruct HJ as (HA & _ & _ & HK & Htp & _ & Htop). exact (conj Hag (conj HA (conj HK (conj Htp Htop)))). Qed.
Lemma LERM : ltac2:(tb__ "0|0|
S3S19Q40A1SdS19Q8A1A1F_;S14VrhoE;A1S14Vrho1';A1A3").
Proof. apply functional_extensionality. intros a. symmetry. exact (proj2 (proj2 (proj1 LJ)) a). Qed.
Lemma LPIN : ltac2:(tb__ "0|3|
S2S3S19Q40M0A1M1S13Vrho1';P97A2S18G0S28VG;A1A2A3S2S3G1S13Vrho1';P98A2S18G0S26VG;A1A2A3S2S3G1S13Vrho1';P9bA2S18G0S22VG;A1A2A3S2S3G1S13Vrho1';PcA2S18G0Vp;A2A3S2S3G1S13Vrho1';P69A2S18G0S5dVn;A1M2A2A3S2S3G1S13Vrho1';P6aA2S18G0S1fG2Z8A2A2A3S3G1S13Vrho1';P7bA2S18G0S45S25VA;A1A1A2A3A2A2A2A2A2A2").
Proof.
  destruct HLK as (Lw & _). destruct HDO as (EG & _ & _ & _ & _ & _ & EQT & _). unfold G. rewrite EG, EQT. rewrite !Lw.
  repeat split; try reflexivity. change (rw rho1 12%positive) with (rw rho 12%positive). rewrite <- Hp12. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma LRW : ltac2:(tb__ "0|0|
S1S68R1S2eA2S3S19Q40A1S13VrhoE;R2A2S13Vrho1';R2A2A3F_;Fv;").
Proof. intros v Hv. symmetry. exact (proj1 (proj1 LJ) v Hv). Qed.
Lemma HL' : ltac2:(tb__ "0|0|
S35S7S0S0A2S9S0S0Vp;Vn;A4S23VA;A1A3"). Proof. destruct HDO as (_ & _ & _ & _ & _ & EL & _). rewrite EL. exact HL0. Qed.

Let rK : valuation := ltac2:(tb__ "0|3|
S64VrhoE;S8S7S1S19Q40M0A1M1A2M2S9S1G1P9cS18G0S1bS22VG;A1S38A2A2A4SbG2A1A3A2").
Lemma LK0 : ltac2:(tb__ "0|0|
S5fVKc;VA;VrK;VtpE;Vtr;Vmd;A6").
Proof.
  destruct LJ as (_ & HA & HK & Htp & Htop). destruct LPIN as (P151 & P152 & P155 & _).
  assert (ERM : rm rK = rm rhoE) by (unfold rK; apply rm_rho_sets).
  assert (OTH : forall v, v <> 156%positive -> rw rK v = rw rhoE v) by (intros v Hv; unfold rK; rewrite rho_sets_other; [reflexivity | cbn; intros [E0|[]]; congruence]).
  split; [|split; [exact HK|split; [|split]]].
  - pose proof (AInvA_Q A rhoE tpE md HA) as HQ. unfold AInvQ in *. rewrite ERM. exact HQ.
  - unfold tp_ok in *. rewrite OTH by discriminate. exact Htp.
  - unfold top_high in *. unfold V_DEPTH in *. rewrite !OTH by discriminate. exact Htop.
  - unfold rigidQ. rewrite !OTH by discriminate. rewrite !LRW by (unfold GW; lia). split; [exact P151|]. split; [exact P152|]. split; [exact P155|].
    unfold rK. apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto].
Qed.

Lemma LPARTS : ltac2:(tb__ "0|1|
S2S49VG;A1S2S4aVA;A1S2S50VA;A1S2S0S2S1cZ1R1A2S1cR1Z1eA2A2S2S1cZ0S2aS4fVA;R2A2A1M0A2S1cG0S3dA2A2F_;Fc;S5S30S30S5S30S30S2S4bVA;A1S2S4cR2VA;A2S2S4dR2VA;A2S48R1VA;A2A2A2A2Lmf;A2Lmq;A2A2A2A2A2").
Proof.
  destruct LJ as (_ & HA & _). pose proof (AInvA_Q A rhoE tpE md HA) as HAQ.
  pose proof HAQ as (HG & _ & HF & HRest & _ & HI3 & _). cbn zeta in HRest, HF. destruct HRest as (R1 & _ & R3 & R4 & (R5 & _) & _).
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
  { intros c Hc. destruct R3 as (_ & _ & _ & P4). pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia. }
  split; [exact HG|]. split; [exact HI3|]. split; [exact R5|]. split; [exact HAU|]. eexists. eexists. exact (conj R1 (conj R3 (conj R4 HF))).
Qed.

Section WithChunk.
Variables (i : nat) (ch : sec_chunk).
Hypothesis HI : ltac2:(tb__ "0|0|
S3SdS21A1S37S21S24VA;A1Vi;A3SfS21Vch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S3S0Vp;S1bS1bS2bVch;A1S3aA2Z800A2A3").
Hypothesis HPR : is_primary n = false.

Lemma LZT : ltac2:(tb__ "0|1|
S0S2S1cS28VG;A1M0R1A2S1dR1S1bG0Z1000A2A2A2S4S2fVA;Vi;Vch;R2A4A1F_;Fz;").
Proof. intros z Hz HD. destruct LPARTS as (HG & HI3 & _ & _ & mq & mf & _ & _ & R4 & _). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b.nRZ_T A mq HG R4 HI3 i ch HI z Hz (proj1 (DUZh_RZ A i ch z) HD)). Qed.
Lemma LZC : ltac2:(tb__ "0|1|
S0S2S1cS26VG;A1M0R1A2S1dR1S1bG0Z1000A2A2A2S4S2fVA;Vi;Vch;R2A4A1F_;Fz;").
Proof. intros z Hz HD. destruct LPARTS as (HG & HI3 & _ & _ & mq & mf & _ & _ & R4 & _). exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b.nRZ_ctx A mq HG R4 HI3 i ch HI z Hz (proj1 (DUZh_RZ A i ch z) HD)). Qed.
Lemma LZL : ltac2:(tb__ "0|0|
S0S2S1cZ0R1A2S1dR1S39A2A2S4S2S1cS1bS47Z38A2R2A2S1dR2Zee070A2A2A1S4S2fVA;Vi;Vch;R3A4A1F_;F_;Fz;").
Proof.
  intros z Hz NS HD. destruct LPARTS as (HG & HI3 & _ & _ & mq & mf & _ & _ & R4 & _).
  exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b.nRZ_low A mq R4 i ch HI z ltac:(unfold IMG_HI in Hz; lia) NS (proj1 (DUZh_RZ A i ch z) HD)).
Qed.
Lemma LNQ : ltac2:(tb__ "0|0|
S0S40VCST;VA;R1A3S4S4eVA;R2A2A1F_;Fa;").
Proof. intros a Hc. destruct LPARTS as (HG & HI3 & R5 & HAU & mq & mf & R1 & R3 & R4 & HF). exact (client_not_QRD CST HCST HCSTQ A HG HI3 R5 HAU _ _ R1 R3 R4 HF a Hc). Qed.
Lemma LNQS : ltac2:(tb__ "0|0|
S0S42VCST;VXGL;VA;R1A4S4S4eVA;R2A2A1F_;Fa;").
Proof. intros a Hc. destruct LPARTS as (HG & HI3 & R5 & HAU & mq & mf & R1 & R3 & R4 & HF). exact (cshadow_not_QRD CST XGL HCST HXGL HCSTQ A HG HI3 R5 HAU _ _ R1 R3 R4 HF a Hc). Qed.
Lemma LNOC : ltac2:(tb__ "0|2|
ScS7S0S0A2M0A1M1G1S3G1S23VA;A1S10G0R2S8G0S9S0S0Vp;Vn;A4R1A3A3A3S0S40VCST;S61VA;R4R3Vi;A4R1A3S4S65Vch;R2A2A1F_;Fy;F_;Fl2;Fl1;").
Proof.
  intros l1 l2 HLV y Hc HZ. destruct LPARTS as (HG & HI3 & R5 & HAU & mq & mf & R1 & R3 & R4 & HF).
  assert (NRZ : ~ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b.RZ A i ch y -> False) by (intros X; apply X; right; right; left; exact HZ).
  pose proof R4 as (SC1 & _). destruct (SC1 i ch HI) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & D10 & _ & D12 & _).
  pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; lia)) as BIG. unfold chunk_zone in HZ.
  assert (HF2 : fs_inv mf (freeBigA A l1 l2 i)) by exact HF.
  destruct (client_addr_cases CST (freeBigA A l1 l2 i) y mf HF2 Hc) as [S|[L|[FR|[C|FL]]]]; change (aa_geom (freeBigA A l1 l2 i)) with G in *.
  - fold G in D12. lia.
  - destruct L as (b & m & Hbm & Hx). change (aa_live (freeBigA A l1 l2 i)) with (l1 ++ l2) in Hbm. apply NRZ.
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11.nRZ_liveL A mq HG R1 R3 R4 HI3 i ch HI (l1 ++ l2)) with (b := b) (n := m); [| | exact Hbm | left; pose proof (rz_bound m); lia].
    + intros bn Hbn. rewrite HLV. apply in_app_or in Hbn as [X|X]; apply in_or_app; [left; exact X | right; right; exact X].
    + intros b0 n0 Hb0 Hp0. rewrite <- HU. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11.PL_live_other A l1 l2 p n HLV HPR HI3 b0 n0 Hb0 Hp0).
  - destruct FR as (c & p0 & Hc0 & Hp & _ & Hx). pose proof (fs_geom_nums G c p0 HG Hc0 Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M.
    apply NRZ. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b.nRZ_fsb A mq HG R4 HI3 i ch HI). fold G. lia.
  - destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in *. lia.
  - destruct FL as (c & p0 & Hc0 & Hp & _ & ->). pose proof (fs_geom_nums G c p0 HG Hc0 Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M.
    apply NRZ. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b.nRZ_fsb A mq HG R4 HI3 i ch HI). fold G. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *. lia.
Qed.

Hypothesis HSZ : ltac2:(tb__ "0|0|
S3S0S2cVch;A1S1bS3eVn;Z8A2Z1000A2A3").
Hypothesis HN : 1 <= n.
Let T : Z := ag_thread G.

Lemma LQ : ltac2:(tb__ "0|1|
S2S31S34S2dS14Vrho1';A1A2S33S1bVT;Z68A2U8S45S25VA;A1A1M0A3A2S2S1cZ0G0A2S1cG0S3bA2A2A2").
Proof.
  destruct LJ as (_ & HA & _). pose proof (qF A rhoE tpE md p n HA HL') as QF. cbn zeta in QF. destruct QF as (_ & _ & Qs & QB & _).
  rewrite LERM in Qs. split; [|exact QB]. replace (T + 104) with (ag_thread (aa_geom A) + 80 + 24) by (unfold T, G; lia). exact Qs.
Qed.

Let bsP : list (positive * word) := ltac2:(tb__ "0|3|
S8S7S1S19Q40M0A1M1A2M2S9S1G1Pc8S18G0S27VG;A1A2A4S8G2S9S1G1Pc9S18G0S1eSeS21S24VA;A1A2A1A2A4S8G2S9S1G1Pc3S18G0S1bS22VG;A1S38A2A2A4SbG2A1A3A3A3").
Let rB : valuation := rho_sets rhoE bsP.
Lemma LRB : ltac2:(tb__ "0|5|
S2S1S4S35S1R1S8S1Pc8M0S8S1Pc9M1S8S1Pc3M2SbS1A1A3A3A3A3A1S3S19Q40M3A1M4S13VrB;R2A2S13VrhoE;R2A2A3F_;Fv;S2S3G4SdS19Q8A1A1F_;S14VrB;A1S14VrhoE;A1A3S2S3G4S13VrB;G0A2S18G3S27VG;A1A2A3S2S3G4S13VrB;G1A2S18G3S1eSeS21S24VA;A1A2A1A2A3S3G4S13VrB;G2A2S18G3S1bS22VG;A1S38A2A2A3A2A2A2A2").
Proof.
  assert (NDB : List.NoDup (map fst bsP)) by (cbn; repeat constructor; cbn; intuition discriminate).
  split; [intros v Hv; unfold rB; apply rho_sets_other; exact Hv|]. split; [unfold rB; apply rm_rho_sets|].
  split; [exact (rho_sets_get bsP rhoE _ _ NDB (or_introl eq_refl))|]. split; [exact (rho_sets_get bsP rhoE _ _ NDB (or_intror (or_introl eq_refl)))|].
  exact (rho_sets_get bsP rhoE _ _ NDB (or_intror (or_intror (or_introl eq_refl)))).
Qed.
Lemma LENVB : ltac2:(tb__ "0|0|
S57VA;S9S0S0Vp;Vn;A4Vi;Vch;VrB;A5").
Proof.
  destruct LJ as (_ & HA & HK & Htp & Htop). destruct LPIN as (P151 & P152 & P155 & P12 & _). destruct LRB as (OTH & ERM & E200 & E201 & E195).
  assert (O2 : forall v, (v < GW)%positive -> rw rB v = rw rho1' v).
  { intros v Hv. rewrite OTH; [exact (LRW v Hv)|]. unfold GW in Hv. cbn. intros [<-|[<-|[<-|[]]]]; lia. }
  assert (HAB : AInvA segsA A rB tpE md) by (unfold AInvA in *; rewrite ERM; exact HA).
  assert (HtpB : tp_ok A rB) by (unfold tp_ok in *; rewrite O2 by (unfold GW; lia); rewrite <- (LRW 24%positive) by (unfold GW; lia); exact Htp).
  assert (HtopB : top_high A rB) by (unfold top_high in *; unfold V_DEPTH in *; rewrite !O2 by (unfold GW; lia); rewrite <- !LRW by (unfold GW; lia); exact Htop).
  exact (hbenv_intro Kc HKc A p n i ch HI HU HSZ HN (fun _ => True) rB rB tpE tr md HAB HK HtpB HtopB
           ltac:(rewrite O2 by (unfold GW; lia); exact P151) ltac:(rewrite O2 by (unfold GW; lia); exact P152) ltac:(rewrite O2 by (unfold GW; lia); exact P155)
           (blind_rel_refl segsA _ _ rB) ltac:(rewrite O2 by (unfold GW; lia); exact P12) E200 E201 E195).
Qed.

Definition Pxo (v : positive) : bool := ltac2:(tb__ "0|0|
S36S1S67Vv;A1S8S1Pc3S8S1Pc8SbS1A1A3A3A3").
Lemma LRO : ltac2:(tb__ "0|4|
S17S58VA;Vrho1';R1A3S3fS35S3fR1S59A3S55R4S56S2dS14Vrho1';A1A2S20S12S0S0S63R4R2A2A3S7S7S7S15S0A2M0S0A2M1ScS7S7S0SaA2S15A2A1M2A2M3S0Lk;R2G1G2G1S0Lp0;R2G0S0G0S0Lp1;R2S15S0R1Llo;Ls;X7x1Lz;Lp1;X7x1Ll;Lp0;X7x1A2G3G2Lk;R2G1G2G1G2Lp0;R2G0S0G0G2Lp1;R2S15S0R5Lz0;Ls;X7x1Lz;Lp1;X7x1Lcs;Lp0;X7x1A4F_;Fk;F_;Fr;").
Proof.
  intros r (RW & RL & E195 & E200) k Hk.
  assert (RLe : forall l, rl r l = rl rhoE l) by (intros l; rewrite RL; exact (proj1 (proj2 (proj1 LJ)) l)).
  unfold ROSh in Hk. apply in_app_or in Hk as [Hk|Hk]; [|apply in_app_or in Hk as [Hk|Hk]].
  -
    assert (RCIV0 : rcivb (map carve_obj NRTX) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit.NK nW UStopLe E E E (map carve_obj NRTX) eq_refl RCIV0 A0 Kc rho p n t jv keep A rho1' rhoE tpE tr ms md Hp12 HL0 HCL Hii HJMIN HDO HLK H k Hk) as (_ & _ & _ & CIV).
    assert (HP : forall v, Pnrtx v = true -> rw r v = rw rhoE v).
    { intros v Hv. unfold Pnrtx in Hv. apply existsb_exists in Hv as (j & Hj & Ej). apply Pos.eqb_eq in Ej. subst j.
      assert (LT : (v < GW)%positive) by (unfold GW; cbn in Hj; repeat (destruct Hj as [<-|Hj]; [lia|]); destruct Hj).
      rewrite (LRW v LT). exact (RW v LT). }
    pose proof (proj1 (forallb_forall _ _) NRTX_varsb k Hk) as VB. destruct k as [[[b lo] hi] cs]. apply andb_prop in VB as [VBb VBc].
    cbn [spec_range fst] in CIV |- *. rewrite (eval_agree_P Pnrtx r rhoE b HP RLe VBb). rewrite LERM in CIV.
    unfold cells_in_view in *. apply Forall_forall. intros [[o kk] e] Hc j Hj. pose proof (proj1 (Forall_forall _ _) CIV _ Hc j Hj) as X. cbn beta iota in X.
    rewrite (eval_agree_P Pnrtx r rhoE e HP RLe (proj1 (forallb_forall _ _) VBc _ Hc)). exact X.
  -
    destruct LRB as (OTH & ERM & B200 & B201 & B195).
    assert (HP : forall v, Pxo v = true -> rw r v = rw rB v).
    { intros v Hv. unfold Pxo in Hv. apply existsb_exists in Hv as (j & Hj & Ej). apply Pos.eqb_eq in Ej. subst j. cbn in Hj.
      destruct Hj as [<-|[<-|[]]]; [rewrite E195, B195 | rewrite E200, B200]; reflexivity. }
    assert (RLB : forall l, rl r l = rl rB l) by (intros l; rewrite RLe; unfold rB; rewrite rl_rho_sets; reflexivity).
    assert (IN : In k N_hb) by (unfold N_hb in *; cbn [firstn In] in Hk; cbn [In]; tauto).
    pose proof (proj1 (Forall_forall _ _) (carve_hb A (p, n) i ch rB LENVB) k IN) as CK.
    assert (VB : let '(b, _, _, cs) := k in sv_varsb Pxo b = true /\ forallb (fun c : Z * nat * sv => let '(_, _, e) := c in sv_varsb Pxo e) cs = true).
    { unfold N_hb in Hk. cbn [firstn In] in Hk. destruct Hk as [<-|[<-|[<-|[]]]]; split; reflexivity. }
    destruct k as [[[b lo] hi] cs]. destruct VB as [VBb VBc]. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip.carve_okq in CK. destruct CK as (_ & _ & _ & _ & _ & _ & _ & CIV).
    cbn [spec_range fst]. rewrite (eval_agree_P Pxo r rB b HP RLB VBb). rewrite ERM, LERM in CIV.
    replace (bv_unsigned (eval rB b) + lo - lo) with (bv_unsigned (eval rB b)) by lia.
    unfold cells_in_view in *. apply Forall_forall. intros [[o kk] e] Hc j Hj. pose proof (proj1 (Forall_forall _ _) CIV _ Hc j Hj) as X. cbn beta iota in X.
    rewrite (eval_agree_P Pxo r rB e HP RLB (proj1 (forallb_forall _ _) VBc _ Hc)). exact X.
  -
    destruct Hk as [<-|[]]. destruct LQ as (Qs & _). destruct LPIN as (P151 & _ & _ & _ & _ & _ & P123).
    pose proof (qs_nums A (p, n) i ch rB LENVB) as (T0 & T1 & _). pose proof (topG_range (aa_geom A)) as TG. cbv zeta in T0, T1.
    assert (EcQ : bv_unsigned (eval r cQ) = ag_thread (aa_geom A) + 80).
    { unfold cQ, vT. cbn [eval]. rewrite (RW 151%positive) by (unfold GW; lia). rewrite P151. unfold G. rewrite add_val, !u64_lit by lia. apply Z.mod_small. lia. }
    unfold qsz_spec. cbn [spec_range fst]. rewrite EcQ. replace (ag_thread (aa_geom A) + 80 + 24 - 24) with (ag_thread (aa_geom A) + 80) by lia.
    unfold cells_in_view. constructor; [|constructor]. intros j Hj.
    apply (civ_cell r (rm rho1') (ag_thread (aa_geom A) + 80) 24 8 (qsize (aa_q_thread A)) (SVar 123));
      [replace (ag_thread (aa_geom A) + 80 + 24) with (T + 104) by (unfold T, G; lia); exact Qs | | lia | lia | exact Hj].
    cbn [eval]. rewrite (RW 123%positive) by (unfold GW; lia). exact P123.
Qed.
End WithChunk.

Theorem leaf_facts : ltac2:(tb__ "0|0|
S5SaSaS5S21S21S5aVCST;VXGL;VnW;VA;Vrho1';Vp;Vn;R2R1A9Lch;A2Li;A2").
Proof.
  destruct LJ as (_ & HA & _).
  destruct (hb_pure Kc HKc A rhoE rK tpE tr md p n HA LK0 HL' HBIG) as (HPR & i & ch & HI & HU & HSZ & HN & HNB & CH & BND & PAB & NCB & FAM & LST).
  exists i, ch. pose proof LPIN as (P151 & P152 & P155 & P12 & P105 & P106 & P123).
  assert (PB : 0 <= p < 2 ^ 47).
  { destruct CH as (_ & _ & _ & C4 & C5). unfold PG in HU. pose proof (N8_facts n HN). lia. }
  constructor; try assumption.
  - exact (conj P151 (conj P152 (conj P155 (conj P12 (conj P105 (conj P106 (conj P123 PB))))))).
  - exact (LZT i ch HI).
  - exact (LZC i ch HI).
  - exact (LZL i ch HI).
  - exact (LNQ).
  - exact (LNQS).
  - exact (LNOC i ch HI HU HPR).
  - exact (LRO i ch HI HU HSZ HN).
  - exact (LQ).
  - destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k.thr_facts (K0 Kc) (K0_laws Kc HKc) A rK tpE tr md LK0) as (_ & _ & _ & HSB & _). exact HSB.
Qed.
End Leaf.
