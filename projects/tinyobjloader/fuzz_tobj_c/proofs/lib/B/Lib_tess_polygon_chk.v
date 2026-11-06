(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates"; "cutsE"; "exitsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_states"; "FUEL_pg"; "cutpcs_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA"; "ejcert_hdr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ejcertA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_tess_scale2d.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_chk1 Lib_tess_polygon_chk2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Lib_tess_polygon_chk0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_chk1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_chk2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_tess_polygon_chk3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_tess_polygon_chk4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessPolygonAddr.

Lemma hdr_ok : ltac2:(tb__ "0|0|
S2S0S9S5S3A2S1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma ejcert_pg : ltac2:(tb__ "0|0|
S2S0SaS6S5S7S8P64S3S4A7S1A3").
Proof.
  apply ejcertA_of_cuts; [exact hdr_ok|].

  change (cuts_okE segs FUEL_pg cutpcs_pg 100 PE 0 [Pre_pg; C_pro; C_pro2; C_body0; Kfin; C_c84; C_b6cI; C_s1; Kcm; Knw; Knw2; Kext; Ke1; Ke2; Ke3; Kproj; Kbbp; K708; K830; T_sc3; T_sc4; T_r2; Kaa4; Kb08; Kb14; Kd10; Kb64; Kd60; Ktail; C_fin; C_b6cK; T_sfI; T_sfK] TG = true).
  simple apply cuts_okE_cons; [exact cc_0|].
  simple apply cuts_okE_cons; [exact cc_1|].
  simple apply cuts_okE_cons; [exact cc_2|].
  simple apply cuts_okE_cons; [exact cc_3|].
  simple apply cuts_okE_cons; [exact cc_4|].
  simple apply cuts_okE_cons; [exact cc_5|].
  simple apply cuts_okE_cons; [exact cc_6|].
  simple apply cuts_okE_cons; [exact cc_7|].
  simple apply cuts_okE_cons; [exact cc_8|].
  simple apply cuts_okE_cons; [exact cc_9|].
  simple apply cuts_okE_cons; [exact cc_10|].
  simple apply cuts_okE_cons; [exact cc_11|].
  simple apply cuts_okE_cons; [exact cc_12|].
  simple apply cuts_okE_cons; [exact cc_13|].
  simple apply cuts_okE_cons; [exact cc_14|].
  simple apply cuts_okE_cons; [exact cc_15|].
  simple apply cuts_okE_cons; [exact cc_16|].
  simple apply cuts_okE_cons; [exact cc_17|].
  simple apply cuts_okE_cons; [exact cc_18|].
  simple apply cuts_okE_cons; [exact cc_19|].
  simple apply cuts_okE_cons; [exact cc_20|].
  simple apply cuts_okE_cons; [exact cc_21|].
  simple apply cuts_okE_cons; [exact cc_22|].
  simple apply cuts_okE_cons; [exact cc_23|].
  simple apply cuts_okE_cons; [exact cc_24|].
  simple apply cuts_okE_cons; [exact cc_25|].
  simple apply cuts_okE_cons; [exact cc_26|].
  simple apply cuts_okE_cons; [exact cc_27|].
  simple apply cuts_okE_cons; [exact cc_28|].
  simple apply cuts_okE_cons; [exact cc_29|].
  simple apply cuts_okE_cons; [exact cc_30|].
  simple apply cuts_okE_cons; [exact cc_31|].
  simple apply cuts_okE_cons; [exact cc_32|].
  apply cuts_okE_nil.
Qed.
