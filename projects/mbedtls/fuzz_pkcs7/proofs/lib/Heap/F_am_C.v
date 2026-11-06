(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_am_A F_am_K.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_am_C () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.c_meta_area_tail"; "OSSVerify.KrLib.Heap.Malloc.ctx"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Heap.Malloc.area"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "Corelib.Numbers.BinNums.Z"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_areas"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.F_am_K.carve_st"; "OSSVerify.KrLib.Heap.Malloc.upd_ctx"; "OSSVerify.KrLib.Heap.Malloc.mctx"; "OSSVerify.KrLib.Heap.Malloc.set_avail_meta_areas"; "OSSVerify.KrLib.Heap.Malloc.aadd"; "OSSVerify.KrLib.Heap.Malloc.set_avail_meta_area_count"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_area_count"; "OSSVerify.KrLib.Heap.Malloc.set_areas"; "stdpp.base.insert"; "stdpp.fin_maps.map_insert"; "stdpp.gmap.gmap_partial_alter"; "OSSVerify.KrLib.Heap.Malloc.mkArea"; "OSSVerify.KrLib.Heap.Malloc.a_check"; "OSSVerify.KrLib.Heap.Malloc.a_nslots"; "OSSVerify.KrLib.Heap.Malloc.set_meta_area_tail"; "OSSVerify.KrLib.Heap.Malloc.c_secret"; "OSSVerify.KrLib.Heap.Malloc.NSLOTS"; "OSSVerify.KrLib.Heap.Malloc.set_meta_area_head"].


(* [comment removed for export] *)
Definition pgal (z : Z) : Prop := z mod 4096 = 0.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma carve_st_some st p tl ar : ltac2:(CDefT.buildp (gd_tbl_F_am_C ()) "P,(0.$1.(2.(3.O4.))(4.$5.O2.))P,(0.(6.$7.)(8.$5.$7.(9.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.)(12.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.)O2.(13.O4.))(4.$7.O1.))P,(0.(6.$7.)(8.$5.$7.(9.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.)(12.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.)O3.(13.O4.))(14.$7.))(0.$15.(16.O4.O3.)Zst1,$15.(17.Lc,$18.(19.(4.$5.(1:.O3.+1000.))(1;.(1<.(1=.R1.)+1.)R1.))O4.)Zst2,$15.(1>.(1?.$5.$7.(9.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.)(20.$5.$7.(9.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.)(21.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.))O2.(22.(23.O1.)(4.$5.O3.)(24.O1.))(13.R1.))R1.)ZstC,$15.(17.(25.(4.$5.O3.))R1.)(1>.(1?.$5.$7.(9.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.)(20.$5.$7.(9.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.)(21.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.))O3.(22.(26.(3.R2.))(14.$5.)$27.)(13.R1.))R1.))")
(* [comment removed for export] *).
Proof.
  intros HT Har Hp. assert (NE : tl <> p) by (intros ->; rewrite Hp in Har; discriminate).
  unfold carve_st.
  cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
  cbn [s_areas upd_ctx set_areas]. rewrite Har. rewrite lookup_insert_ne by exact NE. rewrite Hp. reflexivity.
Qed.

Lemma carve_st_none st p : ltac2:(CDefT.buildp (gd_tbl_F_am_C ()) "P,(0.$1.(2.(3.O2.))(14.$5.))P,(0.(6.$7.)(8.$5.$7.(9.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.)(12.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.)O1.(13.O2.))(14.$7.))(0.$15.(16.O2.O1.)Zst1,$15.(17.Lc,$18.(19.(4.$5.(1:.O1.+1000.))(1;.(1<.(1=.R1.)+1.)R1.))O2.)Zst2,$15.(17.(28.(4.$5.O1.))R1.)ZstC,$15.(17.(25.(4.$5.O1.))R1.)(1>.(1?.$5.$7.(9.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.)(20.$5.$7.(9.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.)(21.$5.(:.$;.$<.$=.$>.)(?.$;.$<.$10.$=.$>.$11.)$7.))O1.(22.(26.(3.R2.))(14.$5.)$27.)(13.R1.))R1.))")
(* [comment removed for export] *).
Proof.
  intros HT Hp. unfold carve_st.
  cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
  cbn [s_areas upd_ctx set_areas]. rewrite Hp. reflexivity.
Qed.

