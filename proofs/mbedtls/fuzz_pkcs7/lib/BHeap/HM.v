(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_DepotA AW_DepotC AW_DepotInv AW_DepotTop AW_MallocA AW_AllocA
     AW_Poison AW_AllocB AW_MallocB AW_MallocC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined AW_Refill AW_Populate AW_Large.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Blist AW_FakeDefs AW_MmapDie AW_MmapFixedNR AW_PoisonBig AW_SFree5 AW_SMalloc.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_HM () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctx"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctxlen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_fs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocC.msegA_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.fin_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.thr_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Large.large_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DECORATE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_sb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ri_base"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_FL_PPART"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_MHOOKS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_Q_MAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineMax"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineMin"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineCache"; "ARUN_1.A_MRN"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_top"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "ARUN_1.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_UAR_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PoisonBig.rsmr_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SMalloc.smalloc_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_errno"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SFree5.A_F5WORD"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SFree5.f5word"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.b12_ro"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocB.A_ERRNO"; "ARUN_1.A_OOM"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FB_MUTEX"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Stdlib.ZArith.BinInt.Z.le"; "ARUN_1.hm_pclass"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cache"; "ARUN_1.hm_tstats"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_hdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_st"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_n"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_user"; "ARUN_1.shad"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.div"; "ARUN_1.zeros"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.hd_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.last_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bsum"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "ARUN_1.bn_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "ARUN_1.hm_qhead"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.blist"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_Q_GLOBAL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bwf"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_Q_CMUTEX"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_bytes"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_nres"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.emb_cells"; "ARUN_1.emb_P"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "ARUN_1.emb_cap"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_esz"; "ARUN_1.hpure"; "ARUN_1.hm_maps"; "ARUN_1.hm_statics"; "ARUN_1.hm_thread"; "ARUN_1.hm_depot"; "ARUN_1.hm_chunks"; "ARUN_1.hm_regions"; "ARUN_1.hm_quar"; "ARUN_1.hm_sec"; "ARUN_1.hm_fake"; "ARUN_1.hm_ia"; "ARUN_1.hm_emb"].


Notation w64 := (Z_to_bv 64).
Notation b8 := (Z_to_bv 8).

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
Section ARUN_1. Context {hAR : arun}.
Definition shad (a : Z) : Z := 0x7fff8000 + a / 8.
Definition zeros (n : Z) : list byte := repeat (b8 0) (Z.to_nat n).
Definition fill (v n : Z) : list byte := repeat (b8 v) (Z.to_nat n).

(* [comment removed for export] *)
Definition A_UAR_GOT : Z := 0x0f5ea8.     (* [comment removed for export] *)
Definition A_OOM : Z := 0x18bc60.         (* [comment removed for export] *)
Definition A_MRN : Z := 0x18bc61.         (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hm_maps (L : alayout) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HM ()) "(0.(1.$2.O1.+7???7000.+10000000.)(0.(1.$2.O1.+2008???7000.+=???0001000.)(0.(1.$2.O1.(3.O2.)(4.(5.O2.)(3.O2.)))(0.(1.$2.O1.(6.O2.)+1000.)(0.(1.$2.O1.(7.O2.)(8.O2.))(1.$2.O1.(9.O2.)$:.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hm_ro (L : alayout) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HM ()) "ZT,$;.(6.O2.)ZCTX,$;.(7.O2.)(0.(<.O1.R2.R1.)(0.(=.O1.R2.R1.)(0.(>.O1.)(0.(?.O1.)(0.(10.O1.)(0.(11.O1.R1.R2.)(0.(12.O1.(13.O2.))(0.(14.$2.O1.$15.(16.$17.(18.(19.&40.$1:.))(1;.$17.)))(0.(14.$2.O1.$1:.(16.$17.(18.(19.&40.+1000.))(1;.$17.)))(0.(14.$2.O1.$1<.(16.$17.(18.(19.&40.$1=.))(1;.$17.)))(0.(14.$2.O1.$1>.(16.$17.(1?.(19.&8.=))(1;.$17.)))(0.(14.$2.O1.$20.(16.$17.(18.(19.&40.=))(1;.$17.)))(0.(14.$2.O1.(21.$22.+28.)(16.$17.(23.(19.&40.+????????.))(1;.$17.)))(0.(14.$2.O1.(21.$22.+38.)(16.$17.(1?.(19.&8.=))(1;.$17.)))(0.(14.$2.O1.(21.$22.+20.)(16.$17.(18.(19.&40.(24.O2.)))(1;.$17.)))(0.(14.$2.O1.(21.$22.+30.)(16.$17.(18.(19.&40.(25.O2.)))(1;.$17.)))(0.(14.$2.O1.$26.(16.$17.(1?.(19.&8.+1.))(1;.$17.)))(0.(14.$2.O1.(21.$27.+8.)(16.$17.(18.(19.&40.=))(1;.$17.)))(0.(14.$2.O1.$28.(16.$17.(18.(19.&40.$29.))(16.$17.(18.(19.&40.$2:.))(16.$17.(18.(19.&40.$2;.))(1;.$17.)))))(0.(14.$2.O1.$2<.(16.$17.(1?.(19.&8.+1.))(1;.$17.)))(0.(14.$2.O1.(21.R1.+8.)(16.$17.(23.(19.&40.=))(1;.$17.)))(0.(14.$2.O1.R2.(16.$17.(18.(19.&40.R1.))(1;.$17.)))(0.(14.$2.O1.(21.R2.+8.)(16.$17.(18.(19.&40.(2=.O2.)))(16.$17.(18.(19.&40.(4.(2=.O2.)(2>.+2.+17.))))(1;.$17.))))(0.(14.$2.O1.(21.R2.+28.)(16.$17.(1?.(19.&8.=))(1;.$17.)))(0.(14.$2.O1.(21.R2.+48.)(16.$17.(18.(19.&40.(9.O2.)))(1;.$17.)))(0.(2?.(30.&8.)Lf88,(30.&8.)(14.$2.O1.(21.$31.+58.)(16.$17.(1?.R1.)(1;.$17.))))(0.(14.$2.O1.$32.(16.$17.(18.(19.&40.$33.))(1;.$17.)))(0.(14.$2.O1.$33.(16.$17.(23.(19.&40.+1.))(1;.$17.)))(0.(2?.(30.&40.)Lcan,(30.&40.)(2?.(30.&8.)Ldd,(30.&8.)(2?.(30.&8.)Lmadv,(30.&8.)(34.O1.R3.R2.R1.))))(0.(35.O1.(9.O2.)(36.O2.)R2.R1.)(0.(14.$2.O1.$37.(16.$17.(18.(19.&40.$38.))(1;.$17.)))(0.(2?.(30.&40.)Ltb,(30.&40.)(2?.(30.&40.)Lte,(30.&40.)(14.$2.O1.(21.R4.+30.)(16.$17.(18.R2.)(16.$17.(18.R1.)(1;.$17.))))))(0.(14.$2.O1.+19;626.(16.$17.(1?.(19.&8.+1.))(16.$17.(1?.(19.&8.+1.))(1;.$17.))))(0.(14.$2.O1.+?7;80.(16.$17.(18.(19.&40.+>:990.))(16.$17.(18.(19.&40.+>:8<0.))(1;.$17.))))(39.O1.)))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition hm_rwstat (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HM ()) "(0.(2?.(30.&40.)Le,(30.&40.)(3:.$2.O1.$3;.(16.$17.(23.R1.)(1;.$17.))))(0.(2?.(30.&8.)Lo,(30.&8.)(3:.$2.O1.$3<.(16.$17.(1?.R1.)(1;.$17.))))(3:.$2.O1.$3=.(16.$17.(1?.(19.&8.=))(1;.$17.)))))")
(* [comment removed for export] *).                                 (* [comment removed for export] *)

Definition hm_statics (L : alayout) (m : mem) : Prop := hm_ro L m /\ hm_rwstat m.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hm_pclass (m : mem) (T : Z) (cinit : bool) (c : Z) (p : pcl) (ds : list word) : Prop :=
  rw_cells asegs m (T + 208 + 80 * c) [C4 (w64 (pc_count p)); C4 (w64 (pc_max p)); C8 (w64 (pc_csize p))]
  /\ u32arr asegs m (T + 208 + 80 * c + 16) ds /\ length ds = 16%nat
  /\ firstn (length (pc_chunks p)) ds = map w64 (pc_chunks p)
  /\ (if cinit then pc_max p = max_count c /\ pc_csize p = class_size c else pc_max p = 0 /\ pc_csize p = 0 /\ pc_chunks p = []).

(* [comment removed for export] *)
Definition hm_tstats (m : mem) (T : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HM ()) "(2?.(3>.(30.&40.))Lxs,(3>.(30.&40.))(2?.(3>.(30.&40.))Lbs,(3>.(30.&40.))(0.(3?.$2.O2.(21.O1.+:>0.)R2.)(0.(40.$41.(42.(30.&40.)R2.)#10.)(0.(3?.$2.O2.(21.O1.+;60.)R1.)(40.$41.(42.(30.&40.)R1.)#20.))))))")
(* [comment removed for export] *).

Definition hm_thread (h : ahst) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HM ()) "ZL,$43.(44.O2.)ZT,$;.(6.R1.)(0.(3:.$2.O1.(21.R1.+<60.)(16.$17.(1?.(19.&8.=))(1;.$17.)))(0.(2?.P,$;.(3>.(30.&40.))Lds,P,$;.(3>.(30.&40.))Pc,$;.P,(0.(45.+1.R1.)(45.R1.+1?.))(46.O1.R4.(47.O2.)R2.(48.O2.R2.)A1.R3.R2.))(0.(2?.(30.&40.)Lj0,(30.&40.)(2?.(30.&40.)Lj1,(30.&40.)(3:.$2.O1.(21.R3.+:=0.)(16.$17.(18.R2.)(16.$17.(18.R1.)(1;.$17.))))))(49.O1.R1.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hm_depot (h : ahst) (m : mem) : Prop :=
  let D := h_dep h in depot_inv m (d_n D) (d_nb D) (s_total D) (d_bl D).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hm_hdr (m : mem) (k : chunk) : Prop := ltac2:(CDefT.buildp (gd_tbl_HM ()) "(2?.$;.Lb1,$;.(2?.$;.Lid,$;.(0.(3:.$2.O2.(4:.O1.)(16.$17.(1?.(19.&8.(4;.O1.)))(16.$17.(1?.(19.&8.R2.))(16.$17.(4<.(19.&40.=))(16.$17.(23.(19.&40.(4=.(4>.O1.))))(16.$17.(23.(19.&40.R1.))(16.$17.(23.(19.&40.=))(1;.$17.))))))))(0.(40.$;.(4?.R2.+3.)+1.)(0.(0.(45.=R2.)(50.R2.+100.))(0.(45.=R1.)(50.R1.(2>.+2.+20.))))))))")
(* [comment removed for export] *).

Definition hm_magic (m : mem) (k : chunk) : Prop :=
  16 < ck_rz k -> rw_cells asegs m (ck_ab k) [C8 (w64 kAllocBegMagic); C8 (w64 (ck_hdr k))].

(* [comment removed for export] *)
Definition hm_ushadow (m : mem) (k : chunk) : Prop := ltac2:(CDefT.buildp (gd_tbl_HM ()) "Zu,$;.(51.O1.)Zn,$;.(4=.(4>.O1.))(0.(3:.$2.O2.(52.R2.)(16.$17.(53.(54.(55.R1.+8.))(56.(55.R1.+8.)))(1;.$17.)))P,(57.(40.$;.(58.R1.+8.)=))(3:.$2.O2.(52.(21.R3.(59.(55.R2.+8.)+8.)))(16.$17.(1?.(19.&8.(58.R2.+8.)))(1;.$17.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition hm_quser (m : mem) (k : chunk) : Prop :=
  exists fc, rw_cells asegs m (ck_user k) [C8 fc] /\ wr_at asegs m (ck_user k) (nfix (ck_n k)).

Definition hm_chunk (m : mem) (k : chunk) : Prop :=
  hm_hdr m k /\ hm_magic m k
  /\ (if ck_st k =? CHUNK_ALLOCATED then hm_ushadow m k else hm_quser m k).

Definition hm_chunks (h : ahst) (m : mem) : Prop := Forall (hm_chunk m) (h_chunks h).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hm_region (m : mem) (L : alayout) (c : Z) (r : region) (e : bool) : Prop :=
  let R := ri_addr L c in let RB := region_beg L c in let FA := fa_beg L c in
  let nf := r_nfreed r in let mfa := r_mapped_fa r in let au := r_alloc_user r in let mu := r_mapped_user r in
  rw_cells asegs m R [C8 (w64 0)]                                             (* [comment removed for export] *)
  /\ rw_cells asegs m (R + 16) [C8 (w64 nf)] /\ rw_cells asegs m (R + 24) [C8 (w64 mfa)]
  /\ rw_cells asegs m (R + 32) [C8 (w64 au)] /\ rw_cells asegs m (R + 40) [C8 (w64 0)]
  /\ rw_cells asegs m (R + 48) [C8 (w64 mu)] /\ rw_cells asegs m (R + 56) [C8 (w64 0)]
  /\ rw_cells asegs m (R + 68) [C1 (b8 (if e then 1 else 0))]                 (* [comment removed for export] *)
  /\ (exists stw, rw_cells asegs m (R + 72) [C8 stw])
  /\ (exists s80 s88, rw_cells asegs m (R + 80) [C8 s80; C8 s88])                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ u32arr asegs m FA (map w64 (r_fa r))
  /\ (exists js, u32arr asegs m (FA + 4 * nf) js /\ 4 * (nf + Z.of_nat (length js)) = mfa)
  (* [comment removed for export] *)
  /\ wr_at asegs m RB mu
  (* [comment removed for export] *)
  /\ rw_cells asegs m (shad (RB + au)) [CB (Z.to_nat ((mu - au) / 8)) (fill 0xfa ((mu - au) / 8))]
  /\ (forall k, 0 <= k < au / class_size c -> rw_cells asegs m (shad (chunk_at L c k)) [C1 (b8 0xfa)]).

Definition hm_regions (h : ahst) (m : mem) : Prop :=
  forall c, 1 <= c <= 31 -> hm_region m (h_L h) c (h_reg h c) (a_exh (h_acct h) c).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bn_of (b : batch) : bnode := BN (b_addr b) (b_size b) (map w64 (b_elems b)).

Definition hm_qhead (m : mem) (A : Z) (bs : list bnode) : Prop := ltac2:(CDefT.buildp (gd_tbl_HM ()) "(3:.$2.O3.O2.(16.$17.(18.(19.&40.(5:.(42.$5;.O1.))))(16.$17.(18.(19.&40.(5<.O1.)))(16.$17.(18.(19.&40.(5=.=O1.)))(16.$17.(18.(19.&40.(5>.O1.)))(1;.$17.))))))")
(* [comment removed for export] *).

Definition hm_quar (h : ahst) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HM ()) "ZL,$43.(44.O2.)Ztbs,(3>.$5;.)(5?.$60.$5;.$61.(62.(63.O2.)))Zgbs,(3>.$5;.)(5?.$60.$5;.$61.(62.(64.O2.)))(0.(65.O1.(21.(6.R3.)+50.)R2.)(0.(66.O1.R2.)(0.(65.O1.$67.R1.)(0.(66.O1.R1.)(0.(68.VhAR,(69.$5;.R2.R1.))(0.(3:.$2.O1.$6:.(16.$17.(1?.(19.&8.=))(16.$17.(1?.(19.&8.=))(16.$17.(4<.(19.&40.=))(1;.$17.)))))(0.(40.$;.(6;.(63.O2.))(5>.R2.))(40.$;.(6;.(64.O2.))(5>.R1.)))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hm_sec (h : ahst) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HM ()) "ZL,$43.(44.O2.)ZS,$6<.(6=.O2.)ZPA,$;.(13.R2.)Zcks,(3>.$6>.)(6?.R2.)Zncks,$;.(5:.(42.$6>.R1.))(0.(3:.$2.O1.(21.$22.+70.)(16.$17.(18.(19.&40.(70.R4.)))(16.$17.(18.(19.&40.R1.))(1;.$17.))))(0.(2?.(30.&8.)Lsrt,(30.&8.)(3:.$2.O1.(21.$22.+80.)(16.$17.(1?.R1.)(1;.$17.))))(0.(2?.(3>.(30.&40.))Lst,(3>.(30.&40.))(0.(3:.$2.O1.(21.$22.+88.)(5?.(30.&40.)$17.$18.R1.))(40.$41.(42.(30.&40.)R1.)#4.)))(0.(2?.(3>.(30.&40.))Lbsl,(3>.(30.&40.))(0.(3?.$2.O1.(21.$22.+:8.)R1.)(40.$41.(42.(30.&40.)R1.)#40.)))(0.(3:.$2.O1.(21.$22.+2:8.)(16.$17.(23.(19.&40.=))(1;.$17.)))(0.(2?.(30.&40.)Lg0,(30.&40.)(2?.(30.&40.)Lg1,(30.&40.)(3:.$2.O1.(21.$22.+2<0.)(16.$17.(18.R2.)(16.$17.(18.R1.)(1;.$17.))))))(0.(3?.$2.O1.R3.(5?.$6>.(30.&40.)Lsh,$6>.(19.&40.(71.R1.))R2.))(0.(2?.(3>.(30.&40.))Lrest,(3>.(30.&40.))(0.(3?.$2.O1.(21.R4.(59.+8.R2.))R1.)(40.$;.(59.+8.(21.R2.(5:.(42.(30.&40.)R1.))))(72.O2.))))Pi,$41.Psh,$6>.P,(40.(73.$6>.)(74.$6>.R4.R2.)(75.$6>.R1.))(0.(3:.$2.O1.(71.R2.)(16.$17.(18.(19.&40.(71.R2.)))(16.$17.(18.(19.&40.(76.R2.)))(16.$17.(18.(19.&40.(77.R2.)))(16.$17.(18.(19.&40.(5:.R3.)))(1;.$17.))))))(1.$2.O1.(71.R2.)(76.R2.)))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hm_fake (h : ahst) (LF : list (Z * Z)) (m : mem) : Prop := fake_rep (l_fs (h_L h)) LF m.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hm_ia (h : ahst) (m : mem) : Prop :=
  let ia := h_ia h in
  rw_cells asegs m A_IA_INIT [C1 (b8 (if ia then 1 else 0)); C1 (b8 0); C2 (w64 0)]
  /\ rw_cells asegs m A_IA [C1 (b8 0)]
  /\ rw_cells asegs m (A_IA + 8) [CB (Z.to_nat 0x40000) (zeros 0x40000)]
  /\ (exists cs2, rw_cells asegs m (A_IA + 0x40040) cs2 /\ Z.of_nat (cells_size cs2) = 0xd80)
  /\ (exists p0 p1, rw_cells asegs m (A_IA + 0x40dc0) [C8 p0; C8 p1] /\ (ia = true -> p0 = w64 4096 /\ p1 = w64 (A_IA + 0x40dd0)))
  /\ (exists cs4, rw_cells asegs m (A_IA + 0x40dd0) cs4 /\ Z.of_nat (cells_size cs4) = 0x40248 - 16)
  /\ (exists cs5, rw_cells asegs m (A_IA + 0x81008) cs5 /\ Z.of_nat (cells_size cs5) = 40).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition emb_P (a : Z) : Z := if a =? 0 then 0 else A_EMB + 32.
Definition emb_cap (a : Z) : Z := if a =? 0 then 0 else kEmbBytes.
Definition hm_emb (h : ahst) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HM ()) "(78.(79.(7:.(7;.O2.)))(7:.(7;.O2.))(7<.(7:.(7;.O2.)))(7=.(7;.O2.))O1.)")
(* [comment removed for export] *).

Definition hpure (h : ahst) (LB LF : list (Z * Z)) : Prop :=
  awf' h /\ LB = blocks h.

Definition HMc (h : ahst) (LB LF : list (Z * Z)) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HM ()) "(0.(7>.O4.O3.O2.)(0.(7?.(44.O4.)O1.)(0.(80.(44.O4.)O1.)(0.(81.O4.O1.)(0.(82.O4.O1.)(0.(83.O4.O1.)(0.(84.O4.O1.)(0.(85.O4.O1.)(0.(86.O4.O1.)(0.(87.O4.O2.O1.)(0.(88.O4.O1.)(89.O4.O1.))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End ARUN_1.
