(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep .
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export MallocRep RunParams.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Export HP_F_syscalls.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Prog ImgFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RMallocRep () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Corelib.Init.Datatypes.false"; "Corelib.Numbers.BinNums.N"; "Stdlib.ZArith.BinInt.Z.of_N"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mrd"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_reserved"; "ref_reserved"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_ceil"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_secret"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rp_secret"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_canary"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rp_canary"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RCTX"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ctx_head_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.actives"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.usages"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.unmap_seqs"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.bouncess"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ctx_tail_cells"; "RMLOCK"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "Corelib.Init.Datatypes.nil"; "RNEED_LOCKS"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "RPAGE_SIZE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RGOT_SSP"; "RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.a_check"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.pw"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.a_next"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.a_nslots"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.NSLOTS"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.AREA_HDR"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.META_SIZE"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_cells"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aadd"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.zeros"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.g_meta"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.g_active_idx"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Known"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RP_1.rparams_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ranges_free"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.lr_lo"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.pair"; "Corelib.Lists.ListDef.map"; "stdpp.fin_maps.map_to_list"; "stdpp.gmap.gmap_fold"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RP_1.rmrep"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "stdpp.bitvector.definitions.BV"; "stdpp.bitvector.definitions.Z_to_bv_obligation_1"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RSIZE_CLASSES"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le2"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_secret"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "RP_1.rregions_wf"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wr_in"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mctx"; "RP_1.rmrep_ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RP_1.rarea_rep"; "RP_1.rgroup_rep"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.shadow"; "RP_1.rshadow_rep"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RP_1.rmrep_globals"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.wr8"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.wr16"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_set_avail"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_active"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.shadow_le"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.sh_ticks"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_tick"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_shadow"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"].




(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RCTX : Z := 0x7d3c8.
Definition RMLOCK : Z := 0x7d3c0.
Definition RLIBC : Z := 0x7d350.
Definition RNEED_LOCKS : Z := 0x7d353.   (* [comment removed for export] *)
Definition RPAGE_SIZE : Z := 0x7d380.    (* [comment removed for export] *)
Definition RAUXV_CELL : Z := 0x7d358.    (* [comment removed for export] *)
Definition RSIZE_CLASSES : Z := 0x170fc.
Definition RDEBRUIJN : Z := 0x10a27.
Definition RSMALL_CNT : Z := 0x1715c.
Definition RMED_CNT : Z := 0x17177.
Definition RGOT_SSP : Z := 0x4bcd8.      (* [comment removed for export] *)
Definition RSSP_GUARD : Z := 0x7d330.    (* [comment removed for export] *)
Definition RATP : Z := 0x5d0c8.          (* [comment removed for export] *)
Definition RERRNO : Z := 0x5d024.        (* [comment removed for export] *)

Definition rget_meta_entry : Z := 0x3fda8.
Definition rmalloc_entry : Z := 0x40568.      (* [comment removed for export] *)
Definition rfree_entry : Z := 0x3fbdc.        (* [comment removed for export] *)
Definition ralloc_meta_entry : Z := 0x40290.
Definition ralloc_slot_entry : Z := 0x408d8.
Definition renframe_entry : Z := 0x4117c.
Definition rnontrivial_free_entry : Z := 0x3feb8.
Definition rmmap_entry : Z := 0x41448.
Definition rmunmap_entry : Z := 0x4157c.
Definition rmprotect_entry : Z := 0x41534.
Definition rlock_entry : Z := 0x46f80.
Definition runlock_entry : Z := 0x47208.

(* [comment removed for export] *)
Definition ref_reserved : list (Z * Z) := [(0x10000, 0xd000); (0x1d000, 0x2b000); (0x48000, 0x4000); (0x4c000, 0x32000)].

Lemma reservedZ_ref : reservedZ rsegs = ref_reserved.
Proof. vm_compute. reflexivity. Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)

Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x7e000 <= z) ->
  find_segment rsegs z n = None.
Proof.
  intros z n Hn Hz. apply (find_segment_none_window rsegs 0x10000 0x7e000 z n); [|exact Hn|exact Hz].
  replace (seg_ivs rsegs) with [(65536, 53248); (118784, 176128); (294912, 16384); (311296, 204800)]%Z by (vm_compute; reflexivity).
  repeat constructor; cbn; lia.
Qed.

#[using="Type"] Lemma ref_ro_addr_false : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Px,(0.&40.)P,(1.(2.(3.(4.&40.R1.)+1.)+10000.)(2.+7>000.(4.&40.R1.)))(5.$6.(7.$8.R2.)$9.)")
(* [comment removed for export] *).
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

#[using="Type"] Lemma ref_memory_read_none : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Px,(0.&40.)Pn,$:.P,(2.+1.(;.R1.))P,(1.(2.(3.(4.&40.R3.)(;.R2.))+10000.)(2.+7>000.(4.&40.R3.)))(5.(<.(=.(0.&8.)))(>.$8.R4.R3.)(?.(=.(0.&8.))))")
(* [comment removed for export] *).
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

#[using="Type"] Lemma ref_wview_overlay : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pm,P,(0.&40.)(<.(0.&8.))Px,(0.&40.)P,(1.(2.(3.(4.&40.R1.)+1.)+10000.)(2.+7>000.(4.&40.R1.)))(5.(<.(0.&8.))(10.$8.R3.R2.)A1.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

#[using="Type"] Lemma ref_seg_rom_none : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Px,(0.&40.)P,(1.(2.(3.(4.&40.R1.)+1.)+10000.)(2.+7>000.(4.&40.R1.)))(5.(<.(0.&8.))(11.$8.R2.)(?.(0.&8.)))")
(* [comment removed for export] *).
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

#[using="Type"] Lemma ref_mrd_overlay : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pm,P,(0.&40.)(<.(0.&8.))Px,(0.&40.)P,(1.(2.(3.(4.&40.R1.)+1.)+10000.)(2.+7>000.(4.&40.R1.)))(5.(<.(0.&8.))(12.$8.R3.R2.)A1.R3.R2.)")
(* [comment removed for export] *).
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rparams_ok (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "(13.(5.(=.(14.$15.$15.))(16.O1.)$17.)(13.(5.$15.(18.O1.)(19.VhRP,))(13.(5.$15.(1:.O1.)(1;.VhRP,))(5.$15.(1<.O1.)(1=.VhRP,)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition sparams (st : mstate) : list (Z * Z) * Z * Z * Z := (s_reserved st, s_ceil st, s_secret st, s_canary st).

#[using="Type"] Lemma rparams_ok_same st st' : rparams_ok st -> sparams st' = sparams st -> rparams_ok st'.
Proof. unfold sparams, rparams_ok. (intros dd_H; ddestruct dd_H as (A & B & C & D); intros H). injection H as H1 H2 H3 H4. rewrite H1, H2, H3, H4. auto. Qed.

Section MREP.
Variable st : mstate.
Variable m : word -> option byte.

Definition rmrep_ctx : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "(13.(1>.$8.Vm,$1?.(20.Vst,))(13.(21.$8.Vm,(3.$1?.+50.)(22.Vst,))(13.(21.$8.Vm,(3.$1?.+1=0.)(23.Vst,))(13.(24.$8.Vm,(3.$1?.+350.)(25.Vst,))(13.(24.$8.Vm,(3.$1?.+370.)(26.Vst,))(1>.$8.Vm,(3.$1?.+390.)(27.Vst,)))))))")
(* [comment removed for export] *).

Definition rmrep_globals : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "(13.(1>.$8.Vm,$28.(29.$2:.(2;.(2<.=))(2=.$2:.)))(13.(1>.$8.Vm,$2>.(29.$2:.(2?.(30.=))(2=.$2:.)))(13.(1>.$8.Vm,$31.(29.$2:.(32.(2<.+1000.))(2=.$2:.)))(13.(1>.$8.Vm,$33.(29.$2:.(32.(2<.$34.))(2=.$2:.)))(1>.$8.Vm,$34.(29.$2:.(32.(2<.(1=.VhRP,)))(2=.$2:.)))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rarea_rep (a : aptr) (ar : area) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "(13.(1>.$8.Vm,(35.Vst,O2.)(29.$2:.(32.(2<.(36.O1.)))(29.$2:.(32.(37.Vst,(38.O1.)))(29.$2:.(2;.(2<.(39.O1.)))(29.$2:.(2;.(2<.=))(2=.$2:.))))))(13.Pk,$15.P,(13.(2.=R1.)(3:.R1.$3;.))(1>.$8.Vm,(3.(3.(35.Vst,O2.)$3<.)(3=.$3>.R2.))(3?.Vst,(40.Vst,(41.O2.(3.$3<.(3=.$3>.R2.))))))(1>.$8.Vm,(3.(35.Vst,O2.)+?>0.)(29.$2:.(42.#20.(43.#20.))(2=.$2:.)))))")
(* [comment removed for export] *).
Definition rmrep_areas : Prop :=
  forall a ar, (s_areas st) !! a = Some ar -> rarea_rep a ar.

(* [comment removed for export] *)
Definition rgroup_rep (b : aptr) (gh : ghdr) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "(44.(0.&8.)Lw8,(0.&8.)(13.(1>.$8.Vm,(35.Vst,O2.)(29.$2:.(32.(37.Vst,(45.O1.)))(29.$2:.(2?.R1.)(2=.$2:.))))(5.$15.(46.(4.&8.R1.)+1?.)(47.O1.))))")
(* [comment removed for export] *).
Definition rmrep_groups : Prop :=
  forall b gh, (s_groups st) !! b = Some gh -> rgroup_rep b gh.

(* [comment removed for export] *)
Definition rshadow_rep (rid : N) (r : region) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "(13.(48.$8.Vm,(49.O1.)(4:.(4;.O1.)))Po,$15.Pv,$15.P,(13.(2.=R2.)(3:.R2.(4:.(4;.O1.))))P,(5.$4<.(4=.(4>.Vst,O2.)R3.)(4?.R2.))(13.(50.$8.Vm,(3.(49.O1.)R4.)(29.(0.&8.)(30.R3.)(2=.(0.&8.))))(13.(2.=R3.)(3:.R3.+100.))))")
(* [comment removed for export] *).
Definition rmrep_shadow : Prop :=
  forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> rshadow_rep rid r.

(* [comment removed for export] *)
Definition rregions_wf : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "(13.(51.Vst,)(13.Prid,$:.Pr,$52.P,(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)R2.(58.Vst,))(59.$52.R1.))(13.(3:.=(49.R2.))(13.(5.$15.(5:.(49.R2.)+1000.)=)(13.(2.=(4;.R2.))(13.(2.(3.(49.R2.)(4:.(4;.R2.)))(19.VhRP,))(5.$6.(5;.$17.(49.R2.)(4:.(4;.R2.)))$5<.)))))(13.Prid1,$:.Pr1,$52.Prid2,$:.Pr2,$52.P,(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)R4.(58.Vst,))(59.$52.R3.))P,(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)R3.(58.Vst,))(59.$52.R2.))P,(5=.(5.$:.R6.R4.))(1.(2.(3.(49.R6.)(4:.(4;.R6.)))(5>.R4.))(2.(3.(49.R4.)(4:.(4;.R4.)))(5>.R6.)))(13.Pa,(14.$:.$15.)Par,$5?.P,(5.(<.$5?.)(53.(14.$:.$15.)$5?.(54.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$5?.)(57.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$5?.)R2.(65.Vst,))(59.$5?.R1.))(44.$52.Lr,$52.(13.(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)(66.$:.$15.R4.)(58.Vst,))(59.$52.R1.))(13.(2.=(67.$:.$15.R4.))(13.(2.(3.(67.$:.$15.R4.)+1000.)(4:.(4;.R1.)))(13.(5.$15.(5:.(67.$:.$15.R4.)+1000.)=)(13.(5=.(5.$68.(69.R1.)$6:.))(2.(5>.R1.)(3.(49.R1.)(67.$:.$15.R4.)))))))))Pb,(14.$:.$15.)Pgh,$6;.P,(5.(<.$6;.)(53.(14.$:.$15.)$6;.(54.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$6;.)(57.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$6;.)R2.(6<.Vst,))(59.$6;.R1.))(44.$52.Lr,$52.(13.(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)(66.$:.$15.R4.)(58.Vst,))(59.$52.R1.))(13.(5.$68.(69.R1.)$6:.)(13.(2.=(67.$:.$15.R4.))(13.(2.(3.(67.$:.$15.R4.)+10.)(4:.(4;.R1.)))(5.$15.(5:.(67.$:.$15.R4.)+10.)=))))))))))")
(* [comment removed for export] *).

Definition rmrep : Prop :=
  rregions_wf /\ rmrep_ctx /\ rmrep_globals /\ rmrep_areas /\ rmrep_groups /\ rmrep_shadow.

End MREP.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_ceil st m : rmrep st m -> s_ceil st = rceil.
Proof. (intros dd_H; ddestruct dd_H as ((P & _) & _)). exact (proj1 (proj2 P)). Qed.
#[using="Type"] Lemma rmrep_secret st m : rmrep st m -> s_secret st = rp_secret.
Proof. (intros dd_H; ddestruct dd_H as ((P & _) & _)). exact (proj1 (proj2 (proj2 P))). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rmrep_W (st : mstate) : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "(29.(14.$15.$15.)(6=.$15.$15.$1?.(3.$1?.+3:0.))(6>.(14.$:.$52.)(14.$15.$15.)Lkr,(14.$:.$52.)(6=.$15.$15.(49.(67.$:.$52.R1.))(3.(49.(67.$:.$52.R1.))(4:.(4;.(67.$:.$52.R1.)))))(6?.$:.$52.(54.$:.$55.$56.$52.)(70.$:.$55.$56.$52.)(58.O1.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_shadow_read : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Prid,$:.Pr,$52.Po,$15.Pv,$15.P,(72.R6.R5.)P,(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)R5.(58.R7.))(59.$52.R4.))P,(5.$68.(69.R5.)$6:.)P,(13.(2.=R5.)(3:.R5.(4:.(4;.R6.))))P,(5.$4<.(4=.(4>.R:.R8.)R6.)(4?.R5.))(13.(5.(<.(=.(0.&8.)))(73.$8.R:.(74.(3.(49.R8.)R7.))#1.)(59.(=.(0.&8.))(29.(0.&8.)(30.R6.)(2=.(0.&8.)))))(13.(2.=R6.)(3:.R6.+100.)))")
(* [comment removed for export] *).
Proof.
  (intros st m rid r o v dd_H; ddestruct dd_H as (WF & _ & _ & _ & _ & SH); intros Hr Hk Ho Hc).
  destruct (SH rid r Hr Hk) as [HW HB]. destruct (HB o v Ho Hc) as [Hm Hv]. split; [|exact Hv].
  rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read rsegs m _ [b8 v] 0 1 Hm); [lia|cbn; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_shadow_read2 : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Prid,$:.Pr,$52.Po,$15.Pv0,$15.Pv1,$15.P,(72.R7.R6.)P,(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)R6.(58.R8.))(59.$52.R5.))P,(5.$68.(69.R6.)$6:.)P,(2.=R6.)P,(2.(3.R7.+2.)(4:.(4;.R8.)))P,(5.$4<.(4=.(4>.R<.R:.)R8.)(4?.R7.))P,(5.$4<.(4=.(4>.R=.R;.)(3.R9.+1.))(4?.R7.))(13.(5.(<.(=.(0.&8.)))(73.$8.R=.(74.(3.(49.R;.)R:.))#2.)(59.(=.(0.&8.))(29.(0.&8.)(30.R9.)(29.(0.&8.)(30.R8.)(2=.(0.&8.))))))(13.(13.(2.=R9.)(3:.R9.+100.))(13.(2.=R8.)(3:.R8.+100.))))")
(* [comment removed for export] *).
Proof.
  intros st m rid r o v0 v1 MR Hr Hk Ho Ho2 H0 H1.
  dpose MR as (WF & _ & _ & _ & _ & SH).
  destruct (SH rid r Hr Hk) as [HW HB].
  destruct (HB o v0 ltac:(lia) H0) as [B0 V0]. destruct (HB (o + 1) v1 ltac:(lia) H1) as [B1 V1].
  split; [|split; assumption].
  assert (B : bytes_at rsegs m (r_base r + o) ([b8 v0] ++ [b8 v1])).
  { apply bytes_at_app. split; [exact B0|]. cbn [length Z.of_nat Pos.of_succ_nat].
    replace (r_base r + o + 1) with (r_base r + (o + 1)) by lia. exact B1. }
  rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read rsegs m _ _ 0 2 B); [lia|cbn; lia].
Qed.


(* [comment removed for export] *)
Definition rsize_classes_bytes : list byte := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "(29.(0.&8.)(75.&8.+1.(76.&8.+1.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+2.(76.&8.+2.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+3.(76.&8.+3.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+4.(76.&8.+4.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+5.(76.&8.+5.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+6.(76.&8.+6.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+7.(76.&8.+7.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+8.(76.&8.+8.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+9.(76.&8.+9.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+:.(76.&8.+:.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+<.(76.&8.+<.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+?.(76.&8.+?.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+12.(76.&8.+12.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+14.(76.&8.+14.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+19.(76.&8.+19.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+1?.(76.&8.+1?.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+24.(76.&8.+24.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+2:.(76.&8.+2:.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+32.(76.&8.+32.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+3?.(76.&8.+3?.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+48.(76.&8.+48.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+54.(76.&8.+54.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+66.(76.&8.+66.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+7?.(76.&8.+7?.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+92.(76.&8.+92.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+::.(76.&8.+::.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+<<.(76.&8.+<<.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+??.(76.&8.+??.))(29.(0.&8.)(75.&8.=(76.&8.=))(29.(0.&8.)(75.&8.+24.(76.&8.+24.))(29.(0.&8.)(75.&8.+1.(76.&8.+1.))(29.(0.&8.)(75.&8.+54.(76.&8.+54.))(29.(0.&8.)(75.&8.+1.(76.&8.+1.))(29.(0.&8.)(75.&8.+99.(76.&8.+99.))(29.(0.&8.)(75.&8.+1.(76.&8.+1.))(29.(0.&8.)(75.&8.+??.(76.&8.+??.))(29.(0.&8.)(75.&8.+1.(76.&8.+1.))(29.(0.&8.)(75.&8.+48.(76.&8.+48.))(29.(0.&8.)(75.&8.+2.(76.&8.+2.))(29.(0.&8.)(75.&8.+::.(76.&8.+::.))(29.(0.&8.)(75.&8.+2.(76.&8.+2.))(29.(0.&8.)(75.&8.+32.(76.&8.+32.))(29.(0.&8.)(75.&8.+3.(76.&8.+3.))(29.(0.&8.)(75.&8.+??.(76.&8.+??.))(29.(0.&8.)(75.&8.+3.(76.&8.+3.))(29.(0.&8.)(75.&8.+91.(76.&8.+91.))(29.(0.&8.)(75.&8.+4.(76.&8.+4.))(29.(0.&8.)(75.&8.+54.(76.&8.+54.))(29.(0.&8.)(75.&8.+5.(76.&8.+5.))(29.(0.&8.)(75.&8.+65.(76.&8.+65.))(29.(0.&8.)(75.&8.+6.(76.&8.+6.))(29.(0.&8.)(75.&8.+??.(76.&8.+??.))(29.(0.&8.)(75.&8.+7.(76.&8.+7.))(29.(0.&8.)(75.&8.+24.(76.&8.+24.))(29.(0.&8.)(75.&8.+9.(76.&8.+9.))(29.(0.&8.)(75.&8.+::.(76.&8.+::.))(29.(0.&8.)(75.&8.+:.(76.&8.+:.))(29.(0.&8.)(75.&8.+<<.(76.&8.+<<.))(29.(0.&8.)(75.&8.+<.(76.&8.+<.))(29.(0.&8.)(75.&8.+??.(76.&8.+??.))(29.(0.&8.)(75.&8.+?.(76.&8.+?.))(29.(0.&8.)(75.&8.+48.(76.&8.+48.))(29.(0.&8.)(75.&8.+12.(76.&8.+12.))(29.(0.&8.)(75.&8.+54.(76.&8.+54.))(29.(0.&8.)(75.&8.+15.(76.&8.+15.))(29.(0.&8.)(75.&8.+98.(76.&8.+98.))(29.(0.&8.)(75.&8.+19.(76.&8.+19.))(29.(0.&8.)(75.&8.+??.(76.&8.+??.))(29.(0.&8.)(75.&8.+1?.(76.&8.+1?.))(2=.(0.&8.))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rsize_classes_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m RSIZE_CLASSES [CB 96 rsize_classes_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold RSIZE_CLASSES; lia | unfold RSIZE_CLASSES; cbn; lia]. Qed.

#[using="Type"] Lemma rsize_classes_read : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pm,P,(0.&40.)(<.(0.&8.))Psc,$15.P,(77.$8.R2.)P,(13.(2.=R2.)(3:.R2.+30.))(5.(<.(=.(0.&8.)))(73.$8.R4.(74.(3.$78.(3=.+2.R3.)))#2.)(59.(=.(0.&8.))(79.(2<.(7:.R3.)))))")
(* [comment removed for export] *).
Proof.
  intros m sc MI Hsc.
  destruct (rsize_classes_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite (bytes_at_read rsegs m RSIZE_CLASSES rsize_classes_bytes (2 * sc) 2 B) by (cbn; lia).
  assert (Hn : exists n, sc = Z.of_nat n /\ (n < 48)%nat) by (exists (Z.to_nat sc); split; [lia|lia]).
  ddestruct Hn as (n & -> & Hn).
  replace (Z.to_nat (2 * Z.of_nat n)) with (2 * n)%nat by lia.
  Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
  do 48 (destruct n as [|n]; [solve_bytes |]). lia.
Qed.


#[using="Type"] Lemma rmrep_meta_chunk : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Pg,$60.P,(72.R3.R2.)P,(7;.R4.R2.)(1>.$8.R4.(35.R5.R3.)(3?.R5.(40.R5.R3.)))")
(* [comment removed for export] *).
Proof.
  (intros st m g MR dd_H; ddestruct dd_H as (a & ar & k & Ha & Hk & ->)).
  dpose MR as (WF & _ & _ & AR & _ & _).
  ddestruct (AR a ar Ha) as (_ & SL & _).
  ddestruct WF as (_ & _ & _ & WA & _). ddestruct (WA a ar Ha) as (r & Hr & _).
  rewrite conc_aadd by (rewrite Hr; eauto).
  replace (conc st a + (AREA_HDR + META_SIZE * k)) with (conc st a + AREA_HDR + META_SIZE * k) by lia. apply SL. exact Hk.
Qed.

#[using="Type"] Lemma rmrep_group_read : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Pb,$60.Pgh,$6;.P,(72.R4.R3.)P,(5.(<.$6;.)(53.$60.$6;.(54.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$6;.)(57.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$6;.)R3.(6<.R5.))(59.$6;.R2.))(13.(5.(<.(=.(0.&8.)))(73.$8.R5.(74.(35.R6.R4.))#8.)(59.(=.(0.&8.))(7<.(37.R6.(45.R3.)))))(44.(0.&8.)Lw8,(0.&8.)(13.(5.(<.(=.(0.&8.)))(73.$8.R6.(74.(3.(35.R7.R5.)+8.))#1.)(59.(=.(0.&8.))(29.(0.&8.)R1.(2=.(0.&8.)))))(5.$15.(46.(4.&8.R1.)+1?.)(47.R4.)))))")
(* [comment removed for export] *).
Proof.
  intros st m b gh MR Hb. dpose MR as (_ & _ & _ & _ & GR & _).
  ddestruct (GR b gh Hb) as (w8 & RW & Hw8). split.
  - rewrite <- (Z.add_0_r (conc st b)). apply (rw_cells_read_at rsegs m _ _ 0 (C8 (pw st (g_meta gh))) 8 _ RW); reflexivity.
  - exists w8. split; [|exact Hw8].
    apply (rw_cells_read_at rsegs m _ _ 8 (C1 w8) 1 _ RW); reflexivity.
Qed.

#[using="Type"] Lemma rmrep_area_check_read : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Pa,$60.Par,$5?.P,(72.R4.R3.)P,(5.(<.$5?.)(53.$60.$5?.(54.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$5?.)(57.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$5?.)R3.(65.R5.))(59.$5?.R2.))(5.(<.(=.(0.&8.)))(73.$8.R5.(74.(35.R6.R4.))#8.)(59.(=.(0.&8.))(7<.(2<.(36.R3.)))))")
(* [comment removed for export] *).
Proof.
  intros st m a ar MR Ha. dpose MR as (_ & _ & _ & AR & _ & _).
  ddestruct (AR a ar Ha) as (HD & _ & _).
  rewrite <- (Z.add_0_r (conc st a)). apply (rw_cells_read_at rsegs m _ _ 0 (C8 (wz (a_check ar))) 8 _ HD); reflexivity.
Qed.

#[using="Type"] Lemma rmrep_ctx_secret_read : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))P,(72.R2.R1.)(5.(<.(=.(0.&8.)))(73.$8.R2.(74.$1?.)#8.)(59.(=.(0.&8.))(7<.(2<.(7=.(7>.R3.))))))")
(* [comment removed for export] *).
Proof.
  (intros st m dd_H; ddestruct dd_H as (_ & (HD & _) & _)).
  rewrite <- (Z.add_0_r RCTX). apply (rw_cells_read_at rsegs m _ _ 0 (C8 (wz (c_secret (ctx st)))) 8 _ HD); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rreserved_disjoint : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pb,$15.Pn,$15.P,(5.$6.(5;.$17.R2.R1.)$5<.)(13.(1.(2.(3.R3.R2.)+10000.)(2.+1=000.R3.))(13.(1.(2.(3.R3.R2.)+1=000.)(2.+48000.R3.))(13.(1.(2.(3.R3.R2.)+48000.)(2.+4<000.R3.))(1.(2.(3.R3.R2.)+4<000.)(2.+7>000.R3.)))))")
(* [comment removed for export] *).
Proof.
  intros b n H. unfold ranges_free, ref_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.

#[using="Type"] Lemma rreserved_disjoint1 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
  b + n <= 0x10000 \/ 0x7e000 <= b.
Proof. intros b n H Hn. pose proof (rreserved_disjoint b n H). lia. Qed.

#[using="Type"] Lemma rwr_in_image : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Prid,$:.Pa,$15.Plen,$15.P,(7?.R4.)P,(80.R5.R4.R3.R2.)(13.(13.(1.(2.(3.R4.R3.)+48000.)(2.+4<000.R4.))(1.(2.(3.R4.R3.)+4<000.)(2.+7>000.R4.)))(13.(2.=R4.)(2.(3.R4.R3.)(81.+2.+40.))))")
(* [comment removed for export] *).
Proof.
  (intros st rid a len dd_H; ddestruct dd_H as (_ & WR & _); intros dd_H; ddestruct dd_H as (r & Hr & H1 & H2 & H3)).
  ddestruct (WR rid r Hr) as (B0 & _ & L0 & BC & RF). rceilb.
  destruct (rreserved_disjoint _ _ RF) as [_ D2]. pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r). lia.
Qed.

#[using="Type"] Lemma rwr_in_other : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Prid,$:.Pa,$15.Plen,$15.Prid',$:.Pr',$52.P,(7?.R6.)P,(80.R7.R6.R5.R4.)P,(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)R4.(58.R8.))(59.$52.R3.))P,(5=.(5.$:.R5.R8.))(1.(2.(3.R8.R7.)(5>.R5.))(2.(3.(49.R5.)(4:.(4;.R5.)))R8.))")
(* [comment removed for export] *).
Proof.
  (intros st rid a len rid' r' dd_H; ddestruct dd_H as (_ & _ & DJ & _); intros dd_H; ddestruct dd_H as (r & Hr & H1 & H2 & H3); intros Hr' Hne).
  destruct (DJ rid r rid' r' Hr Hr' ltac:(congruence)); lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rarea_lr_lo : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pa,(14.$:.$15.)Par,$5?.Pr,$52.P,(7?.R4.)P,(5.(<.$5?.)(53.(14.$:.$15.)$5?.(54.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$5?.)(57.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$5?.)R4.(65.R5.))(59.$5?.R3.))P,(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)(66.$:.$15.R5.)(58.R6.))(59.$52.R3.))(2.(5>.R4.)(3.(49.R4.)(67.$:.$15.R6.)))")
(* [comment removed for export] *).
Proof.
  (intros st a ar r dd_H; ddestruct dd_H as (_ & _ & _ & WA & _); intros Ha Hr). ddestruct (WA a ar Ha) as (r0 & Hr0 & _ & _ & _ & _ & LO).
  rewrite Hr in Hr0. inversion Hr0; subst. exact LO.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_ctx_ext : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pst',$71.Pm,P,(0.&40.)(<.(0.&8.))P,(5.$82.(7>.R2.)(7>.R3.))P,Pp,$60.(5.$15.(35.R4.R1.)(35.R5.R1.))P,(83.R5.R3.)(83.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros st st' m Hc Hconc H.
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  assert (E1 : ctx_head_cells st' = ctx_head_cells st) by (unfold ctx_head_cells; rewrite Hc, !Hpw; reflexivity).
  assert (E2 : actives st' = actives st). { unfold actives. apply map_ext. intros. unfold active. rewrite Hc. apply Hpw. }
  assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hc. reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hc. reflexivity. }
  assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hc. reflexivity. }
  assert (E6 : ctx_tail_cells st' = ctx_tail_cells st). { unfold ctx_tail_cells, brk_word. rewrite Hc. destruct (c_brk (ctx st)); rewrite ?Hconc; reflexivity. }
  unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.

#[using="Type"] Lemma rarea_rep_ext : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pst',$71.Pm,P,(0.&40.)(<.(0.&8.))Pa,$60.Par,$5?.P,Pp,$60.(5.$15.(35.R5.R1.)(35.R6.R1.))P,Pk,$15.P,(13.(2.=R1.)(3:.R1.$3;.))(5.$84.(40.R7.(41.R5.(3.$3<.(3=.$3>.R2.))))(40.R8.(41.R5.(3.$3<.(3=.$3>.R2.)))))P,(85.R7.R5.R4.R3.)(85.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  (intros st st' m a ar Hconc Hm dd_H; ddestruct dd_H as (H1 & H2 & H3)).
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  assert (Hmc : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
  unfold rarea_rep. rewrite !Hconc, Hpw. split; [exact H1|]. split; [|exact H3].
  intros k Hk. rewrite Hmc, Hm by exact Hk. apply H2. exact Hk.
Qed.

#[using="Type"] Lemma rgroup_rep_ext : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pst',$71.Pm,P,(0.&40.)(<.(0.&8.))Pb,$60.Pgh,$6;.P,Pp,$60.(5.$15.(35.R5.R1.)(35.R6.R1.))P,(86.R6.R4.R3.R2.)(86.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  (intros st st' m b gh Hconc dd_H; ddestruct dd_H as (w8 & H1 & H2)).
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  exists w8. rewrite Hconc, Hpw. auto.
Qed.

#[using="Type"] Lemma rshadow_rep_ext : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pst',$71.Pm,P,(0.&40.)(<.(0.&8.))Prid,$:.Pr,$52.P,(5.$87.(4>.R4.R2.)(4>.R5.R2.))P,(88.R6.R4.R3.R2.)(88.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof. intros st st' m rid r Hs [H1 H2]. split; [exact H1|]. intros o v Ho Hc. rewrite Hs in Hc. eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_ctx_frame : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Pa,$15.Pbs,(=.(0.&8.))Prid,$:.P,(7?.R5.)P,(80.R6.R2.R4.(89.(8:.(0.&8.)R3.)))P,(83.R7.R6.)(83.R8.(8;.R7.(74.R6.)R5.))")
(* [comment removed for export] *).
Proof.
  (intros st m a bs rid WF WI dd_H; ddestruct dd_H as (H1 & H2 & H3 & H4 & H5 & H6)).
  destruct (rwr_in_image st rid a _ WF WI) as (D & A0 & A1).
  assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
  assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
  assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
  assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
  unfold rmrep_ctx. unfold RCTX in *. split; [|split; [|split; [|split; [|split]]]].
  - apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
  - apply u64arr_frame; [exact H2|lia|lia|rewrite L1; cbn; lia].
  - apply u64arr_frame; [exact H3|lia|lia|rewrite L2; cbn; lia].
  - apply u8arr_frame; [exact H4|lia|lia|rewrite L3; cbn; lia].
  - apply u8arr_frame; [exact H5|lia|lia|rewrite L4; cbn; lia].
  - apply rw_cells_frame; [exact H6|lia|lia|cbn; lia].
Qed.

#[using="Type"] Lemma rmrep_globals_frame : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Pa,$15.Pbs,(=.(0.&8.))Prid,$:.P,(7?.R5.)P,(80.R6.R2.R4.(89.(8:.(0.&8.)R3.)))P,(8<.R6.)(8<.(8;.R7.(74.R6.)R5.))")
(* [comment removed for export] *).
Proof.
  (intros st m a bs rid WF WI dd_H; ddestruct dd_H as (H1 & H2 & H3 & H4 & H5)).
  destruct (rwr_in_image st rid a _ WF WI) as (D & A0 & A1).
  unfold rmrep_globals. unfold RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *. split; [|split; [|split; [|split]]].
  - apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H2|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H3|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H4|lia|lia|cbn; lia].
  - apply rw_cells_frame; [exact H5|lia|lia|cbn; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rarea_rep_frame : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Pa,$15.Pbs,(=.(0.&8.))Par0,$60.Par,$5?.P,(7?.R6.)P,(5.(<.$5?.)(53.$60.$5?.(54.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$5?.)(57.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$5?.)R3.(65.R7.))(59.$5?.R2.))P,(2.=R6.)P,(2.(3.R7.(89.(8:.(0.&8.)R6.)))(81.+2.+40.))P,(1.(2.(3.(35.R:.R6.)+1000.)R8.)(2.(3.R8.(89.(8:.(0.&8.)R7.)))(35.R:.R6.)))P,(85.R;.R:.R7.R6.)(85.R<.(8;.R;.(74.R:.)R9.)R8.R7.)")
(* [comment removed for export] *).
Proof.
  (intros st m a bs ar0 ar WF Har A0 A1 D dd_H; ddestruct dd_H as (H1 & H2 & H3)).
  unfold rarea_rep. split; [|split].
  - apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
  - intros k Hk. apply rw_cells_frame; [apply H2; exact Hk|lia|lia|]. unfold AREA_HDR, META_SIZE, NSLOTS in *. cbn. lia.
  - apply rw_cells_frame; [exact H3|lia|lia|cbn; lia].
Qed.

#[using="Type"] Lemma rgroup_rep_frame : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Pa,$15.Pbs,(=.(0.&8.))Pb,$60.Pgh,$6;.P,(2.=R4.)P,(2.(3.R5.(89.(8:.(0.&8.)R4.)))(81.+2.+40.))P,(1.(2.(3.(35.R8.R4.)+9.)R6.)(2.(3.R6.(89.(8:.(0.&8.)R5.)))(35.R8.R4.)))P,(86.R9.R8.R5.R4.)(86.R:.(8;.R9.(74.R8.)R7.)R6.R5.)")
(* [comment removed for export] *).
Proof.
  (intros st m a bs b gh A0 A1 D dd_H; ddestruct dd_H as (w8 & H1 & H2)). exists w8. split; [|exact H2].
  apply rw_cells_frame; [exact H1|lia|lia|cbn; lia].
Qed.

#[using="Type"] Lemma rshadow_rep_frame : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Pa,$15.Pbs,(=.(0.&8.))Prid,$:.Pr,$52.P,(2.=R4.)P,(2.(3.R5.(89.(8:.(0.&8.)R4.)))(81.+2.+40.))P,(1.(2.(3.(49.R3.)(4:.(4;.R3.)))R6.)(2.(3.R6.(89.(8:.(0.&8.)R5.)))(49.R3.)))P,(88.R9.R8.R5.R4.)(88.R:.(8;.R9.(74.R8.)R7.)R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros st m a bs rid r A0 A1 D [HW HB]. split; [apply wr_at_write; exact HW|].
  intros o v Ho Hc. destruct (HB o v Ho Hc) as [Hb Hv]. split; [|exact Hv].
  apply bytes_at_write_other; [exact Hb|lia|lia|cbn; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rarea_conc : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pa,(14.$:.$15.)Par,$5?.P,(7?.R3.)P,(5.(<.$5?.)(53.(14.$:.$15.)$5?.(54.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$5?.)(57.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$5?.)R3.(65.R4.))(59.$5?.R2.))(44.$52.Lr,$52.(13.(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)(66.$:.$15.R5.)(58.R6.))(59.$52.R1.))(13.(5.$15.(35.R6.R5.)(3.(49.R1.)(67.$:.$15.R5.)))(13.(2.=(67.$:.$15.R5.))(13.(2.(3.(67.$:.$15.R5.)+1000.)(4:.(4;.R1.)))(13.(5.$15.(5:.(67.$:.$15.R5.)+1000.)=)(13.(5=.(5.$68.(69.R1.)$6:.))(13.(3:.=(49.R1.))(13.(5.$15.(5:.(49.R1.)+1000.)=)(2.(3.(49.R1.)(4:.(4;.R1.)))(19.VhRP,)))))))))))")
(* [comment removed for export] *).
Proof.
  (intros st a ar dd_H; ddestruct dd_H as (_ & WR & _ & WA & _); intros Ha). ddestruct (WA a ar Ha) as (r & Hr & A0 & A1 & AL & NK & _).
  destruct (WR _ r Hr) as (B0 & BAL & _ & BC & _).
  exists r. rewrite (conc_region' st a r Hr). repeat split; auto.
Qed.

#[using="Type"] Lemma rgroup_conc : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pb,(14.$:.$15.)Pgh,$6;.P,(7?.R3.)P,(5.(<.$6;.)(53.(14.$:.$15.)$6;.(54.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$6;.)(57.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$6;.)R3.(6<.R4.))(59.$6;.R2.))(44.$52.Lr,$52.(13.(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)(66.$:.$15.R5.)(58.R6.))(59.$52.R1.))(13.(5.$15.(35.R6.R5.)(3.(49.R1.)(67.$:.$15.R5.)))(13.(5.$68.(69.R1.)$6:.)(13.(2.=(67.$:.$15.R5.))(13.(2.(3.(67.$:.$15.R5.)+10.)(4:.(4;.R1.)))(13.(5.$15.(5:.(67.$:.$15.R5.)+10.)=)(13.(3:.=(49.R1.))(2.(3.(49.R1.)(4:.(4;.R1.)))(19.VhRP,))))))))))")
(* [comment removed for export] *).
Proof.
  (intros st b gh dd_H; ddestruct dd_H as (_ & WR & _ & _ & WG); intros Hb). ddestruct (WG b gh Hb) as (r & Hr & K & B0 & B1 & AL).
  destruct (WR _ r Hr) as (R0 & _ & _ & RC & _).
  exists r. rewrite (conc_region' st b r Hr). repeat split; auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_wr8 : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Pp,(14.$:.$15.)Pv,$15.Pr,$52.P,(72.R5.R4.)P,(8=.R6.)P,(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)(66.$:.$15.R5.)(58.R7.))(59.$52.R3.))P,(5.$68.(69.R4.)$6:.)P,(13.(2.=(67.$:.$15.R7.))(3:.(67.$:.$15.R7.)(4:.(4;.R5.))))P,Pb,(14.$:.$15.)Pgh,$6;.P,(5.(<.$6;.)(53.(14.$:.$15.)$6;.(54.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$6;.)(57.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$6;.)R2.(6<.R<.))(59.$6;.R1.))P,(5.$:.(66.$:.$15.R3.)(66.$:.$15.R;.))(5=.(13.(2.(67.$:.$15.R4.)(67.$:.$15.R<.))(3:.(67.$:.$15.R<.)(3.(67.$:.$15.R4.)+9.))))P,(13.(2.=R8.)(3:.R8.+100.))(72.(8>.R:.R9.R<.)(8;.R;.(74.(3.(49.R8.)(67.$:.$15.R:.)))(29.(0.&8.)(30.R9.)(2=.(0.&8.)))))")
(* [comment removed for export] *).
Proof.
  intros st m p v r MR TK Hr Hk Ho Hgrp Hv.
  dpose MR as (WF & CX & GL & AR & GR & SH). pose proof (lr_lo_group r Hk) as LRr.
  assert (WI : wr_in st (fst p) (r_base r + snd p) (Z.of_nat (length [b8 v]))).
  { exists r. cbn. repeat split; auto; lia. }
  destruct (rwr_in_image st _ _ _ WF WI) as (D & A0 & A1). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat] in D, A1.
  assert (Hconc : forall q, conc (wr8 p v st) q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *) exact WF.
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|]. eapply rmrep_ctx_frame; eauto.
  - eapply rmrep_globals_frame; eauto.
  - intros a ar Ha. cbn in Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|].
    ddestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
    apply rarea_rep_frame; [exact WF|exact Ha|lia|cbn; lia| |exact (AR a ar Ha)]. rewrite Ca. cbn.
    destruct (N.eq_dec (fst a) (fst p)) as [E|NE].
    + rewrite E in Hra. rewrite Hr in Hra. inversion Hra; subst ra. congruence.
    + destruct (rwr_in_other st _ _ _ _ ra WF WI Hra NE); cbn in *; lia.
  - intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _). pose proof (lr_lo_group rb Kb) as LRb.
    apply rgroup_rep_frame; [lia|cbn; lia| |exact (GR b gh Hb)]. rewrite Cb. cbn.
    destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
    + rewrite E in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. specialize (Hgrp b gh Hb E). lia.
    + destruct (rwr_in_other st _ _ _ _ rb WF WI Hrb NE); cbn in *; lia.
  - intros rid r' Hr' Hk'. cbn in Hr'.
    destruct (N.eq_dec rid (fst p)) as [E|NE].
    + subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
      destruct (SH (fst p) r Hr Hk) as [HW HB]. split; [apply wr_at_write; exact HW|].
      intros o v' Ho' Hc.
      destruct (Z.eq_dec o (snd p)) as [->|NEo].
      * rewrite cell_read_wr8_same in Hc by assumption. inversion Hc; subst v'. split; [|lia].
        apply bytes_at_write_same; cbn; lia.
      * rewrite cell_read_wr8_other in Hc by exact NEo. destruct (HB o v' Ho' Hc) as [Hb Hv']. split; [|exact Hv'].
        apply bytes_at_write_other; [exact Hb|lia|cbn; lia|cbn; lia].
    + eapply rshadow_rep_ext; [apply get_shadow_wr8_other; exact NE|].
      pose proof (lr_lo_group r' Hk') as LR'.
      apply rshadow_rep_frame; [lia|cbn; lia| |exact (SH rid r' Hr' Hk')].
      destruct (rwr_in_other st _ _ _ _ r' WF WI Hr' NE); cbn in *; lia.
Qed.


#[using="Type"] Lemma rmrep_wr16 : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Pp,(14.$:.$15.)Pv,$15.Pr,$52.P,(72.R5.R4.)P,(8=.R6.)P,(5.(<.$52.)(53.$:.$52.(54.$:.$55.$56.$52.)(57.$:.$55.$56.$52.)(66.$:.$15.R5.)(58.R7.))(59.$52.R3.))P,(5.$68.(69.R4.)$6:.)P,(2.=(67.$:.$15.R7.))P,(2.(3.(67.$:.$15.R8.)+2.)(4:.(4;.R6.)))P,Pb,(14.$:.$15.)Pgh,$6;.P,(5.(<.$6;.)(53.(14.$:.$15.)$6;.(54.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$6;.)(57.$60.(61.$:.$55.$15.$62.)(63.$:.$55.$56.$15.$62.$64.)$6;.)R2.(6<.R=.))(59.$6;.R1.))P,(5.$:.(66.$:.$15.R3.)(66.$:.$15.R<.))(1.(2.(3.(67.$:.$15.R=.)+2.)(67.$:.$15.R4.))(2.(3.(67.$:.$15.R4.)+9.)(67.$:.$15.R=.)))P,(13.(2.=R9.)(3:.R9.+10000.))(72.(8?.R;.R:.R=.)(8;.R<.(74.(3.(49.R9.)(67.$:.$15.R;.)))(79.(2<.R:.))))")
(* [comment removed for export] *).
Proof.
  intros st m p v r MR TK Hr Hk Ho Ho2 Hg Hv.
  rewrite le2_split by lia.
  change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 (v / 256)])
    with (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p) + 1) [b8 (v / 256)]).
  rewrite wa_succ. unfold wr16. rewrite (wr8_mod st p v).
  replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (unfold aadd; cbn; lia).
  replace (Z.shiftr v 8) with (v / 256) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
  assert (Hd : 0 <= v / 256 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  apply (rmrep_wr8 (wr8 p (v mod 256) st) _ (aadd p 1) (v / 256) r).
  - apply rmrep_wr8; auto; [lia|]. intros b gh Hb E. specialize (Hg b gh Hb E). lia.
  - apply ticks_ok_wr8. exact TK.
  - cbn. exact Hr.
  - exact Hk.
  - cbn. lia.
  - intros b gh Hb E. cbn in Hb, E |- *. specialize (Hg b gh Hb E). lia.
  - exact Hd.
Qed.



(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_meta_store4 : forall st m g (f : meta -> meta) (off : nat) v,
  rmrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
  (forall mr, cell_at (meta_cells st mr) off = Some (C4 (wz (match off with 24%nat => m_avail mr | _ => m_freed mr end)))) ->
  (forall mr, cell_upd (meta_cells st mr) off (C4 (wz v)) = meta_cells st (f mr)) ->
  (off = 24%nat \/ off = 28%nat) ->
  rmrep (upd_meta g f st) (write_to_mem m (wa (conc st g + Z.of_nat off)) (le4 (wz v))).
Proof.
  (intros st m g f off v MR dd_H; ddestruct dd_H as (a & ar & k & Ha & Hk & Eg); intros Hv Hat Hupd Hoff).
  dpose MR as (WF & CX & GL & AR & GR & SH).
  ddestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). rceilb.
  pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  assert (WI : wr_in st (fst a) (conc st g + Z.of_nat off) (Z.of_nat (length (le4 (wz v))))).
  { exists ra. rewrite length_le4. cbn [Z.of_nat Pos.of_succ_nat Pos.to_nat]. split; [exact Hra|]. rewrite HG, Ca. destruct Hoff; subst; cbn; lia. }
  assert (Hconc : forall q, conc (upd_meta g f st) q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - exact WF.
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|]. eapply rmrep_ctx_frame; eauto.
  - eapply rmrep_globals_frame; eauto.
  - intros a' ar' Ha'. cbn in Ha'.
    assert (Hpw : forall q, pw (upd_meta g f st) q = pw st q) by (intros [q|]; reflexivity).
    assert (Hmc : forall mr, meta_cells (upd_meta g f st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
    ddestruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
    pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra') as LRa'.
    destruct (decide (a' = a)) as [->|NEa].
    + (* [comment removed for export] *)
      rewrite Ha in Ha'. inversion Ha'; subst ar'.
      ddestruct (AR a ar Ha) as (HD & SL & PD). unfold rarea_rep. rewrite !Hconc, Hpw. rewrite length_le4 in *.
      split; [|split].
      * apply rw_cells_frame; [exact HD|lia|rewrite length_le4; cbn in *; lia|]. rewrite length_le4, HG. cbn. destruct Hoff; subst; cbn; lia.
      * intros k' Hk'. rewrite Hmc, get_meta_rec_upd.
        destruct (Z.eq_dec k' k) as [->|NEk].
        -- rewrite <- Eg, aptr_eqb_refl.
           replace (conc st g + Z.of_nat off) with (conc st a + 24 + 40 * k + Z.of_nat off) by (rewrite HG; lia).
           rewrite <- Hupd. unfold le4. change (Z_to_le_bytes 4 (bv_unsigned (wz v))) with (cbytes (C4 (wz v))).
           eapply rw_cells_write; [ | apply Hat | reflexivity | exact I].
           rewrite Eg. replace (24 + 40 * k) with (AREA_HDR + META_SIZE * k) by reflexivity. apply SL. unfold NSLOTS. lia.
        -- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
           2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
           apply rw_cells_frame; [apply SL; lia|lia|rewrite length_le4; cbn in *; lia|].
           rewrite length_le4, HG. cbn [cells_size meta_cells csize Nat.add length]. unfold AREA_HDR, META_SIZE. destruct Hoff; subst; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; nia.
      * apply rw_cells_frame; [exact PD|lia|rewrite length_le4; cbn in *; lia|]. rewrite length_le4, HG. cbn. destruct Hoff; subst; cbn; lia.
    + (* [comment removed for export] *)
      assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
        assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
        Z.div_mod_to_equations. nia. }
      eapply rarea_rep_ext; [exact Hconc| |].
      { intros k0 Hk0. rewrite get_meta_rec_upd.
        replace (aptr_eqb (aadd a' (AREA_HDR + META_SIZE * k0)) g) with false; [reflexivity|].
        symmetry. rewrite Eg. unfold aptr_eqb, aadd, AREA_HDR, META_SIZE. cbn [fst snd].
        destruct PG as [NE|[E PG]].
        - rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
        - rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. unfold NSLOTS in *. lia. }
      apply rarea_rep_frame; [exact WF|exact Ha'|lia|rewrite length_le4; cbn in *; lia| |exact (AR a' ar' Ha')].
      rewrite length_le4, Ca', HG, Ca. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat].
      destruct PG as [NE|[E PG]].
      * destruct (rwr_in_other st _ _ _ _ ra' WF WI Hra' NE); rewrite ?HG, ?Ca in *; cbn in *; lia.
      * rewrite E, Hra in Hra'. inversion Hra'; subst ra'. destruct Hoff; subst; cbn; lia.
  - intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _). pose proof (lr_lo_group rb Kb) as LRb.
    apply rgroup_rep_frame; [lia|rewrite length_le4; cbn in *; lia| |exact (GR b gh Hb)]. rewrite Cb, length_le4. cbn.
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
    destruct (rwr_in_other st _ _ _ _ rb WF WI Hrb NE); cbn in *; lia.
  - intros rid r' Hr' Hk'. cbn in Hr'.
    eapply rshadow_rep_ext; [reflexivity|]. pose proof (lr_lo_group r' Hk') as LR'.
    apply rshadow_rep_frame; [lia|rewrite length_le4; cbn in *; lia| |exact (SH rid r' Hr' Hk')]. rewrite length_le4. cbn.
    assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    destruct (rwr_in_other st _ _ _ _ r' WF WI Hr' NE); cbn in *; lia.
Qed.

#[using="Type"] Lemma rmrep_meta_set_avail : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Pg,$60.Pv,$15.P,(72.R4.R3.)P,(7;.R5.R3.)P,(13.(2.=R3.)(3:.R3.(81.+2.+20.)))(72.(90.R5.(91.R4.)R7.)(8;.R6.(74.(3.(35.R7.R5.)+18.))(92.(2<.R4.))))")
(* [comment removed for export] *).
Proof.
  intros. change 24 with (Z.of_nat 24).
  apply (rmrep_meta_store4 st m g (m_set_avail v) 24%nat v); auto; intros; reflexivity.
Qed.



#[using="Type"] Lemma rmrep_set_active : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Psc,$15.Pv,$93.P,(72.R4.R3.)P,(13.(2.=R3.)(3:.R3.+30.))(72.(94.R4.R3.R6.)(8;.R5.(74.(3.(3.$1?.+50.)(3=.+8.R4.)))(7<.(37.R6.R3.))))")
(* [comment removed for export] *).
Proof.
  intros st m sc v MR Hsc. dpose MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & (G1 & G2 & G3 & G4 & G5) & AR & GR & SH).
  assert (Hconc : forall q, conc (set_active sc v st) q = conc st q) by (intros; reflexivity).
  assert (Hpw : forall q, pw (set_active sc v st) q = pw st q) by (intros [q|]; reflexivity).
  assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
  pose proof (length_le8 (pw st v)) as L8.
  unfold RCTX in *.
  split; [|split; [|split; [|split; [|split]]]].
  - exact WF.
  - unfold rmrep_ctx.
    change (ctx_head_cells (set_active sc v st)) with (ctx_head_cells st).
    change (usages (set_active sc v st)) with (usages st).
    change (unmap_seqs (set_active sc v st)) with (unmap_seqs st).
    change (bouncess (set_active sc v st)) with (bouncess st).
    assert (E6 : ctx_tail_cells (set_active sc v st) = ctx_tail_cells st).
    { unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx set_active upd_ctx c_seq c_brk set_active_map]. destruct (c_brk (s_ctx st)); reflexivity. }
    rewrite E6, actives_set_active by lia. unfold RCTX.
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    split; [|split; [|split; [|split; [|split]]]].
    + apply rw_cells_frame; [exact C1|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + replace (512968 + 80 + 8 * sc) with ((512968 + 80) + 8 * sc) by lia. apply u64arr_write; [exact C2| rewrite L1; lia].
    + apply u64arr_frame; [exact C3|lia|rewrite L8; lia|rewrite L8, L2; lia].
    + apply u8arr_frame; [exact C4|lia|rewrite L8; lia|rewrite L8, L3; lia].
    + apply u8arr_frame; [exact C5|lia|rewrite L8; lia|rewrite L8, L4; lia].
    + apply rw_cells_frame; [exact C6|lia|rewrite L8; lia|rewrite L8; cbn; lia].
  - unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *. split; [|split; [|split; [|split]]].
    + apply rw_cells_frame; [exact G1|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + apply rw_cells_frame; [exact G2|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + apply rw_cells_frame; [exact G3|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + apply rw_cells_frame; [exact G4|lia|rewrite L8; lia|rewrite L8; cbn; lia].
    + apply rw_cells_frame; [exact G5|lia|rewrite L8; lia|rewrite L8; cbn; lia].
  - intros a ar Ha. cbn in Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|].
    ddestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
    ddestruct WF as (_ & WR & _). destruct (WR _ ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    apply rarea_rep_frame; [exact (proj1 MR)|exact Ha|lia|rewrite L8; lia| |exact (AR a ar Ha)].
    rewrite L8, Ca. pose proof (round_up_pg_ge (r_len ra)). cbn. lia.
  - intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
    ddestruct WF as (_ & WR & _). destruct (WR _ rb Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    apply rgroup_rep_frame; [lia|rewrite L8; lia| |exact (GR b gh Hb)]. rewrite L8, Cb. cbn. lia.
  - intros rid r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_ext; [reflexivity|].
    ddestruct WF as (_ & WR & _). destruct (WR _ r' Hr') as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    apply rshadow_rep_frame; [lia|rewrite L8; lia| |exact (SH rid r' Hr' Hk')]. rewrite L8. cbn. lia.
Qed.


#[using="Type"] Lemma rshadow_rep_le : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pst',$71.Pm,P,(0.&40.)(<.(0.&8.))Prid,$:.Pr,$52.P,(95.(4>.R5.R2.)(4>.R4.R2.))P,(88.R6.R4.R3.R2.)(88.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof. intros st st' m rid r [_ HL] [HW HB]. split; [exact HW|]. intros o v Ho Hc. apply HB; auto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_upd_shadow : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pst,$71.Pm,P,(0.&40.)(<.(0.&8.))Prid,$:.Pf,Px,$87.$87.P,(72.R4.R3.)P,(8=.R5.)P,(13.(95.(4>.R6.R4.)A1.R3.(4>.R6.R4.))(96.A1.R3.(4>.R6.R4.)(97.R6.)))(13.(72.(98.R5.R4.R7.)R6.)(8=.(98.R5.R4.R7.)))")
(* [comment removed for export] *).
Proof.
  intros st m rid f MR TK [HL HT]. dpose MR as (WF & CX & GL & AR & GR & SH).
  assert (Hconc : forall q, conc (upd_shadow rid f st) q = conc st q) by (intros; reflexivity).
  assert (GS : forall rid', get_shadow (upd_shadow rid f st) rid' = if N.eqb rid' rid then f (get_shadow st rid) else get_shadow st rid').
  { intros rid'. rewrite (get_shadow_unfold (upd_shadow rid f st)). unfold upd_shadow, set_shadow. cbn [s_shadow].
    destruct (N.eqb_spec rid' rid); [subst; rewrite lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity]. }
  split.
  - split; [exact WF|]. split; [eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX]|]. split; [exact GL|].
    split; [intros a ar Ha; eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)]|].
    split; [intros b gh Hb; eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)]|].
    intros rid' r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_le; [|exact (SH rid' r' Hr' Hk')].
    rewrite GS. destruct (N.eqb_spec rid' rid); [subst; exact HL| apply shadow_le_refl].
  - destruct TK as [T1 T2]. destruct HT as [HT1 HT2]. split.
    + intros rid' sh u hl ch Hs Hu Hin. cbn [s_tick upd_shadow set_shadow] in *.
      pose proof (GS rid') as G. rewrite (get_shadow_unfold (upd_shadow rid f st)) in G. cbn [s_shadow upd_shadow set_shadow] in G. rewrite Hs in G. cbn in G.
      destruct (N.eqb_spec rid' rid); [subst sh; eapply HT1; eauto|].
      unfold get_shadow in G. destruct (s_shadow st !! rid') eqn:E; cbn in G; [subst; eapply T1; eauto| subst; rewrite lookup_empty in Hu; discriminate].
    + intros rid' sh pg t Hs Hp. cbn [s_tick upd_shadow set_shadow] in *.
      pose proof (GS rid') as G. rewrite (get_shadow_unfold (upd_shadow rid f st)) in G. cbn [s_shadow upd_shadow set_shadow] in G. rewrite Hs in G. cbn in G.
      destruct (N.eqb_spec rid' rid); [subst sh; eapply HT2; eauto|].
      unfold get_shadow in G. destruct (s_shadow st !! rid') eqn:E; cbn in G; [subst; eapply T2; eauto| subst; rewrite lookup_empty in Hp; discriminate].
Qed.

#[using="Type"] Lemma rmrep_havoc : forall st m p n, rmrep st m -> ticks_ok st -> rmrep (havoc p n st) m /\ ticks_ok (havoc p n st).
Proof.
  intros st m p n MR TK. unfold havoc. destruct (n <=? 0); [auto|].
  apply rmrep_upd_shadow; [exact MR|exact TK|].
  pose proof (sh_ticks_of_ticks_ok st (fst p) TK) as T0.
  set (sh := get_shadow st (fst p)) in *. destruct sh as [cells hav havp]. cbn [r_cells r_hav r_havp].
  destruct ((snd p + 4095) / 4096 <? (snd p + n) / 4096).
  - destruct (havoc_pages_le cells hav havp ((snd p + 4095) / 4096) ((snd p + n) / 4096) (s_tick st) T0) as [L1 T1].
    set (hav1 := if snd p <? (snd p + 4095) / 4096 * 4096 then havoc_units (snd p) ((snd p + 4095) / 4096 * 4096) (s_tick st) hav else hav).
    assert (S1 : shadow_le (mkShadow cells hav havp) (mkShadow cells hav1 havp) /\ sh_ticks (mkShadow cells hav1 havp) (s_tick st)).
    { subst hav1. destruct (snd p <? _); [apply havoc_units_le; exact T0| split; [apply shadow_le_refl|exact T0]]. }
    destruct S1 as [L2 T2].
    set (hav2 := if (snd p + n) / 4096 * 4096 <? snd p + n then havoc_units ((snd p + n) / 4096 * 4096) (snd p + n) (s_tick st) hav1 else hav1).
    assert (S2 : shadow_le (mkShadow cells hav1 havp) (mkShadow cells hav2 havp) /\ sh_ticks (mkShadow cells hav2 havp) (s_tick st)).
    { subst hav2. destruct (_ <? snd p + n); [apply havoc_units_le; exact T2| split; [apply shadow_le_refl|exact T2]]. }
    destruct S2 as [L3 T3].
    destruct (havoc_pages_le cells hav2 havp ((snd p + 4095) / 4096) ((snd p + n) / 4096) (s_tick st) T3) as [L4 T4].
    split; [|exact T4]. eapply shadow_le_trans; [exact L2|]. eapply shadow_le_trans; [exact L3|exact L4].
  - apply havoc_units_le. exact T0.
Qed.

#[using="Type"] Lemma rmrep_hdr_havoc : forall st m b, rmrep st m -> ticks_ok st -> rmrep (hdr_havoc b st) m /\ ticks_ok (hdr_havoc b st).
Proof.
  intros st m b MR TK. unfold hdr_havoc.
  apply rmrep_upd_shadow; [exact MR|exact TK|].
  pose proof (sh_ticks_of_ticks_ok st (fst b) TK) as T0.
  set (sh := get_shadow st (fst b)) in *. destruct sh as [cells hav havp]. cbn [r_cells r_hav r_havp].
  apply hav_unit_step. exact T0.
Qed.


(* [comment removed for export] *)

#[using="Type"] Lemma rmrep_transport_high : forall st m m' W,
  rmrep st m -> munch W m m' -> wmono rsegs m m' -> rW_high W -> rmrep st m'.
Proof.
  (intros st m m' W dd_H; ddestruct dd_H as (WF & CX & GL & AR & GR & SH); intros MU WM HW).
  dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  assert (D : forall a n, a + n <= rceil -> disjoint_from W a n) by (intros; eapply rW_high_disjoint; eassumption).
  assert (TC : forall A cs, rw_cells rsegs m A cs -> A + Z.of_nat (cells_size cs) <= rceil -> rw_cells rsegs m' A cs).
  { intros A cs H HB. eapply rw_cells_transport; eauto. }
  rceilb.
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - (* [comment removed for export] *) ddestruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 | unfold RCTX; cbn; lia].
    + eapply u64arr_transport; eauto. apply D. unfold actives. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
    + eapply u64arr_transport; eauto. apply D. unfold usages. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
    + eapply u8arr_transport; eauto. apply D. unfold unmap_seqs. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
    + eapply u8arr_transport; eauto. apply D. unfold bouncess. rewrite map_length, seq_length. unfold RCTX; cbn; lia.
    + apply TC; [exact C6 | unfold RCTX; cbn; lia].
  - (* [comment removed for export] *) ddestruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
    + apply TC; [exact G1 | unfold RMLOCK; cbn; lia].
    + apply TC; [exact G2 | unfold RNEED_LOCKS; cbn; lia].
    + apply TC; [exact G3 | unfold RPAGE_SIZE; cbn; lia].
    + apply TC; [exact G4 | unfold RGOT_SSP; cbn; lia].
    + apply TC; [exact G5 | unfold RSSP_GUARD; cbn; lia].
  - (* [comment removed for export] *) intros a ar Ha. ddestruct (AR a ar Ha) as (A1 & A2 & A3).
    ddestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). rceilb.
    split; [|split].
    + apply TC; [exact A1 | cbn; lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
    + apply TC; [exact A3 | cbn; lia].
  - (* [comment removed for export] *) intros b gh Hb. ddestruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Sb0 & Sb1 & SbL & RB0 & RBAL & RBC).
    apply TC; [exact R | cbn; lia].
  - (* [comment removed for export] *) intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
    ddestruct (WR rid r Hr) as (B0 & BAL & L0 & BC & _).
    split.
    + eapply wr_at_transport; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply bytes_at_transport; eauto. apply D. cbn. lia.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_set_tick : forall st m t, rmrep st m -> rmrep (set_tick t st) m.
Proof.
  (intros st m t dd_H; ddestruct dd_H as (WF & CX & GL & AR & GR & SH)).
  split; [exact WF|]. split; [|split; [exact GL|split; [|split]]].
  - eapply rmrep_ctx_ext; [reflexivity | intros; reflexivity | exact CX].
  - intros a ar Ha. eapply rarea_rep_ext; [intros; reflexivity | intros; reflexivity | exact (AR a ar Ha)].
  - intros b gh Hb. eapply rgroup_rep_ext; [intros; reflexivity | exact (GR b gh Hb)].
  - intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity | exact (SH rid r Hr Hk)].
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma rwr_at_bytes_exist : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocRep ()) "Pm,P,(0.&40.)(<.(0.&8.))Pa,$15.Pn,$15.P,(48.$8.R3.R2.R1.)P,(2.=R2.)P,(1.(2.(3.R4.R3.)+10000.)(2.+7>000.R4.))(44.(=.(0.&8.))Lbs,(=.(0.&8.))(13.(5.$99.(8:.(0.&8.)R1.)(9:.R5.))(50.$8.R7.R6.R1.)))")
(* [comment removed for export] *).
Proof.
  (intros m a n dd_H; ddestruct dd_H as (A0 & An & W); intros Hn Himg).
  assert (G : forall i, 0 <= i < n -> exists b, mrd rsegs m (wa (a + i)) = Some b).
  { intros i Hi. specialize (W i Hi). rewrite ref_wview_overlay in W by (rewrite wa_unsigned by lia; lia).
    rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia).
    destruct (m (wa (a + i))) as [b|]; [exists b; reflexivity| exfalso; apply W; reflexivity]. }
  (* [comment removed for export] *)
  assert (REC : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\ bytes_at rsegs m (a + (n - Z.of_nat k)) bs).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - ddestruct (IH ltac:(lia)) as (bs & L & B). destruct (G (n - Z.of_nat (S k)) ltac:(lia)) as (b & Hb).
      exists (b :: bs). split; [cbn; lia|].
      change (b :: bs) with ([b] ++ bs). apply bytes_at_app. split.
      + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn. rewrite Z.add_0_r. exact Hb.
      + cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. replace (a + (n - Z.of_nat (S k)) + 1) with (a + (n - Z.of_nat k)) by lia. exact B. }
  ddestruct (REC (Z.to_nat n) ltac:(lia)) as (bs & L & B). exists bs. split; [exact L|].
  replace (a + (n - Z.of_nat (Z.to_nat n))) with a in B by lia. exact B.
Qed.

(* [comment removed for export] *)

End RP_1.
