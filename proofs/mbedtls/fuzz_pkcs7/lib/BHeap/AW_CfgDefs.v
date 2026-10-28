(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison AW_DepotCfg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined AW_Refill AW_GetFrom AW_Populate AW_Populate2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_CfgDefs () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DECORATE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_SEALED2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_DYING"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DYING"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "ARUN_1.mwc_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_INTERVAL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_PREMAPPED"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "ARUN_1.pop_statics"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.app"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.sub_fp"].

Section ARUN_1. Context {hAR : arun}.
Definition mwc_statics (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CfgDefs ()) "(0.(1.$2.O1.$3.(4.$5.(6.(7.&40.$8.))(9.$5.)))(0.(1.$2.O1.$8.(4.$5.(6.(7.&40.+1000.))(9.$5.)))(0.(1.$2.O1.$:.(4.$5.(6.(7.&40.$;.))(9.$5.)))(0.(1.$2.O1.$<.(4.$5.(=.(7.&8.=))(9.$5.)))(0.(1.$2.O1.$>.(4.$5.(6.(7.&40.=))(9.$5.)))(0.(1.$2.O1.$?.(4.$5.(6.(7.&40.+1.))(9.$5.)))(0.(1.$2.O1.$10.(4.$5.(6.(7.&40.$11.))(9.$5.)))(1.$2.O1.$11.(4.$5.(12.(7.&40.=))(9.$5.))))))))))")
(* [comment removed for export] *).
#[using="Type"] Lemma mwc_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_CfgDefs ()) "PW,(13.$14.)Pm,P,(15.&40.)(16.(15.&8.))Pm',P,(15.&40.)(16.(15.&8.))P,(17.R2.)P,(18.R4.R3.R2.)P,PA,$19.Pn,$19.P,(0.(1:.+10000.R2.)(1:.(1;.R2.R1.)+1=;8<8.))(1<.R8.R3.R2.)(17.R4.)")
(* [comment removed for export] *).
Proof.
  (intros W m m' dd_H; ddestruct dd_H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8); intros MU DJ). unfold mwc_statics.
  unfold A_GOT_PAGESZ, A_PAGESZ_CELL, A_GOT_CFLAGS, A_DECORATE, A_MMAP_LIMIT, A_GOT_SEALED2, A_GOT_DYING, A_DYING in *.
  repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.

(* [comment removed for export] *)
Definition pop_statics (m : mem) (SB : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CfgDefs ()) "(0.(1.$2.O2.$1=.(4.$5.(12.(7.&40.+????????.))(9.$5.)))(0.(1.$2.O2.$1>.(4.$5.(=.(7.&8.=))(9.$5.)))(1.$2.O2.(1;.$1?.+20.)(4.$5.(6.(7.&40.O1.))(9.$5.)))))")
(* [comment removed for export] *).
#[using="Type"] Lemma pop_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_CfgDefs ()) "PW,(13.$14.)Pm,P,(15.&40.)(16.(15.&8.))Pm',P,(15.&40.)(16.(15.&8.))PSB,$19.P,(20.R3.R1.)P,(18.R5.R4.R3.)P,PA,$19.Pn,$19.P,(0.(1:.+10000.R2.)(1:.(1;.R2.R1.)+1=;8<8.))(1<.R9.R3.R2.)(20.R5.R4.)")
(* [comment removed for export] *).
Proof.
  (intros W m m' SB dd_H; ddestruct dd_H as (S1 & S2 & S3); intros MU DJ). unfold pop_statics. unfold A_INTERVAL, A_PREMAPPED, A_INSTANCE in *.
  repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma no_ro_above : ltac2:(CDefT.buildp (gd_tbl_AW_CfgDefs ()) "Pa,$19.Pn,$19.P,(1:.+?1000.R2.)Px,(15.&40.)P,(0.(1:.R4.(21.&40.R1.))(22.(21.&40.R1.)(1;.R4.R3.)))(23.$24.(25.$2.R2.)$26.)")
(* [comment removed for export] *).
Proof.
  intros a n Ha x Hx. destruct (ro_addr asegs x) eqn:E; [| reflexivity].
  pose proof (asegs_ro_lt x E). lia.
Qed.

#[using="Type"] Lemma u32arr_app : ltac2:(CDefT.buildp (gd_tbl_AW_CfgDefs ()) "Pm,P,(15.&40.)(16.(15.&8.))PA,$19.Pl1,(13.(15.&40.))Pl2,(13.(15.&40.))(27.(28.$2.R4.R3.(29.(15.&40.)R2.R1.))(0.(28.$2.R4.R3.R2.)(28.$2.R4.(1;.R3.(2:.+4.(2;.(2<.(15.&40.)R2.))))R1.)))")
(* [comment removed for export] *).
Proof.
  intros m A l1 l2. unfold u32arr. rewrite u32s_app, app_length.
  pose proof (bytes_at_app asegs m A (u32s l1) (u32s l2)) as BA. rewrite u32s_length in BA.
  replace (A + Z.of_nat (4 * length l1)) with (A + 4 * Z.of_nat (length l1)) in BA by lia.
  replace (4 * Z.of_nat (length l1 + length l2)) with (4 * Z.of_nat (length l1) + 4 * Z.of_nat (length l2)) by lia.
  rewrite (wr_at_app asegs m A (4 * Z.of_nat (length l1)) (4 * Z.of_nat (length l2))) by lia.
  tauto.
Qed.
#[using="Type"] Lemma u32s_zeros : forall n, u32s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (4 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat u32s flat_map]. change (flat_map le4 (repeat (Z_to_bv 64 0) n)) with (u32s (repeat (Z_to_bv 64 0) n)).
  rewrite IH. replace (4 * S n)%nat with (S (S (S (S (4 * n)))))%nat by lia. reflexivity.
Qed.
#[using="Type"] Lemma u32arr_zeros : ltac2:(CDefT.buildp (gd_tbl_AW_CfgDefs ()) "Pm,P,(15.&40.)(16.(15.&8.))PA,$19.Pn,$19.P,(1:.=R1.)P,(2=.$2.R4.R3.(4.$5.(2>.(2?.(2:.+4.R2.))(30.(15.&8.)(7.&8.=)(2?.(2:.+4.R2.))))(9.$5.)))(28.$2.R5.R4.(30.(15.&40.)(7.&40.=)(2?.R3.)))")
(* [comment removed for export] *).
Proof.
  intros m A n Hn RC. pose proof (u8arr_of_rw_cells asegs m A _ _ RC) as [HB HW].
  split. { rewrite u32s_zeros. replace (4 * Z.to_nat n)%nat with (Z.to_nat (4 * n)) by lia. exact HB. }
  rewrite repeat_length in HW |- *. replace (4 * Z.of_nat (Z.to_nat n)) with (Z.of_nat (Z.to_nat (4 * n))) by lia. exact HW.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma outside_In : forall W x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
  induction W as [|[a b] W IH]; intros x lo hi Ho Hi; [destruct Hi|].
  cbn in Ho. destruct Ho as [H1 H2]. destruct Hi as [E|Hi]; [injection E; intros; subst; exact H1| exact (IH _ _ _ H2 Hi)].
Qed.
#[using="Type"] Lemma sub_fp_nil : forall W', sub_fp [] W'.
Proof. intros W' x _. exact I. Qed.
#[using="Type"] Lemma sub_fp_cons : ltac2:(CDefT.buildp (gd_tbl_AW_CfgDefs ()) "Plo,$19.Phi,$19.PW,(13.$14.)PW',(13.(31.$19.$19.))P,(32.$19.Llo',$19.(32.$19.Lhi',$19.(0.(33.(31.$19.$19.)(34.$19.$19.R2.R1.)R3.)(0.(1:.R2.R6.)(1:.R5.R1.)))))P,(35.R3.R2.)(35.(4.(31.$19.$19.)(34.$19.$19.R6.R5.)R4.)R3.)")
(* [comment removed for export] *).
Proof.
  (intros lo hi W W' dd_H; ddestruct dd_H as (lo' & hi' & Hi & H1 & H2); intros HS x Ho). cbn. split; [| exact (HS x Ho)].
  pose proof (outside_In W' x lo' hi' Ho Hi). lia.
Qed.
End ARUN_1.
Ltac find_iv W' pos :=
  lazymatch W' with
  | (?a, ?b) :: ?rest => first [ exists a, b; split; [pos; left; reflexivity | split; lia] | find_iv rest ltac:(pos; right) ]
  end.
Ltac solve_sub_fp :=
  repeat (apply sub_fp_cons; [ lazymatch goal with |- exists lo' hi', In _ ?W' /\ _ => find_iv W' ltac:(idtac) end | ]);
  apply sub_fp_nil.


Section ARUN_2. Context {hAR : arun}.
Definition unit_if (b : option bool) : Z := match b with Some true => 2^18 | _ => 0 end.

#[using="Type"] Lemma max_cached_fits : forall c, 1 <= c <= 31 -> class_size c * (max_count c / 2) <= 65536 /\ 1 <= max_count c / 2 <= 8.
Proof.
  intros c Hc.
  pose proof (zall_spec (fun y => (class_size y * (max_count y / 2) <=? 65536) && (1 <=? max_count y / 2) && (max_count y / 2 <=? 8))%bool (Z.to_nat 31) 1
                ltac:(vm_compute; reflexivity) c ltac:(lia)) as E.
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.leb_le in E3. lia.
Qed.

#[using="Type"] Lemma u32arr_of_CB : forall m A n ds, rw_cells asegs m A [CB n (u32s ds)] -> u32arr asegs m A ds.
Proof.
  intros m A n ds H. apply u8arr_of_rw_cells in H. destruct H as [Hb Hw]. split; [exact Hb|]. rewrite u32s_length, Nat2Z.inj_mul in Hw. exact Hw.
Qed.

End ARUN_2.
