(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac AEvt HeapIface Asn1Aux AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.      (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Export ACnt24.    (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImgGlobals.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ARt () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "WithAL.sshad"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.S"; "WithAL.zcells"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.w_client"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell_at"; "Corelib.Init.Nat.add"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "fdata"; "WithR.cshd"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "Corelib.Init.Datatypes.None"; "WithR.presA"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Corelib.Init.Datatypes.pair"; "WithR.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "WithR.blocks_low"; "WithR.wcover"; "WithR.shadow_free"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "sshad"; "arl_uar_got"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_waddr"; "arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "WithR.artA"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "WithR.HST"; "WithR.HM"; "WithR.HK"; "stdpp.bitvector.definitions.bv_unsigned"; "arl_need_malloc"; "WithR.htop"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "arl_tp"; "AMAX"; "WithR.havol"; "AVOL_CALL"; "AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "WithR.hstkhi"; "WithR.hfr"; "fr_charge"; "FR_MAX"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.win24"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "WithR.call_postA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "WithR.hflag"; "WithR.hcs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "arl_malloc"; "Corelib.Lists.ListDef.repeat"; "arl_calloc"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "WithR.KF"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "WithR.hm_writable"; "WithR.presW"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.inside"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "WithR.wlow"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record art_layout := ARL {
  arl_L : heap_layout;           (* [comment removed for export] *)
  arl_AL : asan_layout;
  arl_stklo : Z;                 (* [comment removed for export] *)
  arl_malloc : Z; arl_calloc : Z; arl_free : Z;
  arl_amemcpy : Z; arl_amemset : Z; arl_amemmove : Z;
  arl_memcpy_i : Z; arl_memset_i : Z; arl_memcmp_i : Z;
  arl_set00 : Z; arl_setf5 : Z; arl_setf8 : Z;
  arl_smalloc : Z -> Z;          (* [comment removed for export] *)
  arl_sfree5 : Z;
  arl_uar_got : Z;               (* [comment removed for export] *)
  arl_tp : Z;                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  arl_need_malloc : Z; arl_need_free : Z; arl_need_smalloc : Z; arl_need_amem : Z; arl_need_bcmp : Z; arl_need_setsh : Z;
  arl_need_rip : Z;              (* [comment removed for export] *)
  arl_rip : Z;                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  arl_rtc : mem -> Prop
}.

(* [comment removed for export] *)
Definition AVOL_MAX : Z := 2^36.           (* [comment removed for export] *)
Definition AVOL_CALL : Z := 0.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition FR_MAX : Z := 2^32 - 2^21.
Definition fr_charge (d : Z) : Z := d + 3.
Definition AMAX : Z := 2^28.         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMAX_SEC : Z := 64513.
Definition vchg (n : Z) : Z := if n <? AMAX_SEC then 0 else 2 * n + AVOL_CALL.
Lemma vchg_nonneg : forall n, 0 <= n -> 0 <= vchg n.
Proof. intros n H. unfold vchg, AVOL_CALL. destruct (n <? AMAX_SEC); lia. Qed.
Lemma vchg_le : forall n, 0 <= n -> vchg n <= 2 * n + AVOL_CALL.
Proof. intros n H. unfold vchg, AVOL_CALL. destruct (n <? AMAX_SEC); lia. Qed.
Lemma vchg_small : forall n, n < AMAX_SEC -> vchg n = 0.
Proof. intros n H. unfold vchg. apply Z.ltb_lt in H. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint fdata (LF : list blk) : list blk :=
  match LF with
  | [] => []
  | (FB, n) :: r => (FB, Z.min 24 n) :: (FB + 32, n - 40) :: fdata r
  end.

Lemma fdata_app : forall A B, fdata (A ++ B) = fdata A ++ fdata B.
Proof. induction A as [|[x n] A IH]; intros; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma fdata_cons_sub : forall (b : blk) LB FB n LF, In b (LB ++ fdata LF) -> In b (LB ++ fdata ((FB, n) :: LF)).
Proof.
  intros b LB FB n LF H. apply in_app_iff in H. apply in_app_iff. destruct H as [H|H]; [left; exact H| right].
  cbn. right; right. exact H.
Qed.

Lemma In_fdata_hdr : forall FB n LF, In (FB, n) LF -> In (FB, Z.min 24 n) (fdata LF).
Proof. induction LF as [|[x k] r IH]; cbn; intros H; [destruct H|]. destruct H as [E|H]; [injection E; intros -> ->; left; reflexivity| right; right; apply IH, H]. Qed.
Lemma In_fdata_dat : forall FB n LF, In (FB, n) LF -> In (FB + 32, n - 40) (fdata LF).
Proof. induction LF as [|[x k] r IH]; cbn; intros H; [destruct H|]. destruct H as [E|H]; [injection E; intros -> ->; right; left; reflexivity| right; right; apply IH, H]. Qed.

Section WithAL.
Variable segs : list Segment.
Variable AL : asan_layout.

#[using="Type"] Lemma shadow_of_succ : forall c, shadow_of AL (c + 8) = shadow_of AL c + 1.
Proof. intros. unfold shadow_of. replace (c + 8) with (c + 1 * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

#[using="Type"] Lemma shadow_of_plus : forall c i, shadow_of AL (c + 8 * i) = shadow_of AL c + i.
Proof. intros. unfold shadow_of. rewrite (Z.mul_comm 8 i), Z.div_add by lia. lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sshad (m : mem) (lo hi : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_ARt ()) "(0.(1.$2.(3.O2.+8.)=)(0.(1.$2.(3.O1.+8.)=)Pg,$2.P,(4.O2.R1.)P,(4.(5.R2.+8.)O1.)P,(1.$2.(3.R3.+8.)=)(6.Vsegs,O3.(7.VAL,R4.)(8.$9.(:.(;.&8.=))(<.$9.)))))")
(* [comment removed for export] *).

#[using="Type"] Lemma sshad_split : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "Pm,P,(=.&40.)(>.(=.&8.))Plo,$2.Pmid,$2.Phi,$2.P,(?.R4.R3.R1.)P,(0.(4.R4.R3.)(4.R3.R2.))P,(1.$2.(3.R4.+8.)=)(0.(?.R7.R6.R5.)(?.R7.R5.R4.))")
(* [comment removed for export] *).
Proof. intros m lo mid hi (A0 & A1 & H) Hm Hmid. split; (split; [assumption|]; split; [assumption|]); intros g ? ? ?; apply H; lia. Qed.

#[using="Type"] Lemma sshad_merge : forall m lo mid hi, sshad m lo mid -> sshad m mid hi -> lo <= mid <= hi -> sshad m lo hi.
Proof.
  intros m lo mid hi (A0 & A1 & HA) (B0 & B1 & HB) Hm. split; [assumption|]. split; [assumption|].
  intros g H1 H2 H3. destruct (Z_lt_le_dec g mid).
  - apply HA; lia.
  - apply HB; lia.
Qed.

(* [comment removed for export] *)
Fixpoint zcells (n : nat) : list cell := match n with O => [] | S k => C1 (Z_to_bv 8 0) :: zcells k end.
#[using="Type"] Lemma cells_size_zcells : forall n, cells_size (zcells n) = n.
Proof. induction n; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.

#[using="Type"] Lemma sshad_chunk : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "Pm,P,(=.&40.)(>.(=.&8.))Plo,$2.Phi,$2.Pn,$10.PB,$2.P,(?.R5.R4.R3.)P,(4.R5.R2.)P,(4.(5.R3.(11.+8.(12.(13.R4.))))R5.)P,(1.$2.(3.R4.+8.)=)(6.Vsegs,R9.(7.VAL,R5.)(14.(13.R6.)))")
(* [comment removed for export] *).
Proof.
  intros m lo hi n. induction n as [|n IH]; intros B SS H1 H2 HB.
  - cbn. destruct SS as (_ & _ & SS'). apply SS'; lia.
  - cbn [zcells]. change (C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: zcells n) with ([C1 (Z_to_bv 8 0)] ++ zcells (S n)).
    apply (proj2 (rw_cells_app segs m (shadow_of AL B) [C1 (Z_to_bv 8 0)] (zcells (S n)))). split.
    + destruct SS as (_ & _ & SS'). apply SS'; lia.
    + cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1. rewrite <- shadow_of_succ.
      apply IH; [exact SS| lia | lia |]. rewrite <- Z.add_mod_idemp_l, HB by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sshad_of_chunk : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "Pm,P,(=.&40.)(>.(=.&8.))Pn,$10.PB,$2.P,(6.Vsegs,R3.(7.VAL,R1.)(14.R2.))P,(1.$2.(3.R2.+8.)=)(?.R5.R3.(5.R3.(11.+8.(12.R4.))))")
(* [comment removed for export] *).
Proof.
  intros m n. induction n as [|n IH]; intros B H HB.
  - split; [exact HB|]. split; [rewrite Z.mul_0_r, Z.add_0_r; exact HB|]. intros g ? ? ?. exfalso. lia.
  - cbn [zcells] in H. change (C1 (Z_to_bv 8 0) :: zcells n) with ([C1 (Z_to_bv 8 0)] ++ zcells n) in H.
    apply (proj1 (rw_cells_app segs m (shadow_of AL B) [C1 (Z_to_bv 8 0)] (zcells n))) in H. destruct H as [H0 H1].
    cbn [cells_size csize Nat.add] in H1. change (Z.of_nat 1) with 1 in H1. rewrite <- shadow_of_succ in H1.
    pose proof (IH (B + 8) H1 ltac:(rewrite <- Z.add_mod_idemp_l, HB by lia; reflexivity)) as SS.
    eapply sshad_merge with (mid := B + 8); [| | lia].
    + split; [exact HB|]. split; [rewrite <- Z.add_mod_idemp_l, HB by lia; reflexivity|].
      intros g ? ? ?. replace g with B by lia. exact H0.
    + replace (B + 8 * Z.of_nat (S n)) with (B + 8 + 8 * Z.of_nat n) by lia. exact SS.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sshad_frame : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPm,P,(=.&40.)(>.(=.&8.))Plo,$2.Phi,$2.Pa,$2.Pbs,(15.(=.&8.))P,(16.VAL,R6.)P,(17.R7.R5.(18.R4.R5.))P,(17.R8.R4.(12.(19.(=.&8.)R3.)))P,(4.=R5.)P,(4.(5.R6.(12.(19.(=.&8.)R5.)))(1:.+2.+40.))P,(?.R:.R9.R8.)(?.(1;.R;.(1<.R8.)R7.)R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros CS m lo hi a bs OK HR Ha Ha0 Ha1 (S0 & S1 & SS). split; [exact S0|]. split; [exact S1|].
  intros g G1 G2 G3. pose proof (SS g G1 G2 G3) as H.
  destruct OK as (C1 & _). destruct (C1 g (HR g ltac:(lia))) as (R0 & R1 & R2 & NCS).
  apply rw_cells_frame; [exact H| lia| lia|]. cbn [cells_size csize Nat.add length].
  destruct (Z_lt_le_dec (shadow_of AL g) a); [left; lia|].
  destruct (Z_lt_le_dec (shadow_of AL g) (a + Z.of_nat (length bs))); [|right; lia].
  exfalso. apply NCS. replace (shadow_of AL g) with (a + (shadow_of AL g - a)) by lia. apply Ha. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma apart_by_pred : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PP,P,$2.SpPA,$2.Pn,$2.Pa,$2.Pk,$2.P,Px,$2.P,(0.(4.R5.R1.)(1=.R1.(5.R5.R4.)))A1.R7.R2.P,Px,$2.P,(0.(4.R4.R1.)(1=.R1.(5.R4.R3.)))(1>.A1.R8.R2.)P,(1=.=R5.)P,(1=.=R4.)(1?.(4.(5.R8.R7.)R6.)(4.(5.R6.R5.)R8.))")
(* [comment removed for export] *).
Proof.
  intros P A n a k HA Ha Hn Hk.
  destruct (Z_lt_le_dec a (A + n)) as [H1|H1]; [| left; lia].
  destruct (Z_lt_le_dec A (a + k)) as [H2|H2]; [| right; lia].
  exfalso. destruct (Z_lt_le_dec a A).
  - apply (Ha A ltac:(lia)). apply HA. lia.
  - apply (Ha a ltac:(lia)). apply HA. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shadow_run_not_cs : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPc,$2.Pk,$2.Px,$2.P,(16.VAL,R4.)P,(17.R5.R4.(11.+8.R3.))P,(0.(4.(7.VAL,R5.)R3.)(1=.R3.(5.(7.VAL,R5.)R4.)))(1>.A1.R7.R4.)")
(* [comment removed for export] *).
Proof.
  intros CS c k x OK HC Hx. destruct OK as (C1 & _).
  replace x with (shadow_of AL (c + 8 * (x - shadow_of AL c))) by (rewrite shadow_of_plus; lia).
  apply (proj2 (proj2 (proj2 (C1 _ (HC (c + 8 * (x - shadow_of AL c)) ltac:(lia)))))).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma apart_client_shadow : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPA,$2.Pn,$2.Pc,$2.Ps,$2.Pk,$2.P,(16.VAL,R6.)P,(17.R7.R6.R5.)P,(17.R8.R5.(11.+8.R3.))P,(1.$2.R5.(7.VAL,R6.))P,(1=.=R8.)P,(1=.=R6.)(1?.(4.(5.R;.R:.)R8.)(4.(5.R8.R7.)R;.))")
(* [comment removed for export] *).
Proof.
  intros CS A n c s k OK HA HC -> Hn Hk. apply (apart_by_pred CS); [exact HA| | exact Hn| exact Hk].
  intros x Hx. eapply shadow_run_not_cs; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma apart_shadow_client : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPa,$2.Pn,$2.Pc,$2.Ps,$2.Pk,$2.P,(16.VAL,R6.)P,(17.R7.R6.R5.)P,(17.R8.R5.(11.+8.R3.))P,(1.$2.R5.(7.VAL,R6.))P,(1=.=R8.)P,(1=.=R6.)(1?.(4.(5.R8.R7.)R;.)(4.(5.R;.R:.)R8.))")
(* [comment removed for export] *).
Proof.
  intros CS a n c s k OK HA HC -> Hn Hk.
  destruct (apart_client_shadow CS a n c (shadow_of AL c) k OK HA HC eq_refl Hn Hk); lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma apart_shadow_shadow : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "Pc1,$2.Pk1,$2.Pc2,$2.Pk2,$2.Ps1,$2.Ps2,$2.P,(1.$2.(3.R6.+8.)=)P,(1.$2.(3.R5.+8.)=)P,(1?.(4.(5.R8.(11.+8.R7.))R6.)(4.(5.R6.(11.+8.R5.))R8.))P,(1.$2.R5.(7.VAL,R9.))P,(1.$2.R5.(7.VAL,R8.))(1?.(4.(5.R7.R:.)R6.)(4.(5.R6.R8.)R7.))")
(* [comment removed for export] *).
Proof.
  intros c1 k1 c2 k2 s1 s2 H1 H2 HD -> ->. unfold shadow_of.
  pose proof (Z.div_mod c1 8 ltac:(lia)). pose proof (Z.div_mod c2 8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sshad_munch : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))Plo,$2.Phi,$2.P,(16.VAL,R6.)P,(21.R7.R6.)P,(17.R8.R4.(18.R3.R4.))P,(22.R8.R7.R6.)P,(23.Vsegs,R8.R7.)P,(?.R9.R7.R6.)(?.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros CS W m m' lo hi OK HW HR MU WM (S0 & S1 & SS). split; [exact S0|]. split; [exact S1|].
  intros g G1 G2 G3. pose proof (SS g G1 G2 G3) as H.
  destruct OK as (C1 & _). destruct (C1 g (HR g ltac:(lia))) as (R0 & R1 & R2 & NCS).
  eapply rw_cells_transport; [exact H| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
  apply disjoint1_of_not_cs with (CS := CS); assumption.
Qed.

#[using="Type"] Lemma shadow_cells_munch : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PB,$2.Pcs,(15.$9.)P,(16.VAL,R6.)P,(21.R7.R6.)P,(24.(25.$2.$2.)Liv,(25.$2.$2.)(1=.(26.$2.$2.R1.)(27.$2.$2.R1.))R7.)P,(17.R9.R5.(11.+8.(12.(28.R4.))))P,(4.=R6.)P,(29.#0.(28.R6.))P,(22.R;.R:.R9.)P,(23.Vsegs,R;.R:.)P,(6.Vsegs,R<.(5.(2:.R:.+3.)(2;.VAL,))R9.)(6.Vsegs,R<.(5.(2:.R;.+3.)(2;.VAL,))R:.)")
(* [comment removed for export] *).
Proof.
  intros CS W m m' B cs OK HW HL HC HB Hn MU WM H.
  eapply rw_cells_transport; [exact H| exact MU| exact WM|].
  assert (G : forall x, Z.shiftr B 3 + al_sb AL <= x < Z.shiftr B 3 + al_sb AL + Z.of_nat (cells_size cs) -> ~ CS x).
  { intros x Hx. eapply (shadow_run_not_cs CS B (Z.of_nat (cells_size cs))); [exact OK| exact HC|].
    unfold shadow_of. rewrite Z.shiftr_div_pow2 in Hx by lia. change (2^3) with 8 in Hx. lia. }
  clear - HW HL G Hn. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. inversion HL; subst.
  split; [| apply IH; assumption].
  cbn in H1, H3. destruct (Z_lt_le_dec (Z.shiftr B 3 + al_sb AL + Z.of_nat (cells_size cs)) (lo + 1)); [left; lia|].
  destruct (Z_le_gt_dec hi (Z.shiftr B 3 + al_sb AL)); [right; lia|]. exfalso.
  destruct (Z_lt_le_dec (Z.shiftr B 3 + al_sb AL) lo).
  - apply (G lo ltac:(lia)). apply H1. lia.
  - apply (G (Z.shiftr B 3 + al_sb AL) ltac:(lia)). apply H1. lia.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma aobj_shadow_store : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPm,P,(=.&40.)(>.(=.&8.))PA,$2.Pn,$2.Pc,$2.Pk,$2.Pbs,(15.(=.&8.))P,(16.VAL,R7.)P,(2<.Vsegs,VAL,R8.R7.R6.R5.)P,(17.R9.R5.(11.+8.R4.))P,(1.$2.(3.R6.+8.)=)P,(1.$2.(12.(19.(=.&8.)R5.))R6.)P,(1=.=R7.)P,(1?.(4.(5.R;.R:.)R9.)(4.(5.R9.(11.+8.R8.))R;.))(2<.Vsegs,VAL,R>.(1;.R=.(1<.(7.VAL,R:.))R8.)R<.R;.)")
(* [comment removed for export] *).
Proof.
  intros CS m A n c k bs OK [HC HS] Hc Hal Hlen Hk HD. split; [exact HC|].
  intros a Ha. destruct (HS a Ha) as (kb & B & HK). exists kb. split; [|exact HK].
  destruct OK as (C1 & _). destruct (C1 a (HC a Ha)) as (R0 & R1 & R2 & _).
  destruct (C1 c (Hc c ltac:(lia))) as (Q0 & Q1 & Q2 & _).
  apply bytes_at_write_other; [exact B| lia| rewrite Hlen |]. 
  - destruct (C1 (c + 8 * (k - 1)) (Hc (c + 8 * (k - 1)) ltac:(lia))) as (_ & _ & Q3 & _). rewrite shadow_of_plus in Q3. lia.
  - cbn [length Z.of_nat Pos.of_succ_nat]. rewrite Hlen. unfold shadow_of.
    pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
    assert (a / 8 < c / 8 \/ c / 8 + k <= a / 8) by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma abase_shadow_store : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPm,P,(=.&40.)(>.(=.&8.))Pc,$2.Pk,$2.Pbs,(15.(=.&8.))P,(16.VAL,R5.)P,(2=.Vsegs,VAL,R5.)P,(17.R7.R5.(11.+8.R4.))P,(1.$2.(12.(19.(=.&8.)R4.))R5.)P,(1=.=R6.)(2=.Vsegs,VAL,(1;.R9.(1<.(7.VAL,R8.))R6.))")
(* [comment removed for export] *).
Proof.
  intros CS m c k bs OK [G1 G2] Hc Hlen Hk. destruct OK as (C1 & C2 & C3 & _).
  destruct (C1 c (Hc c ltac:(lia))) as (Q0 & Q1 & Q2 & _).
  destruct (C1 (c + 8 * (k - 1)) (Hc (c + 8 * (k - 1)) ltac:(lia))) as (_ & _ & Q3 & _). rewrite shadow_of_plus in Q3.
  split.
  - apply ro_cells_frame; [exact G1| lia| rewrite Hlen; lia|]. cbn [cells_size csize Nat.add]. rewrite Hlen.
    apply (apart_by_pred (fun x => exists i, 0 <= i < 8 /\ x = al_got AL + i)).
    + intros x Hx. exists (x - al_got AL). lia.
    + intros x Hx (i & Hi & ->).
      apply (proj1 (C3 (c + 8 * (al_got AL + i - shadow_of AL c)) i (Hc (c + 8 * (al_got AL + i - shadow_of AL c)) ltac:(lia)) Hi)).
      rewrite shadow_of_plus. lia.
    + lia. + lia.
  - apply ro_cells_frame; [exact G2| lia| rewrite Hlen; lia|]. cbn [cells_size csize Nat.add]. rewrite Hlen.
    apply (apart_by_pred (fun x => exists i, 0 <= i < 8 /\ x = al_gsb AL + i)).
    + intros x Hx. exists (x - al_gsb AL). lia.
    + intros x Hx (i & Hi & ->).
      apply (proj2 (C3 (c + 8 * (al_gsb AL + i - shadow_of AL c)) i (Hc (c + 8 * (al_gsb AL + i - shadow_of AL c)) ltac:(lia)) Hi)).
      rewrite shadow_of_plus. lia.
    + lia. + lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sshad_shadow_store : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPm,P,(=.&40.)(>.(=.&8.))Plo,$2.Phi,$2.Pc,$2.Pk,$2.Pbs,(15.(=.&8.))P,(16.VAL,R7.)P,(?.R7.R6.R5.)P,(17.R9.R7.(18.R6.R7.))P,(17.R:.R6.(11.+8.R5.))P,(1.$2.(3.R7.+8.)=)P,(1.$2.(12.(19.(=.&8.)R6.))R7.)P,(1=.=R8.)P,(1?.(4.R;.R:.)(4.(5.R:.(11.+8.R9.))R<.))(?.(1;.R>.(1<.(7.VAL,R;.))R9.)R=.R<.)")
(* [comment removed for export] *).
Proof.
  intros CS m lo hi c k bs OK (S0 & S1 & SS) HR Hc Hal Hlen Hk HD. split; [exact S0|]. split; [exact S1|].
  intros g G1 G2 G3. pose proof (SS g G1 G2 G3) as H.
  destruct OK as (C1 & _). destruct (C1 c (Hc c ltac:(lia))) as (Q0 & Q1 & Q2 & _).
  destruct (C1 (c + 8 * (k - 1)) (Hc (c + 8 * (k - 1)) ltac:(lia))) as (_ & _ & Q3 & _). rewrite shadow_of_plus in Q3.
  apply rw_cells_frame; [exact H| lia| rewrite Hlen; lia|]. cbn [cells_size csize Nat.add]. rewrite Hlen.
  change (Z.of_nat 1) with 1.
  destruct (apart_shadow_shadow g 1 c k (shadow_of AL g) (shadow_of AL c) G3 Hal ltac:(lia) eq_refl eq_refl); lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shadow_store_bounds : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPc,$2.Plen,$10.Pa,$2.P,(16.VAL,R4.)P,(17.R5.R4.(11.+8.(12.R3.)))P,(29.#0.R4.)P,(1.$2.R4.(7.VAL,R6.))(0.(4.=R5.)(4.(5.R5.(12.R6.))(1:.+2.+40.)))")
(* [comment removed for export] *).
Proof.
  intros CS c len a OK HC Hl ->. destruct OK as (C1 & _).
  destruct (C1 c (HC c ltac:(lia))) as (_ & R1 & _ & _).
  destruct (C1 (c + 8 * (Z.of_nat len - 1)) (HC (c + 8 * (Z.of_nat len - 1)) ltac:(lia))) as (_ & _ & R2 & _).
  rewrite shadow_of_plus in R2. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aobj_shadow_store_at : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPm,P,(=.&40.)(>.(=.&8.))PA,$2.Pn,$2.Pc,$2.Pa,$2.Pbs,(15.(=.&8.))P,(16.VAL,R7.)P,(2<.Vsegs,VAL,R8.R7.R6.R5.)P,(17.R9.R5.(11.+8.(12.(19.(=.&8.)R3.))))P,(1.$2.(3.R6.+8.)=)P,(29.#0.(19.(=.&8.)R5.))P,(1?.(4.R9.=)(1?.(4.(5.R:.R9.)R8.)(4.(5.R8.(11.+8.(12.(19.(=.&8.)R6.))))R:.)))P,(1.$2.R8.(7.VAL,R9.))(2<.Vsegs,VAL,R>.(1;.R=.(1<.R9.)R8.)R<.R;.)")
(* [comment removed for export] *).
Proof.
  intros CS m A n c a bs OK H Hc Hal Hl HD ->. destruct HD as [Hn|HD].
  - destruct H as [HC HS]. split; [exact HC|]. intros x Hx. exfalso. lia.
  - eapply aobj_shadow_store; eauto; lia.
Qed.

#[using="Type"] Lemma abase_shadow_store_at : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPm,P,(=.&40.)(>.(=.&8.))Pc,$2.Pa,$2.Pbs,(15.(=.&8.))P,(16.VAL,R5.)P,(2=.Vsegs,VAL,R5.)P,(17.R7.R5.(11.+8.(12.(19.(=.&8.)R3.))))P,(29.#0.(19.(=.&8.)R4.))P,(1.$2.R6.(7.VAL,R7.))(2=.Vsegs,VAL,(1;.R9.(1<.R7.)R6.))")
(* [comment removed for export] *).
Proof. intros CS m c a bs OK H Hc Hl ->. eapply abase_shadow_store; eauto; lia. Qed.

#[using="Type"] Lemma sshad_shadow_store_at : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPm,P,(=.&40.)(>.(=.&8.))Plo,$2.Phi,$2.Pc,$2.Pa,$2.Pbs,(15.(=.&8.))P,(16.VAL,R7.)P,(?.R7.R6.R5.)P,(17.R9.R7.(18.R6.R7.))P,(17.R:.R6.(11.+8.(12.(19.(=.&8.)R4.))))P,(1.$2.(3.R7.+8.)=)P,(29.#0.(19.(=.&8.)R6.))P,(1?.(4.R:.R9.)(4.(5.R9.(11.+8.(12.(19.(=.&8.)R7.))))R;.))P,(1.$2.R9.(7.VAL,R:.))(?.(1;.R>.(1<.R:.)R9.)R=.R<.)")
(* [comment removed for export] *).
Proof. intros CS m lo hi c a bs OK H HR Hc Hal Hl HD ->. eapply sshad_shadow_store; eauto; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shadow_cells_client_store : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPm,P,(=.&40.)(>.(=.&8.))PB,$2.Pcs,(15.$9.)Pa,$2.Pbs,(15.(=.&8.))P,(16.VAL,R6.)P,(6.Vsegs,R6.(5.(2:.R5.+3.)(2;.VAL,))R4.)P,(4.=R6.)P,(17.R9.R7.(11.+8.(12.(28.R6.))))P,(17.R:.R6.(12.(19.(=.&8.)R5.)))P,(29.#0.(28.R8.))P,(29.#0.(19.(=.&8.)R7.))P,(4.=R9.)P,(4.(5.R:.(12.(19.(=.&8.)R9.)))(1:.+2.+40.))(6.Vsegs,(1;.R>.(1<.R;.)R:.)(5.(2:.R=.+3.)(2;.VAL,))R<.)")
(* [comment removed for export] *).
Proof.
  intros CS m B cs a bs OK H HB HCB HCa Hn Hl Ha0 Ha1.
  apply rw_cells_frame; [exact H| lia| lia|].
  pose proof (apart_shadow_client CS a (Z.of_nat (length bs)) B (Z.shiftr B 3 + al_sb AL) (Z.of_nat (cells_size cs)) OK HCa HCB) as AP.
  destruct AP; [unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia| lia| lia| |]; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_of_read1 : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "Pm,P,(=.&40.)(>.(=.&8.))Ps,$2.Pb,(=.&8.)P,(4.=R2.)P,(4.(5.R3.+1.)(1:.+2.+40.))P,(1.(>.(15.(=.&8.)))(2>.Vsegs,R5.(1<.R4.)#1.)(2?.(15.(=.&8.))(8.(=.&8.)R3.(<.(=.&8.)))))(30.Vsegs,R6.R5.(8.(=.&8.)R4.(<.(=.&8.))))")
(* [comment removed for export] *).
Proof.
  intros m s b H0 H1 RD. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
  assert (i = 0%nat) as -> by lia. rewrite Z.add_0_r. cbn.
  rewrite ov_rdn, rdn_unfold in RD. destruct (mrd segs m (wa s)) as [b'|]; [|discriminate].
  cbn in RD. congruence.
Qed.

#[using="Type"] Lemma aobj_of_zero_shadow : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPm,P,(=.&40.)(>.(=.&8.))PB,$2.Pcs,(15.$9.)PA,$2.Pg0,$10.Pn,$10.P,(16.VAL,R7.)P,(17.R8.R4.(11.+8.(12.R2.)))P,(1.$2.(3.R7.+8.)=)P,(1.$2.R6.(5.R8.(11.+8.(12.R5.))))P,(6.Vsegs,R:.(7.VAL,R9.)R8.)P,Pi,$10.P,(29.R1.R7.)(1.(>.$9.)(31.R;.(32.R9.R2.))(2?.$9.(:.(;.&8.=))))(2<.Vsegs,VAL,R=.R<.R9.(11.+8.(12.R7.)))")
(* [comment removed for export] *).
Proof.
  intros CS m B cs A g0 n OK HC HB HA H HZ. split; [exact HC|].
  intros a Ha. exists (Z_to_bv 8 0). split; [| left; reflexivity].
  destruct OK as (C1' & _). destruct (C1' a (HC a Ha)) as (R0 & R1 & R2 & _).
  pose proof (Z.div_mod a 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as MB.
  pose proof (Z.div_mod B 8 ltac:(lia)) as DMB.
  set (i := Z.to_nat ((a - A) / 8)).
  assert (Hi : (i < n)%nat).
  { subst i. assert (0 <= (a - A) / 8) by (apply Z.div_pos; lia).
    assert ((a - A) / 8 < Z.of_nat n) by (apply Z.div_lt_upper_bound; lia). lia. }
  pose proof (rw_cells_read segs m _ cs (g0 + i) _ H (HZ i Hi)) as RD. cbn [csize cbytes] in RD.
  assert (E : shadow_of AL a = shadow_of AL B + Z.of_nat (g0 + i)).
  { subst i. unfold shadow_of. rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia).
    pose proof (Z.div_mod (a - A) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a - A) 8 ltac:(lia)).
    subst A. nia. }
  rewrite E. apply bytes_at_of_read1; [lia | lia | exact RD].
Qed.


#[using="Type"] Lemma aobj_of_zero_shadow_sh : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPm,P,(=.&40.)(>.(=.&8.))PB,$2.Pcs,(15.$9.)PA,$2.Pg0,$10.Pn,$10.P,(16.VAL,R7.)P,(6.Vsegs,R7.(5.(2:.R6.+3.)(2;.VAL,))R5.)P,(17.R9.R5.(11.+8.(12.R3.)))P,(1.$2.(3.R8.+8.)=)P,(4.=R9.)P,(1.$2.R8.(5.R:.(11.+8.(12.R7.))))P,Pi,$10.P,(29.R1.R8.)(1.(>.$9.)(31.R<.(32.R:.R2.))(2?.$9.(:.(;.&8.=))))(2<.Vsegs,VAL,R>.R=.R:.(11.+8.(12.R8.)))")
(* [comment removed for export] *).
Proof.
  intros CS m B cs A g0 n OK H HC HB H0 HA HZ.
  replace (Z.shiftr B 3 + al_sb AL) with (shadow_of AL B) in H
    by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
  eapply aobj_of_zero_shadow; eauto.
Qed.

End WithAL.

Section WithR.
Variable segs : list Segment.
Variable R : art_layout.
Let L := arl_L R.
#[local] Existing Instance L.   (* [comment removed for export] *)
Let AL := arl_AL R.

Definition cstatic (a : Z) : Prop := hl_data_lo L <= a < hl_data_hi L /\ ~ hl_static L a.

(* [comment removed for export] *)
Definition cshd (LB LF : list blk) (SSP TOP : Z) (c : Z) : Prop :=
  (SSP <= c < TOP) \/ in_block LB c \/ in_block LF c \/ cstatic c.

(* [comment removed for export] *)
Definition presA (LB LF : list blk) (SP SSP TOP : Z) (W : list ivl) (m m' : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_ARt ()) "(0.(33.Vsegs,VL,(34.$35.O8.(36.O7.))O6.O3.O2.O1.)Pc,$2.P,(37.O8.O7.O5.O4.R1.)P,(0.(4.=(7.VAL,R2.))(1=.(7.VAL,R2.)(1:.+2.+40.)))(0.(1.(>.(=.&8.))A1.O1.(1<.(7.VAL,R3.))A1.O2.(1<.(7.VAL,R3.)))P,(1>.(1.(>.(=.&8.))(38.Vsegs,O2.(1<.(7.VAL,R3.)))(39.(=.&8.))))(1>.(1.(>.(=.&8.))(38.Vsegs,O1.(1<.(7.VAL,R4.)))(39.(=.&8.))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma presA_refl : forall LB LF SP SSP TOP W m, presA LB LF SP SSP TOP W m m.
Proof. intros. split; [apply heap_presx_refl|]. intros; auto. Qed.

#[using="Type"] Lemma presA_trans : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm1,P,(=.&40.)(>.(=.&8.))Pm2,P,(=.&40.)(>.(=.&8.))P,(3:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(3:.R:.R9.R8.R7.R6.R5.R3.R2.)(3:.R;.R:.R9.R8.R7.R6.R5.R3.)")
(* [comment removed for export] *).
Proof.
  intros LB LF SP SSP TOP W m m1 m2 [P1 S1] [P2 S2]. split; [eapply heap_presx_trans; eauto|].
  intros c Hc Hr. destruct (S1 c Hc Hr) as [E1 W1]. destruct (S2 c Hc Hr) as [E2 W2]. split; [congruence| auto].
Qed.

#[using="Type"] Lemma presA_presx : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))P,(3:.R8.R7.R6.R5.R4.R3.R2.R1.)(33.Vsegs,VL,(34.$35.R9.(36.R8.))R7.R4.R3.R2.)")
(* [comment removed for export] *).
Proof. intros LB LF SP SSP TOP W m m' [H _]; exact H. Qed.

#[using="Type"] Lemma in_fdata_hull : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLF,(15.$35.)Pb,$35.Px,$2.P,(3;.$35.R2.(36.R3.))P,(0.(4.(26.$2.$2.R3.)R2.)(1=.R2.(5.(26.$2.$2.R3.)(27.$2.$2.R3.))))(3<.$35.Lfb,$35.(0.(3;.$35.R1.R6.)(0.(4.(26.$2.$2.R1.)R4.)(1=.R4.(5.(26.$2.$2.R1.)(27.$2.$2.R1.))))))")
(* [comment removed for export] *).
Proof.
  induction LF as [|[FB n] r IH]; cbn; intros b x Hb Hx; [destruct Hb|].
  destruct Hb as [E|[E|Hb]].
  - subst b. cbn in Hx. exists (FB, n). split; [left; reflexivity| cbn; lia].
  - subst b. cbn in Hx. exists (FB, n). split; [left; reflexivity| cbn; lia].
  - destruct (IH b x Hb Hx) as (fb & H1 & H2). exists fb. split; [right; exact H1| exact H2].
Qed.

#[using="Type"] Lemma fdata_incl : forall LF LF' b, (forall fb, In fb LF -> In fb LF') -> In b (fdata LF) -> In b (fdata LF').
Proof.
  induction LF as [|[x n] r IH]; cbn; intros LF' b HF Hb; [destruct Hb|].
  destruct Hb as [E|[E|Hb]].
  - subst b. apply (In_fdata_hdr x n). apply HF. left; reflexivity.
  - subst b. apply (In_fdata_dat x n). apply HF. left; reflexivity.
  - apply IH; [| exact Hb]. intros b' Hb'. apply HF. right. exact Hb'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma presA_weaken : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLB',(15.$35.)PLF,(15.$35.)PLF',(15.$35.)PSP,$2.PSP',$2.PSSP,$2.PSSP',$2.PTOP,$2.PTOP',$2.PW,(15.$20.)PW',(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))P,(3:.R>.R<.R:.R8.R6.R4.R2.R1.)P,Pb,$35.P,(3;.$35.R1.R?.)(3;.$35.R2.R11.)P,Pb,$35.P,(3;.$35.R1.R>.)(3;.$35.R2.R10.)P,(4.R=.R<.)P,(4.R<.R;.)P,(4.R:.R;.)P,Px,$2.P,(3=.R:.R1.)(3=.R<.R2.)(3:.R14.R12.R10.R>.R<.R:.R9.R8.)")
(* [comment removed for export] *).
Proof.
  intros LB LB' LF LF' SP SP' SSP SSP' TOP TOP' W W' m m' [P S] HB HF HS HSS HT HW. split.
  - intros a Ha Hc Ho. apply P; [exact Ha| | apply HW, Ho].
    destruct Hc as [H|[H|(b & Hb & Hr)]]; [left; lia| right; left; exact H| right; right].
    exists b. split; [|exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply HB, Hb| right].
    eapply fdata_incl; eauto.
  - intros c Hc Hr. apply S; [|exact Hr].
    destruct Hc as [H|[(b & Hb & Hx)|[(b & Hb & Hx)|H]]]; [left; lia| right; left| right; right; left| right; right; right; exact H].
    + exists b; split; [apply HB, Hb| exact Hx].
    + exists b; split; [apply HF, Hb| exact Hx].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma presA_of_munch : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PCS,P,$2.SpP,(16.VAL,R1.)P,(21.R2.R5.)P,Pc,$2.P,(37.R<.R;.R9.R8.R1.)A1.R5.R2.P,(22.R7.R6.R5.)P,(23.Vsegs,R7.R6.)(3:.R>.R=.R<.R;.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros LB LF SP SSP TOP W m m' CS OK HW HCS MU WM. split.
  - intros a Ha Hc Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia. exact Ho.
  - intros c Hc Hr. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia.
    destruct OK as (C1 & _). apply (outside_of_not_cs CS); [exact HW|].
    exact (proj2 (proj2 (proj2 (C1 c (HCS c Hc))))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fresh_apart (LB LF : list blk) (N k : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_ARt ()) "(0.(1=.=O2.)(0.(4.(5.O2.O1.)(3>.VL,))(0.(1?.(4.(5.O2.O1.)(3?.VL,))(4.(40.VL,)O2.))PB,$2.Pj,$2.P,(3;.(25.$2.$2.)(41.$2.$2.R2.R1.)(34.$35.O4.(36.O3.)))(1?.(4.(5.O2.O1.)R3.)(4.(5.R3.R2.)O2.)))))")
(* [comment removed for export] *).

#[using="Type"] Lemma fresh_apart_client : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)Plo,$2.PA,$2.Pn,$2.PN,$2.Pk,$2.P,(42.R7.R6.R2.R1.)P,(43.VL,(34.$35.R8.(36.R7.))R6.R5.R4.)P,(1=.=R5.)P,(1=.=R4.)P,(4.(3>.VL,)R9.)(1?.(4.(5.R7.R6.)R9.)(4.(5.R9.R8.)R7.))")
(* [comment removed for export] *).
Proof.
  intros LB LF lo A n N k (F0 & F1 & F2 & F3) HR Hn Hk HL. eapply client_range_apart; eauto.
Qed.

#[using="Type"] Lemma fresh_apart_client0 : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)Plo,$2.PA,$2.Pn,$2.PN,$2.Pk,$2.P,(42.R7.R6.R2.R1.)P,(43.VL,(34.$35.R8.(36.R7.))R6.R5.R4.)P,(4.=R5.)P,(1=.=R4.)P,(4.(3>.VL,)R9.)(1?.(1.$2.R8.=)(1?.(4.(5.R7.R6.)R9.)(4.(5.R9.R8.)R7.)))")
(* [comment removed for export] *).
Proof.
  intros LB LF lo A n N k HF HR Hn Hk HL. destruct (Z.eq_dec n 0) as [->|NE]; [left; reflexivity| right].
  eapply fresh_apart_client; eauto. lia.
Qed.

(* [comment removed for export] *)
Definition wcover (LB LF : list blk) (SP : Z) (W : list ivl) (a n : Z) : Prop :=
  forall x, a <= x < a + n -> client_addr L (LB ++ fdata LF) SP x -> ~ outside W x.

#[using="Type"] Lemma wcover_inside : forall LB LF SP W a n, inside W a n -> wcover LB LF SP W a n.
Proof. intros LB LF SP W a n HIn x Hx _. eapply inside_not_outside; eauto. Qed.

(* [comment removed for export] *)
Definition blocks_low (LB LF : list blk) : Prop :=
  forall B j, In (B, j) (LB ++ LF) -> B + j <= alloc_ceiling.

#[using="Type"] Lemma wcover_stack : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PW,(15.$20.)Pa,$2.Pn,$2.P,(44.R6.R5.)P,(4.(40.VL,)(3>.VL,))P,(4.(3>.VL,)R4.)P,(4.(5.R5.R4.)R7.)(45.R:.R9.R8.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros LB LF SP W a n HB HD H1 H2 x Hx Hc _. destruct Hc as [Hs|[[Hd _]|(b & Hb & Hr)]]; [lia| lia|].
  apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
  - destruct b as [B j]. pose proof (HB B j ltac:(apply in_app_iff; left; exact Hb)). cbn in Hr. lia.
  - destruct (in_fdata_hull LF b x Hb Hr) as ([B j] & H3 & H4). pose proof (HB B j ltac:(apply in_app_iff; right; exact H3)). cbn in H4. lia.
Qed.

#[using="Type"] Lemma wcover_fresh : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PW,(15.$20.)Pa,$2.Pn,$2.PN,$2.Pk,$2.P,(42.R8.R7.R2.R1.)P,(4.R3.R5.)P,(4.(5.R6.R5.)(5.R4.R3.))P,(4.(3>.VL,)R9.)(45.R<.R;.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros LB LF SP W a n N k (F0 & F1 & F2 & F3) H1 H2 HSP x Hx Hc _.
  destruct Hc as [Hs|[[Hd1 Hd2]|([B j] & Hb & Hr)]]; [lia| lia|]. cbn in Hr. pose proof (F3 B j Hb). lia.
Qed.

#[using="Type"] Lemma wcover_nil : forall LB LF SP W a n, n <= 0 -> wcover LB LF SP W a n.
Proof. intros LB LF SP W a n H x Hx; lia. Qed.

#[using="Type"] Lemma wcover_sub : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PW,(15.$20.)PA,$2.Pn,$2.Pa,$2.Pk,$2.P,(45.R8.R7.R6.R5.R4.R3.)P,(4.R5.R3.)P,(4.(5.R4.R3.)(5.R6.R5.))(45.R;.R:.R9.R8.R5.R4.)")
(* [comment removed for export] *).
Proof. intros LB LF SP W A n a k H H1 H2 x Hx. apply H. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma write_outside : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "Pm,P,(=.&40.)(>.(=.&8.))Pa,$2.Pbs,(15.(=.&8.))Px,$2.P,(4.=R3.)P,(4.(5.R4.(12.(19.(=.&8.)R3.)))(1:.+2.+40.))P,(0.(4.=R3.)(1=.R3.(1:.+2.+40.)))P,(1?.(1=.R4.R6.)(4.(5.R6.(12.(19.(=.&8.)R5.)))R4.))(1.(>.(=.&8.))(1;.R8.(1<.R7.)R6.(1<.R5.))A1.R8.(1<.R5.))")
(* [comment removed for export] *).
Proof.
  intros m a bs x Ha Hl Hx Ho. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity. exfalso; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma presA_store_client : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pa,$2.Pbs,(15.(=.&8.))P,(16.VAL,R;.)P,Pc,$2.P,(37.R<.R;.R9.R8.R1.)A1.R>.R2.P,(3:.R<.R;.R:.R9.R8.R7.R6.R5.)P,(17.R>.R5.(12.(19.(=.&8.)R4.)))P,(4.=R6.)P,(4.(5.R7.(12.(19.(=.&8.)R6.)))(1:.+2.+40.))P,(45.R10.R?.R>.R;.R8.(12.(19.(=.&8.)R7.)))(3:.R11.R10.R?.R>.R=.R<.R;.(1;.R:.(1<.R9.)R8.))")
(* [comment removed for export] *).
Proof.
  intros CS LB LF SP SSP TOP W m0 m a bs OK HCS [P S] HC Ha Hl HW. split.
  - intros x Hx Hc Ho. destruct (P x Hx Hc Ho) as [E1 W1]. split.
    + rewrite <- E1. apply write_outside; [exact Ha| exact Hl| exact Hx|].
      destruct (Z_lt_le_dec x a); [left; lia|]. destruct (Z_lt_le_dec x (a + Z.of_nat (length bs))); [| right; lia].
      exfalso. exact (HW x ltac:(lia) Hc Ho).
    + intros Hw. apply wview_write_mono. apply W1, Hw.
  - intros c Hc Hr. destruct (S c Hc Hr) as [E1 W1]. split.
    + rewrite <- E1. apply write_outside; [exact Ha| exact Hl| exact Hr|].
      destruct (Z_lt_le_dec (shadow_of AL c) a); [left; lia|]. destruct (Z_lt_le_dec (shadow_of AL c) (a + Z.of_nat (length bs))); [| right; lia].
      exfalso. destruct OK as (C1 & _). apply (proj2 (proj2 (proj2 (C1 c (HCS c Hc))))).
      replace (shadow_of AL c) with (a + (shadow_of AL c - a)) by lia. apply HC. lia.
    + intros Hw. apply wview_write_mono. apply W1, Hw.
Qed.

(* [comment removed for export] *)
Definition shadow_free (LB LF : list blk) (SSP TOP : Z) (c n : Z) : Prop :=
  forall c', cshd LB LF SSP TOP c' -> ~ (c <= c' < c + n).

#[using="Type"] Lemma shadow_free_stack : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSSP,$2.PTOP,$2.Pc,$2.Pn,$2.P,(44.R6.R5.)P,(4.(40.VL,)(3>.VL,))P,(4.(3>.VL,)R4.)P,(4.(5.R5.R4.)R7.)(46.R:.R9.R8.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros LB LF SSP TOP c n HB HD H1 H2 c' Hc' Hr.
  destruct Hc' as [Hs|[([B j] & Hb & Hx)|[([B j] & Hb & Hx)|[Hd _]]]]; cbn in *; [lia| | | lia].
  - pose proof (HB B j ltac:(apply in_app_iff; left; exact Hb)). lia.
  - pose proof (HB B j ltac:(apply in_app_iff; right; exact Hb)). lia.
Qed.

#[using="Type"] Lemma shadow_free_fresh : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSSP,$2.PTOP,$2.Pc,$2.Pn,$2.PN,$2.Pk,$2.P,(42.R8.R7.R2.R1.)P,(44.R9.R8.)P,(4.R4.R6.)P,(4.(5.R7.R6.)(5.R5.R4.))P,(4.(3>.VL,)R:.)P,PB,$2.Pj,$2.P,(3;.(25.$2.$2.)(41.$2.$2.R2.R1.)R>.)(1?.(4.(5.R:.R9.)R3.)(4.(5.R3.R2.)R:.))(46.R>.R=.R<.R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros LB LF SSP TOP c n N k (F0 & F1 & F2 & F3) HB H1 H2 HS HLF c' Hc' Hr.
  destruct Hc' as [Hs|[([B j] & Hb & Hx)|[([B j] & Hb & Hx)|[Hd _]]]]; cbn in *; [lia| | | lia].
  - pose proof (F3 B j ltac:(apply in_app_iff; left; exact Hb)). lia.
  - pose proof (HLF B j Hb). lia.
Qed.

#[using="Type"] Lemma shadow_free_sub : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSSP,$2.PTOP,$2.PC,$2.Pn,$2.Pc,$2.Pk,$2.P,(46.R8.R7.R6.R5.R4.R3.)P,(4.R5.R3.)P,(4.(5.R4.R3.)(5.R6.R5.))(46.R;.R:.R9.R8.R5.R4.)")
(* [comment removed for export] *).
Proof. intros LB LF SSP TOP C n c k H H1 H2 c' Hc' Hr. apply (H c' Hc'). lia. Qed.

#[using="Type"] Lemma blocks_apart_mid : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)Pr,(15.$35.)PA,$2.Pn,$2.P,(47.(34.$35.R4.(8.(25.$2.$2.)(41.$2.$2.R2.R1.)R3.)))PB,$2.Pk,$2.P,(3;.(25.$2.$2.)(41.$2.$2.R2.R1.)R6.)(1?.(4.(5.R6.R5.)R3.)(4.(5.R3.R2.)R6.))")
(* [comment removed for export] *).
Proof.
  induction LB as [|[x y] LB IH]; cbn; intros r A n H B k HIn.
  - destruct H as [H _]. apply H, HIn.
  - destruct H as [_ H]. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma presA_store_shadow : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pc,$2.Pa,$2.Pbs,(15.(=.&8.))P,(16.VAL,R<.)P,Pc',$2.P,(37.R=.R<.R:.R9.R1.)A1.R?.R2.P,Px,$2.P,A1.R?.R1.(0.(4.(40.VL,)(7.VAL,R2.))(1=.(7.VAL,R2.)(3>.VL,)))P,(4.(3>.VL,)R<.)P,PB,$2.Pj,$2.P,(3;.(25.$2.$2.)(41.$2.$2.R2.R1.)(34.$35.R11.(36.R10.)))(17.R13.R3.R2.)P,(3:.R10.R?.R>.R=.R<.R;.R:.R9.)P,(1.$2.R8.(7.VAL,R9.))P,(1.$2.(3.R:.+8.)=)P,(17.R14.R;.(11.+8.(12.(19.(=.&8.)R9.))))P,(46.R14.R13.R11.R10.R<.(11.+8.(12.(19.(=.&8.)R:.))))(3:.R15.R14.R13.R12.R11.R10.R?.(1;.R>.(1<.R<.)R;.))")
(* [comment removed for export] *).
Proof.
  intros CS LB LF SP SSP TOP W m0 m c a bs OK HCS SHB HSP HBK [P S] -> Hc8 HC HF.
  destruct OK as (C1 & _).
  assert (NCS : forall x, shadow_of AL c <= x < shadow_of AL c + Z.of_nat (length bs) -> ~ CS x).
  { intros x Hx. replace x with (shadow_of AL (c + 8 * (x - shadow_of AL c))) by (rewrite shadow_of_plus; lia).
    apply (proj2 (proj2 (proj2 (C1 _ (HC (c + 8 * (x - shadow_of AL c)) ltac:(lia)))))). }
  destruct bs as [|b0 bs'].
  { cbn. split; [exact P| exact S]. }
  remember (b0 :: bs') as bs eqn:Ebs.
  assert (LEN : 0 < Z.of_nat (length bs)) by (subst bs; cbn; lia).
  destruct (C1 c (HC c ltac:(lia))) as (_ & B0 & _ & _).
  destruct (C1 (c + 8 * (Z.of_nat (length bs) - 1)) (HC (c + 8 * (Z.of_nat (length bs) - 1)) ltac:(lia))) as (_ & _ & B1 & _). rewrite shadow_of_plus in B1.
  assert (B1' : shadow_of AL c + Z.of_nat (length bs) <= 2^64) by lia. clear B1. rename B1' into B1.
  split.
  - intros x Hx Hcl Ho. destruct (P x Hx Hcl Ho) as [E1 W1]. split; [| intros Hw; apply wview_write_mono; apply W1, Hw].
    rewrite <- E1. apply write_outside; [exact B0| exact B1| exact Hx|].
    destruct (Z_lt_le_dec x (shadow_of AL c)); [left; lia|]. destruct (Z_lt_le_dec x (shadow_of AL c + Z.of_nat (length bs))); [| right; lia].
    exfalso.
    (* [comment removed for export] *)
    set (c1 := c + 8 * (x - shadow_of AL c)).
    assert (X1 : x = shadow_of AL c1) by (subst c1; rewrite shadow_of_plus; lia).
    assert (CS1 : CS c1) by (subst c1; apply HC; lia).
    destruct (SHB c1 CS1) as [D1 D2].
    destruct Hcl as [Hs|[[Hd1 Hd2]|([B j] & Hb & Hr)]]; [lia| lia|].
    apply (NCS x ltac:(lia)). cbn in Hr. replace x with (B + (x - B)) by lia. apply (HBK B j Hb). lia.
  - intros c' Hc' Hr. destruct (S c' Hc' Hr) as [E1 W1]. split; [| intros Hw; apply wview_write_mono; apply W1, Hw].
    rewrite <- E1. apply write_outside; [exact B0| exact B1| exact Hr|].
    destruct (Z_lt_le_dec (shadow_of AL c') (shadow_of AL c)); [left; lia|].
    destruct (Z_lt_le_dec (shadow_of AL c') (shadow_of AL c + Z.of_nat (length bs))); [| right; lia].
    exfalso. apply (HF c' Hc'). unfold shadow_of in *.
    pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.div_mod c' 8 ltac:(lia)). pose proof (Z.mod_pos_bound c' 8 ltac:(lia)).
    nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma presA_rw_cells : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PA,$2.Pcs,(15.$9.)P,(3:.R:.R9.R8.R7.R6.R5.R4.R3.)P,(6.Vsegs,R5.R3.R2.)P,(43.VL,(34.$35.R<.(36.R;.))R:.R4.(12.(28.R3.)))P,(48.R8.R5.(12.(28.R4.)))(6.Vsegs,R7.R6.R5.)")
(* [comment removed for export] *).
Proof. intros. eapply heap_presx_rw_cells; eauto. eapply presA_presx; eauto. Qed.

#[using="Type"] Lemma presA_ro_cells : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PA,$2.Pcs,(15.$9.)P,(3:.R:.R9.R8.R7.R6.R5.R4.R3.)P,(49.Vsegs,R5.R3.R2.)P,(43.VL,(34.$35.R<.(36.R;.))R:.R4.(12.(28.R3.)))P,(48.R8.R5.(12.(28.R4.)))(49.Vsegs,R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros LB LF SP SSP TOP W m m' A cs HP [Hwf HB] HR HD. split; [exact Hwf|].
  eapply heap_presx_bytes_at; [eapply presA_presx; exact HP| exact HB| |]; rewrite cells_bytes_length by assumption; assumption.
Qed.

#[using="Type"] Lemma presA_bytes_at : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PA,$2.Pbs,(15.(=.&8.))P,(3:.R:.R9.R8.R7.R6.R5.R4.R3.)P,(30.Vsegs,R5.R3.R2.)P,(43.VL,(34.$35.R<.(36.R;.))R:.R4.(12.(19.(=.&8.)R3.)))P,(48.R8.R5.(12.(19.(=.&8.)R4.)))(30.Vsegs,R7.R6.R5.)")
(* [comment removed for export] *).
Proof. intros. eapply heap_presx_bytes_at; eauto. eapply presA_presx; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma presA_bytes_at0 : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PA,$2.Pbs,(15.(=.&8.))P,(3:.R:.R9.R8.R7.R6.R5.R4.R3.)P,(30.Vsegs,R5.R3.R2.)P,(1?.(1.$10.(19.(=.&8.)R3.)#0.)(0.(43.VL,(34.$35.R<.(36.R;.))R:.R4.(12.(19.(=.&8.)R3.)))(48.R7.R4.(12.(19.(=.&8.)R3.)))))(30.Vsegs,R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros LB LF SP SSP TOP W m m' A bs HP H [E|[HR HD]].
  - destruct bs; [|cbn in E; lia]. destruct H as (H0 & H1 & _). split; [exact H0|]. split; [exact H1|]. intros i Hi; cbn in Hi; lia.
  - eapply presA_bytes_at; eauto.
Qed.

#[using="Type"] Lemma presA_u8arr : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PA,$2.Pxs,(15.(=.&8.))P,(3:.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4:.Vsegs,R5.R3.R2.)P,(43.VL,(34.$35.R<.(36.R;.))R:.R4.(12.(19.(=.&8.)R3.)))P,(48.R8.R5.(12.(19.(=.&8.)R4.)))(4:.Vsegs,R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros LB LF SP SSP TOP W m m' A xs HP H HR HD. apply (u8arr_of_rw_cells segs m' A (length xs)).
  eapply presA_rw_cells; [exact HP| apply rw_cells_of_u8arr; exact H| |]; cbn [cells_size csize]; rewrite Nat.add_0_r; assumption.
Qed.

#[using="Type"] Lemma presA_stk : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))Plo,$2.Phi,$2.P,(3:.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4;.Vsegs,R5.R3.R2.)P,(4.R:.R4.)P,(48.R8.R5.(18.R4.R5.))(4;.Vsegs,R7.R6.R5.)")
(* [comment removed for export] *).
Proof. intros. eapply heap_presx_stk; eauto. eapply presA_presx; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma client_range_cshd : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PA,$2.Pn,$2.Pc,$2.P,(43.VL,(34.$35.R8.(36.R7.))R6.R3.R2.)P,(4.R6.R7.)P,(4.(5.R5.R4.)R6.)P,(0.(4.R6.R4.)(1=.R4.(5.R6.R5.)))(37.R<.R;.R9.R8.R5.)")
(* [comment removed for export] *).
Proof.
  intros LB LF SP SSP TOP A n c HR HS HT Hc. destruct (HR c Hc) as [H|[H|(b & Hb & Hr)]]; [left; lia| right; right; right; exact H|].
  apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [right; left; exists b; auto| right; right; left].
  destruct (in_fdata_hull LF b c Hb Hr) as (fb & H1 & H2). exists fb; auto.
Qed.

#[using="Type"] Lemma presA_aobj : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PA,$2.Pn,$2.P,(16.VAL,R;.)P,(3:.R;.R:.R9.R8.R7.R6.R5.R4.)P,(2<.Vsegs,VAL,R=.R6.R4.R3.)P,(43.VL,(34.$35.R=.(36.R<.))R;.R5.R4.)P,(4.R;.R<.)P,Px,$2.P,A1.R11.R1.(1=.R2.R=.)(2<.Vsegs,VAL,R11.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros CS LB LF SP SSP TOP W m m' A n OK [_ S] [HC HS] HR HSP HTOP. split; [exact HC|].
  intros a Ha. destruct (HS a Ha) as (k & B & HK). exists k. split; [|exact HK].
  destruct OK as (C1 & _). destruct (C1 a (HC a Ha)) as (R0 & R1 & R2 & _).
  assert (CSa : cshd LB LF SSP TOP a).
  { eapply client_range_cshd with (A := a) (n := 1); [| exact HSP| apply (Z.le_succ_l a TOP), HTOP, HC, Ha | lia].
    intros x Hx. apply HR. lia. }
  destruct (S a CSa ltac:(lia)) as [E _].
  destruct B as (B0 & B1 & B). split; [exact B0|]. split; [exact B1|]. intros i Hi.
  assert (i = 0%nat) as -> by (cbn in Hi; lia). specialize (B 0%nat Hi). rewrite Z.add_0_r in B. rewrite Z.add_0_r.
  unfold mrd in B |- *. rewrite E. exact B.
Qed.

#[using="Type"] Lemma presA_aobj0 : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PA,$2.Pn,$2.P,(16.VAL,R;.)P,(3:.R;.R:.R9.R8.R7.R6.R5.R4.)P,(2<.Vsegs,VAL,R=.R6.R4.R3.)P,Px,$2.P,A1.R?.R1.(1=.R2.R;.)P,(1?.(4.R5.=)(0.(43.VL,(34.$35.R>.(36.R=.))R<.R6.R5.)(4.R;.R<.)))(2<.Vsegs,VAL,R10.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros CS LB LF SP SSP TOP W m m' A n OK HP H HT [Hn|[HR HS]].
  - destruct H as [HC _]. split; [exact HC|]. intros a Ha. exfalso. lia.
  - eapply presA_aobj; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma presA_shadow_cells : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PB,$2.Pcs,(15.$9.)P,(16.VAL,R;.)P,(17.R<.R3.(11.+8.(12.(28.R2.))))P,(1.$2.(3.R4.+8.)=)P,(3:.R=.R<.R;.R:.R9.R8.R7.R6.)P,(6.Vsegs,R8.(7.VAL,R6.)R5.)P,Pc,$2.P,(0.(4.R8.R1.)(1=.R1.(5.R8.(11.+8.(12.(28.R7.))))))(37.R11.R10.R>.R=.R2.)(6.Vsegs,R9.(7.VAL,R8.)R7.)")
(* [comment removed for export] *).
Proof.
  intros CS LB LF SP SSP TOP W m m' B cs OK HC HB [_ S] [[Hwf (B0 & B1 & HBY)] (W0 & W1 & HW)] HSH.
  rewrite cells_bytes_length in B1, HBY by assumption.
  destruct OK as (C1 & _).
  assert (G : forall i, 0 <= i < Z.of_nat (cells_size cs) ->
             m' (wa (shadow_of AL B + i)) = m (wa (shadow_of AL B + i))
             /\ (wview segs m (wa (shadow_of AL B + i)) <> None -> wview segs m' (wa (shadow_of AL B + i)) <> None)).
  { intros i Hi. rewrite <- shadow_of_plus. apply S; [apply HSH; lia|].
    destruct (C1 (B + 8 * i) (HC (B + 8 * i) ltac:(lia))) as (R0 & R1 & R2 & _). lia. }
  split; [split; [exact Hwf|]|].
  - split; [exact B0|]. rewrite cells_bytes_length by assumption. split; [exact B1|]. intros i Hi. unfold mrd. destruct (G (Z.of_nat i) ltac:(lia)) as [E _].
    rewrite E. apply HBY. exact Hi.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. destruct (G i Hi) as [_ Wm]. apply Wm, HW, Hi.
Qed.

#[using="Type"] Lemma presA_shadow_cells_sh : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PCS,P,$2.SpPLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PB,$2.Pcs,(15.$9.)P,(16.VAL,R;.)P,(17.R<.R3.(11.+8.(12.(28.R2.))))P,(1.$2.(3.R4.+8.)=)P,(4.=R5.)P,(3:.R>.R=.R<.R;.R:.R9.R8.R7.)P,(6.Vsegs,R9.(5.(2:.R7.+3.)(2;.VAL,))R6.)P,Pc,$2.P,(0.(4.R9.R1.)(1=.R1.(5.R9.(11.+8.(12.(28.R8.))))))(37.R12.R11.R?.R>.R2.)(6.Vsegs,R:.(5.(2:.R9.+3.)(2;.VAL,))R8.)")
(* [comment removed for export] *).
Proof.
  intros CS LB LF SP SSP TOP W m m' B cs OK HC HB H0 HP H HSH.
  replace (Z.shiftr B 3 + al_sb AL) with (shadow_of AL B) in *
    by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
  eapply presA_shadow_cells; eauto.
Qed.

#[using="Type"] Lemma presA_sshad : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PTOP,$2.PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))Plo,$2.Phi,$2.P,(3:.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4<.Vsegs,VAL,R5.R3.R2.)P,(4.R9.R4.)P,(4.R4.R9.)(4<.Vsegs,VAL,R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros LB LF SP SSP TOP W m m' lo hi [_ S] (S0 & S1 & SS) HLO HHI. split; [exact S0|]. split; [exact S1|].
  intros g G1 G2 G3. destruct (SS g G1 G2 G3) as [[Hwf (B0 & B1 & HB)] (W0 & W1 & HW)].
  destruct (S g ltac:(left; lia) ltac:(cbn in B1; lia)) as [E Wm].
  split; [split; [exact Hwf|]|].
  - split; [exact B0|]. split; [exact B1|]. intros i Hi. assert (i = 0%nat) as -> by (cbn in Hi; lia).
    specialize (HB 0%nat Hi). rewrite Z.add_0_r in HB. rewrite Z.add_0_r. unfold mrd in HB |- *. rewrite E. exact HB.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. assert (i = 0) as -> by (cbn in Hi; lia).
    rewrite Z.add_0_r. apply Wm. specialize (HW 0 ltac:(cbn; lia)). rewrite Z.add_0_r in HW. exact HW.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition auar (flag_addr : Z) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_ARt ()) "(0.(49.Vsegs,O1.(4=.VR,)(8.$9.(4>.(;.&40.O2.))(<.$9.)))(49.Vsegs,O1.O2.(8.$9.(4?.(;.&40.+1.))(<.$9.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition hm_writable (LB LF : list blk) (TOP : Z) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_ARt ()) "(1?.(50.VL,(34.$35.O4.(36.O3.))(51.VR,)O2.O1.)(3<.$2.Lc,$2.(0.(1?.(0.(4.(51.VR,)R1.)(1=.R1.O2.))(52.O3.R1.))(1.$2.O1.(7.VAL,R1.)))))")
(* [comment removed for export] *).

Definition call_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : word -> mem -> Prop) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_ARt ()) "Lms',$53.(3<.(=.&40.)Lt0,(=.&40.)(3<.(=.&40.)Lt1,(=.&40.)(3<.(=.&40.)Lt2,(=.&40.)(3<.(=.&40.)La0,(=.&40.)(3<.(=.&40.)La1,(=.&40.)(3<.(=.&40.)La2,(=.&40.)(3<.(=.&40.)La3,(=.&40.)(3<.(=.&40.)La4,(=.&40.)(3<.(=.&40.)La5,(=.&40.)(3<.(=.&40.)La6,(=.&40.)(3<.(=.&40.)La7,(=.&40.)(3<.(=.&40.)Lt3,(=.&40.)(3<.(=.&40.)Lt4,(=.&40.)(3<.(=.&40.)Lt5,(=.&40.)(3<.(=.&40.)Lt6,(=.&40.)(3<.P,(=.&40.)(>.(=.&8.))Lm',P,(=.&40.)(>.(=.&8.))(0.(1.$53.R11.(54.(55.O13.O12.O11.O10.R10.R?.R>.O?.O>.R=.R<.R;.R:.R9.R8.R7.R6.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.R5.R4.R3.R2.)O3.(56.O13.)O2.(39.(=.&40.))R1.(57.Vsegs,)))A2.O1.R=.R1.)))))))))))))))))")
(* [comment removed for export] *).

Record artA := ART {
  HST : Type;
  HM : HST -> list blk -> list blk -> mem -> Prop;        (* [comment removed for export] *)
  HK : HST -> Model -> Prop;                              (* [comment removed for export] *)
  hcs : HST -> Z -> Prop;                                 (* [comment removed for export] *)
  htop : HST -> Z;                                        (* [comment removed for export] *)
  hstkhi : HST -> Z;                                      (* [comment removed for export] *)
  hflag : HST -> Z;                                       (* [comment removed for export] *)
  havol : HST -> Z;                                       (* [comment removed for export] *)
  hfr : HST -> Z;                                         (* [comment removed for export] *)
  aspin : config -> Prop;                                 (* [comment removed for export] *)

  (* [comment removed for export] *)
  hk_halted : forall h mo, HK h mo -> m_halted mo = None;
  hk_mat : forall h mo acc, HK h mo -> acc_ok AL (hcs h) acc ->
      exists mo', materialize_model_accesses mo acc = Some mo' /\ HK h mo' /\ mo_mat mo mo';
  hk_vmonly : forall h mo mo', HK h mo ->
      m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_vm_materialized mo' = m_vm_materialized mo ->
      m_halted mo' = m_halted mo -> HK h mo';

  (* [comment removed for export] *)
  art_alwf : al_wf AL;
  art_uar_img : al_img_lo AL <= arl_uar_got R /\ arl_uar_got R + 8 <= al_img_hi AL;
  art_lo : alloc_ceiling <= arl_stklo R;
  hcs_ok : forall h, cs_ok AL (hcs h);
  hm_top : forall h LB LF m, HM h LB LF m -> arl_stklo R <= htop h <= hstkhi h;
  (* [comment removed for export] *)
  hm_cnt24 : forall h LB LF m, HM h LB LF m -> cnt24 LB <= C24MAX;
  hm_top16 : forall h LB LF m, HM h LB LF m -> htop h + 16 <= 2^47;                      (* [comment removed for export] *)
  hcs_stack : forall h, crange (hcs h) (arl_stklo R) (hstkhi h - arl_stklo R);
  hcs_block : forall h LB LF m A n, HM h LB LF m -> In (A, n) LB -> crange (hcs h) A n;
  hcs_fake : forall h LB LF m A n, HM h LB LF m -> In (A, n) LF -> crange (hcs h) A n;
  hcs_static : forall h a, cstatic a -> hcs h a;
  hcs_below_top : forall h x, hcs h x -> x < hstkhi h;      (* [comment removed for export] *)
  (* [comment removed for export] *)
  hcs_shadow_band : forall h c, hcs h c -> hl_data_hi L <= shadow_of AL c < alloc_ceiling;
  art_data_lo : hl_data_hi L <= alloc_ceiling;
  (* [comment removed for export] *)
  hcs_app : forall h a n, crange (hcs h) a n -> 0 < n ->
      (0 < a /\ a + n + 7 < al_sb AL) \/ (al_sb AL + 2^44 <= a /\ a + n <= 2^47);   (* [comment removed for export] *)
  art_stk_high : al_sb AL + 2^44 <= arl_stklo R;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  hcs_img : forall h a n, al_img_lo AL <= a -> a + n <= al_img_hi AL ->
      (a + n <= al_got AL - 63 \/ al_got AL + 64 <= a) -> (a + n <= al_gsb AL - 63 \/ al_gsb AL + 64 <= a) -> crange (hcs h) a n;
  (* [comment removed for export] *)
  hcs_hull64 : forall h x y, hcs h x -> x - x mod 64 <= y < x - x mod 64 + 64 -> hcs h y;
  hm_flag_img : forall h LB LF m, HM h LB LF m -> al_img_lo AL <= hflag h /\ hflag h + 4 <= al_img_hi AL;

  (* [comment removed for export] *)
  hm_abase : forall h LB LF m, HM h LB LF m -> abase segs AL m;
  hm_auar : forall h LB LF m, HM h LB LF m -> auar (hflag h) m;
  hm_rtc : forall h LB LF m, HM h LB LF m -> arl_rtc R m;
  (* [comment removed for export] *)
  hm_shadow_rd : forall h LB LF m c, HM h LB LF m -> hcs h c ->
      exists b, bytes_at segs m (shadow_of AL c) [b] /\ wr_at segs m (shadow_of AL c) 1;
  (* [comment removed for export] *)
  hm_img_shadow : forall h LB LF m, HM h LB LF m -> img_shadow_ok segs AL m;
  hm_aobj_block : forall h LB LF m A n, HM h LB LF m -> In (A, n) LB -> aobj segs AL (hcs h) m A n;
  hm_apart : forall h LB LF m, HM h LB LF m ->
      Forall (fun b => 0 < fst b /\ 0 <= snd b /\ fst b + snd b <= alloc_ceiling
                       /\ (fst b + snd b <= hl_img_lo L \/ hl_img_hi L <= fst b)) (LB ++ LF)
      /\ blocks_apart (LB ++ LF);
  (* [comment removed for export] *)
  hm_stack_readable : forall h LB LF m a, HM h LB LF m -> arl_stklo R <= a < hstkhi h -> wview segs m (wa a) <> None;
  hm_frame : forall h LB LF m m',
      HM h LB LF m ->
      (forall a, 0 <= a < 2^64 -> ~ hm_writable LB LF (htop h) a -> m' (wa a) = m (wa a)) ->
      wmono segs m m' -> HM h LB LF m';
  (* [comment removed for export] *)
  hm_stack_shadow_w : forall h LB LF m g, HM h LB LF m -> arl_stklo R <= g -> g + 8 <= hstkhi h -> g mod 8 = 0 ->
      wr_at segs m (shadow_of AL g) 1;

  (* [comment removed for export] *)
  hm_fake_free : forall h LB LF m FB n,
      HM h LB LF m -> In (FB, n) LF ->
      exists p h',
        ro_cells segs m (FB + n - 8) [C8 (Z_to_bv 64 p)]
        /\ (exists old, rw_cells segs m p [C1 old]) /\ crange (hcs h) p 1
        /\ (forall a, client_addr L (LB ++ fdata LF) (arl_stklo R) a -> a <> p)
        /\ (forall c, cshd LB LF (arl_stklo R) (hstkhi h) c -> shadow_of AL c <> p)
        /\ HM h' LB (lb_remove FB LF) (write_to_mem m (wa p) [Z_to_bv 8 0])
        /\ hcs h' = hcs h /\ htop h' = htop h /\ hstkhi h' = hstkhi h /\ hflag h' = hflag h /\ havol h' = havol h /\ hfr h' = hfr h
        /\ (forall mo, HK h' mo <-> HK h mo);

  (* [comment removed for export] *)

  heapA_malloc_t : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST) (LB LF : list blk) (n lo d : Z),
      HM h LB LF m -> HK h mo ->
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_malloc R ->
      bv_unsigned sp <= htop h -> bv_unsigned sp mod 16 = 0 ->
      mem_inv segs m -> tp = Z_to_bv 64 (arl_tp R) ->
      a0 = Z_to_bv 64 n -> 0 <= n < AMAX ->
      havol h + vchg n <= AVOL_MAX ->
      uwc segs m (arl_stklo R) (hstkhi h) (bv_unsigned s0) (bv_unsigned sp) d -> hfr h + fr_charge d <= FR_MAX ->   (* [comment removed for export] *)
      (win24 n = true -> cnt24 LB < C24MAX) ->                                             (* [comment removed for export] *)
      aevtS segs
        (fun c => exists ms' mo', c = mkCfg ms' mo' /\
           call_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' =>
             mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ mo_frame mo mo' /\ wmono segs m m'
             /\ presA LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi h) [] m m'
             /\ exists h', htop h' = htop h /\ hstkhi h' = hstkhi h /\ hflag h' = hflag h /\ HK h' mo'
                /\ (forall x, hcs h x -> hcs h' x)
                /\ havol h' <= havol h + vchg n /\ hfr h' <= hfr h + fr_charge d /\
                ( (r = Z_to_bv 64 0 /\ HM h' LB LF m')
                \/ (exists A junk, r = Z_to_bv 64 A /\ A mod 16 = 0 /\ fresh_apart LB LF A n
                     /\ (A + n <= arl_stklo R \/ hstkhi h <= A)
                     /\ HM h' ((A, n) :: LB) LF m'
                     /\ rw_cells segs m' A [CB (Z.to_nat n) junk]) )) ms')
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (arl_malloc R)) fc None m (seg_rom segs)) mo);

  heapA_calloc_t : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST) (LB LF : list blk) (cnt sz lo d : Z),
      HM h LB LF m -> HK h mo ->
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_malloc R ->
      bv_unsigned sp <= htop h -> bv_unsigned sp mod 16 = 0 ->
      mem_inv segs m -> tp = Z_to_bv 64 (arl_tp R) ->
      a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt -> 0 <= sz -> cnt * sz < AMAX ->
      havol h + vchg (cnt * sz) <= AVOL_MAX ->
      uwc segs m (arl_stklo R) (hstkhi h) (bv_unsigned s0) (bv_unsigned sp) d -> hfr h + fr_charge d <= FR_MAX ->   (* [comment removed for export] *)
      (win24 (cnt * sz) = true -> cnt24 LB < C24MAX) ->                                    (* [comment removed for export] *)
      aevtS segs
        (fun c => exists ms' mo', c = mkCfg ms' mo' /\
           call_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' =>
             mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ mo_frame mo mo' /\ wmono segs m m'
             /\ presA LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi h) [] m m'
             /\ exists h', htop h' = htop h /\ hstkhi h' = hstkhi h /\ hflag h' = hflag h /\ HK h' mo'
                /\ (forall x, hcs h x -> hcs h' x)
                /\ havol h' <= havol h + vchg (cnt * sz) /\ hfr h' <= hfr h + fr_charge d /\
                ( (r = Z_to_bv 64 0 /\ HM h' LB LF m')
                \/ (exists A, r = Z_to_bv 64 A /\ A mod 16 = 0 /\ fresh_apart LB LF A (cnt * sz)
                     /\ (A + cnt * sz <= arl_stklo R \/ hstkhi h <= A)
                     /\ HM h' ((A, cnt * sz) :: LB) LF m'
                     /\ rw_cells segs m' A [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]) )) ms')
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (arl_calloc R)) fc None m (seg_rom segs)) mo);

  heapA_free : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST) (LB LF : list blk) (A n lo d : Z),
      HM h LB LF m -> HK h mo -> In (A, n) LB ->
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_free R ->
      bv_unsigned sp <= htop h -> bv_unsigned sp mod 16 = 0 ->
      mem_inv segs m -> tp = Z_to_bv 64 (arl_tp R) ->
      a0 = Z_to_bv 64 A ->
      havol h + AVOL_CALL <= AVOL_MAX ->
      uwc segs m (arl_stklo R) (hstkhi h) (bv_unsigned s0) (bv_unsigned sp) d -> hfr h + fr_charge d <= FR_MAX ->   (* [comment removed for export] *)
      aevtS segs
        (fun c => exists ms' mo', c = mkCfg ms' mo' /\
           call_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun _ m' =>
             mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ mo_frame mo mo'   (* [comment removed for export] *)
             /\ presA (lb_remove A LB) LF (bv_unsigned sp) (arl_stklo R) (hstkhi h) [] m m'
             /\ exists h', htop h' = htop h /\ hstkhi h' = hstkhi h /\ hflag h' = hflag h /\ HK h' mo'
                /\ (forall x, hcs h x -> hcs h' x)            (* [comment removed for export] *)
                /\ havol h' <= havol h + AVOL_CALL /\ hfr h' <= hfr h + fr_charge d
                /\ HM h' (lb_remove A LB) LF m') ms')
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (arl_free R)) fc None m (seg_rom segs)) mo);

  (* [comment removed for export] *)
  heapA_free_null : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (h : HST) (LB LF : list blk) (lo : Z),
      HM h LB LF m ->
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_free R ->
      bv_unsigned sp <= htop h -> bv_unsigned sp mod 16 = 0 ->
      mem_inv segs m -> tp = Z_to_bv 64 (arl_tp R) ->
      a0 = Z_to_bv 64 0 ->
      evtA segs AL (hcs h)
        (call_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun _ m' =>
            mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ wmono segs m m'
            /\ presA LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi h) [] m m'
            /\ exists h', hcs h' = hcs h /\ htop h' = htop h /\ hstkhi h' = hstkhi h /\ hflag h' = hflag h
               /\ havol h' = havol h /\ hfr h' = hfr h /\ (forall mo, HK h' mo <-> HK h mo) /\ HM h' LB LF m'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (arl_free R)) fc None m (seg_rom segs));

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  artA_amemcpy : forall (entry : Z)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (h : HST) (LB LF : list blk) (DST SRC n lo : Z) (ds ss : list byte),
      (entry = arl_amemcpy R \/ entry = arl_memcpy_i R \/ entry = arl_amemmove R) ->
      HM h LB LF m ->
      u8arr segs m DST ds -> bytes_at segs m SRC ss -> Z.of_nat (length ds) = n -> Z.of_nat (length ss) = n ->
      aobj segs AL (hcs h) m DST n -> aobj segs AL (hcs h) m SRC n ->
      (n = 0 \/ DST + n <= SRC \/ SRC + n <= DST) ->
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_amem R ->
      crange (hcs h) lo (bv_unsigned sp - lo) -> mem_inv segs m ->
      (* [comment removed for export] *)
      (DST + n <= lo \/ bv_unsigned sp <= DST) -> (SRC + n <= lo \/ bv_unsigned sp <= SRC) ->
      (n = 0 \/ DST + n + 8 <= 2^47) -> (n = 0 \/ SRC + n + 8 <= 2^47) ->
      (* [comment removed for export] *)
      n < 2^40 -> client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop h) DST n -> bv_unsigned sp <= htop h ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 SRC -> a2 = Z_to_bv 64 n ->
      evtA segs AL (hcs h)
        (call_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' =>
            munch [(DST, DST + n); (lo, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
            /\ r = Z_to_bv 64 DST /\ u8arr segs m' DST ss /\ stk segs m' lo (bv_unsigned sp) /\ HM h LB LF m'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom segs));

  (* [comment removed for export] *)
  artA_amemset : forall (entry : Z)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (h : HST) (LB LF : list blk) (DST v n lo : Z) (ds : list byte),
      (entry = arl_amemset R \/ entry = arl_memset_i R) ->
      HM h LB LF m ->
      u8arr segs m DST ds -> Z.of_nat (length ds) = n -> aobj segs AL (hcs h) m DST n -> 0 <= v < 256 ->
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_amem R ->
      crange (hcs h) lo (bv_unsigned sp - lo) -> mem_inv segs m ->
      (DST + n <= lo \/ bv_unsigned sp <= DST) -> (n = 0 \/ DST + n + 8 <= 2^47) ->      (* [comment removed for export] *)
      n < 2^40 -> client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop h) DST n -> bv_unsigned sp <= htop h ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 v -> a2 = Z_to_bv 64 n ->
      evtA segs AL (hcs h)
        (call_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' =>
            munch [(DST, DST + n); (lo, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
            /\ r = Z_to_bv 64 DST /\ u8arr segs m' DST (repeat (Z_to_bv 8 v) (Z.to_nat n))
            /\ stk segs m' lo (bv_unsigned sp) /\ HM h LB LF m'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom segs));

  (* [comment removed for export] *)
  artA_bcmp : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (h : HST) (LB LF : list blk) (P Q n lo : Z) (ps qs : list byte),
      HM h LB LF m ->
      bytes_at segs m P ps -> bytes_at segs m Q qs -> Z.of_nat (length ps) = n -> Z.of_nat (length qs) = n ->
      aobj segs AL (hcs h) m P n -> aobj segs AL (hcs h) m Q n ->
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_bcmp R ->
      crange (hcs h) lo (bv_unsigned sp - lo) -> mem_inv segs m ->
      (P + n <= lo \/ bv_unsigned sp <= P) -> (Q + n <= lo \/ bv_unsigned sp <= Q) ->                      (* [comment removed for export] *)
      (n = 0 \/ P + n + 8 <= 2^47) -> (n = 0 \/ Q + n + 8 <= 2^47) ->
      n < 2^40 -> bv_unsigned sp <= htop h ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 Q -> a2 = Z_to_bv 64 n ->
      evtA segs AL (hcs h)
        (call_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' =>
            munch [(lo, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
            /\ (r = Z_to_bv 64 0 <-> ps = qs) /\ stk segs m' lo (bv_unsigned sp) /\ HM h LB LF m'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (arl_memcmp_i R)) fc None m (seg_rom segs));

  (* [comment removed for export] *)
  artA_set_shadow : forall (xx : Z)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (h : HST) (LB LF : list blk) (A s n lo : Z) (old : list cell),
      HM h LB LF m ->
      (xx = 0 \/ xx = 0xf5 \/ xx = 0xf8) ->
      A mod 8 = 0 -> 0 < n -> crange (hcs h) A (8 * n) -> s = shadow_of AL A ->
      (forall x, A <= x < A + 8 * n -> (arl_stklo R <= x < htop h) \/ in_block LF x) ->
      rw_cells segs m (Z.shiftr A 3 + al_sb AL) old -> Z.of_nat (cells_size old) = n ->
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_setsh R ->
      crange (hcs h) lo (bv_unsigned sp - lo) -> mem_inv segs m ->
      a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 n ->
      evtA segs AL (hcs h)
        (call_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun _ m' =>
            munch [(s, s + n); (lo, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
            /\ rw_cells segs m' (Z.shiftr A 3 + al_sb AL) [CB (Z.to_nat n) (repeat (Z_to_bv 8 xx) (Z.to_nat n))]
            /\ stk segs m' lo (bv_unsigned sp) /\ HM h LB LF m'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (if Z.eqb xx 0 then arl_set00 R else if Z.eqb xx 0xf5 then arl_setf5 R else arl_setf8 R))
            fc None m (seg_rom segs));

  (* [comment removed for export] *)
  art_rip : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (h : HST) (LB LF : list blk) (BEG n lo : Z),
      HM h LB LF m -> aobj segs AL (hcs h) m BEG n -> 0 <= n < 2^40 ->
      (n = 0 \/ BEG + n + 8 <= 2^47) ->                                                                      (* [comment removed for export] *)
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_rip R ->
      bv_unsigned sp <= htop h -> mem_inv segs m ->
      a0 = Z_to_bv 64 BEG -> a1 = Z_to_bv 64 n ->
      evtA segs AL (hcs h)
        (call_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' =>
            r = Z_to_bv 64 0 /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
            /\ stk segs m' lo (bv_unsigned sp) /\ HM h LB LF m'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (arl_rip R)) fc None m (seg_rom segs));

  (* [comment removed for export] *)
  art_smalloc : forall (k : Z)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (h : HST) (LB LF : list blk) (sz lo : Z),
      HM h LB LF m -> (length LF < 512)%nat ->
      0 <= k <= 5 -> 0 < sz <= 64 * 2^k ->
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_smalloc R ->
      bv_unsigned sp <= htop h ->
      mem_inv segs m -> tp = Z_to_bv 64 (arl_tp R) ->
      a0 = Z_to_bv 64 sz ->
      evtA segs AL (hcs h)
        (call_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' =>
            mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ wmono segs m m'
            /\ presA LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi h) [] m m'
            /\ exists h', hcs h' = hcs h /\ htop h' = htop h /\ hstkhi h' = hstkhi h /\ hflag h' = hflag h
               /\ havol h' = havol h /\ hfr h' = hfr h /\ (forall mo, HK h' mo <-> HK h mo) /\
               (exists FB junk, r = Z_to_bv 64 FB /\ FB mod 64 = 0
                    /\ fresh_apart LB LF FB (64 * 2^k)
                    /\ HM h' LB ((FB, 64 * 2^k) :: LF) m'
                    (* [comment removed for export] *)
                    /\ rw_cells segs m' FB [CB (Z.to_nat (64 * 2^k)) junk]
                    /\ rw_cells segs m' (Z.shiftr FB 3 + al_sb AL) (zcells (Z.to_nat (8 * 2^k)))) ))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (arl_smalloc R k)) fc None m (seg_rom segs));

  (* [comment removed for export] *)
  art_sfree5 : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (h : HST) (LB LF : list blk) (FB sz lo : Z) (old : list cell),
      HM h LB LF m -> In (FB, 2048) LF ->
      rw_cells segs m (Z.shiftr FB 3 + al_sb AL) old -> cells_size old = 256%nat ->
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_smalloc R ->
      crange (hcs h) lo (bv_unsigned sp - lo) -> mem_inv segs m ->
      a0 = Z_to_bv 64 FB -> a1 = Z_to_bv 64 sz ->
      evtA segs AL (hcs h)
        (call_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun _ m' =>
            mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ wmono segs m m'
            /\ presA LB (lb_remove FB LF) (bv_unsigned sp) (arl_stklo R) (hstkhi h) [] m m'
            /\ exists h', hcs h' = hcs h /\ htop h' = htop h /\ hstkhi h' = hstkhi h /\ hflag h' = hflag h
               /\ havol h' = havol h /\ hfr h' = hfr h /\ (forall mo, HK h' mo <-> HK h mo)
               /\ HM h' LB (lb_remove FB LF) m'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (arl_sfree5 R)) fc None m (seg_rom segs))
}.

(* [comment removed for export] *)
#[using="Type"] Lemma heapA_malloc : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Pra,(=.&40.)Psp,(=.&40.)Pgp,(=.&40.)Ptp,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Ps0,(=.&40.)Ps1,(=.&40.)Pa0,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Ps2,(=.&40.)Ps3,(=.&40.)Ps4,(=.&40.)Ps5,(=.&40.)Ps6,(=.&40.)Ps7,(=.&40.)Ps8,(=.&40.)Ps9,(=.&40.)Ps10,(=.&40.)Ps11,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)PF,(59.&5.(=.&40.))Pfc,(=.&20.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$5:.Ph,(5;.R24.)PLB,(15.$35.)PLF,(15.$35.)Pn,$2.Plo,$2.Pd,$2.P,(5<.R2:.R6.R5.R4.R8.)P,(5=.R2;.R7.R8.)P,(4;.Vsegs,R:.R4.(5>.&40.R2:.))P,(4.(51.VR,)R5.)P,(4.R6.(18.(5>.&40.R2<.)(5?.VR,)))P,(4.(5>.&40.R2=.)(60.R2?.R;.))P,(1.$2.(3.(5>.&40.R2>.)+10.)=)P,(61.Vsegs,R?.)P,(1.(=.&40.)R2>.(;.&40.(62.VR,)))P,(1.(=.&40.)R29.(;.&40.R<.))P,(0.(4.=R=.)(1=.R=.$63.))P,(4.(5.(64.R35.R11.)(5.(11.+2.R>.)$65.))$66.)P,(67.Vsegs,R14.(51.VR,)(68.R36.R12.)(5>.&40.R2>.)(5>.&40.R34.)R=.)P,(4.(5.(69.R37.R13.)(6:.R>.))$6;.)P,P,(1.$6<.(6=.R11.)$6>.)(1=.(6?.R14.)$70.)(71.Vsegs,Lc,$72.(3<.$53.Lms',$53.(3<.$5:.Lmo',$5:.(0.(1.$72.R3.(73.R2.R1.))(74.R3;.R3:.R39.R38.R34.R33.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1<.R1;.Lr,(=.&40.)Lm',P,(=.&40.)(>.(=.&8.))(0.(61.Vsegs,R1.)(0.(4;.Vsegs,R1.R16.(5>.&40.R3<.))(0.(75.R1;.R3.)(0.(23.Vsegs,R1<.R1.)(0.(3:.R19.R18.(5>.&40.R3<.)(51.VR,)(68.R3>.R1:.)(<.$20.)R1<.R1.)(3<.(5;.R3>.)Lh',(5;.R3>.)(0.(1.$2.(60.R3?.R1.)(60.R3?.R1;.))(0.(1.$2.(68.R3?.R1.)(68.R3?.R1;.))(0.(1.$2.(76.R3?.R1.)(76.R3?.R1;.))(0.(5=.R3?.R1.R4.)(0.Px,$2.P,(77.R40.R1<.R1.)(77.R41.R3.R2.)(0.(4.(64.R3?.R1.)(5.(64.R3?.R1;.)(5.(11.+2.R18.)$65.)))(0.(4.(69.R3?.R1.)(5.(69.R3?.R1;.)(6:.R16.)))(1?.(0.(1.(=.&40.)R3.(;.&40.=))(5<.R3?.R1.R1:.R19.R2.))(3<.$2.LA,$2.(3<.(15.(=.&8.))Ljunk,(15.(=.&8.))(0.(1.(=.&40.)R5.(;.&40.R2.))(0.(1.$2.(3.R2.+10.)=)(0.(42.R1<.R1;.R2.R1:.)(0.(1?.(4.(5.R2.R1:.)(51.VR,))(4.(68.R41.R1=.)R2.))(0.(5<.R41.R3.(8.(25.$2.$2.)(41.$2.$2.R2.R1:.)R1<.)R1;.R4.)(6.Vsegs,R4.R2.(8.$9.(78.(79.R1:.)R1.)(<.$9.))))))))))))))))))))))))R2.))))(73.(54.(55.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(;.&40.(7:.VR,))R18.(39.(=.&40.))R17.(57.Vsegs,))R16.))")
(* [comment removed for export] *).
Proof.
  intros HIA. intros until d. intros HH HKK ST LOS SLO TOP SPA MI TPV EA0 NB BUD UW BUDF C24.
  eapply aevtS_mono.
  - eapply (heapA_malloc_t HIA); try eassumption. pose proof (vchg_le n ltac:(lia)). lia.
  - intros c (ms' & mo' & E & PO). exists ms', mo'. split; [exact E|].
    unfold call_postA in *. destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E2 & PO).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E2|].
    destruct PO as (Q1 & Q2 & Q3 & Q4 & Q5 & h' & R1 & R2 & R3 & R4 & R5 & R6 & R7).
    refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 _))))). exists h'.
    refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj _ R7)))))).
    pose proof (vchg_le n ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma heapA_calloc : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Pra,(=.&40.)Psp,(=.&40.)Pgp,(=.&40.)Ptp,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Ps0,(=.&40.)Ps1,(=.&40.)Pa0,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Ps2,(=.&40.)Ps3,(=.&40.)Ps4,(=.&40.)Ps5,(=.&40.)Ps6,(=.&40.)Ps7,(=.&40.)Ps8,(=.&40.)Ps9,(=.&40.)Ps10,(=.&40.)Ps11,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)PF,(59.&5.(=.&40.))Pfc,(=.&20.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$5:.Ph,(5;.R24.)PLB,(15.$35.)PLF,(15.$35.)Pcnt,$2.Psz,$2.Plo,$2.Pd,$2.P,(5<.R2;.R7.R6.R5.R9.)P,(5=.R2<.R8.R9.)P,(4;.Vsegs,R;.R4.(5>.&40.R2;.))P,(4.(51.VR,)R5.)P,(4.R6.(18.(5>.&40.R2=.)(5?.VR,)))P,(4.(5>.&40.R2>.)(60.R30.R<.))P,(1.$2.(3.(5>.&40.R2?.)+10.)=)P,(61.Vsegs,R10.)P,(1.(=.&40.)R2?.(;.&40.(62.VR,)))P,(1.(=.&40.)R2:.(;.&40.R=.))P,(1.(=.&40.)R2:.(;.&40.R=.))P,(4.=R?.)P,(4.=R?.)P,(1=.(11.R11.R10.)$63.)P,(4.(5.(64.R39.R15.)(5.(11.+2.(11.R12.R11.))$65.))$66.)P,(67.Vsegs,R18.(51.VR,)(68.R3:.R16.)(5>.&40.R32.)(5>.&40.R38.)R10.)P,(4.(5.(69.R3;.R17.)(6:.R11.))$6;.)P,P,(1.$6<.(6=.(11.R15.R14.))$6>.)(1=.(6?.R18.)$70.)(71.Vsegs,Lc,$72.(3<.$53.Lms',$53.(3<.$5:.Lmo',$5:.(0.(1.$72.R3.(73.R2.R1.))(74.R3?.R3>.R3=.R3<.R38.R37.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R20.R1?.Lr,(=.&40.)Lm',P,(=.&40.)(>.(=.&8.))(0.(61.Vsegs,R1.)(0.(4;.Vsegs,R1.R19.(5>.&40.R40.))(0.(75.R1?.R3.)(0.(23.Vsegs,R20.R1.)(0.(3:.R1=.R1<.(5>.&40.R40.)(51.VR,)(68.R42.R1>.)(<.$20.)R20.R1.)(3<.(5;.R42.)Lh',(5;.R42.)(0.(1.$2.(60.R43.R1.)(60.R43.R1?.))(0.(1.$2.(68.R43.R1.)(68.R43.R1?.))(0.(1.$2.(76.R43.R1.)(76.R43.R1?.))(0.(5=.R43.R1.R4.)(0.Px,$2.P,(77.R44.R20.R1.)(77.R45.R3.R2.)(0.(4.(64.R43.R1.)(5.(64.R43.R1?.)(5.(11.+2.(11.R1<.R1;.))$65.)))(0.(4.(69.R43.R1.)(5.(69.R43.R1?.)(6:.R19.)))(1?.(0.(1.(=.&40.)R3.(;.&40.=))(5<.R43.R1.R1>.R1=.R2.))(3<.$2.LA,$2.(0.(1.(=.&40.)R4.(;.&40.R1.))(0.(1.$2.(3.R1.+10.)=)(0.(42.R1?.R1>.R1.(11.R1=.R1<.))(0.(1?.(4.(5.R1.(11.R1=.R1<.))(51.VR,))(4.(68.R44.R20.)R1.))(0.(5<.R44.R2.(8.(25.$2.$2.)(41.$2.$2.R1.(11.R1=.R1<.))R1?.)R1>.R3.)(6.Vsegs,R3.R1.(8.$9.(78.(79.(11.R1=.R1<.))(7;.(=.&8.)(;.&8.=)(79.(11.R1=.R1<.))))(<.$9.)))))))))))))))))))))))R2.))))(73.(54.(55.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(;.&40.(7<.VR,))R1<.(39.(=.&40.))R1;.(57.Vsegs,))R1:.))")
(* [comment removed for export] *).
Proof.
  intros HIA. intros until d. intros HH HKK ST LOS SLO TOP SPA MI TPV EA0 EA1 C0 S0 CSB BUD UW BUDF C24.
  eapply aevtS_mono.
  - eapply (heapA_calloc_t HIA); try eassumption. pose proof (vchg_le (cnt * sz) ltac:(lia)). lia.
  - intros c (ms' & mo' & E & PO). exists ms', mo'. split; [exact E|].
    unfold call_postA in *. destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E2 & PO).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E2|].
    destruct PO as (Q1 & Q2 & Q3 & Q4 & Q5 & h' & R1 & R2 & R3 & R4 & R5 & R6 & R7).
    refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 _))))). exists h'.
    refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj _ R7)))))).
    pose proof (vchg_le (cnt * sz) ltac:(lia)). lia.
Qed.


(* [comment removed for export] *)
Definition AIh (HIA : artA) (h : HST HIA) (CS : Z -> Prop) (mo : Model) : Prop :=
  HK HIA h mo /\ (forall x, CS x -> hcs HIA h x).

#[using="Type"] Lemma AIh_laws : forall (HIA : artA) h, ainv_laws AL (AIh HIA h).
Proof.
  intros HIA h. split.
  - intros CS mo [H _]. eapply hk_halted; exact H.
  - intros CS mo acc [H HS] OK.
    destruct (hk_mat HIA h mo acc H (acc_ok_mono AL CS (hcs HIA h) acc HS OK)) as (mo' & E & H' & MM).
    exists mo'. split; [exact E|]. split; [split; assumption| exact MM].
  - intros CS CS' mo HS [H H1]. split; [exact H|]. intros x Hx. apply H1, HS, Hx.
Qed.

#[using="Type"] Lemma AIh_kinv : forall (HIA : artA) h, kinv_laws (AIh HIA h) (hcs HIA h) (HK HIA h).
Proof.
  intros HIA h. split.
  - intros mo H. split; [exact H| auto].
  - intros mo mo' _ [H _] _. exact H.
Qed.

(* [comment removed for export] *)
Definition KF (HIA : artA) (h : HST HIA) (mo0 : Model) (mo : Model) : Prop :=
  HK HIA h mo /\ mo_frame mo0 mo.

#[using="Type"] Lemma mo_mat_frame : forall a b, mo_mat a b -> mo_frame a b.
Proof. unfold mo_mat, mo_frame; intros a b H; intuition congruence. Qed.

#[using="Type"] Lemma KF_kinv : forall (HIA : artA) h mo0, kinv_laws (AIh HIA h) (hcs HIA h) (KF HIA h mo0).
Proof.
  intros HIA h mo0. split.
  - intros mo [H _]. split; [exact H| auto].
  - intros mo mo' [_ F0] [H _] MM. split; [exact H|]. eapply mo_frame_trans; [exact F0| apply mo_mat_frame, MM].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aevtA_step_HK : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PQ,P,$72.SpPms,$53.Pms1,$53.Pacc,(15.$7=.)P,(0.(1.(>.(=.&40.))(7>.R3.)(39.(=.&40.)))(1.(7?.(80.$53.))(81.Vsegs,R3.)(82.(80.$53.)(83.$53.R2.R1.))))P,(84.VAL,(77.R7.R6.)R2.)P,(85.Vsegs,(5=.R8.R7.)R6.R4.)(85.Vsegs,(5=.R9.R8.)R7.R6.)")
(* [comment removed for export] *).
Proof. intros HIA h Q ms ms1 acc H OK K. eapply (aevtA_step segs AL (AIh HIA h) (AIh_laws HIA h)); eauto using AIh_kinv. Qed.

#[using="Type"] Lemma aevtA_step_KF : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)Pmo0,$5:.PQ,P,$72.SpPms,$53.Pms1,$53.Pacc,(15.$7=.)P,(0.(1.(>.(=.&40.))(7>.R3.)(39.(=.&40.)))(1.(7?.(80.$53.))(81.Vsegs,R3.)(82.(80.$53.)(83.$53.R2.R1.))))P,(84.VAL,(77.R8.R7.)R2.)P,(85.Vsegs,(86.R9.R8.R7.)R6.R4.)(85.Vsegs,(86.R:.R9.R8.)R7.R6.)")
(* [comment removed for export] *).
Proof. intros HIA h mo0 Q ms ms1 acc H OK K. eapply (aevtA_step segs AL (AIh HIA h) (AIh_laws HIA h)); eauto using KF_kinv. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma aevtA_cut_evtA_HK : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PP,P,$53.SpPQ,P,$72.SpPms,$53.P,(87.Vsegs,VAL,(77.R5.R4.)R3.R1.)P,Pms',$53.P,A1.R5.R1.(85.Vsegs,(5=.R8.R7.)R5.R2.)(85.Vsegs,(5=.R7.R6.)R4.R3.)")
(* [comment removed for export] *).
Proof. intros HIA h P Q ms H K. eapply (aevtA_cut_evtA segs AL (AIh HIA h) (AIh_laws HIA h)); eauto using AIh_kinv. Qed.

#[using="Type"] Lemma aevtA_cut_evtA_KF : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)Pmo0,$5:.PP,P,$53.SpPQ,P,$72.SpPms,$53.P,(87.Vsegs,VAL,(77.R6.R5.)R3.R1.)P,Pms',$53.P,A1.R5.R1.(85.Vsegs,(86.R9.R8.R7.)R5.R2.)(85.Vsegs,(86.R8.R7.R6.)R4.R3.)")
(* [comment removed for export] *).
Proof. intros HIA h mo0 P Q ms H K. eapply (aevtA_cut_evtA segs AL (AIh HIA h) (AIh_laws HIA h)); eauto using KF_kinv. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aevtA_call : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PK,P,$5:.SpPPmo,P,$5:.P,$72.SpPQ,P,$72.SpPms,$53.P,Pmo,$5:.P,A1.R5.R1.(71.Vsegs,A1.R5.R2.(73.R3.R2.))P,Pms',$53.Pmo',$5:.P,(3<.$5:.Lmo1,$5:.(0.A1.R8.R1.A2.R7.R1.(73.R3.R2.)))(71.Vsegs,R6.(73.R3.R2.))(85.Vsegs,R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros K Pmo Q ms HC HK mo Hmo. eapply aevtS_bind; [apply HC, Hmo|].
  intros [ms' mo'] HP. apply HK. exists mo. split; [exact Hmo| exact HP].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hm_write : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)Pm,P,(=.&40.)(>.(=.&8.))Pa,$2.Pbs,(15.(=.&8.))P,(5<.R7.R6.R5.R4.R3.)P,(88.VL,(34.$35.R6.(36.R5.))(51.VR,)(60.R8.R7.)R3.(12.(19.(=.&8.)R2.)))P,(4.=R4.)P,(4.(5.R5.(12.(19.(=.&8.)R4.)))(1:.+2.+40.))(5<.R;.R:.R9.R8.(1;.R7.(1<.R6.)R5.))")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF m a bs HH HW Ha Hl. eapply (hm_frame HIA); [exact HH| | apply wmono_write, wmono_refl].
  intros x Hx NW. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
  exfalso. apply NW. left. apply HW. lia.
Qed.

#[using="Type"] Lemma hm_write_shadow : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)Pm,P,(=.&40.)(>.(=.&8.))Pc,$2.Pa,$2.Pbs,(15.(=.&8.))P,(5<.R8.R7.R6.R5.R4.)P,Px,$2.P,(0.(4.R5.R1.)(1=.R1.(5.R5.(11.+8.(12.(19.(=.&8.)R3.))))))(1?.(0.(4.(51.VR,)R2.)(1=.R2.(60.R;.R:.)))(52.R8.R2.))P,(1.$2.R4.(7.VAL,R5.))P,(4.=R5.)P,(4.(5.R6.(12.(19.(=.&8.)R5.)))(1:.+2.+40.))(5<.R=.R<.R;.R:.(1;.R9.(1<.R7.)R6.))")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF m c a bs HH HW -> Ha Hl. eapply (hm_frame HIA); [exact HH| | apply wmono_write, wmono_refl].
  intros x Hx NW. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 (shadow_of AL c) x); destruct (Z.ltb_spec0 x (shadow_of AL c + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
  exfalso. apply NW. right. exists (c + 8 * (x - shadow_of AL c)). split; [apply HW; lia|].
  rewrite shadow_of_plus. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma w_writable_of_client_wrange : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PTOP,$2.Plo,$2.Phi,$2.P,(88.VL,(34.$35.R5.(36.R4.))(51.VR,)R3.R2.(18.R1.R2.))Pa,$2.P,(0.(4.R4.R1.)(1=.R1.R3.))(89.R8.R7.R6.R2.)")
(* [comment removed for export] *).
Proof. intros LB LF TOP lo hi H a Ha. left. apply H. lia. Qed.

#[using="Type"] Lemma hm_munch : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PW,(15.$20.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))P,(5<.R7.R6.R5.R4.R2.)P,(22.R4.R3.R2.)P,(23.Vsegs,R4.R3.)P,(24.(25.$2.$2.)Liv,(25.$2.$2.)Pa,$2.P,(0.(4.(26.$2.$2.R2.)R1.)(1=.R1.(27.$2.$2.R2.)))(89.R;.R:.(60.R=.R<.)R2.)R6.)(5<.R;.R:.R9.R8.R5.)")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF W m m' HH MU WM HW. eapply (hm_frame HIA); [exact HH| | exact WM].
  intros a Ha NW. apply MU. rewrite wa_unsigned by lia.
  clear - HW NW. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in H1.
  split; [| apply IH; assumption]. intros Hr. apply NW. apply H1. exact Hr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma alloc_ceiling_val : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. exact alloc_ceiling_bounds. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hm_blocks_low : forall (HIA : artA) h LB LF m, HM HIA h LB LF m -> blocks_low LB LF.
Proof.
  intros HIA h LB LF m HH B j HIn. destruct (hm_apart HIA h LB LF m HH) as [HF _].
  rewrite Forall_forall in HF. destruct (HF (B, j) HIn) as (_ & _ & H & _). exact H.
Qed.

#[using="Type"] Lemma hm_blocks_cs : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)Pm,P,(=.&40.)(>.(=.&8.))P,(5<.R5.R4.R3.R2.R1.)PB,$2.Pj,$2.P,(3;.(25.$2.$2.)(41.$2.$2.R2.R1.)(34.$35.R6.(36.R5.)))(17.(77.R9.R8.)R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF m HH B j HIn. apply in_app_iff in HIn. destruct HIn as [HIn|HIn].
  - eapply hcs_block; eauto.
  - intros x Hx. destruct (in_fdata_hull LF (B, j) x HIn Hx) as ([FB n] & H1 & H2). cbn in H2.
    replace x with (FB + (x - FB)) by lia. eapply (hcs_fake HIA h LB LF m FB n HH H1). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cshd_hcs : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)Pm,P,(=.&40.)(>.(=.&8.))PSSP,$2.Pc,$2.P,(5<.R7.R6.R5.R4.R3.)P,(4.(51.VR,)R3.)P,(37.R7.R6.R4.(68.R9.R8.)R3.)(77.R:.R9.R4.)")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF m SSP c HH HS [Hs|[([B j] & Hb & Hr)|[([B j] & Hb & Hr)|Hc]]]; cbn in *.
  - replace c with (arl_stklo R + (c - arl_stklo R)) by lia. apply (hcs_stack HIA h). lia.
  - replace c with (B + (c - B)) by lia. eapply (hcs_block HIA h LB LF m B j HH Hb). lia.
  - replace c with (B + (c - B)) by lia. eapply (hcs_fake HIA h LB LF m B j HH Hb). lia.
  - apply (hcs_static HIA h). exact Hc.
Qed.

(* [comment removed for export] *)
Definition presW (HIA : artA) (h : HST HIA) (LB LF : list blk) (SP SSP : Z) (W : list ivl) (m0 m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_ARt ()) "(0.(3:.O7.O6.O5.O4.(68.O9.O8.)O3.O2.O1.)(0.Pc,$2.P,(37.O7.O6.O4.(68.O9.O8.)R1.)(77.O9.O8.R2.)(0.PB,$2.Pj,$2.P,(3;.(25.$2.$2.)(41.$2.$2.R2.R1.)(34.$35.O7.(36.O6.)))(17.(77.O9.O8.)R3.R2.)(44.O7.O6.))))")
(* [comment removed for export] *).

#[using="Type"] Lemma presW_init : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)Pm,P,(=.&40.)(>.(=.&8.))PSP,$2.PSSP,$2.PW,(15.$20.)P,(5<.R8.R7.R6.R5.R4.)P,(4.(51.VR,)R3.)(8:.R:.R9.R8.R7.R5.R4.R3.R6.R6.)")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF m SP SSP W HH HS. split; [apply presA_refl|]. split; [intros c Hc; eapply cshd_hcs; eauto|].
  split; [eapply hm_blocks_cs; exact HH| eapply hm_blocks_low; exact HH].
Qed.

#[using="Type"] Lemma presW_presA : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))P,(8:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(3:.R8.R7.R6.R5.(68.R:.R9.)R4.R3.R2.)")
(* [comment removed for export] *).
Proof. intros HIA h LB LF SP SSP W m0 m [H _]; exact H. Qed.

#[using="Type"] Lemma presW_store_client : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pa,$2.Pbs,(15.(=.&8.))P,(8:.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(17.(77.R<.R;.)R3.(12.(19.(=.&8.)R2.)))P,(4.=R4.)P,(4.(5.R5.(12.(19.(=.&8.)R4.)))(1:.+2.+40.))P,(45.R=.R<.R;.R9.R6.(12.(19.(=.&8.)R5.)))(8:.R10.R?.R>.R=.R<.R;.R:.R9.(1;.R8.(1<.R7.)R6.))")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF SP SSP W m0 m a bs (P & C1 & C2 & C3) HC Ha Hl HW. split; [| split; [exact C1| split; [exact C2| exact C3]]].
  eapply presA_store_client; eauto using hcs_ok.
Qed.

#[using="Type"] Lemma presW_store_shadow : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pc,$2.Pa,$2.Pbs,(15.(=.&8.))P,(8:.R<.R;.R:.R9.R8.R7.R6.R5.R4.)P,(4.(3>.VL,)R9.)P,(1.$2.R4.(7.VAL,R5.))P,(1.$2.(3.R6.+8.)=)P,(17.(77.R10.R?.)R7.(11.+8.(12.(19.(=.&8.)R5.))))P,(46.R?.R>.R<.(68.R11.R10.)R8.(11.+8.(12.(19.(=.&8.)R6.))))(8:.R12.R11.R10.R?.R>.R=.R<.R;.(1;.R:.(1<.R8.)R7.))")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF SP SSP W m0 m c a bs (P & C1 & C2 & C3) HSP Ha Hc HC HF. split; [| split; [exact C1| split; [exact C2| exact C3]]].
  eapply presA_store_shadow; eauto using hcs_ok. apply (hcs_shadow_band HIA).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma presW_store_cov : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pa,$2.Pbs,(15.(=.&8.))PA,$2.Pn,$2.P,(8:.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(17.(77.R>.R=.)R5.(12.(19.(=.&8.)R4.)))P,(4.=R6.)P,(4.(5.R7.(12.(19.(=.&8.)R6.)))(1:.+2.+40.))P,(45.R?.R>.R=.R;.R6.R5.)P,(4.R7.R9.)P,(4.(5.R:.(12.(19.(=.&8.)R9.)))(5.R8.R7.))(8:.R14.R13.R12.R11.R10.R?.R>.R=.(1;.R<.(1<.R;.)R:.))")
(* [comment removed for export] *).
Proof. intros. eapply presW_store_client; eauto. eapply wcover_sub; eauto. Qed.

#[using="Type"] Lemma presW_store_out : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pa,$2.Pbs,(15.(=.&8.))P,(8:.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(17.(77.R<.R;.)R3.(12.(19.(=.&8.)R2.)))P,(4.=R4.)P,(4.(5.R5.(12.(19.(=.&8.)R4.)))(1:.+2.+40.))P,(8;.R9.R6.(12.(19.(=.&8.)R5.)))(8:.R10.R?.R>.R=.R<.R;.R:.R9.(1;.R8.(1<.R7.)R6.))")
(* [comment removed for export] *).
Proof. intros. eapply presW_store_client; eauto. apply wcover_inside; assumption. Qed.

#[using="Type"] Lemma presW_store_stack : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pa,$2.Pbs,(15.(=.&8.))P,(8:.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(17.(77.R<.R;.)R3.(12.(19.(=.&8.)R2.)))P,(4.=R4.)P,(4.(5.R5.(12.(19.(=.&8.)R4.)))(1:.+2.+40.))P,(4.(3>.VL,)R6.)P,(4.(5.R7.(12.(19.(=.&8.)R6.)))R<.)(8:.R11.R10.R?.R>.R=.R<.R;.R:.(1;.R9.(1<.R8.)R7.))")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF SP SSP W m0 m a bs HP HC Ha Hl H1 H2. eapply presW_store_client; eauto.
  destruct HP as (_ & _ & _ & BL). eapply wcover_stack; eauto using art_data_lo.
Qed.

#[using="Type"] Lemma presW_store_fresh : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pa,$2.Pbs,(15.(=.&8.))PN,$2.Pk,$2.P,(8:.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(17.(77.R>.R=.)R5.(12.(19.(=.&8.)R4.)))P,(4.=R6.)P,(4.(5.R7.(12.(19.(=.&8.)R6.)))(1:.+2.+40.))P,(42.R?.R>.R6.R5.)P,(4.R7.R9.)P,(4.(5.R:.(12.(19.(=.&8.)R9.)))(5.R8.R7.))P,(4.(3>.VL,)R10.)(8:.R15.R14.R13.R12.R11.R10.R?.R>.(1;.R=.(1<.R<.)R;.))")
(* [comment removed for export] *).
Proof. intros. eapply presW_store_client; eauto. eapply wcover_fresh; eauto. Qed.

#[using="Type"] Lemma presW_store_shadow_cov : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pc,$2.Pa,$2.Pbs,(15.(=.&8.))PC,$2.Pn,$2.P,(8:.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(4.(3>.VL,)R;.)P,(1.$2.R6.(7.VAL,R7.))P,(1.$2.(3.R8.+8.)=)P,(17.(77.R12.R11.)R9.(11.+8.(12.(19.(=.&8.)R7.))))P,(46.R11.R10.R>.(68.R13.R12.)R7.R6.)P,(4.R8.R;.)P,(4.(5.R<.(11.+8.(12.(19.(=.&8.)R:.))))(5.R9.R8.))(8:.R16.R15.R14.R13.R12.R11.R10.R?.(1;.R>.(1<.R<.)R;.))")
(* [comment removed for export] *).
Proof. intros. eapply presW_store_shadow; eauto. eapply shadow_free_sub; eauto. Qed.

#[using="Type"] Lemma presW_store_shadow_stack : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pc,$2.Pa,$2.Pbs,(15.(=.&8.))P,(8:.R<.R;.R:.R9.R8.R7.R6.R5.R4.)P,(4.(3>.VL,)R9.)P,(1.$2.R4.(7.VAL,R5.))P,(1.$2.(3.R6.+8.)=)P,(17.(77.R10.R?.)R7.(11.+8.(12.(19.(=.&8.)R5.))))P,(4.(3>.VL,)R8.)P,(4.(5.R9.(11.+8.(12.(19.(=.&8.)R7.))))R=.)(8:.R13.R12.R11.R10.R?.R>.R=.R<.(1;.R;.(1<.R9.)R8.))")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF SP SSP W m0 m c a bs HP HSP Ha Hc HC H1 H2. eapply presW_store_shadow; eauto.
  destruct HP as (_ & _ & _ & BL). eapply shadow_free_stack; eauto using art_data_lo.
Qed.

#[using="Type"] Lemma presW_store_shadow_fresh : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pc,$2.Pa,$2.Pbs,(15.(=.&8.))PN,$2.Pk,$2.P,(8:.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(4.(3>.VL,)R;.)P,(1.$2.R6.(7.VAL,R7.))P,(1.$2.(3.R8.+8.)=)P,(17.(77.R12.R11.)R9.(11.+8.(12.(19.(=.&8.)R7.))))P,(42.R11.R10.R7.R6.)P,PB,$2.Pj,$2.P,(3;.(25.$2.$2.)(41.$2.$2.R2.R1.)R13.)(1?.(4.(5.R;.R:.)R3.)(4.(5.R3.R2.)R;.))P,(4.R9.R<.)P,(4.(5.R=.(11.+8.(12.(19.(=.&8.)R;.))))(5.R:.R9.))P,(4.(3>.VL,)R12.)(8:.R18.R17.R16.R15.R14.R13.R12.R11.(1;.R10.(1<.R>.)R=.))")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF SP SSP W m0 m c a bs N k HP HSP Ha Hc HC HF HAP H1 H2 H3. eapply presW_store_shadow; eauto.
  destruct HP as (_ & _ & _ & BL). eapply shadow_free_fresh; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wcover_of_stack : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pa,$2.Pn,$2.P,(8:.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4.(3>.VL,)R3.)P,(4.(5.R4.R3.)R9.)(45.R<.R;.R:.R8.R5.R4.)")
(* [comment removed for export] *).
Proof. intros HIA h LB LF SP SSP W m0 m a n (_ & _ & _ & BL) H1 H2. eapply wcover_stack; eauto using art_data_lo. Qed.

#[using="Type"] Lemma shadow_free_of_stack : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pc,$2.Pn,$2.P,(8:.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4.(3>.VL,)R3.)P,(4.(5.R4.R3.)R8.)(46.R<.R;.R9.(68.R>.R=.)R5.R4.)")
(* [comment removed for export] *).
Proof. intros HIA h LB LF SP SSP W m0 m c n (_ & _ & _ & BL) H1 H2. eapply shadow_free_stack; eauto using art_data_lo. Qed.

#[using="Type"] Lemma hm_fresh_frame_apart : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.(25.$2.$2.))Pm,P,(=.&40.)(>.(=.&8.))PFB,$2.Pn,$2.P,(5<.R7.R6.R5.(8.(25.$2.$2.)(41.$2.$2.R2.R1.)R4.)R3.)PB,$2.Pj,$2.P,(3;.(25.$2.$2.)(41.$2.$2.R2.R1.)R7.)(1?.(4.(5.R6.R5.)R3.)(4.(5.R3.R2.)R6.))")
(* [comment removed for export] *).
Proof. intros HIA h LB LF m FB n HH. destruct (hm_apart HIA h LB _ m HH) as [_ BA]. eapply blocks_apart_mid; exact BA. Qed.

#[using="Type"] Lemma shadow_free_of_fresh : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)Ph1,(5;.R2.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pm1,P,(=.&40.)(>.(=.&8.))PFB,$2.Pn,$2.Pc,$2.Pk,$2.P,(8:.R?.R>.R<.R;.R:.R9.R8.R7.R6.)P,(42.R=.R<.R5.R4.)P,(5<.R11.R?.R>.(8.(25.$2.$2.)(41.$2.$2.R6.R5.)R=.)R7.)P,(4.R7.R5.)P,(4.(5.R6.R5.)(5.R8.R7.))P,(4.(3>.VL,)R>.)(46.R12.R11.R?.(68.R15.R14.)R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros HIA h h1 LB LF SP SSP W m0 m m1 FB n c k (_ & _ & _ & BL) HF HH H1 H2 H3.
  eapply shadow_free_fresh; eauto. eapply hm_fresh_frame_apart; exact HH.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nc_apart : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLBF,(15.$35.)PLBF',(15.$35.)PSP,$2.PSP',$2.Pp,$2.PA,$2.Pn,$2.P,Pa,$2.P,(8<.VL,R7.R5.R1.)(1>.(1.$2.R2.R5.))P,(43.VL,R8.R6.R3.R2.)P,Pb,$35.P,(3;.$35.R1.R:.)(3;.$35.R2.R:.)P,(4.R7.R8.)P,(1=.=R5.)(1?.(4.(5.R7.R6.)R8.)(4.(5.R8.+1.)R7.))")
(* [comment removed for export] *).
Proof.
  intros LBF LBF' SP SP' p A n NC CR SUB HS Hn.
  destruct (Z_lt_le_dec p A); [right; lia|]. destruct (Z_lt_le_dec p (A + n)); [| left; lia].
  exfalso. apply (NC p); [| reflexivity].
  destruct (CR p ltac:(lia)) as [X|[X|(b & Hb & Hr)]]; [left; lia| right; left; exact X| right; right; exists b; split; [apply SUB, Hb| exact Hr]].
Qed.
#[using="Type"] Lemma nc_apart0 : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLBF,(15.$35.)PLBF',(15.$35.)PSP,$2.PSP',$2.Pp,$2.PA,$2.Pn,$2.P,Pa,$2.P,(8<.VL,R7.R5.R1.)(1>.(1.$2.R2.R5.))P,(43.VL,R8.R6.R3.R2.)P,Pb,$35.P,(3;.$35.R1.R:.)(3;.$35.R2.R:.)P,(4.R7.R8.)(1?.(1.$2.R5.=)(1?.(4.(5.R6.R5.)R7.)(4.(5.R7.+1.)R6.)))")
(* [comment removed for export] *).
Proof.
  intros LBF LBF' SP SP' p A n NC CR SUB HS. destruct (Z.eq_dec n 0); [left; lia| right].
  destruct (Z_lt_le_dec 0 n); [eapply nc_apart; eauto|].
  destruct (Z_lt_le_dec p A); [right; lia| left; lia].
Qed.
#[using="Type"] Lemma wcover_nc : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PLBF',(15.$35.)PSP',$2.PW,(15.$20.)Pp,$2.P,Pa,$2.P,(8<.VL,R5.R4.R1.)(1>.(1.$2.R2.R3.))P,Pb,$35.P,(3;.$35.R1.(34.$35.R9.(36.R8.)))(3;.$35.R2.R7.)P,(4.R5.R7.)(45.R:.R9.R8.R5.R4.+1.)")
(* [comment removed for export] *).
Proof.
  intros LB LF SP LBF' SP' W p NC SUB HS x Hx Hc _. apply (NC x); [| lia].
  destruct Hc as [X|[X|(b & Hb & Hr)]]; [left; lia| right; left; exact X| right; right; exists b; split; [apply SUB, Hb| exact Hr]].
Qed.

(* [comment removed for export] *)
Definition wlow (LB LF : list blk) : Prop := blocks_low LB LF /\ hl_data_hi L <= alloc_ceiling.

#[using="Type"] Lemma hm_wlow : forall (HIA : artA) h LB LF m, HM HIA h LB LF m -> wlow LB LF.
Proof. intros HIA h LB LF m HH. split; [eapply hm_blocks_low; exact HH| apply (art_data_lo HIA)]. Qed.

#[using="Type"] Lemma wcover_of_wlow : forall LB LF SP W a n, wlow LB LF -> alloc_ceiling <= a -> a + n <= SP -> wcover LB LF SP W a n.
Proof. intros LB LF SP W a n [BL DL] H1 H2. eapply wcover_stack; eauto. Qed.

#[using="Type"] Lemma shadow_free_of_wlow : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PLB,(15.$35.)PLF,(15.$35.)PSSP,$2.PTOP,$2.Pc,$2.Pn,$2.P,(8=.R6.R5.)P,(4.(3>.VL,)R3.)P,(4.(5.R4.R3.)R6.)(46.R9.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof. intros LB LF SSP TOP c n [BL DL] H1 H2. eapply shadow_free_stack; eauto. Qed.

#[using="Type"] Lemma shadow_free_of_fresh' : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph1,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSSP,$2.PTOP,$2.Pm1,P,(=.&40.)(>.(=.&8.))PFB,$2.Pn,$2.Pc,$2.Pk,$2.P,(8=.R9.R8.)P,(42.R:.R9.R5.R4.)P,(5<.R=.R<.R;.(8.(25.$2.$2.)(41.$2.$2.R6.R5.)R:.)R7.)P,(4.R7.R5.)P,(4.(5.R6.R5.)(5.R8.R7.))P,(4.(3>.VL,)R<.)(46.R?.R>.R=.R<.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros HIA h1 LB LF SSP TOP m1 FB n c k [BL DL] HF HH H1 H2 H3.
  eapply shadow_free_fresh; eauto. eapply hm_fresh_frame_apart; exact HH.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma presW_call : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PLB',(15.$35.)PLF',(15.$35.)PSP',$2.PSSP',$2.PTOP',$2.PW',(15.$20.)P,(8:.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(3:.R7.R6.R5.R4.R3.R2.R9.R8.)P,Pb,$35.P,(3;.$35.R1.R11.)(3;.$35.R2.R:.)P,Pb,$35.P,(3;.$35.R1.R11.)(3;.$35.R2.R:.)P,(4.R8.R10.)P,(4.R8.R10.)P,(4.(68.R16.R15.)R8.)P,Px,$2.P,(3=.R12.R1.)(3=.R:.R2.)(8:.R18.R17.R16.R15.R14.R13.R12.R11.R?.)")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF SP SSP W m0 m m' LB' LF' SP' SSP' TOP' W' (P & C1 & C2 & C3) P' HB HF HS HSS HT HW.
  split; [| split; [exact C1| split; [exact C2| exact C3]]].
  eapply presA_trans; [exact P|]. eapply presA_weaken; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma not_outside_in : forall W x, ~ outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x H.
  - exfalso. exact (H I).
  - destruct (Z_le_gt_dec lo x) as [G1|G1]; [destruct (Z_lt_ge_dec x hi) as [G2|G2]|].
    + exists lo, hi. split; [left; reflexivity| lia].
    + destruct (IH x) as (l1 & h1 & H1 & H2); [intros Ho; apply H; split; [lia| exact Ho]|]. exists l1, h1. split; [right; exact H1| exact H2].
    + destruct (IH x) as (l1 & h1 & H1 & H2); [intros Ho; apply H; split; [lia| exact Ho]|]. exists l1, h1. split; [right; exact H1| exact H2].
Qed.

#[using="Type"] Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x; [left; exact I|].
  destruct (IH x) as [H|H]; [| right; intros [_ H']; exact (H H')].
  destruct (Z_le_gt_dec lo x) as [G1|G1]; [destruct (Z_lt_ge_dec x hi) as [G2|G2]|]; [right; intros [H' _]; lia| left; split; [lia| exact H] | left; split; [lia| exact H]].
Qed.

#[using="Type"] Lemma presW_munch : ltac2:(CDefT.buildp (gd_tbl_ARt ()) "PHIA,$58.Ph,(5;.R1.)PLB,(15.$35.)PLF,(15.$35.)PSP,$2.PSSP,$2.PW,(15.$20.)Pm0,P,(=.&40.)(>.(=.&8.))Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PW',(15.$20.)P,(8:.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(22.R2.R4.R3.)P,(23.Vsegs,R5.R4.)P,(21.(77.R>.R=.)R4.)P,(24.(25.$2.$2.)Liv,(25.$2.$2.)(45.R>.R=.R<.R:.(26.$2.$2.R1.)(18.(27.$2.$2.R1.)(26.$2.$2.R1.)))R5.)(8:.R10.R?.R>.R=.R<.R;.R:.R9.R7.)")
(* [comment removed for export] *).
Proof.
  intros HIA h LB LF SP SSP W m0 m m' W' (P & C1 & C2 & C3) MU WM HW HC.
  split; [| split; [exact C1| split; [exact C2| exact C3]]].
  eapply presA_trans; [exact P|]. split.
  - intros a Ha Hc Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia.
    destruct (outside_dec W' a) as [Y|N]; [exact Y|]. exfalso.
    destruct (not_outside_in W' a N) as (lo & hi & HIn & Hr).
    rewrite Forall_forall in HC. exact (HC (lo, hi) HIn a ltac:(cbn; lia) Hc Ho).
  - intros c Hc Hr. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia.
    pose proof (hcs_ok HIA h) as OK. destruct OK as (K1 & _). apply (outside_of_not_cs (hcs HIA h)); [exact HW|].
    exact (proj2 (proj2 (proj2 (K1 c (C1 c Hc))))).
Qed.

End WithR.

Arguments cshd R LB LF SSP TOP c /.


