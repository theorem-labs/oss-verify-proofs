(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_string U_mpi_addsub U_mpi_grow U_mpi_core_mla U_mpi_core_add.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_ecp_red () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.max"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.le"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "reducer_R"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_grow.grow_R"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "relimb"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_mla.MPI_CORE_MLA_STACK"; "SAMEARR.arrcall_post"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_add.MPI_CORE_ADD_STACK"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "Corelib.Init.Datatypes.Some"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Nat.mul"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"].


Definition MBEDTLS_ERR_ECP_BAD_INPUT_DATA : Z := -0x4F80.

Definition reducer_R (K : Z) (dX : mpd) (LB : list blk) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "(0.(1.(0.(2.(3.$4.O2.$5.))(0.(3.$4.(6.O1.)(6.O4.))(0.(3.$4.(7.O1.)(8.(7.O4.)O5.))(0.(3.(9.&40.)(:.O1.)(:.O4.))(3.$;.(<.O1.)$=.)))))(0.(3.$4.O2.$5.)(3.$>.O1.O4.)))(0.Pb,$?.P,(10.$?.R1.(11.O1.))(1.(10.$?.R2.(11.O4.))(2.(10.$?.R2.O3.)))(0.(12.(13.(14.+2.+1?.))O2.)(15.O2.=))))")
(* [comment removed for export] *).     (* [comment removed for export] *)

Definition ecp_reducer_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF K STK : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Pra,(9.&40.)Psp,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PF,(16.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(17.(9.&8.))Pmo,$18.Ph,(19.O7.O6.O5.)PLB,(1:.$?.)PdX,$>.Plo,$4.P,(1;.O7.O6.O5.R4.R3.R6.R5.)P,(1<.O7.R7.R4.R3.)P,(2.(3.$;.(<.R4.)$1=.))P,(1>.O6.R6.(1?.&40.R29.)(20.O7.O6.O5.R7.)R5.)P,(21.O7.R:.R5.(1?.&40.R2:.))P,(15.R6.(22.(22.(1?.&40.R2;.)O1.)(23.O6.)))P,(15.(24.O6.)R7.)P,(15.(1?.&40.R2=.)(20.O7.O6.O5.R;.))P,(3.$4.(25.(1?.&40.R2>.)+10.)=)P,(15.(26.O6.)(24.O6.))P,(3.(9.&40.)R2>.(27.&40.(28.O6.)))P,(29.O7.R11.)P,(2:.O7.O6.R12.)P,(2;.O6.O3.+8.)P,(3.(9.&40.)R2<.(27.&40.(2<.R10.)))(2=.O7.R14.(2>.O7.O6.O5.R36.R35.R34.R33.R2?.R2>.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R17.R16.R13.R12.R11.(2?.O2.R11.R12.)R10.R15.R14.)(30.(31.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(27.&40.O4.)R16.(32.(9.&40.))R15.(33.O7.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition relimb (d : mpd) (ws : list word) : mpd := mkMPD (md_addr d) (md_sg d) (md_n d) (md_p d) ws (md_pad d) (md_own d).

Lemma relimb_blk : forall d ws, mpd_blk (relimb d ws) = mpd_blk d.
Proof. intros; reflexivity. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L24469178591.24L24930653726.21L54480673688.18L66092257292.2400000B00[01201DS2dX3dX'2nb3POS2HnS2dX3dX'2nb3POS2N02Hn3HnbS4segs1m2LB2dX3dX'2nb1CS2dX3dX'2nb3POS2HL". (* [comment removed for export] *)
Lemma grow_ok_facts : ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Psegs,(1:.$34.)Pm,P,(9.&40.)(17.(9.&8.))PLB,(1:.$?.)PLB0,(1:.$?.)PdX,$>.PdX',$>.Pnb,$4.P,(1<.R7.R6.R5.R2.)P,(35.R5.R4.R6.R3.)P,(36.R3.R5.R6.=R4.)P,(15.+1.R4.)(0.(3.$;.(<.R6.)$=.)(0.(3.$4.(7.R6.)(8.(7.R7.)R5.))(0.(3.$4.(6.R6.)(6.R7.))(0.(3.(9.&40.)(:.R6.)(:.R7.))(0.(3.$4.(2<.R6.)(2<.R7.))(0.(3.$4.(37.(38.(9.&40.)(39.R6.)))(7.R6.))(0.(10.(3:.$4.$4.)(3;.$4.$4.(3<.R6.)(3=.+4.(7.R6.)))R9.)(0.(3.$4.(25.(3<.R6.)+10.)=)(3>.R;.R:.(3<.R6.)(39.R6.))))))))))")
(* [comment removed for export] *).
Proof.
  (intros segs m LB LB0 dX dX' nb [(CH & AL & POS & HL & HN & HO) SG] dd_H; ddestruct dd_H as (EA & NS & _); intros dd_H; ddestruct dd_H as [[(_ & Hs & Hn & Hp & _ & _)|[C _]] _]; intros Hnb);
    [| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in C; lia].
  assert (O : md_own dX' = LHeap).
  { destruct (md_own dX') eqn:E; [| reflexivity| exfalso; exact (NS eq_refl)]. destruct HO as [_ N0]. lia. }
  rewrite O in HO. ddestruct HO as (N1 & IN & PAL & U).
  refine (conj O (conj _ (conj Hs (conj Hp (conj EA (conj _ (conj IN (conj PAL U)))))))); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma relimb_at : ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Psegs,(1:.$34.)Pm,P,(9.&40.)(17.(9.&8.))Pm',P,(9.&40.)(17.(9.&8.))PLB,(1:.$?.)Pd,$>.Pws,(1:.(9.&40.))P,(1<.R6.R5.R3.R2.)P,(3.$;.(<.R3.)$=.)P,(3?.R8.R6.(2<.R4.)(40.(3<.R4.)(27.&40.(6.R4.))(7.R4.)(:.R4.)))P,(3>.R9.R7.(3<.R5.)R4.)P,(3.$4.(37.(38.(9.&40.)R5.))(7.R6.))(1<.R;.R9.R8.(41.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros segs m m' LB d ws [(CH & AL & POS & HL & HN & HO) SG] O CH' U L. rewrite O in HO. ddestruct HO as (N1 & IN & PAL & _).
  split; [| exact SG]. unfold relimb, mpi_at; cbn. rewrite O.
  refine (conj CH' (conj AL (conj POS (conj L (conj HN (conj N1 (conj IN (conj PAL U)))))))).
Qed.

Lemma reducer_R_ok : ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "PK,$4.PdX,$>.PdX',$>.PLB0,(1:.$?.)PLB,(1:.$?.)Pws,(1:.(9.&40.))Pr,$4.Psegs,(1:.$34.)Pm,P,(9.&40.)(17.(9.&8.))P,(1<.R2.R1.R5.R7.)P,(35.R7.R9.R6.R8.)P,(36.R;.R:.R8.=R9.)P,(15.+1.R<.)P,(0.(0.(12.(13.(14.+2.+1?.))R7.)(15.R7.=))(2.(3.$4.R7.$5.)))(2?.R>.R=.R;.R8.(41.R<.R9.))")
(* [comment removed for export] *).
Proof.
  intros K dX dX' LB0 LB ws r segs m MA OUT GR HK [Hr0 Hr].
  destruct (grow_ok_facts _ _ _ _ _ _ _ MA OUT GR HK) as (O & N & S & P & _).
  destruct GR as [_ FR]. split; [left; unfold relimb; cbn; auto 10|]. rewrite relimb_blk. exact (conj FR Hr0).
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010<L244748061.3000001S". (* [comment removed for export] *)
Lemma reducer_R_fail : forall K dX LB0, reducer_R K dX LB0 MBEDTLS_ERR_MPI_ALLOC_FAILED dX.
Proof. intros. split; [right; auto|]. split; [intros b Hb; left; exact Hb| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L49230201348.33L49232476450.39L52103796997.33L57053699933.32L59308664946.3500000F00_00h01:01ES2SP3lo'1a1C1L3ACL3DHIS1L2SP3lo'3ACL1a1B1k1R2B4S2dX1a2HoS1L2SP3lo'3ACL3LOSS2dX1a1R2Ho". (* [comment removed for export] *)
Lemma reducer_presx : ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Psegs,(1:.$34.)PL,$42.PHI,(43.R2.R1.)Ph',(19.R3.R2.R1.)PLB0,(1:.$?.)PLB,(1:.$?.)Pm0,P,(9.&40.)(17.(9.&8.))Pm,P,(9.&40.)(17.(9.&8.))Pm',P,(9.&40.)(17.(9.&8.))Pmo',$18.PSP,$4.Plo',$4.PdX,$>.PdX',$>.P,(1;.R>.R=.R<.R;.R9.R7.R5.)P,(1<.R?.R8.R:.R2.)P,(35.R<.R4.R;.R3.)P,Pb,$?.P,(10.$?.R1.(11.R5.))(1.(10.$?.R2.(11.R7.))(2.(10.$?.R2.R?.)))P,(3.$;.(<.R5.)$=.)P,(3.$4.(2<.R6.)(2<.R7.))P,(44.R14.R13.R10.R:.(45.R8.)R>.R=.)P,(46.(47.(3:.$4.$4.)(3;.$4.$4.(3<.R8.)(48.(3<.R8.)(3=.+4.(7.R8.))))(47.(3:.$4.$4.)(3;.$4.$4.(2<.R8.)(48.(2<.R8.)+10.))(47.(3:.$4.$4.)(3;.$4.$4.R:.R;.)(49.(3:.$4.$4.)))))R>.R=.)P,(4:.R16.R?.R>.)P,(15.(24.R16.)R<.)P,(15.R=.R>.)P,(15.(26.R18.)(24.R18.))P,(15.(4;.R19.)(4<.R19.))P,(15.(26.R1:.)(4=.R1:.))(44.R1<.R1;.R18.R12.(45.R10.)R16.R14.)")
(* [comment removed for export] *).
Proof.
  intros segs L HI h' LB0 LB m0 m m' mo' SP lo' dX dX' HH MA OUT FR O EA PX MU WM ACL LOS DHI DI1 DI2.
  eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
  intros a Ha Hc Ho. cbn. split; [| split; [| split; [| exact I]]].
  - refine (new_limbs_apart segs L HI h' LB0 LB m m mo' SP dX dX' a HH MA OUT FR ltac:(lia) DI1 DI2 Hc _ O).
    intros HOX. unfold mpd_ivs in Ho. rewrite HOX in Ho. cbn in Ho. lia.
  - unfold mpd_ivs in Ho. rewrite EA. cbn in Ho. destruct Ho as [Ho _]. exact Ho.
  - destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    ddestruct OUT as (_ & _ & _ & K2 & _).
    destruct Hc as [C|[C|([B k] & Hb & R)]]; [lia| lia|]. cbn in R.
    destruct (in_dec (fun x y : blk => ltac:(decide equality; apply Z.eq_dec)) (B, k) (mpd_blk dX)) as [I|NI].
    + unfold mpd_blk in I. destruct (md_own dX) eqn:EO; try (destruct I; fail). destruct I as [E|[]]. injection E as E1 E2.
      exfalso. unfold mpd_ivs in Ho. rewrite EO in Ho. cbn in Ho. subst B k. lia.
    + pose proof (K2 _ Hb NI) as HbLB. pose proof (proj1 (Forall_forall _ _) HBR _ HbLB) as (_ & _ & _ & B4 & _). cbn in B4. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wrc H L FS i :=
  let SOK := fresh "SOK" in let H' := fresh "HX'" in
  lazymatch type of H with
  | u32arr ?sg ?mm ?A ?l =>
      pose proof (u32arr_store_ok sg mm A l i _ H ltac:(lia) ltac:(f_equal; lia)) as SOK;
      zstep;
      lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem _ ?a (le4 ?v)) _) =>
        let E := addr_expr a in
        pose proof (u32arr_write sg mm A l i v H ltac:(lia)) as H';
        try (replace (A + 4 * i)%Z with E in H' by lia);
        apply (same_from_upd_lt _ _ _ (Z.to_nat i) v) in FS; [| lia];
        store_done; try clear H; rename H' into H;
        let l1 := fresh "ws" in let EE := fresh "E" in let L1 := fresh "LEN" in
        remember (upd l (Z.to_nat i) v) as l1 eqn:EE;
        lazymatch type of L with _ = ?r =>
          assert (L1 : Z.of_nat (length l1) = r) by (rewrite EE, upd_length; exact L) end;
        clear L EE; rename L1 into L; try clear l
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L17703687358.600000=S1a1b2Hb1H2H0". (* [comment removed for export] *)
Lemma lor_le_add : forall a b, 0 <= a -> 0 <= b -> a <= Z.lor a b <= a + b.
Proof.
  intros a b Ha Hb. split.
  - rewrite Z.lor_comm. apply lor_ge_r; assumption.
  - pose proof (Z.add_lor_land a b). pose proof (Z.land_nonneg a b). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Ltac lor_facts K :=
  repeat match type of K with context [Z.lor ?x ?y] =>
    pose proof (lor_le_add x y ltac:(lia) ltac:(lia)); let lv := fresh "lv" in set (lv := Z.lor x y) in *; clearbody lv end.
(* [comment removed for export] *)
Ltac zlogic_lits K :=
  repeat match type of K with
  | context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in K
  | context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v in K
  | context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v in K
  end.
Ltac gkillx K := if_cases K; zify_cond K;
  [ exfalso; rewrite ?Z.lxor_0_l, ?Z.lxor_0_r, ?Z.lor_0_l, ?Z.lor_0_r in K; lor_facts K; ub_decide K; zlogic_lits K;
    rewrite ?Z.lor_0_l, ?Z.lor_0_r in K; try (rewrite Z.div_small in K by lia); first [ lia | discriminate K | congruence ]
  | clear K ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MEMSETW.
  Variable segs : list Segment.
  Variable MEMSET : Z.
  Hypothesis SPM : memset_stmt segs MEMSET.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11805649803.74L19054383986.56L3069359204.45 L32607120735.55L32607459445.74L32992720649.74L35323375837.45L40614287107.74L4778019672.74 L53519025459.57L60546950992.50L66105753560.74L66125982750.56L66125999263.57L68150233355.57L68150282634.5600000P01201D01d02D02f03103Q04504M04`05;05e06O07907cS1X2ws1i1k1A2Bm1C2Hi2Hk2LA2LB2LCS2ws1i1k1A2Bm1C2Hi2Hk3Hik2LA2LB2LCS2ws1i1k2Hi2Hk3HikS1X2ws1i1k1A2Bm1C2Hi2Hk2LA2LB2LCS1X2ws1i1k1A2Bm1C2Hi2Hk2LA2LB2LCS2ws1i1k1A2Bm1C2Hi2Hk3Hik2LA2LB2LCS2ws1i1k2HkS1X2ws1i1k1A2Bm1C2Hi2Hk2LA2LB2LCS1X2ws1i1k1A2Bm1C2Hi2Hk3Hik2LA2LB2LCS2ws1i1k1A2Bm1C2LA2LB2LCS2ws1i1k1A2Bm2LA2LBS2ws1i1k1A2Bm1C2Hk2LA2LB2LCS1X2ws1i1k1A2Bm1C2XP2Hi2Hk3Hik2UB2LA2LB2LCS1X2ws1i1k1A2Bm1C2XP2Hi2Hk3Hik2UB2LA2LB2LCS1X2ws1i1k1A2Bm1C2XP2Hi2Hk3Hik2UB2LA2LB2LCS1X2ws1i1k1A2Bm1C2XP2Hi2Hk3Hik2UB2LA2LB2LC". (* [comment removed for export] *)
  #[using="SPM"] Lemma memset_limbs : ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Pra,(9.&40.)Psp,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PF,(16.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(17.(9.&8.))PX,$4.Pws,(1:.(9.&40.))Pi,$4.Pk,$4.P,(3>.Vsegs,R5.R4.R3.)P,(12.=R5.)P,(15.=R4.)P,(15.+1.R4.)P,(15.(48.R6.R5.)(37.(38.(9.&40.)R7.)))P,(29.Vsegs,R:.)P,(3.(9.&40.)R23.(27.&40.(48.R:.(3=.+4.R8.))))P,(3.(9.&40.)R23.(27.&40.=))P,(3.(9.&40.)R23.(27.&40.(3=.+4.R9.)))(4>.Vsegs,Lms',$4?.(50.(9.&40.)Lt0',(9.&40.)(50.(9.&40.)Lt1',(9.&40.)(50.(9.&40.)Lt2',(9.&40.)(50.(9.&40.)La1',(9.&40.)(50.(9.&40.)La2',(9.&40.)(50.(9.&40.)La3',(9.&40.)(50.(9.&40.)La4',(9.&40.)(50.(9.&40.)La5',(9.&40.)(50.(9.&40.)La6',(9.&40.)(50.(9.&40.)La7',(9.&40.)(50.(9.&40.)Lt3',(9.&40.)(50.(9.&40.)Lt4',(9.&40.)(50.(9.&40.)Lt5',(9.&40.)(50.(9.&40.)Lt6',(9.&40.)(50.P,(9.&40.)(17.(9.&8.))Lm',P,(9.&40.)(17.(9.&8.))(50.(1:.(9.&40.))Lws',(1:.(9.&40.))(0.(3.$4?.R11.(30.(31.R40.R3?.R3>.R3=.R10.R?.R>.R39.R38.R37.R=.R<.R;.R:.R9.R8.R7.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R6.R5.R4.R3.)R21.(51.R40.)R20.(32.(9.&40.))R2.(33.Vsegs,)))(0.(46.(47.(3:.$4.$4.)(3;.$4.$4.(48.R1>.(3=.+4.R1<.))(48.(48.R1>.(3=.+4.R1<.))(3=.+4.R1;.)))(49.(3:.$4.$4.)))R1?.R2.)(0.(4:.Vsegs,R1?.R2.)(0.(29.Vsegs,R2.)(0.(3>.Vsegs,R2.R1>.R1.)(3.$52.(38.(9.&40.)R1.)(38.(9.&40.)R1=.)))))))))))))))))))))))(30.(31.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(27.&40.VMEMSET,)R?.(32.(9.&40.))R>.(33.Vsegs,)))")
(* [comment removed for export] *).
  Proof.
    intros until k. intros U XP Hi Hk Hik MI -> -> ->.
    pose proof (u32arr_bound _ _ _ _ U) as UB.
    ddestruct (split3 ws (Z.to_nat i) (Z.to_nat (i + k)) ltac:(lia) ltac:(lia)) as (EY & LA & LB).
    set (A := firstn (Z.to_nat i) ws) in *. set (Bm := firstn _ (skipn _ ws)) in *. set (C := skipn (Z.to_nat (i + k)) ws) in *.
    assert (LC : length C = (length ws - Z.to_nat (i + k))%nat) by (subst C; rewrite skipn_length; lia).
    pose proof U as U0. rewrite EY in U. apply u32arr_app in U. destruct U as [UA U]. apply u32arr_app in U. destruct U as [UBm UC].
    rewrite LA in UBm, UC. rewrite LB in UC. apply u32arr_cells in UBm. rewrite LB in UBm.
    replace (X + 4 * Z.of_nat (Z.to_nat i)) with (X + 4 * i) in UBm, UC by lia.
    pose proof SPM as SP. unfold memset_stmt in SP.
    eapply evt_mono.
    { eapply SP; [| exact MI]. rewrite !unsigned_lit by lia.
      replace (Z.to_nat (4 * k)) with (4 * (Z.to_nat (i + k) - Z.to_nat i))%nat by lia. exact UBm. }
    clear SP. intros ms' PO. unfold memset_post in PO. rewrite !unsigned_lit in PO by lia.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU & WM & MI' & HZ).
    apply (u32arr_of_cells segs m' _ _ _ (repeat (Z_to_bv 64 0) (Z.to_nat k))) in HZ;
      [| rewrite u32s_repeat0; replace (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 by reflexivity; f_equal; lia ].
    deexists 15. exists (A ++ (repeat (Z_to_bv 64 0) (Z.to_nat k) ++ C)).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split.
    - apply u32arr_app. split.
      + eapply u32arr_transport; [exact UA| exact MU| exact WM| cbn; rewrite LA; lia].
      + rewrite LA. apply u32arr_app. split.
        * replace (X + 4 * Z.of_nat (Z.to_nat i)) with (X + 4 * i) by lia. exact HZ.
        * rewrite repeat_length. replace (X + 4 * Z.of_nat (Z.to_nat i) + 4 * Z.of_nat (Z.to_nat k)) with (X + 4 * i + 4 * Z.of_nat (Z.to_nat (i + k) - Z.to_nat i)) by lia.
          eapply u32arr_transport; [exact UC| exact MU| exact WM| cbn; rewrite LC; lia].
    - rewrite !app_length, repeat_length, LA, LC. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MEMSETW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MEMCPYW.
  Variable segs : list Segment.
  Variable MEMCPY : Z.
  Hypothesis SPC : memcpy_stmt segs MEMCPY.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L10718379223.69L10718395478.68L11805649803.86L16747846456.86L19054383986.68L27715771891.62L30998160208.57L32234987135.86L35323277533.52L38788363751.62L44690187508.66L47276535738.68L53728430345.86L57533712327.62L57535465709.86L62288400716.68L65421167952.86L66224921825.69L66224970848.68L68150233355.69L68150282634.68L8161634916.52 00000m01j02d03c04[05=05U06O06_07O08E09H0:@0:e0;_0<W0=Q0>R0?S0@\0Ae0B<S1D3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik2DB2LA2LB2LC3LSA3LSBS1D3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik2DB2LA2LB2LC3LSA3LSBS1D3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik2LA2LB2LC3LSA3LSBS1D1S3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik2DJ2LA2LB2LC3LSA3LSBS3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik2LA2LB2LC3LSA3LSBS3dws3sws1i1j1k1A2Bm1C2Hk2LA2LB2LCS3dws3sws1i1k1A2Bm2LA2LBS1D3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik2LA2LB2LC3LSA3LSBS3dws3sws1i1k2HkS3dws3sws1i1j1k1A2Bm1C2Hi2Hj2Hk3Hik3Hjk2LA2LB2LCS1S3dws3sws1i1j1k1A2Bm1C2Hi2Hj2Hk3Hik2LA2LB2LC3LSA3LSBS1D1S3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik3Hjk2DJ2LA2LB2LC3LSA3LSBS3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik2LA2LB2LC3LSA3LSBS1D3dws3sws1i1k1A2Bm1C2Hi2Hk2LA2LB2LCS1D3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik2LA2LB2LC3LSA3LSBS3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik2LA2LB2LC3LSA3LSBS1D3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik2LA2LB2LC3LSA3LSBS1S3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik3Hjk2SB2LA2LB2LC3LSA3LSBS1S3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik3Hjk2SB2LA2LB2LC3LSA3LSBS1D1S3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik3Hjk2DJ2DB2SB2LA2LB2LC3LSA3LSBS1D1S3dws3sws1i1j1k1A2Bm1C3SRC2Hi2Hj2Hk3Hik3Hjk2DJ2DB2SB2LA2LB2LC3LSA3LSBS3dws3sws1i1k2Hi2Hk3Hik". (* [comment removed for export] *)
  #[using="SPC"] Lemma memcpy_limbs : ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Pra,(9.&40.)Psp,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PF,(16.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(17.(9.&8.))PD,$4.PS,$4.Pdws,(1:.(9.&40.))Psws,(1:.(9.&40.))Pi,$4.Pj,$4.Pk,$4.P,(3>.Vsegs,R8.R7.R5.)P,(3>.Vsegs,R9.R7.R5.)P,(15.=R5.)P,(15.=R5.)P,(15.+1.R5.)P,(15.(48.R8.R6.)(37.(38.(9.&40.)R:.)))P,(15.(48.R8.R7.)(37.(38.(9.&40.)R:.)))P,(1.(15.(48.R=.(3=.+4.(37.(38.(9.&40.)R;.))))R>.)(15.(48.R>.(3=.+4.(37.(38.(9.&40.)R<.))))R=.))P,(29.Vsegs,R10.)P,(3.(9.&40.)R29.(27.&40.(48.R10.(3=.+4.R<.))))P,(3.(9.&40.)R29.(27.&40.(48.R10.(3=.+4.R<.))))P,(3.(9.&40.)R29.(27.&40.(3=.+4.R<.)))(4>.Vsegs,Lms',$4?.(50.(9.&40.)Lt0',(9.&40.)(50.(9.&40.)Lt1',(9.&40.)(50.(9.&40.)Lt2',(9.&40.)(50.(9.&40.)La1',(9.&40.)(50.(9.&40.)La2',(9.&40.)(50.(9.&40.)La3',(9.&40.)(50.(9.&40.)La4',(9.&40.)(50.(9.&40.)La5',(9.&40.)(50.(9.&40.)La6',(9.&40.)(50.(9.&40.)La7',(9.&40.)(50.(9.&40.)Lt3',(9.&40.)(50.(9.&40.)Lt4',(9.&40.)(50.(9.&40.)Lt5',(9.&40.)(50.(9.&40.)Lt6',(9.&40.)(50.P,(9.&40.)(17.(9.&8.))Lm',P,(9.&40.)(17.(9.&8.))(50.(1:.(9.&40.))Ldws',(1:.(9.&40.))(0.(3.$4?.R11.(30.(31.R46.R45.R44.R43.R10.R?.R>.R3?.R3>.R3=.R=.R<.R;.R:.R9.R8.R7.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R6.R5.R4.R3.)R27.(51.R46.)R26.(32.(9.&40.))R2.(33.Vsegs,)))(0.(46.(47.(3:.$4.$4.)(3;.$4.$4.(48.R24.(3=.+4.R20.))(48.(48.R24.(3=.+4.R20.))(3=.+4.R1>.)))(49.(3:.$4.$4.)))R25.R2.)(0.(4:.Vsegs,R25.R2.)(0.(29.Vsegs,R2.)(0.(3>.Vsegs,R2.R24.R1.)(0.(3.$52.(38.(9.&40.)R1.)(38.(9.&40.)R22.))(3>.Vsegs,R2.R23.R21.)))))))))))))))))))))))(30.(31.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R16.(27.&40.VMEMCPY,)R15.(32.(9.&40.))R14.(33.Vsegs,)))")
(* [comment removed for export] *).
  Proof.
    intros until k. intros UD US Hi Hj Hk Hik Hjk DJ MI -> -> ->.
    pose proof (u32arr_bound _ _ _ _ UD) as DB. pose proof (u32arr_bound _ _ _ _ US) as SB.
    ddestruct (split3 dws (Z.to_nat i) (Z.to_nat (i + k)) ltac:(lia) ltac:(lia)) as (EY & LA & LB).
    set (A := firstn (Z.to_nat i) dws) in *. set (Bm := firstn _ (skipn _ dws)) in *. set (C := skipn (Z.to_nat (i + k)) dws) in *.
    assert (LC : length C = (length dws - Z.to_nat (i + k))%nat) by (subst C; rewrite skipn_length; lia).
    pose proof UD as UD0. rewrite EY in UD. apply u32arr_app in UD. destruct UD as [UA UD]. apply u32arr_app in UD. destruct UD as [UBm UC].
    rewrite LA in UBm, UC. rewrite LB in UC. apply u32arr_cells in UBm. rewrite LB in UBm.
    replace (D + 4 * Z.of_nat (Z.to_nat i)) with (D + 4 * i) in UBm, UC by lia.
    (* [comment removed for export] *)
    ddestruct (split3 sws (Z.to_nat j) (Z.to_nat (j + k)) ltac:(lia) ltac:(lia)) as (EZ & LSA & LSB).
    pose proof US as US0. rewrite EZ in US. apply u32arr_app in US. destruct US as [_ US]. apply u32arr_app in US. destruct US as [USm _].
    rewrite LSA in USm. replace (S + 4 * Z.of_nat (Z.to_nat j)) with (S + 4 * j) in USm by lia.
    set (SRC := firstn (Z.to_nat (j + k) - Z.to_nat j) (skipn (Z.to_nat j) sws)) in *.
    destruct USm as [SRCB _].
    pose proof SPC as SP. unfold memcpy_stmt in SP.
    eapply evt_mono.
    { eapply SP with (src := u32s SRC); rewrite ?unsigned_lit by lia; [exact SRCB| rewrite u32s_length; lia| | lia| exact MI].
      replace (Z.to_nat (4 * k)) with (4 * (Z.to_nat (i + k) - Z.to_nat i))%nat by lia. exact UBm. }
    clear SP. intros ms' PO. unfold memcpy_post in PO. rewrite !unsigned_lit in PO by lia.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU & WM & MI' & HZ & _).
    apply (u32arr_of_cells segs m' _ _ _ SRC) in HZ; [| reflexivity].
    deexists 15. exists (A ++ (SRC ++ C)).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [| split].
    - apply u32arr_app. split.
      + eapply u32arr_transport; [exact UA| exact MU| exact WM| cbn; rewrite LA; lia].
      + rewrite LA. apply u32arr_app. split.
        * replace (D + 4 * Z.of_nat (Z.to_nat i)) with (D + 4 * i) by lia. exact HZ.
        * rewrite LSB. replace (D + 4 * Z.of_nat (Z.to_nat i) + 4 * Z.of_nat (Z.to_nat (j + k) - Z.to_nat j)) with (D + 4 * i + 4 * Z.of_nat (Z.to_nat (i + k) - Z.to_nat i)) by lia.
          eapply u32arr_transport; [exact UC| exact MU| exact WM| cbn; rewrite LC; lia].
    - rewrite !app_length, LA, LSB, LC. lia.
    - eapply u32arr_transport; [exact US0| exact MU| exact WM| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MEMCPYW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SAMEARR.
  Variable segs : list Segment.
  Variables MLA ADD : Z.
  Hypothesis SPL : mpi_core_mla_stmt segs MLA.
  Hypothesis SPA : mpi_core_add_stmt segs ADD.

  Definition arrcall_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (X n STK : Z) (ws : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Lms',$4?.(50.(9.&40.)Lt0,(9.&40.)(50.(9.&40.)Lt1,(9.&40.)(50.(9.&40.)Lt2,(9.&40.)(50.(9.&40.)La0,(9.&40.)(50.(9.&40.)La1,(9.&40.)(50.(9.&40.)La2,(9.&40.)(50.(9.&40.)La3,(9.&40.)(50.(9.&40.)La4,(9.&40.)(50.(9.&40.)La5,(9.&40.)(50.(9.&40.)La6,(9.&40.)(50.(9.&40.)La7,(9.&40.)(50.(9.&40.)Lt3,(9.&40.)(50.(9.&40.)Lt4,(9.&40.)(50.(9.&40.)Lt5,(9.&40.)(50.(9.&40.)Lt6,(9.&40.)(50.P,(9.&40.)(17.(9.&8.))Lm',P,(9.&40.)(17.(9.&8.))(50.(1:.(9.&40.))Lws',(1:.(9.&40.))(0.(3.$4?.R12.(30.(31.O18.O17.O16.O15.R11.R10.R?.O14.O13.R>.R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(51.O18.)O7.(32.(9.&40.))R2.(33.Vsegs,)))(0.(46.(47.(3:.$4.$4.)(3;.$4.$4.O6.(48.O6.(3=.+4.O5.)))(47.(3:.$4.$4.)(3;.$4.$4.(22.(1?.&40.O17.)O4.)(1?.&40.O17.))(49.(3:.$4.$4.))))O1.R2.)(0.(4:.Vsegs,O1.R2.)(0.(29.Vsegs,R2.)(0.(3>.Vsegs,R2.O6.R1.)(0.(3.$52.(38.(9.&40.)R1.)(38.(9.&40.)O3.))(21.Vsegs,R2.O2.(1?.&40.O17.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L1277821070.59 L26840991892.81L26843069069.58L28810406828.59L320453071.59  L36758623999.54L40339269548.59L42322678625.59L45542131645.59L45586436448.59L46267841186.55L50745278824.81L54059125378.59L55883755591.59L56899964406.59L60726144203.59L6327654815.82 00000X01901S01m02`03?03\04=04e05F05W06C06]07407g07h08gS2ra2sp1X2ws1W2sl2HW3Hsl3HWs2XP2XT2LP2LQS2ra2sp1X2ws1W2HW2XP2LP2LQ3ds'2L'S2ra2sp1X2ws1W2HW2XP2LP2LQS2ra2sp1X2ws1W2HW2XP2LP2LQS2ra2sp1X2ws1W2sl2lo2HW3Hsl3HWs2AL2XP4SPAL2SX2LP2LQS2ra2sp1X2ws1W2sl2HW3Hsl3HWs2XPS2ra2sp1X2ws1W2HW2AL2XP2LP2LQS2ra2sp1X2ws1W2sl2HW3HWs2XP2LP2LQS2ra2sp1X2ws1W2sl2HW3Hsl3HWs2XP2XT2LP2LQS2ra2sp1X2ws1W2sl2HW3Hsl2XP2LP2LQS2ra2sp1X2ws1W2LPS2ra2sp1X2ws1W2sl2HW3Hsl3HWs2XP2LP2LQ3ds'2L'S2ra2sp1X2ws1W2HW2XP2LP2LQS2ra2sp1X2ws1W2HW2LP2LQS2ra2sp1X2ws1W2sl2lo2HW3Hsl3HWs2AL2XP4SPAL2SX2LP2LQFS2ra2sp1X2ws1W2sl2lo2HW3Hsl3HWs2AL2XP2LO4SPAL2SX2LP2LQ3ds'2L'1H". (* [comment removed for export] *)
  #[using="SPL"] Lemma mla_hi_into_lo : ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Pra,(9.&40.)Psp,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PF,(16.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(17.(9.&8.))PX,$4.Pws,(1:.(9.&40.))PW,$4.Psl,$4.Plo,$4.P,(3>.Vsegs,R6.R5.R4.)P,(0.(15.+1.R4.)(15.R4.+2710.))P,(0.(15.=R4.)(15.R4.+2710.))P,(15.(48.R6.R5.)(37.(38.(9.&40.)R7.)))P,(3.$4.(25.R9.+4.)=)P,(12.=R:.)P,(12.(48.R;.(3=.+4.(37.(38.(9.&40.)R:.))))(14.+2.+40.))P,(21.Vsegs,R=.R8.(1?.&40.R2=.))P,(15.R9.(22.(1?.&40.R2>.)$53.))P,(3.$4.(25.(1?.&40.R2?.)+10.)=)P,(1.(15.(48.R?.(3=.+4.(37.(38.(9.&40.)R>.))))R;.)(15.(1?.&40.R30.)R?.))P,(29.Vsegs,R11.)P,(3.$4.(25.(1?.&40.R33.)+2.)=)P,(3.(9.&40.)R2;.(27.&40.R12.))P,(3.(9.&40.)R2;.(27.&40.R11.))P,(3.(9.&40.)R2;.(27.&40.(48.R14.(3=.+4.R12.))))P,(3.(9.&40.)R2;.(27.&40.R12.))(4>.Vsegs,(54.R38.R37.R36.R35.R31.R30.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R19.R18.R16.R14.$53.R15.R12.R17.)(30.(31.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(27.&40.VMLA,)R18.(32.(9.&40.))R17.(33.Vsegs,)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros U HW Hsl HWs AL XP XT ST LO SPAL SX MI RA -> -> -> ->.
    pose proof (firstn_skipn (Z.to_nat W) ws) as EY. symmetry in EY.
    assert (LP : length (firstn (Z.to_nat W) ws) = Z.to_nat W) by (rewrite firstn_length; lia).
    assert (LQ : length (skipn (Z.to_nat W) ws) = (length ws - Z.to_nat W)%nat) by (rewrite skipn_length; lia).
    pose proof U as U0. rewrite EY in U. apply u32arr_app in U. destruct U as [Ulo Uhi]. rewrite LP in Uhi.
    replace (X + 4 * Z.of_nat (Z.to_nat W)) with (X + 4 * W) in Uhi by lia.
    pose proof SPL as SP. unfold mpi_core_mla_stmt in SP.
    eapply evt_mono.
    { eapply SP with (D := X) (dl := W) (S := X + 4 * W) (sl := sl) (ds := firstn (Z.to_nat W) ws) (ss := skipn (Z.to_nat W) ws) (lo := lo);
        try reflexivity; try eassumption; try (rewrite ?LP, ?LQ; lia).
      all: apply u32arr_ro; exact Uhi. }
    clear SP. intros ms' PO. unfold mpi_core_mla_post in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & ds' & -> & MU & WM & MI' & U' & L' & _ & ST').
    unfold arrcall_post. deexists 16. exists (ds' ++ skipn (Z.to_nat W) ws).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [| split; [rewrite app_length, L', LP, LQ; lia| exact ST']].
    apply u32arr_app. split; [exact U'|]. rewrite L', LP. replace (X + 4 * Z.of_nat (Z.to_nat W)) with (X + 4 * W) by lia.
    eapply u32arr_transport; [exact Uhi| exact MU| exact WM|]. cbn. rewrite LQ. pose proof (u32arr_bound _ _ _ _ U0). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L13393549565.58L25564353251.58L25715690834.58L26840991892.81L26843055039.57L28810406828.58L320453071.58  L36758623999.52L40339269548.58L46267841186.53L50745278824.81L5656942982.58 L56899964406.58L60448205867.58L60726144203.58L61711087399.58L6332258238.81 00000J00h00i01J01d02>02m03E03b04004U04V05E05_05`06>077S2sp1X2ws1W1n3HnW2XP2LP2LQS2sp1X2ws1W1n3HnW3HWn2XP2LP2LQFS2sp1X2ws1W1n3HnW2XP2LP2LQ3xs'2L'S2sp1X2ws1W1n3HnW2XP2LP2LQS2sp1X2ws1W1n3HnW2XP2LP2LQS2sp1X2ws1W1n2lo3HnW3HWn2AL2XP4SPAL2SX2LP2LQ2UBS2sp1X2ws1W1n3HnW3HWn2XPS2sp1X2ws1W1n3HnW2AL2XP2LP2LQS2sp1X2ws1W2LPS2sp1X2ws1W1n3HnW3HWn2XP2LP2LQ3xs'2L'FS2sp1X2ws1W1n2lo3HnW3HWn2AL2XP4SPAL2SX2LP2LQ2UBS2sp1X2ws1W1n3HnW2Hn2LP2LQFS2sp1X2ws1W1n3HnW3HWn2XP2LP2LQS2sp1X2ws1W1n2lo3HnW3HWn2AL2XP2LO4SPAL2SX2LP2LQ2UB3xs'2L'". (* [comment removed for export] *)
  #[using="SPA"] Lemma core_add_hi_into_lo : ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Pra,(9.&40.)Psp,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PF,(16.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(17.(9.&8.))PX,$4.Pws,(1:.(9.&40.))PW,$4.Pn,$4.Plo,$4.P,(3>.Vsegs,R6.R5.R4.)P,(0.(15.=R3.)(15.R3.R4.))P,(15.R4.+2710.)P,(15.(48.R6.R5.)(37.(38.(9.&40.)R7.)))P,(3.$4.(25.R9.+4.)=)P,(12.=R:.)P,(21.Vsegs,R<.R7.(1?.&40.R2<.))P,(15.R8.(22.(1?.&40.R2=.)$55.))P,(3.$4.(25.(1?.&40.R2>.)+10.)=)P,(1.(15.(48.R>.(3=.+4.(37.(38.(9.&40.)R=.))))R:.)(15.(1?.&40.R2?.)R>.))P,(29.Vsegs,R10.)P,(3.(9.&40.)R29.(27.&40.R10.))P,(3.(9.&40.)R29.(27.&40.R11.))P,(3.(9.&40.)R29.(27.&40.(48.R12.(3=.+4.R10.))))P,(3.(9.&40.)R29.(27.&40.R10.))(4>.Vsegs,(54.R36.R35.R34.R33.R2?.R2>.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R17.R16.R14.R11.$55.R13.R10.R15.)(30.(31.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(27.&40.VADD,)R16.(32.(9.&40.))R15.(33.Vsegs,)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros U HnW Hn HWn AL XP ST LO SPAL SX MI -> -> -> ->.
    pose proof (firstn_skipn (Z.to_nat W) ws) as EY. symmetry in EY.
    assert (LP : length (firstn (Z.to_nat W) ws) = Z.to_nat W) by (rewrite firstn_length; lia).
    assert (LQ : length (skipn (Z.to_nat W) ws) = (length ws - Z.to_nat W)%nat) by (rewrite skipn_length; lia).
    pose proof U as U0. pose proof (u32arr_bound _ _ _ _ U0) as UB. rewrite EY in U. apply u32arr_app in U. destruct U as [Ulo Uhi]. rewrite LP in Uhi.
    replace (X + 4 * Z.of_nat (Z.to_nat W)) with (X + 4 * W) in Uhi by lia.
    pose proof SPA as SP. unfold mpi_core_add_stmt in SP.
    eapply evt_mono.
    { eapply SP with (X := X) (A := X) (B := X + 4 * W) (n := n) (xs := firstn (Z.to_nat W) ws) (ys := firstn (Z.to_nat W) ws) (zs := skipn (Z.to_nat W) ws) (lo := lo);
        try reflexivity; try eassumption; try (rewrite ?LP, ?LQ; lia).
      all: first [apply u32arr_ro; exact Ulo | apply u32arr_ro; exact Uhi | left; split; reflexivity]. }
    clear SP. intros ms' PO. unfold mpi_core_add_post in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & c & xs' & -> & MU & WM & MI' & _ & _ & U' & L' & _ & _ & ST').
    unfold arrcall_post. deexists 16. exists (xs' ++ skipn (Z.to_nat W) ws).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [| split; [rewrite app_length, L', LP, LQ; lia| exact ST']].
    apply u32arr_app. split; [exact U'|]. rewrite L', LP. replace (X + 4 * Z.of_nat (Z.to_nat W)) with (X + 4 * W) by lia.
    eapply u32arr_transport; [exact Uhi| exact MU| exact WM|]. cbn. rewrite LQ. unfold MPI_CORE_ADD_STACK in *.
    lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SAMEARR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L17481912259.14000004S2ws". (* [comment removed for export] *)
Lemma heap_presx_u32arr : ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Psegs,(1:.$34.)PL,$42.PLB,(1:.$?.)PSP,$4.PX,(1:.$56.)Pm,P,(9.&40.)(17.(9.&8.))Pm',P,(9.&40.)(17.(9.&8.))PA,$4.Pws,(1:.(9.&40.))P,(44.R9.R8.R7.R6.R5.R4.R3.)P,(3>.R:.R5.R3.R2.)P,(57.R:.R9.R8.R4.(3=.+4.(37.(38.(9.&40.)R3.))))P,(58.R8.R5.(3=.+4.(37.(38.(9.&40.)R4.))))(3>.R=.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros segs L LB SP X m m' A ws PX [Hb Hw] CR D. split.
  - eapply heap_presx_bytes_at; [exact PX| exact Hb| rewrite u32s_length| rewrite u32s_length];
      replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia; assumption.
  - eapply heap_presx_wr_at; [exact PX| exact Hw| exact CR| exact D].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac presx_stack segs L PX DJ :=
  lazymatch type of PX with heap_presx _ _ _ _ _ ?m _ =>
    repeat match goal with
    | H : rw_cells segs m ?a ?cs |- _ =>
        apply (heap_presx_rw_cells segs L _ _ _ _ _ _ _ PX) in H; [| cbn; intros xx Hxx; left; lia| DJ]
    | H : u32arr segs m ?a ?ws |- _ =>
        apply (heap_presx_u32arr segs L _ _ _ _ _ _ _ PX) in H; [| cbn; intros xx Hxx; left; lia| DJ]
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L34491537124.9L9336311464.9 00000>00IS2ws1i1n2Hi2HnS2ws1i1n2Hi". (* [comment removed for export] *)
Lemma u32arr_read_any : ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Psegs,(1:.$34.)Pm,P,(9.&40.)(17.(9.&8.))PA,$4.Pws,(1:.(9.&40.))Pi,$4.Pn,$52.Pa,(9.&40.)P,(3>.R7.R6.R5.R4.)P,(15.=R4.)P,(15.(48.(3=.+4.R5.)(37.R4.))(3=.+4.(37.(38.(9.&40.)R6.))))P,(3.(9.&40.)R4.(59.(48.R8.(3=.+4.R6.))))(3.(17.(1:.(9.&8.)))(5:.R;.R:.R5.R6.)(5;.(1:.(9.&8.))(5<.(9.&8.)R6.(5=.(9.&8.)(5>.(3=.+4.R7.))(5?.R8.)))))")
(* [comment removed for export] *).
Proof.
  intros segs m A ws i n a [Hb _] Hi Hn ->. replace (4 * i) with (Z.of_nat (Z.to_nat (4 * i))) at 1 by lia.
  apply bytes_at_ov_read; [exact Hb| rewrite u32s_length; lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L42865824178.9L62303078074.900000;00FS2ws1i1n2HiS2ws1i1n2Hn". (* [comment removed for export] *)
Lemma u32arr_store_ok_any : ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Psegs,(1:.$34.)Pm,P,(9.&40.)(17.(9.&8.))PA,$4.Pws,(1:.(9.&40.))Pi,$4.Pn,$52.Pa,(9.&40.)P,(3>.R7.R6.R5.R4.)P,(15.=R4.)P,(15.(48.(3=.+4.R5.)(37.R4.))(3=.+4.(37.(38.(9.&40.)R6.))))P,(3.(9.&40.)R4.(59.(48.R8.(3=.+4.R6.))))(3.$60.(61.R;.R:.R5.R6.)$62.)")
(* [comment removed for export] *).
Proof. intros segs m A ws i n a [_ Hw] Hi Hn ->. eapply wr_at_store_ok; [exact Hw| lia| lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L10221820751.13L42865823793.12L47987976646.13L47990074882.1200000<00M00a015S2ws2bs1k2HlS2ws1i2bs1k2Hl2HiS2ws1i2bs1k2Hl2Hi2HkS2ws1i2bs1k2Hl2Hi2Hk". (* [comment removed for export] *)
Lemma u32arr_write_any : ltac2:(CDefT.buildp (gd_tbl_P_ecp_red ()) "Psegs,(1:.$34.)Pm,P,(9.&40.)(17.(9.&8.))PA,$4.Pws,(1:.(9.&40.))Pi,$4.Pbs,(1:.(9.&8.))Pk,$52.P,(3>.R7.R6.R5.R4.)P,(3.$52.(38.(9.&8.)R3.)(63.#4.R2.))P,(15.=R5.)P,(15.(48.R6.(37.R4.))(37.(38.(9.&40.)R7.)))(50.(1:.(9.&40.))Lws',(1:.(9.&40.))(0.(3>.R<.(64.R;.(59.(48.R:.(3=.+4.R8.)))R7.)R:.R1.)(3.$52.(38.(9.&40.)R1.)(38.(9.&40.)R9.))))")
(* [comment removed for export] *).
Proof.
  intros segs m A ws i bs k [Hb Hw] Hl Hi Hk.
  pose proof (bytes_at_write_inside segs m A (u32s ws) (4 * i) bs Hb ltac:(lia) ltac:(rewrite u32s_length; lia)) as Hb'.
  assert (L : length (upd_bytes (u32s ws) (Z.to_nat (4 * i)) bs) = (4 * length ws)%nat) by (rewrite upd_bytes_length; rewrite u32s_length; lia).
  destruct (bytes_as_u32s (length ws) _ L) as (ws' & E & L'). rewrite E in Hb'.
  exists ws'. split; [| exact L']. split; [exact Hb'|]. rewrite L'. apply wr_at_write. exact Hw.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rdx H i n :=
  let RD := fresh "RD" in
  lazymatch type of H with
  | u32arr ?sg ?mm ?A ?l =>
      pose proof (u32arr_read_any sg mm A l i n _ H ltac:(lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
      cbn [firstn skipn Z.to_nat Pos.to_nat] in RD
  end;
  zstep; try clear RD.

(* [comment removed for export] *)
Ltac wrx H L FS i n :=
  let SOK := fresh "SOK" in let H' := fresh "HX'" in let L' := fresh "LEN'" in let ws' := fresh "ws" in
  lazymatch type of H with
  | u32arr ?sg ?mm ?A ?l =>
      pose proof (u32arr_store_ok_any sg mm A l i n _ H ltac:(lia) ltac:(lia) ltac:(f_equal; lia)) as SOK;
      zstep;
      lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem _ ?a ?bs) _) =>
        let E := addr_expr a in
        destruct (u32arr_write_any sg mm A l i bs (Nat.div n 4) H ltac:(cbn; rewrite ?length_le8, ?length_le4; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (ws' & H' & L');
        try (replace (A + 4 * i)%Z with E in H' by lia);
        store_done; try clear H; rename H' into H;
        lazymatch type of L with _ = ?r =>
          let L1 := fresh "LEN" in assert (L1 : Z.of_nat (length ws') = r) by (rewrite L'; exact L); clear L L' FS; rename L1 into L;
          pose proof (same_from_refl (Z.to_nat r) ws') as FS end;
        try clear l
      end
  end.
