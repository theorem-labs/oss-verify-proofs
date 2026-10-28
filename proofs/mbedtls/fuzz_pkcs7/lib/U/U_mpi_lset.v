(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P03cd922fe7255765 2 23 1 1 8 3 1 1 35 1 36 1 6 0 1 28 1 29 1 34 1 37 1 38 8 1 1 8 3 2 1 34 1 37 1 4 0 2 35 2 36 2 38 16P0e4bb1be71a7a470 0 2 0 1 12 1P12aebef4e966f265 2 17 1 1 8 3 2 1 34 1 35 1 6 0 1 27 1 28 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P1a70feb083f3792a 2 23 1 1 8 3 1 1 35 1 36 1 6 0 1 28 1 29 1 34 1 37 1 38 8 1 1 8 3 2 1 34 1 37 1 4 0 2 35 2 36 2 38 16P1ac77674ebdbbe9d 0 8 0 16 10 16 16 16 25 16 26 16 27 16 32 16 33 16P1cd7849ae9195a97 0 2 0 1 12 1P1e0f80b2bdf8f5f2 0 2 0 1 12 1P22a709399ed9ea55 2 17 1 1 8 3 2 1 34 1 35 1 6 0 1 27 1 28 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P267800799e3af356 0 5 0 1 24 1 25 1 30 1 31 1P277ed2cac30e5257 0 2 0 1 13 1P2e82c83f1625c83c 0 2 0 1 13 1P31379c4eb5194355 2 17 1 1 8 3 2 1 34 1 35 1 6 0 1 27 1 28 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P35f060e50272862d 1 2 16 2 0 1 32 1 16 2 17 1 33 1 2 34 1 35 1P362bb63e6a341fcc 1 1 16 2 17 1 33 1 3 0 1 32 1 34 16P3690f8170fe854d0 2 17 1 1 8 3 2 1 34 1 35 1 6 0 1 27 1 28 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P39dc98a479dc7f04 0 2 0 1 13 1N003660058b1f7f43N11cde5e50ab6bc99N159130765053fae8N1d1197ce316f3ab2N1fe64f2b766fbf5aN32e0808560e38260N3548992e4ae1f290N36a2efd56d08d9b7N399bf711f26eaeef"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_lset () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "lset_R"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_waddr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "Corelib.Init.Logic.False"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"].


Definition U_MPI_LSET : Z := 0x1f808.
Definition U_MEMSET : Z := 0x46e44.
Notation MPI_LSET_STACK := 48 (only parsing).

Definition lset_R (z : Z) (dX : mpd) (LB : list blk) (r : Z) (dX' : mpd) : Prop :=
  ( (r = 0 /\ md_n dX' = Z.max (md_n dX) 1 /\ md_own dX' = LHeap
       /\ (exists w0, md_limbs dX' = w0 :: repeat (Z_to_bv 64 0) (Z.to_nat (md_n dX' - 1)))   (* [comment removed for export] *)
       /\ md_sg dX' = (if z <? 0 then -1 else 1) /\ md_pad dX' = md_pad dX)
    \/ (r = MBEDTLS_ERR_MPI_ALLOC_FAILED /\ dX' = dX) )
  /\ md_addr dX' = md_addr dX
  /\ (forall b, In b (mpd_blk dX') -> In b (mpd_blk dX) \/ ~ In b LB).

Definition mpi_lset_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_lset ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.O5.O4.O3.)PLB,(5.$6.)PdX,$7.Pz,$8.Plo,$8.P,(9.O5.O4.O3.R5.R4.R7.R6.)P,(:.O5.R8.R5.R4.)P,(;.(<.$=.(>.R5.)$?.))P,(10.O4.R7.(11.&40.R2:.)(12.O5.O4.O3.R8.)R6.)P,(13.(14.(15.(16.+2.+1?.))R6.)(17.R6.(16.+2.+1?.)))P,(18.O5.R<.R6.(11.&40.R2<.))P,(14.R7.(19.(19.(11.&40.R2=.)+30.)(1:.O4.)))P,(14.(1;.O4.)R8.)P,(14.(11.&40.R2?.)(12.O5.O4.O3.R=.))P,(<.$8.(1<.(11.&40.R30.)+10.)=)P,(14.(1=.O4.)(1;.O4.))P,(<.(0.&40.)R30.(1>.&40.(1?.O4.)))P,(20.O5.R13.)P,(21.O5.O4.R14.)P,(22.O4.O1.+8.)P,(<.(0.&40.)R2>.(1>.&40.(23.R12.)))P,(<.(0.&40.)R2>.(1>.&40.R12.))(24.O5.R17.(25.O5.O4.O3.R39.R38.R37.R36.R32.R31.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1:.R19.R16.R15.R14.(26.R13.R14.R15.)R12.R18.R17.)(27.(28.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(1>.&40.O2.)R19.(29.(0.&40.))R18.(2:.O5.)))")
(* [comment removed for export] *).

Section LS.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  (* [comment removed for export] *)
  Ltac flia := first [clear_disj; lia | lia].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12779162959.12L18926747689.12L18926759668.1200000:00;00@S1a1b1k2HkSS1a1b". (* [comment removed for export] *)
  Lemma zbv_mod64 : forall a b, (a - b) mod 18446744073709551616 = 0 -> (Z_to_bv 64 a : word) = Z_to_bv 64 b.
  Proof.
    intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    apply Z.mod_divide in H; [| lia]. flat constr:(H) 2%nat. flclear H. intros k Hk. replace a with (b + k * 18446744073709551616) by lia. apply Z.mod_add. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac fix_regs :=
    repeat match goal with |- context [Z_to_bv 64 (Zpos ?p)] =>
      let z := constr:(Zpos p) in
      lazymatch eval compute in (Z.leb (2^63) z) with
      | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) by (apply zbv_mod64; reflexivity)
      end end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L54391995694.31L54398102733.3200000L00bS1L2HI2sp1h2lo4HTOP3SLO1a2HfS1L2HI2sp1h2lo3SLO1a1C". (* [comment removed for export] *)
  Lemma run_heap : ltac2:(CDefT.buildp (gd_tbl_P_mpi_lset ()) "Psp,(0.&40.)Ph,(4.$2;.VL,VHI,)Phc,(4.$2;.VL,VHI,)PLBc,(5.$6.)Pmc,P,(0.&40.)(2.(0.&8.))Pm',P,(0.&40.)(2.(0.&8.))Pmoc,$3.PW,(5.$2<.)PX,$8.Plo,$8.P,(9.$2;.VL,VHI,R8.R7.R6.R4.)P,(<.$8.(12.$2;.VL,VHI,R9.)(12.$2;.VL,VHI,R:.))P,(14.(11.&40.R<.)(12.$2;.VL,VHI,R;.))P,(14.(1;.VL,)R4.)P,(14.R5.(19.(11.&40.R>.)+20.))P,Pa,$8.P,(13.(14.R8.R1.)(17.R1.(2=.R8.+10.)))(2>.VL,R>.(11.&40.R11.)(12.$2;.VL,VHI,R10.)R2.)P,(2?.R9.R<.R;.)P,(30.$2;.R=.R<.)P,Pa,$8.P,(;.(31.R<.R1.))(32.(13.(14.(19.(11.&40.R14.)+20.)R2.)(17.R2.(11.&40.R14.)))(13.(14.R<.R2.)(17.R2.(2=.R<.+10.))))(9.$2;.VL,VHI,R11.R10.R>.R=.)")
(* [comment removed for export] *).
  Proof.
    intros sp h hc LBc mc m' moc W X lo HH HT HTOP ACL SLO XCW MU WM WC.
    eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH| exact ACL| exact MU| exact WM|].
    intros a Ha NO. rewrite HT. destruct (WC a NO) as [Hf|Hx]; [left; lia|].
    destruct (XCW a Hx) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L59308562768.30L59308579027.32L59308585861.30L59308743383.3400000<00X00c01BS2dX1a2Hx2O1S1L2sp2lo3DHI3ACL3SLO1a1C2HfS2sp1a1C2HfS1L2sp2lo3ACL3SLO1a1B1k1R2Hf2B4". (* [comment removed for export] *)
  Lemma run_presx : ltac2:(CDefT.buildp (gd_tbl_P_mpi_lset ()) "Psp,(0.&40.)PLB,(5.$6.)PdX,$7.Pm,P,(0.&40.)(2.(0.&8.))Pmc,P,(0.&40.)(2.(0.&8.))Pm',P,(0.&40.)(2.(0.&8.))PW,(5.$2<.)Plo,$8.P,(33.$2;.VL,R7.(11.&40.R8.)(34.R6.)R5.R4.)P,(35.(36.$8.$8.)Lb,(36.$8.$8.)(37.VL,(38.$8.$8.R1.)(39.$8.$8.R1.))R8.)P,(14.(1=.VL,)(1;.VL,))P,(14.(1;.VL,)R4.)P,(14.R5.(19.(11.&40.R<.)+20.))P,(2?.R7.R9.R8.)P,(30.$2;.R:.R9.)P,Pa,$8.P,(;.(31.R:.R1.))(32.(13.(14.(19.(11.&40.R11.)+20.)R2.)(17.R2.(11.&40.R11.)))(13.(14.(23.R?.)R2.)(17.R2.(2=.(23.R?.)+10.))))(33.$2;.VL,R?.(11.&40.R10.)(34.R>.)R=.R;.)")
(* [comment removed for export] *).
  Proof.
    intros sp LB dX m mc m' W lo HPX HBR DHI ACL SLO MU WM WC.
    eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Ho. destruct (outside_dec W a) as [O|NO]; [exact O| exfalso].
    destruct (WC a NO) as [Hf|Hx].
    - destruct Hc as [C|[C|([B k] & Hb & R)]]; [lia| destruct DIMG; lia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (_ & _ & _ & B4 & _); cbn in R, B4; lia].
    - cbn in Ho. flat constr:(Ho) 2%nat. flclear Ho. intros O1 _. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59308585861.2600000MS1L2sp2lo3DHI3ACL3SLO1a2Ha2Hf". (* [comment removed for export] *)
  Lemma run_statics : ltac2:(CDefT.buildp (gd_tbl_P_mpi_lset ()) "Psp,(0.&40.)Pmc,P,(0.&40.)(2.(0.&8.))Pm',P,(0.&40.)(2.(0.&8.))PW,(5.$2<.)PX,$8.Plo,$8.P,(21.$2;.VL,R5.)P,(14.(1=.VL,)(1;.VL,))P,(14.(1;.VL,)R3.)P,(14.R4.(19.(11.&40.R9.)+20.))P,Pa,$8.P,(13.(14.R7.R1.)(17.R1.(2=.R7.+10.)))P,(13.(14.(3:.VL,)R2.)(17.R2.(1=.VL,)))(3;.VL,R3.)P,(2?.R8.R:.R9.)P,Pa,$8.P,(;.(31.R:.R1.))(32.(13.(14.(19.(11.&40.R>.)+20.)R2.)(17.R2.(11.&40.R>.)))(13.(14.R:.R2.)(17.R2.(2=.R:.+10.))))(21.$2;.VL,R;.)")
(* [comment removed for export] *).
  Proof.
    intros sp mc m' W X lo SOK DHI ACL SLO XD MU WC.
    eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha NW. destruct (outside_dec W a) as [O|NO]; [exact O| exfalso].
    destruct (WC a NO) as [Hf|Hx]; [lia| exact (NW (XD a Hx Ha))].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac land3_zero p :=
    let E := fresh "E" in
    assert (E : Z.land p 3 = 0) by (change (Z.land p 3) with (Z.land p (Z.ones 2)); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; lia);
    rewrite ?E; clear E.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00R0@L14309835423.97 L14948133805.96 L15887591131.103L18871530766.97 L20042825086.102L21887662552.98 L23100341967.97 L25068783078.100L33351296353.97 L33510041944.98 L36269931622.102L38555123746.97 L38557272733.96 L39409836362.107L39409836362.108L39939502872.101L41562522430.100L50467811335.103L54398102733.108L56851291470.109L57124307491.102L59308562768.108L59308562768.109L59308579027.108L59314873579.107L59577446157.96 L59579458994.97 L62478642744.104L65699720142.107L65706006518.106L66083662040.98 L7922653143.102 L8323683058.103 L9962237875.98  00000800901B01J01X01c01k02802@02K02Y02Z02[02j03903K03V04U05905H05_06106D07N08J08R08Z09c0:c0;U0;`0<70=30=>S1X1n2P'FS1L2sp1X1n1z2lo2P'2n'3ACL3SLO3XAL2X04PAL'4NMAX3P0'3P4'3XP'2HB5Ha_st5Hl_stS1X1n2P'S1X1n2P'2n'2NLS2sp1X1n2P'S1X1n2P'S1X1n1z2P'2ZBS1X1n2P'S2sp1X1n2P'S1X1n2P'2n'2NLFFS1X1n2P'1a1H2H0S1X1n2P'1a1H2H0S2sp1X1n2lo2P'3SLOS2sp1X1n2P'S1L2sp1X1n1z2lo2P'2n'3ACL3SLO2X04NMAX3P0'3P4'2XS2HB5Ha_st5Hl_stS1L2HI2sp1h1X1n2lo2P'3SLO2X03P0'1a1CS1X1n2P'1a1H2H0S1X1n2P'2n'2X04NMAX3P0'S1X1n2P'1a2NO1H2O1S1X1n2P'1a2NO2H02O1S1L2sp1X1n2lo2P'2n'3ACL3SLO3DHI3XAL2X04PAL'4NMAX3P0'3P4'2PD3XP'1a2Ha2NO2H0S1L2sp1X1n2lo2P'2n'3ACL3SLO3DHI2X04NMAX3P0'3P4'2PD1a2Ha2NO1HS1X1n2P'S1X1n2P'S1L2sp1X1n1z2lo2P'2n'3ACL3SLO3XAL2X04PAL'4NMAX3P0'3P4'3XP'2HB5Ha_st5Hl_stS1L2sp1X1n2lo2P'2n'3ACL3SLO3XAL2X04PAL'4NMAX3P0'3P4'3XP'1a2NO2H0S1L2sp1X1n2lo2P'2n'3ACL3SLO2X04NMAX3P0'3P4'1a2NO1HS2sp1X1n2P'S1X1n2P'2n'2X04NMAX3P0'S1L2sp1X1n1z2lo2P'2n'3ACL3SLO2X04NMAX3P0'3P4'2HB5Ha_st5Hl_stS2sp1X1n2P'". (* [comment removed for export] *)
  Lemma L_TAIL : ltac2:(CDefT.buildp (gd_tbl_P_mpi_lset ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$2;.VL,VHI,)PLB,(5.$6.)PdX,$7.Pz,$8.Plo,$8.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px18,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm2,P,(0.&40.)(2.(0.&8.))Pmo2,$3.Ph2,(4.$2;.VL,VHI,)PLB',(5.$6.)PP',$8.Pn',$8.Psg,(0.&40.)P,(9.$2;.VL,VHI,R5.R4.R7.R6.)P,(<.$8.(12.$2;.VL,VHI,R6.)(12.$2;.VL,VHI,R1<.))P,(3<.R1>.R8.)P,(21.$2;.VL,R:.)P,(33.$2;.VL,R1>.(11.&40.R32.)(34.R1=.)R21.R;.)P,Pa,$8.P,(13.(14.(23.R1?.)R1.)(17.R1.(2=.(23.R1?.)+10.)))(2>.VL,R;.(11.&40.R35.)(12.$2;.VL,VHI,R22.)R2.)P,Pa,$8.P,(13.(14.(23.R20.)R1.)(17.R1.(2=.(23.R20.)+10.)))P,(13.(14.(3:.VL,)R2.)(17.R2.(1=.VL,)))(3;.VL,R3.)P,(14.(11.&40.R35.)(12.$2;.VL,VHI,R22.))P,(14.(1;.VL,)R1?.)P,(14.R20.(19.(11.&40.R37.)+20.))P,(17.(11.&40.R38.)(16.+2.+40.))P,(35.(36.$8.$8.)Lb,(36.$8.$8.)(37.VL,(38.$8.$8.R1.)(39.$8.$8.R1.))R25.)P,(14.(1=.VL,)(1;.VL,))P,(13.(14.(15.(16.+2.+1?.))R25.)(17.R25.(16.+2.+1?.)))P,(20.$2;.R15.)P,(18.$2;.R16.R26.(2=.(11.&40.R3=.)-20.))P,(3=.$2;.R17.(2=.(11.&40.R3>.)-20.)(3>.$3?.(40.R39.)(3>.$3?.(40.R3:.)(3>.$3?.(40.R3;.)(3>.$3?.(40.R3?.)(41.$3?.))))))P,(3=.$2;.R18.(23.R2:.)(3>.$3?.(40.(1>.&40.R14.))(3>.$3?.(42.R12.)(3>.$3?.(42.(1>.&40.R13.))(3>.$3?.(43.(44.R2:.))(41.$3?.))))))P,(<.$8.(1<.(23.R2;.)+8.)=)P,(17.=(23.R2<.))P,(14.(2=.(23.R2=.)+10.)(16.+2.+40.))P,(3=.$2;.R1<.R18.(3>.$3?.(43.(1>.&40.=))(41.$3?.)))P,(<.$8.(1<.R19.+10.)=)P,(45.(36.$8.$8.)(46.$8.$8.R1:.(47.+4.R19.))R1;.)P,(13.(14.+1.R1:.)(14.R1:.+2710.))P,(<.$8.R1;.(48.(49.R32.)+1.))P,(17.=R1=.)P,(14.(2=.R1>.(47.+4.R1=.))(1;.VL,))P,(32.(14.(2=.R1?.(47.+4.R1>.))(3:.VL,))(14.(1=.VL,)R1?.))P,(32.(14.(2=.(23.R36.)+10.)R20.)(14.(2=.R20.(47.+4.R1?.))(23.R36.)))P,(32.(14.(2=.(23.R37.)+10.)R35.)(14.(11.&40.R4<.)(23.R37.)))P,Pa,$8.P,(13.(14.R23.R1.)(17.R1.(2=.R23.+4.)))P,(4:.VL,R3;.(11.&40.R4?.)R2.)P,(31.(34.R3;.)R3.)$4;.P,Pm5,P,(0.&40.)(2.(0.&8.))Pw,(0.&40.)P,(3=.$2;.R2.R25.(3>.$3?.(4<.#4.(4=.R1.))(41.$3?.)))P,(2?.(3>.(36.$8.$8.)(46.$8.$8.(23.R3<.)(2=.(23.R3<.)+10.))(3>.(36.$8.$8.)(46.$8.$8.R26.(2=.R26.+4.))(41.(36.$8.$8.))))R2:.R3.)P,(30.$2;.R2;.R4.)(4>.$2;.R5.R28.(3>.(0.&40.)R4.(4?.(0.&40.)(1>.&40.=)(50.(19.R27.+1.)))))P,Psg',$8.Plimbs',(5.(0.&40.))(51.R3=.R3<.R27.(52.(23.R3<.)R2.R25.R26.R1.(44.R3<.)$53.))P,(32.(45.(36.$8.$8.)(46.$8.$8.R25.(47.+4.R24.))(54.R3;.))(;.(45.(36.$8.$8.)(46.$8.$8.R25.(47.+4.R24.))R3<.)))(24.$2;.R29.(25.$2;.VL,VHI,R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R3>.R3=.R3<.(26.R3;.R3<.R3=.)R3:.R40.R3?.)(27.(28.(1>.&40.+1?8:4.)(1>.&40.(2=.(11.&40.R51.)-20.))R50.R4?.R39.R38.R37.(1>.&40.(23.R3<.))(1>.&40.R3;.)(1>.&40.R26.)R36.R35.R34.R33.R32.R31.R30.R2?.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R2>.R2=.R2<.R2;.)R42.(1>.&40.+1?8:4.)R41.(29.(0.&40.))R2:.(2:.$2;.)))")
(* [comment removed for export] *).
  Proof.
    intros until sg. destruct dX as [X sg0 n P limbs pad own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
    intros HH2 HT2 MF2 SOK2 HPX2 XCW XD HTOP ACL SLO SPB HBR DHI ZB MI2 ST2 FR CH XAL X0 X16 PZ0 PAL' PIN' NL NMAX P0' P4' PD XP' XS PFR LIMBS MO AFR.
    pose proof alloc_ceiling_pos as ACP. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    pose proof (conj HH2 I) as HH2c. pose proof (conj SOK2 I) as SOK2c. clear HH2 SOK2.
    pose proof (munch_refl [(X, X + 16); (P', P' + 4)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof (@alloc_ceiling_bounds L) as ACB.
    assert (NZP : bv_eqb (Z_to_bv 64 P') (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
    zstep. zstep. rewrite NZP; cbv_concl_iota. zstep. land3_zero P'.
    zstep. if_false. clear ACB NZP.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => match goal with H : stk usegs mx _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
    zstep.
    flat constr:(HH2c) 2%nat. flclear HH2c. intros HH2 _. flat constr:(SOK2c) 2%nat. flclear SOK2c. intros SOK2 _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : rw_cells usegs m5 X _ |- _ => rename H into CH5 end.
    match goal with H : rw_cells usegs m5 P' _ |- _ => rename H into PZ5 end.
    apply (rw_cells_C2_congr usegs m5 X [C8 (Z_to_bv 64 P')] _ (if z <? 0 then -1 else 1)) in CH5; [| apply to_sign_mod16; lia].
    lazymatch type of PZ5 with rw_cells _ _ _ [C4 ?w] => set (w0 := w) in PZ5 end.
    assert (PZ5' : rw_cells usegs m5 P' [CB 4 (le4 w0)]).
    { eapply rw_cells_reshape; [exact PZ5| cbn -[le4]; split; [apply length_le4| exact I] | cbn -[le4]; reflexivity]. }
    apply aevtM_done. unfold mpi_binop_post. flexi 16%nat. exists h2.
    exists LB', (mkMPD X (if z <? 0 then -1 else 1) n' P' (w0 :: repeat (Z_to_bv 64 0) (Z.to_nat (n' - 1))) pad LHeap), 0.
    split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact MF2|]. split; [exact HT2|].
    split. { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH2| exact ACL| exact MU| exact WM|].
      intros a Ha NO. cbn in NO. rewrite HT2.
      destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [destruct (XCW a ltac:(lia)) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C] |]|].
      all: right; right; exists (P', 4 * n'); split; [exact PIN'| cbn; lia]. }
    split. { split; [| cbn; destruct (z <? 0); [right| left]; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CH5|]. split; [exact XAL|]. split; [exact X0|]. split; [cbn [length]; rewrite repeat_length; lia|]. split; [unfold MPI_MAX_LIMBS; lia|].
      split; [lia|]. split; [exact PIN'|]. split; [exact PAL'|]. exact (LIMBS m5 w0 PZ5' MU WM). }
    split; [exact (MO _ _)|].
    split. { eapply heap_presx_trans; [exact HPX2|]. eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho.
      destruct (outside_dec [(X, X + 16); (P', P' + 4)] a) as [O|NO]; [exact O| exfalso]. cbn in NO.
      destruct (Z.le_gt_cases P' a); [destruct (Z.lt_ge_cases a (P' + 4)); [exact (PFR a ltac:(lia) Hc Ho)|]|]; cbn in Ho; (flat constr:(Ho) 2%nat; flclear Ho; intros O1 _); lia. }
    split. { eapply statics_ok_munch; [exact SOK2| exact MU|]. intros a Ha NW.
      destruct (outside_dec [(X, X + 16); (P', P' + 4)] a) as [O|NO]; [exact O| exfalso]. cbn in NO.
      destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [exact (NW (XD a ltac:(lia) Ha))|]|]; lia. }
    unfold lset_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk].
    split; [left; split; [reflexivity|]; split; [lia|]; split; [reflexivity|]; split; [eexists; reflexivity| split; reflexivity]|].
    split; [reflexivity|]. intros b [<-|[]]. exact AFR.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01V0@D1429363837.106 D29471186428.106L10041968289.0  L10110901746.101L11668620365.96 L11670653879.98 L11742676846.113L12292857614.134L15327658209.93 L16628975680.83 L18468879667.116L1943863265.79  L19730768531.106L22700267513.115L22702002814.110L22706563396.135L23431794531.115L26106920326.83 L28812073595.118L28814103937.116L29300996232.100L29300996232.101L29300996232.119L29300996232.120L29300996232.121L29300996232.90 L29300996232.91 L29300996232.92 L29300996232.99 L2936939567.131 L29769722245.107L33226917280.133L34261378459.111L34265930351.131L34290115814.85 L34510058176.113L38441453918.84 L39330466957.116L39332496247.118L40238812268.134L40823233389.84 L41560443984.107L41560573297.89 L41560573297.98 L41560573303.118L41560655089.88 L41560655089.97 L41560656314.127L41570799093.117L41570977777.90 L41570977777.99 L41570977783.119L41930136202.106L43055153712.83 L43155117305.131L43781938198.127L43781986812.107L45376681122.107L45377024328.127L46287989547.135L50716086261.114L51209632897.116L51209632897.120L51796838330.114L5285886713.106 L53251959398.84 L53518944813.116L53518944813.96 L55065257727.131L55799931056.123L56529457971.107L59308551673.97 L59308562897.115L59308579027.119L59308579414.133L59308579414.139L59308579543.137L59308579668.92 L59308587026.135L59314873579.120L59315317366.116L61263218231.134L6332324384.112 L6332324384.116 L63691941651.106L64638675.98    L65357022237.111L65500066615.113L65502163868.81 L65803042429.114L66797865.96    L6739891305.133 L6739899949.141 L6739900076.139 L6753770045.84  L68238445262.98 L7190686615.102 L7193126325.84  L772750287.81   R14801101130.106R22706563525.138R22706564033.11800000>00?00@01701m02c03]04K04b05=05Z05o06=06V07607M07e08F09409b0:80:N0:c0;80;M0;`0<30<F0<\0=10=J0>A0>R0>l0?;0?K0?e0@50@E0@X0@f0AN0B00BX0C?0Ca0DI0E00EW0F90Fa0GH0GV0H90HL0H`0I50IF0IV0Ik0J^0J_0KX0LC0LD0L[0Lk0M<0ML0Mg0N50NL0OJ0PI0PW0QS0RU0Rg0S\0TY0UR0V80V90W:0WH0Wk0XK0X[0Xj0Y@0Yc0ZU0[N0\M0\[0]?0]i0^S0_60_D0_m0`XS2sp1X2XB4LXKTFSS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X03LEN2XB2P04PRNGS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P04PRNG2H2S1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P04PRNG2H2S1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3DHI3SPB2X02XB2P02P51H2H0S1L3HLS2sp1X2lo3SLO3ACL3SPB2X02XB4LXKT1A2A02A4S2sp1X1n5limbs2NR2XB2H2S1L2sp1X1n1P5limbs2XB2P02P4S2sp1X1n1P5limbs3SPB2X02XB2P0S1L2sp1X5limbs3ACP2XBS2sp1X2XB4LXKTS2sp1X1n1P5limbs2XB3x141HS2sp1X1n1P5limbs3SPB2X02XB2P02H2S2sp1X2XB4LXKT1A3x282H3S2sp1X1n1P5limbs2XB1a2NOS2sp1X1n1b5limbs3SPB2X03LEN2XB2N0S1L3HLS2sp1X2lo3SLO3ACL3SPB2X02XB4LXKT1A2A02A4S1L3HLS2sp1X2lo3SLO3ACL3SPB2X02XB4LXKT1A2A02A4S2sp1X1P5limbs2XB1a2NOS2sp1X1P5limbs2XB1a2NOS2sp1X2XB4LXKT1A1a2NOS2sp1X2XB4LXKT1A1a2NOS2sp1X2XB4LXKT1A1a2NOS2sp1X2XB4LXKT1a2NOS2sp1X2XB4LXKT1a2NOS2sp1X2XB4LXKT1a2NOS2sp1X1P5limbs2XB1a2NOS1L2sp1X2XB4LXKT1A2A4S2sp1X1n1P5limbs2NR2XB2N1S1L3HLS2sp1X2lo3SLO3ACL3SPB2X02XB4LXKT1A2A02A42A52H32H4S2sp1X1P5limbs2XBS2sp1X3SPB2X02XB4LXKT1A2A0S2sp1X5limbs2XBS2sp1X2XB4LXKT1AS1L2HI2sp1h1X4HTOP2XB4LXKTS2sp1X2XB4LXKT1AS2sp1X2XB4LXKT1AS2sp1X2XB4LXKT1A2XAS2sp1X2XB4LXKTS1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X2lo3SLO3SPB2X02XB4LXKTS1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X2lo3SLO3SPB2X02XB4LXKT1A2A0S1L3HLS2sp1X2lo3SLO3SPB2X02XB4LXKTS1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X2lo3SLO3SPB2X02XB4LXKT1A2A0S1L3HLS2sp1X2lo3SLO3SPB2X02XB4LXKT1A2A0S1L3HLS2sp1X2lo3SLO3SPB2X02XB4LXKTS1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X2lo3SLO3SPB2X02XB4LXKT1A2A0S2sp1X2XB4LXKTS1L3HLS2sp1X5limbs2lo3SLO3SPB2X02XBS2sp1X2XB4LXKT1A2XAS2sp1X3SPB2XB4LXKT1AS2sp1X1P5limbs3SPB2XBS2sp1X1P5limbs2XBS2sp1X2XB4LXKT1AS2sp1X2XB4LXKT1A1a2NOS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P04PRNGFS1L3HLS2sp1X2lo3SLO3ACL3SPB3XAL2X02XB4LXKT1A2A03A162A42XAS1L2sp1X1n1P5limbs2lo3ACL3SPB2X02XB2P04PRNGFS1L2sp1X2lo3SLO2XB4LXKTS2sp1X2XB4LXKT1AS2sp1X1P5limbs2XBS2sp1X2XB4LXKT1AS1L2HI2sp1h1X2XB4LXKT1A1a1CS2sp1X2XB4LXKTS2sp1X1n5limbs2XB2N12H2S1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P04PRNG2H21a2Ha2O2S1L3HLS2sp1X2lo3SLO3ACL3SPB2X02XB4LXKT1A2A02A42A51a2Ha1C1D1H2H0S2sp1X2XB1A2H3S1L3HLS2sp1X2lo3SLO3ACL3SPB2X02XB4LXKT1A2A02A41a2Ha1B1k1R2H3S1L3HLS2sp1X2lo3SLO3ACL3DHI3SPB2X02XB4LXKT1A2A02A42A51a2Ha1C2H32H4S2sp1X5limbs2XB2H2S1L3HLS2sp1X2lo3SLO3ACL3SPB2X02XB4LXKT1A2A02A41a2Ha1CS1L3HLS2sp1X2lo3SLO3ACL3SPB2X02XB4LXKT1A2A02A41a2Ha1C1B1k1R1HS1L2HI3HLS2sp1h1X2lo3SLO3ACL3SPB2X02XB4LXKT1A2A02A41a1C1SS1L2sp1X2lo3ACL3SPB2X02XB4LXKT1A2A02A4FS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB3XAL2X02XP2XB3PAL2P04PRNG2H2S2sp1X2XB4LXKTS2sp1X1n1P5limbs3SPB2X02NR2XB2P02H2S2sp1X1n1P5limbs3SPB2X02XB2N12P0S2sp1X2XB4LXKT1AS2sp1X5limbs2XBS2sp1X1n1P5limbs2XP2XBS2sp1X1n1P5limbs3SPB2X02NR2XB2P02H2S1L3HLS2sp1X2lo3SLO3ACL3SPB2X02XB4LXKT1A2A02A41a1CS1L3HLS2sp1X2lo3SLO3ACL3SPB2X02XB4LXKT1A2A02A41a1B1k1R2H3S1L3HLS2sp1X2lo3SLO3ACL3DHI3SPB2X02XB4LXKT1A2A02A42A51a1C2H32H4S2sp1X2XB4LXKTS2sp1X1n1P5limbs3SPB2X03LEN2XB2P02H2S1L3HLS2sp1X2lo3SLO3ACL3ACP3SPB2X02XB4LXKTS1L3HLS2sp1X2lo3SLO3ACL3ACP3SPB2X02XB4LXKTS1L3HLS2sp1X5limbs2lo3SLO3SPB2X02XBS2sp1X2XB4LXKTS1L4DIMG2sp1X3SPB2X02XB4LXKT1A2A02A51a2H3S1L4DIMG2sp1X1n1P5limbs3SPB2X02XB2P02P51a1H". (* [comment removed for export] *)
  Lemma U_mpi_lset_spec : mpi_lset_stmt usegs L HI U_MPI_LSET U_MEMSET_FUNC.
  Proof.
    unfold mpi_lset_stmt, U_MPI_LSET. intros until lo. intros HH MA NST XW ZB ST SLO ACL HTOP SPA DHI TP MI SOK CA -> ->.
    clear HFREE.   (* [comment removed for export] *)
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP. pose proof (HND _ _ _ _ HH) as ND.
    destruct dX as [X sg n P limbs pad own].
    flat constr:(MA) 2%nat. flclear MA. intros FLt1 SG. flat constr:(FLt1) 6%nat. flclear FLt1. intros CH XAL X0 LEN NR OWN. unfold mpi_cells in CH.
    flat constr:(XW) 3%nat. flclear XW. intros XCW XD XP. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    unfold MPI_MAX_LIMBS in NR. pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as XS.
    (* [comment removed for export] *)
    assert (OWF : (own = LNull /\ P = 0 /\ n = 0 /\ limbs = []) \/ (own = LHeap /\ 1 <= n /\ In (P, 4 * n) LB /\ P mod 16 = 0 /\ u32arr usegs m P limbs /\ 0 < P /\ P + 4 * n <= alloc_ceiling)).
    { destruct own as [| |]; [left| right| exfalso; exact (NST eq_refl)].
      - flat constr:(OWN) 2%nat. flclear OWN. intros P0 N0. split; [reflexivity|]. split; [exact P0|]. split; [exact N0|]. destruct limbs; [reflexivity| cbn in LEN; lia].
      - flat constr:(OWN) 4%nat. flclear OWN. intros N1 PIN PAL PCH. flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5.
        split; [reflexivity|]. split; [exact N1|]. split; [exact PIN|]. split; [exact PAL|]. split; [exact PCH|]. split; [exact P0| exact P4]. }
    clear OWN.
    assert (PRNG : 0 <= P /\ P + 4 * n <= alloc_ceiling) by (destruct OWF as [(_ & -> & -> & _)|(_ & _ & _ & _ & _ & P0 & P4)]; lia).
    carve_frame 32%nat ST.
    assert (HPX0 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad own)) m m) by apply heap_presx_refl.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x46e44; 0x3f960] [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hm : munch ?W ?mA mx, Hw : wmono _ ?mA' mx |- _ => rename Hm into MU1; rename Hw into WM1; rename mx into m1 end end.
    (* [comment removed for export] *)
    2: {
      destruct OWF as [(_ & _ & -> & _)|(-> & N1 & PIN & PAL & PCH & P0 & P4)]; [exfalso; flia|]. specialize (XP eq_refl).
      flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros _ _ _ _ P5. cbn in P5.
      lazymatch goal with Hc : rw_cells _ m1 X _, Hf : rw_cells _ m1 (bv_unsigned sp + -32) _, Hs : stk _ m1 _ _, Hi : mem_inv _ m1 |- _ =>
        rename Hc into CH1; rename Hf into FR1; rename Hs into ST1; rename Hi into MI1 end.
      pose proof (run_heap sp h h LB m m1 mo _ X lo HH eq_refl HTOP ACL ltac:(flia) XCW MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HH1.
      pose proof (run_statics sp m m1 _ X lo SOK DHI ACL ltac:(flia) XD MU1 ltac:(intros a NO; cbn in NO |- *; flia)) as SOK1.
      pose proof (run_presx sp LB _ m m m1 _ lo HPX0 HBR DHI ACL ltac:(flia) MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HPX1.
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
      lazymatch type of MU1 with munch ?W _ _ => apply (u32arr_transport usegs W m m1) in PCH; [| exact MU1| exact WM1| cbn; flia] end.
      clear ST MI CH FR MK MU1 WM1 HPX0 HH SOK.
      pose proof (munch_refl [(P, P + 4 * n)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      apply u32arr_cells in PCH.
      pose proof U_memset_spec as SPs. unfold memset_stmt in SPs.
      eapply aevtM_cut_evt; [ exact MK1 | eapply SPs; rewrite ?unsigned_lit by lia; [ replace (Z.to_nat (4 * n)) with (4 * length limbs)%nat by lia; exact PCH | assumption ] | ].
      clear SPs PCH. unfold memset_post. rewrite !unsigned_lit by lia. post_call usegs m1.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      match goal with H : rw_cells usegs m2 P _ |- _ => rename H into PZ end.
      assert (HH2 : HEAP usegs L HI h LB m2 mo).
      { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH1| exact ACL| exact MU| exact WM|].
        intros a Ha NO. cbn in NO. right; right. exists (P, 4 * n). split; [exact PIN| cbn; lia]. }
      assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad LHeap)) m m2).
      { eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
        intros a Ha Hc Ho. cbn in Ho |- *. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _. split; [exact O2| exact I]. }
      clear HH1 HPX1 MU WM.
      assert (PZ' : rw_cells usegs m2 P ([C4 (Z_to_bv 64 0)] ++ [CB (Z.to_nat (4 * n - 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * n - 4)))])).
      { eapply rw_cells_reshape; [exact PZ| |].
        - cbn. rewrite repeat_length. (flsplit; repeat split); reflexivity.
        - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. change (le4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 4).
          rewrite <- repeat_app. f_equal. lia. }
      apply rw_cells_app in PZ'. flat constr:(PZ') 2%nat. flclear PZ'. intros PZ0 PZR. cbn [cells_size csize Nat.add] in PZR. clear PZ.
      replace (P + Z.of_nat 4) with (P + 4) in PZR by lia.
      try lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with Hc : rw_cells _ m2 X _, Hf : rw_cells _ m2 (bv_unsigned sp + -32) _ |- _ =>
      eapply L_TAIL; [exact HH2| reflexivity| apply mo_frame_refl| assumption| exact HPX2| exact XCW| exact XD| exact HTOP| exact ACL| flia| flia| exact HBR| exact DHI
        | exact ZB| assumption| assumption| exact Hf| exact Hc| exact XAL| exact X0| cbn [md_addr]; flia| exact PZ0
        | exact PAL| exact PIN| cbn [md_n]; flia| cbn [md_n]; lia| exact P0| exact P4| destruct DIMG; lia| cbn [md_addr]; exact XP| exact XS
        | intros a Ha Hc' Ho; cbn in Ho; (flat constr:(Ho) 3%nat; flclear Ho; intros _ O2 _); lia
        | intros m5 w PZ5 MU5 WM5; cbn [md_addr] in MU5;
          apply (rw_cells_transport usegs [(X, X + 16); (P, P + 4)] m2 m5) in PZR; [| exact MU5| exact WM5| cbn; flia];
          change (w :: repeat (Z_to_bv 64 0) (Z.to_nat (n - 1))) with ([w] ++ repeat (Z_to_bv 64 0) (Z.to_nat (n - 1)));
          apply u32arr_app; split;
          [ eapply u32arr_of_cells; [exact PZ5|]; cbn; rewrite ?app_nil_r; reflexivity
          | cbn [length Z.of_nat Pos.of_succ_nat]; eapply u32arr_of_cells; [exact PZR|]; rewrite u32s_repeat0; f_equal; lia ]
        | intros sg' limbs'; apply mpd_out_same_blocks; cbn; [reflexivity| discriminate| reflexivity]
        | cbn; left; left; reflexivity ] end. }
    (* [comment removed for export] *)
    assert (NZ : n = 0) by flia. destruct OWF as [(-> & -> & -> & ->)|(_ & N1 & _)]; [| exfalso; lia]. clear NZ LEN.
    lazymatch goal with Hc : rw_cells _ m1 X _, Hf : rw_cells _ m1 (bv_unsigned sp + -32) _, Hs : stk _ m1 _ _, Hi : mem_inv _ m1 |- _ =>
      rename Hc into CH1; rename Hf into FR1; rename Hs into ST1; rename Hi into MI1 end.
    pose proof (run_heap sp h h LB m m1 mo _ X lo HH eq_refl HTOP ACL ltac:(flia) XCW MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HH1.
    pose proof (run_statics sp m m1 _ X lo SOK DHI ACL ltac:(flia) XD MU1 ltac:(intros a NO; cbn in NO |- *; flia)) as SOK1.
    pose proof (run_presx sp LB _ m m m1 _ lo HPX0 HBR DHI ACL ltac:(flia) MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HPX1.
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    clear ST MI CH FR MK MU1 WM1 HPX0 HH SOK.
    replace (Z_to_bv 64 0x3f960) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := 1) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia; try eassumption; try reflexivity; try lia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
    destruct_ands PO.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match goal with H : heap_pres _ _ _ _ m1 m2 |- _ => rename H into HPc end.
    match goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end.
    match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    match goal with H : mo_frame mo mo2 |- _ => rename H into MF2 end.
    heap_transport HPc.
    assert (SOK2 : statics_ok usegs L m2) by (eapply statics_ok_heap_pres; [exact SOK1| exact HPc| exact SW]).
    assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg 0 0 [] pad LNull)) m m2).
    { eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_pres_sub; [exact HPc| intros b Hb; exact Hb| lia| lia]. }
    clear HH1 SOK1 HPX1 HPc MK1. try clear ST1. try clear MI1. try clear m1.
    destruct PO as (h2 & HT2 & [[-> HH2] | (A & -> & HBA & HH2 & HNEW)]); pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    { (* [comment removed for export] *)
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK2).
      lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
      all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
      lazymatch goal with Hc : rw_cells _ m2 X _ |- _ => rename Hc into CH end.
      apply aevtM_done. unfold mpi_binop_post. flexi 16%nat. exists h2.
      exists LB, (mkMPD X sg 0 0 [] pad LNull), MBEDTLS_ERR_MPI_ALLOC_FAILED.
      split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact MF2|]. split; [exact HT2|].
      split; [exact HH2|].
      split; [ split; [|exact SG]; split; [exact CH|]; split; [exact XAL|]; split; [exact X0|]; split; [reflexivity|]; split; [cbn [md_n]; unfold MPI_MAX_LIMBS; lia|];
               cbn [md_own md_n md_p md_limbs]; split; reflexivity |].
      split; [apply mpd_out_refl; cbn; discriminate|].
      split; [exact HPX2|].
      split; [exact SOK2|].
      unfold lset_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk]. split; [right; split; reflexivity|]. split; [reflexivity|]. intros b []. }
    (* [comment removed for export] *)
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 HAP2. pose proof (HND _ _ _ _ HH2) as ND2.
    pose proof HBA as HBA'. flat constr:(HBA') 5%nat. flclear HBA'. intros A0 A16 _ A4 A5. flat constr:(HAP2) 2%nat. flclear HAP2. intros HAPA _.
    assert (XA' : forall a, X <= a < X + 16 -> ~ (A <= a < A + 1 * 4)).
    { intros a Ha C. destruct (XCW a Ha) as [S|[[D NS]|([B k] & Hb & R)]]; [lia| destruct DIMG; lia| pose proof (HAPA B k Hb); cbn in R; lia]. }
    pose proof (pointwise_apart X 16 A (1 * 4) ltac:(lia) ltac:(lia) XA') as XA. clear XA'.
    lazymatch type of HNEW with ?T => change (lx_hidden T) in HNEW end.
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK2).
    lx_run_tac (PLANS [0x46e44] [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs; unfold lx_hidden in HNEW.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with Hm : munch ?W m2 m3, Hw : wmono _ m2 m3 |- _ =>
      rename Hm into MU3; rename Hw into WM3; apply (rw_cells_transport usegs W m2 m3) in HNEW; [| exact MU3| exact WM3| cbn; flia] end.
    assert (XCW5 : forall a, X <= a < X + 16 -> client_waddr L ((A, 1 * 4) :: LB) (bv_unsigned sp) (heap_top usegs L HI h) a).
    { intros a Ha. destruct (XCW a Ha) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists (B, k); split; [right; exact Hb|exact R]]. }
    pose proof (run_heap sp h h2 _ m2 m3 mo2 _ X lo HH2 HT2 HTOP ACL ltac:(flia) XCW5 MU3 WM3 ltac:(intros a NO; cbn in NO |- *; flia)) as HH3.
    pose proof (run_statics sp m2 m3 _ X lo SOK2 DHI ACL ltac:(flia) XD MU3 ltac:(intros a NO; cbn in NO |- *; flia)) as SOK3.
    pose proof (run_presx sp LB _ m m2 m3 _ lo HPX2 HBR DHI ACL ltac:(flia) MU3 WM3 ltac:(intros a NO; cbn in NO |- *; flia)) as HPX3.
    clear MU3 WM3 HH2 SOK2 HPX2.
    repeat match goal with H : stk _ m2 _ _ |- _ => clear H | H : mem_inv _ m2 |- _ => clear H | H : rw_cells _ m2 _ _ |- _ => clear H end.
    (* [comment removed for export] *)
    pose proof (munch_refl [(A, A + 4)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    pose proof U_memset_spec as SPs. unfold memset_stmt in SPs.
    eapply aevtM_cut_evt; [ exact MK2 | eapply SPs; rewrite ?unsigned_lit by lia; [ exact HNEW | assumption ] | ].
    clear SPs HNEW. unfold memset_post. rewrite !unsigned_lit by lia. post_call usegs m3.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    match goal with H : rw_cells usegs m4 A _ |- _ => rename H into PZ end.
    assert (PZ' : rw_cells usegs m4 A [C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_reshape; [exact PZ| cbn; (flsplit; repeat split); reflexivity | cbn -[le4]; reflexivity]. }
    clear PZ.
    assert (HH4 : HEAP usegs L HI h2 ((A, 1 * 4) :: LB) m4 mo2).
    { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH3| exact ACL| exact MU| exact WM|].
      intros a Ha NO. cbn in NO. right; right. exists (A, 1 * 4). split; [left; reflexivity| cbn; lia]. }
    assert (HPX4 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg 0 0 [] pad LNull)) m m4).
    { eapply heap_presx_trans; [exact HPX3|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [C|[C|([B k] & Hb & R)]]; [flia| destruct DIMG; lia| pose proof (HAPA B k Hb); cbn in R; lia]. }
    assert (MOx : forall sg' limbs', mpd_out LB (mkMPD X sg 0 0 [] pad LNull) ((A, 1 * 4) :: LB) (mkMPD X sg' 1 A limbs' pad LHeap)).
    { intros sg' limbs'. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
      split. { intros b [<-|Hb]; [right; left; reflexivity| left; exact Hb]. }
      split. { intros b Hb Hn. right. exact Hb. }
      intros b []. }
    clear HH3 HPX3 MU WM.
    try lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with Hc : rw_cells _ m4 X _, Hf : rw_cells _ m4 (bv_unsigned sp + -32) _ |- _ =>
    eapply L_TAIL; [exact HH4| exact HT2| exact MF2| assumption| exact HPX4| exact XCW5| exact XD| exact HTOP| exact ACL| flia| flia| exact HBR| exact DHI
      | exact ZB| assumption| assumption| exact Hf| exact Hc| exact XAL| exact X0| cbn [md_addr]; flia| exact PZ'
      | exact A16| left; reflexivity| lia| cbn [md_n]; lia| exact A0| lia| destruct DIMG; lia| cbn [md_addr]; lia| exact XS
      | intros a Ha Hc' Ho; destruct Hc' as [C|[C|([B k] & Hb & R)]]; [lia| destruct DIMG; lia| pose proof (HAPA B k Hb); cbn in R; lia]
      | intros m5 w PZ5 MU5 WM5; eapply u32arr_of_cells; [exact PZ5|]; cbn; rewrite ?app_nil_r; reflexivity
      | exact MOx
      | cbn [mpd_blk md_own md_p md_n]; right; intros Hin; pose proof (HAPA A 4 Hin); lia ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End LS.
