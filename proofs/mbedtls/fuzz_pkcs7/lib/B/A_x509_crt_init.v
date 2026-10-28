(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxA_sums.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P033148a789ace5fa 0 4 1 1 2 1 41 1 42 1P04cc0d60835aa72e 0 5 0 1 31 1 34 1 39 1 40 1P04e878c6e4b6ddac 0 4 0 1 30 1 39 1 40 1P05a82cb96cfbe237 0 2 0 1 32 1P09b8850770acbde7 0 5 0 1 33 1 36 1 41 1 42 1P0bad487fe258c2ce 0 6 0 1 2 1 33 1 36 1 41 1 42 1P0d1f3ec236e8c7c1 0 4 0 1 31 1 39 1 40 1P0db1500716760858 0 5 0 1 31 1 34 1 39 1 40 1P0f691351f22c1654 0 5 0 1 31 1 34 1 39 1 40 1P1110a653e7270325 0 4 0 1 30 1 39 1 40 1P11e1371dcdd55404 0 6 0 1 2 1 33 1 36 1 41 1 42 1P12ee79a30579c6bb 0 5 0 1 31 1 34 1 39 1 40 1P14d675efc580f139 0 6 0 1 31 1 32 1 34 1 39 1 40 1P15053961bb980936 0 4 0 1 30 1 39 1 40 1P160125b045e4f0d4 0 2 0 1 32 1P16b64e2660c175ae 0 2 0 1 2 1P184cda97361b194a 0 4 1 1 2 1 41 1 42 1P19fd9e47eaaa45ac 0 2 0 1 32 1P1a5afcd20e6f6cfe 2 31 0 6 0 1 2 1 33 1 36 1 41 1 42 1 0 4 0 1 1 1 41 1 42 1P1d95b9a14c430f12 0 5 0 1 31 1 34 1 39 1 40 1P1deb3c0698c37b31 0 4 1 1 2 1 41 1 42 1P1eb1c49ad0e70c08 0 5 0 1 33 1 36 1 41 1 42 1P1ff7869c5ed2290b 1 1 16 2 0 1 39 1 3 3 1 40 1 41 16P2178d3dd17030394 0 5 0 1 31 1 34 1 39 1 40 1P231af431bab3eb67 0 2 0 1 32 1P2391a77dcf2d9688 2 31 0 6 0 1 2 1 33 1 36 1 41 1 42 1 0 4 0 1 1 1 41 1 42 1P250ed36137194a1a 0 4 0 1 30 1 39 1 40 1P26803bd2e53fe445 0 5 0 1 31 1 34 1 39 1 40 1P271fb8bc065a32c1 1 1 16 2 0 1 39 1 3 3 1 40 1 41 16P2a84d50aa679dbd3 0 4 0 16 2 16 39 16 40 16P2e6db3a80363ae25 0 4 0 1 31 1 39 1 40 1P2eb4bc2474afbf99 0 5 0 1 33 1 36 1 41 1 42 1P2ef1f49f7eaffd6b 0 6 0 1 31 1 32 1 34 1 39 1 40 1P2f760cc03fb57913 0 4 0 1 30 1 39 1 40 1P342ad651bcb18bb0 0 5 0 1 33 1 36 1 41 1 42 1P35a7f4b62bed0b53 0 2 0 1 2 1P35e0a02c16899b40 0 5 0 1 31 1 34 1 39 1 40 1P3a70fa8b6790b69a 0 4 0 1 30 1 39 1 40 1P3bc3cf2c32b57879 0 4 0 16 2 16 39 16 40 16P3e3bfbc0cb6fc5ed 0 4 1 1 2 1 41 1 42 1N015a0347873bb38aN02443bd42de2a372N039ad345c34ae342N0465d5a75e53be97N094e8df7a7c195a2N0c360b8a84b9100cN0d606c5bd215b62eN147b291cfa4732b4N17dd7bff6a369acdN194b9753752a5865N1e0a940d6fb076b5N1ebd7bc4f0725383N219f656108d7bf14N21b886a54536861bN2867ce300dabc501N28c8ff12a9a940e8N28ff30b1a0d47407N29d87daaa32fbbb9N29f4538ea1e137f3N2b053f46bb3b0f24N2c58e6147ccec079N2d2c1524ecf66a97N2d6e69d076b4e9a2N36483104ab048d01N386fff6502df0e14N3d24989920968385N3e011827ec92f6c8N3e9ab50afbdbe240"%lxh.
Ltac2 gd_tbl_A_x509_crt_init () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "struct_init_postA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "A_AMEMSET_I"; "struct_init_stmtA"; "A_X509_CRT_INIT"; "X509_CRT_INIT_SIZE"; "A_PKCS7_INIT"; "PKCS7_INIT_SIZE"].


Definition A_X509_CRT_INIT : Z := 0x0aa030.   (* [comment removed for export] *)
Definition A_PKCS7_INIT : Z := 0x097788.      (* [comment removed for export] *)
Definition A_AMEMSET_I : Z := 0x68258.        (* [comment removed for export] *) (* [comment removed for export] *)
Definition X509_CRT_INIT_SIZE : Z := 744.
Definition PKCS7_INIT_SIZE : Z := 1440.

(* [comment removed for export] *)
Notation STRUCT_INIT_STACK_A := 16 (only parsing).

Definition struct_init_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_init ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O16.O15.O14.O13.R10.R?.R>.O12.O11.R=.R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(8.O16.)O5.(9.(2.&40.))R1.(:.O1<.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.O4.(10.O4.O3.))(<.(=.$>.$>.)(?.$>.$>.O2.(11.&40.O15.))(12.(=.$>.$>.))))O1.R1.)(4.(13.O1<.O1.R1.)(4.(14.O1<.R1.)(4.(15.O1<.R1.O4.(<.$16.(17.(18.O3.)(19.(2.&8.)(1:.&8.=)(18.O3.)))(12.$16.)))(4.(1;.O1<.R1.O2.(11.&40.O15.))(1<.O1<.O1;.O1:.O19.O18.O17.R1.)))))))))))))))))))))))")
(* [comment removed for export] *).

Definition struct_init_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY n : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_init ()) "Ph,(1=.O5.O4.O3.)PLB,(1>.$1?.)PLF,(1>.$1?.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$>.Plo,$>.Pjunk,(1>.(2.&8.))P,(1<.O5.O4.O3.R28.R27.R26.R4.)P,(15.O5.R5.R4.(<.$16.(17.(18.O1.)R2.)(12.$16.)))P,(21.=R5.)P,(1;.O5.R7.R5.(11.&40.R27.))P,(22.(23.O4.)R6.)P,(22.R7.(24.(24.(11.&40.R29.)+10.)(25.O4.)))P,(22.(11.&40.R2:.)(26.O5.O4.O3.R2>.))P,(5.$>.(27.(11.&40.R2;.)+10.)=)P,(28.(22.(10.R;.O1.)R:.)(22.(11.&40.R2<.)R;.))P,(14.O5.R=.)P,(29.O5.(2:.O4.)(2;.O5.O4.O3.R32.)R>.R=.O1.)P,(2<.(2=.O4.)(2>.$1?.R32.(2?.R31.))(23.O4.)(26.O5.O4.O3.R33.)R>.O1.)P,(5.(2.&40.)R28.(1:.&40.R?.))(30.O5.(2:.O4.)(2;.O5.O4.O3.R35.)(31.O5.O4.O3.R35.R34.R33.R32.R31.R30.R2?.R2;.R2:.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R13.R12.R10.O1.R?.R11.)(6.(7.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R13.(1:.&40.O2.)R12.(9.(2.&40.))R11.(:.O5.)))")
(* [comment removed for export] *).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis AMS : arl_amemset R = A_AMEMSET_I.
  Hypothesis NEED0 : 0 <= arl_need_amem R.

  Lemma A_x509_crt_init_walk : struct_init_stmtA asegs R HIA A_X509_CRT_INIT X509_CRT_INIT_SIZE.
  Proof.
    unfold struct_init_stmtA, A_X509_CRT_INIT, X509_CRT_INIT_SIZE.
    intros until junk. intros HH HB HA ST LOS SLO TOP SPA DS MI OA CWA ->.
    pose proof (hcs_ok asegs R HIA h) as CSOK.
    pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof alloc_ceiling_pos as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by lia.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| lia| lia]).
    pose proof (rw_cells_bound _ _ _ _ HB) as AB. cbn [cells_size csize Nat.add] in AB.
    assert (JL : length junk = Z.to_nat 744) by (destruct HB as [[WF _] _]; cbn in WF; destruct WF as [WF _]; exact WF).
    assert (AB' : 0 <= A /\ A + 744 <= 2^64) by lia. clear AB. rename AB' into AB.
    pose proof (munch_refl [(A, A + 744); (lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    lx_pre. lxr_pose. lxa_auto [SUM_amemsetA 744 4] [A].
    lx_pre. lx_run_tac (PLANS [] [] 40%N [SUM_amemsetA 744 4]). lx_tree.
    all: lxr_leaf; lx_leaf.
  Qed.

  Lemma A_pkcs7_init_walk : struct_init_stmtA asegs R HIA A_PKCS7_INIT PKCS7_INIT_SIZE.
  Proof.
    unfold struct_init_stmtA, A_PKCS7_INIT, PKCS7_INIT_SIZE.
    intros until junk. intros HH HB HA ST LOS SLO TOP SPA DS MI OA CWA ->.
    pose proof (hcs_ok asegs R HIA h) as CSOK.
    pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof alloc_ceiling_pos as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by lia.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| lia| lia]).
    pose proof (rw_cells_bound _ _ _ _ HB) as AB. cbn [cells_size csize Nat.add] in AB.
    assert (JL : length junk = Z.to_nat 1440) by (destruct HB as [[WF _] _]; cbn in WF; destruct WF as [WF _]; exact WF).
    assert (AB' : 0 <= A /\ A + 1440 <= 2^64) by lia. clear AB. rename AB' into AB.
    pose proof (munch_refl [(A, A + 1440); (lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    lx_pre. lxr_pose. lxa_auto [SUM_amemsetA 1440 4] [A].
    lx_pre. lx_run_tac (PLANS [] [] 40%N [SUM_amemsetA 1440 4]). lx_tree.
    all: lxr_leaf; lx_leaf.
  Qed.
End Walk.

Lemma A_x509_crt_init_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_init ()) "PR,$32.PHIA,(33.$34.R1.)P,(35.(2:.R2.))P,(5.$>.(36.R3.)$37.)P,(22.=(25.R4.))(38.$34.R5.R4.$39.$3:.)")
(* [comment removed for export] *).
Proof. intros. eapply A_x509_crt_init_walk; eauto. Qed.

Lemma A_pkcs7_init_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_init ()) "PR,$32.PHIA,(33.$34.R1.)P,(35.(2:.R2.))P,(5.$>.(36.R3.)$37.)P,(22.=(25.R4.))(38.$34.R5.R4.$3;.$3<.)")
(* [comment removed for export] *).
Proof. intros. eapply A_pkcs7_init_walk; eauto. Qed.
