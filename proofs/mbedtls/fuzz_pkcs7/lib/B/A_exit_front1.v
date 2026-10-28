(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_exit_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Printing Width 200.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P009886b070391d80 0 3 1 1 33 1 34 1P018f261f2ecbf1ef 0 2 0 1 32 1P024131178a37e44c 0 3 0 1 31 1 32 1P03c128066b11a581 0 3 1 1 33 1 34 1P04c761095b4c0f13 0 3 0 1 33 1 34 1P051119d4115a7e84 0 3 1 1 31 1 32 1P0671d28398af4ed9 0 3 1 1 31 1 32 1P06a39751bb431b5b 0 2 0 1 32 1P07381a81e6b25abb 0 3 0 1 32 1 33 1P07520e4274bb8853 0 3 1 1 31 1 32 1P0d545363ed84a4ce 0 2 0 1 30 1P0dba22af7ffe59a7 0 3 0 1 33 1 34 1P0e03409da7d1fa83 0 3 1 1 33 1 34 1P0e2fef9addc39484 0 3 1 1 33 1 34 1P0e6f2e258ed9a6de 0 3 1 1 33 1 34 1P0f020b3784e36887 0 3 1 1 33 1 34 1P0f120da17a3932f4 0 3 1 1 33 1 34 1P122eecdbb78f2147 0 3 1 1 33 1 34 1P126a6168e540ff3c 0 3 1 1 31 1 32 1P13515a42be64d4db 0 3 1 1 31 1 32 1P14c5fed71fc707e6 0 3 1 1 31 1 32 1P157b9fd86fcbecbb 0 2 0 1 32 1P15ce3cf3c507043f 0 3 0 1 33 1 34 1P177858e6627a040d 0 3 0 1 30 1 31 1P17925255b90609ba 0 3 1 1 33 1 34 1P17f07c404215e983 0 2 0 1 30 1P18730fbe53179fbd 0 3 1 1 31 1 32 1P188121ff6d92a450 0 2 0 1 32 1P18ab8976b74a1e13 0 2 0 1 30 1P18c9ab25d3838aa3 0 3 1 1 33 1 34 1P19cb1e0aeff3bf5f 0 3 1 1 33 1 34 1P1c2dc9f1b56c6aa6 0 3 0 1 30 1 31 1P1c3b77f376f6a3f2 0 3 0 1 31 1 32 1P1c570dea6e243036 0 3 1 1 31 1 32 1P1d6619df35bcdf20 0 3 0 1 32 1 33 1P1ee2229103d0a63f 0 3 1 1 33 1 34 1P1ff040b52e619189 0 3 1 1 33 1 34 1P1ff18b55d9d19c86 0 2 0 1 32 1P20856453c03550a0 0 2 0 1 32 1P20d3966573cc996c 0 2 0 1 32 1P22f37d7f9420d307 0 2 0 1 30 1P2369fffe75ef1f14 0 3 0 1 30 1 31 1P24aa9c17549d8c23 0 3 1 1 33 1 34 1P24b257856fee74a9 0 3 1 1 31 1 32 1P2530b041c8a0d667 0 3 1 1 31 1 32 1P262166e393b756a0 0 3 1 1 31 1 32 1P2728a90afe1d0233 0 3 1 1 31 1 32 1P273cf10fef049181 0 3 1 1 33 1 34 1P2799c7d9256b5223 0 3 0 1 32 1 33 1P28358929c2b6732a 0 3 0 1 32 1 33 1P28697aba2ee4e3b3 0 3 1 1 31 1 32 1P2a4c1abf3db9dae8 0 3 1 1 33 1 34 1P2a57446134390cc4 0 3 0 1 33 1 34 1P2b1b71cb8169b098 0 3 1 1 33 1 34 1P2b29841cf3c64c9b 0 3 1 1 33 1 34 1P2b69302ec56a67ec 0 2 0 1 30 1P2d6ce05f01707dec 0 2 0 1 30 1P2eecc12ccfdde9cf 0 3 0 1 32 1 33 1P2f88ae14a756663d 0 3 1 1 33 1 34 1P31111dd1734d9eaf 0 3 1 1 33 1 34 1P31eddb5bb912462e 0 3 0 1 32 1 33 1P327470a058efcfa9 0 3 1 1 33 1 34 1P3660ee221c418570 0 3 0 1 32 1 33 1P37e0b67b8cb299d1 0 3 0 1 30 1 31 1P389d610c4e4a5875 0 3 1 1 33 1 34 1P38be1ebf72c7b479 0 2 0 1 32 1P398205f6f1f4f38d 0 3 1 1 33 1 34 1P39e6146d7c1c62bf 0 3 0 1 31 1 32 1P39fce8de45f54bd7 0 3 0 1 30 1 31 1P3a979c8546dd73fa 0 3 1 1 31 1 32 1P3c1f7a07d902d1b5 0 3 1 1 31 1 32 1P3c2bc2d7000d9940 0 3 1 1 33 1 34 1P3ce92a354f6a78cc 0 3 1 1 33 1 34 1P3d54940a2116f9d3 0 2 0 1 32 1P3e83259a5794482a 0 3 1 1 33 1 34 1P3ec7c15af04c8e9a 0 3 1 1 33 1 34 1N06ef6a0fefd3e96aN1515720370bea00fN158cf653a6ed3c48N1635756850453c8dN16c340dfdfa3604eN16e37db9941c1086N19369997b7d9b851N1b8e72ebc99c0129N32820e2f6a7d4991N32b74fac9add99bfN358d96bd54d20f76N386fc20082c41798"%lxh.
Ltac2 gd_tbl_A_exit_front1 () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Walk.atexit_done"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "Walk.atexit_cells"; "Corelib.Init.Datatypes.true"; "Walk.incb_cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.funcs_on_exit_post"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Walk.dtors_aux_post"].


Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition atexit_cells (reg : bool) (m : mem) (fin : byte) (jp jq jf : list byte) : Prop :=
    rw_cells asegs m 0x65cae0 [C1 fin; CB 3 jp; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (if reg then 2 else 1)); CB 4 jq;
                              C8 (Z_to_bv 64 0x65caf8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x0e1154);
                              C8 (Z_to_bv 64 (if reg then 0x0e1154 else 0)); CB 240 jf;
                              C8 (Z_to_bv 64 0x086b40); C8 (Z_to_bv 64 (if reg then 0x097508 else 0))].

  (* [comment removed for export] *)
  Definition incb_cell (m : mem) : Prop := rw_cells asegs m 0x63c054 [C1 (Z_to_bv 8 0)].

  (* [comment removed for export] *)
  Definition atexit_done (reg : bool) (m : mem) (jp jq jf : list byte) : Prop :=
    rw_cells asegs m 0x65cae0 [C1 (Z_to_bv 8 1); CB 3 jp; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 32); CB 4 jq;
                              C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x0e1154);
                              C8 (Z_to_bv 64 (if reg then 0x0e1154 else 0)); CB 240 jf;
                              C8 (Z_to_bv 64 0x086b40); C8 (Z_to_bv 64 (if reg then 0x097508 else 0))].

  (* [comment removed for export] *)
  Definition funcs_on_exit_post (reg : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (jp jq jf : list byte) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_exit_front1 ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O17.O16.O15.O14.R10.R?.R>.O13.O12.R=.R<.R;.R:.R9.R8.R7.R6.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(8.O17.)O6.(9.(2.&40.))R1.(:.$;.)))(4.(<.(=.(>.$?.$?.)(10.$?.$?.+65<:>0.+65<:?8.)(=.(>.$?.$?.)(10.$?.$?.(11.(12.&40.O16.)+30.)(12.&40.O16.))(13.(>.$?.$?.))))O1.R1.)(4.(14.$;.O1.R1.)(4.(15.$;.R1.)(4.(16.$;.R1.O5.(12.&40.O16.))(17.O18.R1.O4.O3.O2.))))))))))))))))))))))")
(* [comment removed for export] *).

  Lemma funcs_on_exit_spec : ltac2:(CDefT.buildp (gd_tbl_A_exit_front1 ()) "Preg,$18.Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(19.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Plo,$?.Pfin,(2.&8.)Pjp,(1:.(2.&8.))Pjq,(1:.(2.&8.))Pjf,(1:.(2.&8.))P,(1;.R28.R6.R4.R3.R2.R1.)P,P,(5.$18.R29.$1<.)(1=.R8.)P,(1>.$;.R8.+65<=23.(=.$1?.(20.(21.&8.=))(13.$1?.)))P,(1>.$;.R9.+19;8:0.(=.$1?.(20.(21.&8.=))(13.$1?.)))P,(16.$;.R:.R9.(12.&40.R2:.))P,(22.+65?000.R:.)P,(22.R;.(11.(12.&40.R2<.)+30.))P,(22.(12.&40.R2=.)(23.+2.+2?.))P,(24.VCS,R=.(11.(12.&40.R2>.)R=.))P,(15.$;.R?.)P,(5.$?.(25.(12.&40.R31.)+2.)=)(26.$;.VAL,VCS,(27.R33.R32.R31.R30.R2?.R2;.R2:.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R13.R12.R10.R>.R=.R<.R11.)(6.(7.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R13.(21.&40.+>0?<4.)R12.(9.(2.&40.))R11.(:.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros reg. intros until jf. intros AT ICB NL COV ST LOLO SPL SPH SCS MI RA. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(0x65cae0, 0x65caf8); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    unfold atexit_cells in AT.
    replace fin with (Z_to_bv 8 (bv_unsigned fin)) in AT by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    remember (bv_unsigned fin) as fz eqn:Efz in AT. clear Efz.
    carve_frame 48%nat ST.
    destruct reg.
    - (* [comment removed for export] *)
      specialize (ICB eq_refl). unfold incb_cell in ICB.
      lx_run_tac (PLAN ([] : list Z) [] 150%N). lx_tree.
      try replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in * by lia.
      finish. all: unfold atexit_done; try assumption.
    - (* [comment removed for export] *)
      clear ICB.
      lx_run_tac (PLAN ([] : list Z) [] 150%N). lx_tree.
      try replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in * by lia.
      finish. all: unfold atexit_done; try assumption.
  Qed.

  (* [comment removed for export] *)
  Definition dtors_aux_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_exit_front1 ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O14.O13.O12.O11.R10.R?.R>.O10.O?.R=.R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(8.O14.)O3.(9.(2.&40.))R1.(:.$;.)))(4.(<.(=.(>.$?.$?.)(10.$?.$?.+106390.+106391.)(=.(>.$?.$?.)(10.$?.$?.(11.(12.&40.O13.)+10.)(12.&40.O13.))(13.(>.$?.$?.))))O1.R1.)(4.(14.$;.O1.R1.)(4.(15.$;.R1.)(4.(16.$;.R1.O2.(12.&40.O13.))(28.$;.R1.+106390.(=.$1?.(20.(21.&8.+1.))(13.$1?.))))))))))))))))))))))))")
(* [comment removed for export] *).

  Lemma dtors_aux_spec : ltac2:(CDefT.buildp (gd_tbl_A_exit_front1 ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(19.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Plo,$?.P,(28.$;.R2.+106390.(=.$1?.(20.(21.&8.=))(13.$1?.)))P,(1>.$;.R3.+?5>20.(=.$1?.(29.(21.&40.+>108<.))(13.$1?.)))P,(1>.$;.R4.+?5>28.(=.$1?.(29.(21.&40.=))(13.$1?.)))P,(1>.$;.R5.+?7;60.(=.$1?.(29.(21.&40.+?7;60.))(13.$1?.)))P,(16.$;.R6.R5.(12.&40.R26.))P,(22.+65?000.R6.)P,(22.R7.(11.(12.&40.R28.)+10.))P,(22.(12.&40.R29.)(23.+2.+2?.))P,(24.VCS,R9.(11.(12.&40.R2:.)R9.))P,(15.$;.R;.)P,(5.$?.(25.(12.&40.R2=.)+2.)=)(26.$;.VAL,VCS,(2:.R2>.R2=.R2<.R2;.R27.R26.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R?.R>.R<.R=.)(6.(7.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(21.&40.+4690<.)R>.(9.(2.&40.))R=.(:.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros CO G1 G2 DSO ST LOLO SPL SPH SCS MI RA. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(0x106390, 0x106391); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    lx_run_tac (PLAN ([] : list Z) [] 60%N). lx_tree.
    try replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in * by lia.
    finish.
  Qed.
End Walk.
