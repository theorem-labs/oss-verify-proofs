(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_stringA A_rip.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_amem_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_IMemmove AW_AMemmove.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Printing Width 200.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0653ae33d7352010 0 2 0 1 13 1P06664dd345d1854f 0 2 0 1 13 1P07826e4bfcfbb141 0 2 0 1 13 1P0903adda583390a6 0 3 1 1 14 1 15 1P09a7c33e12752033 0 2 0 1 13 1P0a3b882673b38a34 0 3 1 1 14 1 15 1P0a4026cbcaf7e47c 0 2 0 1 13 1P0c49045ce5047db8 0 2 0 1 11 1P0ef24299530c37a6 0 2 0 1 13 1P0fa19717d3a8a5fc 0 2 0 1 13 1P0fdcc94af3d50658 0 3 1 1 14 1 15 1P101dee1796af5341 0 2 0 1 10 1P142d810e50c50752 0 3 1 1 14 1 15 1P14c1e22d0afcaf9f 0 2 0 1 13 1P16a87b63f9c731bb 0 2 0 1 13 1P16def19741a213a1 0 2 0 1 13 1P175f46448defd9f9 0 3 1 1 14 1 15 1P17e88605de8eab51 0 2 0 1 13 1P1bb8cc42077f7cca 0 2 0 1 12 1P1d8099a36b6e025f 0 2 0 1 13 1P1d91ceb0cde3dd9d 0 2 0 1 13 1P1e0ec90380752cbc 0 3 1 1 14 1 15 1P1e1dba4fe25e3c63 0 3 1 1 14 1 15 1P1e5f21b872a33e8f 0 2 0 1 10 1P1e7a3ff5cb9352a8 0 3 1 1 14 1 15 1P20963c87bbb68eb3 0 2 0 1 13 1P20e8a81181927a1e 0 3 1 1 14 1 15 1P2296df36ee29fbac 0 2 0 1 13 1P249a4bcbb1e1ed34 0 3 1 1 14 1 15 1P256f9b77886d5d65 0 2 0 1 13 1P277a5fae8b8c0cbf 0 2 0 1 13 1P28ecb500818f2c7d 0 2 0 1 13 1P2ad68322a4783a36 0 2 0 1 13 1P2b9b7b48144817c3 0 3 1 1 14 1 15 1P2c10d3d2bc1c9bd4 0 2 0 1 9 1P2c34e5b2ef82424f 0 2 0 1 13 1P2df57f68bf2efb10 0 2 0 1 13 1P2e421074a8b7a8af 0 2 0 1 13 1P2fbc0e2fe6e00367 0 2 0 1 12 1P3058f992873fef1b 0 2 0 1 13 1P34c851fd364044d6 0 3 1 1 14 1 15 1P3587cdb8e5974bfe 0 2 0 1 13 1P35d93370a9264777 0 3 1 1 14 1 15 1P35f7dee37e805054 0 3 1 1 14 1 15 1P368dead3cf7594f3 0 2 0 1 11 1P3a6e2346719d6abd 0 2 0 1 13 1P3af871be947d46f5 0 3 1 1 14 1 15 1P3c66983fd579b313 0 3 1 1 14 1 15 1N08deafbb472c1fb9N17c46e8e7bc690efN19c453fbee2542efN1dba013d1da2138eN2818a553924a280dN31e6c320857029a5"%lxh.
Ltac2 gd_tbl_AW_AMemmove0 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.amem_consts"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AMemmove.amemmove_post"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = SB.
  Hypothesis GSB : al_gsb AL = 0x1099f8.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  #[using="Type"] Lemma ltu_zero : forall x : word, bv_ltu x (Z_to_bv 64 0) = false.
  Proof. intros x. unfold bv_ltu. rewrite unsigned_lit by lia. apply Z.ltb_ge. pose proof (bv_unsigned_in_range 64 x). lia. Qed.

  #[using="IMG ALWF"] Lemma amemmove0_asan : ltac2:(CDefT.buildp (gd_tbl_AW_AMemmove0 ()) "PCS,P,$0.SpPra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))PDST,$0.PSRC,$0.Plo,$0.P,(4.VAL,R26.)P,(5.(6.=R4.)(7.R4.(8.+2.+40.)))P,(5.(6.=R4.)(7.R4.(8.+2.+40.)))P,(9.R7.)P,(:.$;.R8.R5.(<.&40.R28.))P,(7.+10007???7???.R6.)P,(6.R7.(=.(<.&40.R2:.)+8;0.))P,(>.R2=.R8.(=.(<.&40.R2;.)R8.))P,(?.$;.R<.)P,(10.(1.&40.)R25.(11.&40.R<.))P,(10.(1.&40.)R25.(11.&40.R<.))P,(10.(1.&40.)R25.(11.&40.=))(12.$;.VAL,R32.(13.R31.R30.R2?.R2>.R2:.R29.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R12.R11.R?.=R=.(14.(1.&8.))R10.)(15.(16.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(11.&40.+68498.)R11.(17.(1.&40.))R10.(18.$;.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB. try lx_hide GSB.  (* [comment removed for export] *)
    intros until lo. intros CSOK DB SBd AC ST LO0 SPL SCS MI -> -> ->.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct AC as [AC1 AC2 _ _ _].
    (* [comment removed for export] *)
    lx_run (PLAN [] [(0x6857c, DMerge 0)] 120%N).
    all: lx_deads.
    unfold amemmove_post. lx_post.
    - eapply munch_weaken; [| eassumption]. lx_subfp.
    - unfold u8arr, bytes_at, wr_at. cbn [length Z.of_nat]. repeat split; first [clear - DB; lia | intros i Hi; exfalso; clear - Hi; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF"] Lemma amemmove0_walk : ltac2:(CDefT.buildp (gd_tbl_AW_AMemmove0 ()) "PCS,P,$0.SpPra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))PDST,$0.PSRC,$0.Plo,$0.P,(4.VAL,R26.)P,(5.(6.=R4.)(6.R4.(8.+2.+40.)))P,(5.(6.=R4.)(6.R4.(8.+2.+40.)))P,(9.R7.)P,(:.$;.R8.R5.(<.&40.R28.))P,(7.+10007???7???.R6.)P,(6.R7.(=.(<.&40.R2:.)+8;0.))P,(>.R2=.R8.(=.(<.&40.R2;.)R8.))P,(?.$;.R<.)P,(10.(1.&40.)R25.(11.&40.R<.))P,(10.(1.&40.)R25.(11.&40.R<.))P,(10.(1.&40.)R25.(11.&40.=))(12.$;.VAL,R32.(13.R31.R30.R2?.R2>.R2:.R29.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R12.R11.R?.=R=.(14.(1.&8.))R10.)(15.(16.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(11.&40.+68498.)R11.(17.(1.&40.))R10.(18.$;.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB. try lx_hide GSB.  (* [comment removed for export] *)
    intros until lo. intros CSOK DB SBd AC ST LO0 SPL SCS MI -> -> ->.
    rewrite <- (Z_to_bv_mod64 DST), <- (Z_to_bv_mod64 SRC).
    assert (DB' : 0 <= DST mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
    assert (SB' : 0 <= SRC mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
    eapply evtA_mono.
    { eapply amemmove0_asan with (DST := DST mod 2^64) (SRC := SRC mod 2^64); try eassumption; reflexivity. }
    cbv beta. unfold amemmove_post. intros ms' PO. destruct_exs PO. destruct PO as (E & MU & WM & MI' & AR & ST').
    do 15 eexists. split; [rewrite (Z_to_bv_mod64 DST) in E; exact E|].
    split; [eapply munch_weaken; [| exact MU]; intros y Hy; cbn [outside fst snd] in *; clear - Hy; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [| exact ST'].
    unfold u8arr, bytes_at, wr_at. cbn [length Z.of_nat]. repeat split; first [clear - DB; lia | intros i Hi; exfalso; clear - Hi; lia].
  Qed.
End Walk.
