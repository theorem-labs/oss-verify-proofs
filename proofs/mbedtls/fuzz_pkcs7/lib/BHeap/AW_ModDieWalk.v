(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_exit_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_PfNum AW_PfVsn.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AW_MmapDie AW_MapOrDie.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
#[local] Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | first [tb_light_a a | lia] | first [tb_light_l a | (simpl_sizes; slia)]
                | first [ solve [cbn [inside]; tb_free] | (cbn [inside]; simpl_sizes; slia) ] ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq;
              [ | first [tb_light_a a | lia] | first [tb_light_l a | (simpl_sizes; slia)] ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P004e5ff9aea08462 0 3 1 1 33 1 34 1P014885baba8a6f5b 0 3 1 1 41 1 42 1P018c80e71204a992 0 2 0 1 40 1P01b220f7eecbe952 0 2 0 1 40 1P01ed966ace99fa2d 0 3 1 1 33 1 34 1P02b08418b655898d 0 3 1 1 41 1 42 1P02dd179d4e16058a 0 2 0 1 32 1P03f337a926566e3c 0 3 1 1 33 1 34 1P04d365ca1e55309d 0 2 0 1 2 1P0599575692031079 0 2 0 1 32 1P06334366e3e5bf52 0 2 0 1 32 1P07a9314c1121e460 0 2 0 1 32 1P07b89de8144f681d 0 2 0 1 32 1P07bc0675e1e2a264 0 2 0 1 32 1P07c2d119d3db1655 0 3 1 1 33 1 34 1P08e829252366db50 0 3 1 1 41 1 42 1P09718e34884fb2b1 0 2 0 1 32 1P0a67c16767f7e718 0 3 1 1 33 1 34 1P0aa007521a56e4f8 0 3 1 1 41 1 42 1P0bcd7daa7cf7682f 0 3 1 1 33 1 34 1P0c2e94a85355e6ba 0 2 0 1 40 1P0c51f51de8c13e09 0 3 1 1 41 1 42 1P0ca058ca85697254 0 3 1 1 33 1 34 1P0d7f8e497c54c8cb 0 3 1 1 33 1 34 1P0d9993432d1e2f5e 0 3 1 1 33 1 34 1P0de7a336347b7c06 0 3 1 1 33 1 34 1P0e051f87c72c8767 0 3 1 1 41 1 42 1P0e326c4998018764 0 2 0 1 32 1P0e7fbcb1b5d5e682 0 3 1 1 41 1 42 1P0e8d01519dfafc25 0 2 0 1 32 1P0ee83e798078bcca 0 3 1 1 41 1 42 1P107b9d6124d0a66c 0 2 0 1 32 1P1095a294003e0248 0 2 0 1 40 1P11289d458fd5d976 0 2 0 1 40 1P11418d5944f6623c 0 2 0 1 32 1P11d9cc2517d3937f 0 3 1 1 33 1 34 1P1339bb37faa70e7c 0 2 0 1 32 1P1422b06405102a71 0 3 1 1 33 1 34 1P15591c77909b42f9 0 2 0 1 32 1P15e55c11d60fbf09 0 3 1 1 33 1 34 1P1887e60dea7e9d6a 0 3 1 1 33 1 34 1P1897e63df01cf7c4 0 2 0 1 32 1P1babe164541b35d8 0 3 1 1 33 1 34 1P1c8f6738dbf85798 0 3 1 1 33 1 34 1P1d23c9cb99692da7 0 2 0 1 40 1P1d24fd0861f170bd 0 3 1 1 33 1 34 1P1df1c2f7f83e2bcc 0 3 1 1 33 1 34 1P1e55ed945884f267 0 2 0 1 32 1P1e959ccfbad47435 0 2 0 1 2 1P1efdb536e3179534 0 3 1 1 33 1 34 1P1f671d3d68d0a46d 0 3 1 1 41 1 42 1P1f9dc4bf43e72b0a 0 3 1 1 33 1 34 1P1fa763ff2cedcca2 0 2 0 1 32 1P1fc20be889fd389b 0 2 0 1 40 1P1fdf3f63dde527a4 0 2 0 1 40 1P214235ec39ed7055 0 3 1 1 33 1 34 1P21e906b30747652e 0 2 0 1 32 1P22ae498646287dae 0 3 1 1 33 1 34 1P22c8c753c1564703 0 2 0 1 32 1P23c941e1a6a1cd15 0 3 1 1 41 1 42 1P2459927d2ea6c481 0 3 1 1 33 1 34 1P24f5707d6729d8f0 0 3 1 1 33 1 34 1P25781efbbe5dfecc 0 3 1 1 33 1 34 1P2595155e62d2e954 0 2 0 1 32 1P260a67f8dfc8a32c 0 3 1 1 33 1 34 1P26a9071e5e6b7026 0 2 0 1 32 1P270e0739b5acdffb 0 3 1 1 41 1 42 1P2780aca57a5d9873 0 3 1 1 41 1 42 1P278ec37947eced08 0 3 1 1 41 1 42 1P28eee0044e540a24 0 2 0 1 32 1P29094354a7448681 0 3 1 1 33 1 34 1P29bf139e2d2d5dd7 0 3 1 1 33 1 34 1P2b9208b05277ed5c 0 2 0 1 40 1P2d26529b814244d5 0 2 0 1 32 1P2e163d58fc592539 0 2 0 1 32 1P2e78a44ed0c24e94 0 2 0 1 32 1P2eeafa25f25523b1 0 3 1 1 33 1 34 1P2fb571c3b6fee2df 0 2 0 1 40 1P2fd7b7d769bff9ae 0 3 1 1 33 1 34 1P3047eefd5bc9153e 0 3 1 1 41 1 42 1P30badceb3ea52b46 0 2 0 1 32 1P316d09a5d7d0ae12 0 3 1 1 33 1 34 1P324d9f0a9486157c 0 2 0 1 31 1P32d2b56ee4943019 0 3 1 1 33 1 34 1P32f221dd77d3cbb2 0 2 0 1 32 1P32f67712c8c1dc66 0 2 0 1 32 1P33a2fc0faa017061 0 3 1 1 33 1 34 1P33acf740b132fcda 0 3 1 1 33 1 34 1P357cf4163fd96d91 0 3 1 1 41 1 42 1P3608b10afa004584 0 2 0 1 32 1P365ed6f09aede5e4 0 3 1 1 33 1 34 1P3689e9d4c29fd96b 0 2 0 1 32 1P3807630a7de06a5d 0 2 0 1 40 1P384f035d3c7824a9 0 3 1 1 33 1 34 1P386979d80dbec974 0 3 1 1 33 1 34 1P3a12e38507bd6926 0 3 1 1 33 1 34 1P3b1fc794299045e5 0 2 0 1 32 1P3c5f5b4ab9c0a270 0 3 1 1 33 1 34 1P3c6b7127a0170cb5 0 2 0 1 40 1N0137d503c50256e8N03f1ac5146eb0144"%lxh.
Ltac2 gd_tbl_AW_ModDieWalk () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_SEALED2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DYING"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.die_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.A_SPIN_MMAPDIE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MapOrDie.mod_answered"].

Section ARUN_1. Context {hAR : arun}.

Section ModDie.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Lemma mapordie_post_die : ltac2:(CDefT.buildp (gd_tbl_AW_ModDieWalk ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa6,(0.&40.)Pra,(0.&40.)PSP0,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pmm,P,(0.&40.)(3.(0.&8.))Paddr,$1.Psize,$1.Plo0,$1.Pfr,(4.(0.&8.))P,(5.(6.=R4.)(7.R4.(8.+2.+2?.)))P,(5.(7.=R4.)(6.R4.(8.+2.+28.)))P,(9.$:.R7.(;.R;.-60.)(<.$=.(>.(?.&40.+32.))(<.$=.(10.#2<.R3.)(<.$=.(11.R19.)(<.$=.(11.R1:.)(<.$=.(11.R1;.)(<.$=.(11.R1<.)(<.$=.(11.R1=.)(<.$=.(11.R<.)(12.$=.))))))))))P,(13.$:.R8.$14.(<.$=.(11.(?.&40.+1.))(12.$=.)))P,(13.$:.R9.$15.(<.$=.(>.(?.&40.=))(12.$=.)))P,(16.$:.R:.R7.(;.R>.-60.))P,(6.+65?000.R8.)P,(6.R9.(17.R10.+400.))P,(6.R11.(8.+2.+3?.))P,(18.(<.(19.$1.$1.)(1:.$1.$1.R;.R12.)(12.(19.$1.$1.)))R?.R>.)P,(1;.$:.R10.R?.)P,(1<.$:.R10.)P,(1=.VCS,R>.(17.R15.R>.))(1>.$:.VAL,VCS,(1?.R14.$20.)(21.(?.&40.(17.(8.+2.+40.)+<.))R16.R2=.R2<.R2;.R2:.R29.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R15.R14.R11.R10.R12.))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 ra SP0 F fc m0 mm addr size lo0 fr
      AB SZ FR SEAL DY ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold mod_answered, A_PAGESZ_CELL, A_GOT_SEALED2, A_DYING, A_SPIN_MMAPDIE in *.
    (* [comment removed for export] *)
    assert (PATC : ro_cells asegs mm 66640 [C8 (Z_to_bv 64 12297829382473034410)]).
    { split; [cbn; repeat split; exact I|]. apply ro_bytes_at; [exact MI| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. }
    lx_hide MU. lx_hide WM.
    pose proof (munch_refl [(lo0, SP0)] mm) as MU1. pose proof (wmono_refl asegs mm) as WM1.
    lx_run (PLAN [0x7d810] [] 80%N). try clear LXlen.
    (* [comment removed for export] *)
    set (pat := le8 (Z_to_bv 64 12297829382473034410)) in *.
    lazymatch goal with FRl : rw_cells _ ?mx (SP0 + -136) _, STl : stk _ _ lo0 (SP0 + -160) |- _ =>
      chunk_split FRl 5%nat VAA FRr; chunk_split FRr 5%nat BUFC FRR;
      replace (SP0 + -136 + 40) with (SP0 + -96) in BUFC by (clear; lia); replace (SP0 + -136 + 40 + 40) with (SP0 + -56) in FRR by (clear; lia);
      chunk_split VAA 1%nat VAC VAB; replace (SP0 + -136 + 8) with (SP0 + -128) in VAB by (clear; lia);
      apply (rw_cells_reshape asegs mx (SP0 + -96) _ [CB 40 (pat ++ pat ++ pat ++ pat ++ pat)]) in BUFC;
        [| split; [vm_compute; reflexivity| exact I] | vm_compute; reflexivity ];
      apply u8arr_of_rw_cells in BUFC;
      eapply (evtA_cut asegs AL CS);
      [ eapply (vsn_p_spec AL IMG ALWF CS CSOK addr (SP0 + -160) lo0 (SP0 + -96) 40 (SP0 + -136) (pat ++ pat ++ pat ++ pat ++ pat));
          first [ exact STl | exact BUFC | exact VAC | assumption
                | match goal with |- Z.of_nat _ = _ => subst pat; vm_compute; reflexivity end
                | match goal with |- crange _ _ _ => intros x Hx; apply SCS; clear -Hx SPL; lia end
                | match goal with |- _ \/ _ => left; clear; lia end
                | clear -AB SPL SPH LOIMG; lia ]
      | ] end.
    cbn beta. intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & bs' & m2 & -> & ST2 & OUT2 & LEN2 & VAC2 & MUc & WMc & MI2).
    clear BUFC VAC. lx_acc_run m0 mm. lx_clear_mem mm. lx_acc_call m0 MUc WMc. ret_lit.
    (* [comment removed for export] *)
    clear OUT2. pose proof (munch_refl [(lo0, SP0)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    lx_run (PLAN [0x76ad4] [] 40%N).
    apply evtA_done. unfold die_post. do 3 eexists. reflexivity.
  Qed.
End ModDie.
End ARUN_1.
