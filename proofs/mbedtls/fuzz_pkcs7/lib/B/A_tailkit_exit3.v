(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame BBFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA Restrict RestrictLib RestrictRun NodesA SymDriveA SymDriveAX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_base A_exit_lib A_exit_defs A_exit_front1 A_unreg_globals A_exit A_stdio_defs A_stdio_write A_stdio_call A_fwrite_oom A_oomtail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tailkit_defs A_tailkit_exit2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance Lib.PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_tailkit_exit3 () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_exit2.tail_postD"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_exit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.exit_code"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"].



Section TailExit3.
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable KI : Model -> Prop.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000%Z.
  Hypothesis GSB : al_gsb AL = 0x1099f8%Z.
  Hypothesis IMGCS : A_unreg_globals.img_cs AL CS.
  Hypothesis K_halted : forall mo, KI mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_tailkit_exit3 ()) "Pmo,$0.Pacc,(1.(2.(3.&40.)$4.))P,A1.VKI,R2.P,(5.VAL,VCS,R2.)(6.$0.Lmo',$0.(7.(8.(9.$0.)(:.R5.R4.)(;.$0.R1.))(7.A1.VKI,R1.(<.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_tailkit_exit3 ()) "Pmo,$0.Pmo',$0.P,A1.VKI,R2.P,(8.$=.(>.R2.)(>.R3.))P,(8.(1.(2.(3.&40.)(3.&40.)))(?.R3.)(?.R4.))P,(8.(1.(3.&40.))(10.R4.)(10.R5.))P,(8.(9.(3.&40.))(11.R5.)(11.R6.))A1.VKI,R6.")
(* [comment removed for export] *).

  Variable sp0 : word.
  Hypothesis SPlo : (0x7fff7f000000 + 4096 <= bv_unsigned sp0)%Z.
  Hypothesis SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis SPal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Hypothesis WCS : crange CS (bv_unsigned sp0 - 4096) 4096.
  Variable lo : Z.
  Hypothesis LOlo : (0x10007fff7fff < lo)%Z.   (* [comment removed for export] *)
  Hypothesis LOhi : (lo <= bv_unsigned sp0 - 4096)%Z.

  Variables (M : word -> option byte) (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  Hypothesis TM : tail_memA sp0 M can tid wp0 rp0 wp1 rp1.

  (* [comment removed for export] *)
  Variable su : Z.
  Hypothesis SUal : (su mod 16 = 0)%Z.
  Hypothesis SUlo : (bv_unsigned sp0 <= su)%Z.
  Hypothesis SUhi : (su <= 0x800000000000)%Z.
  Hypothesis SUCS : crange CS (su - 320) 320.

  (* [comment removed for export] *)
  #[using="AL CS IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly SPlo SPhi LOlo can tid wp0 rp0 wp1 rp1 TM SUal SUlo SUhi SUCS"] Theorem exit2_at_dddf8_deep : ltac2:(CDefT.buildp (gd_tbl_A_tailkit_exit3 ()) "Pra,(3.&40.)Pgp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PM',P,(3.&40.)(9.(3.&8.))Pmo',$0.P,(12.Vsp0,Vlo,VM,R2.)P,A1.VKI,R2.P,(13.$14.R4.(15.&40.Vsp0,)Vsu,)(16.$14.(17.(18.(19.R21.(1:.&40.Vsu,)R20.(1:.&40.+63<:90.)R1?.R1>.R1=.R1<.R1;.(1:.&40.+2.)R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)(1;.&5.(3.&40.))(1:.&40.+>11:8.)(1:.&20.=)(1<.(3.&40.))R5.(1=.$14.))R4.)(1>.(1?.+2.)(20.R4.)))")
(* [comment removed for export] *).
  Proof.
    intros * POST HKI2 FRM.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct TM as [_ RO _ _ RTC _ _ STK MI TID LOCK MTID ATEXIT NL COMP MAPPED GLOB FIN FOUT].
    change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pc Mx rom).
    (* [comment removed for export] *)
    destruct POST as [AG MU GR WM CLEAN].
    assert (DJ : forall a n, (0 <= a)%Z -> (a + n <= 0x65f000)%Z -> (a + n <= 0x0fa488 \/ 0x0fa570 <= a)%Z ->
                 disjoint_from [(lo, bv_unsigned sp0); (0x0fa488%Z, 0x0fa570%Z)] a n).
    { intros a n Ha Hn Hd. cbn. repeat split; lia. }
    assert (OUT : forall x : word, (bv_unsigned x + 8 <= bv_unsigned sp0 - 4096 \/ True)%Z ->
                  (bv_unsigned x < 0x65f000)%Z -> (bv_unsigned x + 1 <= 0x0fa488 \/ 0x0fa570 <= bv_unsigned x)%Z -> M' x = M x).
    { intros x _ H1 H2. apply AG; lia. }
    assert (RDN : forall (a : Z) n bs, (0 <= a)%Z -> (a + Z.of_nat n <= 0x65f000)%Z -> (a + Z.of_nat n <= 0x0fa488 \/ 0x0fa570 <= a)%Z ->
                  rdn RSEGS M (Z_to_bv 64 a) n = Some bs -> rdn RSEGS M' (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Ha Hn Hd H. rewrite <- H. apply rdn_agree. intros j Hj. rewrite (u_small a) by lia. apply AG; rewrite u_small by lia; lia. }
    assert (MI' : mem_inv RSEGS M').
    { intros a b Hb. pose proof (u64_range a).
      destruct (M a) as [bb0|] eqn:E0; [exact (MI a bb0 E0)|].
      destruct (Z_lt_le_dec (bv_unsigned a) lo).
      - destruct (Z_lt_le_dec (bv_unsigned a) 0x0fa488); [| destruct (Z_lt_le_dec (bv_unsigned a) 0x0fa570)].
        1,3: exfalso; rewrite AG in Hb by lia; congruence.
        (* [comment removed for export] *)
        rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
        eapply wview_not_ro with (m := M).
        + pose proof (store_ok_data M (Z_to_bv 64 (bv_unsigned a)) 1 ltac:(rewrite u_small by lia; lia) ltac:(rewrite u_small by lia; cbn; lia)) as SO.
          pose proof (store_ok_wview RSEGS M _ 1 0 SO ltac:(lia)) as WV. rewrite u_small in WV by lia. rewrite Z.add_0_r in WV. exact WV.
        + unfold wa. rewrite Z_to_bv_bv_unsigned. exact E0.
      - destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned sp0)).
        + rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)). apply ro_addr_high. unfold AIMG_HI in *. lia.
        + exfalso. rewrite AG in Hb by lia. congruence. }
    eapply srzJ_conseq.
    { eapply (ref_exitA AL CS KI IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly su ltac:(lia) ltac:(lia)
                ltac:(intros z Hz; apply SUCS; lia) _ M' mo' (Z_to_bv 64 2) []); [| exact HKI2].
      ddestruct CLEAN as (wp2 & rp2 & CLEAN). dexists tid, wp0, rp0, wp2, rp2. split.
      - split.
        + reflexivity.
        + reflexivity.
        + reflexivity.
        + exact SUal.
        + (* [comment removed for export] *)
          assert (STKlo : stk RSEGS M' (bv_unsigned sp0 - 320) (bv_unsigned sp0)).
          { eapply stk_transport; [eapply (proj2 (stk_split RSEGS M (bv_unsigned sp0 - 4096) (bv_unsigned sp0 - 320) (bv_unsigned sp0) STK ltac:(lia))) | exact MU | exact WM |].
            intros x Hx. right. ddestruct STK as (_ & _ & S3). destruct (S3 x ltac:(lia)) as [_ (b & Hb)].
            unfold mrd in Hb. destruct (M (wa x)) as [bb0|] eqn:E0.
            * destruct (M' (wa x)) as [bb1|] eqn:E1; [exists bb1; reflexivity|]. exfalso. apply (GR (wa x)); [congruence | exact E1].
            * exfalso. pose proof (seg_rom_high x ltac:(unfold AIMG_HI; lia)) as SR. change asegs with RSEGS in SR. cbn in Hb. congruence. }
          pose proof (stk_merge RSEGS M' (bv_unsigned sp0 - 320) (bv_unsigned sp0) su STKlo FRM ltac:(lia)) as STKall.
          exact (proj2 (stk_split RSEGS M' (bv_unsigned sp0 - 320) (su - 320) su STKall ltac:(lia))).
        + exact MI'.
        + exact TID.
        + eapply rw_cells_transport; [exact LOCK | exact MU | exact WM | apply DJ; cbn; lia].
        + eapply rw_cells_transport; [exact MTID | exact MU | exact WM | apply DJ; cbn; lia].
        + ddestruct ATEXIT as (jp & jq & jf & AT). dexists false, (Z_to_bv 8 0), jp, jq, jf. split; [| intros HB; discriminate HB].
          unfold atexit_cells in *. eapply rw_cells_transport; [exact AT | exact MU | exact WM | apply DJ; cbn; lia].
        + eapply ro_cells_transport; [exact NL | exact MU | apply DJ; cbn; lia].
        + eapply rw_cells_transport; [exact COMP | exact MU | exact WM | apply DJ; cbn; lia].
        + eapply asan_rtc_munch_fw; [exact MU | lia | exact RTC].
        + eapply mapped_transport; [exact MAPPED | exact MU | unfold AIMG_HI; lia | lia |]. intros x Hx. left. cbn. lia.
        + ddestruct GLOB as (Q1 & Q2 & Q3 & Q4 & Q5). unfold stdio_globals.
          repeat split; (eapply RDN; [lia | cbn; lia | cbn; lia | assumption]).
        + ddestruct FIN as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean.
          repeat split; (eapply RDN; [lia | cbn; lia | cbn; lia | assumption]).
        + exact CLEAN.
      - left. split; [reflexivity|]. dexists wp1, rp1.
        ddestruct FOUT as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean.
        repeat split; (eapply RDN; [lia | cbn; lia | cbn; lia | assumption]). }
    (* [comment removed for export] *)
    cbn [W map].
    replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
    apply t_emit_nil_eq. unfold t_exit. apply t_emit_has_nil.
  Qed.
End TailExit3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
