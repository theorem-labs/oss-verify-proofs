(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_stringA A_rip A_amem_lib A_icpt_read.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA Restrict RestrictLib RestrictRun SRz SymDriveA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Hoare MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_exit.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require SymExec2Sound.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_memchr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_icpt_str A_icpt_strnlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_A_icpt_strnlenJ () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.A_rip.app_range"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.B.A_icpt_strnlen.sn_consts"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L56765667309.2L59309037779.6L59309070547.4L59309070547.6L59309070672.6L59315336847.400000600>00F00O00W00_S1a2HaS1a1n2n0S1a2Ha1nS1a2Ha2n0S1a1n2n0S1a2Ha1n". (* [comment removed for export] *)
Lemma ro_addr_textA : forall a : Z, (0x10000 <= a < 0x0f1000)%Z -> ro_addr asegs (wa a) = true.
Proof.
  intros a Ha. unfold ro_addr, wa. rewrite (SymExec2Sound.SX2S.u_small a) by lia.
  unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
  repeat match goal with
  | |- context [Z.of_N (seg_base ?s)] => let v := eval vm_compute in (Z.of_N (seg_base s)) in replace (Z.of_N (seg_base s)) with v by (vm_compute; reflexivity)
  | |- context [Z.of_N (seg_size ?s)] => let v := eval vm_compute in (Z.of_N (seg_size s)) in replace (Z.of_N (seg_size s)) with v by (vm_compute; reflexivity)
  | |- context [seg_writable ?s] => let v := eval vm_compute in (seg_writable s) in replace (seg_writable s) with v by (vm_compute; reflexivity)
  end.
  destruct (Z.leb_spec0 65536 a); destruct (Z.leb_spec0 (a + 1) (65536 + 221184)); cbn [andb];
    [vm_compute; reflexivity | | exfalso; lia | exfalso; lia].
  destruct (Z.leb_spec0 286720 a); destruct (Z.leb_spec0 (a + 1) (286720 + 700416)); cbn [andb];
    [vm_compute; reflexivity | exfalso; lia | exfalso; lia | exfalso; lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Printing Width 200.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = SB.
  Hypothesis GSB : al_gsb AL = 0x1099f8.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Section Glue.
    Variable K : Model -> Prop.
    Hypothesis K_halted : forall mo, K mo -> m_halted mo = None.
    Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_icpt_strnlenJ ()) "Pmo,$0.Pacc,(1.(2.(3.&40.)$4.))P,A1.VK,R2.P,(5.VAL,VCS,R2.)(6.$0.Lmo',$0.(7.(8.(9.$0.)(:.R5.R4.)(;.$0.R1.))(7.A1.VK,R1.(<.R5.R1.))))")
(* [comment removed for export] *).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00V0@L10522033817.96 L10522292633.107L11668570566.97 L11669062336.76 L11670933105.96 L11671143536.104L13741527359.107L17543312104.98 L17543671698.101L19063762832.107L19487498895.98 L19487500959.97 L1952315491.93  L1954408332.99  L26277551252.107L26279681829.76 L28082725956.99 L32917955557.76 L32920543316.107L37838904711.99 L37840833870.96 L38237936311.107L40207340256.96 L43882031723.107L45632084589.107L46123156034.95 L50874460779.92 L53084894193.107L53087088704.76 L53197428842.97 L53694673008.75 L56541679272.96 L58295166326.107L60001757254.96 L61929687456.76 L63956051107.96 L8258011167.95  L940433721.76   00000Q01201V02:02^03B03U03i04=04R04d05605W06806N06d07807907:07L07^08008E08Z09309L09[0:40:M0:b0;C0;R0;f0<:0<d0=70=D0=ES2sp3str5extra1P2lo1L3LO03SPL3SPPS2sp3str5extra1P2lo1L3LO03SPL3SPPS2sp3str5extra1P2lo1L3LO03SPL3SPP2BHS2sp3str5extra1P2lo1L3LO03SPL3SPP2BHS2sp3str5extra1P2lo1L3LO03SPL3SPP2BHS2sp3str5extra1P2lo1L3LO03SPL3SPP2BHS3str5extra1P1L3L40S3str5extra1P1L1i2HiS3str5extra1P1L1i2HiS3str5extra1P1n1L3N63S3str5extra1P1j2HjS3str5extra1P1j2HjS2sp3str5extra1P2lo1L3LO03SPL3SPPS2sp3str5extra1P2lo1L3LO03SPL3SPPS3str5extra1P2lo1L3LO0S3str5extra1P2lo1L3LO0S3str5extra1P1L1z2HzFFS3str5extra1P1L2BHS3str5extra1P1L2BHS3str5extra1P2lo1LS3str5extra1P1n1L3N63S2sp3str5extra1P2lo1LS2sp3str5extra1P1L3SPP2BHS2sp3str5extra1P2lo1L3SPPS3str5extra1P1LS2sp3str5extra1P2lo1L3SPLS2sp3str5extra1P2lo1L3SPLS3str5extra1P1L2BH2LBS2sp3str5extra1P2lo1L3LO03SPL3SPPS3str5extra1P1LS3str5extra1P1n1L2LNS3str5extra1P1n1L2LNS2sp3str5extra1P1n2lo1L2LN3N633LO03SPL3SPPS3str5extra1P1L3WINS3str5extra1PF". (* [comment removed for export] *)
    #[using="IMG ALWF CSOK ASB K_halted K_mat"] Theorem strnlen_icptA : ltac2:(CDefT.buildp (gd_tbl_A_icpt_strnlenJ ()) "Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)Pm,P,(3.&40.)(9.(3.&8.))Pmo,$0.Pstr,(1.(3.&8.))Pextra,(1.(3.&8.))PP,$=.Pn,$=.Plo,$=.PT,$>.ZL,$=.(?.(10.(3.&8.)R6.))Zbuf,(1.(3.&8.))(11.(3.&8.)R7.(12.(3.&8.)(13.&8.=)R6.))P,A1.VK,R9.P,(14.$15.R;.R7.R2.)P,(16.(17.(3.&8.)(13.&8.=)R:.))P,(18.(19.(1:.(1;.(19.R9.R5.)+8.)+8.)+8.)(19.R9.(?.(10.(3.&8.)R4.))))P,(1<.VCS,R:.(?.(10.(3.&8.)R5.)))P,(1=.$15.VAL,VCS,R?.R;.(19.R7.+1.))P,(1>.(19.R8.+1.)(1?.+2.+28.))P,(18.(19.R9.+8.)R<.)P,(1>.R=.(1?.+2.+3?.))P,(20.R?.(19.(19.(19.R?.R;.)+1.)+7.))P,(1<.VCS,(21.R10.(22.R10.+40.))+40.)P,(1<.VCS,(21.(19.R11.R=.)(22.(19.R11.R=.)+40.))+40.)P,Pc,$=.P,A1.VCS,R1.(6.(3.&8.)Lb,(3.&8.)(14.$15.R19.(23.VAL,R3.)(12.(3.&8.)R1.(24.(3.&8.)))))P,(25.R17.)P,(26.$15.R18.R12.(27.&40.R36.))P,(1>.+10007???7???.R13.)P,(18.R14.(21.(27.&40.R38.)+1120.))P,(18.(27.&40.R39.)R17.)P,(1>.(19.R18.(?.(10.(3.&8.)R13.)))(1?.+2.+3?.))P,(1<.VCS,R17.(21.(27.&40.R3;.)R17.))P,(28.$15.R1>.)P,(8.(3.&40.)R35.(13.&40.R1;.))P,(8.(3.&40.)R35.(13.&40.R1;.))P,Pt0',(3.&40.)Pt1',(3.&40.)Pt2',(3.&40.)Pa1',(3.&40.)Pa2',(3.&40.)Pa3',(3.&40.)Pa4',(3.&40.)Pa5',(3.&40.)Pa6',(3.&40.)Pa7',(3.&40.)Pt3',(3.&40.)Pt4',(3.&40.)Pt5',(3.&40.)Pt6',(3.&40.)Pm',P,(3.&40.)(9.(3.&8.))Pmo',$0.P,(29.(12.(2.$=.$=.)(2:.$=.$=.R2;.(27.&40.R4?.))(24.(2.$=.$=.)))R31.R2.)P,(2;.$15.R32.R3.)P,(28.$15.R4.)P,(26.$15.R5.R2>.(27.&40.R52.))P,A1.VK,R5.P,(<.R35.R6.)(2<.$15.(2=.(2>.(2?.R56.R55.R54.R53.R16.R15.R14.R4?.R4>.(13.&40.R2?.)R13.R12.R11.R10.R?.R>.R=.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R<.R;.R:.R9.)(30.&5.(3.&40.))(31.R56.)(13.&20.=)(32.(3.&40.))R8.(33.$15.))R7.)R30.)(2<.$15.(2=.(2>.(2?.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)(30.&5.(3.&40.))(13.&40.+586?4.)(13.&20.=)(32.(3.&40.))R22.(33.$15.))R21.)R1;.)")
(* [comment removed for export] *).
    Proof.
      intros until T. cbv zeta. intros HK BY NZ WIN CRB OBJ L40 LN N63 AR HULL0 HULL1 SHRD RC ST LO0 SPL SPP BH SCS MI -> -> HC.
      al_facts. pose proof AR as AR'. unfold app_range in AR'.
      set (L := Z.of_nat (length str)) in *.
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
      assert (LB : Z.of_nat (length (str ++ Z_to_bv 8 0 :: extra)) = L + 1 + Z.of_nat (length extra)).
      { rewrite length_app. cbn [length]. lia. }
      rewrite LB in *.
      (* [comment removed for export] *)
      eapply (rz_evtA_K asegs AL CS K K_halted K_mat); [exact HK | | ].
      { eapply sn_pre with (P := P) (n := n) (lo := lo); first [exact IMG | exact ALWF | exact CSOK | exact ASB | exact GSB | exact RC | exact ST | reflexivity | lia | exact SCS | exact MI]. }
      cbn beta. intros ms1 mo1 POST HK1 MM1. unfold sn_pre_post in POST.
      ddestruct POST as (j8 & j2080 & j2072 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FRa & FRb & FRc & FRd & FRe).
      (* [comment removed for export] *)
      set (ivs := [(P, P + (L + 1 + Z.of_nat (length extra)))]).
      assert (HCS : Forall (fun iv => crange CS (fst iv) (snd iv - fst iv)) ivs).
      { subst ivs. constructor; [cbn [fst snd]; replace (P + (L + 1 + Z.of_nat (length extra)) - P) with (L + 1 + Z.of_nat (length extra)) by lia; exact CRB | constructor]. }
      assert (H0 : Forall (fun iv => 0 < fst iv) ivs) by (subst ivs; repeat constructor; cbn; lia).
      assert (BY1 : bytes_at asegs m1 P (str ++ Z_to_bv 8 0 :: extra)).
      { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from fst snd]; rewrite LB; lia]. }
      assert (MH : mchrH (restrict (Dimg ivs) m1) (Z_to_bv 64 P) (str ++ Z_to_bv 8 0 :: extra) L n).
      { split.
        - pose proof (bytes_at_rdn asegs m1 P _ 0 (length (str ++ Z_to_bv 8 0 :: extra)) BY1 ltac:(lia)) as RD.
          rewrite Z.add_0_r in RD. cbn [skipn] in RD. rewrite firstn_all in RD.
          unfold wa in RD. apply rdn_restrictD; [exact RD | rewrite unsigned_lit by lia; lia |].
          rewrite unsigned_lit by lia. intros z Hz. apply (Dimg_cov ivs P (P + (L + 1 + Z.of_nat (length extra)))); [subst ivs; left; reflexivity | lia | lia | rewrite LB in Hz; lia].
        - rewrite unsigned_lit, LB by lia. lia.
        - rewrite unsigned_lit, LB by lia. lia.
        - lia.
        - subst L. rewrite Nat2Z.id, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
        - intros j Hj. subst L. rewrite Nat2Z.id in Hj. rewrite app_nth1 by lia. intros Hz. apply NZ.
          replace (Z_to_bv 8 0) with (nth j str (Z_to_bv 8 0)) by (apply bv_eq; rewrite Hz; reflexivity). apply nth_In. lia.
        - lia.
        - lia.
        - intros i Hi. rewrite restrict_in.
          2:{ pose proof (Dimg_img ivs i ltac:(unfold AIMG_LO, AIMG_HI; lia)) as Di. exact Di. }
          destruct (m1 (Z_to_bv 64 i)) as [b|] eqn:Mb; [|reflexivity]. exfalso.
          pose proof (MI1 _ _ Mb) as RO. change (Z_to_bv 64 i) with (wa i) in RO. rewrite ro_addr_textA in RO by lia. discriminate. }
      change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None m1 ?rom) with (mkst Rx pc m1 rom).
      lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?Rx _ _ _) _) _ => set (R1 := Rx) end.
      ddestruct (ref_memchr0 (restrict (Dimg ivs) m1) (Z_to_bv 64 P) (str ++ Z_to_bv 8 0 :: extra) L n (seg_rom asegs) R1 (Z_to_bv 64 0x59f28)
                  MH ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        as (R2 & RUN & KC & A10).
      lazymatch type of RUN with Shape.msteps _ (mkst _ ?pcw _ _) _ => replace pcw with (Z_to_bv 64 0x0ea8c4 : word) in RUN by (apply bv_eq; reflexivity) end.
      eapply (rz_smsteps_RK asegs (Dimg ivs) AL CS K K_halted K_mat (Dimg_Dseg ivs) asegs_top (Dimg_DOK AL CS IMG ivs HCS) (Dimg_D0 ivs H0));
        [exact HK1 | exact RUN | intros; reflexivity |].
      intros mo2 HK2 MM2.
      (* [comment removed for export] *)
      apply (srzJ_getr_ext asegs (regs_tree R2) R2). { intros r. apply getr_regs_tree. }
      unfold regs_tree.
      rewrite (KC 1%bv ltac:(cbn; tauto)), (KC 2%bv ltac:(cbn; tauto)), (KC 3%bv ltac:(cbn; tauto)), (KC 4%bv ltac:(cbn; tauto)),
              (KC 8%bv ltac:(cbn; tauto)), (KC 9%bv ltac:(cbn; tauto)), (KC 18%bv ltac:(cbn; tauto)), (KC 19%bv ltac:(cbn; tauto)),
              (KC 20%bv ltac:(cbn; tauto)), (KC 21%bv ltac:(cbn; tauto)), (KC 22%bv ltac:(cbn; tauto)), (KC 23%bv ltac:(cbn; tauto)),
              (KC 24%bv ltac:(cbn; tauto)), (KC 25%bv ltac:(cbn; tauto)), (KC 26%bv ltac:(cbn; tauto)), (KC 27%bv ltac:(cbn; tauto)), A10.
      subst R1. unfold mkR. norm_getr.
      rewrite (unsigned_lit P) by lia.
      change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
      assert (OBJ1 : aobj asegs AL CS m1 P (L + 1)).
      { eapply (aobj_munch asegs AL CS CSOK); [| exact MU1 | exact OBJ]. unfold w_client. apply Forall_cons; [cbn [fst snd]; exact SCS | apply Forall_nil]. }
      assert (SHRD1 : forall c, CS c -> exists b, bytes_at asegs m1 (shadow_of AL c) [b]).
      { eapply (shrd_munch AL CS CSOK [(lo, bv_unsigned sp)]); [| exact MU1 | exact SHRD]. unfold w_client. apply Forall_cons; [cbn [fst snd]; exact SCS | apply Forall_nil]. }
      assert (RC1 : sn_consts m1) by (eapply sn_consts_munch; [exact MU1 | exact LO0 | exact RC]).
      eapply (rz_evtA_K asegs AL CS K K_halted K_mat); [exact HK2 | | ].
      { eapply (sn_back AL IMG ALWF CS CSOK ASB) with (P := P) (L := L) (n := n) (lo := lo);
          first [ exact OBJ1 | exact AR | exact HULL0 | exact HULL1 | exact SHRD1 | exact RC1 | exact ST1 | exact MI1
                | exact FRa | exact FRb | exact FRc | exact FRd | exact FRe | lia | eapply crange_sub; [exact SCS | lia | lia] ]. }
      cbn beta. intros ms3 mo3 POST HK3 MM3. unfold sn_back_post in POST.
      ddestruct POST as (t0' & t1' & t2' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & MI3 & ST3).
      apply HC.
      - eapply munch_trans; [exact MU1 | exact MU3].
      - eapply wmono_trans; [exact WM1 | exact WM3].
      - exact MI3.
      - exact ST3.
      - exact HK3.
      - eapply mo_mat_trans; [exact MM1|]. eapply mo_mat_trans; [exact MM2 | exact MM3].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Glue.
End Walk.
