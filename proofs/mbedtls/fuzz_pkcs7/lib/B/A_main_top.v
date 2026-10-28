(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Shape Mem Cells Frame HeapIface Asn1Aux RegsExt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import ShapeLaws.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt ARtDrv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import ATopContract24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_unreg_globals A_tailkit_defs ATopContract A_main_inv A_main_loop A_main_fin A_main_hdr A_main_target A_main_open.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require SpinAlg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_main_top () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.B.A_main_open.openfail_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_main_open.readerr_stmtA"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.dot_path"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.B.A_main_open.usage_stmtA"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.Fs.fs_lookup"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.B.A_main_loop.after_loop_stmtA"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_main_open.MENTRY"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.B.A_main_open.MREGS"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.spec"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.B.A_main_open.MENTRYU"; "Stdlib.ZArith.BinInt.Z.of_nat"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "entry_packA"; "entry_bridgeA"; "RocqVerifyHarness.AgentSubmission.ABoot.SpinAlg.srealizes"].


Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; destruct q as [|b q]; cbn; try (split; congruence).
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq.
  split.
  - intros [H1 ->]. f_equal. apply bv_eq. exact H1.
  - intros H. injection H. intros -> ->. auto.
Qed.

Section Top.
  Variable R : art_layout.
  Variable HIA : artA asegs R.
  Variable HID : artD asegs R HIA.
  Let AL := arl_AL R.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis HMALLOC : arl_malloc R = 0x69480.
  Hypothesis HFREE : arl_free R = 0x6947c.
  Hypothesis HMEMCPY : arl_memcpy_i R = 0x67db8.
  Hypothesis HTP : arl_tp R = 0x63ca90.
  Hypothesis HIMGCS : forall h, A_unreg_globals.img_cs AL (hcs asegs R HIA h).
  Variable SI : sinv (arl_L R).
  Hypothesis SIFP : forall a, ~ outside (si_fp SI) a -> 0x63c0a0 <= a < 0x63c180.
  (* [comment removed for export] *)
  Variable PHI : Z -> Z.
  Variable FPHI : Z.
  Hypothesis PHI_max : forall n, 0 <= n < 2^26 -> 0 <= PHI n <= FPHI.
  Variable FSTK : Z.
  Hypothesis FSTK_range : 0 <= FSTK <= 2^22.
  (* [comment removed for export] *)
  Variable FFR : Z -> Z.
  Variable FFFR : Z.
  Hypothesis FFR_max : forall n, 0 <= n < 2^26 -> 0 <= FFR n <= FFFR.
  Variable C24f : Z.                               (* [comment removed for export] *)
  Hypothesis C24F_max : C24f <= 65536.
  Hypothesis FUZZ : fuzz_entry_stmtA24 asegs R HIA SI PHI FSTK C24f FFR FUZZ_ENTRY.
  (* [comment removed for export] *)
  Variable sp0 : word.
  Hypothesis SPlo : 0x7fff80000000 <= bv_unsigned sp0.       (* [comment removed for export] *)
  Hypothesis SPhi : bv_unsigned sp0 <= 0x800000000000.       (* [comment removed for export] *)
  Hypothesis SPal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis STKLO : arl_stklo R = bv_unsigned sp0 - 8388608.
  Variables (fs0 : Fs) (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word) (TOP STKHI V0 : Z).
  Hypothesis HTOPlo : bv_unsigned sp0 - 48 <= TOP.
  Hypothesis HSTKHI : bv_unsigned sp0 <= STKHI.
  Hypothesis STKHI8 : STKHI mod 8 = 0.
  Hypothesis STKHImax : STKHI <= 2^47.
  Hypothesis HV0 : V0 + 2^29 <= AVOL_SPLIT.      (* [comment removed for export] *)
  Let HV0M : V0 + 2^29 <= AVOL_MAX.                (* [comment removed for export] *)
  Proof. pose proof HV0 as H. unfold AVOL_SPLIT, AVOL_MAX in *. clear - H. lia. Qed.
  Hypothesis HVF : V0 + 2^28 + 4 * FPHI + 8 * AVOL_CALL <= AVOL_MAX.
  Variable FR0 : Z.                                 (* [comment removed for export] *)
  Hypothesis HFRF : FR0 + 4 * FFFR + 16 <= FR_MAX.
  #[using="FFR FFFR FFR_max sp0 SPlo STKHI HSTKHI HFRF"] Lemma HFR0 : FR0 <= FR_MAX. Proof. pose proof (FFR_max 0 ltac:(lia)). lia. Qed.
  #[using="FFR FFFR FFR_max sp0 SPlo STKHI HSTKHI HFRF"] Lemma HFR3 : FR0 + 3 <= FR_MAX. Proof. pose proof (FFR_max 0 ltac:(lia)). lia. Qed.
  (* [comment removed for export] *)
  Hypothesis OPENFAIL : ltac2:(CDefT.buildp (gd_tbl_A_main_top ()) "Ppath,(0.(1.&8.))Ppathp,(1.&40.)(2.VR,VHIA,Vsp0,R2.R1.Vfs0,Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,VTOP,VSTKHI,)")
(* [comment removed for export] *).
  Hypothesis READERR : ltac2:(CDefT.buildp (gd_tbl_A_main_top ()) "Ppathp,(1.&40.)(3.VR,VHIA,Vsp0,$4.R1.Vfs0,Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,VTOP,VSTKHI,)")
(* [comment removed for export] *).
  Hypothesis USAGE : ltac2:(CDefT.buildp (gd_tbl_A_main_top ()) "Pargc,$5.Pa0p,(1.&40.)Pa0s,(0.(1.&8.))(6.VR,VHIA,Vsp0,Vfs0,Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,VTOP,VSTKHI,R3.R2.R1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="AL IMG ASB HMALLOC HFREE HMEMCPY HTP HIMGCS SIFP PHI FPHI PHI_max FSTK FSTK_range FFR FFFR FFR_max C24f C24F_max FUZZ SPlo SPhi SPal STKLO HTOPlo HSTKHI HV0 HVF HFRF"] Lemma AFTER : ltac2:(CDefT.buildp (gd_tbl_A_main_top ()) "Ppath,(0.(1.&8.))Ppathp,(1.&40.)Pfdata,(0.(1.&8.))Ppad,(0.(1.&8.))P,(7.(8.(0.(1.&8.)))(9.Vfs0,R4.)(:.(0.(1.&8.))R2.))(;.VR,VHIA,VHID,Vsp0,R5.R4.Vfs0,R3.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,VTOP,VSTKHI,VV0,VFR0,R2.VSI,)")
(* [comment removed for export] *).
  Proof.
    intros path pathp fdata pad Hfs.
    apply (after_loopA R HIA HID IMG ASB HFREE HTP HIMGCS SI SIFP sp0 SPlo SPhi SPal STKLO path pathp fs0 fdata can tid wp0 rp0 wp1 rp1 TOP STKHI V0 HTOPlo HSTKHI HV0 FR0 HFR3 pad).
    exact (target_phaseA R HIA HID IMG ASB HMALLOC HFREE HMEMCPY HTP HIMGCS sp0 SPlo SPhi SPal STKLO fs0 fdata can tid wp0 rp0 wp1 rp1 TOP STKHI V0 HTOPlo HSTKHI HV0 SI SIFP PHI FPHI PHI_max HVF FSTK FSTK_range FFR FFFR FFR_max FR0 HFRF pad C24f C24F_max FUZZ).
  Qed.

  (* [comment removed for export] *)
  #[using="AL IMG ASB HMALLOC HFREE HMEMCPY HTP HIMGCS SIFP PHI FPHI PHI_max FSTK FSTK_range FFR FFFR FFR_max C24f C24F_max FUZZ SPlo SPhi SPal STKLO HTOPlo HSTKHI STKHI8 STKHImax HV0 HVF HFRF OPENFAIL READERR"] Theorem main2A : ltac2:(CDefT.buildp (gd_tbl_A_main_top ()) "Pa0s,(0.(1.&8.))Ppath,(0.(1.&8.))Ppathp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pm,P,(1.&40.)(8.(1.&8.))Pmo,$<.Ph,(=.$>.VR,VHIA,)P,(?.VR,VHIA,VHID,VSI,Vsp0,R11.R10.Vfs0,Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,VTOP,VSTKHI,VV0,VFR0,R3.R2.R1.)(10.$>.(11.(12.(13.Vsp0,R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.+2.)(14.&5.(1.&40.))(15.&40.+970>0.)(15.&20.=)(16.(1.&40.))R4.(17.$>.))R3.)(18.(19.(0.(1.&8.))R13.(19.(0.(1.&8.))R12.(1:.(0.(1.&8.)))))Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros * ME. cbn [spec].
    destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
    - exact (main_toolongA R HIA HID IMG ASB SI SIFP sp0 SPlo SPhi SPal STKLO path pathp fs0 can tid wp0 rp0 wp1 rp1 TOP STKHI V0
               HTOPlo HSTKHI STKHI8 STKHImax FR0 (OPENFAIL path pathp) t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo h ME Hlong).
    - destruct (list_byte_eqb path []) eqn:Hemp.
      + apply list_byte_eqb_eq in Hemp.
        exact (main_emptyA R HIA HID IMG ASB SI SIFP sp0 SPlo SPhi SPal STKLO path pathp fs0 can tid wp0 rp0 wp1 rp1 TOP STKHI V0
                 HTOPlo HSTKHI STKHI8 STKHImax FR0 (OPENFAIL path pathp) t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo h ME Hemp).
      + assert (Hne : path <> []) by (intros E; apply list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
        destruct (list_byte_eqb path dot_path) eqn:Hdot.
        * apply list_byte_eqb_eq in Hdot. subst path.
          exact (main_dirA R HIA HID IMG ASB HMALLOC HTP HIMGCS SI SIFP sp0 SPlo SPhi SPal STKLO dot_path pathp fs0 can tid wp0 rp0 wp1 rp1 TOP STKHI V0
                   HTOPlo HSTKHI STKHI8 STKHImax HV0 FR0 HFR0 (OPENFAIL dot_path pathp) (READERR pathp) t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo h ME eq_refl).
        * assert (Hnd : path <> dot_path) by (intros E; apply list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
          destruct (fs_lookup fs0 path) as [fdata|] eqn:Hlk.
          -- exact (main_fileA R HIA HID IMG ASB HMALLOC HFREE HMEMCPY HTP HIMGCS SI SIFP sp0 SPlo SPhi SPal STKLO path pathp fs0 can tid wp0 rp0 wp1 rp1 TOP STKHI V0
                      HTOPlo HSTKHI STKHI8 STKHImax HV0 FR0 HFR0 (OPENFAIL path pathp) (AFTER path pathp) t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo h fdata
                      ME Hlk Hne Hnd ltac:(lia)).
          -- exact (main_absentA R HIA HID IMG ASB SI SIFP sp0 SPlo SPhi SPal STKLO path pathp fs0 can tid wp0 rp0 wp1 rp1 TOP STKHI V0
                      HTOPlo HSTKHI STKHI8 STKHImax FR0 (OPENFAIL path pathp) t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo h ME Hlk Hne Hnd ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  #[using="HID AL IMG ASB SPlo SPhi SPal STKLO HTOPlo HSTKHI STKHI8 USAGE"] Theorem mainUA : ltac2:(CDefT.buildp (gd_tbl_A_main_top ()) "Pargv,(0.(0.(1.&8.)))Pa0s,(0.(1.&8.))Prest,(0.(0.(1.&8.)))Pa0p,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pm,P,(1.&40.)(8.(1.&8.))Pmo,$<.Ph,(=.$>.VR,VHIA,)P,(7.(0.(0.(1.&8.)))R13.(19.(0.(1.&8.))R12.R11.))P,(1;.(7.$1<.(1=.(0.(1.&8.))R14.)#2.))P,(1>.VR,VHIA,Vsp0,Vfs0,Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,VTOP,VSTKHI,(1?.(1=.(0.(1.&8.))R15.))R12.R14.R5.R4.R3.)(10.$>.(11.(12.(13.Vsp0,R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.(1?.(1=.(0.(1.&8.))R16.)))(14.&5.(1.&40.))(15.&40.+970>0.)(15.&20.=)(16.(1.&40.))R6.(17.$>.))R5.)(18.R16.Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros * Hargv Hlen ME.
    assert (E : spec argv fs0 = t_die (msg_usage a0s) fs0).
    { subst argv. destruct rest as [|x [|y l]]; cbn [spec hd length] in *; [reflexivity | exfalso; apply Hlen; reflexivity | reflexivity]. }
    rewrite E.
    exact (main_usageA R HIA HID IMG ASB sp0 SPlo SPhi SPal STKLO fs0 can tid wp0 rp0 wp1 rp1 TOP STKHI HTOPlo HSTKHI STKHI8
             (Z.of_nat (length argv)) a0p a0s t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo h (USAGE _ a0p a0s) ME ltac:(lia)).
  Qed.
End Top.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record drv_premises (sp0 : word) (fs0 : Fs) : Type := MKDP {
  dp_R : art_layout;                                                         (* [comment removed for export] *)
  dp_HIA : artA asegs dp_R;                                                  (* [comment removed for export] *)
  dp_HID : artD asegs dp_R dp_HIA;                                           (* [comment removed for export] *)
  dp_IMG : asan_img_ok (arl_AL dp_R);                                        (* [comment removed for export] *)
  dp_ASB : al_sb (arl_AL dp_R) = 0x7fff8000;                                 (* [comment removed for export] *)
  dp_HMALLOC : arl_malloc dp_R = 0x69480;                                    (* [comment removed for export] *)
  dp_HFREE : arl_free dp_R = 0x6947c;                                        (* [comment removed for export] *)
  dp_HMEMCPY : arl_memcpy_i dp_R = 0x67db8;                                  (* [comment removed for export] *)
  dp_HTP : arl_tp dp_R = 0x63ca90;                                           (* [comment removed for export] *)
  dp_HIMGCS : forall h, A_unreg_globals.img_cs (arl_AL dp_R) (hcs asegs dp_R dp_HIA h);   (* [comment removed for export] *)
  dp_STKLO : arl_stklo dp_R = bv_unsigned sp0 - 8388608;                    (* [comment removed for export] *)
  dp_SI : sinv (arl_L dp_R);                                                 (* [comment removed for export] *)
  dp_SIFP : forall a, ~ outside (si_fp dp_SI) a -> 0x63c0a0 <= a < 0x63c180; (* [comment removed for export] *)
  dp_PHI : Z -> Z;                                                           (* [comment removed for export] *)
  dp_FPHI : Z;                                                               (* [comment removed for export] *)
  dp_PHI_max : forall n, 0 <= n < 2^26 -> 0 <= dp_PHI n <= dp_FPHI;          (* [comment removed for export] *)
  dp_FSTK : Z;                                                               (* [comment removed for export] *)
  dp_FSTK_range : 0 <= dp_FSTK <= 2^22;                                      (* [comment removed for export] *)
  dp_FFR : Z -> Z;                                                           (* [comment removed for export] *)
  dp_FFFR : Z;                                                               (* [comment removed for export] *)
  dp_FFR_max : forall n, 0 <= n < 2^26 -> 0 <= dp_FFR n <= dp_FFFR;          (* [comment removed for export] *)
  dp_C24f : Z;                                                             (* [comment removed for export] *)
  dp_C24F_max : dp_C24f <= 65536;
  dp_FUZZ : fuzz_entry_stmtA24 asegs dp_R dp_HIA dp_SI dp_PHI dp_FSTK dp_C24f dp_FFR FUZZ_ENTRY;   (* [comment removed for export] *)
  dp_SPlo : 0x7fff80000000 <= bv_unsigned sp0;                               (* [comment removed for export] *)
  dp_SPhi : bv_unsigned sp0 <= 0x800000000000;                               (* [comment removed for export] *)
  dp_SPal : bv_unsigned sp0 mod 16 = 0;                                      (* [comment removed for export] *)
  dp_can : word; dp_tid : Z; dp_wp0 : word; dp_rp0 : word; dp_wp1 : word; dp_rp1 : word;   (* [comment removed for export] *)
  dp_TOP : Z; dp_STKHI : Z; dp_V0 : Z;                                       (* [comment removed for export] *)
  dp_HTOPlo : bv_unsigned sp0 - 48 <= dp_TOP;                                (* [comment removed for export] *)
  dp_HSTKHI : bv_unsigned sp0 <= dp_STKHI;                                   (* [comment removed for export] *)
  dp_STKHI8 : dp_STKHI mod 8 = 0;                                            (* [comment removed for export] *)
  dp_STKHImax : dp_STKHI <= 2^47;                                            (* [comment removed for export] *)
  dp_HV0 : dp_V0 + 2^29 <= AVOL_SPLIT;                                       (* [comment removed for export] *)
  dp_HVF : dp_V0 + 2^28 + 4 * dp_FPHI + 8 * AVOL_CALL <= AVOL_MAX;           (* [comment removed for export] *)
  dp_FR0 : Z;                                                                (* [comment removed for export] *)
  dp_HFRF : dp_FR0 + 4 * dp_FFFR + 16 <= FR_MAX;                             (* [comment removed for export] *)
  dp_OPENFAIL : forall (path : list byte) (pathp : word),                    (* [comment removed for export] *)
    openfail_stmtA dp_R dp_HIA sp0 path pathp fs0 dp_can dp_tid dp_wp0 dp_rp0 dp_wp1 dp_rp1 dp_TOP dp_STKHI;
  dp_READERR : forall (pathp : word),                                        (* [comment removed for export] *)
    readerr_stmtA dp_R dp_HIA sp0 dot_path pathp fs0 dp_can dp_tid dp_wp0 dp_rp0 dp_wp1 dp_rp1 dp_TOP dp_STKHI;
  dp_USAGE : forall (argc : Z) (a0p : word) (a0s : list byte),               (* [comment removed for export] *)
    usage_stmtA dp_R dp_HIA sp0 fs0 dp_can dp_tid dp_wp0 dp_rp0 dp_wp1 dp_rp1 dp_TOP dp_STKHI argc a0p a0s
}.

Arguments dp_R {sp0 fs0} _.  Arguments dp_HIA {sp0 fs0} _.  Arguments dp_HID {sp0 fs0} _.  Arguments dp_SI {sp0 fs0} _.
Arguments dp_can {sp0 fs0} _. Arguments dp_tid {sp0 fs0} _. Arguments dp_wp0 {sp0 fs0} _. Arguments dp_rp0 {sp0 fs0} _.
Arguments dp_wp1 {sp0 fs0} _. Arguments dp_rp1 {sp0 fs0} _. Arguments dp_TOP {sp0 fs0} _. Arguments dp_STKHI {sp0 fs0} _.
Arguments dp_V0 {sp0 fs0} _. Arguments dp_FR0 {sp0 fs0} _.

(* [comment removed for export] *)
Definition entry_packA (argv : list (list byte)) (fs0 : Fs) (sp0 : word) (c : config) : Prop :=
  exists (D : drv_premises sp0 fs0) (Rg : bvmap 5 word) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (mo : Model)
         (h : HST asegs (dp_R D) (dp_HIA D)),
    c = mkCfg (MS Rg bvmap_empty (Z_to_bv 64 0x0970e0) (Z_to_bv 32 0) None m (seg_rom asegs)) mo /\
    (forall r, getr Rg r = getr (MREGS sp0 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Z.of_nat (length argv))) r) /\
    match argv with
    | [a0s; path] => exists pathp : word,
        MENTRY (dp_R D) (dp_HIA D) (dp_HID D) (dp_SI D) sp0 path pathp fs0 (dp_can D) (dp_tid D) (dp_wp0 D) (dp_rp0 D) (dp_wp1 D) (dp_rp1 D)
               (dp_TOP D) (dp_STKHI D) (dp_V0 D) (dp_FR0 D) m mo h
    | a0s :: _ => exists a0p : word,
        MENTRYU (dp_R D) (dp_HIA D) sp0 fs0 (dp_can D) (dp_tid D) (dp_wp0 D) (dp_rp0 D) (dp_wp1 D) (dp_rp1 D) (dp_TOP D) (dp_STKHI D)
                (Z.of_nat (length argv)) a0p a0s m mo h
    | [] => False
    end.

Theorem A_driver_srealizesJ : forall argv fs0 sp0 c, entry_packA argv fs0 sp0 c -> srealizesJ asegs c (spec argv fs0).
Proof.
  (intros argv fs0 sp0 c dd_H; ddestruct dd_H as (D & Rg & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & mo & h & -> & HR & HE)).
  change (MS Rg bvmap_empty (Z_to_bv 64 0x0970e0) (Z_to_bv 32 0) None m (seg_rom asegs))
    with (@mkst fx0 Rg (Z_to_bv 64 0x0970e0) m (seg_rom asegs)).
  apply (srzJ_getr_ext asegs (MREGS sp0 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Z.of_nat (length argv))) Rg);
    [intros r; symmetry; apply HR|].
  change (@mkst fx0 ?R ?pc m (seg_rom asegs)) with (MS R bvmap_empty pc (Z_to_bv 32 0) None m (seg_rom asegs)).
  destruct D as [R HIA HID IMG ASB HMALLOC HFREE HMEMCPY HTP HIMGCS STKLO SI SIFP PHI FPHI PHI_max FSTK FSTK_range FFR FFFR FFR_max C24f C24F_max FUZZ SPlo SPhi SPal
                 can tid wp0 rp0 wp1 rp1 TOP STKHI V0 HTOPlo HSTKHI STKHI8 STKHImax HV0 HVF FR0 HFRF OPENFAIL READERR USAGE]; cbn in *.
  destruct argv as [|a0s [|path [|x l]]].
  - destruct HE.
  - destruct HE as [a0p ME]. eapply (mainUA R HIA HID IMG ASB sp0 SPlo SPhi SPal STKLO fs0 can tid wp0 rp0 wp1 rp1 TOP STKHI HTOPlo HSTKHI STKHI8 USAGE [a0s]);
      [reflexivity | cbn; lia | exact ME].
  - destruct HE as [pathp ME].
    exact (main2A R HIA HID IMG ASB HMALLOC HFREE HMEMCPY HTP HIMGCS SI SIFP PHI FPHI PHI_max FSTK FSTK_range FFR FFFR FFR_max C24f C24F_max FUZZ sp0 SPlo SPhi SPal STKLO
             fs0 can tid wp0 rp0 wp1 rp1 TOP STKHI V0 HTOPlo HSTKHI STKHI8 STKHImax HV0 HVF FR0 HFRF OPENFAIL READERR a0s path pathp
             t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo h ME).
  - destruct HE as [a0p ME]. eapply (mainUA R HIA HID IMG ASB sp0 SPlo SPhi SPal STKLO fs0 can tid wp0 rp0 wp1 rp1 TOP STKHI HTOPlo HSTKHI STKHI8 USAGE (a0s :: path :: x :: l));
      [reflexivity | cbn; lia | exact ME].
Qed.

Theorem A_driver_srealizes : forall argv fs0 sp0 c, entry_packA argv fs0 sp0 c -> SpinAlg.srealizes asegs c (spec argv fs0).
Proof. intros argv fs0 sp0 c H. apply srzJ_srz. eapply A_driver_srealizesJ. exact H. Qed.

(* [comment removed for export] *)
Definition entry_bridgeA (ENTRY : bvmap 5 word -> mem -> Model -> Prop) (argv : list (list byte)) (fs : Fs) (sp : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_main_top ()) "PRg,(20.&5.(1.&40.))Pmem,P,(1.&40.)(8.(1.&8.))Pmd,$<.P,A3.O4.R3.R2.R1.P,(7.$21.(22.R2.)O2.)(23.O3.O2.O1.(11.(12.R5.(14.&5.(1.&40.))(15.&40.+970>0.)(15.&20.=)(16.(1.&40.))R4.(17.$>.))R3.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Theorem A_main_stmt_of_bridge : ltac2:(CDefT.buildp (gd_tbl_A_main_top ()) "PENTRY,P,(20.&5.(1.&40.))P,P,(1.&40.)(8.(1.&8.))P,$<.SpPargv,(0.(0.(1.&8.)))Pfs,$21.Psp,(1.&40.)P,(24.R4.R3.R2.R1.)PRg,(20.&5.(1.&40.))Pmem,P,(1.&40.)(8.(1.&8.))Pmd,$<.P,A3.R8.R3.R2.R1.P,(7.$21.(22.R2.)R7.)(25.$>.(11.(12.R5.(14.&5.(1.&40.))(15.&40.+970>0.)(15.&20.=)(16.(1.&40.))R4.(17.$>.))R3.)(18.R9.R8.))")
(* [comment removed for export] *).
Proof.
  intros ENTRY argv fs sp BR Rg mem md ME Hfs.
  eapply (A_driver_srealizes argv fs sp). exact (BR Rg mem md ME Hfs).
Qed.

(* [comment removed for export] *)
