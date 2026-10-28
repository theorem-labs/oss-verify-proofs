(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame HeapIface Asn1Aux Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StoreOk MemSplit SymExec2 SymExec2Sound SymDriveX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt ARtDrv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals ARestrict A_exit_base A_exit_lib A_exit_front1 A_tailkit_defs A_rip A_icpt_read.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations. Import SX2. Import SX2S.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_A_main_inv () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_shadow_ok"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.ZIMG_LO"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.ZIMG_HI"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.AgentSubmission.LibB.ARtDrv.drv_static"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.tail_memA"; "drv_kept"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_LO"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_HI"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.modulo"; "files_pristine"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Logic.or"; "RS"; "RSN"].

#[local] Unset Lia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation drv_static := ARtDrv.drv_static.

(* [comment removed for export] *)
Definition drv_compl : list ivl := ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "(0.(1.$2.$2.)(3.$2.$2.=+?:360.)(0.(1.$2.$2.)(3.$2.$2.+?:400.+?:460.)(0.(1.$2.$2.)(3.$2.$2.+?:780.+106390.)(0.(1.$2.$2.)(3.$2.$2.+106391.+62<050.)(0.(1.$2.$2.)(3.$2.$2.+63<080.+63<084.)(0.(1.$2.$2.)(3.$2.$2.+63<0:0.+63<180.)(0.(1.$2.$2.)(3.$2.$2.+63<9><.+63<9?0.)(0.(1.$2.$2.)(3.$2.$2.+63<:38.+63<:40.)(0.(1.$2.$2.)(3.$2.$2.+63<:88.+63<::4.)(0.(1.$2.$2.)(3.$2.$2.+63<:;0.+63<:<0.)(0.(1.$2.$2.)(3.$2.$2.+65<=50.+65<=58.)(0.(1.$2.$2.)(3.$2.$2.+65=:;0.(4.+2.+40.))(5.(1.$2.$2.))))))))))))))")
(* [comment removed for export] *).
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L12069892561.2000006S1a2Ha". (* [comment removed for export] *)
Lemma outside_drv_compl : forall a, 0 <= a < 2^64 -> outside drv_compl a <-> drv_static a.
Proof. intros a Ha. unfold drv_compl, drv_static. cbn. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition RS : Z := 0x62c050.
Definition RSN : Z := 65536.
Definition drv_kept (a : Z) : Prop := drv_static a /\ (a < RS \/ RS + RSN <= a).
Definition drv_compl_rs : list ivl := (RS, RS + RSN) :: drv_compl.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38021830416.2000003S1a". (* [comment removed for export] *)
Lemma outside_drv_compl_rs : forall a, 0 <= a < 2^64 -> outside drv_compl_rs a <-> drv_kept a.
Proof. intros a Ha. unfold drv_compl_rs, drv_kept, RS, RSN. cbn [outside fst snd]. rewrite <- (outside_drv_compl a Ha). unfold drv_compl. cbn. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition files_pristine (m : mem) : Prop := forall a : Z, 0x0fa578 <= a < 0x0fa780 -> m (Z_to_bv 64 a) = None.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L56765667309.2L59309037779.6L59309070547.4L59309070547.6L59309070672.6L59315336847.400000600>00F00O00W00_S1a2HaS1a1n2n0S1a2Ha1nS1a2Ha2n0S1a1n2n0S1a2Ha1n". (* [comment removed for export] *)
Lemma ro_addr_textA : forall a : Z, 0x10000 <= a < 0x0f1000 -> ro_addr asegs (wa a) = true.
Proof.
  intros a Ha. unfold ro_addr, wa. rewrite (u_small a) by lia.
  unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
  repeat match goal with
  | |- context [Z.of_N (seg_base ?s)] => let v := eval vm_compute in (Z.of_N (seg_base s)) in replace (Z.of_N (seg_base s)) with v by (vm_compute; reflexivity)
  | |- context [Z.of_N (seg_size ?s)] => let v := eval vm_compute in (Z.of_N (seg_size s)) in replace (Z.of_N (seg_size s)) with v by (vm_compute; reflexivity)
  | |- context [seg_writable ?s] => let v := eval vm_compute in (seg_writable s) in replace (seg_writable s) with v by (vm_compute; reflexivity)
  end.
  (* [comment removed for export] *)
  destruct (Z.leb_spec0 65536 a); destruct (Z.leb_spec0 (a + 1) (65536 + 221184)); cbn [andb];
    [vm_compute; reflexivity | | exfalso; lia | exfalso; lia].
  destruct (Z.leb_spec0 286720 a); destruct (Z.leb_spec0 (a + 1) (286720 + 700416)); cbn [andb];
    [vm_compute; reflexivity | exfalso; lia | exfalso; lia | exfalso; lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L16083901835.7000006S1a2Ha". (* [comment removed for export] *)
Lemma mem_inv_text_noneA : forall m (a : Z), mem_inv asegs m -> 0x10000 <= a < 0x0f1000 -> m (Z_to_bv 64 a) = None.
Proof.
  intros m a MI Ha. destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [|reflexivity].
  exfalso. pose proof (MI _ _ E) as X. change (Z_to_bv 64 a) with (wa a) in X. rewrite ro_addr_textA in X by lia. discriminate.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rtc_cell RTC a n v := exact (asan_rtc_cell _ a n v RTC ltac:(unfold rtc_cells; cbn [In]; repeat (first [left; reflexivity | right]))).
Lemma rtc_rd_consts : forall m, asan_rtc m -> rd_consts m.
Proof.
  intros m RTC. split; [rtc_cell RTC 0x10a6d8 1%nat 1 | rtc_cell RTC 0x0f7ba0 8%nat 0x0f00c4 |].
  split; [ rtc_cell RTC 0x0f5e50 8%nat 0x1099f8 | rtc_cell RTC 0x1099f8 8%nat 0x7fff8000 | rtc_cell RTC 0x0f5e58 8%nat 0x10a6e8
         | rtc_cell RTC 0x0f5e60 8%nat 0x10a6f0 | rtc_cell RTC 0x0f5e68 8%nat 0x10a6e0 | rtc_cell RTC 0x10a6e8 8%nat 0
         | rtc_cell RTC 0x10a6f0 8%nat 0 | rtc_cell RTC 0x10a6e0 8%nat 0x7fffffffffff ].
Qed.


(* [comment removed for export] *)
Lemma img_globs_above : forallb (fun r => 0x49a5 <=? fst (glob_piv r)) img_globs = true.
Proof. vm_compute. reflexivity. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L46039047271.2L59315036641.800000600DS1g2HgS1g2Hg2lo2I11B". (* [comment removed for export] *)
Lemma img_shval_low : forall g, 0x2000 <= g < 0x49a5 -> img_shval g = 0.
Proof.
  intros g Hg. unfold img_shval.
  replace (in_iv g tab_piv) with false.
  2:{ symmetry. unfold in_iv, tab_piv, ATAB, ATAB_N. apply Bool.andb_false_iff. left. apply Z.leb_gt. cbn. lia. }
  destruct (find (fun r => in_iv g (glob_piv r)) img_globs) as [r|] eqn:E; [|reflexivity].
  exfalso. apply find_some in E. destruct E as [IN IV].
  pose proof (proj1 (forallb_forall _ _) img_globs_above r IN) as B. cbn beta in B.
  destruct (glob_piv r) as [lo hi]. cbn [fst] in B. unfold in_iv in IV. apply andb_prop in IV. destruct IV as [I1 _].
  apply Z.leb_le in B. apply Z.leb_le in I1. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L45751123804.6L55686436812.9L57565870410.8L61028955103.8L63345811781.8L6355131649.1000000600;00C00D00G00OS1a2HaS1a1gS1a1g2HgSS1aS1a2Ha1g". (* [comment removed for export] *)
Lemma img_shadow_low_zero : ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "PAL,$6.Pm,P,(7.&40.)(8.(7.&8.))P,(9.$2.(:.R2.)+7???8000.)P,(;.$<.R3.R2.)Pa,$2.P,(=.(>.$?.R1.)(10.R1.$11.))(9.(8.(7.&8.))A1.R5.(12.&40.R2.)(13.(7.&8.)(12.&8.=)))")
(* [comment removed for export] *).
Proof.
  intros AL m SB ISH a Ha. unfold ZIMG_LO, ZIMG_HI in Ha.
  set (g := a - 0x7fff8000).
  assert (Hg : 0x2000 <= g < 0x49a5) by (subst g; lia).
  pose proof (img_shadow_ok_zero asegs AL m g ISH ltac:(unfold IMG_GLO, IMG_GHI; lia) ltac:(unfold img_shadow0; rewrite (img_shval_low g Hg); reflexivity)) as BY.
  replace (shadow_of AL (8 * g)) with a in BY. 2:{ unfold shadow_of. rewrite SB. subst g. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
  ddestruct BY as (_ & _ & BY). specialize (BY 0%nat ltac:(cbn; lia)). cbn [nth_error] in BY. rewrite Z.add_0_r in BY.
  unfold mrd in BY. unfold wa in BY. destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
  - cbn in BY. congruence.
  - exfalso. pose proof (A_exit_lib.seg_rom_high a ltac:(unfold AIMG_HI; lia)) as SR. unfold wa in SR. rewrite SR in BY. discriminate.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L45781502933.1400000;S1A2cs1i2Hi". (* [comment removed for export] *)
Lemma rw_cells_transport_w : ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "PW,(14.$15.)Pm,P,(7.&40.)(8.(7.&8.))Pm',P,(7.&40.)(8.(7.&8.))PA,$2.Pcs,(14.$16.)P,(17.$<.R4.R2.R1.)P,(18.R6.R5.R4.)P,Pa,$2.P,(=.(>.R5.R1.)(10.R1.(19.R5.(1:.(1;.R4.)))))P,(1<.(9.(8.(7.&8.))(1=.$<.R8.(1>.R2.))(1?.(7.&8.))))(1<.(9.(8.(7.&8.))(1=.$<.R8.(1>.R3.))(1?.(7.&8.))))P,(20.R8.R5.(1:.(1;.R4.)))(17.$<.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' A cs [RO WR] MU WV DJ. split.
  - eapply ro_cells_transport; [exact RO | exact MU | exact DJ].
  - ddestruct WR as (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|]. intros i Hi. apply WV; [lia|]. apply H2. exact Hi.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Inv.
  Variable R : art_layout.
  Variable HIA : artA asegs R.
  Let AL := arl_AL R.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis HRTC : forall m, arl_rtc R m -> asan_rtc m.
  Hypothesis HM_LOWSH : forall h LB LF m, HM asegs R HIA h LB LF m -> mapped m 0x7fffa000 0x800d3000.
  Hypothesis HM_ZIMG : ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "Ph,(21.$<.VR,VHIA,)PLB,(14.$22.)PLF,(14.$22.)Pm,P,(7.&40.)(8.(7.&8.))P,(23.$<.VR,VHIA,R4.R3.R2.R1.)Pa,$2.P,(=.(>.$?.R1.)(10.R1.$11.))(9.(8.(7.&8.))A1.R4.(12.&40.R2.)(13.(7.&8.)(12.&8.=)))")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Hypothesis DRVS : forall a, drv_static a -> cstatic R a.
  Variables (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L53024458802.27L56765666148.2700000:00JS1a1n1j2HjS1a1n2Ha2Hn1j2Hj". (* [comment removed for export] *)
  #[using="Type"] Lemma rdn_agree_pred : ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "PP,P,$2.SpPm,Px,(7.&40.)(8.(7.&8.))Pm',Px,(7.&40.)(8.(7.&8.))Pa,$2.Pn,$24.Pbs,(14.(7.&8.))P,Px,$2.P,A1.R7.R1.(9.(8.(7.&8.))A1.R6.(1>.R2.)A1.R7.(1>.R2.))P,Px,$2.P,(=.(>.R5.R1.)(10.R1.(19.R5.(1:.R4.))))A1.R9.R2.P,(>.=R5.)P,(>.(19.R6.(1:.R5.))(4.+2.+40.))P,(9.(8.(14.(7.&8.)))(25.$<.R9.(12.&40.R7.)R6.)(13.(14.(7.&8.))R5.))(9.(8.(14.(7.&8.)))(25.$<.R9.(12.&40.R8.)R7.)(13.(14.(7.&8.))R6.))")
(* [comment removed for export] *).
  Proof.
    intros P m m' a n bs AG DS Ha Hn H. rewrite <- H. symmetry. apply rdn_agree. intros j Hj. rewrite u_small by lia.
    symmetry. change (Z_to_bv 64 (a + Z.of_nat j)) with (wa (a + Z.of_nat j)). apply AG. apply DS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma rdn_agree_static : ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "Pm,Px,(7.&40.)(8.(7.&8.))Pm',Px,(7.&40.)(8.(7.&8.))Pa,$2.Pn,$24.Pbs,(14.(7.&8.))P,Px,$2.P,(26.R1.)(9.(8.(7.&8.))A1.R6.(1>.R2.)A1.R7.(1>.R2.))P,Px,$2.P,(=.(>.R5.R1.)(10.R1.(19.R5.(1:.R4.))))(26.R2.)P,(>.=R5.)P,(>.(19.R6.(1:.R5.))(4.+2.+40.))P,(9.(8.(14.(7.&8.)))(25.$<.R9.(12.&40.R7.)R6.)(13.(14.(7.&8.))R5.))(9.(8.(14.(7.&8.)))(25.$<.R9.(12.&40.R8.)R7.)(13.(14.(7.&8.))R6.))")
(* [comment removed for export] *).
  Proof. exact (rdn_agree_pred drv_static). Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0?L1240803304.50 L12971186197.54L13989399637.54L14499301895.50L15823104540.54L16800013344.54L18925010976.54L19055460448.54L19900862718.52L19900862718.55L21918964855.54L22696620384.54L27045534584.51L28836423456.54L30963002144.54L31564125703.54L34849821856.54L36362444629.54L37732096680.50L38056642261.54L40634434460.54L40845677333.54L43004104224.54L44353546140.50L4761991456.54 L47903664213.54L49402993052.54L52399232597.54L54967697052.54L56156922531.53L57614144341.54L57643738119.54L59315354426.50L60427588053.54L61192393640.50L62122842453.54L63709270919.54L63820332456.50L66442651500.54L67672770216.50L68570113960.53L866750368.54  L8787542563.52 L8787542563.56 L9911160071.54 00000100200300400500600700800>00L00M00N00S00T00U00V00W00X00Y00Z00[00\00]00^00_00`00a00b00c00l00m00n00o01001101201301401501601701801=01B01CSSSSSSSSS1a2HaS1A2cs2DS1a2HaSSS1x1HSSSSSSSSSSSSSSSSS1A2cs2DSSSSSSSSSSSSSS1x1HS1x1HS". (* [comment removed for export] *)
  #[using="HRTC HM_LOWSH HM_ZIMG"] Theorem tail_rebuild : ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "Psp,(7.&40.)Pm,P,(7.&40.)(8.(7.&8.))Pm',Px,(7.&40.)(8.(7.&8.))Ph',(21.$<.VR,VHIA,)PLB',(14.$22.)PLF,(14.$22.)P,(27.R6.R5.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,Pa,$2.P,(28.R1.)(9.(8.(7.&8.))A1.R7.(1>.R2.)A1.R8.(1>.R2.))P,Pa,$2.P,(28.R1.)P,(1<.(9.(8.(7.&8.))(1=.$<.R9.(1>.R2.))(1?.(7.&8.))))(1<.(9.(8.(7.&8.))(1=.$<.R9.(1>.R3.))(1?.(7.&8.))))P,Pa,$2.P,(=.(>.(29.R:.)R1.)(10.R1.(2:.R:.)))(9.(8.(7.&8.))A1.R9.(12.&40.R2.)A1.R:.(12.&40.R2.))P,(23.$<.VR,VHIA,R7.R6.R5.R8.)P,(2;.$<.R9.)P,(2<.$<.R:.(2=.(2>.&40.R<.)+1000.)(2>.&40.R<.))(27.R=.R;.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)")
(* [comment removed for export] *).
  Proof.
    intros sp m m' h' LB' LF TM AG WV SH HH MI ST. pose proof (u64_range sp) as SPR.
    destruct TM as [WIN RO ERR CAN RTC ZI ZS STK MI0 TID LOCK MTID ATEXIT NL COMP MAPPED GLOB FIN FOUT FLG INCB].
    assert (MU : munch drv_compl_rs m m').
    { intros x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)).
      apply AG. apply (proj1 (outside_drv_compl_rs (bv_unsigned x) ltac:(lia))). exact Hx. }
    assert (RW : forall A cs, rw_cells asegs m A cs ->
                 (0x0fa360 <= A /\ A + Z.of_nat (cells_size cs) <= 0x0fa400) \/ (0x0fa460 <= A /\ A + Z.of_nat (cells_size cs) <= 0x0fa780) \/ (A = 0x106390 /\ cells_size cs = 1%nat) \/ (0x63c180 <= A /\ A + Z.of_nat (cells_size cs) <= 0x63c9ec) \/ (0x63cae8 <= A /\ A + Z.of_nat (cells_size cs) <= 0x65cd50) \/ (0x63c050 <= A /\ A + Z.of_nat (cells_size cs) <= 0x63c080) ->
                 rw_cells asegs m' A cs).
    { intros A cs H DS. eapply rw_cells_transport_w; [exact H | exact MU | intros a Ha; apply WV; unfold drv_kept, drv_static, RS, RSN; lia |].
      unfold drv_compl_rs, drv_compl, RS, RSN. cbn [disjoint_from fst snd]. lia. }
    split.
    - intros a Ha. pose proof (proj1 (proj2 (proj2 ST) (bv_unsigned a) Ha)) as W. unfold wa in W. rewrite Z_to_bv_bv_unsigned in W. exact W.
    - intros a Ha. apply mem_inv_text_noneA; [exact MI | exact Ha].
    - intros a Ha. change (Z_to_bv 64 a) with (wa a). rewrite AG; [apply ERR; exact Ha | unfold drv_kept, drv_static, RS, RSN; lia].
    - eapply (rdn_agree_pred drv_kept); [exact AG | unfold drv_kept, drv_static, RS, RSN; intros; lia | lia | cbn; lia | exact CAN].
    - apply HRTC. eapply (hm_rtc _ _ HIA). exact HH.
    - eapply HM_ZIMG. exact HH.
    - intros a Ha. rewrite SH by exact Ha. apply ZS. exact Ha.
    - exact ST.
    - exact MI.
    - exact TID.
    - apply RW; [exact LOCK | cbn; lia].
    - apply RW; [exact MTID | cbn; lia].
    - ddestruct ATEXIT as (jp & jq & jf & AT). dexists jp, jq, jf. unfold atexit_cells in *.
      apply RW; [exact AT | cbn; lia].
    - eapply ro_cells_transport; [exact NL | exact MU |]. unfold drv_compl_rs, drv_compl, RS, RSN. cbn [disjoint_from fst snd cells_size csize]. lia.
    - apply RW; [exact COMP | cbn; lia].
    - eapply HM_LOWSH. exact HH.
    - ddestruct GLOB as (Q1 & Q2 & Q3 & Q4 & Q5). unfold stdio_globals.
      repeat split; (eapply (rdn_agree_pred drv_kept); [exact AG | unfold drv_kept, drv_static, RS, RSN; intros; lia | lia | cbn; lia | assumption]).
    - ddestruct FIN as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean.
      repeat split; (eapply (rdn_agree_pred drv_kept); [exact AG | unfold drv_kept, drv_static, RS, RSN; intros; lia | lia | cbn; lia | assumption]).
    - ddestruct FOUT as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean.
      repeat split; (eapply (rdn_agree_pred drv_kept); [exact AG | unfold drv_kept, drv_static, RS, RSN; intros; lia | lia | cbn; lia | assumption]).
    - apply RW; [exact FLG | cbn; lia].
    - apply RW; [exact INCB | cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L17607520885.38L28291499091.35L33278878119.33L34761659771.36L56765454317.38L56765480893.36L56765667309.35L61028789409.3600000Q00g01001:01M01Z01g01oS1R2sp5STKHI2LO2HI3SPR3LO01a1c2HcS2sp4AL163SPR3LO01a2HaS1R2sp2LOS2sp3LO01aS2sp3SPR3LO01a1c2HcS2sp3SPR1a2HaS2sp3SPR1a2HaS2sp3LO0". (* [comment removed for export] *)
  #[using="AL ASB HRTC HM_LOWSH HM_ZIMG DRVS"] Theorem tail_presA : ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "Psp,(7.&40.)Pm,P,(7.&40.)(8.(7.&8.))Pm',P,(7.&40.)(8.(7.&8.))Ph',(21.$<.VR,VHIA,)PLB,(14.$22.)PLB',(14.$22.)PLF,(14.$22.)PSTKHI,$2.P,(27.R8.R7.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,(2?.$<.VR,R5.R3.(2>.&40.R9.)(30.VR,)R2.(5.$15.)R8.R7.)P,(23.$<.VR,VHIA,R7.R5.R4.R8.)P,(2;.$<.R9.)P,(2<.$<.R:.(30.VR,)(2>.&40.R<.))P,(>.(19.(30.VR,)+1000.)(2>.&40.R=.))P,(>.(2>.&40.R>.)R7.)P,(9.$2.(31.(2>.&40.R?.)+10.)=)(27.R10.R>.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)")
(* [comment removed for export] *).
  Proof.
    intros sp m m' h' LB LB' LF STKHI TM [HP SHD] HH MI ST LO HI AL16. pose proof (u64_range sp) as SPR.
    pose proof (proj1 (tm_stk _ _ _ _ _ _ _ _ TM)) as LO0.
    eapply tail_rebuild; [exact TM | | | | exact HH | exact MI | eapply (proj2 (stk_split asegs m' (arl_stklo R) (bv_unsigned sp - 4096) (bv_unsigned sp) ST ltac:(lia)))].
    - intros a [Ha _]. pose proof (DRVS a Ha) as [D1 _].
      apply (proj1 (HP a ltac:(unfold drv_static in Ha; lia) ltac:(right; left; exact (DRVS a Ha)) ltac:(exact I))).
    - intros a [Ha _]. apply (proj2 (HP a ltac:(unfold drv_static in Ha; lia) ltac:(right; left; exact (DRVS a Ha)) ltac:(exact I))).
    - intros a Ha. unfold SSH_LO, SSH_HI in Ha.
      set (c := 8 * (a - 0x7fff8000)).
      assert (Hc : bv_unsigned sp - 4096 <= c < bv_unsigned sp) by (subst c; lia).
      assert (Ea : shadow_of (arl_AL R) c = a). { unfold shadow_of. change (arl_AL R) with AL. rewrite ASB. subst c. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
      pose proof (proj1 (SHD c ltac:(left; lia) ltac:(rewrite Ea; lia))) as E1. rewrite Ea in E1. unfold wa in E1. exact E1.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L36029363060.24L56759174154.2500000600<S1a2HaS1a2Ha". (* [comment removed for export] *)
  #[using="DRVS"] Lemma files_presA : ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "Pm,P,(7.&40.)(8.(7.&8.))Pm',P,(7.&40.)(8.(7.&8.))PLB,(14.$22.)PLF,(14.$22.)PSP,$2.PSTKHI,$2.P,(32.R6.)P,(2?.$<.VR,R5.R4.R3.(30.VR,)R2.(5.$15.)R7.R6.)(32.R7.)")
(* [comment removed for export] *).
  Proof.
    intros m m' LB LF SP STKHI FP [HP _] a Ha.
    assert (D : drv_static a) by (unfold drv_static; lia).
    pose proof (proj1 (HP a ltac:(lia) ltac:(right; left; exact (DRVS a D)) ltac:(exact I))) as E.
    unfold wa in E. rewrite E. apply FP. exact Ha.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L53505215649.8 L56765667309.2200000G00MS2lo2hi1W2D12D21a2Ha2IHS1a2Ha". (* [comment removed for export] *)
  #[using="Type"] Lemma files_munch : ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "Pm,P,(7.&40.)(8.(7.&8.))Pm',P,(7.&40.)(8.(7.&8.))PW,(14.$15.)P,(32.R3.)P,(18.R2.R4.R3.)P,(20.R3.+?:578.(2=.+?:780.+?:578.))(32.R5.)")
(* [comment removed for export] *).
  Proof.
    intros m m' W FP MU DJ a Ha. change (Z_to_bv 64 a) with (wa a). rewrite (MU (wa a)).
    - apply FP. exact Ha.
    - rewrite wa_unsigned by lia. clear -DJ Ha. induction W as [|[lo hi] W IH]; cbn in *; [exact I|]. destruct DJ as [D1 D2]. split; [lia | apply IH; exact D2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L34227238271.31L59308694102.35L62024336360.3100000?00P00VS1R3HIA1h2hi2HIS1R2hi2GE1g2G12G2S1R2hi". (* [comment removed for export] *)
  #[using="Type"] Lemma sshad_keep_munch : ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "Ph,(21.$<.VR,VHIA,)PLB,(14.$22.)PLF,(14.$22.)Pm,P,(7.&40.)(8.(7.&8.))Pm',P,(7.&40.)(8.(7.&8.))PB,$2.PE,$2.Phi,$2.P,(23.$<.VR,VHIA,R8.R7.R6.R5.)P,(33.$<.VAL,R6.(30.VR,)R2.)P,(18.(0.(1.$2.$2.)(3.$2.$2.R5.R4.)(0.(1.$2.$2.)(3.$2.$2.(30.VR,)R3.)(5.(1.$2.$2.))))R7.R6.)P,(34.$<.R8.R7.)P,(35.(36.$<.VR,VHIA,R<.)R7.(2=.R6.R7.))P,(>.R6.(37.$<.VR,VHIA,R=.))(33.$<.VAL,R:.(30.VR,)R7.)")
(* [comment removed for export] *).
  Proof.
    intros h LB LF m m' B E hi HH SS MU WM CB HI.
    pose proof (proj1 SS) as M0. pose proof (proj1 (proj2 SS)) as M1.
    destruct (Z_lt_le_dec (arl_stklo R) hi) as [LT|GE].
    - eapply (sshad_munch asegs AL (hcs asegs R HIA h)); [apply (hcs_ok _ _ HIA h) | | | exact MU | exact WM | exact SS].
      + unfold w_client. constructor; [cbn [fst snd]; exact CB | constructor; [cbn [fst snd] | constructor]].
        eapply crange_sub; [apply (hcs_stack _ _ HIA h) | lia | lia].
      + eapply crange_sub; [apply (hcs_stack _ _ HIA h) | lia | lia].
    - split; [exact M0|]. split; [exact M1|]. intros g G1 G2 G3. exfalso. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L56765667309.35L57628696595.3500000A00cS1a2Ha2sp3HSP3SPRS1R2sp1B1E3HB03HLO1a2Ha2HB3HSP3SPR". (* [comment removed for export] *)
  #[using="HRTC HM_LOWSH HM_ZIMG"] Theorem tail_munch : ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "Psp,(7.&40.)Pm,P,(7.&40.)(8.(7.&8.))Pm',P,(7.&40.)(8.(7.&8.))Ph',(21.$<.VR,VHIA,)PLB',(14.$22.)PLF,(14.$22.)PB,$2.PE,$2.P,(27.R8.R7.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,(18.(0.(1.$2.$2.)(3.$2.$2.R3.R2.)(0.(1.$2.$2.)(3.$2.$2.(30.VR,)(2>.&40.R9.))(5.(1.$2.$2.))))R8.R7.)P,(34.$<.R9.R8.)P,(>.+65?000.R5.)P,(38.(>.R5.+7???7000.)(>.+10007???8000.R6.))P,(>.+10007???8000.(30.VR,))P,(10.(2>.&40.R>.)(4.+2.+2?.))P,(23.$<.VR,VHIA,R<.R;.R:.R=.)P,(2;.$<.R>.)P,(2<.$<.R?.(2=.(2>.&40.R11.)+1000.)(2>.&40.R11.))(27.R12.R10.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)")
(* [comment removed for export] *).
  Proof.
    intros sp m m' h' LB' LF B E TM MU WM HB0 HB HLO HSP HH MI ST. pose proof (u64_range sp) as SPR.
    eapply tail_rebuild; [exact TM | | | | exact HH | exact MI | exact ST].
    - intros a [Ha _]. apply MU. rewrite wa_unsigned by (unfold drv_static in Ha; lia). cbn. unfold drv_static in Ha. lia.
    - intros a Ha W0. apply WM. exact W0.
    - intros a Ha. unfold SSH_LO, SSH_HI in Ha. change (Z_to_bv 64 a) with (wa a). apply MU. rewrite wa_unsigned by lia. cbn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L56763572091.34L56765667309.33L57626601605.34L57628696595.3300000600G00_01;S1a2HaS2sp3HSP3SPR1a2HaS1R2sp1w2Hw3HLO1a2Ha3HrsS1R2sp1w2Hw3HLO3HSP3SPR1a2Ha". (* [comment removed for export] *)
  #[using="HRTC HM_LOWSH HM_ZIMG"] Theorem tail_munch_rs : ltac2:(CDefT.buildp (gd_tbl_A_main_inv ()) "Psp,(7.&40.)Pm,P,(7.&40.)(8.(7.&8.))Pm',P,(7.&40.)(8.(7.&8.))Ph',(21.$<.VR,VHIA,)PLB',(14.$22.)PLF,(14.$22.)Pw,$2.P,(27.R7.R6.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,(18.(0.(1.$2.$2.)(3.$2.$2.$39.(19.$39.R2.))(0.(1.$2.$2.)(3.$2.$2.(30.VR,)(2>.&40.R8.))(5.(1.$2.$2.))))R7.R6.)P,(34.$<.R8.R7.)P,(=.(>.=R4.)(>.R4.$3:.))P,(>.+10007???8000.(30.VR,))P,(10.(2>.&40.R<.)(4.+2.+2?.))P,(23.$<.VR,VHIA,R:.R9.R8.R;.)P,(2;.$<.R<.)P,(2<.$<.R=.(2=.(2>.&40.R?.)+1000.)(2>.&40.R?.))(27.R10.R>.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)")
(* [comment removed for export] *).
  Proof.
    intros sp m m' h' LB' LF w TM MU WM Hw HLO HSP HH MI ST. pose proof (u64_range sp) as SPR.
    eapply tail_rebuild; [exact TM | | | | exact HH | exact MI | exact ST].
    - intros a [Ha Hrs]. apply MU. rewrite wa_unsigned by (unfold drv_static in Ha; lia). cbn. unfold drv_static in Ha. unfold RS, RSN in *. lia.
    - intros a Ha W0. apply WM. exact W0.
    - intros a Ha. unfold SSH_LO, SSH_HI in Ha. change (Z_to_bv 64 a) with (wa a). apply MU. rewrite wa_unsigned by lia. cbn. unfold RS, RSN in *. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Inv.
