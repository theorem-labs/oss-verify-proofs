(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Exec Shape Mem Cells Arr Frame Step.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_string.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA AShadow Restrict RestrictLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg ARestrict A_string.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac dcov CV := cbn [cells_size csize cells_bytes length app]; rewrite ?Nat.add_0_r, ?repeat_length; rewrite ?Z2Nat.id by lia;
  first [ exact CV | eapply Dcov_sub; [exact CV | lia | lia] ].
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_stringA () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.P.P_string.memcpy_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "Stdlib.ZArith.BinInt.Z.pow"; "WithLayout.memset_postZ"; "RocqVerifyHarness.AgentSubmission.P.P_string.memcmp_post"].


Section WithLayout.
Variable AL : asan_layout.
Variable CS : Z -> Prop.
Hypothesis IMG : asan_img_ok AL.

#[using="IMG"] Theorem A_memcpy_evtA : ltac2:(CDefT.buildp (gd_tbl_A_stringA ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Psrc,(3.(0.&8.))Pjunk,(3.(0.&8.))P,(4.$5.R3.(6.&40.R1:.)R2.)P,(7.$8.(9.(0.&8.)R3.)(:.(6.&40.R1:.)))P,(;.$5.R5.(6.&40.R1=.)(<.$=.(>.(:.(6.&40.R1;.))R3.)(?.$=.)))P,(10.(11.(12.(6.&40.R1=.)(6.&40.R1<.))(6.&40.R1>.))(11.(12.(6.&40.R1>.)(6.&40.R1<.))(6.&40.R1=.)))P,(13.$5.R7.)P,(14.VCS,(6.&40.R20.)(6.&40.R1>.))P,(14.VCS,(6.&40.R20.)(6.&40.R1?.))P,(15.=(6.&40.R22.))P,(15.=(6.&40.R22.))(16.$5.VAL,VCS,(17.$5.R2=.R2<.R2;.R2:.R26.R25.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R>.R=.R24.R23.R22.R;.R<.)(18.(19.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R>.(1:.&40.+>:9<0.)R=.(1;.(0.&40.))R<.(1<.$5.)))")
(* [comment removed for export] *).
Proof.
  intros until junk. intros SRC LEN DST SEP MI C0 C1 P0 P1.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R0, R1, R2.
  set (n := bv_unsigned a2) in *.
  assert (B0 : bv_unsigned a0 + n <= 2^64).
  { destruct DST as [_ (_ & W1 & _)]. cbn [cells_size csize] in W1. rewrite Nat.add_0_r, Z2Nat.id in W1 by lia. exact W1. }
  assert (B1 : bv_unsigned a1 + n <= 2^64).
  { ddestruct SRC as (_ & S1 & _). rewrite LEN, Z2Nat.id in S1 by lia. exact S1. }
  set (ivs := [(bv_unsigned a0, bv_unsigned a0 + n); (bv_unsigned a1, bv_unsigned a1 + n)]).
  assert (HCS : Forall (fun iv => crange CS (fst iv) (snd iv - fst iv)) ivs).
  { subst ivs. constructor; [|constructor; [|constructor]]; cbn;
      [ replace (bv_unsigned a0 + n - bv_unsigned a0) with n by lia; exact C0
      | replace (bv_unsigned a1 + n - bv_unsigned a1) with n by lia; exact C1 ]. }
  assert (H0 : Forall (fun iv => 0 < fst iv) ivs) by (subst ivs; repeat constructor; cbn; lia).
  assert (CV0 : Dcov (Dimg ivs) (bv_unsigned a0) (bv_unsigned a0 + n)).
  { apply Dimg_cov; [subst ivs; left; reflexivity | lia | lia]. }
  assert (CV1 : Dcov (Dimg ivs) (bv_unsigned a1) (bv_unsigned a1 + n)).
  { apply Dimg_cov; [subst ivs; right; left; reflexivity | lia | lia]. }
  eapply evtA_mono.
  - eapply (evtA_of_evt_img AL CS IMG ivs). 1,2: assumption.
    (* [comment removed for export] *)
    apply (A_memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
             (restrict (Dimg ivs) m) src junk).
    + apply (proj2 (bytes_at_restrict asegs (Dimg ivs) m (bv_unsigned a1) src ltac:(dcov CV1))). exact SRC.
    + exact LEN.
    + apply (proj2 (rw_cells_restrict asegs (Dimg ivs) m (bv_unsigned a0) [CB (Z.to_nat n) junk] ltac:(dcov CV0))). exact DST.
    + exact SEP.
    + apply mem_inv_restrict. exact MI.
  - (* [comment removed for export] *)
    cbn beta. intros ms1 [POST AGREE].
    ddestruct POST as (x5 & x6 & x7 & a1' & a2' & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m'D & E & MU & WM & MI' & RW & BA).
    destruct (rms_eq_MS (Dimg ivs) ms1 _ _ _ _ _ _ _ E) as (M1 & -> & RM).
    cbn [ms_mem MS] in AGREE. subst m'D.
    dexists x5, x6, x7, a1', a2', x13, x14, x15, x16, x17, x28, x29, x30, x31, M1.
    split; [reflexivity|]. split; [eapply munch_unrestrict; eauto|]. split; [eapply wmono_unrestrict; eauto|].
    split; [eapply mem_inv_unrestrict; eauto|].
    split.
    + apply (proj1 (rw_cells_restrict asegs (Dimg ivs) M1 (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src] ltac:(dcov CV0))). exact RW.
    + apply (proj1 (bytes_at_restrict asegs (Dimg ivs) M1 (bv_unsigned a1) src ltac:(dcov CV1))). exact BA.
Qed.


(* [comment removed for export] *)
Definition memset_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S k v : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_stringA ()) "Lms',$1=.(1>.(0.&40.)Lt0,(0.&40.)(1>.(0.&40.)Lt1,(0.&40.)(1>.(0.&40.)Lt2,(0.&40.)(1>.(0.&40.)La1',(0.&40.)(1>.(0.&40.)La2',(0.&40.)(1>.(0.&40.)La3,(0.&40.)(1>.(0.&40.)La4,(0.&40.)(1>.(0.&40.)La5,(0.&40.)(1>.(0.&40.)La6,(0.&40.)(1>.(0.&40.)La7,(0.&40.)(1>.(0.&40.)Lt3,(0.&40.)(1>.(0.&40.)Lt4,(0.&40.)(1>.(0.&40.)Lt5,(0.&40.)(1>.(0.&40.)Lt6,(0.&40.)(1>.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(1?.(7.$1=.R10.(18.(19.O16.O15.O14.O13.R?.R>.R=.O12.O11.(1:.&40.O4.)R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(20.O16.)O5.(1;.(0.&40.))R1.(1<.$5.)))(1?.(21.(<.(22.$23.$23.)(24.$23.$23.O4.(12.O4.O3.))(?.(22.$23.$23.)))O1.R1.)(1?.(25.$5.O1.R1.)(1?.(13.$5.R1.)(;.$5.R1.O4.(<.$=.(>.(:.O3.)(26.(0.&8.)(1:.&8.O2.)(:.O3.)))(?.$=.))))))))))))))))))))))")
(* [comment removed for export] *).

#[using="IMG"] Theorem A_memset_evtA_aok : ltac2:(CDefT.buildp (gd_tbl_A_stringA ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))PS,$23.Pk,$23.Pv,$23.Pjunk,(3.(0.&8.))P,(;.$5.R5.R4.(<.$=.(>.(:.R3.)R1.)(?.$=.)))P,(13.$5.R6.)P,Px,$23.P,(1?.(11.R7.R1.)(15.R1.(12.R7.R6.)))(27.VAL,VCS,R2.)P,(15.=R7.)P,(11.=R7.)P,(15.(12.R9.R8.)(28.+2.+40.))P,(1?.(11.=R8.)(15.R8.+100.))P,(7.(0.&40.)R24.(1:.&40.R;.))P,(7.(0.&40.)R24.(1:.&40.R:.))P,(7.(0.&40.)R24.(1:.&40.R<.))(16.$5.VAL,VCS,(29.R30.R2?.R2>.R2=.R29.R28.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R11.R10.R>.R=.R<.R?.)(18.(19.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(1:.&40.+>:=<4.)R10.(1;.(0.&40.))R?.(1<.$5.)))")
(* [comment removed for export] *).
Proof.
  intros until junk. intros DST MI AOK P0 K0 B0 V0 -> -> ->.
  rewrite <- (unsigned_lit S) in DST by lia.
  set (ivs := [(S, S + k)]).
  assert (HA : Forall (fun iv => forall z, fst iv <= z < snd iv -> aok_addr AL CS z) ivs).
  { subst ivs. constructor; [|constructor]. cbn. exact AOK. }
  assert (H0 : Forall (fun iv => 0 < fst iv) ivs) by (subst ivs; repeat constructor; cbn; lia).
  assert (CV0 : Dcov (Dimg ivs) S (S + k)).
  { apply Dimg_cov; [subst ivs; left; reflexivity | lia | lia]. }
  eapply evtA_mono.
  - eapply (evtA_of_evt_imgA AL CS IMG ivs). 1,2: assumption.
    apply (A_memset_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 v) (Z_to_bv 64 k) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
             (restrict (Dimg ivs) m) junk).
    + apply (proj2 (rw_cells_restrict asegs (Dimg ivs) m (bv_unsigned (Z_to_bv 64 S)) [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 k))) junk]
               ltac:(rewrite !unsigned_lit by lia; dcov CV0))). rewrite (unsigned_lit k) by lia. exact DST.
    + apply mem_inv_restrict. exact MI.
  - cbn beta. intros ms1 [POST AGREE].
    ddestruct POST as (x5 & x6 & x7 & a1' & a2' & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m'D & E & MU & WM & MI' & RW).
    destruct (rms_eq_MS (Dimg ivs) ms1 _ _ _ _ _ _ _ E) as (M1 & -> & RM).
    cbn [ms_mem MS] in AGREE. subst m'D.
    dexists x5, x6, x7, a1', a2', x13, x14, x15, x16, x17, x28, x29, x30, x31, M1.
    rewrite !unsigned_lit in MU by lia. rewrite ?(unsigned_lit S), ?(unsigned_lit k), ?(unsigned_lit v) in RW by lia.
    rewrite (Z.mod_small v 256) in RW by lia.
    split; [reflexivity|]. split; [eapply munch_unrestrict; eauto|]. split; [eapply wmono_unrestrict; eauto|].
    split; [eapply mem_inv_unrestrict; eauto|].
    apply (proj1 (rw_cells_restrict asegs (Dimg ivs) M1 S [CB (Z.to_nat k) (repeat (Z_to_bv 8 v) (Z.to_nat k))] ltac:(dcov CV0))). exact RW.
Qed.

(* [comment removed for export] *)
#[using="IMG"] Theorem A_memcmp_evtA : ltac2:(CDefT.buildp (gd_tbl_A_stringA ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pxs,(3.(0.&8.))Pys,(3.(0.&8.))P,(4.$5.R3.(6.&40.R1;.)R2.)P,(4.$5.R4.(6.&40.R1;.)R2.)P,(7.$8.(9.(0.&8.)R4.)(:.(6.&40.R1;.)))P,(7.$8.(9.(0.&8.)R4.)(:.(6.&40.R1<.)))P,(14.VCS,(6.&40.R1?.)(6.&40.R1=.))P,(14.VCS,(6.&40.R1?.)(6.&40.R1>.))P,(15.=(6.&40.R21.))P,(15.=(6.&40.R21.))(16.$5.VAL,VCS,(2:.$5.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R:.R9.R;.)(18.(19.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(1:.&40.+>:990.)R<.(1;.(0.&40.))R;.(1<.$5.)))")
(* [comment removed for export] *).
Proof.
  intros until ys. intros HX HY LX LY C0 C1 P0 P1.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R0, R1, R2.
  set (n := bv_unsigned a2) in *.
  assert (B0 : bv_unsigned a0 + n <= 2^64). { ddestruct HX as (_ & S1 & _). rewrite LX, Z2Nat.id in S1 by lia. exact S1. }
  assert (B1 : bv_unsigned a1 + n <= 2^64). { ddestruct HY as (_ & S1 & _). rewrite LY, Z2Nat.id in S1 by lia. exact S1. }
  set (ivs := [(bv_unsigned a0, bv_unsigned a0 + n); (bv_unsigned a1, bv_unsigned a1 + n)]).
  assert (HCS : Forall (fun iv => crange CS (fst iv) (snd iv - fst iv)) ivs).
  { subst ivs. constructor; [|constructor; [|constructor]]; cbn;
      [ replace (bv_unsigned a0 + n - bv_unsigned a0) with n by lia; exact C0
      | replace (bv_unsigned a1 + n - bv_unsigned a1) with n by lia; exact C1 ]. }
  assert (H0 : Forall (fun iv => 0 < fst iv) ivs) by (subst ivs; repeat constructor; cbn; lia).
  assert (CV0 : Dcov (Dimg ivs) (bv_unsigned a0) (bv_unsigned a0 + n)).
  { apply Dimg_cov; [subst ivs; left; reflexivity | lia | lia]. }
  assert (CV1 : Dcov (Dimg ivs) (bv_unsigned a1) (bv_unsigned a1 + n)).
  { apply Dimg_cov; [subst ivs; right; left; reflexivity | lia | lia]. }
  eapply evtA_mono.
  - eapply (evtA_of_evt_img AL CS IMG ivs). 1,2: assumption.
    apply (A_memcmp_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
             (restrict (Dimg ivs) m) xs ys).
    + apply (proj2 (bytes_at_restrict asegs (Dimg ivs) m (bv_unsigned a0) xs ltac:(dcov CV0))). exact HX.
    + apply (proj2 (bytes_at_restrict asegs (Dimg ivs) m (bv_unsigned a1) ys ltac:(dcov CV1))). exact HY.
    + exact LX.
    + exact LY.
  - cbn beta. intros ms1 [POST AGREE].
    ddestruct POST as (a0' & a1' & a2' & x13 & x14 & r & E & Hr & Hrr & Hiff).
    destruct (rms_eq_MS (Dimg ivs) ms1 _ _ _ _ _ _ _ E) as (M1 & -> & RM).
    cbn [ms_mem MS] in AGREE.
    assert (EM : M1 = m).
    { apply functional_extensionality. intros a. destruct (Dimg ivs a) eqn:Da; [|apply AGREE; exact Da].
      rewrite <- (restrict_in (Dimg ivs) M1 a Da), RM. apply restrict_in. exact Da. }
    subst M1. dexists a0', a1', a2', x13, x14, r. split; [reflexivity|]. split; [exact Hr|]. split; [exact Hrr|exact Hiff].
Qed.
End WithLayout.
