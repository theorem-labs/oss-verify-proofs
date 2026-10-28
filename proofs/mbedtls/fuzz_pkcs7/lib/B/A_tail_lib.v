(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt ZBridge Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame BBFrame LibTail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import Restrict RestrictLib RestrictRun SymDriveA SymDriveAX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_base A_exit_lib A_oomtail A_printf1 A_refused A_tailkit_defs A_splice A_rip A_amem_lib A_icpt_read A_icpt_strnlen.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_tail_lib () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.env"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sentry"; "AGR"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibA.Restrict.restrict"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.mem_denot"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.true"; "outzone"; "RocqVerifyHarness.AgentSubmission.B.A_printf1.log_out"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.B.ARestrict.AIMG_HI"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.A_exit_lib.mapped"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.kentry_ok"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KZero"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition outzone (lo hi : Z) (x : word) : Prop :=
  ~ (lo <= bv_unsigned x < hi) /\ ~ (0x0fa488 <= bv_unsigned x < 0x0fa570).

Definition AGR (M : mem) (lo hi : Z) (Mk : mem) : Prop :=
  (forall x : word, outzone lo hi x -> Mk x = M x) /\ mem_grows M Mk.

Lemma AGR_refl : forall M lo hi, AGR M lo hi M.
Proof. intros. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

Lemma AGR_trans : forall M lo hi M1 M2, AGR M lo hi M1 -> AGR M1 lo hi M2 -> AGR M lo hi M2.
Proof.
  intros M lo hi M1 M2 [A1 G1] [A2 G2]. split.
  - intros x Hx. rewrite (A2 x Hx). apply A1. exact Hx.
  - intros x Hx. apply G2. apply G1. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma AGR_block : ltac2:(CDefT.buildp (gd_tbl_A_tail_lib ()) "PD,P,(0.&40.)$1.PE,$2.PM,P,(0.&40.)(3.(0.&8.))Plo,$4.Phi,$4.PMk,P,(0.&40.)(3.(0.&8.))PM',P,(0.&40.)(3.(0.&8.))Plog,(5.$6.)P,(7.R6.R5.R4.R3.)P,(8.P,(0.&40.)(3.(0.&8.))(9.R9.R3.)(:.R8.(9.R9.R4.)R2.))P,Pa,(0.&40.)P,(8.$1.A1.R;.R1.$;.)(8.(3.(0.&8.))A1.R6.R2.A1.R7.R2.)P,Px,(0.&40.)P,(8.$1.A1.R<.R1.$<.)P,(=.R:.R9.R2.)(>.R=.R3.R7.)(7.R:.R9.R8.R6.)")
(* [comment removed for export] *).
Proof.
  intros D E M lo hi Mk M' log [AG GR] EQM OUT LO. split.
  - intros x Hx. rewrite <- (AG x Hx). destruct (D x) eqn:Dx; [|apply OUT; exact Dx].
    rewrite <- (restrict_in D M' x Dx), EQM, (mem_denot_out E _ log x (LO x Dx Hx)). apply restrict_in. exact Dx.
  - eapply StoreOk.mem_grows_trans; [exact GR|]. eapply (grows_of_rst D); [exact EQM | exact OUT].
Qed.

(* [comment removed for export] *)
Lemma AGR_munch : ltac2:(CDefT.buildp (gd_tbl_A_tail_lib ()) "PW,(5.$?.)PM,P,(0.&40.)(3.(0.&8.))Plo,$4.Phi,$4.PMk,P,(0.&40.)(3.(0.&8.))PM',P,(0.&40.)(3.(0.&8.))P,(7.R5.R4.R3.R2.)P,(10.R7.R3.R2.)P,(11.$12.R4.R3.)P,Px,$4.P,(13.(14.R:.R1.))(15.(16.R9.R2.)(17.R2.R8.))P,(16.$18.R8.)(7.R:.R9.R8.R6.)")
(* [comment removed for export] *).
Proof.
  intros W M lo hi Mk M' [AG GR] MU WM IN LO. split.
  - intros x Hx. rewrite (MU x); [apply AG; exact Hx|].
    destruct (outside_dec W (bv_unsigned x)) as [O|NO]; [exact O|]. exfalso. destruct Hx as [H1 _]. apply H1. apply IN. exact NO.
  - eapply StoreOk.mem_grows_trans; [exact GR|]. eapply grows_of_munch_high; [exact MU | exact WM |]. intros x Hx. specialize (IN x Hx). lia.
Qed.

Section Zone.
  Variable M : mem.
  Variables lo hi : Z.
  Hypothesis LOlo : 0x10007fff7fff < lo.     (* [comment removed for export] *)
  Hypothesis HI : hi <= 2^64.
  Hypothesis MI : mem_inv asegs M.

  #[using="LOlo"] Lemma AGR_rdn : ltac2:(CDefT.buildp (gd_tbl_A_tail_lib ()) "PMk,P,(0.&40.)(3.(0.&8.))Pa,$4.Pn,$19.Pbs,(5.(0.&8.))P,(7.VM,Vlo,Vhi,R4.)P,(16.=R4.)P,(16.(1:.R5.(1;.R4.))(1<.+2.+40.))P,(1=.(16.(1:.R6.(1;.R5.))Vlo,)(16.Vhi,R6.))P,(1=.(16.(1:.R7.(1;.R6.))+?:488.)(16.+?:570.R7.))P,(8.(3.(5.(0.&8.)))(1>.$12.VM,(1?.&40.R8.)R7.)(20.(5.(0.&8.))R6.))(8.(3.(5.(0.&8.)))(1>.$12.R:.(1?.&40.R9.)R8.)(20.(5.(0.&8.))R7.))")
(* [comment removed for export] *).
  Proof.
    intros Mk a n bs [AG _] Ha Hn D1 D2 H. rewrite <- H. apply rdn_agree. intros j Hj. rewrite (unsigned_lit a) by lia.
    apply AG. unfold outzone. rewrite unsigned_lit by lia. lia.
  Qed.

  #[using="Type"] Lemma AGR_byte : ltac2:(CDefT.buildp (gd_tbl_A_tail_lib ()) "PMk,P,(0.&40.)(3.(0.&8.))Pa,$4.Pb,(3.(0.&8.))P,(7.VM,Vlo,Vhi,R3.)P,(15.(16.=R3.)(17.R3.(1<.+2.+40.)))P,(1=.(17.R4.Vlo,)(16.Vhi,R4.))P,(1=.(17.R5.+?:488.)(16.+?:570.R5.))P,(8.(3.(0.&8.))A1.VM,(1?.&40.R6.)R5.)(8.(3.(0.&8.))A1.R8.(1?.&40.R7.)R6.)")
(* [comment removed for export] *).
  Proof. intros Mk a b [AG _] Ha D1 D2 H. rewrite <- H. apply AG. unfold outzone. rewrite unsigned_lit by lia. lia. Qed.

  #[using="Type"] Lemma AGR_bytes_at : ltac2:(CDefT.buildp (gd_tbl_A_tail_lib ()) "PMk,P,(0.&40.)(3.(0.&8.))Pa,$4.Pbs,(5.(0.&8.))P,(7.VM,Vlo,Vhi,R3.)P,(1=.(16.(1:.R3.(1;.(21.(0.&8.)R2.)))Vlo,)(16.Vhi,R3.))P,(1=.(16.(1:.R4.(1;.(21.(0.&8.)R3.)))+?:488.)(16.+?:570.R4.))P,(22.$12.VM,R5.R4.)(22.$12.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros Mk a bs [AG _] D1 D2 H. eapply (bytes_at_transport asegs [(lo, hi); (0x0fa488, 0x0fa570)]); [exact H | | cbn; lia].
    intros x Hx. apply AG. cbn in Hx. unfold outzone. lia.
  Qed.

  #[using="Type"] Lemma AGR_munch2 : forall Mk, AGR M lo hi Mk -> munch [(lo, hi); (0x0fa488, 0x0fa570)] M Mk.
  Proof. intros Mk [AG _] x Hx. apply AG. cbn in Hx. unfold outzone. lia. Qed.

  
  (* [comment removed for export] *)
  #[using="LOlo MI"] Lemma AGR_mem_inv : ltac2:(CDefT.buildp (gd_tbl_A_tail_lib ()) "PMk,P,(0.&40.)(3.(0.&8.))P,(7.VM,Vlo,Vhi,R1.)P,Pa,$4.P,(15.(16.+?:488.R1.)(17.R1.+?:578.))(8.(3.(0.&8.))A1.VM,(1?.&40.R2.)(23.(0.&8.)))(24.$12.R3.)")
(* [comment removed for export] *).
  Proof.
    intros Mk [AG GR] ERR a b Hb. pose proof (u64_range a).
    destruct (M a) as [bb0|] eqn:E0; [exact (MI a bb0 E0)|].
    destruct (Z_lt_le_dec (bv_unsigned a) lo).
    - destruct (Z_lt_le_dec (bv_unsigned a) 0x0fa488); [| destruct (Z_lt_le_dec (bv_unsigned a) 0x0fa570)].
      1,3: exfalso; rewrite AG in Hb by (unfold outzone; lia); congruence.
      rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
      eapply wview_not_ro with (m := M).
      + pose proof (store_ok_data M (Z_to_bv 64 (bv_unsigned a)) 1 ltac:(rewrite u_small by lia; lia) ltac:(rewrite u_small by lia; cbn; lia)) as SO.
        pose proof (store_ok_wview asegs M _ 1 0 SO ltac:(lia)) as WV. rewrite u_small in WV by lia. rewrite Z.add_0_r in WV. exact WV.
      + unfold wa. rewrite Z_to_bv_bv_unsigned. exact E0.
    - destruct (Z_lt_le_dec (bv_unsigned a) hi).
      + rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)). apply ro_addr_high. unfold AIMG_HI. lia.
      + exfalso. rewrite AG in Hb by (unfold outzone; lia). congruence.
  Qed.

  #[using="Type"] Lemma AGR_mapped : forall Mk a b, AGR M lo hi Mk -> mapped M a b -> mapped Mk a b.
  Proof.
    intros Mk a b [_ GR] MP x Hx. destruct (MP x Hx) as [v Hv].
    destruct (Mk (wa x)) as [v'|] eqn:E; [exists v'; reflexivity|]. exfalso. apply (GR (wa x)); [congruence | exact E].
  Qed.
End Zone.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u8arr_of_mapped : ltac2:(CDefT.buildp (gd_tbl_A_tail_lib ()) "Pm,P,(0.&40.)(3.(0.&8.))PA,$4.Pn,$19.P,(25.R3.R2.(1:.R2.(1;.R1.)))P,(16.=R3.)P,(16.(1:.R4.(1;.R3.))(1<.+2.+40.))(26.(5.(0.&8.))Lds,(5.(0.&8.))(15.(8.$19.(21.(0.&8.)R1.)R5.)(27.$12.R7.R6.R1.)))")
(* [comment removed for export] *).
Proof.
  intros m A n MP A0 AH.
  pose proof (mapped_stk m A (A + Z.of_nat n) MP A0 AH) as ST.
  destruct (stk_carve asegs m A (A + Z.of_nat n) n ST ltac:(lia)) as [_ (junk & RW)].
  replace (A + Z.of_nat n - Z.of_nat n) with A in RW by lia.
  pose proof RW as RW'. destruct RW' as [[WF _] _]. cbn in WF. destruct WF as [LEN _].
  exists junk. split; [exact LEN | apply (u8arr_of_rw_cells asegs m A n); exact RW].
Qed.

Lemma skipn_repeat' : forall {A} (x : A) i n, skipn i (repeat x n) = repeat x (n - i).
Proof. intros A x i. induction i as [|i IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.

(* [comment removed for export] *)
Lemma kentry_kzero_high : ltac2:(CDefT.buildp (gd_tbl_A_tail_lib ()) "PE,$2.PM,P,(0.&40.)(3.(0.&8.))Pub,$28.Puk,$4.Pn,$4.PA,$4.P,(8.$4.(1:.(29.&40.(2:.R6.R4.))R3.)R1.)P,(16.=R2.)P,(16.=R4.)P,(17.(1:.R4.R5.)(1<.+2.+40.))P,(16.$18.R5.)P,(27.$12.R:.R6.(2;.(0.&8.)(1?.&8.=)(2<.R7.)))(2=.$12.R<.R;.(2>.(2?.R:.R9.)(30.R8.)))")
(* [comment removed for export] *).
Proof.
  intros E M ub uk n A HA A0 N0 AH HI [BY _]. unfold AIMG_HI in HI.
  cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite (unsigned_lit n) by lia. rewrite HA.
  split; [lia|]. intros i Hi.
  pose proof (bytes_at_rdn asegs M A _ (Z.to_nat i) 1 BY ltac:(rewrite repeat_length; lia)) as RD.
  rewrite Z2Nat.id in RD by lia.
  rewrite skipn_repeat' in RD. replace (Z.to_nat n - Z.to_nat i)%nat with (S (Z.to_nat n - Z.to_nat i - 1))%nat in RD by lia. cbn [repeat firstn] in RD.
  unfold wa in RD. rewrite rdn_unfold in RD. unfold mrd in RD.
  change (rdn asegs M (Z_to_bv 64 (A + i) + 1) 0) with (Some (@nil byte)) in RD.
  destruct (M (Z_to_bv 64 (A + i))) as [b|] eqn:Mb.
  - injection RD. intros ->. reflexivity.
  - exfalso. pose proof (seg_rom_high (A + i) ltac:(unfold AIMG_HI; lia)) as SR. unfold wa in SR. rewrite SR in RD. discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma aobj_of_zero_range : ltac2:(CDefT.buildp (gd_tbl_A_tail_lib ()) "PAL,$31.PCS,P,$4.SpPm,Px,(0.&40.)(3.(0.&8.))PA,$4.Pn,$4.P,(32.R5.R4.)P,(8.$4.(33.R6.)+7???8000.)P,(34.R6.R4.R3.)P,(16.=R5.)P,(16.=R5.)P,Ps,$4.P,(15.(16.(1:.+7???8000.(35.R8.+8.))R1.)(16.R1.(1:.+7???8000.(35.(36.(1:.R8.R7.)+1.)+8.))))(8.(3.(0.&8.))A1.R:.(1?.&40.R2.)(20.(0.&8.)(1?.&8.=)))(37.$12.R;.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros AL CS m A n OK SB CR A0 N0 ZS. split; [exact CR|].
  intros a Ha. exists (Z_to_bv 8 0). split; [| left; reflexivity].
  unfold shadow_of. rewrite SB.
  assert (R : 0x7fff8000 + A / 8 <= 0x7fff8000 + a / 8 <= 0x7fff8000 + (A + n - 1) / 8).
  { split; apply Z.add_le_mono_l; apply Z.div_le_mono; lia. }
  destruct (OK) as (C1 & _). ddestruct (C1 a (CR a Ha)) as (Q0 & Q1 & Q2 & _).
  apply (bytes_at_of_read1 asegs); [lia | unfold shadow_of in Q1; rewrite SB in Q1; lia | ].
  rewrite ov_rdn. unfold wa. rewrite rdn_unfold. unfold mrd. rewrite (ZS _ R). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_block : ltac2:(CDefT.buildp (gd_tbl_A_tail_lib ()) "PD,P,(0.&40.)$1.PE,$2.PMk,P,(0.&40.)(3.(0.&8.))PM1,P,(0.&40.)(3.(0.&8.))Plog,(5.$6.)Pa,$4.Pbs,(5.(0.&8.))P,(22.$12.R5.R2.R1.)P,(8.P,(0.&40.)(3.(0.&8.))(9.R8.R5.)(:.R7.(9.R8.R6.)R4.))P,Pz,$4.P,(15.(16.R5.R1.)(17.R1.(1:.R5.(1;.(21.(0.&8.)R4.)))))(15.(8.$1.A1.R;.(1?.&40.R2.)$<.)(>.R:.(1?.&40.R2.)R7.))(22.$12.R7.R5.R4.)")
(* [comment removed for export] *).
Proof.
  (intros D E Mk M1 log a bs dd_H; ddestruct dd_H as (B0 & B1 & B); intros EQM H). split; [exact B0|]. split; [exact B1|].
  intros i Hi. rewrite <- (B i Hi). unfold mrd, wa. destruct (H (a + Z.of_nat i)%Z ltac:(lia)) as [Dz Lz].
  rewrite <- (restrict_in D M1 _ Dz), EQM, (mem_denot_out E _ log _ Lz), (restrict_in D Mk _ Dz). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rtc_cell' RTC a n v := exact (asan_rtc_cell _ a n v RTC ltac:(unfold rtc_cells; cbn [In]; repeat (first [left; reflexivity | right]))).

(* [comment removed for export] *)
Lemma rtc_rd_constsT : forall m, asan_rtc m -> rd_consts m.
Proof.
  intros m RTC. split; [rtc_cell' RTC 0x10a6d8 1%nat 1 | rtc_cell' RTC 0x0f7ba0 8%nat 0x0f00c4 |].
  split; [ rtc_cell' RTC 0x0f5e50 8%nat 0x1099f8 | rtc_cell' RTC 0x1099f8 8%nat 0x7fff8000 | rtc_cell' RTC 0x0f5e58 8%nat 0x10a6e8
         | rtc_cell' RTC 0x0f5e60 8%nat 0x10a6f0 | rtc_cell' RTC 0x0f5e68 8%nat 0x10a6e0 | rtc_cell' RTC 0x10a6e8 8%nat 0
         | rtc_cell' RTC 0x10a6f0 8%nat 0 | rtc_cell' RTC 0x10a6e0 8%nat 0x7fffffffffff ].
Qed.

Lemma rtc_rip_consts : forall m, asan_rtc m -> rip_consts m.
Proof. intros m RTC. exact (rc_rip _ (rtc_rd_constsT m RTC)). Qed.

Lemma rtc_sn_consts : forall m, asan_rtc m -> sn_consts m.
Proof.
  intros m RTC. split; [rtc_cell' RTC 0x10a6d8 1%nat 1 | rtc_cell' RTC 0x0f7c78 8%nat 0x0eb24c | rtc_cell' RTC 0x0f7b90 8%nat 0x0ea8c4
                      | rtc_cell' RTC 0x0f5e40 8%nat 0x19b528 | rtc_cell' RTC 0x19b623 1%nat 1 | apply rtc_rip_consts; exact RTC].
Qed.

Lemma rtc_amem_consts : forall m, asan_rtc m -> amem_consts m.
Proof.
  intros m RTC. split; [rtc_cell' RTC 0x0f69b8 8%nat 0x10a6d9 | rtc_cell' RTC 0x10a6d9 1%nat 1 | rtc_cell' RTC 0x0f7cd0 8%nat 0x0eadc4
                      | rtc_cell' RTC 0x0f7cc8 8%nat 0x0ea9c0 | apply rtc_rip_consts; exact RTC].
Qed.
