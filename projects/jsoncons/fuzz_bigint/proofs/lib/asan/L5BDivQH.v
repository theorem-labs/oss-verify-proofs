(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5BDivQP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADQH.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADIVQP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

Lemma r14 : (14%bv : bv 5) = reg 14. Proof. apply bv_eq. reflexivity. Qed.
Definition OPDIVQ : Z := 0x94b00.
Definition Q_FRAME : Z := 96.
Definition AMEMSET : Z := 0x5e7f0.

(* [comment removed for export] *)
Definition qown (E F : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop := L5DSA.diveq_frame R M E F.
Definition qocell (E : Z) (a : Z) : Prop := E - 88 <= a < E.
Lemma qown_agree E F R M1 M1' : 4096 <= E - 96 -> E <= 2 ^ 47 ->
  qown E F R M1 -> (forall a, qocell E a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> qown E F R M1'.
Proof.
  intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) AG. unfold qown, L5DSA.diveq_frame, qocell in *.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

(* [comment removed for export] *)
Definition shr8 (Mk : word -> option byte) (F off n v : Z) : Prop := forall j, 0 <= j < n -> L5.u8_at RSEGS Mk (F / 8 + SB + off + j) v.
Definition qsh (Mk : word -> option byte) (F vT : Z) : Prop := shr8 Mk F 0 4 241 /\ shr8 Mk F 4 4 vT /\ shr8 Mk F 8 4 243 /\ shr8 Mk F 12 4 0.

(* [comment removed for export] *)
Definition rinvQ (R0 : bvmap 5 word) (E F X dv : Z) (Rc : bvmap 5 word) : Prop :=
  getr Rc (reg 2) = Z_to_bv 64 (E - 96) /\ getr Rc (reg 8) = Z_to_bv 64 E /\ getr Rc (reg 9) = Z_to_bv 64 (E - 96) /\
  getr Rc (reg 3) = getr R0 (reg 3) /\ getr Rc (reg 4) = getr R0 (reg 4) /\
  getr Rc (reg 18) = Z_to_bv 64 F /\ getr Rc (reg 19) = Z_to_bv 64 X /\ getr Rc (reg 20) = Z_to_bv 64 dv /\ getr Rc (reg 21) = Z_to_bv 64 (F + 32) /\
  getr Rc (reg 22) = Z_to_bv 64 (F / 8 + SB) /\ getr Rc (reg 23) = Z_to_bv 64 F /\ getr Rc (reg 24) = Z_to_bv 64 1172321806 /\
  getr Rc (reg 25) = getr R0 (reg 25) /\ getr Rc (reg 26) = getr R0 (reg 26) /\ getr Rc (reg 27) = getr R0 (reg 27).

Definition QIDX : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma rinvQ_keep (R : bvmap 5 word) (E F X dv : Z) Ra Rb : rinvQ R E F X dv Ra -> (forall k, In k QIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinvQ R E F X dv Rb.
Proof.
  intros (X2 & X8 & X9 & X3 & X4 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27) Kp. unfold rinvQ.
  rewrite (Kp 2%nat), (Kp 8%nat), (Kp 9%nat), (Kp 3%nat), (Kp 4%nat), (Kp 18%nat), (Kp 19%nat), (Kp 20%nat), (Kp 21%nat), (Kp 22%nat), (Kp 23%nat), (Kp 24%nat), (Kp 25%nat), (Kp 26%nat), (Kp 27%nat)
    by (unfold QIDX; cbn [In]; tauto). repeat split; assumption.
Qed.
Lemma rinvQ_ks (R : bvmap 5 word) (E F X dv : Z) Ra Rb (KS : list nat) : rinvQ R E F X dv Ra -> (forall x, In x KS -> getr Rb (reg x) = getr Ra (reg x)) ->
  forallb (fun i => existsb (Nat.eqb i) KS) QIDX = true -> rinvQ R E F X dv Rb.
Proof. intros RI Kp HB. apply (rinvQ_keep R E F X dv Ra Rb RI). intros k Hk. apply Kp. exact (L5K.incl_b QIDX KS HB k Hk). Qed.
Lemma rinvQ_pres (R : bvmap 5 word) (E F X dv : Z) Ra Rb : rinvQ R E F X dv Ra -> regs_preserved Ra Rb -> rinvQ R E F X dv Rb.
Proof. intros RI RP. apply (rinvQ_keep R E F X dv Ra Rb RI). intros k Hk. apply (cs_of_preserved Ra Rb k RP). revert Hk. apply (L5K.incl_b QIDX); vm_compute; reflexivity. Qed.


Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Local Abbreviation statics_vis := (L5ADH.statics_vis L ar C HI LY HIok).

(* [comment removed for export] *)
Lemma dq_entry SCRD (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
      (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (X dv E r : Z) :
  96 + 512 <= SCRD ->
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
  getr R 10%bv = Z_to_bv 64 X -> getr R 11%bv = Z_to_bv 64 dv -> 0 <= X < 2 ^ 64 -> 0 <= dv < 2 ^ 64 ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E SCRD ->
  ffrk 1 FF LK 5 -> ffrs FF E ->
  (forall (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (fx3 : FPState) R3 M3 model3,
      L5AFK.gctx L ar HI LB FF LK A E SCRD (E - 96) (E - 96) E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr ->
      U R 1 = r -> getr R (reg 2) = Z_to_bv 64 E -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
      L5AFK.binv L ar HI M model LB FF LK A E SCRD (E - 96) (qown E F R) F 1 [] [] M3 model3 LK2 cr A ->
      rinvQ R E F X dv R3 -> getr R3 (reg 1) = Z_to_bv 64 0x94c20 ->
      getr R3 (reg 10) = Z_to_bv 64 (F + 40) /\ getr R3 (reg 11) = Z_to_bv 64 0 /\ getr R3 (reg 12) = Z_to_bv 64 24 ->
      qsh M3 F 0 -> shadow_zero M3 (F + 32) 4 -> L5.u8_at RSEGS M3 (F + 32) 0 -> L5.u64_at RSEGS M3 F 1102416563 ->
      srealizes RSEGS SCFG (cfg (fx:=fx3) R3 AMEMSET M3 model3) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R OPDIVQ M model) K.
Proof.
  intros HSCR HH AM HK G10 G11 XR DVR G1 RA G2 A32 G4 STK FFR1 FFRS KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (ER : 140735332487680 <= E <= 140737488355328 /\ 0 <= E < 2 ^ 64) by (clear - SLO SHI SPT HSCR; lia). destruct ER as (ER & ERG).
  assert (EA : aligned E 32) by exact A32.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (WSv : L5.writable RSEGS MV (E - 96) 96).
  { apply (proj2 (writable_vis H M (E - 96) 96 (VIS (E - 96) 96 ltac:(clear - SLO HSCR; lia) ltac:(clear - ER; lia)) ltac:(clear - ER; lia) ltac:(clear - ER; lia))).
    eapply (astk_writable ar M E). exact STK. clear - HSCR; lia. clear; lia. clear; lia. }
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [Y _]. clear - Y; lia. }
  assert (G2' : getr R (reg 2) = Z_to_bv 64 E) by (rewrite <- r2; exact G2).
  assert (G10' : getr R (reg 10) = Z_to_bv 64 X) by (rewrite <- r10; exact G10).
  assert (G11' : getr R (reg 11) = Z_to_bv 64 dv) by (rewrite <- r11; exact G11).
  (* [comment removed for export] *)
  pose proof (vdeP0_conc fx R MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => dv | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR19 & aR20 & aR22 & aCS)).
  assert (aR3 : getr R1 (reg 3) = getr R (reg 3)) by (apply aKS; inl). assert (aR4 : getr R1 (reg 4) = getr R (reg 4)) by (apply aKS; inl).
  assert (aR25 : getr R1 (reg 25) = getr R (reg 25)) by (apply aKS; inl). assert (aR26 : getr R1 (reg 26) = getr R (reg 26)) by (apply aKS; inl).
  assert (aR27 : getr R1 (reg 27) = getr R (reg 27)) by (apply aKS; inl).
  destruct aCS as (C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C96).
  set (W1 := fun a => E - 96 <= a < E).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R OPDIVQ R1 SM1 M1v W1 K HH AM aMS MG1).
  { intros a Ha Hna. apply aFZ. exact Ha. all: clear - Hna; subst W1; cbn beta in Hna; lia. }
  { intros a Ha Wa. subst W1; cbn beta in Wa. split. apply stack_client. clear - Wa SLO SHI SPT HSCR; lia. clear; lia. clear - Wa ER; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  (* [comment removed for export] *)
  pose proof (aio_stack_malloc _ _ _ _ _ HIok 1 ltac:(left; reflexivity)) as SM. unfold astack_malloc_spec in SM.
  rewrite (aly_segs L C LY), (aly_sm1 L C LY), (aly_scr_sm L C LY) in SM.
  assert (U2 : bv_unsigned (getr R1 2%bv) = E - 96). { rewrite r2, aR2. apply L5.unsigned_lit. clear - ER; lia. }
  assert (SA16 : (E - 96) mod 16 = 0 /\ (E - 96) mod 32 = 0). { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  eapply (SM fx1 R1 M1 model1 LB FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
  - rewrite r4, aR4, <- r4. exact G4.
  - rewrite r1, aR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
  - rewrite U2. apply (astack_ok_of_astk L ar C LY M M1 E SCRD 96 512 STK MGM1). clear; lia. clear; lia. clear - HSCR; lia. exact (proj1 SA16).
  - apply (ffrk_room 1 FF LK 5 FFR1). clear; lia.
  - intros f Hf. rewrite U2. specialize (FFRS f Hf). clear - FFRS. lia.
  - exact HK.
  - intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
    rewrite U2 in FLNC. rewrite U2 in PRES2. rewrite U2 in HH2. rewrite ?U2. rewrite r1, aR1.
    pose proof (sm_facts L ar C HI LY HIok LB FF LK2 cr A M2 model2 F 1 (E - 96 + 32) fl HH2 ltac:(left; reflexivity) FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
      as (FR & FFL & F32 & F8 & _ & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
    change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
    assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
    assert (ASTK2 : astk ar M2 E SCRD).
    { apply (astk_after_rt L ar C HI HIok LB FF LK cr A M M1 M2 _ E _ (E - 96) 512 HH STK MGM1 PRES2). clear - HSCR; lia. clear; lia. clear - HSCR; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB _ LK2 cr A M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & _).
    pose proof (statics_vis LB _ LK2 cr A M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    set (H2 := ahid A model2) in *. set (MV2 := mrestrict H2 M2) in *.
    assert (SVIS : forall a, E - 96 <= a < E -> H (Z_to_bv 64 a) = false).
    { intros a Ha. replace a with ((E - 96) + (a - (E - 96))) by (clear; lia). apply (VIS (E - 96) 96). clear - SLO HSCR; lia. clear - ER; lia. clear - Ha; lia. }
    assert (AG2 : forall a, E - 96 <= a < E -> MV2 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ha. unfold MV2. rewrite (mrestrict_visible H2 M2). 2:{ replace a with ((E - 96) + (a - (E - 96))) by (clear; lia). apply (VIS2 (E - 96) 96). clear - SLO HSCR; lia. clear - ER; lia. clear - Ha; lia. }
      rewrite (proj1 PRES2 a). 2:{ clear - Ha ER; lia. } 2:{ apply stack_client. clear - Ha SLO SHI SPT HSCR; lia. clear - Ha; lia. }
      rewrite <- VIS1. symmetry. apply mrestrict_visible. apply SVIS. exact Ha. }
    assert (W96b : L5.writable RSEGS MV2 (E - 96) 96).
    { eapply (L5C.writable_agree RSEGS M1v MV2). intros j Hj. apply AG2. clear - Hj; lia. clear - ER; lia. clear - ER; lia. eapply L5.writable_grows. exact MG1. exact WSv. }
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 1 _ fl E 0 (E - 96) 96 HH2 SPT ltac:(left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC
                  ltac:(intros i Hi; apply stack_client; clear - Hi SLO SHI SPT HSCR; lia) ltac:(clear; lia)) as (SF & SFSH & SFL).
    change (ff_bytes 1) with 128 in SF. change (ff_bytes 1 / 8) with 16 in SFSH.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (FQ : (F + 128 - 1) / 8 = F / 8 + 16 - 1 /\ F mod 8 = 0 /\ (F + 32) / 8 = F / 8 + 4 /\ (F + 32) mod 8 = 0) by (clear - F8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (NCF : forall a, (F <= a < F + 128 \/ S F <= a <= S (F + 128 - 1)) -> ~ aclient L ar LB FF E SCRD a).
    { intros a Ha. apply (fresh_frame_not_client L ar C HI LY HIok LB FF LK cr A M _ E SCRD F 128 a HH SPT).
      clear - FR; lia. exact FCEIL. exact FAPP. exact (proj1 (proj2 FQ)). clear; lia. reflexivity.
      eapply fframes_apart_incl. exact FAPART. intros g0 Hg; apply in_or_app; left; exact Hg. exact FBLK. exact Ha. }
    assert (NCS : forall a, E - 96 <= a < E -> ~ aclient L ar LB FF E SCRD a).
    { intros a Xa Hc. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ E SCRD a HH SPT Hc) as [Y|Y]. clear - Xa Y HSCR; lia. clear - Xa Y SLO HSCR; lia. }
    assert (EK2 : ek L ar LB FF E SCRD [] M M2).
    { eapply ek_trans. { apply (ek_piece L ar LB FF E SCRD [] M M1 W1 FRM1). intros a Ha Hc _ Xa. subst W1; cbn beta in Xa. apply (NCS a). exact Xa. exact Hc. }
      apply (ek_rt L ar LB FF [] E SCRD (E - 96) 512 [] M1 M2 PRES2). clear - HSCR; lia. clear; lia. }
    assert (DK2 : dk L ar LB FF E SCRD M M2).
    { eapply dk_trans. apply dk_grows. exact MGM1. apply (dk_rt L ar LB FF [] E SCRD (E - 96) 512 M1 M2 PRES2). clear - HSCR; lia. clear; lia. }
    (* [comment removed for export] *)
    assert (FRG : 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 4096 <= F <= 140737488355200 /\ 4096 <= fl <= 140737488355327) by (clear - FR FLR; lia). destruct FRG as (FRG & FLRG & FRP & FLRP).
    assert (ALF : aligned F 32) by exact F32.
    assert (SFA : E - 96 + 96 <= F \/ F + 128 <= E - 96) by (clear - FCEIL SLO HSCR; lia).
    assert (SFLA : E - 96 + 96 <= fl \/ fl + 1 <= E - 96) by (clear - FLR SLO HSCR; lia).
    assert (FLCv' : L5.u64_at RSEGS MV2 (F + 120) fl). { replace (F + 120) with (F + 128 - 8) by (clear; lia). exact FLCv. }
    assert (RC2 : forall j, In j [8; 9; 19; 20; 22; 25; 26; 27; 3; 4]%nat -> getr R2 (reg j) = getr R1 (reg j)). { intros j Hj. apply (cs_of_preserved R1 R2 j RP2). revert Hj. apply (L5K.incl_b [8; 9; 19; 20; 22; 25; 26; 27; 3; 4]%nat); vm_compute; reflexivity. }
    pose proof (vdeP1_conc fx1 R2 MV2 (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => dv | 40%nat => F | 41%nat => fl | 58%nat => U R2 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r10; exact B10) | (rewrite (RC2 _) by inl; sc) | (rewrite (cs_of_preserved R1 R2 _ RP2) by inl; sc) ]).
    destruct P as (fx3 & R3 & M3v & MG3 & bFR & bFZ & (bMS & bKS & bR1 & bR10 & bR11 & bR12 & bR13 & bR18 & bR21 & bR22 & bR23 & bR24 & BQ)).
    set (W3 := fun a => E - 88 <= a < E - 80 \/ (F <= a < F + 24 \/ F + 32 <= a < F + 33) \/ F / 8 + SB <= a < F / 8 + SB + 12).
    apply (apiece L ar C HI LY HIok LB _ LK2 cr A M2 model2 fx1 fx3 R2 0x94b68 R3 AMEMSET M3v W3 K HH2 (conj Hh2 MI2) bMS MG3).
    { intros a Ha Hna. apply bFZ. exact Ha. all: clear - Hna; subst W3; cbn beta in Hna; unfold SB in *; lia. }
    { intros a Ha Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
      - split. apply stack_client. clear - Wa SLO SHI SPT HSCR; lia. clear; lia. clear - Wa ER; lia.
      - split. apply (fframe_client L ar LB _ 0 0 F 1 (E - 96 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Wa; lia. clear - Wa FR; lia.
      - split. apply (fframe_shadow_client L ar LB _ 0 0 F 1 (E - 96 + 32)). left; reflexivity. change (ff_bytes 1) with 128. unfold in_shadow_of, S. rewrite (proj1 FQ). clear - Wa. unfold SB in *. lia.
        clear - Wa FR; unfold SB in Wa; lia. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    (* [comment removed for export] *)
    assert (G : L5AFK.gctx L ar HI LB FF LK A E SCRD (E - 96) (E - 96) E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr).
    { refine (L5AFK.GCTX L ar HI LB FF LK A E SCRD (E - 96) (E - 96) E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr
               ltac:(left; reflexivity) SPT SLO SHI _ _ _ FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC _ _ FBIG F32 FLA FLR FLBIG NCF _).
      - clear - SLO SHI SPT HSCR; lia.
      - intros a Ha. unfold qocell in Ha. clear - Ha; lia.
      - intros Ma Mb OW AG. apply (qown_agree E F R Ma Mb ltac:(clear - ER; lia) ltac:(clear - ER; lia) OW AG).
      - change (ff_bytes 1) with 128. clear - FR; lia.
      - change (ff_bytes 1) with 128. change (128 / 8) with 16. split. exact F8. split. exact (proj1 FQ). reflexivity.
      - exact NCS. }
    assert (SV2 : forall a, E - 96 <= a < E -> ahid A model2 (Z_to_bv 64 a) = false).
    { intros a Ha. replace a with ((E - 96) + (a - (E - 96))) by (clear; lia). apply (VIS2 (E - 96) 96). clear - SLO HSCR; lia. clear - ER; lia. clear - Ha; lia. }
    assert (XS3 : forall a v, E - 96 <= a -> a + 8 <= E -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
    { intros a v Ha Hb Hc. apply (proj1 (u64_at_vis (ahid A model2) M3 a v ltac:(intros i Hi; apply SV2; clear - Hi Ha Hb; lia) ltac:(clear - Ha ER; lia) ltac:(clear - Hb ER; lia))). rewrite VIS3. exact Hc. }
    destruct BQ as (bT & z7 & z6 & z5 & z4 & t11 & t10 & t9 & t8 & o3 & o2 & o1 & o0 & h16 & h8 & h0 & bOWN & d24 & d33 & z12).
    assert (KEEP3v : forall a, E - 80 <= a < E -> M3v (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ha. rewrite bFZ. apply AG2. clear - Ha; lia. clear - Ha ER; lia. clear - Ha; lia. clear - Ha SF; lia. clear - Ha SF; lia. clear - Ha SFSH; unfold SB in *; lia. }
    assert (OWN3 : qown E F R M3).
    { unfold qown, L5DSA.diveq_frame, L5DSA.U.
      assert (T : forall a v, E - 80 <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M3 a v).
      { intros a v Ha Hb Hc. apply XS3. clear - Ha; lia. exact Hb. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha ER; lia. 2: clear - Hb ER; lia. intros j Hj. apply KEEP3v. clear - Hj Ha Hb; lia. }
      split. apply T. clear; lia. clear; lia. exact C8. split. apply T. clear; lia. clear; lia. exact C16. split. apply T. clear; lia. clear; lia. exact C24.
      split. apply T. clear; lia. clear; lia. exact C32. split. apply T. clear; lia. clear; lia. exact C40. split. apply T. clear; lia. clear; lia. exact C48.
      split. apply T. clear; lia. clear; lia. exact C56. split. apply T. clear; lia. clear; lia. exact C64. split. apply T. clear; lia. clear; lia. exact C72.
      split. apply T. clear; lia. clear; lia. exact C80. apply XS3. clear; lia. clear; lia. exact bOWN. }
    assert (BI3 : L5AFK.binv L ar HI M model LB FF LK A E SCRD (E - 96) (qown E F R) F 1 [] [] M3 model3 LK2 cr A).
    { unfold L5AFK.binv. split. exact HH3. split. exact AM3.
      split. { eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT3. }
      split. apply incl_refl. split. exact LKI2. split. { eapply astk_grows. exact ASTK2. exact MGM3. }
      split. { eapply ek_trans. exact EK2. apply (ek_piece L ar LB FF E SCRD [] M2 M3 W3 FRM3). intros a Ha Hc _ Xa. subst W3; cbn beta in Xa. destruct Xa as [Xa|[Xa|Xa]].
               - apply (NCS a). clear - Xa; lia. exact Hc.
               - apply (NCF a). left; clear - Xa; lia. exact Hc.
               - apply (NCF a). right. unfold S. rewrite (proj1 FQ). clear - Xa. unfold SB in Xa |- *. lia. exact Hc. }
      split. { eapply dk_trans. exact DK2. apply dk_grows. exact MGM3. }
      split. exact OWN3.
      change (ff_bytes 1 / 8) with 16. eapply L5.defined_grows. exact MGM3. intros i Hi. unfold shadow_zero, byte_at, S in FSH. rewrite (FSH i Hi). discriminate. }
    assert (SHV3 : forall a, F / 8 + SB <= a < F / 8 + SB + 16 -> ahid A model2 (Z_to_bv 64 a) = false).
    { intros a Ha. replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply VSH. clear - Ha; lia. }
    assert (XB3 : forall a v, F / 8 + SB <= a < F / 8 + SB + 16 -> L5.u8_at RSEGS M3v a v -> L5.u8_at RSEGS M3 a v).
    { intros a v Ha Hc. apply (proj1 (u8_at_vis (ahid A model2) M3 a v ltac:(intros i Hi; apply SHV3; clear - Hi Ha; lia) ltac:(clear - Ha FR; unfold SB in *; lia) ltac:(clear - Ha FR F8; unfold SB in *; lia))). rewrite VIS3. exact Hc. }
    assert (QSH3 : qsh M3 F 0).
    { unfold qsh, shr8. repeat split; intros j Hj; (apply XB3; [clear - Hj; lia|]);
        first [ (assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia); unfold SB; destruct J as [J|[J|[J|J]]]; subst j; gmem)
              | (pose proof (z12 j Hj) as B0; unfold L5.u8_at; cbn [rdn]; unfold SB;
                 replace (F / 8 + 2147450880 + 12 + j) with (F / 8 + 2147450892 + j) by (clear; lia); rewrite B0; reflexivity) ]. }
    assert (SZT3 : shadow_zero M3 (F + 32) 4).
    { intros j Hj. unfold byte_at, S. rewrite (proj1 (proj2 (proj2 FQ))). destruct QSH3 as (_ & Z4 & _). specialize (Z4 j Hj).
      replace (F / 8 + 4 + SB + j) with (F / 8 + SB + 4 + j) by (clear; lia). apply (byte_of_u8 M3 _ 0 Z4). right. clear - Hj FR F8; unfold SB; lia. clear - Hj FR F8; unfold SB; lia. }
    assert (FV3 : forall a, F <= a < F + 128 -> ahid A model2 (Z_to_bv 64 a) = false).
    { intros a Ha. replace a with (F + (a - F)) by (clear; lia). apply VF. clear - Ha; lia. }
    apply (KONT F fl LK2 M2 model2 fx3 R3 M3 model3 G UR1 G2' ltac:(rewrite <- r4; exact G4) BI3).
    + unfold rinvQ. rewrite ?(bKS 2%nat), ?(bKS 8%nat), ?(bKS 9%nat), ?(bKS 3%nat), ?(bKS 4%nat), ?(bKS 19%nat), ?(bKS 20%nat), ?(bKS 25%nat), ?(bKS 26%nat), ?(bKS 27%nat) by inl.
      rewrite ?(RC2 8%nat), ?(RC2 9%nat), ?(RC2 3%nat), ?(RC2 4%nat), ?(RC2 19%nat), ?(RC2 20%nat), ?(RC2 25%nat), ?(RC2 26%nat), ?(RC2 27%nat) by inl.
      rewrite (cs_of_preserved R1 R2 2 RP2) by inl.
      repeat split; assumption.
    + exact bR1.
    + split. exact bR10. split. exact bR11. exact bR12.
    + exact QSH3.
    + exact SZT3.
    + apply (proj1 (u8_at_vis (ahid A model2) M3 (F + 32) 0 ltac:(intros i Hi; apply FV3; clear - Hi; lia) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). rewrite VIS3. exact bT.
    + apply (proj1 (u64_at_vis (ahid A model2) M3 F _ ltac:(intros i Hi; apply FV3; clear - Hi; lia) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). rewrite VIS3. exact h0.
Qed.

End WithIface.

End SCFG_1.
End L5ADQH.
