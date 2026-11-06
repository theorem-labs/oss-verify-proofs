(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK L5DivKitA L5ADivP1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVH.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADIVP1.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

Lemma r14 : (14%bv : bv 5) = reg 14. Proof. apply bv_eq. reflexivity. Qed.
Definition DIVIDE : Z := 0x920ec.
Definition DIV_FRAME : Z := 352.

(* [comment removed for export] *)
Definition dfrk (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (E - 8) (U R 1) /\ L5.u64_at RSEGS M (E - 16) (U R 8) /\ L5.u64_at RSEGS M (E - 24) (U R 9) /\ L5.u64_at RSEGS M (E - 32) (U R 18) /\
  L5.u64_at RSEGS M (E - 40) (U R 19) /\ L5.u64_at RSEGS M (E - 48) (U R 20) /\ L5.u64_at RSEGS M (E - 56) (U R 21) /\ L5.u64_at RSEGS M (E - 64) (U R 22) /\
  L5.u64_at RSEGS M (E - 72) (U R 23) /\ L5.u64_at RSEGS M (E - 80) (U R 24) /\ L5.u64_at RSEGS M (E - 88) (U R 25) /\ L5.u64_at RSEGS M (E - 96) (U R 26) /\
  L5.u64_at RSEGS M (E - 104) (U R 27).
(* [comment removed for export] *)
Definition down (E F ro : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  dfrk E R M /\ L5.u64_at RSEGS M (E - 280) F /\ L5.u64_at RSEGS M (E - 256) ro /\ L5.u64_at RSEGS M (E - 240) (F / 8 + SB)
  /\ L5.u64_at RSEGS M (E - 200) SB /\ L5.u64_at RSEGS M (E - 192) F.
Definition docell (E : Z) (a : Z) : Prop :=
  E - 104 <= a < E \/ E - 280 <= a < E - 272 \/ E - 256 <= a < E - 248 \/ E - 240 <= a < E - 232 \/ E - 200 <= a < E - 184.
Lemma down_agree E F ro R M1 M1' : 4096 <= E - 352 -> E <= 2 ^ 47 ->
  down E F ro R M1 -> (forall a, docell E a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> down E F ro R M1'.
Proof.
  intros H0 H1 ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) & C14 & C15 & C16 & C17 & C18) AG. unfold down, dfrk, docell in *.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

(* [comment removed for export] *)
Definition shr8 (Mk : word -> option byte) (F off n v : Z) : Prop := forall j, 0 <= j < n -> L5.u8_at RSEGS Mk (F / 8 + SB + off + j) v.
Definition dsh (Mk : word -> option byte) (F vn v0 vq vr vh : Z) : Prop :=
  shr8 Mk F 0 4 241 /\ shr8 Mk F 4 4 0 /\ shr8 Mk F 8 4 242 /\ shr8 Mk F 12 4 vn /\ shr8 Mk F 16 4 242 /\ shr8 Mk F 20 4 v0 /\ shr8 Mk F 24 4 242 /\
  shr8 Mk F 28 4 vq /\ shr8 Mk F 32 4 242 /\ shr8 Mk F 36 4 vr /\ shr8 Mk F 40 4 242 /\ shr8 Mk F 44 4 vh /\ shr8 Mk F 48 4 243 /\ shr8 Mk F 52 12 0.

(* [comment removed for export] *)
Definition rinvD (R0 : bvmap 5 word) (E : Z) (Rc : bvmap 5 word) : Prop :=
  getr Rc (reg 2) = Z_to_bv 64 (E - 352) /\ getr Rc (reg 8) = Z_to_bv 64 E /\ getr Rc (reg 9) = Z_to_bv 64 (E - 352) /\
  getr Rc (reg 3) = getr R0 (reg 3) /\ getr Rc (reg 4) = getr R0 (reg 4).

Definition DIDX : list nat := [2; 3; 4; 8; 9]%nat.
Lemma rinvD_keep (R : bvmap 5 word) (E : Z) Ra Rb : rinvD R E Ra -> (forall k, In k DIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinvD R E Rb.
Proof.
  intros (X2 & X8 & X9 & X3 & X4) Kp. unfold rinvD.
  rewrite (Kp 2%nat), (Kp 8%nat), (Kp 9%nat), (Kp 3%nat), (Kp 4%nat) by (unfold DIDX; cbn [In]; tauto). repeat split; assumption.
Qed.
Lemma rinvD_ks (R : bvmap 5 word) (E : Z) Ra Rb (KS : list nat) : rinvD R E Ra -> (forall x, In x KS -> getr Rb (reg x) = getr Ra (reg x)) ->
  forallb (fun i => existsb (Nat.eqb i) KS) DIDX = true -> rinvD R E Rb.
Proof. intros RI Kp HB. apply (rinvD_keep R E Ra Rb RI). intros k Hk. apply Kp. exact (L5K.incl_b DIDX KS HB k Hk). Qed.
Lemma rinvD_pres (R : bvmap 5 word) (E : Z) Ra Rb : rinvD R E Ra -> regs_preserved Ra Rb -> rinvD R E Rb.
Proof. intros RI RP. apply (rinvD_keep R E Ra Rb RI). intros k Hk. apply (cs_of_preserved Ra Rb k RP). revert Hk. apply (L5K.incl_b DIDX); vm_compute; reflexivity. Qed.


Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Local Abbreviation statics_vis := (L5ADH.statics_vis L ar C HI LY HIok).
Local Abbreviation stack_rt := (L5ADH.stack_rt L ar).

Lemma div_entry SCRD (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
      (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (to dno qo ro rd E r : Z) :
  352 + 512 <= SCRD ->
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
  getr R 10%bv = Z_to_bv 64 to -> getr R 11%bv = Z_to_bv 64 dno -> getr R 12%bv = Z_to_bv 64 qo -> getr R 13%bv = Z_to_bv 64 ro -> getr R 14%bv = Z_to_bv 64 rd ->
  0 <= to < 2 ^ 64 -> 0 <= dno < 2 ^ 64 -> 0 <= qo < 2 ^ 64 -> 0 <= ro < 2 ^ 64 -> 0 <= rd < 2 ^ 64 ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E SCRD ->
  ffrk 3 FF LK 2 -> ffrs FF E ->
  (forall (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (fx3 : FPState) R3 M3 model3,
      L5AFK.gctx L ar HI LB FF LK A E SCRD (E - 352) (E - 352) E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr ->
      U R 1 = r -> getr R (reg 2) = Z_to_bv 64 E -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
      L5AFK.binv L ar HI M model LB FF LK A E SCRD (E - 352) (down E F ro R) F 3 [] [] M3 model3 LK2 cr A ->
      rinvD R E R3 -> getr R3 (reg 1) = Z_to_bv 64 0x922cc ->
      getr R3 (reg 10) = Z_to_bv 64 (F + 32) /\ getr R3 (reg 11) = Z_to_bv 64 dno /\ getr R3 (reg 12) = Z_to_bv 64 (E - 136) ->
      getr R3 (reg 18) = Z_to_bv 64 (F / 8 + SB) /\ getr R3 (reg 19) = Z_to_bv 64 qo /\ getr R3 (reg 20) = Z_to_bv 64 SB /\ getr R3 (reg 21) = Z_to_bv 64 dno
      /\ getr R3 (reg 22) = Z_to_bv 64 rd /\ getr R3 (reg 23) = Z_to_bv 64 (F + 32) /\ getr R3 (reg 24) = Z_to_bv 64 to /\ getr R3 (reg 27) = Z_to_bv 64 F
      /\ getr R3 (reg 25) = getr R (reg 25) /\ getr R3 (reg 26) = getr R (reg 26) ->
      dsh M3 F 248 248 248 248 248 -> shadow_zero M3 (F + 32) 4 -> L5.u64_at RSEGS M3 F 1102416563 ->
      srealizes RSEGS SCFG (cfg (fx:=fx3) R3 COPYA M3 model3) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R DIVIDE M model) K.
Proof.
  intros HSCR HH AM HK G10 G11 G12 G13 G14 TOR DNR QOR ROR RDR G1 RA G2 A32 G4 STK FFR3 FFRS KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (ER : 140735332487680 <= E <= 140737488355328 /\ 0 <= E < 2 ^ 64) by (clear - SLO SHI SPT HSCR; lia). destruct ER as (ER & ERG).
  assert (EA : aligned E 32) by exact A32.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (WSv : L5.writable RSEGS MV (E - 352) 352).
  { apply (proj2 (writable_vis H M (E - 352) 352 (VIS (E - 352) 352 ltac:(clear - SLO HSCR; lia) ltac:(clear - ER; lia)) ltac:(clear - ER; lia) ltac:(clear - ER; lia))).
    eapply (astk_writable ar M E). exact STK. clear - HSCR; lia. clear; lia. clear; lia. }
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  assert (G2' : getr R (reg 2) = Z_to_bv 64 E) by (rewrite <- r2; exact G2).
  assert (G10' : getr R (reg 10) = Z_to_bv 64 to) by (rewrite <- r10; exact G10).
  assert (G11' : getr R (reg 11) = Z_to_bv 64 dno) by (rewrite <- r11; exact G11).
  assert (G12' : getr R (reg 12) = Z_to_bv 64 qo) by (rewrite <- r12; exact G12).
  assert (G13' : getr R (reg 13) = Z_to_bv 64 ro) by (rewrite <- r13; exact G13).
  assert (G14' : getr R (reg 14) = Z_to_bv 64 rd) by (rewrite <- r14; exact G14).
  (* [comment removed for export] *)
  pose proof (v5P0_conc fx R MV (fun j => match j with 2%nat => E | 33%nat => to | 34%nat => dno | 35%nat => qo | 36%nat => ro | 37%nat => rd | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR18 & aR19 & aR20 & aR21 & aR22 & aR24 & aCS)).
  assert (aR3 : getr R1 (reg 3) = getr R (reg 3)) by (apply aKS; inl). assert (aR4 : getr R1 (reg 4) = getr R (reg 4)) by (apply aKS; inl).
  assert (aR25 : getr R1 (reg 25) = getr R (reg 25)) by (apply aKS; inl). assert (aR26 : getr R1 (reg 26) = getr R (reg 26)) by (apply aKS; inl).
  assert (FRK1v : dfrk E R M1v). { unfold dfrk, U. decompose [and] aCS. repeat split; gmem. }
  set (W1 := fun a => E - 352 <= a < E).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R DIVIDE R1 SM3 M1v W1 K HH AM aMS MG1).
  { intros a Ha Hna. apply aFZ. exact Ha. all: clear - Hna; subst W1; cbn beta in Hna; lia. }
  { intros a Ha Wa. subst W1; cbn beta in Wa. split. apply stack_client. clear - Wa SLO SHI SPT HSCR; lia. clear; lia. clear - Wa ER; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  (* [comment removed for export] *)
  pose proof (aio_stack_malloc _ _ _ _ _ HIok 3 ltac:(right; right; left; reflexivity)) as SM. unfold astack_malloc_spec in SM.
  rewrite (aly_segs L C LY), (aly_sm3 L C LY), (aly_scr_sm L C LY) in SM.
  assert (U2 : bv_unsigned (getr R1 2%bv) = E - 352). { rewrite r2, aR2. apply L5.unsigned_lit. clear - ER; lia. }
  assert (SA16 : (E - 352) mod 16 = 0 /\ (E - 352) mod 32 = 0). { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  eapply (SM fx1 R1 M1 model1 LB FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
  - rewrite r4, aR4, <- r4. exact G4.
  - rewrite r1, aR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
  - rewrite U2. apply (astack_ok_of_astk L ar C LY M M1 E SCRD 352 512 STK MGM1). clear; lia. clear; lia. clear - HSCR; lia. exact (proj1 SA16).
  - apply (ffrk_room 3 FF LK 2 FFR3). clear; lia.
  - intros f Hf. rewrite U2. specialize (FFRS f Hf). clear - FFRS. lia.
  - exact HK.
  - intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
    rewrite U2 in FLNC. rewrite U2 in PRES2. rewrite U2 in HH2. rewrite ?U2. rewrite r1, aR1.
    pose proof (sm_facts L ar C HI LY HIok LB FF LK2 cr A M2 model2 F 3 (E - 352 + 32) fl HH2 ltac:(right; right; left; reflexivity) FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
      as (FR & FFL & F32 & F8 & _ & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
    change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
    assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
    assert (ASTK2 : astk ar M2 E SCRD).
    { apply (astk_after_rt L ar C HI HIok LB FF LK cr A M M1 M2 _ E _ (E - 352) 512 HH STK MGM1 PRES2). clear - HSCR; lia. clear; lia. clear - HSCR; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB _ LK2 cr A M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & _).
    pose proof (statics_vis LB _ LK2 cr A M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    set (H2 := ahid A model2) in *. set (MV2 := mrestrict H2 M2) in *.
    assert (SVIS : forall a, E - 352 <= a < E -> H (Z_to_bv 64 a) = false).
    { intros a Ha. replace a with ((E - 352) + (a - (E - 352))) by (clear; lia). apply (VIS (E - 352) 352). clear - SLO HSCR; lia. clear - ER; lia. clear - Ha; lia. }
    assert (AG2 : forall a, E - 352 <= a < E -> MV2 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ha. unfold MV2. rewrite (mrestrict_visible H2 M2). 2:{ replace a with ((E - 352) + (a - (E - 352))) by (clear; lia). apply (VIS2 (E - 352) 352). clear - SLO HSCR; lia. clear - ER; lia. clear - Ha; lia. }
      rewrite (proj1 PRES2 a). 2:{ clear - Ha ER; lia. } 2:{ apply stack_client. clear - Ha SLO SHI SPT HSCR; lia. clear - Ha; lia. }
      rewrite <- VIS1. symmetry. apply mrestrict_visible. apply SVIS. exact Ha. }
    assert (W352b : L5.writable RSEGS MV2 (E - 352) 352).
    { eapply (L5C.writable_agree RSEGS M1v MV2). intros j Hj. apply AG2. clear - Hj; lia. clear - ER; lia. clear - ER; lia. eapply L5.writable_grows. exact MG1. exact WSv. }
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 3 _ fl E 0 (E - 352) 352 HH2 SPT ltac:(right; right; left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC
                  ltac:(intros i Hi; apply stack_client; clear - Hi SLO SHI SPT HSCR; lia) ltac:(clear; lia)) as (SF & SFSH & SFL).
    change (ff_bytes 3) with 512 in SF. change (ff_bytes 3 / 8) with 64 in SFSH.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (FQ : (F + 512 - 1) / 8 = F / 8 + 64 - 1 /\ F mod 8 = 0 /\ (F + 32) / 8 = F / 8 + 4 /\ (F + 32) mod 8 = 0) by (clear - F8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (NCF : forall a, (F <= a < F + 512 \/ S F <= a <= S (F + 512 - 1)) -> ~ aclient L ar LB FF E SCRD a).
    { intros a Ha. apply (fresh_frame_not_client L ar C HI LY HIok LB FF LK cr A M _ E SCRD F 512 a HH SPT).
      clear - FR; lia. exact FCEIL. exact FAPP. exact (proj1 (proj2 FQ)). clear; lia. reflexivity.
      eapply fframes_apart_incl. exact FAPART. intros g0 Hg; apply in_or_app; left; exact Hg. exact FBLK. exact Ha. }
    assert (NCS : forall a, E - 352 <= a < E -> ~ aclient L ar LB FF E SCRD a).
    { intros a X Hc. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ E SCRD a HH SPT Hc) as [Y|Y]. clear - X Y HSCR; lia. clear - X Y SLO HSCR; lia. }
    assert (EK2 : ek L ar LB FF E SCRD [] M M2).
    { eapply ek_trans. { apply (ek_piece L ar LB FF E SCRD [] M M1 W1 FRM1). intros a Ha Hc _ X. subst W1; cbn beta in X. apply (NCS a). exact X. exact Hc. }
      apply (ek_rt L ar LB FF [] E SCRD (E - 352) 512 [] M1 M2 PRES2). clear - HSCR; lia. clear; lia. }
    assert (DK2 : dk L ar LB FF E SCRD M M2).
    { eapply dk_trans. apply dk_grows. exact MGM1. apply (dk_rt L ar LB FF [] E SCRD (E - 352) 512 M1 M2 PRES2). clear - HSCR; lia. clear; lia. }
    (* [comment removed for export] *)
    assert (FRG : 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 4096 <= F <= 140737488354816 /\ 4096 <= fl <= 140737488355327) by (clear - FR FLR; lia). destruct FRG as (FRG & FLRG & FRP & FLRP).
    assert (ALF : aligned F 32) by exact F32.
    assert (SFA : E - 352 + 352 <= F \/ F + 512 <= E - 352) by (clear - FCEIL SLO HSCR; lia).
    assert (SFLA : E - 352 + 352 <= fl \/ fl + 1 <= E - 352) by (clear - FLR SLO HSCR; lia).
    assert (FLCv' : L5.u64_at RSEGS MV2 (F + 504) fl). { replace (F + 504) with (F + 512 - 8) by (clear; lia). exact FLCv. }
    assert (RC2 : forall j, In j [8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 3; 4]%nat -> getr R2 (reg j) = getr R1 (reg j)). { intros j Hj. apply (cs_of_preserved R1 R2 j RP2). revert Hj. apply (L5K.incl_b [8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 3; 4]%nat); vm_compute; reflexivity. }
    pose proof (v5P1_conc fx1 R2 MV2 (fun j => match j with 2%nat => E | 33%nat => to | 34%nat => dno | 35%nat => qo | 36%nat => ro | 37%nat => rd | 40%nat => F | 41%nat => fl | 58%nat => U R2 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r10; exact B10) | (rewrite (RC2 _) by inl; sc) ]).
    destruct P as (fx3 & R3 & M3v & MG3 & bFR & bFZ & (bMS & bKS & bR1 & bR10 & bR11 & bR12 & bR13 & bR18 & bR23 & bR27 & BQ)).
    set (W3 := fun a => (E - 280 <= a < E - 272 \/ E - 256 <= a < E - 248 \/ E - 240 <= a < E - 232 \/ E - 200 <= a < E - 184) \/ F <= a < F + 24 \/ F / 8 + SB <= a < F / 8 + SB + 52).
    apply (apiece L ar C HI LY HIok LB _ LK2 cr A M2 model2 fx1 fx3 R2 598380 R3 COPYA M3v W3 K HH2 (conj Hh2 MI2) bMS MG3).
    { intros a Ha Hna. apply bFZ. exact Ha. all: clear - Hna; subst W3; cbn beta in Hna; unfold SB in *; lia. }
    { intros a Ha Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
      - split. apply stack_client. clear - Wa SLO SHI SPT HSCR; lia. clear; lia. clear - Wa ER; lia.
      - split. apply (fframe_client L ar LB _ 0 0 F 3 (E - 352 + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Wa; lia. clear - Wa FR; lia.
      - split. apply (fframe_shadow_client L ar LB _ 0 0 F 3 (E - 352 + 32)). left; reflexivity. change (ff_bytes 3) with 512. unfold in_shadow_of, S. rewrite (proj1 FQ). clear - Wa. unfold SB in *. lia.
        clear - Wa FR; unfold SB in Wa; lia. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    decompose [and] BQ. clear BQ.
    (* [comment removed for export] *)
    assert (G : L5AFK.gctx L ar HI LB FF LK A E SCRD (E - 352) (E - 352) E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr).
    { refine (L5AFK.GCTX L ar HI LB FF LK A E SCRD (E - 352) (E - 352) E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr
               ltac:(right; right; left; reflexivity) SPT SLO SHI _ _ _ FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC _ _ FBIG F32 FLA FLR FLBIG NCF _).
      - clear - SLO SHI SPT HSCR; lia.
      - intros a Ha. unfold docell in Ha. clear - Ha; lia.
      - intros Ma Mb OW AG. apply (down_agree E F ro R Ma Mb ltac:(clear - ER; lia) ltac:(clear - ER; lia) OW AG).
      - change (ff_bytes 3) with 512. clear - FR; lia.
      - change (ff_bytes 3) with 512. change (512 / 8) with 64. split. exact F8. split. exact (proj1 FQ). reflexivity.
      - exact NCS. }
    assert (SV2 : forall a, E - 352 <= a < E -> ahid A model2 (Z_to_bv 64 a) = false).
    { intros a Ha. replace a with ((E - 352) + (a - (E - 352))) by (clear; lia). apply (VIS2 (E - 352) 352). clear - SLO HSCR; lia. clear - ER; lia. clear - Ha; lia. }
    assert (XS3 : forall a v, E - 352 <= a -> a + 8 <= E -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
    { intros a v Ha Hb Hc. apply (proj1 (u64_at_vis (ahid A model2) M3 a v ltac:(intros i Hi; apply SV2; clear - Hi Ha Hb; lia) ltac:(clear - Ha ER; lia) ltac:(clear - Hb ER; lia))). rewrite VIS3. exact Hc. }
    assert (OWN3 : down E F ro R M3).
    { split.
      - assert (X : dfrk E R M3v). { unfold dfrk in *. decompose [and] FRK1v. repeat split.
          all: eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; rewrite bFZ; [apply AG2; clear - Hj; lia | clear - Hj ER; lia | | | | | | ] | clear - ER; lia | clear - ER; lia].
          all: clear - Hj SF SFSH; unfold SB in *; lia. }
        unfold dfrk in *. decompose [and] X. repeat split; (apply XS3; [clear; lia | clear; lia | assumption]).
      - repeat split; (apply XS3; [clear; lia | clear; lia | gmem]). }
    assert (BI3 : L5AFK.binv L ar HI M model LB FF LK A E SCRD (E - 352) (down E F ro R) F 3 [] [] M3 model3 LK2 cr A).
    { unfold L5AFK.binv. split. exact HH3. split. exact AM3.
      split. { eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT3. }
      split. apply incl_refl. split. exact LKI2. split. { eapply astk_grows. exact ASTK2. exact MGM3. }
      split. { eapply ek_trans. exact EK2. apply (ek_piece L ar LB FF E SCRD [] M2 M3 W3 FRM3). intros a Ha Hc _ X. subst W3; cbn beta in X. destruct X as [X|[X|X]].
               - apply (NCS a). clear - X; lia. exact Hc.
               - apply (NCF a). left; clear - X; lia. exact Hc.
               - apply (NCF a). right. unfold S. rewrite (proj1 FQ). clear - X. unfold SB in X |- *. lia. exact Hc. }
      split. { eapply dk_trans. exact DK2. apply dk_grows. exact MGM3. }
      split. exact OWN3.
      change (ff_bytes 3 / 8) with 64. eapply L5.defined_grows. exact MGM3. intros i Hi. unfold shadow_zero, byte_at, S in FSH. rewrite (FSH i Hi). discriminate. }
    assert (SHV3 : forall a, F / 8 + SB <= a < F / 8 + SB + 64 -> ahid A model2 (Z_to_bv 64 a) = false).
    { intros a Ha. replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply VSH. clear - Ha; lia. }
    assert (XB3 : forall a v, F / 8 + SB <= a < F / 8 + SB + 64 -> L5.u8_at RSEGS M3v a v -> L5.u8_at RSEGS M3 a v).
    { intros a v Ha Hc. apply (proj1 (u8_at_vis (ahid A model2) M3 a v ltac:(intros i Hi; apply SHV3; clear - Hi Ha; lia) ltac:(clear - Ha FR; unfold SB in *; lia) ltac:(clear - Ha FR F8; unfold SB in *; lia))). rewrite VIS3. exact Hc. }
    assert (DSH3 : dsh M3 F 248 248 248 248 248).
    { unfold dsh, shr8. repeat split; intros j Hj; (apply XB3; [clear - Hj; lia|]);
        first [ (assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia); unfold SB; destruct J as [J|[J|[J|J]]]; subst j; gmem)
              | (match goal with Z0 : L5KA.zeros_at M3v _ 12 |- _ => pose proof (Z0 j Hj) as B0 end; unfold L5.u8_at; cbn [rdn]; unfold SB;
                 replace (F / 8 + 2147450880 + 52 + j) with (F / 8 + 2147450932 + j) by (clear; lia); rewrite B0; reflexivity) ]. }
    assert (SZD3 : shadow_zero M3 (F + 32) 4).
    { intros j Hj. unfold byte_at, S. rewrite (proj1 (proj2 (proj2 FQ))). destruct DSH3 as (_ & Z4 & _). specialize (Z4 j Hj).
      replace (F / 8 + 4 + SB + j) with (F / 8 + SB + 4 + j) by (clear; lia). apply (byte_of_u8 M3 _ 0 Z4). right. clear - Hj FR F8; unfold SB; lia. clear - Hj FR F8; unfold SB; lia. }
    apply (KONT F fl LK2 M2 model2 fx3 R3 M3 model3 G UR1 G2' ltac:(rewrite <- r4; exact G4) BI3).
    + unfold rinvD. split. { rewrite (bKS 2%nat) by inl. rewrite (cs_of_preserved R1 R2 2 RP2) by inl. exact aR2. }
      split. { rewrite (bKS 8%nat) by inl. rewrite (RC2 8%nat) by inl. exact aR8. }
      split. { rewrite (bKS 9%nat) by inl. rewrite (RC2 9%nat) by inl. exact aR9. }
      split. { rewrite (bKS 3%nat) by inl. rewrite (RC2 3%nat) by inl. exact aR3. }
      rewrite (bKS 4%nat) by inl. rewrite (RC2 4%nat) by inl. exact aR4.
    + exact bR1.
    + split. exact bR10. split. exact bR11. exact bR12.
    + split. exact bR18. split. { rewrite (bKS 19%nat) by inl. rewrite (RC2 19%nat) by inl. exact aR19. }
      split. { rewrite (bKS 20%nat) by inl. rewrite (RC2 20%nat) by inl. exact aR20. }
      split. { rewrite (bKS 21%nat) by inl. rewrite (RC2 21%nat) by inl. exact aR21. }
      split. { rewrite (bKS 22%nat) by inl. rewrite (RC2 22%nat) by inl. exact aR22. }
      split. exact bR23. split. { rewrite (bKS 24%nat) by inl. rewrite (RC2 24%nat) by inl. exact aR24. }
      split. exact bR27. split. { rewrite (bKS 25%nat) by inl. rewrite (RC2 25%nat) by inl. exact aR25. }
      rewrite (bKS 26%nat) by inl. rewrite (RC2 26%nat) by inl. exact aR26.
    + exact DSH3.
    + exact SZD3.
    + apply (proj1 (u64_at_vis (ahid A model2) M3 F _ ltac:(intros i Hi; replace (F + i) with (F + (i)) by (clear; lia); apply VF; clear - Hi; lia) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). rewrite VIS3. gmem.
Qed.

End WithIface.
End SCFG_1.
End L5ADVH.
