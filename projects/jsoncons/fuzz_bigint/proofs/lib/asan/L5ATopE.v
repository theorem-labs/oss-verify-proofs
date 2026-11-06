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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue BigModel BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5AStrInit L5ACopyS L5AStrctor L5ADetailH L5AFrameK L5ATopP1 L5ATopP2 L5ATopH L5ATopD.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ATE.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ATP1. Import L5ADH. Import L5ATH.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Definition TOP : Z := 0x8de88.

Lemma tfrk_agree S R M1 M1' : 4096 <= S - 104 -> S <= 2 ^ 47 -> tfrk S R M1 -> (forall a, S - 104 <= a < S -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> tfrk S R M1'.
Proof.
  intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) AG. unfold tfrk.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Let LY2 : as0_layout2 L := as0_layout2_of L C LY.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Local Abbreviation statics_vis := (L5ADH.statics_vis L ar C HI LY HIok).
Local Abbreviation apure := (L5ADH.apure L ar C HI LY HIok).
Local Abbreviation stack_rt := (L5ADH.stack_rt L ar).

Lemma u8_of_some Mk a b : Mk (Z_to_bv 64 a) = Some b -> L5.u8_at RSEGS Mk a (bv_unsigned b).
Proof. intros E. unfold L5.u8_at. cbn [rdn]. rewrite E. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma top_entry SCRT (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
      (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (data sp r : Z) (cs : list byte) :
  208 + 4304 <= SCRT -> strinit_spec L ar HI ->
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
  getr R 10%bv = Z_to_bv 64 data -> getr R 11%bv = Z_to_bv 64 (Z.of_nat (length cs)) -> 0 <= Z.of_nat (length cs) < 2 ^ 26 ->
  (23 <= Z.of_nat (length cs) -> acredit_ok L cr (str_cap (Z.of_nat (length cs)))) ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R 2%bv = Z_to_bv 64 sp -> sp mod 16 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SCRT ->
  ffrk 3 FF LK 2 -> ffrs FF sp ->
  rdn RSEGS M (Z_to_bv 64 data) (length cs) = Some cs -> 0 <= data /\ data + Z.of_nat (length cs) <= 2 ^ 47 ->
  (Z.of_nat (length cs) = 0 \/ exists b m, In (b, m) LB /\ b <= data /\ data + Z.of_nat (length cs) <= b + m) ->
  (forall (V2 cls F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model)
          (fx4 : FPState) R4 M4 model4 LK4 cr4 A4 sk,
      L5AFK.gctx L ar HI LB FF LK A (V2 + cls) SCRT (V2 - 192) (V2 - 192) (V2 + cls) (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr ->
      sp = V2 + cls -> (cls = 0 \/ cls = 16) -> L5ATP2.aligned V2 32 -> 140735332487424 <= V2 <= 140737488355328 -> V2 + cls <= 140737488355328 ->
      U R 1 = r -> getr R (reg 2) = Z_to_bv 64 (V2 + cls) -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
      L5AFK.binv L ar HI M model LB FF LK A (V2 + cls) SCRT (V2 - 192) (town V2 cls F R) F 3 [] (L5ATD.ostr sk) M4 model4 LK4 cr4 A4 ->
      rinvT R V2 cls F R4 -> getr R4 (reg 21) = Z_to_bv 64 (Z.of_nat (length cs)) ->
      shadow_zero M4 (F + 224) 4 -> shadow_zero M4 (F + 288) 4 -> shadow_zero M4 (F + 32) 3 ->
      L5ATD.str_full F M4 sk (map bv_unsigned cs) ->
      (sk = None /\ cr4 = cr \/ exists ps, sk = Some (ps, str_cap (Z.of_nat (length cs))) /\ cr4 = adebit L cr (str_cap (Z.of_nat (length cs)))) ->
      srealizes RSEGS SCFG (cfg (fx:=fx4) R4 581648 M4 model4) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R TOP M model) K.
Proof.
  intros HSCR Hsi HH AM HK G10 G11 NR CRD G1 RA G2 A16 G4 STK FFR3 FFRS RDN DRG0 SRCB KONT.
  set (n := Z.of_nat (length cs)) in *.
  pose proof STK as (_ & SLO & SHI & SPT & DSCR & DUP).
  (* [comment removed for export] *)
  assert (CLSX : exists cls, (cls = 0 \/ cls = 16) /\ (sp - cls) mod 32 = 0).
  { clear - A16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (X : sp mod 32 = 0 \/ sp mod 32 = 16) by lia. destruct X as [X|X]; [exists 0 | exists 16]; split; [left; reflexivity | lia | right; reflexivity | lia]. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct CLSX as (cls & CLS & V2A0). set (V2 := sp - cls) in *.
  assert (SE : sp = V2 + cls) by (subst V2; clear; lia).
  assert (V2A : aligned V2 32) by exact V2A0.
  assert (V2R : 140735332487424 <= V2 <= 140737488355328 /\ 0 <= V2 < 2 ^ 64 /\ V2 + cls <= 140737488355328) by (subst V2; clear - SLO SHI SPT HSCR CLS; lia). destruct V2R as (V2R & V2RG & V2S).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (WSv : L5.writable RSEGS MV (V2 - 192) (192 + cls)).
  { apply (proj2 (writable_vis H M (V2 - 192) (192 + cls) (VIS (V2 - 192) (192 + cls) ltac:(subst V2; clear - SLO HSCR CLS; lia) ltac:(clear - V2R CLS; lia)) ltac:(clear - V2R; lia) ltac:(clear - V2R CLS; lia))).
    eapply (astk_writable ar M sp). exact STK. subst V2; clear - HSCR CLS; lia. subst V2; clear; lia. clear - CLS; lia. }
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  assert (NRG : 0 <= n < 2 ^ 64) by (clear - NR; lia). assert (DRG : 0 <= data < 2 ^ 64) by (clear - DRG0 NR; lia). assert (DNB : data + n <= 2 ^ 47) by (exact (proj2 DRG0)).
  (* [comment removed for export] *)
  assert (EXA : exists (fx1 : FPState) R1 M1v, msteps RSEGS (st fx R TOP MV) (st fx1 R1 SM3 M1v) /\ mem_grows MV M1v
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (V2 - 192 <= i < V2 + cls) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
            /\ getr R1 (reg 1) = Z_to_bv 64 581372 /\ getr R1 (reg 2) = Z_to_bv 64 (V2 - 192) /\ getr R1 (reg 8) = Z_to_bv 64 (V2 + cls)
            /\ getr R1 (reg 9) = Z_to_bv 64 (V2 - 192) /\ getr R1 (reg 10) = Z_to_bv 64 352 /\ getr R1 (reg 18) = Z_to_bv 64 2147450880
            /\ getr R1 (reg 21) = Z_to_bv 64 n /\ getr R1 (reg 22) = Z_to_bv 64 data
            /\ getr R1 (reg 3) = getr R (reg 3) /\ getr R1 (reg 4) = getr R (reg 4) /\ tfrk (V2 + cls) R M1v).
  { assert (G2' : getr R (reg 2) = Z_to_bv 64 (V2 + cls)) by (rewrite <- r2, G2, SE; reflexivity).
    assert (G10' : getr R (reg 10) = Z_to_bv 64 data) by (rewrite <- r10; exact G10).
    assert (G11' : getr R (reg 11) = Z_to_bv 64 n) by (rewrite <- r11; exact G11).
    destruct CLS as [E|E]; rewrite E in *.
    - assert (W0 : L5.writable RSEGS MV (V2 - 192) 192) by (eapply L5.writable_sub; [exact WSv | clear; lia | clear; lia]).
      pose proof (tpA0_conc fx R MV (fun j => match j with 2%nat => V2 | 33%nat => data | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR18 & aR21 & aR22 & aCS)).
      exists fx1, R1, M1v. split. exact aMS. split. exact MG1. split. { intros i Hi Hn. apply aFZ. exact Hi. clear - Hn; lia. }
      split. exact aR1. split. exact aR2. split. { rewrite aR8. f_equal. clear; lia. } split. exact aR9. split. exact aR10. split. exact aR18. split. exact aR21. split. exact aR22.
      split. apply aKS; inl. split. apply aKS; inl. unfold tfrk, U. decompose [and] aCS. repeat split; gmem.
    - assert (W0 : L5.writable RSEGS MV (V2 - 192) 208) by (eapply L5.writable_sub; [exact WSv | clear; lia | clear; lia]).
      pose proof (tpA16_conc fx R MV (fun j => match j with 2%nat => V2 | 33%nat => data | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR18 & aR21 & aR22 & aCS)).
      exists fx1, R1, M1v. split. exact aMS. split. exact MG1. split. { intros i Hi Hn. apply aFZ. exact Hi. clear - Hn; lia. }
      split. exact aR1. split. exact aR2. split. exact aR8. split. exact aR9. split. exact aR10. split. exact aR18. split. exact aR21. split. exact aR22.
      split. apply aKS; inl. split. apply aKS; inl. unfold tfrk, U. decompose [and] aCS. repeat split; gmem. }
  destruct EXA as (fx1 & R1 & M1v & aMS & MG1 & aFZ & aR1 & aR2 & aR8 & aR9 & aR10 & aR18 & aR21 & aR22 & aR3 & aR4 & FRK1v).
  set (W1 := fun a => V2 - 192 <= a < V2 + cls).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R TOP R1 SM3 M1v W1 K HH AM aMS MG1).
  { intros a Ha Hna. apply aFZ. exact Ha. exact Hna. }
  { intros a Ha Wa. subst W1; cbn beta in Wa. split. apply stack_client. subst V2; clear - Wa SLO SHI SPT HSCR CLS; lia. clear; lia. clear - Wa V2R; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  (* [comment removed for export] *)
  pose proof (aio_stack_malloc _ _ _ _ _ HIok 3 ltac:(right; right; left; reflexivity)) as SM. unfold astack_malloc_spec in SM.
  rewrite (aly_segs L C LY), (aly_sm3 L C LY), (aly_scr_sm L C LY) in SM.
  assert (U2 : bv_unsigned (getr R1 2%bv) = V2 - 192). { rewrite r2, aR2. apply L5.unsigned_lit. clear - V2R; lia. }
  assert (SA16 : (V2 - 192) mod 16 = 0 /\ (V2 - 192) mod 32 = 0). { clear - V2A. unfold aligned in V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  eapply (SM fx1 R1 M1 model1 LB FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
  - rewrite r4, aR4, <- r4. exact G4.
  - rewrite r1, aR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
  - rewrite U2. replace (V2 - 192) with (sp - (192 + cls)) by (subst V2; clear; lia).
    apply (astack_ok_of_astk L ar C LY M M1 sp SCRT (192 + cls) 512 STK MGM1). clear - CLS; lia. clear; lia. clear - HSCR CLS; lia.
    replace (sp - (192 + cls)) with (V2 - 192) by (subst V2; clear; lia). exact (proj1 SA16).
  - apply (ffrk_room 3 FF LK 2 FFR3). clear; lia.
  - intros f Hf. rewrite U2. specialize (FFRS f Hf). subst V2; clear - FFRS CLS. lia.
  - exact HK.
  - intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
    rewrite U2 in FLNC. rewrite U2 in PRES2. rewrite U2 in HH2. rewrite ?U2. rewrite r1, aR1.
    pose proof (sm_facts L ar C HI LY HIok LB FF LK2 cr A M2 model2 F 3 (V2 - 192 + 32) fl HH2 ltac:(right; right; left; reflexivity) FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
      as (FR & FFL & F32 & F8 & _ & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
    change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
    assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
    assert (ASTK2 : astk ar M2 sp SCRT).
    { apply (astk_after_rt L ar C HI HIok LB FF LK cr A M M1 M2 _ sp _ (V2 - 192) 512 HH STK MGM1 PRES2). subst V2; clear - HSCR CLS; lia. subst V2; clear - CLS; lia. clear - HSCR; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB _ LK2 cr A M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & _).
    pose proof (statics_vis LB _ LK2 cr A M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    set (H2 := ahid A model2) in *. set (MV2 := mrestrict H2 M2) in *.
    assert (SVIS : forall a, V2 - 192 <= a < V2 + cls -> H (Z_to_bv 64 a) = false).
    { intros a Ha. replace a with ((V2 - 192) + (a - (V2 - 192))) by (clear; lia). apply (VIS (V2 - 192) (192 + cls)). subst V2; clear - SLO HSCR CLS; lia. clear - V2R CLS; lia. clear - Ha; lia. }
    assert (AG2 : forall a, V2 - 192 <= a < V2 + cls -> MV2 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ha. unfold MV2. rewrite (mrestrict_visible H2 M2). 2:{ replace a with ((V2 - 192) + (a - (V2 - 192))) by (clear; lia). apply (VIS2 (V2 - 192) (192 + cls)). subst V2; clear - SLO HSCR CLS; lia. clear - V2R CLS; lia. clear - Ha; lia. }
      rewrite (proj1 PRES2 a). 2:{ clear - Ha V2R CLS; lia. } 2:{ apply stack_client. subst V2; clear - Ha SLO SHI SPT HSCR CLS; lia. clear - Ha; lia. }
      rewrite <- VIS1. symmetry. apply mrestrict_visible. apply SVIS. exact Ha. }
    assert (W192b : L5.writable RSEGS MV2 (V2 - 192) 192).
    { eapply (L5C.writable_agree RSEGS M1v MV2). intros j Hj. apply AG2. clear - Hj CLS; lia. clear - V2R; lia. clear - V2R; lia. eapply L5.writable_grows. exact MG1. eapply L5.writable_sub. exact WSv. clear; lia. clear - CLS; lia. }
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 3 _ fl sp 0 (V2 - 192) (192 + cls) HH2 SPT ltac:(right; right; left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC
                  ltac:(intros i Hi; apply stack_client; subst V2; clear - Hi SLO SHI SPT HSCR CLS; lia) ltac:(clear - CLS; lia)) as (SF & SFSH & SFL).
    change (ff_bytes 3) with 512 in SF. change (ff_bytes 3 / 8) with 64 in SFSH.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (FQ : (F + 512 - 1) / 8 = F / 8 + 64 - 1 /\ F mod 8 = 0 /\ (F + 32) / 8 = F / 8 + 4 /\ (F + 32) mod 8 = 0) by (clear - F8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (NCF : forall a, (F <= a < F + 512 \/ S F <= a <= S (F + 512 - 1)) -> ~ aclient L ar LB FF sp SCRT a).
    { intros a Ha. apply (fresh_frame_not_client L ar C HI LY HIok LB FF LK cr A M _ sp SCRT F 512 a HH SPT).
      clear - FR; lia. exact FCEIL. exact FAPP. exact (proj1 (proj2 FQ)). clear; lia. reflexivity.
      eapply fframes_apart_incl. exact FAPART. intros g0 Hg; apply in_or_app; left; exact Hg. exact FBLK. exact Ha. }
    assert (NCS : forall a, V2 - 192 <= a < sp -> ~ aclient L ar LB FF sp SCRT a).
    { intros a X Hc. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp SCRT a HH SPT Hc) as [Y|Y]. subst V2; clear - X Y HSCR CLS; lia. subst V2; clear - X Y SLO HSCR CLS; lia. }
    assert (EK2 : ek L ar LB FF sp SCRT [] M M2).
    { eapply ek_trans. { apply (ek_piece L ar LB FF sp SCRT [] M M1 W1 FRM1). intros a Ha Hc _ X. subst W1; cbn beta in X. apply (NCS a). rewrite SE. exact X. exact Hc. }
      apply (ek_rt L ar LB FF [] sp SCRT (V2 - 192) 512 [] M1 M2 PRES2). subst V2; clear - HSCR CLS; lia. subst V2; clear - CLS; lia. }
    assert (DK2 : dk L ar LB FF sp SCRT M M2).
    { eapply dk_trans. apply dk_grows. exact MGM1. apply (dk_rt L ar LB FF [] sp SCRT (V2 - 192) 512 M1 M2 PRES2). subst V2; clear - HSCR CLS; lia. subst V2; clear - CLS; lia. }
    (* [comment removed for export] *)
    assert (FRG : 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 4096 <= F <= 140737488354816 /\ 4096 <= fl <= 140737488355327) by (clear - FR FLR; lia). destruct FRG as (FRG & FLRG & FRP & FLRP).
    assert (ALF : aligned F 32) by exact F32.
    assert (SFA : V2 - 192 + 192 <= F \/ F + 512 <= V2 - 192) by (clear - FCEIL SLO HSCR CLS; subst V2; lia).
    assert (SFLA : V2 - 192 + 192 <= fl \/ fl + 1 <= V2 - 192) by (clear - FLR SLO HSCR CLS; subst V2; lia).
    assert (FLCv' : L5.u64_at RSEGS MV2 (F + 504) fl). { replace (F + 504) with (F + 512 - 8) by (clear; lia). exact FLCv. }
    pose proof (tpB_conc fx1 R2 MV2 (fun j => match j with 2%nat => V2 | 33%nat => data | 34%nat => n | 40%nat => F | 41%nat => fl | 58%nat => U R2 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r10; exact B10) ]).
    destruct P as (fx3 & R3 & M3v & MG3 & bFR & bFZ & (bMS & bKS & bR1 & bR10 & bR11 & bR12 & BQ)).
    set (W3 := fun a => V2 - 176 <= a < V2 - 168 \/ F <= a < F + 24 \/ F / 8 + SB <= a < F / 8 + SB + 44).
    apply (apiece L ar C HI LY HIok LB _ LK2 cr A M2 model2 fx1 fx3 R2 581372 R3 STRINIT M3v W3 K HH2 (conj Hh2 MI2) bMS MG3).
    { intros a Ha Hna. apply bFZ. exact Ha. all: clear - Hna; subst W3; cbn beta in Hna; unfold SB in *; lia. }
    { intros a Ha Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
      - split. apply stack_client. subst V2; clear - Wa SLO SHI SPT HSCR CLS; lia. clear; lia. clear - Wa V2R; lia.
      - split. apply (fframe_client L ar LB _ 0 0 F 3 (V2 - 192 + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Wa; lia. clear - Wa FR; lia.
      - split. apply (fframe_shadow_client L ar LB _ 0 0 F 3 (V2 - 192 + 32)). left; reflexivity. change (ff_bytes 3) with 512. unfold in_shadow_of, S. rewrite (proj1 FQ). clear - Wa. unfold SB in *. lia.
        clear - Wa FR; unfold SB in Wa; lia. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    decompose [and] BQ. clear BQ.
    (* [comment removed for export] *)
    assert (G : L5AFK.gctx L ar HI LB FF LK A (V2 + cls) SCRT (V2 - 192) (V2 - 192) (V2 + cls) (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr).
    { rewrite <- SE. refine (L5AFK.GCTX L ar HI LB FF LK A sp SCRT (V2 - 192) (V2 - 192) sp (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr
               ltac:(right; right; left; reflexivity) SPT SLO SHI _ _ _ FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC _ _ FBIG F32 FLA FLR FLBIG NCF _).
      - subst V2; clear - SLO SHI SPT HSCR CLS; lia.
      - intros a Ha. unfold tocell in Ha. subst V2; clear - Ha CLS; lia.
      - intros Ma Mb OW AG. apply (town_agree V2 cls F R Ma Mb ltac:(clear - V2R; lia) ltac:(clear - V2S; lia) ltac:(clear - CLS; lia) OW AG).
      - change (ff_bytes 3) with 512. clear - FR; lia.
      - change (ff_bytes 3) with 512. change (512 / 8) with 64. split. exact F8. split. exact (proj1 FQ). reflexivity.
      - exact NCS. }
    assert (G2S : getr R (reg 2) = Z_to_bv 64 (V2 + cls)) by (rewrite <- r2, G2, SE; reflexivity).
    assert (G4' : getr R (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite <- r4; exact G4).
    assert (SV2 : forall a, V2 - 192 <= a < V2 + cls -> ahid A model2 (Z_to_bv 64 a) = false).
    { intros a Ha. replace a with ((V2 - 192) + (a - (V2 - 192))) by (clear; lia). apply (VIS2 (V2 - 192) (192 + cls)). subst V2; clear - SLO HSCR CLS; lia. clear - V2R CLS; lia. clear - Ha; lia. }
    assert (OWN3 : town V2 cls F R M3).
    { split.
      - apply (tfrk_agree (V2 + cls) R M1v M3 ltac:(clear - V2R CLS; lia) ltac:(clear - V2S; lia) FRK1v). intros a Ha.
        rewrite FRM3. 2: clear - Ha V2R CLS; lia. 2:{ subst W3; cbn beta. clear - Ha SF SFSH CLS. unfold SB in *. lia. }
        rewrite (stack_rt LB FF (V2 - 192) 512 M1 M2 a PRES2 ltac:(clear - Ha V2R CLS; lia) ltac:(subst V2; clear - Ha SLO SHI SPT HSCR CLS; lia) ltac:(clear - Ha CLS; lia)).
        apply EQ1. apply SVIS. clear - Ha CLS; lia.
      - apply (proj1 (u64_at_vis (ahid A model2) M3 (V2 - 176) F ltac:(intros i Hi; apply SV2; clear - Hi CLS; lia) ltac:(clear - V2R; lia) ltac:(clear - V2R; lia))). rewrite VIS3. gmem. }
    assert (BI3 : L5AFK.binv L ar HI M model LB FF LK A (V2 + cls) SCRT (V2 - 192) (town V2 cls F R) F 3 [] [] M3 model3 LK2 cr A).
    { rewrite <- SE. unfold L5AFK.binv. split. exact HH3. split. exact AM3.
      split. { eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT3. }
      split. apply incl_refl. split. exact LKI2. split. { eapply astk_grows. exact ASTK2. exact MGM3. }
      split. { eapply ek_trans. exact EK2. apply (ek_piece L ar LB FF sp SCRT [] M2 M3 W3 FRM3). intros a Ha Hc _ X. subst W3; cbn beta in X. destruct X as [X|[X|X]].
               - apply (NCS a). subst V2; clear - X CLS; lia. exact Hc.
               - apply (NCF a). left; clear - X; lia. exact Hc.
               - apply (NCF a). right. unfold S. rewrite (proj1 FQ). clear - X. unfold SB in X |- *. lia. exact Hc. }
      split. { eapply dk_trans. exact DK2. apply dk_grows. exact MGM3. }
      split. exact OWN3.
      change (ff_bytes 3 / 8) with 64. eapply L5.defined_grows. exact MGM3. intros i Hi. unfold shadow_zero, byte_at, S in FSH. rewrite (FSH i Hi). discriminate. }
    assert (RI3 : rinvT R V2 cls F R3).
    { unfold rinvT. split. rk. split. rk. split. rk. split. greg. split. greg. split. greg. split. greg.
      split. { rewrite (bKS 3%nat) by inl. rewrite (cs_of_preserved R1 R2 3 RP2) by inl. exact aR3. }
      rewrite (bKS 4%nat) by inl. rewrite (cs_of_preserved R1 R2 4 RP2) by inl. exact aR4. }
    (* [comment removed for export] *)
    set (FF' := (F, 3, V2 - 192 + 32) :: FF) in *.
    assert (AOS : aobj FF' (F + 32) 24).
    { exists (F, 3, V2 - 192 + 32). split. left; reflexivity. cbn [ff_addr ff_class fst snd]. change (ff_bytes 3) with 512. split. clear; lia. split. clear; lia. exact (proj2 (proj2 (proj2 FQ))). }
    assert (SHV3 : forall a, F / 8 + SB <= a < F / 8 + SB + 64 -> ahid A model2 (Z_to_bv 64 a) = false).
    { intros a Ha. replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply VSH. clear - Ha; lia. }
    assert (SZS3 : shadow_zero M3 (F + 32) 3).
    { intros j Hj. unfold byte_at, S. rewrite (proj1 (proj2 (proj2 FQ))).
      assert (X : L5.u8_at RSEGS M3v (F / 8 + 4 + SB + j) 0).
      { assert (J : j = 0 \/ j = 1 \/ j = 2) by (clear - Hj; lia). unfold SB. destruct J as [J|[J|J]]; subst j; gmem. }
      rewrite EQ3. apply (byte_of_u8 M3v _ 0 X). right. clear - Hj FR F8; unfold SB; lia. clear - Hj FR F8; unfold SB; lia.
      apply SHV3. clear - Hj; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (IDX : (F + 224) / 8 = F / 8 + 28 /\ (F + 288) / 8 = F / 8 + 36 /\ 0 <= F / 8 /\ F / 8 + SB + 64 <= 2 ^ 47) by (clear - F8 FR; unfold SB; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct IDX as (I224 & I288 & F80 & SHTOP).
    assert (XZ3 : shadow_zero M3 (F + 224) 4).
    { intros j Hj. unfold byte_at. assert (E : HeapIfaceA.S (F + 224) + j = F / 8 + 2147450908 + j) by (unfold HeapIfaceA.S, SB; rewrite I224; clear; lia). rewrite E.
      rewrite EQ3. match goal with Hz : L5KA.zeros_at M3v (F / 8 + 2147450908) 4 |- _ => apply (Hz j Hj) end. apply SHV3. clear - Hj; unfold SB; lia. }
    assert (YZ3 : shadow_zero M3 (F + 288) 4).
    { intros j Hj. unfold byte_at. assert (E : HeapIfaceA.S (F + 288) + j = F / 8 + 2147450916 + j) by (unfold HeapIfaceA.S, SB; rewrite I288; clear; lia). rewrite E.
      rewrite EQ3. match goal with Hz : L5KA.zeros_at M3v (F / 8 + 2147450916) 4 |- _ => apply (Hz j Hj) end. apply SHV3. clear - Hj; unfold SB; lia. }
    assert (EK3 : ek L ar LB FF sp SCRT [] M M3) by (rewrite SE; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 BI3)))))))).
    assert (RDN3 : rdn RSEGS M3 (Z_to_bv 64 data) (Z.to_nat n) = Some cs).
    { subst n. rewrite Nat2Z.id. rewrite <- RDN. apply (L5C.rdn_agree RSEGS M M3). clear - DRG; lia. clear - DRG NR DNB; lia.
      intros i Hi. destruct SRCB as [N0|(pb & pm & INB & PB1 & PB2)]. exfalso; clear - N0 Hi; lia.
      apply EK3. split. clear - Hi DRG NR DNB; lia. split. apply (block_client L ar LB FF sp SCRT pb pm i INB). clear - Hi PB1 PB2; lia. intros rr []. }
    pose proof RI3 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y27 & Y3 & Y4).
    apply (Hsi fx3 R3 M3 model3 K LB FF' LK2 cr A (F + 32) data n (V2 - 192) 581648 cs HH3 AM3 HK).
    + rewrite r10. exact bR10.
    + rewrite r11. exact bR11.
    + rewrite r12. exact bR12.
    + clear - NR; lia.
    + exact CRD.
    + rewrite r1. exact bR1.
    + split. clear; lia. reflexivity.
    + rewrite r2. exact Y2.
    + exact (proj2 SA16).
    + rewrite r4, Y4. exact G4'.
    + replace (V2 - 192) with (sp - (192 + cls)) by (subst V2; clear; lia). apply (astk_sub ar M2 M3 sp SCRT (192 + cls) STRINIT_SCR ASTK2 MGM3).
      clear - CLS; lia. unfold STRINIT_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear; lia. unfold STRINIT_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear - HSCR CLS; lia.
      replace (sp - (192 + cls)) with (V2 - 192) by (subst V2; clear; lia). exact (proj1 SA16).
    + exact AOS.
    + exact SZS3.
    + exact RDN3.
    + destruct SRCB as [N0|(pb & pm & INB & PB1 & PB2)]. left; exact N0. right. exists pb, pm. split. exact INB. split. exact PB1. exact PB2.
    + intros fx4 R4 M4 model4 LB4 cr4 LK4 A4 POST RT4 IA4 AM4 LKI4 HH4.
      destruct POST as (RP4 & SHORT & LONG).
      assert (RI4 : rinvT R V2 cls F R4) by (apply (rinvT_pres R V2 cls F R3 R4 RI3 RP4)).
      assert (R421 : getr R4 (reg 21) = Z_to_bv 64 n).
      { rewrite (cs_of_preserved R3 R4 21 RP4) by inl. rewrite (bKS 21%nat) by inl. rewrite (cs_of_preserved R1 R2 21 RP2) by inl. exact aR21. }
      assert (BIC : forall BX1 cr1, ahpres L ar LB FF' (V2 - 192) STRINIT_SCR [(F + 32, 24)] M3 M4 -> ri_inv HI (BX1 ++ LB) FF' LK4 cr1 A4 M4 (vml_of model4) ->
                L5AFK.binv L ar HI M model LB FF LK A (V2 + cls) SCRT (V2 - 192) (town V2 cls F R) F 3 [] BX1 M4 model4 LK4 cr1 A4).
      { intros BX1 cr1 AH4 HHx.
        apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A (V2 + cls) SCRT (V2 - 192) (V2 - 192) (V2 + cls) (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr G
                 [] [] [] [] BX1 M3 model3 LK2 cr A M4 model4 LK4 cr1 A4 STRINIT_SCR [(F + 32, 24)] BI3 AH4 HHx AM4 RT4 IA4 LKI4).
        - unfold STRINIT_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear; lia.
        - unfold STRINIT_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear - HSCR CLS; lia.
        - intros rr a [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. split. unfold tocell. clear - X SF CLS. lia.
          change (ff_bytes 3 / 8) with 64. clear - X FR FBIG F8. unfold SB. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia.
        - intros a Hc _ rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. rewrite <- SE in Hc. apply (NCF a). left; clear - X; lia. exact Hc.
        - intros a X. exact X. }
      assert (SHK : forall o k g, HeapIfaceA.S o = F / 8 + SB + k -> 0 <= k -> k + g <= 64 -> ahpres L ar LB FF' (V2 - 192) STRINIT_SCR [(F + 32, 24)] M3 M4 -> shadow_zero M3 o g -> shadow_zero M4 o g).
      { intros o k g E Hk Hg AH4 OZ j Hj. unfold byte_at. rewrite (proj1 AH4). apply OZ. exact Hj. rewrite E.
        split. clear - Hj Hk Hg F80 SHTOP; unfold SB in *; lia.
        split. { apply (fframe_shadow_client L ar LB FF' (V2 - 192) STRINIT_SCR F 3 (V2 - 192 + 32)). left; reflexivity. change (ff_bytes 3) with 512. unfold in_shadow_of, HeapIfaceA.S.
                 rewrite (proj1 FQ). clear - Hj Hk Hg. lia. }
        intros rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. clear - X Hj Hk Hg FR FBIG F8. unfold SB in *.
        pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia. }
      set (s := map bv_unsigned cs).
      assert (LS : Z.of_nat (length s) = n) by (subst s n; rewrite length_map; reflexivity).
      assert (BYT : forall p, (forall i, 0 <= i < n -> exists c, nth_error cs (Z.to_nat i) = Some c /\ M4 (Z_to_bv 64 (p + i)) = Some c) -> L5.bytes_at RSEGS M4 p s).
      { intros p CH i Hi. subst s. rewrite length_map in Hi. destruct (CH (Z.of_nat i) ltac:(subst n; clear - Hi; lia)) as (c & NE & MC). rewrite Nat2Z.id in NE.
        replace (nth i (map bv_unsigned cs) 0) with (bv_unsigned c). apply u8_of_some. exact MC.
        symmetry. change 0 with (bv_unsigned (Z_to_bv 8 0)). rewrite (map_nth bv_unsigned cs (Z_to_bv 8 0) i). f_equal. apply nth_error_nth. exact NE. }
      destruct (Z_le_gt_dec n 22) as [HS|HL].
      * destruct (SHORT HS) as (ELB & ECR & SB0 & CHARS & NUL & AH4). subst LB4 cr4.
        apply (KONT V2 cls F fl LK2 M2 model2 fx4 R4 M4 model4 LK4 cr A4 None G SE CLS V2A V2R V2S UR1 G2S G4' (BIC [] cr AH4 HH4) RI4 R421).
        -- apply (SHK (F + 224) 28 4 ltac:(unfold HeapIfaceA.S; rewrite I224; clear; lia) ltac:(clear; lia) ltac:(clear; lia) AH4 XZ3).
        -- apply (SHK (F + 288) 36 4 ltac:(unfold HeapIfaceA.S; rewrite I288; clear; lia) ltac:(clear; lia) ltac:(clear; lia) AH4 YZ3).
        -- apply (SHK (F + 32) 4 3 ltac:(unfold HeapIfaceA.S; rewrite (proj1 (proj2 (proj2 FQ))); clear; lia) ltac:(clear; lia) ltac:(clear; lia) AH4 SZS3).
        -- cbn [L5ATD.str_full]. fold s. split. { apply Nat2Z.inj_le. rewrite LS. exact HS. } split. rewrite LS. exact SB0. split. apply BYT. intros i Hi. replace (F + 32 + 1 + i) with (F + 32 + 1 + i) by reflexivity. exact (CHARS i Hi).
           rewrite LS. exact NUL.
        -- left. split; reflexivity.
      * destruct (LONG ltac:(clear - HL; lia)) as (ps & ELB & ECR & FRESH & SW0 & SLEN & SPD & CHARS & NUL & AH4). subst LB4 cr4.
        set (cap := str_cap n) in *.
        destruct FRESH as ((Q0 & _ & _ & Q3 & Q4 & (_ & _ & Q6)) & _).
        assert (CAPF : n + 1 <= cap /\ 0 <= cap < 2 ^ 60 /\ Z.testbit (cap + 1) 0 = true).
        { destruct (Z.eq_dec n 23) as [E23|N23]. subst cap. rewrite E23. vm_compute. repeat split; discriminate.
          assert (ECAP : cap = 8 * (n / 8) + 8) by (apply L5ASTR.str_cap_ge; clear - HL N23; lia). rewrite ECAP.
          assert (N8 : 0 <= n / 8 < 2 ^ 23 /\ n <= 8 * (n / 8) + 7). { clear - NR. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          split. clear - N8; lia. split. clear - N8; lia.
          replace (8 * (n / 8) + 8 + 1) with (1 + 2 * (4 * (n / 8) + 4)) by (clear; lia). rewrite Z.bit0_odd, Z.odd_add_mul_2. reflexivity. }
        apply (KONT V2 cls F fl LK2 M2 model2 fx4 R4 M4 model4 LK4 (adebit L cr cap) A4 (Some (ps, cap)) G SE CLS V2A V2R V2S UR1 G2S G4' (BIC [(ps, cap)] _ AH4 HH4) RI4 R421).
        -- apply (SHK (F + 224) 28 4 ltac:(unfold HeapIfaceA.S; rewrite I224; clear; lia) ltac:(clear; lia) ltac:(clear; lia) AH4 XZ3).
        -- apply (SHK (F + 288) 36 4 ltac:(unfold HeapIfaceA.S; rewrite I288; clear; lia) ltac:(clear; lia) ltac:(clear; lia) AH4 YZ3).
        -- apply (SHK (F + 32) 4 3 ltac:(unfold HeapIfaceA.S; rewrite (proj1 (proj2 (proj2 FQ))); clear; lia) ltac:(clear; lia) ltac:(clear; lia) AH4 SZS3).
        -- cbn [L5ATD.str_full]. fold s. exists (cap + 1). split.
           { split. exact (proj2 (proj2 CAPF)). split. exact SW0. split. rewrite LS. exact SLEN. split. exact SPD. split. apply BYT. exact CHARS. rewrite LS. exact NUL. }
           split. clear; lia. split. rewrite LS. clear - CAPF; lia. split. clear - CAPF; lia. clear - Q0 Q3 Q6; lia.
        -- right. exists ps. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DISPATCH.
Variable IL : icpt_layout.
Variable XS : Type.
Variable xs_pre : XS -> (word -> option byte) -> Prop.
Variable xs_foot : list L5.range.
Variable e2_landed e3_landed : XS -> list (Z * Z) -> list fframe -> list fframe -> credit -> Z -> (word -> option byte) -> bvmap 5 word ->
                               list (Z * Z) -> credit -> list fframe -> Prop.
Variables (SCRo D1 D2 D3 K1 K2 SCRs d1 d2 d3 : Z) (bytes1 bytes2 : Z -> Z) (st0 : XS).
Hypothesis Hsi : strinit_spec L ar HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hcp : copy_spec L ar HI.
Hypothesis Hcps : L5ACPS.copy_stk_spec L ar HI.
Hypothesis Hcs : L5PSA.cstr_spec L ar IL HI.
Hypothesis Hsc : L5ASC.strctor_norm_spec L ar IL HI SCRs.
Hypothesis Hom1 : L5OMA.opmod1A_spec L ar HI XS xs_pre xs_foot e2_landed e3_landed SCRo D1 D2 D3 K1 bytes1.
Hypothesis Hom2 : L5OMA.opmod2A_spec L ar HI SCRo D1 D2 D3 K2 bytes2.
Hypothesis HDO : D1 <= d1 /\ D2 <= d2 /\ D3 <= d3.
Hypothesis HD : 5 <= d1 /\ 2 <= d2 /\ 1 <= d3.
Hypothesis HK1 : 0 <= K1 /\ forall c, 0 <= c -> 0 <= bytes1 c.
Hypothesis HK2 : 0 <= K2 /\ forall c, 0 <= c -> 0 <= bytes2 c.
Hypothesis HBM : (forall c c', c <= c' -> bytes1 c <= bytes1 c') /\ (forall c c', c <= c' -> bytes2 c <= bytes2 c').
Local Notation REST := (bytes1 268 + (64 + (8 * 268 + bytes2 268 + 8 * Z.max 268 8))).

Theorem top_norm_ok SCRT (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
      (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (data sp r : Z) (cs : list byte) :
  let n := Z.of_nat (length cs) in
  let NEED := str_cap n + (2 * 64 + (2 * L5PSA.vblk (length (snd (L5PSA.split_sign (map bv_unsigned cs)))) + REST)) in
  let crmin := L5OMA.adebits L cr (5 + (K1 + K2 + 3)) NEED in
  208 + 4304 <= SCRT -> 208 + COPY_SCR <= SCRT -> 208 + L5PSA.CSTR_SCR <= SCRT -> 0 <= SCRs /\ 208 + SCRs <= SCRT -> 0 <= SCRo /\ 208 + SCRo <= SCRT ->
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
  getr R 10%bv = Z_to_bv 64 data -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R 2%bv = Z_to_bv 64 sp -> sp mod 16 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SCRT ->
  ffrk 1 FF LK d1 -> ffrk 2 FF LK d2 -> ffrk 3 FF LK (d3 + 1) -> ffrs FF sp ->
  L5OMA.stksh ar M (sp - SCRT) -> SCRT mod 8 = 0 -> SCRo mod 8 = 0 -> getr R 3%bv = Z_to_bv 64 67584 ->      (* [comment removed for export] *)
  L5.img_clear M 0x10000 0x3c000 ->
  rdn RSEGS M (Z_to_bv 64 data) (length cs) = Some cs -> 0 <= data /\ data + n <= 2 ^ 47 ->
  (n = 0 \/ exists b m, In (b, m) LB /\ b <= data /\ data + n <= b + m) ->
  (forall Mk, L5ATD.img_same L ar M Mk -> xs_pre st0 Mk) ->
  L5OMA.acredit_for L cr (5 + (K1 + K2 + 3)) NEED ->
  (forall V2 cls F fl LK2 M2 model2,
      L5AFK.gctx L ar HI LB FF LK A (V2 + cls) SCRT (V2 - 192) (V2 - 192) (V2 + cls) (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr ->
      sp = V2 + cls -> (cls = 0 \/ cls = 16) -> L5ATP2.aligned V2 32 ->
      L5ATD.pads_ok L ar HI R M model K LB FF LK A V2 cls SCRT F crmin XS xs_pre xs_foot e2_landed e3_landed SCRo K1 K2 bytes1 bytes2 SCRs) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr' (LK' : list fframe) (A' : list (Z * Z)),
      getr R' 10%bv = Z_to_bv 64 0 -> regs_preserved R R' ->
      ahpres L ar LB FF sp SCRT [] M M' -> credit_le crmin cr' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R TOP M model) K.
Proof.
  intros n NEED crmin HSCR HS_COPY HS_CS HS_SC HS_OM HH AM HK G10 G11 NR G1 RA G2 A16 G4 STK FFR1 FFR2 FFR3 FFRS STK28 HSCR8 HSO8 G3 IMG0 RDN DRG0 SRCB XSP CRF PADS KONT.
  pose proof HK1 as [HK1a HK1b]. pose proof HK2 as [HK2a HK2b]. pose proof HD as (HD1 & HD2 & HD3).
  set (s := map bv_unsigned cs) in *. set (m := length (snd (L5PSA.split_sign s))) in *. set (vb := L5PSA.vblk m) in *.
  assert (VB0 : 0 <= vb). { subst vb. unfold L5PSA.vblk. destruct (m <? 39)%nat. clear; lia. unfold round_up. pose proof (Z.div_pos (Z.of_nat (num_words_est m)) 8 ltac:(clear; lia) ltac:(clear; lia)) as X. clear - X; lia. }
  assert (RB0 : 0 <= REST). { pose proof (HK1b 268 ltac:(clear; Lia.lia)). pose proof (HK2b 268 ltac:(clear; Lia.lia)). clear - H H0. lia. }
  assert (SC0 : 0 <= str_cap n). { unfold str_cap. destruct (Z.lor n 7 =? 23). clear; lia. pose proof (proj2 (Z.lor_nonneg n 7) ltac:(clear - NR; lia)) as X. clear - X; lia. }
  set (REM := 2 * 64 + (2 * vb + REST)) in *.
  assert (REM0 : 0 <= REM) by (subst REM; clear - VB0 RB0; lia).
  destruct (L5OMA.acredit_for_take L cr (5 + (K1 + K2 + 3)) NEED (str_cap n) LY2 CRF ltac:(clear - HK1a HK2a; lia) ltac:(subst NEED; clear - SC0 REM0; lia)) as [CRS CRFs].
  replace (5 + (K1 + K2 + 3) - 1) with (4 + (K1 + K2 + 3)) in CRFs by (clear; lia). replace (NEED - str_cap n) with REM in CRFs by (subst NEED; clear; lia).
  apply (top_entry SCRT fx R M model K LB FF LK cr A data sp r cs HSCR Hsi HH AM HK G10 G11 NR (fun _ => CRS) G1 RA G2 A16 G4 STK
           (ffrk_le 3 FF LK (d3 + 1) 2 FFR3 ltac:(clear - HD3; lia)) FFRS RDN DRG0 SRCB).
  intros V2 cls F fl LK2 M2 model2 fx4 R4 M4 model4 LK4 cr4 A4 sk G SE CLS V2A V2R V2S UR1 G2S G4' BI4 RI4 R421 XZ4 YZ4 SZS4 SF4 CRC.
  specialize (PADS V2 cls F fl LK2 M2 model2 G SE CLS V2A).
  assert (HSCR' : 208 + 4096 <= SCRT) by (clear - HSCR; lia).
  assert (STKSH : L5OMA.stksh ar M (V2 + cls - SCRT)) by (rewrite <- SE; exact STK28).
  assert (G3' : getr R (reg 3) = Z_to_bv 64 67584). { replace (reg 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact G3. }
  assert (KF : forall (fxf : FPState) Rf Mf modelf LKf Af crf, regs_preserved R Rf -> getr Rf (reg 10) = Z_to_bv 64 0 -> ahpres L ar LB FF (V2 + cls) SCRT [] M Mf ->
             model_rt model modelf -> incl A Af -> amodel_ok Af modelf -> incl LKf LK -> credit_le crmin crf -> ri_inv HI LB FF LKf crf Af Mf (vml_of modelf) ->
             srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K).
  { intros fxf Rf Mf modelf LKf Af crf RPf R10f AHf RTf IAf AMf LKIf CRLf HHf. apply (KONT fxf Rf Mf modelf crf LKf Af). rewrite r10. exact R10f. exact RPf. rewrite SE. exact AHf.
    exact CRLf. exact RTf. exact IAf. exact AMf. exact LKIf. exact HHf. }
  assert (CR4 : L5OMA.acredit_for L cr4 (4 + (K1 + K2 + 3)) REM /\ credit_le crmin (L5OMA.adebits L cr4 (4 + (K1 + K2 + 3)) REM)).
  { destruct CRC as [[_ E4]|(ps & _ & E4)]; fold n in E4; subst cr4.
    - split. apply (L5OMA.acredit_for_le L cr (5 + (K1 + K2 + 3)) NEED _ _ LY2 CRF). clear; lia. subst NEED; clear - SC0; lia.
      subst crmin. apply (L5OMA.adebits_le L cr _ _ _ _ LY2). clear; lia. subst NEED; clear - SC0; lia.
    - split. exact CRFs. subst crmin. rewrite <- (L5OMA.adebits_1 L cr (str_cap n)). rewrite L5OMA.adebits_add.
      replace (1 + (4 + (K1 + K2 + 3))) with (5 + (K1 + K2 + 3)) by (clear; lia). replace (str_cap n + REM) with NEED by (subst NEED REM; clear; lia). apply credit_le_refl. }
  destruct CR4 as [CRF4 CRL4].
  assert (FFRS' : ffrs FF (V2 + cls)) by (rewrite <- SE; exact FFRS).
  destruct (Z_lt_ge_dec n 5000) as [SMALL|BIG].
  - (* [comment removed for export] *)
    assert (LEN : (length s <= 4999)%nat). { subst s. rewrite length_map. clear - SMALL. subst n. lia. }
    assert (BYTES : Forall (fun c => 0 <= c < 256) s).
    { subst s. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (b & <- & _). pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb. clear - Hb; lia. }
    apply (L5ATD.ph_cstr_p L ar C HI LY HIok Hdel R M model K LB FF LK A V2 cls r SCRT F fl LK2 M2 model2 cr G CLS V2A V2R V2S HK RA UR1 G2S G4' G3' HSCR' d1 d2 d3 FFR1 FFR2 FFR3 FFRS' STKSH HSCR8 HD1 HD2 HS_COPY
             crmin KF XS xs_pre xs_foot e2_landed e3_landed SCRo D1 D2 D3 K1 K2 bytes1 bytes2 Hom2 HS_OM HSO8 HDO HK2 Hcps IMG0 Hcp Hom1 HK1 st0 XSP IL SCRs Hsc HS_SC HBM Hcs HS_CS
             fx4 R4 M4 model4 LK4 cr4 A4 sk s n PADS BI4 RI4 R421 ltac:(clear - NR SMALL; lia) XZ4 YZ4 SF4 SZS4 LEN BYTES CRF4 CRL4).
  - (* [comment removed for export] *)
    destruct sk as [[ps cap]|]. 2:{ exfalso. cbn [L5ATD.str_full] in SF4. destruct SF4 as (L22 & _). fold s in L22. subst s. rewrite length_map in L22. clear - L22 BIG. subst n. lia. }
    destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A (V2 + cls) SCRT (V2 - 192) (V2 - 192) (V2 + cls) (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr G
                [] [(ps, cap)] M4 model4 LK4 cr4 A4 BI4) as ((WSv4 & IMGC4 & CSB4 & CUAR4 & RMS4) & _).
    set (MV4 := mrestrict (ahid A4 model4) M4) in *.
    assert (W192c : L5.writable RSEGS MV4 (V2 - 192) 192). { eapply L5.writable_sub. exact WSv4. clear; lia. clear - CLS; lia. }
    pose proof RI4 as (Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z27 & Z3 & Z4).
    assert (NR' : 5000 <= n <= 67108863) by (clear - NR BIG; lia). assert (NRG : 0 <= n < 2 ^ 64) by (clear - NR; lia).
    pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
    assert (FRG : 0 <= F < 2 ^ 64 /\ 0 <= V2 < 2 ^ 64) by (clear - FR V2R; lia). destruct FRG as [FRG V2RG].
    assert (V2A1 : L5ATP1.aligned V2 32) by exact V2A.
    pose proof (tpCbig_conc fx4 R4 MV4 (fun j => match j with 2%nat => V2 | 34%nat => n | 40%nat => F | 58%nat => U R4 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx5 & R5 & M5v & _ & cFR & _ & (cMS & cKS & _)).
    assert (E5 : M5v = MV4) by (apply mem_eq_of_agree; intros a Ha; apply cFR). subst M5v.
    pose proof BI4 as (B41 & B42 & _).
    apply (apure ([(ps, cap)] ++ LB) ((F, 3, V2 - 192 + 32) :: FF) LK4 cr4 A4 M4 model4 fx4 fx5 R4 581648 R5 0x8e198 K B41 B42 cMS).
    intros model5 HH5 AM5 RT5 AH5.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A (V2 + cls) SCRT (V2 - 192) (town V2 cls F R) F 3 [] [(ps, cap)] M4 model4 LK4 cr4 A4 model5 BI4 HH5 AM5 RT5) as BI5.
    assert (RI5 : rinvT R V2 cls F R5). { apply (rinvT_ks R V2 cls F R4 R5 KS_tpCbig RI4 cKS). vm_compute; reflexivity. }
    assert (CRL5 : credit_le crmin cr4).
    { eapply credit_le_trans. exact CRL4. destruct LY2 as [_ (Kc & Bc & Oc)]. unfold credit_le, L5OMA.adebits. cbn [fst snd]. clear - Kc Bc Oc HK1a HK2a REM0. nia. }
    apply (L5ATD.ph_str L ar C HI LY HIok Hdel R M model K LB FF LK A V2 cls r SCRT F fl LK2 M2 model2 cr G CLS V2A V2R V2S HK RA UR1 G2S G4' HSCR' crmin KF
             fx5 R5 M4 model5 LK4 cr4 A4 (Some (ps, cap)) BI5 CRL5 RI5).
    apply (L5ATD.str_full_at F M4 (Some (ps, cap)) s SF4).
Qed.
End DISPATCH.
End WithIface.
End SCFG_1.
End L5ATE.
