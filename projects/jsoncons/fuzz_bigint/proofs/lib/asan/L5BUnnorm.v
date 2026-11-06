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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5WordsB L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreBB0 L5CoreSpecsAB0 L5StepAB0 L5BRed L5BMul10K L5BLeafK L5DivLeafSpecsAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivInnerSpecsAB0 L5BUnnormP L5BShr L5BShrOk L5BNorm.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Bo0_code_94368_9505c.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AUNNORM.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5AMULK. Import L5BLK. Import L5AUNNORMP. Import L5DSA. Import L5DIA. Import L5W.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Notation U := L5BLK.U (only parsing).
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | blia] ].

Lemma r3' : (3%bv : bv 5) = reg 3. Proof. apply bv_eq; reflexivity. Qed.
Lemma USCR_EQ : UNNORM_SCR = 5328. Proof. reflexivity. Qed.
Lemma QSCR_EQ : DIVEQ_SCR = 5264. Proof. reflexivity. Qed.
Lemma SSCR_EQ : L5ASHROK.SHR_SCR = 4592. Proof. reflexivity. Qed.


(* [comment removed for export] *)
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis RZ : resize_spec L ar HI.
Hypothesis DIVEQ : diveq_specA L ar HI.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma callee_stack LBc FF LKc crc Ac M model Mc Wc E scr fr scr' o d n :
  ri_inv HI LBc FF LKc crc Ac M (vml_of model) -> astk ar M E scr -> 0 <= fr -> 0 <= scr' -> fr + scr' <= scr ->
  ahpres L ar LBc FF (E - fr) scr' Wc M Mc -> (forall x, L5.outside [(o, 32); (d, n)] x -> L5.outside Wc x) ->
  aobj FF o 32 -> ((d = o + 16 /\ n <= 16) \/ (exists c, In (d, 8 * c) LBc /\ n <= 8 * c)) ->
  (forall a, E - fr <= a < 2 ^ 47 -> Mc (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall o2, aobj FF o2 32 -> forall i, 0 <= i < 4 -> Mc (Z_to_bv 64 (o2 / 8 + SB + i)) = M (Z_to_bv 64 (o2 / 8 + SB + i)))
  /\ astk ar Mc E scr.
Proof.
  intros HH STK Hfr Hscr' Hsum AHP WS AOB DLOC.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (aobj_facts L ar C HI LY HIok LBc FF LKc crc Ac M model o 32 (E - fr) scr' HH AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & _ & _ & _ & _ & _).
  assert (DF : 0 <= d /\ d + n <= ahl_ceil ar /\ (d + n <= 0x7fff7000 \/ 0x10007fff8000 <= d \/ n <= 0)).
  { destruct DLOC as [[-> Hn]|(c & INc & Hn)].
    - split. clear - OR; lia. split. clear - OR Hn; lia. clear - OBIG Hn; lia.
    - pose proof (WB _ INc) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
      unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5. split. clear - Q0; lia. split. clear - Q4 Hn; lia. clear - Q5 Hn; lia. }
  destruct DF as (D0 & DCEIL & DAPP).
  destruct AHP as (P & DEFc & DKc).
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBc FF (E - fr) scr' a -> ~ (o <= a < o + 32) -> ~ (d <= a < d + n) -> Mc (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. apply P. split. exact Ha. split. exact Hc. apply WS. apply L5ANORM.outside2; assumption. }
  split. { intros a Ra. apply KEEP. clear - Ra SLO SPT Hfr Hscr' Hsum; lia. apply stack_client. clear - Ra SLO Hfr Hscr' Hsum; lia. clear - Ra Hscr'; lia.
           clear - Ra OR SLO Hfr Hscr' Hsum; lia. clear - Ra DCEIL SLO Hfr Hscr' Hsum; lia. }
  split. { intros o2 AO2 i Hi.
           pose proof (aobj_facts L ar C HI LY HIok LBc FF LKc crc Ac M model o2 32 (E - fr) scr' HH AO2 ltac:(clear; lia) ltac:(reflexivity)) as (OR2 & _ & _ & _ & _ & _ & OCLSH2).
           change (32 / 8) with 4 in OCLSH2. apply KEEP. clear - Hi OR2; unfold SB; lia. apply OCLSH2. exact Hi.
           clear - Hi OR2 OBIG; unfold SB; lia. clear - Hi OR2 DAPP; unfold SB; lia. }
  apply (astk_after L ar C HI HIok LBc FF LKc crc Ac M M Mc _ E _ (E - fr) scr' Wc HH STK (mem_grows_refl M)). split. exact P. split. exact DEFc. exact DKc.
  clear - Hfr Hscr' Hsum; lia. clear - Hfr; lia. clear - Hfr Hscr' Hsum; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (X xs sd E r : Z) (bX : L5.bigobj) (wX : list Z).
Hypothesis HH0 : ri_inv HI LB FF LK cr A M0 (vml_of model0).
Hypothesis AM0 : amodel_ok A model0.
Hypothesis HK0 : K [].
Hypothesis G11 : getr R0 11%bv = Z_to_bv 64 X.
Hypothesis G12 : getr R0 12%bv = Z_to_bv 64 xs.
Hypothesis Hxs : 0 <= xs <= 63.
Hypothesis G13 : getr R0 13%bv = Z_to_bv 64 sd.
Hypothesis Hsd : sd = 0 \/ sd = 1.
Hypothesis G1 : getr R0 1%bv = Z_to_bv 64 r.
Hypothesis RA : L5.ra_ok r.
Hypothesis G2 : getr R0 2%bv = Z_to_bv 64 E.
Hypothesis A32 : E mod 32 = 0.
Hypothesis G4 : getr R0 4%bv = Z_to_bv 64 (hl_tp L).
Hypothesis STK : astk ar M0 E UNNORM_SCR.
Hypothesis SSH : L5OMA.stksh ar M0 (E - UNNORM_SCR).
Hypothesis ROOM1 : ffrk 1 FF LK 5.
Hypothesis ROOM3 : ffrk 3 FF LK 2.
Hypothesis RS : ffrs FF E.
Hypothesis OB : L5.big_at RSEGS M0 X bX.
Hypothesis OL : L5C.obj_limbs RSEGS M0 bX wX.
Hypothesis Hlen : (1 <= L5.bo_len bX <= 299)%nat.
Hypothesis SGN : Z.testbit (L5.bo_fb bX) 1 = false.
Hypothesis AOX : aobj FF X 32.
Hypothesis SZX0 : shadow_zero M0 X 4.
Hypothesis INB : forall cap q, L5.bo_st bX = L5.BDyn cap q -> In (q, 8 * cap) LB.
Hypothesis SD1 : sd = 1 -> exists qX, L5.bo_st bX = L5.BDyn 8 qX /\ (2 <= L5.bo_len bX <= 6)%nat.
Hypothesis CRD : sd = 1 -> L5OMA.acredit_for L cr DIVN_K DIVN_BYTES.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr' (LK' : list fframe) (A' : list (Z * Z)),
        unnorm_postA L ar LB FF cr M0 M' R0 R' X E bX cr' ->
        model_rt model0 model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K.
Hypothesis KONT3 : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) qX LB' cr' (LK' : list fframe) (A' : list (Z * Z))
            (F1 fl1 F3 fl3 F1c fl1c F1d fl1d : Z),
        sd = 1 -> L5.bo_st bX = L5.BDyn 8 qX ->
        unnorm_e3A L ar LB FF cr M0 M' R0 R' X qX (L5.bo_len bX) E F1 fl1 F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
        model_rt model0 model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' (ff_u FF E F1 F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model') K.

Let W0 : list L5.range := [(X, 32); (L5.bo_data X bX, 8 * L5.bo_cap bX)].

Lemma sp_rng : 140735332492496 <= E <= 140737488355328 /\ ahl_ceil ar + 4096 + 5328 <= E /\ E <= ar_sptop ar /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47.
Proof. pose proof STK as (A16 & SLO & SHI & SPT & _). rewrite USCR_EQ in SLO. clear - SLO SHI SPT. lia. Qed.
Lemma UR1 : U R0 1 = r. Proof. apply (U_of R0 1 r). rewrite <- r1. exact G1. destruct RA as [Y _]. clear - Y; lia. Qed.
Lemma cost_nonneg : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L. Proof. exact (aly_cost L C LY). Qed.

Definition usaved (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (E - 8) (U R0 1) /\ L5.u64_at RSEGS M (E - 16) (U R0 8) /\ L5.u64_at RSEGS M (E - 24) (U R0 9).
Definition KSU : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
(* [comment removed for export] *)
Definition uctx (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr1 : credit) (LK1 : list fframe) (A1 : list (Z * Z)) : Prop :=
  ri_inv HI LB FF LK1 cr1 A1 M (vml_of model) /\ amodel_ok A1 model /\ model_rt model0 model /\ incl A A1 /\ incl LK1 LK
  /\ getr R (reg 2) = Z_to_bv 64 (E - 64) /\ getr R (reg 8) = Z_to_bv 64 X /\ getr R (reg 9) = Z_to_bv 64 xs
  /\ (forall k, In k KSU -> getr R (reg k) = getr R0 (reg k))
  /\ usaved M /\ astk ar M E UNNORM_SCR /\ shadow_zero M X 4
  /\ ek L ar LB FF E UNNORM_SCR W0 M0 M /\ dk L ar LB FF E UNNORM_SCR M0 M
  /\ L5OMA.acredit_after L cr DIVN_K DIVN_BYTES cr1.
(* [comment removed for export] *)
Definition same_st (st0 st1 : L5.bstore) : Prop :=
  match st0, st1 with L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q | L5.BInl _ _, L5.BInl _ _ => True | _, _ => False end.
Definition uobj (M : word -> option byte) (b1 : L5.bigobj) (w1 : list Z) : Prop :=
  L5.big_at RSEGS M X b1 /\ L5C.obj_limbs RSEGS M b1 w1 /\ same_st (L5.bo_st bX) (L5.bo_st b1) /\ Z.testbit (L5.bo_fb b1) 1 = false.
Lemma same_data b1 : same_st (L5.bo_st bX) (L5.bo_st b1) -> L5.bo_data X b1 = L5.bo_data X bX /\ L5.bo_cap b1 = L5.bo_cap bX.
Proof. unfold same_st, L5.bo_data, L5.bo_cap. destruct (L5.bo_st bX), (L5.bo_st b1); try contradiction. split; reflexivity. intros [-> ->]. split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ufin (viaS : bool) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr1 : credit) (LK1 : list fframe) (A1 : list (Z * Z))
      (fb' : Z) (n' : nat) (st' : L5.bstore) (w' : list Z) :
  uctx R M model cr1 LK1 A1 -> uobj M (L5.BO fb' n' st') w' ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R (if viaS then 0x94474 else 0x9447c) M model) K.
Proof.
  intros CTX (OB1 & OL1 & EST & SG1).
  destruct CTX as (HH & AM & RT & IA & ILK & g2 & g8 & g9 & gK & SV & STK1 & SZX & EK & DK & CRL).
  pose proof sp_rng as (SPR & SLO & SHI & SPT).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK1 cr1 A1 M model HH) as (HOFF & VIS & _).
  set (H := ahid A1 model) in *. set (MV := mrestrict H M) in *.
  assert (W64 : L5.writable RSEGS MV (E - 64) 64).
  { apply (proj2 (writable_vis H M (E - 64) 64 (VIS (E - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M E). exact STK1. rewrite USCR_EQ; clear; lia. clear; lia. clear; lia. }
  assert (XF : forall a v, E - 64 <= a -> a + 8 <= E -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v).
  { intros a v Ha Hb Hc. apply (proj2 (u64_at_vis H M a v (VIS a 8 ltac:(clear - SLO Ha; lia) ltac:(clear - SPR Hb; lia)) ltac:(clear - SPR Ha; lia) ltac:(clear - SPR Hb; lia))). exact Hc. }
  destruct SV as (S1 & S8 & S9).
  assert (A16 : aligned E 16). { unfold aligned. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - A32. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (RUN : exists fx3 R3 M3v, mem_grows MV M3v /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M3v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx R (if viaS then 0x94474 else 0x9447c) MV) (st fx3 R3 0x9448c M3v)
            /\ (forall x, In x KSU -> getr R3 (reg x) = getr R (reg x))
            /\ getr R3 (reg 1) = Z_to_bv 64 (U R0 1) /\ getr R3 (reg 2) = Z_to_bv 64 E /\ getr R3 (reg 8) = Z_to_bv 64 (U R0 8) /\ getr R3 (reg 9) = Z_to_bv 64 (U R0 9)).
  { destruct viaS.
    - pose proof (vunEs_conc fx R MV (fun j => match j with 2%nat => E | 42%nat => U R 1 | 48%nat => U R0 1 | 49%nat => U R0 8 | 50%nat => U R0 9 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XF; [clear; lia | clear; lia | sc])]).
      destruct P as (fx3 & R3 & M3v & MG3 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9)).
      exists fx3, R3, M3v. split. exact MG3. split. exact eFZ. split. exact eMS.
      split. { intros x Hx. apply eKS. revert Hx; apply (L5K.incl_b _ KS_vunEs); vm_compute; reflexivity. }
      repeat split; assumption.
    - pose proof (vunEr_conc fx R MV (fun j => match j with 2%nat => E | 42%nat => U R 1 | 48%nat => U R0 1 | 49%nat => U R0 8 | 50%nat => U R0 9 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XF; [clear; lia | clear; lia | sc])]).
      destruct P as (fx3 & R3 & M3v & MG3 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9)).
      exists fx3, R3, M3v. split. exact MG3. split. exact eFZ. split. exact eMS.
      split. { intros x Hx. apply eKS. revert Hx; apply (L5K.incl_b _ KS_vunEr); vm_compute; reflexivity. }
      repeat split; assumption. }
  destruct RUN as (fx3 & R3 & M3v & MG3 & eFZ & eMS & eKS & eR1 & eR2 & eR8 & eR9).
  rewrite UR1 in eR1.
  pose proof (ret_to fx3 R3 M3v 0x9448c Bo0_code_94368_9505c.W_9448c r Bo0_code_94368_9505c.F_9448c eq_refl Bo0_code_94368_9505c.D_9448c eR1 (proj1 RA) (proj2 RA)) as RETs.
  apply (apiece_ro L ar C HI LY HIok LB FF LK1 cr1 A1 M model fx fx3 R _ R3 r M3v K HH AM (msteps_trans _ _ _ _ eMS RETs) MG3 eFZ).
  intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3.
  pose proof (mem_eq_of_agree M M3 FRM3) as EM. subst M3.
  apply (KONT fx3 R3 M model3 cr1 LK1 A1).
  - unfold unnorm_postA. split.
    { apply preserved_by_index. intros j Hj. cbn in Hj.
      assert (CH : forall j', In j' KSU -> getr R3 (reg j') = getr R0 (reg j')). { intros j' Hj1. rewrite (eKS j' Hj1). apply gK. exact Hj1. }
      destruct Hj as [<-|Hj]. { rewrite eR2. rewrite <- r2, G2. reflexivity. }
      destruct Hj as [<-|Hj]. { apply CH; inl. }
      destruct Hj as [<-|Hj]. { apply CH; inl. }
      destruct Hj as [<-|Hj]. { rewrite eR8. symmetry. apply U_to. }
      destruct Hj as [<-|Hj]. { rewrite eR9. symmetry. apply U_to. }
      repeat (destruct Hj as [<-|Hj]; [apply CH; inl|]). destruct Hj. }
    split. { exists fb', n', st', w'. split. exact OB1. split. exact OL1. split. exact SG1. exact EST. }
    split. exact CRL.
    apply ahpres_of. exact EK. eapply astk_defined. exact STK1. clear; lia. clear; lia. exact DK.
  - eapply L5LZ.model_rt_trans. exact RT. exact RT3.
  - exact IA.
  - exact AM3.
  - exact ILK.
  - exact HH3.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma uctx_after (R R5 : bvmap 5 word) (M M5 : word -> option byte) (model model5 : Model) (cr1 cr5 : credit) (LK1 LK5 : list fframe) (A1 A5 : list (Z * Z))
      (Wc : list L5.range) (scr' n : Z) :
  uctx R M model cr1 LK1 A1 -> regs_preserved R R5 ->
  ri_inv HI LB FF LK5 cr5 A5 M5 (vml_of model5) -> amodel_ok A5 model5 -> model_rt model model5 -> incl A1 A5 -> incl LK5 LK1 ->
  0 <= scr' -> 64 + scr' <= UNNORM_SCR ->
  ahpres L ar LB FF (E - 64) scr' Wc M M5 -> (forall x, L5.outside [(X, 32); (L5.bo_data X bX, n)] x -> L5.outside Wc x) -> n <= 8 * L5.bo_cap bX ->
  L5.big_at RSEGS M0 X bX -> L5OMA.acredit_after L cr DIVN_K DIVN_BYTES cr5 ->
  uctx R5 M5 model5 cr5 LK5 A5.
Proof.
  intros CTX RP HH5 AM5 RT5 IA5 ILK5 Hscr Hsum AHP WS Hn OB0 CRL5.
  destruct CTX as (HH & AM & RT & IA & ILK & g2 & g8 & g9 & gK & SV & STK1 & SZX & EK & DK & CRL).
  pose proof sp_rng as (SPR & SLO & SHI & SPT).
  assert (DLOC : (L5.bo_data X bX = X + 16 /\ n <= 16) \/ (exists c, In (L5.bo_data X bX, 8 * c) LB /\ n <= 8 * c)).
  { unfold L5.bo_data, L5.bo_cap in *. destruct (L5.bo_st bX) as [v0 v1|cap q] eqn:EST. left. split. reflexivity. clear - Hn; lia.
    right. exists cap. split. exact (INB cap q eq_refl). exact Hn. }
  pose proof (callee_stack LB FF LK1 cr1 A1 M model M5 Wc E UNNORM_SCR 64 scr' X (L5.bo_data X bX) n HH STK1 ltac:(clear; lia) Hscr Hsum AHP WS AOX DLOC) as (K1 & K3 & STK5).
  unfold uctx.
  split. exact HH5. split. exact AM5. split. { eapply L5LZ.model_rt_trans. exact RT. exact RT5. }
  split. { intros x Hx. apply IA5. apply IA. exact Hx. } split. { intros x Hx. apply ILK. apply ILK5. exact Hx. }
  split. { rewrite (cs_of_preserved R R5 _ RP) by inl. exact g2. } split. { rewrite (cs_of_preserved R R5 _ RP) by inl. exact g8. } split. { rewrite (cs_of_preserved R R5 _ RP) by inl. exact g9. }
  split. { intros k Hk. rewrite (cs_of_preserved R R5 k RP). apply gK. exact Hk. revert Hk; apply (L5K.incl_b _ cs_all); vm_compute; reflexivity. }
  split. { destruct SV as (S1 & S8 & S9). unfold usaved.
           repeat split; (eapply L5ANORM.u64_at_agree1; [intros i Hi; apply K1; clear - Hi SPR; lia | clear - SPR; lia | clear - SPR; lia | assumption]). }
  split. exact STK5.
  split. { intros j Hj. unfold byte_at, S. rewrite (K3 X AOX j Hj). apply SZX. exact Hj. }
  split.
  - eapply ek_trans. exact EK. eapply (ek_callee L ar LB [] FF [] E UNNORM_SCR (E - 64) scr' W0 Wc M M5). exact AHP. clear - Hsum; lia. clear; lia.
    intros a Hc Ho. apply WS. apply L5ANORM.outside2. { pose proof (Ho (X, 32) ltac:(left; reflexivity)) as Y. unfold L5.in_rng in Y. cbn [fst snd] in Y. exact Y. }
    pose proof (Ho (L5.bo_data X bX, 8 * L5.bo_cap bX) ltac:(right; left; reflexivity)) as Y. unfold L5.in_rng in Y. cbn [fst snd] in Y. clear - Y Hn. lia.
  - split. eapply dk_trans. exact DK. eapply (dk_callee L ar LB [] FF [] E UNNORM_SCR (E - 64) scr' Wc M M5). exact AHP. clear - Hsum; lia. clear; lia. exact CRL5.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma W0_off_shadow a : in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W0 a.
Proof.
  intros SX rr Hr IR. unfold in_shadow_of, S, SB in SX. unfold L5.in_rng in IR.
  pose proof sp_rng as (SR & SLO & SHI & SPT).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as (WB & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M0 model0 X 32 E UNNORM_SCR HH0 AOX ltac:(clear; lia) ltac:(reflexivity)) as ((DLO & DCE & _) & DBIG & _).
  replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) in SX by (clear; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415 in SX.
  assert (SX' : 2147450880 <= a <= 17592186044415 + 2147450880).
  { split. 2: exact (proj2 SX). eapply Z.le_trans. 2: exact (proj1 SX). apply (Z.add_le_mono_r 0 (ahl_ceil ar / 8) 2147450880). apply Z.div_pos. clear - DLO DCE; lia. clear; lia. }
  clear SX. unfold W0 in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in IR.
  - clear - SX' IR DBIG. lia.
  - unfold L5.bo_data, L5.bo_cap in IR. destruct (L5.bo_st bX) as [v0 v1|cap q] eqn:ES.
    + clear - SX' IR DBIG. lia.
    + pose proof (INB cap q eq_refl) as INq. pose proof (WB _ INq) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5. clear - SX' IR Q5. lia.
Qed.
Lemma ustksh_at (Mk : word -> option byte) cs : ek L ar LB FF E UNNORM_SCR W0 M0 Mk -> 0 <= cs <= 5264 -> cs mod 8 = 0 -> L5OMA.stksh ar Mk (E - 64 - cs).
Proof.
  intros EK CSR C8. pose proof sp_rng as (SR & SLO & SHI & SPT).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as WF0.
  assert (TOP : ar_stack_top ar <= 2 ^ 47). { clear - WF0. decompose [and] WF0. assumption. } clear WF0.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (M8 : (E - UNNORM_SCR) mod 8 = 0 /\ (E - 64 - cs) mod 8 = 0) by (rewrite USCR_EQ; clear - A32 C8; Lia.lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (L5ANORM.stksh_sub ar M0 Mk (E - UNNORM_SCR) (E - 64 - cs) SSH); [rewrite USCR_EQ; clear - CSR; lia | exact (proj1 M8) | exact (proj2 M8) | rewrite USCR_EQ; clear - SLO; lia | rewrite USCR_EQ; clear - SR; lia
                                                                | exact TOP | clear - SPT; lia | ].
  intros a Ha SX. apply EK. split. exact Ha. split. right; right; right; right; left. exact SX. apply W0_off_shadow. exact SX.
Qed.

Lemma tail_shr (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr1 : credit) (LK1 : list fframe) (A1 : list (Z * Z)) (b1 : L5.bigobj) (w1 : list Z) :
  uctx R M model cr1 LK1 A1 -> uobj M b1 w1 -> 1 <= xs ->
  getr R (reg 10) = Z_to_bv 64 X -> getr R (reg 11) = Z_to_bv 64 xs -> getr R (reg 1) = Z_to_bv 64 0x94474 ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R L5ASHR.SHR M model) K.
Proof.
  intros CTX (OB1 & OL1 & EST & SG1) Hxs1 G10 G11' G1'.
  pose proof CTX as (HH & AM & RT & IA & ILK & g2 & g8 & g9 & gK & SV & STK1 & SZX & EK & DK & CRL).
  pose proof sp_rng as (SPR & SLO & SHI & SPT). destruct (same_data b1 EST) as (EDATA & ECAP).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF1.
  assert (ND1 : NoDup (map ff_addr (FF ++ LK1))). { clear - WF1. decompose [and] WF1. assumption. } clear WF1.
  apply (L5ASHROK.shr_okA L ar C HI LY HIok RZ fx R M model K LB FF LK1 cr1 A1 X (E - 64) 0x94474 xs b1 w1 HH AM HK0).
  - rewrite r10. exact G10.
  - rewrite r11. exact G11'.
  - clear - Hxs Hxs1; lia.
  - rewrite r1. exact G1'.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact g2.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - A32. lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite r4, (gK 4%nat ltac:(inl)), <- r4. exact G4.
  - rewrite SSCR_EQ. eapply astk_sub. exact STK1. apply mem_grows_refl. clear; lia. clear; lia. rewrite USCR_EQ; clear; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - A32. lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite SSCR_EQ. apply (ustksh_at M 4592 EK ltac:(clear; lia) ltac:(reflexivity)).
  - apply (L5ANORM.ffr_lk FF LK LK1 4). 2: exact ILK. 2: exact ND1. unfold ffr. unfold ffrk in ROOM1. clear - ROOM1. lia.
  - eapply ffrs_le. exact RS. clear; lia.
  - exact OB1.
  - exact OL1.
  - exact AOX.
  - exact SZX.
  - intros cap q E1. unfold same_st in EST. rewrite E1 in EST. destruct (L5.bo_st bX) as [v0 v1|cap0 q0] eqn:E0; [contradiction|]. destruct EST as [-> ->]. exact (INB cap0 q0 eq_refl).
  - intros fx5 R5 M5 model5 LK5 A5 POST RT5 IA5 AM5 ILK5 HH5.
    destruct POST as (RP5 & B10 & rw & st5 & LRW & WRW & (OB5 & OL5) & STM & AHP5). rewrite SSCR_EQ in AHP5.
    destruct b1 as [fb1 len1 st1]. cbn [L5.bo_len L5.bo_fb L5.bo_st] in *.
    assert (LC : Z.of_nat len1 <= L5.bo_cap bX).
    { rewrite <- ECAP. unfold L5.bo_cap. cbn [L5.bo_st]. destruct OB1 as (_ & _ & _ & OST). cbn [L5.bo_st L5.bo_len] in OST. destruct st1 as [v0 v1|c q].
      destruct OST as (_ & _ & _ & Hl2 & _). clear - Hl2; Lia.lia. destruct OST as (_ & _ & _ & Hlc & _). exact Hlc. }
    assert (CTX5 : uctx R5 M5 model5 cr1 LK5 A5).
    { apply (uctx_after R R5 M M5 model model5 cr1 cr1 LK1 LK5 A1 A5 _ 4592 (8 * Z.of_nat len1) CTX RP5 HH5 AM5 RT5 IA5 ILK5 ltac:(clear; lia) ltac:(rewrite USCR_EQ; clear; lia) AHP5).
      rewrite <- EDATA. intros x Hx. exact Hx. clear - LC; lia. exact OB. exact CRL. }
    set (n' := rlen rw) in *.
    set (fb5 := if Nat.eqb len1 0 then fb1 else if Nat.eqb n' 0 then Z.land fb1 253 else fb1) in *.
    apply (ufin true fx5 R5 M5 model5 cr1 LK5 A5 fb5 n' st5 (firstn n' rw) CTX5).
    split. exact OB5.
    split. { apply (L5ANORM.obj_limbs_prefix M5 fb5 len1). exact OL5. pose proof (rlen_le rw) as Y. rewrite LRW in Y. exact Y.
             destruct st5 as [v0 v1|c q]. 2: exact I. destruct OB5 as (_ & _ & _ & OST5). cbn [L5.bo_st L5.bo_len] in OST5.
             destruct st1 as [u0 u1|c1 q1]; [|contradiction]. destruct OB1 as (_ & _ & _ & OST1). cbn [L5.bo_st L5.bo_len] in OST1. exact (proj1 (proj2 (proj2 (proj2 OST1)))). }
    split. { cbn [L5.bo_st]. unfold same_st in *. destruct (L5.bo_st bX) as [v0 v1|cap0 q0]; destruct st1 as [u0 u1|c1 q1]; destruct st5 as [z0 z1|c5 q5]; try contradiction; try exact I.
             destruct EST as [-> ->]. exact STM. }
    cbn [L5.bo_fb]. subst fb5. destruct (Nat.eqb len1 0). exact SG1. destruct (Nat.eqb n' 0). 2: exact SG1.
    rewrite Z.land_spec, SG1. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_red (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr1 : credit) (LK1 : list fframe) (A1 : list (Z * Z)) (b1 : L5.bigobj) (w1 : list Z) :
  uctx R M model cr1 LK1 A1 -> uobj M b1 w1 ->
  getr R (reg 10) = Z_to_bv 64 X -> getr R (reg 1) = Z_to_bv 64 0x9447c ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R L5ARED.REDUCE M model) K.
Proof.
  intros CTX (OB1 & OL1 & EST & SG1) G10 G1'.
  pose proof CTX as (HH & AM & RT & IA & ILK & g2 & g8 & g9 & gK & SV & STK1 & SZX & EK & DK & CRL).
  pose proof sp_rng as (SPR & SLO & SHI & SPT). destruct (same_data b1 EST) as (EDATA & ECAP).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK1 cr1 A1 M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (L5ASHROK.statics_vis L ar C HI LY HIok LB FF LK1 cr1 A1 M model HH) as (IMGC & CSB & CUAR).
  pose proof (L5ANORM.obj_vis L ar C HI LY HIok LB FF LK1 cr1 A1 M model X E HH AOX SZX ltac:(clear - SLO; lia) SPT) as ((XR & XA & XBIG & XFR & XLO) & XZ & XW & XV & XOD & XBD).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  set (H := ahid A1 model) in *. set (MV := mrestrict H M) in *.
  assert (W16 : L5.writable RSEGS MV (E - 64 - 16) 16).
  { apply (proj2 (writable_vis H M (E - 64 - 16) 16 (VIS (E - 64 - 16) 16 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M E). exact STK1. rewrite USCR_EQ; clear; lia. clear; lia. clear; lia. }
  destruct b1 as [fb len sto]. cbn [L5.bo_len L5.bo_st L5.bo_fb] in *.
  set (d := L5.bo_data X (L5.BO fb len sto)). set (cap := L5.bo_cap (L5.BO fb len sto)).
  pose proof OB1 as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Hfb, O8, OST.
  assert (INB1 : forall c q, sto = L5.BDyn c q -> In (q, 8 * c) LB).
  { intros c q E1. unfold same_st in EST. rewrite E1 in EST. destruct (L5.bo_st bX) as [v0 v1|cap0 q0] eqn:E0; [contradiction|]. destruct EST as [-> ->]. exact (INB cap0 q0 eq_refl). }
  assert (DF : ((2147446784 + 17592186048512 <= d \/ d + 8 * cap <= 2147446784) /\ (E - 64 - 16 + 16 <= d \/ d + 8 * cap <= E - 64 - 16) /\ (X + 16 <= d \/ d + 8 * cap <= X)
                /\ L5.writable RSEGS MV d (8 * cap) /\ L5KA.zeros_at MV (d / 8 + SB) cap /\ cap <= 2 ^ 27)
               /\ (forall a v, d <= a -> a + 8 <= d + 8 * cap -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v)
               /\ Z.of_nat len <= cap
               /\ (forall a, d <= a < d + 8 * cap -> H (Z_to_bv 64 a) = false)).
  { subst d cap. unfold L5.bo_data, L5.bo_cap. cbn [L5.bo_st]. destruct sto as [u0 u1|c q].
    - destruct OST as (Bb & O16b & O24b & Hl2b & Ru0 & Ru1). split. 2: split. 3: split.
      + split. clear - XBIG; lia. split. clear - XFR; lia. split. left; clear; lia.
        split. eapply L5.writable_sub. exact XW. clear; lia. clear; lia.
        split. { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
                 change (X mod 8 = 0) in XA. eapply L5KA.zeros_at_sub. exact XZ. clear - XR XA. lia. clear - XR XA. lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). clear; lia.
      + intros a v Ha Hb Hc. apply XOD. clear - Ha; lia. clear - Hb; lia. exact Hc.
      + clear - Hl2b; Lia.lia.
      + intros a Ha. replace a with (X + (a - X)) by (clear; lia). apply (XV (a - X)). clear - Ha; lia.
    - destruct OST as (Bb & O16b & O24b & Hlcb & Hcapb & Q8b & Q4096b & Q47b & QHb). pose proof (INB1 c q eq_refl) as STB.
      pose proof (L5ASHROK.block_vis L ar C HI LY HIok LB FF LK1 cr1 A1 M model q c E HH STB ltac:(clear - Hcapb; lia) ltac:(clear - SLO; lia) SPT) as (QR & QD8 & QBIG & QFR & QSHD & QIMG & QW & QZ & QV & XQ).
      fold H in QV, XQ. fold MV in QW, QZ, XQ.
      pose proof (L5ANORM.blk_obj_apart L ar C HI HIok LB FF LK1 cr1 A1 M _ q c X HH STB AOX) as QO.
      split. 2: split. 3: split.
      + split. exact QBIG. split. clear - QFR; lia. split. clear - QO; lia. split. exact QW. split. exact QZ. clear - Hcapb; lia.
      + exact XQ. + exact Hlcb.
      + intros a Ha. replace a with (q + (a - q)) by (clear; lia). apply (QV (a - q)). clear - Ha; lia. }
  destruct DF as (DFACTS & XD & CAPb & DVIS).
  assert (OBv : L5.big_at RSEGS MV X (L5.BO fb len sto)).
  { eapply L5C.big_at_agree. 4: exact OB1. 2: clear - XR; lia. 2: clear - XR; lia. intros j Hj. unfold MV. apply mrestrict_visible. replace j with (X + (j - X)) by (clear; lia). apply (XV (j - X)). clear - Hj; lia. }
  assert (OLv : L5C.obj_limbs RSEGS MV (L5.BO fb len sto) w1).
  { destruct OL1 as (L1 & R1' & LAT2). cbn [L5.bo_len L5.bo_st] in L1, LAT2 |- *. split. exact L1. split. exact R1'. destruct sto as [u0 u1|c q]. exact LAT2.
    subst d cap. unfold L5.bo_data, L5.bo_cap in XD, CAPb. cbn [L5.bo_st] in XD, CAPb. intros i Hi. apply XD. clear - Hi; lia. rewrite L1 in Hi. clear - Hi CAPb; lia. apply LAT2. exact Hi. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (A16' : (E - 64) mod 16 = 0) by (clear - A32; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct (L5ARED.reduce_run fx R MV X (E - 64) 0x9447c (L5.BO fb len sto) w1 G10 G1' ltac:(split; [clear; lia | reflexivity]) g2 ltac:(clear - SPR; lia)
              A16' W16 IMGC CSB CUAR ltac:(clear - XLO XR; lia) XA XBIG ltac:(clear - XFR; lia) XZ XW OBv OLv DFACTS)
    as (fx3 & R3 & M3v & MS3 & (OB3 & K3 & R3_2 & R3_10 & FR3 & GR3)).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  set (W3 := fun a => X <= a < X + 16 \/ E - 80 <= a < E - 64).
  apply (apiece L ar C HI LY HIok LB FF LK1 cr1 A1 M model fx fx3 R L5ARED.REDUCE R3 0x9447c M3v W3 K HH AM MS3 GR3).
  { intros a Ha Hna. apply FR3. exact Ha. all: clear - Hna; subst W3; cbn beta in Hna; lia. }
  { intros a Ha Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|Wa].
    - split. apply (obj_client L ar LB FF 0 0 X 32 a AOX). clear - Wa; lia. clear - Wa XLO; lia.
    - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (X <= a < X + 16) -> ~ (E - 80 <= a < E - 64) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N1 N2. apply FRM3. exact Ha. subst W3; cbn beta. clear - N1 N2. Lia.lia. }
  set (n' := rlen w1) in *. set (fb3 := if Nat.eqb n' 0 then Z.land fb 253 else fb) in *.
  assert (CTX3 : uctx R3 M3 model3 cr1 LK1 A1).
  { unfold uctx. split. exact HH3. split. exact AM3. split. { eapply L5LZ.model_rt_trans. exact RT. exact RT3. } split. exact IA. split. exact ILK.
    split. exact R3_2. split. { rewrite K3 by inl. exact g8. } split. { rewrite K3 by inl. exact g9. }
    split. { intros k Hk. rewrite K3. apply gK. exact Hk. revert Hk; apply (L5K.incl_b _ L5ARED.KS); vm_compute; reflexivity. }
    split. { destruct SV as (S1 & S8 & S9). unfold usaved.
             repeat split; (eapply L5ANORM.u64_at_agree1; [intros i Hi; apply KEEP3; [clear - Hi SPR; lia | clear - Hi XFR; lia | clear - Hi; lia] | clear - SPR; lia | clear - SPR; lia | assumption]). }
    split. { eapply astk_grows. exact STK1. exact MGM3. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split. { intros j Hj. unfold byte_at, S. rewrite KEEP3. apply SZX. exact Hj. clear - Hj XR; unfold SB; lia. clear - Hj XR XBIG; unfold SB; lia. clear - Hj XR SPR; unfold SB; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split.
    - eapply ek_trans. exact EK. apply (ek_piece L ar LB FF E UNNORM_SCR W0 M M3 W3 FRM3). intros a Ha Hc Ho Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|Wa].
      + apply (Ho (X, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - Wa; lia.
      + destruct (aclient_cases L ar C HI LY HIok LB FF LK1 cr1 A1 M _ E UNNORM_SCR a HH SPT Hc) as [Y|Y]. rewrite USCR_EQ in Y. clear - Wa Y; lia. clear - Wa Y SLO; lia.
    - split. eapply dk_trans. exact DK. apply dk_grows. exact MGM3. exact CRL. }
  apply (ufin false fx3 R3 M3 model3 cr1 LK1 A1 fb3 n' sto (firstn n' w1) CTX3).
  split. { eapply L5C.big_at_agree. 4: exact OB3. 2: clear - XR; lia. 2: clear - XR; lia. intros j Hj. symmetry. rewrite <- VIS3. apply mrestrict_visible.
           replace j with (X + (j - X)) by (clear; lia). apply (XV (j - X)). clear - Hj; lia. }
  split. { apply (L5ANORM.obj_limbs_prefix M3 fb3 len). 2:{ pose proof (rlen_le w1) as Y. rewrite (proj1 OL1) in Y. exact Y. }
           2:{ destruct sto as [u0 u1|c q]. destruct OST as (_ & _ & _ & Hl2 & _). exact Hl2. exact I. }
           destruct OL1 as (L1 & R1' & LAT2). cbn [L5.bo_len L5.bo_st] in L1, LAT2 |- *. split. exact L1. split. exact R1'. destruct sto as [u0 u1|c q]. exact LAT2.
           destruct OST as (_ & _ & _ & Hlc & Hcap & _ & Q4 & Q47 & _). pose proof (INB1 c q eq_refl) as STB.
           pose proof (L5ANORM.blk_obj_apart L ar C HI HIok LB FF LK1 cr1 A1 M _ q c X HH STB AOX) as QO. pose proof (proj1 (WB _ STB)) as (_ & _ & _ & _ & QCE & _). cbn [fst snd] in QCE.
           eapply (L5C.limbs_at_agree RSEGS M M3). 4: exact LAT2. 2: clear - Q4; lia. 2:{ rewrite L1. clear - Hlc Q47. lia. }
           intros j Hj. rewrite L1 in Hj. apply KEEP3. clear - Hj Q4 Q47 Hlc; lia. clear - Hj QO Hlc; lia. clear - Hj QCE SLO Hlc; lia. }
  split. exact EST.
  cbn [L5.bo_fb]. subst fb3. destruct (Nat.eqb n' 0). 2: exact SG1. rewrite Z.land_spec, SG1. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma entry_obj : uobj M0 bX wX.
Proof. split. exact OB. split. exact OL. split. 2: exact SGN. unfold same_st. destruct (L5.bo_st bX); [exact I | split; reflexivity]. Qed.

Lemma after_A (fx1 : FPState) (R1 : bvmap 5 word) (M1v : word -> option byte) (pc1 : Z) :
  let MV := mrestrict (ahid A model0) M0 in
  mem_grows MV M1v -> (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (E - 64 <= i < E - 64 + 64) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)) ->
  msteps RSEGS (st fx0 R0 UNNORM MV) (st fx1 R1 pc1 M1v) ->
  (forall x, In x KSU -> getr R1 (reg x) = getr R0 (reg x)) ->
  getr R1 (reg 2) = Z_to_bv 64 (E - 64) -> getr R1 (reg 8) = Z_to_bv 64 X -> getr R1 (reg 9) = Z_to_bv 64 xs ->
  L5.u64_at RSEGS M1v (E - 24) (U R0 9) -> L5.u64_at RSEGS M1v (E - 16) (U R0 8) -> L5.u64_at RSEGS M1v (E - 8) (U R0 1) ->
  (forall M1 model1, uctx R1 M1 model1 cr LK A -> uobj M1 bX wX ->
       (forall a v, E - 64 <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v) ->
       (forall a v, E - 64 <= a -> a + 1 <= E -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v) ->
       (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 64 <= a < E) -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
       srealizes RSEGS SCFG (cfg (fx:=fx1) R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx0) R0 UNNORM M0 model0) K.
Proof.
  intros MV MG1 AFZ AMS AKS aR2 aR8 aR9 C24 C16 C8 KK.
  pose proof sp_rng as (SPR & SLO & SHI & SPT).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M0 model0 HH0) as (HOFF & VIS & _).
  pose proof (L5ANORM.obj_vis L ar C HI LY HIok LB FF LK cr A M0 model0 X E HH0 AOX SZX0 ltac:(clear - SLO; lia) SPT) as ((XR & XA & XBIG & XFR & XLO) & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as (WB & _).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M0 model0 fx0 fx1 R0 UNNORM R1 pc1 M1v (fun a => E - 64 <= a < E) K HH0 AM0 AMS MG1).
  { intros a Ha Hna. apply AFZ. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (HV : forall a, E - 64 <= a < E -> ahid A model0 (Z_to_bv 64 a) = false).
  { intros a Ra. replace a with ((E - 64) + (a - (E - 64))) by (clear; lia). apply (VIS (E - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia. }
  assert (T64 : forall a v, E - 64 <= a -> a + 8 <= E -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj. apply EQ1. apply HV. clear - Ha Hb Hj; lia. }
  assert (T8 : forall a v, E - 64 <= a -> a + 1 <= E -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v).
  { intros a v Ha Hb Hc. eapply L5C.u8_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj. apply EQ1. apply HV. clear - Ha Hb Hj; lia. }
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (E - 64 <= a < E) -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)). { intros a Ha Hn. apply FRM1. exact Ha. exact Hn. }
  apply (KK M1 model1). 3: exact T64. 3: exact T8. 3: exact KEEP1.
  - unfold uctx. split. exact HH1. split. exact AM1. split. exact RT1. split. apply incl_refl. split. apply incl_refl.
    split. exact aR2. split. exact aR8. split. exact aR9. split. exact AKS.
    split. { unfold usaved. split. apply T64. clear; lia. clear; lia. exact C8. split. apply T64. clear; lia. clear; lia. exact C16. apply T64. clear; lia. clear; lia. exact C24. }
    split. { eapply astk_grows. exact STK. exact MGM1. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split. { intros j Hj. unfold byte_at, S. rewrite KEEP1. apply SZX0. exact Hj. clear - Hj XR; unfold SB; lia. clear - Hj XR SPR; unfold SB; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split. { apply (ek_piece L ar LB FF E UNNORM_SCR W0 M0 M1 (fun a => E - 64 <= a < E) FRM1). intros a Ha Hc Ho Wa.
             destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M0 _ E UNNORM_SCR a HH0 SPT Hc) as [Y|Y]. rewrite USCR_EQ in Y. clear - Wa Y; lia. clear - Wa Y SLO; lia. }
    split. { apply dk_grows. exact MGM1. }
    pose proof cost_nonneg as (CK & CL & CO). unfold L5OMA.acredit_after, credit_le, L5OMA.adebits, DIVN_K, DIVN_BYTES. cbn [fst snd]. split. clear - CK; lia. clear - CL CO; lia.
  - destruct entry_obj as (OB0 & OL0 & EST & SG0). split. 2: split. 3: split. 3: exact EST. 3: exact SG0.
    + eapply L5C.big_at_agree. 4: exact OB. 2: clear - XR; lia. 2: clear - XR; lia. intros j Hj. apply KEEP1. clear - Hj XR; lia. clear - Hj XFR; lia.
    + destruct OL as (L1 & R1' & LAT). split. exact L1. split. exact R1'. destruct (L5.bo_st bX) as [v0 v1|cap q] eqn:E0. exact LAT.
      pose proof (INB cap q eq_refl) as STB. pose proof (proj1 (WB _ STB)) as (Q0 & _ & _ & _ & QCE & _). cbn [fst snd] in Q0, QCE.
      pose proof OB as (_ & _ & _ & OST). rewrite E0 in OST. destruct OST as (_ & _ & _ & Hlc & _).
      eapply (L5C.limbs_at_agree RSEGS M0 M1). 4: exact LAT. 2: clear - Q0; lia. 2:{ rewrite L1. clear - Hlc QCE SPT. lia. }
      intros j Hj. rewrite L1 in Hj. apply KEEP1. clear - Hj Q0 QCE SPT Hlc; lia. clear - Hj QCE SLO Hlc; lia.
Qed.

Lemma uctx_ro (R R1 : bvmap 5 word) (M : word -> option byte) (model model1 : Model) cr1 LK1 A1 :
  uctx R M model cr1 LK1 A1 -> (forall k, In k (2 :: 8 :: 9 :: KSU)%nat -> getr R1 (reg k) = getr R (reg k)) ->
  ri_inv HI LB FF LK1 cr1 A1 M (vml_of model1) -> amodel_ok A1 model1 -> model_rt model model1 -> uctx R1 M model1 cr1 LK1 A1.
Proof.
  intros (HH & AM & RT & IA & ILK & g2 & g8 & g9 & gK & REST) KS HH1 AM1 RT1.
  split. exact HH1. split. exact AM1. split. { eapply L5LZ.model_rt_trans. exact RT. exact RT1. } split. exact IA. split. exact ILK.
  split. { rewrite KS by inl. exact g2. } split. { rewrite KS by inl. exact g8. } split. { rewrite KS by inl. exact g9. }
  split. 2: exact REST. intros k Hk. rewrite KS. apply gK. exact Hk. right; right; right. exact Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_diveq (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr1 : credit) (LK1 : list fframe) (A1 : list (Z * Z)) (b1 : L5.bigobj) (w1 : list Z) :
  uctx R M model cr1 LK1 A1 -> uobj M b1 w1 -> mword_obj M (E - 56) 0 ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R 0x94444 M model) K.
Proof.
  intros CTX UO (MW & _).
  pose proof CTX as (HH & AM & RT & IA & ILK & g2 & g8 & g9 & gK & SV & STK1 & SZX & EK & DK & CRL).
  pose proof sp_rng as (SPR & SLO & SHI & SPT).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK1 cr1 A1 M model HH) as (HOFF & VIS & _).
  set (H := ahid A1 model) in *. set (MV := mrestrict H M) in *.
  assert (W64 : L5.writable RSEGS MV (E - 64) 64).
  { apply (proj2 (writable_vis H M (E - 64) 64 (VIS (E - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M E). exact STK1. rewrite USCR_EQ; clear; lia. clear; lia. clear; lia. }
  assert (TB : L5.u8_at RSEGS MV (E - 56) 0).
  { apply (proj2 (u8_at_vis H M (E - 56) 0 (VIS (E - 56) 1 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))). exact (proj1 MW). }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (A16 : aligned E 16). { unfold aligned. clear - A32. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (TBIT : Z.testbit 0 0 = false) by reflexivity.
  pose proof (L5ANORM.obj_vis L ar C HI LY HIok LB FF LK1 cr1 A1 M model X E HH AOX SZX ltac:(clear - SLO; lia) SPT) as ((XR & _) & _).
  assert (HVX : 0 <= X < 2 ^ 64) by (clear - XR; lia). assert (HVXS : 0 <= xs < 2 ^ 64) by (clear - Hxs; lia).
  destruct (Z_lt_le_dec xs 1) as [X0|X1].
  - (* [comment removed for export] *)
    assert (EX : xs = 0) by (clear - X0 Hxs; lia).
    pose proof (vunBr_conc fx R MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => xs | 36%nat => 0 | 42%nat => U R 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx3 & R3 & M3v & MG3 & eFR & eFZ & (eMS & eKS & eR1 & eR10)).
    apply (apiece_ro L ar C HI LY HIok LB FF LK1 cr1 A1 M model fx fx3 R _ R3 L5ARED.REDUCE M3v K HH AM eMS MG3 eFZ).
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3. pose proof (mem_eq_of_agree M M3 FRM3) as EM. subst M3.
    apply (tail_red fx3 R3 M model3 cr1 LK1 A1 b1 w1). 2: exact UO. 2: exact eR10. 2: exact eR1.
    apply (uctx_ro R R3 M model model3 cr1 LK1 A1 CTX). 2: exact HH3. 2: exact AM3. 2: exact RT3.
    intros k Hk. apply eKS. revert Hk; apply (L5K.incl_b _ KS_vunBr); vm_compute; reflexivity.
  - pose proof (vunBs_conc fx R MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => xs | 36%nat => 0 | 42%nat => U R 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx3 & R3 & M3v & MG3 & eFR & eFZ & (eMS & eKS & eR1 & eR10 & eR11)).
    apply (apiece_ro L ar C HI LY HIok LB FF LK1 cr1 A1 M model fx fx3 R _ R3 L5ASHR.SHR M3v K HH AM eMS MG3 eFZ).
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3. pose proof (mem_eq_of_agree M M3 FRM3) as EM. subst M3.
    apply (tail_shr fx3 R3 M model3 cr1 LK1 A1 b1 w1). 2: exact UO. 2: exact X1. 2: exact eR10. 2: exact eR11. 2: exact eR1.
    apply (uctx_ro R R3 M model model3 cr1 LK1 A1 CTX). 2: exact HH3. 2: exact AM3. 2: exact RT3.
    intros k Hk. apply eKS. revert Hk; apply (L5K.incl_b _ KS_vunBs); vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma uentry : srealizes RSEGS SCFG (cfg (fx:=fx0) R0 UNNORM M0 model0) K.
Proof.
  pose proof sp_rng as (SPR & SLO & SHI & SPT).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M0 model0 HH0) as (HOFF & VIS & _).
  pose proof (L5ANORM.obj_vis L ar C HI LY HIok LB FF LK cr A M0 model0 X E HH0 AOX SZX0 ltac:(clear - SLO; lia) SPT) as ((XR & _) & _).
  assert (HVX : 0 <= X < 2 ^ 64) by (clear - XR; lia). assert (HVXS : 0 <= xs < 2 ^ 64) by (clear - Hxs; lia).
  set (H := ahid A model0) in *. set (MV := mrestrict H M0) in *.
  assert (W64 : L5.writable RSEGS MV (E - 64) 64).
  { apply (proj2 (writable_vis H M0 (E - 64) 64 (VIS (E - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M0 E). exact STK. rewrite USCR_EQ; clear; lia. clear; lia. clear; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (A16 : aligned E 16). { unfold aligned. clear - A32. lia. }
  assert (A32' : (E - 64) mod 32 = 0) by (clear - A32; lia).
  assert (A8' : (E - 56) mod 8 = 0) by (clear - A32; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct Hsd as [SD0|SD1'].
  - (* [comment removed for export] *)
    rewrite SD0 in G13.
    destruct (Z_lt_le_dec xs 1) as [X0|X1].
    + assert (EX : 0 <= xs <= 0) by (clear - X0 Hxs; lia).
      pose proof (vunA0r_conc fx0 R0 MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => xs | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & C24 & C16 & C8)).
      assert (E0 : xs = 0) by (clear - EX; lia). rewrite <- E0 in aR9.
      apply (after_A fx1 R1 M1v L5ARED.REDUCE MG1 aFZ aMS). { intros x Hx. apply aKS. revert Hx; apply (L5K.incl_b _ KS_vunA0r); vm_compute; reflexivity. }
      exact aR2. exact aR8. exact aR9. exact C24. exact C16. exact C8.
      intros M1 model1 CTX1 UO1 _ _ _. apply (tail_red fx1 R1 M1 model1 cr LK A bX wX CTX1 UO1 aR10 aR1).
    + assert (EX : 1 <= xs <= 63) by (clear - X1 Hxs; lia).
      pose proof (vunA0s_conc fx0 R0 MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => xs | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & C24 & C16 & C8)).
      apply (after_A fx1 R1 M1v L5ASHR.SHR MG1 aFZ aMS). { intros x Hx. apply aKS. revert Hx; apply (L5K.incl_b _ KS_vunA0s); vm_compute; reflexivity. }
      exact aR2. exact aR8. exact aR9. exact C24. exact C16. exact C8.
      intros M1 model1 CTX1 UO1 _ _ _. apply (tail_shr fx1 R1 M1 model1 cr LK A bX wX CTX1 UO1 X1 aR10 aR11 aR1).
  - (* [comment removed for export] *)
    rewrite SD1' in G13. destruct (SD1 SD1') as (qX & ESTX & LENX). pose proof (CRD SD1') as CRQ.
    pose proof (vunA1_conc fx0 R0 MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => xs | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR13 & T32 & T40 & T48 & T56 & C24 & C16 & C8)).
    assert (AKS : forall x, In x KSU -> getr R1 (reg x) = getr R0 (reg x)). { intros x Hx. apply aKS. revert Hx; apply (L5K.incl_b _ KS_vunA1); vm_compute; reflexivity. }
    apply (after_A fx1 R1 M1v OPDIV MG1 aFZ aMS AKS aR2 aR8 aR9 C24 C16 C8).
    intros M1 model1 CTX1 UO1 T64 T8 KEEP1.
    pose proof CTX1 as (HH1 & AM1 & RT1 & IA1 & ILK1 & g2 & g8 & g9 & gK & SV1 & STK1 & SZX1 & EK1 & DK1 & CRL1).
    destruct UO1 as (OB1 & OL1 & _ & _).
    assert (MW1 : mword_obj M1 (E - 56) 0).
    { split. 2: reflexivity. unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
      split. apply T8. clear; lia. clear; lia. exact T56. split. clear; lia.
      split. replace (E - 56 + 8) with (E - 48) by (clear; lia). apply T64. clear; lia. clear; lia. exact T48.
      split. reflexivity. split. replace (E - 56 + 16) with (E - 40) by (clear; lia). apply T64. clear; lia. clear; lia. exact T40.
      split. replace (E - 56 + 24) with (E - 32) by (clear; lia). apply T64. clear; lia. clear; lia. exact T32.
      split. clear; Lia.lia. unfold MWORD. split; clear; lia. }
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as WF0.
    assert (TOP : ar_stack_top ar <= 2 ^ 47). { clear - WF0. decompose [and] WF0. assumption. } clear WF0.
    apply (DIVEQ fx1 R1 M1 model1 K LB FF LK cr A X qX (E - 56) 0 (E - 64) 0x94444 bX wX HH1 AM1 HK0).
    + rewrite r10. exact aR10.
    + rewrite r11. exact aR11.
    + rewrite r1. exact aR1.
    + split. clear; lia. reflexivity.
    + rewrite r2. exact g2.
    + exact A32'.
    + rewrite r4, (gK 4%nat ltac:(inl)), <- r4. exact G4.
    + rewrite QSCR_EQ. eapply astk_sub. exact STK1. apply mem_grows_refl. clear; lia. clear; lia. rewrite USCR_EQ; clear; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - A32. lia.
    + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      replace (E - 64 - DIVEQ_SCR) with (E - UNNORM_SCR) by (rewrite USCR_EQ, QSCR_EQ; clear; lia).
      intros j Hj. unfold byte_at. unfold L5OMA.stksh, shadow_zero, byte_at in SSH.
      assert (HB : 0 <= S (E - UNNORM_SCR) + j < 2 ^ 45).
      { unfold S, SB. rewrite USCR_EQ in Hj |- *. set (mx := Z.max (ar_sptop ar) (ar_stack_top ar)) in *.
        assert (MX : mx <= 2 ^ 47) by (subst mx; apply Z.max_lub; [clear - SPT; lia | exact TOP]).
        pose proof (Z.mul_div_le (E - 5328) 8 ltac:(clear; lia)) as D1. pose proof (Z.mul_div_le (mx - (E - 5328)) 8 ltac:(clear; lia)) as D2.
        assert (D0 : 0 <= (E - 5328) / 8) by (apply Z.div_pos; [clear - SPR; lia | clear; lia]).
        clear - Hj MX D1 D2 D0. lia. }
      rewrite KEEP1. apply SSH. exact Hj. clear - HB; lia. clear - HB SPR; lia.
    + exact ROOM1.
    + exact ROOM3.
    + eapply ffrs_le. exact RS. clear; lia.
    + exact OB1.
    + exact OL1.
    + exact ESTX.
    + exact LENX.
    + exact SGN.
    + replace 64 with (8 * 8) by reflexivity. exact (INB 8 qX ESTX).
    + exact AOX.
    + exact SZX1.
    + exact MW1.
    + split. clear; lia. split. clear - SHI; lia. exact A8'.
    + eapply astk_defined. exact STK1. rewrite USCR_EQ; clear; lia. clear; lia.
    + exact CRQ.
    + (* [comment removed for export] *)
      intros fx2 R2 M2 model2 cr2 LK2 A2 POST RT2 IA2 AM2 ILK2 HH2.
      destruct POST as (RP2 & B10 & (fbq & nq & wq & OBq & OLq & SGq & NQ) & MW2 & CRL2 & AHP2). rewrite QSCR_EQ in AHP2.
      assert (CTX2 : uctx R2 M2 model2 cr2 LK2 A2).
      { apply (uctx_after R1 R2 M1 M2 model1 model2 cr cr2 LK LK2 A A2 _ 5264 64 CTX1 RP2 HH2 AM2 RT2 IA2 ILK2 ltac:(clear; lia) ltac:(rewrite USCR_EQ; clear; lia) AHP2).
        - unfold L5.bo_data. rewrite ESTX. intros x Hx. exact Hx.
        - unfold L5.bo_cap. rewrite ESTX. clear; lia.
        - exact OB.
        - exact CRL2. }
      apply (after_diveq fx2 R2 M2 model2 cr2 LK2 A2 (L5.BO fbq nq (L5.BDyn 8 qX)) wq CTX2). 2: exact MW2.
      split. exact OBq. split. exact OLq. split. 2: exact SGq. unfold same_st. cbn [L5.bo_st]. rewrite ESTX. split; reflexivity.
    + (* [comment removed for export] *)
      intros fx3 R3 M3 model3 LB3 cr3 LK3 A3 F1 fl1 F3 fl3 F1c fl1c F1d fl1d E3A RT3 IA3 AM3 ILK3 HH3.
      pose proof E3A as (RN & MN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AHPQ). rewrite QSCR_EQ in AHPQ.
      pose proof (callee_stack LB FF LK cr A M1 model1 M3 [] E UNNORM_SCR 64 5264 X (X + 16) 0 HH1 STK1 ltac:(clear; lia) ltac:(clear; lia) ltac:(rewrite USCR_EQ; clear; lia) AHPQ
                    ltac:(intros x _ rr []) AOX ltac:(left; split; [reflexivity | clear; lia])) as (KQ & _ & STK3).
      apply (KONT3 fx3 R3 M3 model3 qX LB3 cr3 LK3 A3 F1 fl1 F3 fl3 F1c fl1c F1d fl1d SD1' ESTX).
      * exists R1, M1.
        split. { unfold L5DSA.U. change (Z_to_bv 5 1) with (reg 1). rewrite aR1. rewrite L5.unsigned_lit by (clear; lia). reflexivity. }
        split. { unfold L5DSA.U. change (Z_to_bv 5 8) with (reg 8). rewrite aR8. apply L5.unsigned_lit. exact HVX. }
        split. { unfold L5DSA.U. change (Z_to_bv 5 9) with (reg 9). change (Z_to_bv 5 12) with (reg 12). rewrite aR9. rewrite <- r12, G12. reflexivity. }
        split. { intros k Hk. unfold L5DSA.U.
                 assert (KC : k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by (clear - Hk; lia).
                 destruct KC as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]].
                 exact (f_equal bv_unsigned (AKS 18%nat ltac:(inl))). exact (f_equal bv_unsigned (AKS 19%nat ltac:(inl))). exact (f_equal bv_unsigned (AKS 20%nat ltac:(inl))).
                 exact (f_equal bv_unsigned (AKS 21%nat ltac:(inl))). exact (f_equal bv_unsigned (AKS 22%nat ltac:(inl))). exact (f_equal bv_unsigned (AKS 23%nat ltac:(inl))).
                 exact (f_equal bv_unsigned (AKS 24%nat ltac:(inl))). exact (f_equal bv_unsigned (AKS 25%nat ltac:(inl))). exact (f_equal bv_unsigned (AKS 26%nat ltac:(inl))).
                 exact (f_equal bv_unsigned (AKS 27%nat ltac:(inl))). }
        split. { rewrite r3'. apply (AKS 3%nat ltac:(inl)). }
        split. { rewrite r4. apply (AKS 4%nat ltac:(inl)). }
        split. exact E3A.
        destruct SV1 as (S1 & S8 & S9).
        split. { unfold L5DSA.U. change (Z_to_bv 5 1) with (reg 1). eapply L5ANORM.u64_at_agree1. 4: exact S1. intros i Hi. apply KQ. clear - Hi SPR; lia. clear - SPR; lia. clear - SPR; lia. }
        split. { unfold L5DSA.U. change (Z_to_bv 5 8) with (reg 8). eapply L5ANORM.u64_at_agree1. 4: exact S8. intros i Hi. apply KQ. clear - Hi SPR; lia. clear - SPR; lia. clear - SPR; lia. }
        split. { unfold L5DSA.U. change (Z_to_bv 5 9) with (reg 9). eapply L5ANORM.u64_at_agree1. 4: exact S9. intros i Hi. apply KQ. clear - Hi SPR; lia. clear - SPR; lia. clear - SPR; lia. }
        split. { split. 2: reflexivity. eapply L5C.big_at_agree. 4: exact (proj1 MW1). 2: clear - SPR; lia. 2: clear - SPR; lia. intros j Hj. apply KQ. clear - Hj SPR; lia. }
        apply ahpres_of.
        -- eapply ek_trans.
           { apply (ek_piece L ar LB FF E UNNORM_SCR [] M0 M1 (fun a => E - 64 <= a < E)). intros a Ha Hn. apply KEEP1. exact Ha. exact Hn.
             intros a Ha Hc _ Wa. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M0 _ E UNNORM_SCR a HH0 SPT Hc) as [Y|Y]. rewrite USCR_EQ in Y. clear - Wa Y; lia. clear - Wa Y SLO; lia. }
           eapply (ek_callee L ar LB [] FF [] E UNNORM_SCR (E - 64) 5264 [] [] M1 M3). exact AHPQ. rewrite USCR_EQ; clear; lia. clear; lia. intros a _ Ho. exact Ho.
           (* [comment removed for export] *)
        -- eapply astk_defined. exact STK3. clear; lia. clear; lia.
        -- eapply dk_trans. exact DK1. eapply (dk_callee L ar LB [] FF [] E UNNORM_SCR (E - 64) 5264 [] M1 M3). exact AHPQ. rewrite USCR_EQ; clear; lia. clear; lia.
      * eapply L5LZ.model_rt_trans. exact RT1. exact RT3.
      * intros x Hx. apply IA3. apply IA1. exact Hx.
      * exact AM3.
      * intros x Hx. apply ILK1. apply ILK3. exact Hx.
      * exact HH3.
Qed.

End Call.

(* [comment removed for export] *)
Theorem unnorm_okA : unnorm_specA L ar HI.
Proof.
  intros fx R M model K LB FF LK cr A X xs sd E r bX wX HH AM HK G11 G12 Hxs G13 Hsd G1 RA G2 A32 G4 STK SSH ROOM1 ROOM3 RS OB OL Hlen SGN AOX SZX INB SD1 CRD KONT KONT3.
  exact (uentry fx R M model K LB FF LK cr A X xs sd E r bX wX HH AM HK G11 G12 Hxs G13 Hsd G1 RA G2 A32 G4 STK SSH ROOM1 ROOM3 RS OB OL Hlen SGN AOX SZX INB SD1 CRD KONT KONT3).
Qed.
End WithIface.
End SCFG_1.
End L5AUNNORM.
