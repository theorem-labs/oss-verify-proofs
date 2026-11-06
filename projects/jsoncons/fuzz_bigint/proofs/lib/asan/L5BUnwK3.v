(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface BigLinkBase
     AsanAcct L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5DivSpecsAB0 L5UnwindSpecsAB0 L5BDetailG L5BFrameK L5BUnwK L5BUnwK2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AUK3.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5AUK. Import L5AUK2.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition numg (P : Prop) : Prop := P.

(* [comment removed for export] *)
Definition nz (v : Z) : Z := bv_unsigned (Z_to_bv 64 v).
Lemma nz_range v : 0 <= nz v < 2 ^ 64. Proof. unfold nz. apply BL.bvu_range. Qed.
Lemma nz_bv v : Z_to_bv 64 (nz v) = Z_to_bv 64 v. Proof. unfold nz. apply Z_to_bv_bv_unsigned. Qed.
Lemma u64_at_nz M a v : L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M a (nz v).
Proof. unfold L5.u64_at. rewrite nz_bv. exact (fun H => H). Qed.

(* [comment removed for export] *)
Lemma shrun_def M F off n v i : L5DSA.sh_run M F off n v -> off <= i < off + n -> M (Z_to_bv 64 (F / 8 + SB + i)) <> None.
Proof.
  intros H Hi. specialize (H (i - off) ltac:(Lia.lia)). unfold byte_at, S in H. replace (F / 8 + SB + off + (i - off)) with (F / 8 + SB + i) in H by Lia.lia.
  rewrite H. discriminate.
Qed.

(* [comment removed for export] *)
Ltac feed_rng P tac :=
  lazymatch type of P with
  | (0 <= ?v < 2 ^ 64) -> _ =>
      let H := fresh "SC" in
      first [ assert (H : 0 <= v < 2 ^ 64) by tac | fail 1 "feed_rng: cannot prove the range of" v ];
      specialize (P H); clear H; feed_rng P tac
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac expand_arr H n :=
  lazymatch n with
  | O => idtac
  | Datatypes.S ?m => (let X := fresh "FC" in pose proof (H m ltac:(clear; Lia.lia)) as X; cbn [nth] in X; let z := eval vm_compute in (Z.of_nat m) in change (Z.of_nat m) with z in X); expand_arr H m
  end.


(* [comment removed for export] *)
Definition Wpad (F B fl a : Z) : Prop := F <= a < F + 8 \/ F / 8 + SB <= a < F / 8 + SB + B / 8 \/ a = fl.
Lemma Wpad_dec F B fl a : Wpad F B fl a \/ ~ Wpad F B fl a.
Proof.
  unfold Wpad. destruct (rng_dec a F (F + 8)); [left; tauto|]. destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + B / 8)); [left; tauto|].
  destruct (Z.eq_dec a fl); [left; tauto|]. right; tauto.
Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RETIRE.
Variables (M0 : word -> option byte) (model0 : Model) (A0 : list (Z * Z)) (LB : list (Z * Z)) (FF : list fframe) (Sp Scr : Z) (W : list L5.range)
          (F k rs : Z).
Local Notation FF' := ((F, k, rs) :: FF).
Local Notation B := (ff_bytes k).
Local Abbreviation cinv' := (L5AUK.cinv L ar HI M0 model0 A0 LB FF' Sp Scr W).
Local Abbreviation cinv := (L5AUK.cinv L ar HI M0 model0 A0 LB FF Sp Scr W).

Section FACTS.
Variables (XB : list (Z * Z)) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)).
Hypothesis CI : cinv' XB Mc modelc LKc crc Ac.
Hypothesis Hk : In k [1; 2; 3].
Local Notation MV := (mrestrict (ahid Ac modelc) Mc).

(* [comment removed for export] *)
Lemma fr_num : ar_fs ar <= F /\ F + B <= ar_fs ar + FS_BYTES /\ F mod B = 0 /\ 0x634000 <= ar_fs ar /\ ar_fs ar + FS_BYTES <= ahl_ceil ar
               /\ (ar_fs ar + FS_BYTES <= BIGSHADOW_LO \/ BIGSHADOW_HI <= ar_fs ar) /\ ar_fs ar + FS_BYTES <= 2 ^ 47 /\ (B = 128 \/ B = 256 \/ B = 512).
Proof.
  destruct CI as (HH & _). pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF (F, k, rs) ltac:(left; reflexivity)) as (W1 & W2 & W3 & _). cbn [ff_addr ff_class fst snd] in W1, W2, W3.
  rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG. unfold app_mem in FSAPP.
  assert (HB : B = 128 \/ B = 256 \/ B = 512). { destruct Hk as [<-|[<-|[<-|[]]]]; [left | right; left | right; right]; reflexivity. }
  split. exact W1. split. exact W2. split. exact W3. split. unfold FS_BYTES in *. clear - FSAPP FSIMG. lia. split. exact FSCEIL. split. exact (proj1 (proj2 FSAPP)).
  split. exact (proj2 (proj2 FSAPP)). exact HB.
Qed.

(* [comment removed for export] *)
Lemma cv_frame fl : cell_is RSEGS Mc (F + B - 8) 8 fl -> ar_fs ar <= fl < ar_fs ar + FS_BYTES -> L5.defined Mc (F / 8 + SB) (B / 8) ->
  L5.defined MV F B /\ L5.writable RSEGS MV F B /\ L5.writable RSEGS MV (F / 8 + SB) (B / 8) /\ L5.u64_at RSEGS MV (F + B - 8) fl /\ L5.writable RSEGS MV fl 1
  /\ avis (ahid Ac modelc) F B /\ avis (ahid Ac modelc) fl 1.
Proof.
  intros FLC FLP SHD. pose proof fr_num as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB). pose proof CI as (HH & _).
  pose proof (vis_pack L ar C HI LY HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & VFS & _ & _ & VFSSH & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & _).
  pose proof (WF (F, k, rs) ltac:(left; reflexivity)) as (_ & _ & _ & _ & FD & _). cbn [ff_addr ff_class fst snd] in FD.
  assert (FV : avis (ahid Ac modelc) F B) by (apply (VFS F B N1 N2)).
  assert (F8 : F / 8 * 8 = F /\ (F + B - 1) / 8 = F / 8 + B / 8 - 1 /\ B / 8 * 8 = B /\ 0 < B).
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - N3 HB. destruct HB as [E|[E|E]]; rewrite E in *; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SHV : avis (ahid Ac modelc) (F / 8 + SB) (B / 8)).
  { apply (VFSSH (F / 8 + SB) (B / 8)). intros i Hi. unfold in_shadow_of, S.
    pose proof (Z.div_le_mono (ar_fs ar) F 8 ltac:(clear; lia) N1) as X1. pose proof (Z.div_le_mono (F + B - 1) (ar_fs ar + FS_BYTES - 1) 8 ltac:(clear; lia) ltac:(clear - N2; lia)) as X2.
    destruct F8 as (_ & X3 & _). clear - Hi X1 X2 X3. lia. }
  assert (FR : 4096 <= F /\ F + B <= 2 ^ 47) by (clear - N1 N2 N4 N7; lia).
  assert (FDEF : L5.defined MV F B). { apply (proj2 (defined_vis _ Mc F B FV)). exact FD. }
  split. exact FDEF. split. { apply (L5C.writable_of_defined RSEGS). exact FDEF. clear - FR; lia. clear - FR; lia. }
  split. { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis _ Mc _ _ SHV)). exact SHD.
           clear - FR. unfold SB. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
           clear - FR F8. unfold SB. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H. lia. }
  pose proof (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ modelc F k _ _ fl HH HH (or_introl eq_refl) (or_introl eq_refl) Hk FLC) as [_ FL8].
  split. exact FL8.
  pose proof (fl_writable L ar C HI LY HIok _ FF' LKc _ Ac Mc _ fl HH FLP) as [_ FLW].
  pose proof (fl_vis L ar C HI LY HIok _ FF' LKc _ Ac Mc modelc fl HH FLP) as FLV.
  split. { apply (proj2 (writable_vis _ Mc fl 1 FLV ltac:(clear - FLP N4; lia) ltac:(clear - FLP N7; unfold FS_BYTES in *; lia))). exact FLW. }
  split. exact FV. exact FLV.
Qed.

(* [comment removed for export] *)
Lemma cv_fs_u64 a v : ar_fs ar <= a -> a + 8 <= ar_fs ar + FS_BYTES -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v.
Proof.
  intros H1 H2 X. pose proof fr_num as (_ & _ & _ & N4 & _ & _ & N7 & _). destruct CI as (HH & _).
  pose proof (vis_pack L ar C HI LY HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & VFS & _).
  apply (proj2 (u64_at_vis _ Mc a v (VFS a 8 H1 H2) ltac:(clear - H1 N4; lia) ltac:(clear - H2 N7; lia))). exact X.
Qed.
Lemma cv_fs_u8 a v : ar_fs ar <= a -> a + 1 <= ar_fs ar + FS_BYTES -> L5.u8_at RSEGS Mc a v -> L5.u8_at RSEGS MV a v.
Proof.
  intros H1 H2 X. pose proof fr_num as (_ & _ & _ & N4 & _ & _ & N7 & _). destruct CI as (HH & _).
  pose proof (vis_pack L ar C HI LY HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & VFS & _).
  apply (proj2 (u8_at_vis _ Mc a v (VFS a 1 H1 H2) ltac:(clear - H1 N4; lia) ltac:(clear - H2 N7; lia))). exact X.
Qed.
End FACTS.

(* [comment removed for export] *)
Lemma cinv_ek_agree (FFx : list fframe) XB Mc modelc LKc crc Ac a n :
  L5AUK.cinv L ar HI M0 model0 A0 LB FFx Sp Scr W XB Mc modelc LKc crc Ac ->
  0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> aclient L ar LB FFx Sp Scr i /\ L5.outside W i) -> L5C.agree_on M0 Mc a n.
Proof.
  intros (_ & _ & _ & _ & _ & _ & EK & _) H1 H2 HC i Hi. apply EK. destruct (HC i Hi) as [X Y]. split. clear - H1 H2 Hi; lia. split. exact X. exact Y.
Qed.

Lemma cinv_dk_defined (FFx : list fframe) XB Mc modelc LKc crc Ac a n :
  L5AUK.cinv L ar HI M0 model0 A0 LB FFx Sp Scr W XB Mc modelc LKc crc Ac ->
  0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> aclient L ar LB FFx Sp Scr i) -> L5.defined M0 a n -> L5.defined Mc a n.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & DK) H1 H2 HC D i Hi. apply DK. clear - H1 H2 Hi; lia. apply HC. clear - Hi; lia. apply D. exact Hi.
Qed.

(* [comment removed for export] *)
Hypothesis WIMG : forall r a, In r W -> L5.in_rng r a -> 0x10000 <= a < 0x634000 /\ ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Lemma frame_agree XB Mc modelc LKc crc Ac a n :
  cinv' XB Mc modelc LKc crc Ac -> In k [1; 2; 3] -> F <= a -> a + n <= F + B - 8 -> (a + n <= F + 24 \/ F + 32 <= a) -> L5C.agree_on M0 Mc a n.
Proof.
  intros CI Hk H1 H2 H3. pose proof (fr_num XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB). unfold FS_BYTES in *.
  apply (cinv_ek_agree FF' XB Mc modelc LKc crc Ac a n CI). clear - H1 N1 N4; lia. clear - H2 N2 N7; lia.
  intros i Hi. split. apply (fframe_client L ar LB FF' Sp Scr F k rs). left; reflexivity. clear - Hi H1 H2 H3; lia.
  intros r Hr X. destruct (WIMG r i Hr X) as (Y & _). clear - Y Hi H1 N1 N4. lia.
Qed.
Lemma frame_shadow_defined XB Mc modelc LKc crc Ac :
  cinv' XB Mc modelc LKc crc Ac -> In k [1; 2; 3] -> L5.defined M0 (F / 8 + SB) (B / 8) -> L5.defined Mc (F / 8 + SB) (B / 8).
Proof.
  intros CI Hk D. pose proof (fr_num XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB). unfold FS_BYTES in *.
  assert (F8 : (F + B - 1) / 8 = F / 8 + B / 8 - 1 /\ 0 <= F / 8 /\ F / 8 + B / 8 <= 17592186044416).
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - N1 N2 N3 N4 N7 HB. destruct HB as [E|[E|E]]; rewrite E in *; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (cinv_dk_defined FF' XB Mc modelc LKc crc Ac _ _ CI). unfold SB; clear - F8; lia. unfold SB; clear - F8; lia. 2: exact D.
  intros i Hi. apply (fframe_shadow_client L ar LB FF' Sp Scr F k rs). left; reflexivity. unfold in_shadow_of, S. rewrite (proj1 F8). clear - Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma cinv_retire XB Mc modelc LKc crc Ac (fx fx9 : FPState) Rc (pc : Z) R9 (pc9 : Z) (M9v : word -> option byte) (Wp : Z -> Prop) fl K :
  cinv' XB Mc modelc LKc crc Ac -> 0 <= Scr -> In k [1; 2; 3] ->
  cell_is RSEGS Mc (F + B - 8) 8 fl -> ar_fs ar <= fl < ar_fs ar + FS_BYTES -> ~ aclient L ar LB FF' 0 0 fl ->
  msteps RSEGS (st fx Rc pc (mrestrict (ahid Ac modelc) Mc)) (st fx9 R9 pc9 M9v) -> mem_grows (mrestrict (ahid Ac modelc) Mc) M9v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M9v (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
  (forall a, Wp a -> F <= a < F + 8 \/ F / 8 + SB <= a < F / 8 + SB + B / 8 \/ a = fl \/ Sp - Scr <= a < Sp) -> (forall a, Wp a \/ ~ Wp a) ->
  L5.u8_at RSEGS M9v fl 0 ->
  (forall M9 model9,
      cinv XB M9 model9 LKc crc Ac -> ahid Ac model9 = ahid Ac modelc -> mrestrict (ahid Ac model9) M9 = M9v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M9 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx9) R9 pc9 M9 model9) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc pc Mc modelc) K.
Proof.
  intros CI HS0 Hk FLC FLP FLNC MS MG FZ WP WD FL0 KONT.
  pose proof (fr_num XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB).
  pose proof (L5AUK.cinv_num L ar HI M0 model0 A0 LB FF' Sp Scr W _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
  pose proof (L5AUK.cinv_top L ar C HI HIok M0 model0 A0 LB FF' Sp Scr W _ _ _ _ _ _ CI) as STOP.
  pose proof CI as (HH & AM & RT & IA & STK & SH & EK & DK).
  unfold BIGSHADOW_LO, BIGSHADOW_HI in N6. unfold FS_BYTES in *.
  assert (F8 : F / 8 * 8 = F /\ (F + B - 1) / 8 = F / 8 + B / 8 - 1 /\ B / 8 * 8 = B /\ 0 < B /\ 64 <= B).
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - N3 HB. destruct HB as [E|[E|E]]; rewrite E in *; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct F8 as (F8a & F8b & F8c & B0 & B64).
  assert (FLNC8 : ~ aclient L ar (XB ++ LB) FF' 0 0 fl).
  { apply (not_client_bx L ar FF' fl XB LB). apply (blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ XB LB HH eq_refl). unfold FS_BYTES. exact FLP. clear - FLP N6; lia. exact FLNC. }
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  pose proof (WF (F, k, rs) ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & FAP). cbn [ff_addr ff_class fst snd ff_remove] in FAP. rewrite Z.eqb_refl in FAP.
  (* [comment removed for export] *)
  assert (NK : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF Sp Scr a -> ~ Wp a).
  { intros a Ha Hc Wa.
    destruct (sm_apart L ar C HI LY HIok (XB ++ LB) FF LKc crc Ac Mc _ F k rs fl Sp Scr a 1 HH SPT Hk ltac:(clear - N1 N4; lia) ltac:(clear - N2 N5; lia)
                ltac:(unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI; clear - N1 N2 N4 N6 N7; lia) N3 FAP) as (X1 & X2 & X3).
    - intros b Hb. destruct (WB b Hb) as (_ & _ & _ & _ & _ & FA & _). specialize (FA (F, k, rs) ltac:(apply in_or_app; left; left; reflexivity)). cbn [ff_addr ff_class fst snd] in FA. clear - FA. lia.
    - exact FLNC8.
    - intros i Hi. replace (a + i) with a by (clear - Hi; lia). apply aclient_appb. exact Hc.
    - clear; lia.
    - destruct (WP a Wa) as [Y|[Y|[Y|Y]]].
      + clear - X1 Y B64. lia.
      + clear - X2 Y. lia.
      + clear - X3 Y. lia.
      + destruct (aclient_cases L ar C HI LY HIok (XB ++ LB) FF' LKc crc Ac Mc _ Sp Scr a HH SPT (aclient_appb L ar LB XB FF' Sp Scr a (aclient_cons L ar LB FF (F, k, rs) Sp Scr a Hc))) as [Z0|Z0].
        clear - Z0 Y; lia. clear - Z0 Y SLO HS0; lia. }
  apply (apiece_retire L ar C HI LY HIok (XB ++ LB) FF LKc crc Ac Mc modelc fx fx9 Rc pc R9 pc9 M9v Wp F k rs fl K HH AM FLC FLNC8).
  { exact (fl_vis L ar C HI LY HIok _ FF' LKc _ Ac Mc modelc fl HH FLP). }
  { clear - FLP N4 N7; lia. }
  { exact MS. } { exact MG. } { exact FZ. }
  { intros a Ha Wa. destruct (WP a Wa) as [Y|[Y|[Y|Y]]].
    - right. apply (fframe_client L ar (XB ++ LB) FF' 0 0 F k rs). left; reflexivity. clear - Y B64; lia.
    - right. apply (fframe_shadow_client L ar (XB ++ LB) FF' 0 0 F k rs). left; reflexivity. unfold in_shadow_of, S. rewrite F8b. clear - Y. lia.
    - left; exact Y.
    - right. apply stack_client. clear - Y SLO SHI SPT HS0; lia. clear; lia. }
  { exact WD. } { exact FL0. }
  intros M9 model9 HH9 AM9 RT9 AH9 VIS9 MGM9 FRM9 EQ9.
  apply (KONT M9 model9).
  - unfold L5AUK.cinv. split. exact HH9. split. exact AM9. split. eapply L5LZ.model_rt_trans. exact RT. exact RT9. split. exact IA.
    split. eapply astk_grows. exact STK. exact MGM9.
    split. { intros j Hj. unfold byte_at. rewrite FRM9. apply SH. exact Hj.
             pose proof (L5AUK.stksh_range ar (Sp - Scr) j ltac:(clear - SLO SPT; lia) Hj ltac:(clear - SPT; lia) STOP) as RG. clear - RG; lia.
             intros Wa. pose proof (L5AUK.stksh_range ar (Sp - Scr) j ltac:(clear - SLO SPT; lia) Hj ltac:(clear - SPT; lia) STOP) as RG.
             destruct (WP _ Wa) as [Y|[Y|[Y|Y]]].
             - clear - Y RG N1 N2 N4 N5 N6 B64. lia.
             - assert (X : F / 8 + B / 8 <= ahl_ceil ar / 8). { rewrite <- (Z.div_add F (B / 8) 8 ltac:(clear; lia)). rewrite F8c. apply Z.div_le_mono. clear; lia. clear - N2 N5; lia. }
               assert (X2 : ahl_ceil ar / 8 <= (Sp - Scr) / 8) by (apply Z.div_le_mono; [clear; lia | clear - SLO HS0; lia]).
               unfold S in Y, RG |- *. clear - Y X X2 RG Hj. lia.
             - clear - Y RG FLP N4 N5 N6. lia.
             - clear - Y RG SLO SPT HS0. lia. }
    split. { eapply ek_trans. { intros a (Ha & Hc & Ho). apply EK. split. exact Ha. split. apply aclient_cons. exact Hc. exact Ho. }
             intros a (Ha & Hc & Ho). apply FRM9. exact Ha. exact (NK a Ha Hc). }
    eapply dk_trans. { intros a Ha Hc D. apply DK. exact Ha. apply aclient_cons. exact Hc. exact D. } apply dk_grows. exact MGM9.
  - exact AH9.
  - rewrite AH9. exact VIS9.
  - exact FRM9.
Qed.

(* [comment removed for export] *)
Lemma pad_agree XB Mc modelc LKc crc Ac fl (M9 : word -> option byte) :
  cinv' XB Mc modelc LKc crc Ac -> In k [1; 2; 3] -> ar_fs ar <= fl < ar_fs ar + FS_BYTES ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wpad F B fl a -> M9 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  forall a n, 0 <= a -> a + n <= 2 ^ 64 -> L5AUK.cvis ar LB XB a n -> L5C.agree_on Mc M9 a n.
Proof.
  intros CI Hk FLP FRM a n Ha Hn CV i Hi.
  pose proof (fr_num XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB).
  pose proof (L5AUK.cinv_num L ar HI M0 model0 A0 LB FF' Sp Scr W _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
  destruct CI as (HH & _). pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  unfold BIGSHADOW_LO, BIGSHADOW_HI in N6. unfold FS_BYTES in *.
  assert (D : 0 <= F / 8 /\ F / 8 + B / 8 <= 17592186044416).
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - N1 N2 N4 N7 HB. destruct HB as [E|[E|E]]; rewrite E in *; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (B64 : 64 <= B) by (clear - HB; destruct HB as [E|[E|E]]; rewrite E; lia).
  apply FRM. clear - Ha Hn Hi; lia. unfold Wpad, SB. intros Wa.
  destruct CV as [[X1 X2]|[[X1 X2]|(q & m & Hin & X1 & X2)]].
  - clear - Wa Hi X1 N1 N2 N5 FLP SPT D B64. lia.
  - clear - Wa Hi X1 X2 N1 N4 FLP D B64. lia.
  - destruct (WB (q, m) Hin) as (BR & _ & _ & _ & _ & _ & BFS). cbn [fst snd] in BR, BFS. destruct BR as (_ & _ & _ & _ & _ & BAPP).
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BAPP. clear - Wa Hi X1 X2 N1 N2 FLP D BFS BAPP B64. lia.
Qed.

End RETIRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma leak_filter F k rs (FFr : list fframe)
      (H : forall x : fframe, base.Decision (Is_true (negb (existsb (fun g => Z.eqb (ff_addr g) (ff_addr x)) [(F, k, rs)])))) : ~ In F (map ff_addr FFr) ->
  @base.filter fframe (list fframe) (@list_basics.list.list_filter fframe)
     (fun f => Is_true (negb (existsb (fun g => Z.eqb (ff_addr g) (ff_addr f)) [(F, k, rs)]))) H ((F, k, rs) :: FFr) = FFr.
Proof.
  intros NI. rewrite list_basics.list.filter_cons_False. 2:{ simpl. rewrite Z.eqb_refl. simpl. intros []. }
  induction FFr as [|g FFr IH]. reflexivity. simpl in NI.
  rewrite list_basics.list.filter_cons_True. f_equal. apply IH. intros X. apply NI. right. exact X.
  simpl. change (ff_addr (F, k, rs)) with F. destruct (Z.eqb_spec F (ff_addr g)) as [E|E]. exfalso. apply NI. left. symmetry. exact E. exact I.
Qed.
Lemma cinv_leak M0 model0 A0 LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac :
  L5AUK.cinv L ar HI M0 model0 A0 LB ((F, k, rs) :: FFr) Sp Scr W XB Mc modelc LKc crc Ac ->
  L5AUK.cinv L ar HI M0 model0 A0 LB FFr Sp Scr W XB Mc modelc ((F, k, rs) :: LKc) crc Ac.
Proof.
  intros (HH & AM & RT & IA & STK & SH & EK & DK).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WFX. do 11 apply proj2 in WFX. destruct WFX as (ND & _).
  assert (NI : ~ In F (map ff_addr FFr)).
  { cbn [app map] in ND. change (ff_addr (F, k, rs)) with F in ND. apply list_relations.list.NoDup_cons in ND. destruct ND as [X _]. intros Y. apply X.
    apply base.list_elem_of_In. rewrite map_app. apply in_or_app. left. exact Y. }
  pose proof (aio_leak _ _ _ _ _ HIok _ _ _ _ _ _ _ [(F, k, rs)] HH ltac:(intros x [<-|[]]; left; reflexivity) ltac:(apply list_relations.list.NoDup_singleton)) as HL.
  rewrite (leak_filter F k rs FFr _ NI) in HL. cbn [app] in HL.
  split. exact HL. split. exact AM. split. exact RT. split. exact IA. split. exact STK. split. exact SH.
  split. { intros a (Ha & Hc & Ho). apply EK. split. exact Ha. split. apply aclient_cons. exact Hc. exact Ho. }
  intros a Ha Hc X. apply DK. exact Ha. apply aclient_cons. exact Hc. exact X.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_split q n (X1 X2 : list (Z * Z)) : ~ In q (map fst X1) -> lb_remove q (X1 ++ (q, n) :: X2) = X1 ++ X2.
Proof.
  intros NI. induction X1 as [|[p m] X1 IH]. cbn [app lb_remove fst]. rewrite Z.eqb_refl. reflexivity.
  cbn [app lb_remove fst]. cbn [map In fst] in NI. destruct (Z.eqb_spec p q) as [E|E]. exfalso. apply NI. left. exact E.
  f_equal. apply IH. intros Y. apply NI. right. exact Y.
Qed.
Lemma cinv_opdel M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac (fx : FPState) R q n sp' r K :
  L5CSA.opdel_sized_spec L ar HI ->
  L5AUK.cinv L ar HI M0 model0 A0 LB FF Sp Scr W XB Mc modelc LKc crc Ac -> K [] -> 0 <= Scr ->
  In (q, n) XB -> getr R (reg 10) = Z_to_bv 64 q -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  sp' mod 16 = 0 -> Sp - Scr <= sp' - L5CSA.OPDEL_SCR -> sp' <= Sp ->
  (forall (fx' : FPState) R' M' model' A',
      regs_preserved R R' -> L5AUK.cinv L ar HI M0 model0 A0 LB FF Sp Scr W (lb_remove q XB) M' model' LKc crc A' ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (lb_remove q XB ++ LB) FF sp' L5CSA.OPDEL_SCR a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R L5CSA.OPDEL_SIZED Mc modelc) K.
Proof.
  intros HD CI HK HS0 Hin G10 G1 RA G2 G4 A16' HLO HHI KONT. pose proof CI as (HH & AM & RT & IA & STK & SH & EK & DK).
  pose proof (L5AUK.cinv_num L ar HI M0 model0 A0 LB FF Sp Scr W _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
  pose proof (L5AUK.cinv_top L ar C HI HIok M0 model0 A0 LB FF Sp Scr W _ _ _ _ _ _ CI) as STOP.
  assert (SCR0 : 0 <= L5CSA.OPDEL_SCR) by (unfold L5CSA.OPDEL_SCR, L5CSA.MALLOC_SCR; clear; lia).
  assert (RME : lb_remove q (XB ++ LB) = lb_remove q XB ++ LB).
  { apply L5AUK.lb_remove_app_in. apply in_map_iff. exists (q, n). split. reflexivity. exact Hin. }
  unfold cfg.
  apply (HD fx R Mc modelc K (XB ++ LB) FF LKc crc Ac q n sp' r HH AM HK).
  - apply in_or_app. left. exact Hin.
  - rewrite r10. exact G10.
  - rewrite r1. exact G1.
  - exact RA.
  - rewrite r2. exact G2.
  - rewrite r4. exact G4.
  - replace sp' with (Sp - (Sp - sp')) by (clear; lia). apply (astk_sub ar Mc Mc Sp Scr (Sp - sp') L5CSA.OPDEL_SCR STK (mem_grows_refl Mc)).
    clear - HHI; lia. exact SCR0. clear - HLO; lia. replace (Sp - (Sp - sp')) with sp' by (clear; lia). exact A16'.
  - intros fx' R' M' model' A' RP (PK & PD & PDK) RT2 IA2 AM2 HH2. rewrite RME in PK, PDK, HH2.
    assert (PRES : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (lb_remove q XB ++ LB) FF sp' L5CSA.OPDEL_SCR a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
    { intros a Ha Hc. apply PK. split. exact Ha. split. exact Hc. intros rr []. }
    apply (KONT fx' R' M' model' A' RP).
    + unfold L5AUK.cinv. split. exact HH2. split. exact AM2. split. eapply L5LZ.model_rt_trans. exact RT. exact RT2.
      split. { intros x Hx. apply IA2. apply IA. exact Hx. }
      split. { apply (astk_after_eq L ar C HI HIok (XB ++ LB) FF LKc crc Ac Mc Mc M' _ Sp Scr sp' L5CSA.OPDEL_SCR HH STK (mem_grows_refl Mc)).
               - intros a Ha Hs Hns. apply PRES. exact Ha. apply stack_client. exact Hs. exact Hns.
               - intros a Ha. replace a with (sp' - L5CSA.OPDEL_SCR + (a - (sp' - L5CSA.OPDEL_SCR))) by (clear; lia). apply PD. clear - Ha; lia.
               - exact HLO.
               - exact HHI.
               - exact HS0. }
      split. { intros j Hj. unfold byte_at. rewrite PRES. apply SH. exact Hj.
               pose proof (L5AUK.stksh_range ar (Sp - Scr) j ltac:(clear - SLO SPT; lia) Hj ltac:(clear - SPT; lia) STOP) as RG. clear - RG; lia.
               apply L5AUK.stksh_client. clear - SLO HS0; lia. exact Hj. clear - SPT; lia. exact STOP. }
      assert (AHP : ahpres L ar (lb_remove q XB ++ LB) ([] ++ FF) sp' L5CSA.OPDEL_SCR [] Mc M') by (split; [exact PK | split; [exact PD | exact PDK]]).
      split. { eapply ek_trans. exact EK. apply (ek_callee L ar LB (lb_remove q XB) FF [] Sp Scr sp' L5CSA.OPDEL_SCR W [] Mc M' AHP HLO HHI). intros a _ _ rr []. }
      eapply dk_trans. exact DK. apply (dk_callee L ar LB (lb_remove q XB) FF [] Sp Scr sp' L5CSA.OPDEL_SCR [] Mc M' AHP HLO HHI).
    + exact PRES.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ACC.
Variables (M : word -> option byte) (model : Model) (A : list (Z * Z)) (LB : list (Z * Z)) (Sp Scr : Z) (W : list L5.range).
Hypothesis WIMG : forall r a, In r W -> L5.in_rng r a -> 0x10000 <= a < 0x634000 /\ ~ hl_rt_static L a /\ ~ hl_rt_ro L a.

Definition acc (FFa : list fframe) (Mb : word -> option byte) (modelb : Model) (Ab : list (Z * Z)) : Prop :=
  ek L ar LB FFa Sp Scr W M Mb /\ dk L ar LB FFa Sp Scr M Mb /\ model_rt model modelb /\ incl A Ab.
Lemma acc_init FFa : acc FFa M model A.
Proof. split. intros a _; reflexivity. split. intros a _ _ X; exact X. split. apply L5AUK.model_rt_refl. apply incl_refl. Qed.
Definition sufl (FFs FFb : list fframe) : Prop := forall sp scr a, aclient L ar LB FFs sp scr a -> aclient L ar LB FFb sp scr a.
Lemma sufl_app FX FF : sufl FF (FX ++ FF). Proof. intros sp scr a H. apply aclient_app. exact H. Qed.
Lemma sufl_refl FF : sufl FF FF. Proof. intros sp scr a H. exact H. Qed.
Lemma acc_weaken FFa FFb Mb modelb Ab : acc FFa Mb modelb Ab -> sufl FFb FFa -> acc FFb Mb modelb Ab.
Proof.
  intros (E & D & RT & IA) SU. split. intros a (Ha & Hc & Ho). apply E. split. exact Ha. split. apply SU. exact Hc. exact Ho.
  split. intros a Ha Hc X. apply D. exact Ha. apply SU. exact Hc. exact X. split. exact RT. exact IA.
Qed.
(* [comment removed for export] *)
Lemma acc_step FFa FFx Mb modelb Ab XB Mc modelc LKc crc Ac :
  acc FFa Mb modelb Ab -> sufl FFa FFx -> L5AUK.cinv L ar HI Mb modelb Ab LB FFx Sp Scr W XB Mc modelc LKc crc Ac -> acc FFa Mc modelc Ac.
Proof.
  intros (E & D & RT & IA) SU (_ & _ & RT' & IA' & _ & _ & EK & DK).
  split. { eapply ek_trans. exact E. intros a (Ha & Hc & Ho). apply EK. split. exact Ha. split. apply SU. exact Hc. exact Ho. }
  split. { eapply dk_trans. exact D. intros a Ha Hc X. apply DK. exact Ha. apply SU. exact Hc. exact X. }
  split. eapply L5LZ.model_rt_trans. exact RT. exact RT'. intros x Hx. apply IA'. apply IA. exact Hx.
Qed.
(* [comment removed for export] *)
Lemma acc_agree FFa FFx Mb modelb Ab XB Mc modelc LKc crc Ac a n :
  acc FFa Mb modelb Ab -> sufl FFa FFx -> L5AUK.cinv L ar HI Mb modelb Ab LB FFx Sp Scr W XB Mc modelc LKc crc Ac ->
  0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> aclient L ar LB FFa Sp Scr i /\ L5.outside W i) -> L5C.agree_on M Mc a n.
Proof.
  intros AC SU CI H1 H2 HC i Hi. destruct (acc_step FFa FFx Mb modelb Ab XB Mc modelc LKc crc Ac AC SU CI) as (E & _).
  apply E. destruct (HC i Hi) as [X Y]. split. clear - H1 H2 Hi; lia. split. exact X. exact Y.
Qed.
Lemma acc_defined FFa FFx Mb modelb Ab XB Mc modelc LKc crc Ac a n :
  acc FFa Mb modelb Ab -> sufl FFa FFx -> L5AUK.cinv L ar HI Mb modelb Ab LB FFx Sp Scr W XB Mc modelc LKc crc Ac ->
  0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> aclient L ar LB FFa Sp Scr i) -> L5.defined M a n -> L5.defined Mc a n.
Proof.
  intros AC SU CI H1 H2 HC D i Hi. destruct (acc_step FFa FFx Mb modelb Ab XB Mc modelc LKc crc Ac AC SU CI) as (_ & DK & _).
  apply DK. clear - H1 H2 Hi; lia. apply HC. clear - Hi; lia. apply D. exact Hi.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma frame_not_client LBx F k rs FFr LK cr Ax Mx V sp scr a :
  ri_inv HI LBx ((F, k, rs) :: FFr) LK cr Ax Mx V -> In k [1; 2; 3] -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 ->
  (F <= a < F + ff_bytes k \/ S F <= a <= S (F + ff_bytes k - 1)) -> ~ aclient L ar LBx FFr sp scr a.
Proof.
  intros HH Hk SPT Hx Hc. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF (F, k, rs) ltac:(left; reflexivity)) as (W1 & W2 & W3 & _ & _ & FA). cbn [ff_addr ff_class fst snd ff_remove] in W1, W2, W3, FA. rewrite Z.eqb_refl in FA.
  rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *. unfold S, SB in Hx.
  assert (HB : ff_bytes k = 128 \/ ff_bytes k = 256 \/ ff_bytes k = 512). { destruct Hk as [<-|[<-|[<-|[]]]]; [left | right; left | right; right]; reflexivity. }
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as (b & Hb & X). destruct (WB b Hb) as ((Y0 & _ & _ & _ & Y & Y2) & _ & _ & _ & _ & FB & BFS). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2.
    specialize (FB (F, k, rs) ltac:(apply in_or_app; left; left; reflexivity)). cbn [ff_addr ff_class fst snd] in FB. destruct HB as [E|[E|E]]; rewrite E in *; lia.
  - destruct HB as [E|[E|E]]; rewrite E in *; lia.
  - rewrite (aly_img_hi L C LY) in Hc. destruct HB as [E|[E|E]]; rewrite E in *; lia.
  - destruct Hc as (f & Hf & X). pose proof (WF f (or_intror Hf)) as (Y1 & Y & _). specialize (FA f (in_or_app _ _ _ (or_introl Hf))). destruct HB as [E|[E|E]]; rewrite E in *; lia.
  - unfold in_shadow_of, S, SB in Hc. destruct HB as [E|[E|E]]; rewrite E in *; lia.
  - destruct Hc as (f & Hf & X). pose proof (WF f (or_intror Hf)) as (Y1 & Y & Y3 & Y4 & _). specialize (FA f (in_or_app _ _ _ (or_introl Hf))). unfold in_shadow_of, S, SB in X.
    assert (Y5 : ff_bytes (ff_class f) = 128 \/ ff_bytes (ff_class f) = 256 \/ ff_bytes (ff_class f) = 512). { destruct Y4 as [<-|[<-|[<-|[]]]]; [left | right; left | right; right]; reflexivity. }
    destruct HB as [E|[E|E]]; rewrite E in *; destruct Y5 as [E5|[E5|E5]]; rewrite E5 in *; lia.
  - destruct Hc as (b & Hb & X). destruct (WB b Hb) as ((Y0 & _ & Y1 & _ & Y & Y2) & _ & _ & _ & _ & FB & _). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2.
    specialize (FB (F, k, rs) ltac:(apply in_or_app; left; left; reflexivity)). cbn [ff_addr ff_class fst snd] in FB. unfold in_shadow_of, S, SB in X.
    destruct HB as [E|[E|E]]; rewrite E in *; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma cinv_piece_rebase FFa Mb modelb Ab F k rs FFr XB Mc modelc LKc crc Ac (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) (M1v : word -> option byte) (Wp : Z -> Prop) K :
  acc FFa Mb modelb Ab -> sufl FFr FFa ->
  L5AUK.cinv L ar HI Mb modelb Ab LB ((F, k, rs) :: FFr) Sp Scr W XB Mc modelc LKc crc Ac -> 0 <= Scr -> In k [1; 2; 3] ->
  msteps RSEGS (st fx R pc (mrestrict (ahid Ac modelc) Mc)) (st fx1 R1 pc1 M1v) -> mem_grows (mrestrict (ahid Ac modelc) Mc) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1v (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
  (forall a, Wp a -> L5AUK.cfoot Sp Scr W XB a \/ (F <= a < F + ff_bytes k - 8 /\ ~ (F + 24 <= a < F + 32)) \/ F / 8 + SB <= a < F / 8 + SB + ff_bytes k / 8) ->
  (forall M1 model1,
      acc FFr M1 model1 Ac ->
      L5AUK.cinv L ar HI M1 model1 Ac LB ((F, k, rs) :: FFr) Sp Scr W XB M1 model1 LKc crc Ac ->
      ahid Ac model1 = ahid Ac modelc -> mrestrict (ahid Ac model1) M1 = M1v -> mem_grows Mc M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R pc Mc modelc) K.
Proof.
  intros AC SU CI HS0 Hk MS MG FZ WP KONT.
  pose proof (fr_num Mb modelb Ab LB FFr Sp Scr W F k rs XB Mc modelc LKc crc Ac CI Hk) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & HB).
  pose proof (L5AUK.cinv_num L ar HI Mb modelb Ab LB ((F, k, rs) :: FFr) Sp Scr W _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
  pose proof (L5AUK.cinv_top L ar C HI HIok Mb modelb Ab LB ((F, k, rs) :: FFr) Sp Scr W _ _ _ _ _ _ CI) as STOP.
  pose proof CI as (HH & AM & RT & IA & STK & SH & EK & DK).
  unfold BIGSHADOW_LO, BIGSHADOW_HI in N6. unfold FS_BYTES in *.
  assert (F8 : (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1 /\ ff_bytes k / 8 * 8 = ff_bytes k /\ 64 <= ff_bytes k /\ 0 <= F / 8 /\ F / 8 + ff_bytes k / 8 <= 17592186044416).
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - N1 N2 N3 N4 N7 HB. destruct HB as [E|[E|E]]; rewrite E in *; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct F8 as (F8b & F8c & B64 & D0 & D1).
  apply (L5AUK.apiece_x L ar C HI LY HIok (XB ++ LB) ((F, k, rs) :: FFr) LKc crc Ac Mc modelc fx fx1 R pc R1 pc1 M1v Wp K HH AM MS MG FZ).
  { intros a Ha Wa. destruct (WP a Wa) as [Y|[Y|Y]].
    - exact (L5AUK.cfoot_client L ar C HI LY HIok Mb modelb Ab LB ((F, k, rs) :: FFr) Sp Scr W WIMG XB Mc modelc LKc crc Ac a CI HS0 Y).
    - split. apply (fframe_client L ar (XB ++ LB) _ 0 0 F k rs). left; reflexivity. exact Y.
      intros X. pose proof (aly_ro_img L C LY a X) as Z0. clear - Z0 Y N1 N4. lia.
    - split. apply (fframe_shadow_client L ar (XB ++ LB) _ 0 0 F k rs). left; reflexivity. unfold in_shadow_of, S. rewrite F8b. clear - Y. lia.
      intros X. pose proof (aly_ro_img L C LY a X) as Z0. unfold SB in Y. clear - Z0 Y D0. lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1.
  assert (NK : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FFr Sp Scr a -> L5.outside W a -> ~ Wp a).
  { intros a Ha Hc Ho Wa. destruct (WP a Wa) as [Y|[Y|Y]].
    - exact (L5AUK.cfoot_not_kept L ar C HI LY HIok Mb modelb Ab LB ((F, k, rs) :: FFr) Sp Scr W XB Mc modelc LKc crc Ac a CI (aclient_cons L ar LB FFr (F, k, rs) Sp Scr a Hc) Ho Y).
    - apply (frame_not_client (XB ++ LB) F k rs FFr LKc crc Ac Mc _ Sp Scr a HH Hk SPT). left. clear - Y; lia. apply aclient_appb. exact Hc.
    - apply (frame_not_client (XB ++ LB) F k rs FFr LKc crc Ac Mc _ Sp Scr a HH Hk SPT). right. unfold S. rewrite F8b. clear - Y. lia. apply aclient_appb. exact Hc. }
  apply (KONT M1 model1).
  - destruct (acc_step FFr ((F, k, rs) :: FFr) Mb modelb Ab XB Mc modelc LKc crc Ac (acc_weaken FFa FFr Mb modelb Ab AC SU)
                ltac:(intros sp scr a H; apply aclient_cons; exact H) CI) as (E & D & RT0 & IA0).
    split. { eapply ek_trans. exact E. intros a (Ha & Hc & Ho). apply FRM1. exact Ha. exact (NK a Ha Hc Ho). }
    split. { eapply dk_trans. exact D. apply dk_grows. exact MGM1. }
    split. eapply L5LZ.model_rt_trans. exact RT0. exact RT1. exact IA0.
  - apply (L5AUK.cinv_init L ar HI M1 model1 Ac LB ((F, k, rs) :: FFr) Sp Scr W XB LKc crc HH1 AM1).
    + eapply astk_grows. exact STK. exact MGM1.
    + intros j Hj. unfold byte_at. rewrite FRM1. apply SH. exact Hj.
      pose proof (L5AUK.stksh_range ar (Sp - Scr) j ltac:(clear - SLO SPT; lia) Hj ltac:(clear - SPT; lia) STOP) as RG. clear - RG; lia.
      intros Wa. pose proof (L5AUK.stksh_range ar (Sp - Scr) j ltac:(clear - SLO SPT; lia) Hj ltac:(clear - SPT; lia) STOP) as RG.
      destruct (WP _ Wa) as [Y|[Y|Y]].
      * exact (L5AUK.cfoot_not_stksh L ar C HI LY HIok Mb modelb Ab LB ((F, k, rs) :: FFr) Sp Scr W WIMG XB Mc modelc LKc crc Ac j CI HS0 Hj Y).
      * clear - Y RG N1 N2 N4 N5 N6 B64. lia.
      * assert (X : F / 8 + ff_bytes k / 8 <= ahl_ceil ar / 8). { rewrite <- (Z.div_add F (ff_bytes k / 8) 8 ltac:(clear; lia)). rewrite F8c. apply Z.div_le_mono. clear; lia. clear - N2 N5; lia. }
        assert (X2 : ahl_ceil ar / 8 <= (Sp - Scr) / 8) by (apply Z.div_le_mono; [clear; lia | clear - SLO HS0; lia]).
        unfold S in Y, RG |- *. clear - Y X X2 RG Hj. lia.
  - exact AH1.
  - rewrite AH1. exact VIS1.
  - exact MGM1.
  - exact FRM1.
Qed.
End ACC.

End WithIface.
End SCFG_1.
End L5AUK3.
