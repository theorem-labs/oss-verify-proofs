(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg AgentLib AsanAcct AsanAcctShape SpinAlg Hoare Frame RefMemcpyLib.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArg AsanNodesArgSound MallocDefs EnframeArith ImgParams MallocSpec MallocNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section KLemmas.
  Context {fx : FPState}.
  Variable SEGS : list Segment.

  Lemma kreadZ_rdn : forall E M k b off n z,
    know_ok SEGS E M k -> kreadZ SEGS k b off n = Some z -> (1 <= n <= 8)%nat ->
    flat E (SA b off) (Z.of_nat n) ->
    rdn SEGS M (adenot E (SA b off)) n = Some (word_to_le_bytes n (Z_to_bv 64 z)) /\ 0 <= z < 2 ^ (8 * Z.of_nat n) /\ z < two64.
  Proof.
    intros E M k b off n z HK H Hn Hfl. unfold kreadZ in H.
    pose proof (know_lookup_sound SEGS E M k b off n false [] [] HK ltac:(lia) ltac:(lia)) as Hs.
    destruct (know_lookup SEGS k b off n false [] []) as [v scs h|scs h|]; try discriminate.
    destruct v as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
    destruct (Hs ltac:(constructor) Hfl) as (bs & P1 & P2 & P3). unfold extz in P3. cbn [edenot] in P3.
    pose proof (bytes_le_to_Z_bound bs) as Hbnd. rewrite P2 in Hbnd.
    assert (Hlt : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    apply (f_equal bv_unsigned) in P3. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in P3.
    rewrite (Z.mod_small (bytes_le_to_Z bs)) in P3 by lia. unfold two64. rewrite <- P3.
    split; [|lia]. rewrite P1. f_equal. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    rewrite Z.mod_small by lia. rewrite <- P2. symmetry. apply Z_to_le_bytes_lez.
  Qed.

  Lemma kread8e_rdn : forall E M k b off v,
    know_ok SEGS E M k -> kread8e SEGS k b off = Some v -> flat E (SA b off) 8 ->
    rdn SEGS M (adenot E (SA b off)) 8 = Some (word_to_le_bytes 8 (edenot E v)).
  Proof.
    intros E M k b off v HK H Hfl. unfold kread8e in H.
    pose proof (know_lookup_sound SEGS E M k b off 8 false [] [] HK ltac:(lia) ltac:(lia)) as Hs.
    destruct (know_lookup SEGS k b off 8 false [] []) as [v' scs h|scs h|]; try discriminate.
    destruct scs; [|discriminate]. injection H as ->.
    destruct (Hs ltac:(constructor) Hfl) as (bs & P1 & P2 & P3). unfold extz in P3.
    rewrite P1, <- P3. f_equal. unfold word_to_le_bytes.
    pose proof (bytes_le_to_Z_bound bs) as Hbnd. rewrite P2 in Hbnd. change (8 * Z.of_nat 8) with 64 in Hbnd.
    rewrite Z_to_bv_unsigned, bv_wrap64_mod. rewrite Z.mod_small by lia. rewrite <- P2. symmetry. apply Z_to_le_bytes_lez.
  Qed.

  Lemma kimg_cover_none : forall E M k a b,
    know_ok SEGS E M k -> AN.kimg_cover k a b = true -> forall i, a <= i < b -> M (Z_to_bv 64 i) = None.
  Proof.
    intros E M k a b HK H i Hi. unfold AN.kimg_cover in H. apply existsb_exists in H as [K [Hin HKb]].
    destruct K as [| | |lo hi| | | | | |]; try discriminate. apply andb_prop in HKb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as KK. cbn [kentry_ok] in KK. destruct KK as (_ & _ & KK). apply KK. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn1_off_image : forall A M (a : word) b,
    (forall x : word, in_hull A (bv_unsigned x) = false -> find_segment SEGS (bv_unsigned x) 1 = None) ->
    img_hi A <= bv_unsigned a ->
    rdn SEGS M a 1 = Some [b] -> M a = Some b.
  Proof.
    intros A M a b Hh Ha H. cbn [rdn] in H.
    destruct (M a) as [b'|] eqn:E.
    - injection H as ->. reflexivity.
    - unfold seg_rom, memory_read in H. change (Z.of_N 1) with 1 in H. rewrite (Hh a) in H; [discriminate|].
      unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge. exact Ha.
  Qed.
End KLemmas.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
  Context {fx : FPState}.
  Variable ip : imgparams.
  #[local] Notation SEGS := (ip_segs ip).
  #[local] Notation A := (ip_A ip).
  #[local] Notation MTB := (ip_M ip).
  Variable nx0 : nat.
  Hypothesis NX0_min : APS.nx0_min_ok nx0.   (* [comment removed for export] *)
  Variable LIMIT : Z.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Variable FS0 : Fs.Fs.

  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).
  #[local] Notation MR := (Mr A argH) (only parsing).

  Hypothesis ENF : ENFRAME_STMT ip.
  Hypothesis FRP : FREEPRO_STMT ip.

  (* [comment removed for export] *)
  Lemma page_aligned_sound' : forall E M0 k e0,
    know_ok SEGS E M0 k -> page_aligned k e0 = true -> bv_unsigned (edenot E e0) mod 4096 = 0.
  Proof.
    intros E M0 k e0 HK H.
    assert (GEN : 12 <= ealign k e0 -> bv_unsigned (edenot E e0) mod 4096 = 0).
    { intros Hle. destruct (ealign_sound SEGS E M0 k e0 HK) as [Hr [c Hc]]. rewrite Hc.
      replace (2 ^ ealign k e0) with (2 ^ (ealign k e0 - 12) * 4096) by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
      rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
    unfold page_aligned in H. destruct e0 as [z| | | | | | |]; try (apply GEN; apply Z.leb_le; exact H).
    apply Z.eqb_eq in H. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    rewrite Z.mod_mod_divide; [exact H | exists (2 ^ 52); reflexivity].
  Qed.

  Lemma u_lit : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros z Hz. apply u64_lit. unfold two64 in Hz. lia. Qed.

  Lemma estart_SA : forall E b k, estart E (SA b k) = bv_unsigned (edenot E b) + k.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma store_ok_defined_off_image : forall M (a : Z) (n : nat),
    0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> img_hi A <= a ->
    store_ok SEGS M (Z_to_bv 64 a) n = true ->
    forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) <> None.
  Proof.
    intros M a n Ha Han Hhi Hso i Hi.
    assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_lit; unfold two64; lia).
    assert (Hui : bv_unsigned (Z_to_bv 64 (a + i)) = a + i) by (apply u_lit; unfold two64; lia).
    pose proof (store_ok_all SEGS M n (Z_to_bv 64 a) ltac:(rewrite Hu; lia) Hso (Z_to_bv 64 (a + i)) ltac:(rewrite Hu, Hui; lia)) as W.
    unfold wview in W. destruct (M (Z_to_bv 64 (a + i))) as [b|] eqn:HM; [discriminate|].
    rewrite (SEGS_in_hull (Z_to_bv 64 (a + i))) in W; [exact W|].
    unfold in_hull. apply Bool.andb_false_iff. right. apply Z.ltb_ge. rewrite Hui. lia.
  Qed.

  Lemma mem_grows_defined : forall (m m' : word -> option byte) x, mem_grows m m' -> m x <> None -> m' x <> None.
  Proof. intros m m' x H Hx. exact (H x Hx). Qed.

  Lemma edenot_eaddz : forall E b k, edenot E (eaddz b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
  Proof.
    intros E b k. unfold eaddz. rewrite mkAlu_denot. apply bv_eq.
    rewrite u_add64, edenot_lit, !u_lit64a, Zplus_mod_idemp_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma slack_mono : forall st nlo nhi n, nlo <= n <= nhi ->
    (st - 4 - nhi) / 16 <= slack_of st n <= (st - 4 - nlo) / 16.
  Proof. intros st nlo nhi n Hn. unfold slack_of, IB, UNIT. split; apply Z.div_le_mono; lia. Qed.


  (* [comment removed for export] *)
  Lemma regs_freehead : forall E nx sr R R' (HR : regs_ok E sr R) (Hsv : AP.sr_vars_lt nx sr = true)
      (e2 e9 e8 e10 e11 e14 e15 : expr),
    (forall k, In k [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
    getr R' (Z_to_bv 5 2) = edenot (ext_call E nx R') e2 ->
    getr R' (Z_to_bv 5 9) = edenot (ext_call E nx R') e9 ->
    getr R' (Z_to_bv 5 8) = edenot (ext_call E nx R') e8 ->
    getr R' (Z_to_bv 5 10) = edenot (ext_call E nx R') e10 ->
    getr R' (Z_to_bv 5 11) = edenot (ext_call E nx R') e11 ->
    getr R' (Z_to_bv 5 14) = edenot (ext_call E nx R') e14 ->
    getr R' (Z_to_bv 5 15) = edenot (ext_call E nx R') e15 ->
    regs_ok (ext_call E nx R')
      (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_fresh sr caller_saved nx) 2 e2) 9 e9) 8 e8) 10 e10) 11 e11) 14 e14) 15 e15) R'.
  Proof.
    intros E nx sr R R' HR Hsv e2 e9 e8 e10 e11 e14 e15 Hkept H2 H9 H8 H10 H11 H14 H15.
    assert (OLD : forall r : bv 5, r <> 0%bv -> getr R r = edenot E (nth (ridx r) sr (ELit 0))).
    { intros r Hr0. pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|]. exact X. }
    assert (KEEP : forall r : bv 5, r <> 0%bv -> In (ridx r) [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
                   getr R' r = edenot (ext_call E nx R') (nth (ridx r) (sr_fresh sr caller_saved nx) (ELit 0))).
    { intros r Hr0 Hin. rewrite nth_sr_fresh_out.
      2:{ unfold caller_saved. cbn [In] in Hin |- *. intros X. lia. }
      rewrite <- (edenot_agree' nx E (ext_call E nx R')); [| apply ext_call_agree | apply nth_sr_vars_lt'; [exact Hsv | apply ridx_range]].
      rewrite <- (OLD r Hr0). rewrite (reg_of_ridx r _ eq_refl). apply Hkept. exact Hin. }
    assert (FRESH : forall (r : bv 5) j, (j < 16)%nat -> nth j caller_saved 0%nat = ridx r ->
                    getr R' r = edenot (ext_call E nx R') (nth (ridx r) (sr_fresh sr caller_saved nx) (ELit 0))).
    { intros r j Hj Hnth. rewrite <- Hnth. rewrite (nth_sr_fresh_in caller_saved nx sr j caller_saved_nodup ltac:(cbn; lia)).
      cbn [edenot]. rewrite ext_call_var by (unfold NCS; lia). rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity. }
    apply regs_ok_pointwise. intros r Hr0.
    pose proof (ridx_range r) as Hrr.
    rewrite !nth_sr_upd.
    destruct (Nat.eqb_spec (ridx r) 15) as [E15|N15]; [rewrite (reg_of_ridx r _ E15); exact H15|].
    destruct (Nat.eqb_spec (ridx r) 14) as [E14|N14]; [rewrite (reg_of_ridx r _ E14); exact H14|].
    destruct (Nat.eqb_spec (ridx r) 11) as [E11|N11]; [rewrite (reg_of_ridx r _ E11); exact H11|].
    destruct (Nat.eqb_spec (ridx r) 10) as [E10|N10]; [rewrite (reg_of_ridx r _ E10); exact H10|].
    destruct (Nat.eqb_spec (ridx r) 8) as [E8|N8]; [rewrite (reg_of_ridx r _ E8); exact H8|].
    destruct (Nat.eqb_spec (ridx r) 9) as [E9|N9]; [rewrite (reg_of_ridx r _ E9); exact H9|].
    destruct (Nat.eqb_spec (ridx r) 2) as [E2|N2]; [rewrite (reg_of_ridx r _ E2); exact H2|].
    destruct (in_dec Nat.eq_dec (ridx r) [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat) as [Hin|Hnin]; [exact (KEEP r Hr0 Hin)|].
    (* [comment removed for export] *)
    assert (Hz : ridx r <> 0%nat).
    { intros X. apply Hr0. rewrite (reg_of_ridx r 0%nat X). apply bv_eq. reflexivity. }
    assert (CS : exists j, (j < 16)%nat /\ nth j caller_saved 0%nat = ridx r).
    { cbn [In] in Hnin. remember (ridx r) as i eqn:Hi. clear Hi r Hr0.
      assert (Hi32 : (i < 32)%nat) by lia.
      do 32 (destruct i as [|i]; [first [ exfalso; lia | exfalso; tauto
                                       | (exists 0%nat + exists 1%nat + exists 2%nat + exists 3%nat + exists 4%nat + exists 5%nat
                                          + exists 6%nat + exists 7%nat + exists 8%nat + exists 9%nat + exists 10%nat + exists 11%nat
                                          + exists 12%nat + exists 13%nat + exists 14%nat + exists 15%nat); split; [lia|reflexivity] ] |]).
      exfalso. lia. }
    destruct CS as (j & Hj & Hnth). exact (FRESH r j Hj Hnth).
  Qed.
End Sound.
