(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import SymStepR AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesAux. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArgSound ExecNodes ExecNodesSound ExecNodesW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import EXW.
Open Scope Z_scope.

Module EXWS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pure.

Definition in_bands (u : Z) : Prop := (0 <= u < two31) \/ (negband_lo <= u < two64).

Lemma two31_eq : two31 = 2 ^ 31.            Proof. reflexivity. Qed.
Lemma two32_eq : two32 = 2 ^ 32.            Proof. reflexivity. Qed.
Lemma two64_eq : two64 = 2 ^ 64.            Proof. reflexivity. Qed.
Lemma negband_lo_eq : negband_lo = 2 ^ 64 - 2 ^ 31.  Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma small_signed_mod64 : forall w, - 2 ^ 31 <= w < 2 ^ 31 ->
  w mod 2 ^ 64 = (if Z.leb 0 w then w else w + 2 ^ 64).
Proof.
  intros w Hw. destruct (Z.leb 0 w) eqn:Hs.
  - apply Z.leb_le in Hs. apply Z.mod_small. lia.
  - apply Z.leb_gt in Hs. rewrite <- (Z.mod_add w 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma small_signed_in_bands : forall w, - 2 ^ 31 <= w < 2 ^ 31 -> in_bands (w mod 2 ^ 64).
Proof.
  intros w Hw. unfold in_bands. rewrite two31_eq, two64_eq, negband_lo_eq, (small_signed_mod64 w Hw).
  destruct (Z.leb 0 w) eqn:Hs; [apply Z.leb_le in Hs; left; lia | apply Z.leb_gt in Hs; right; lia].
Qed.

Lemma swrap_range : forall n z, (0 < n)%N -> - 2 ^ (Z.of_N n - 1) <= bv_swrap n z < 2 ^ (Z.of_N n - 1).
Proof.
  intros n z Hn. pose proof (bv_swrap_in_range n z ltac:(lia)) as H.
  unfold bv_half_modulus, bv_modulus in H.
  replace (2 ^ Z.of_N n `div` 2) with (2 ^ (Z.of_N n - 1)) in H; [exact H|].
  replace (Z.of_N n) with (Z.of_N n - 1 + 1) at 2 by lia. rewrite Z.pow_add_r by lia.
  change (2 ^ 1) with 2. rewrite Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sext32_in_bands : forall v : bv 32, in_bands (bv_unsigned (sext 64 v)).
Proof.
  intros v. rewrite PropExec.sext32_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply small_signed_in_bands. pose proof (swrap_range 32 (bv_unsigned v) ltac:(lia)) as H. cbn [Z.of_N Z.sub Z.pos_sub] in H.
  change (Z.of_N 32 - 1) with 31 in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma ext_sx_in_bands : forall lo n (v : word), (1 <= n <= 4)%nat -> in_bands (bv_unsigned (ext_val true lo n v)).
Proof.
  intros lo n v Hn. unfold ext_val, ext_Z. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply small_signed_in_bands.
  pose proof (swrap_range (8 * N.of_nat n) ((bv_unsigned v / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ (8 * Z.of_nat n)) ltac:(lia)) as H.
  assert (Hle : 2 ^ (Z.of_N (8 * N.of_nat n) - 1) <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Lemma sx32b_in_bands : forall E e, sx32b e = true -> in_bands (bv_unsigned (edenot E e)).
Proof.
  intros E e H. destruct e; try discriminate; cbn [edenot].
  - apply sext32_in_bands.
  - apply sext32_in_bands.
  - cbn [sx32b] in H. destruct sx; [|discriminate]. apply andb_prop in H as [H1 H2].
    apply Nat.leb_le in H1. apply Nat.leb_le in H2. apply ext_sx_in_bands. lia.
Qed.

Lemma band_clamp_sound : forall lo hi u lo' hi',
  lo <= u <= hi -> in_bands u -> band_clamp lo hi = (lo', hi') -> lo' <= u <= hi'.
Proof.
  intros lo hi u lo' hi' Hu Hb Hc. unfold band_clamp in Hc. injection Hc as <- <-.
  unfold in_bands in Hb. rewrite two31_eq, two64_eq, negband_lo_eq in *.
  destruct (Z.ltb lo (2 ^ 31)) eqn:H1; destruct (Z.leb (2 ^ 64 - 2 ^ 31) hi) eqn:H2;
    first [apply Z.ltb_lt in H1 | apply Z.ltb_ge in H1]; first [apply Z.leb_le in H2 | apply Z.leb_gt in H2]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sval (u : Z) : Z := if Z.ltb u (2 ^ 63) then u else u - 2 ^ 64.

Lemma sband_sound : forall r u sl sh,
  (match r with Some (lo, hi) => lo <= u <= hi | None => False end) -> 0 <= u < 2 ^ 64 ->
  sband r = Some (sl, sh) -> sl <= sval u <= sh /\ - 2 ^ 31 <= sl /\ sh < 2 ^ 31 /\ (sval u) mod 2 ^ 64 = u.
Proof.
  intros [[lo hi]|] u sl sh Hu Hr Hs; [|contradiction]. unfold sband in Hs.
  rewrite two31_eq, two64_eq, negband_lo_eq in Hs. unfold sval.
  destruct (Z.leb 0 lo && Z.leb lo hi && Z.ltb hi (2 ^ 31))%bool eqn:C1.
  - injection Hs as <- <-. apply andb_prop in C1 as [C1 C3]. apply andb_prop in C1 as [C1 C2].
    apply Z.leb_le in C1. apply Z.ltb_lt in C3.
    assert (Hl : (u <? 2 ^ 63) = true) by (apply Z.ltb_lt; lia). rewrite Hl.
    rewrite Z.mod_small by lia. lia.
  - destruct (Z.leb (2 ^ 64 - 2 ^ 31) lo && Z.leb lo hi && Z.ltb hi (2 ^ 64))%bool eqn:C2; [|discriminate].
    injection Hs as <- <-. apply andb_prop in C2 as [C2 C4]. apply andb_prop in C2 as [C2 C3].
    apply Z.leb_le in C2. apply Z.ltb_lt in C4.
    assert (Hl : (u <? 2 ^ 63) = false) by (apply Z.ltb_ge; lia). rewrite Hl.
    rewrite <- (Z.mod_add (u - 2 ^ 64) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap32_eq : forall z, bv_swrap 32 z = z - 2 ^ 32 * wq z.
Proof.
  intros z. unfold bv_swrap, bv_wrap, wq. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite two31_eq, two32_eq. rewrite Z.mod_eq by lia. lia.
Qed.

(* [comment removed for export] *)
Definition congr32 (x y : Z) : Prop := exists k, x - y = k * 2 ^ 32.
Lemma congr32_swrap : forall a b, congr32 a b -> bv_swrap 32 a = bv_swrap 32 b.
Proof.
  intros a b [k Hk]. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32). f_equal.
  replace (a + bv_half_modulus 32) with ((b + bv_half_modulus 32) + k * 2 ^ 32) by lia. apply Z.mod_add. lia.
Qed.
Lemma congr32_mod : forall u, congr32 (u mod 2 ^ 32) u.
Proof. intros u. exists (- (u / 2 ^ 32)). rewrite (Z.mod_eq u (2 ^ 32)) by lia. lia. Qed.
Lemma congr32_sval : forall u, congr32 u (sval u).
Proof.
  intros u. unfold sval. destruct (Z.ltb u (2 ^ 63)); [exists 0; lia|]. exists (2 ^ 32).
  change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). lia.
Qed.
Lemma congr32_add : forall a a' b b', congr32 a a' -> congr32 b b' -> congr32 (a + b) (a' + b').
Proof. intros a a' b b' [k Hk] [l Hl]. exists (k + l). lia. Qed.
Lemma congr32_sub : forall a a' b b', congr32 a a' -> congr32 b b' -> congr32 (a - b) (a' - b').
Proof. intros a a' b b' [k Hk] [l Hl]. exists (k - l). lia. Qed.
Lemma congr32_trans : forall a b c, congr32 a b -> congr32 b c -> congr32 a c.
Proof. intros a b c [k Hk] [l Hl]. exists (k + l). lia. Qed.

Lemma low32_unsigned' : forall a : word, bv_unsigned (low32 a) = bv_unsigned a mod 2 ^ 32.
Proof.
  intros a. unfold low32. rewrite bv_extract_unsigned. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.shiftr_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma aluw_addsub_val : forall (isadd : bool) (a b : word),
  bv_unsigned (sext 64 (alu32 (if isadd then ALU_ADD else ALU_SUB) (low32 a) (low32 b)))
  = (bv_swrap 32 (if isadd then sval (bv_unsigned a) + sval (bv_unsigned b) else sval (bv_unsigned a) - sval (bv_unsigned b))) mod 2 ^ 64.
Proof.
  intros isadd a b. rewrite PropExec.sext32_unsigned. unfold bv_wrap at 1. change (bv_modulus 64) with (2 ^ 64). f_equal.
  destruct isadd; cbn [alu32 alu].
  - rewrite bv_add_unsigned, !low32_unsigned', bv_swrap_wrap. apply congr32_swrap.
    apply congr32_add; (eapply congr32_trans; [apply congr32_mod | apply congr32_sval]).
  - rewrite bv_sub_unsigned, !low32_unsigned', bv_swrap_wrap. apply congr32_swrap.
    apply congr32_sub; (eapply congr32_trans; [apply congr32_mod | apply congr32_sval]).
Qed.

(* [comment removed for export] *)
Lemma alu64_addsub_val : forall (isadd : bool) (a b : word),
  bv_unsigned (alu64 (if isadd then ALU_ADD else ALU_SUB) a b)
  = (if isadd then sval (bv_unsigned a) + sval (bv_unsigned b) else sval (bv_unsigned a) - sval (bv_unsigned b)) mod 2 ^ 64.
Proof.
  intros isadd a b.
  assert (Hs : forall u, exists k, u - sval u = k * 2 ^ 64).
  { intros u. unfold sval. destruct (Z.ltb u (2 ^ 63)); [exists 0; lia | exists 1; lia]. }
  destruct (Hs (bv_unsigned a)) as [k Hk]. destruct (Hs (bv_unsigned b)) as [l Hl].
  destruct isadd; cbn [alu64 alu].
  - rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    replace (bv_unsigned a + bv_unsigned b) with ((sval (bv_unsigned a) + sval (bv_unsigned b)) + (k + l) * 2 ^ 64) by lia.
    apply Z.mod_add. lia.
  - rewrite bv_sub_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    replace (bv_unsigned a - bv_unsigned b) with ((sval (bv_unsigned a) - sval (bv_unsigned b)) + (k - l) * 2 ^ 64) by lia.
    apply Z.mod_add. lia.
Qed.

(* [comment removed for export] *)
Lemma wq_mono : forall x y, x <= y -> wq x <= wq y.
Proof. intros x y H. unfold wq. rewrite two31_eq, two32_eq. apply Z.div_le_mono; lia. Qed.

Lemma wop_core : forall (isadd : bool) (sa sb al ah bl bh : Z),
  al <= sa <= ah -> bl <= sb <= bh ->
  let rl := (if isadd then al + bl else al - bh) in
  let rh := (if isadd then ah + bh else ah - bl) in
  let s := (if isadd then sa + sb else sa - sb) in
  wq rl = wq rh ->
  rl - two32 * wq rl <= bv_swrap 32 s <= rh - two32 * wq rl
  /\ - 2 ^ 31 <= rl - two32 * wq rl /\ rh - two32 * wq rl < 2 ^ 31
  /\ (wq rl = 0 -> bv_swrap 32 s = s).
Proof.
  intros isadd sa sb al ah bl bh Ha Hb rl rh s Hq.
  assert (Hs : rl <= s <= rh) by (subst rl rh s; destruct isadd; lia).
  assert (Hw : wq s = wq rl).
  { pose proof (wq_mono rl s ltac:(lia)). pose proof (wq_mono s rh ltac:(lia)). lia. }
  rewrite swrap32_eq, Hw, two32_eq.
  assert (Hr : - 2 ^ 31 <= rl - 2 ^ 32 * wq rl /\ rh - 2 ^ 32 * wq rh < 2 ^ 31).
  { unfold wq. rewrite two31_eq, two32_eq.
    pose proof (Z.div_mod (rl + 2 ^ 31) (2 ^ 32) ltac:(lia)). pose proof (Z.mod_pos_bound (rl + 2 ^ 31) (2 ^ 32) ltac:(lia)).
    pose proof (Z.div_mod (rh + 2 ^ 31) (2 ^ 32) ltac:(lia)). pose proof (Z.mod_pos_bound (rh + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia. }
  rewrite <- Hq in Hr. repeat split; try lia.
Qed.

End Pure.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
  Context {fx : FPState}.
  Variable SEGS : list Segment.
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound SEGS IT.
  Variable A : atable.
  Variable nx0 : nat.
  Hypothesis NX0_min : APS.nx0_min_ok nx0.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Hypothesis SEGS_wr : forall seg, In seg SEGS -> seg_writable seg = true -> seg_readable seg = true.

  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).

  Lemma reg_ix_sound : forall r rn, reg_ix r = Some rn -> (0 < rn < 32)%nat.
  Proof.
    intros r rn H. unfold reg_ix in H.
    destruct (Nat.ltb 0 (Z.to_nat r) && Nat.ltb (Z.to_nat r) 32)%bool eqn:C; [|discriminate]. injection H as <-.
    apply andb_prop in C as [C1 C2]. apply Nat.ltb_lt in C1. apply Nat.ltb_lt in C2. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem node_sxband_soundF : forall args,
    node1_stmtF SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_sxband cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_sxband in Hn.
    destruct args as [|[r| | | | | | |] [|? ?]]; try discriminate.
    destruct (reg_ix r) as [rn|] eqn:Hix; [|discriminate].
    destruct (sx32b (reg cs rn)) eqn:Hsx; [|discriminate].
    destruct (erange (kn cs) (reg cs rn)) as [[lo hi]|] eqn:Her; [|discriminate].
    destruct (band_clamp lo hi) as [lo' hi'] eqn:Hbc. injection Hn as <-.
    specialize (Hk E R model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    apply Hk; [ | reflexivity | apply APS.mvis_refl | apply (APS.hid_extF0 A argH); [reflexivity | apply APS.mvis_refl]].
    apply cs_ok_set_kn; [exact HC|].
    constructor; [| exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC)].
    cbn [kentry_ok].
    pose proof (erange_sound SEGS E _ (kn cs) (reg cs rn) lo hi (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Her) as Hr.
    exact (band_clamp_sound lo hi _ lo' hi' Hr (sx32b_in_bands E _ Hsx) Hbc).
  Qed.

  (* [comment removed for export] *)

  Theorem node_wop64_soundF : forall args,
    node1_stmtF SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_wop64 cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_wop64 in Hn.
    destruct args as [|[r| | | | | | |] [|? ?]]; try discriminate.
    destruct (reg_ix r) as [rn|] eqn:Hix; [|discriminate]. pose proof (reg_ix_sound r rn Hix) as Hrn.
    destruct (reg cs rn) as [z|v|op a b|op a b|op a b|op a b|sx lo n a|sx k i n] eqn:Hreg; try discriminate.
    set (iso := match op with ALU_ADD => Some true | ALU_SUB => Some false | _ => None end) in Hn.
    destruct iso as [isadd|] eqn:Hiso; [|discriminate].
    assert (Hop : op = (if isadd then ALU_ADD else ALU_SUB)).
    { subst iso. destruct op; try discriminate Hiso; injection Hiso as <-; reflexivity. }
    destruct (sband (erange (kn cs) a)) as [[al ah]|] eqn:Ha; [|discriminate].
    destruct (sband (erange (kn cs) b)) as [[bl bh]|] eqn:Hb; [|discriminate].
    set (rl := if isadd then al + bl else al - bh) in Hn.
    set (rh := if isadd then ah + bh else ah - bl) in Hn.
    destruct (Z.eqb (wq rl) (wq rh)) eqn:Hq; [|discriminate]. apply Z.eqb_eq in Hq. cbn zeta in Hn.
    set (e' := if Z.eqb (wq rl) 0 then mkAlu op a b else EAluw op a b) in Hn.
    set (facts := if Z.leb 0 (rl - two32 * wq rl) then [KRange e' (rl - two32 * wq rl) (rh - two32 * wq rl)]
                  else if Z.ltb (rh - two32 * wq rl) 0 then [KRange e' (rl - two32 * wq rl + two64) (rh - two32 * wq rl + two64)]
                  else []) in Hn.
    injection Hn as <-.
    (* [comment removed for export] *)
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (bv_unsigned_in_range _ (edenot E a)) as Ra. pose proof (bv_unsigned_in_range _ (edenot E b)) as Rb.
    unfold bv_modulus in Ra, Rb. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra, Rb.
    assert (HA : al <= sval (bv_unsigned (edenot E a)) <= ah /\ - 2 ^ 31 <= al /\ ah < 2 ^ 31 /\ (sval (bv_unsigned (edenot E a))) mod 2 ^ 64 = bv_unsigned (edenot E a)).
    { apply (sband_sound (erange (kn cs) a)); [|exact Ra|exact Ha].
      destruct (erange (kn cs) a) as [[lo1 hi1]|] eqn:He; [exact (erange_sound SEGS E _ (kn cs) a lo1 hi1 HK He) | discriminate]. }
    assert (HB : bl <= sval (bv_unsigned (edenot E b)) <= bh /\ - 2 ^ 31 <= bl /\ bh < 2 ^ 31 /\ (sval (bv_unsigned (edenot E b))) mod 2 ^ 64 = bv_unsigned (edenot E b)).
    { apply (sband_sound (erange (kn cs) b)); [|exact Rb|exact Hb].
      destruct (erange (kn cs) b) as [[lo1 hi1]|] eqn:He; [exact (erange_sound SEGS E _ (kn cs) b lo1 hi1 HK He) | discriminate]. }
    destruct HA as (HA & HAl & HAh & HAm). destruct HB as (HB & HBl & HBh & HBm).
    set (sa := sval (bv_unsigned (edenot E a))) in *. set (sb := sval (bv_unsigned (edenot E b))) in *.
    pose proof (wop_core isadd sa sb al ah bl bh HA HB Hq) as (Hw & Hwl & Hwh & Hnowrap). fold rl rh in Hw, Hwl, Hwh, Hnowrap.
    set (sres := if isadd then sa + sb else sa - sb) in *.
    (* [comment removed for export] *)
    assert (Hval : bv_unsigned (edenot E (EAluw op a b)) = (bv_swrap 32 sres) mod 2 ^ 64).
    { cbn [edenot]. rewrite Hop. subst sres sa sb. apply aluw_addsub_val. }
    (* [comment removed for export] *)
    assert (Hval' : edenot E e' = edenot E (EAluw op a b)).
    { subst e'. destruct (Z.eqb (wq rl) 0) eqn:Hz; [|reflexivity]. apply Z.eqb_eq in Hz.
      apply bv_eq. rewrite Hval, mkAlu_denot. rewrite Hop, alu64_addsub_val. subst sres sa sb.
      f_equal. symmetry. apply Hnowrap. exact Hz. }
    (* [comment removed for export] *)
    assert (Hrange : rl - two32 * wq rl <= bv_swrap 32 sres <= rh - two32 * wq rl) by exact Hw.
    specialize (Hk E R model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    apply Hk; [ | reflexivity | apply APS.mvis_refl | apply (APS.hid_extF0 A argH); [reflexivity | apply APS.mvis_refl]].
    apply cs_ok_set_kn.
    { apply EXNS.cs_ok_set_reg_same; [exact HC | exact Hrn |]. rewrite Hreg. exact Hval'. }
    apply Forall_app_intro; [| exact HK].
    subst facts. destruct (Z.leb 0 (rl - two32 * wq rl)) eqn:C1.
    - apply Z.leb_le in C1. constructor; [|constructor]. cbn [kentry_ok]. rewrite Hval', Hval.
      rewrite two32_eq in *. rewrite (small_signed_mod64 (bv_swrap 32 sres)) by lia.
      replace (0 <=? bv_swrap 32 sres) with true by (symmetry; apply Z.leb_le; lia). lia.
    - destruct (Z.ltb (rh - two32 * wq rl) 0) eqn:C2; [|constructor].
      apply Z.leb_gt in C1. apply Z.ltb_lt in C2. constructor; [|constructor]. cbn [kentry_ok]. rewrite Hval', Hval.
      rewrite two32_eq, two64_eq in *. rewrite (small_signed_mod64 (bv_swrap 32 sres)) by lia.
      replace (0 <=? bv_swrap 32 sres) with false by (symmetry; apply Z.leb_gt; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma Z_to_le_bytes_zero : forall n, Z_to_le_bytes n 0 = repeat (Z_to_bv 8 0) n.
  Proof. induction n as [|n IH]; [reflexivity|]. cbn [Z_to_le_bytes repeat]. rewrite Z.shiftr_0_l, IH. reflexivity. Qed.
  Lemma nth_repeat' : forall {T} (x d : T) n j, (j < n)%nat -> nth j (repeat x n) d = x.
  Proof. intros T x d n. induction n as [|n IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.

  Theorem node_zeroword_soundF : forall args,
    node1_stmtF SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_zeroword cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_zeroword in Hn.
    destruct args as [|a [|[nz| | | | | | |] [|? ?]]]; try discriminate.
    destruct (split_lit a) as [ab ao] eqn:Hsl.
    destruct ((Z.eqb nz 1 || Z.eqb nz 2 || Z.eqb nz 4 || Z.eqb nz 8) && kzero_x (kn cs) (kn cs) ab ao (ELit nz))%bool eqn:Hg; [|discriminate].
    injection Hn as <-. apply andb_prop in Hg as [Hnz Hz].
    assert (Hnzv : nz = 1 \/ nz = 2 \/ nz = 4 \/ nz = 8).
    { repeat (apply Bool.orb_prop in Hnz as [Hnz|Hnz]); apply Z.eqb_eq in Hnz; lia. }
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (APSX.kzero_x_sound SEGS E (Mr A argH E cs model FULL) (kn cs) (kn cs) ab ao (ELit nz) HK HK Hz) as (Hbytes & Hlo & Hhi).
    unfold elenZ in Hbytes, Hhi. cbn [edenot] in Hbytes, Hhi.
    assert (Hnzu : bv_unsigned (Z_to_bv 64 nz) = nz) by (rewrite u_lit64a; apply Z.mod_small; lia).
    rewrite Hnzu in Hbytes, Hhi.
    specialize (Hk E R model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    apply Hk; [ | reflexivity | apply APS.mvis_refl | apply (APS.hid_extF0 A argH); [reflexivity | apply APS.mvis_refl]].
    apply cs_ok_set_kn; [exact HC|].
    constructor; [| exact HK].
    cbn [kentry_ok]. split; [lia|]. split.
    - unfold flat. rewrite Z2Nat.id by lia. lia.
    - assert (Hu : bv_unsigned (adenot E (SA ab ao)) = estart E (SA ab ao)) by (apply (flat_u E (SA ab ao) nz); unfold flat; lia).
      cbn [edenot]. unfold word_to_le_bytes. rewrite u_lit64a, Z.mod_0_l by lia. rewrite Z_to_le_bytes_zero.
      apply rdn_pointwise; [apply repeat_length | rewrite Hu, Z2Nat.id; lia |].
      intros j Hj. rewrite (nth_repeat' (Z_to_bv 8 0) (Z_to_bv 8 0) _ j Hj), Hu. apply Hbytes. lia.
  Qed.

  (* [comment removed for export] *)
  Corollary xn_soundF : forall id, ext_stmtF SEGS A nx0 LIMIT (EXW.xn SEGS IT nx0) SINV argH FS0 id.
  Proof.
    intros id args. unfold EXW.xn.
    do 46 (destruct id as [|id]; [apply (EXNS.xn_soundF SEGS IT IT_ok A nx0 NX0_min LIMIT SINV argH FS0 SEGS_wx SEGS_in_hull HULL_ok argH_high argH_agree SINV_frame SINV_agree SEGS_wr)|]).
    destruct id as [|id]; [apply node_sxband_soundF|].
    destruct id as [|id]; [apply node_wop64_soundF|].
    destruct id as [|id]; [apply node_zeroword_soundF|].
    apply (EXNS.xn_soundF SEGS IT IT_ok A nx0 NX0_min LIMIT SINV argH FS0 SEGS_wx SEGS_in_hull HULL_ok argH_high argH_agree SINV_frame SINV_agree SEGS_wr).
  Qed.
  Corollary xn_sound : ext_stmt SEGS A nx0 LIMIT (EXW.xn SEGS IT nx0) SINV argH FS0.
  Proof. intros id args. apply node1_stmtF_stmt. apply xn_soundF. Qed.

End Sound.

End EXWS.
