(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanNodesAux CatExec.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Common Require Import RegEqv.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Frame Mem RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import SrzEqv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Definition canon_regs (R : bvmap 5 word) : bvmap 5 word :=
  mkR (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4)) (getr R (Z_to_bv 5 5))
      (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8)) (getr R (Z_to_bv 5 9)) (getr R (Z_to_bv 5 10))
      (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12)) (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14)) (getr R (Z_to_bv 5 15))
      (getr R (Z_to_bv 5 16)) (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19)) (getr R (Z_to_bv 5 20))
      (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24)) (getr R (Z_to_bv 5 25))
      (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28)) (getr R (Z_to_bv 5 29)) (getr R (Z_to_bv 5 30))
      (getr R (Z_to_bv 5 31)).

Lemma reg_cases : forall r : bv 5, r <> 0%bv -> exists k, 1 <= k <= 31 /\ r = Z_to_bv 5 k.
Proof.
  intros r Hr. exists (bv_unsigned r). split.
  - pose proof (bv_unsigned_in_range 5 r) as Hb. unfold bv_modulus in Hb. cbn in Hb.
    destruct (Z.eq_dec (bv_unsigned r) 0) as [E0|E0]; [|lia]. exfalso. apply Hr. apply bv_eq. rewrite E0. reflexivity.
  - symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma canon_regs_eqv : forall R, regs_eqv (canon_regs R) R.
Proof.
  intros R r Hr. destruct (reg_cases r Hr) as (k & Hk & ->).
  assert (Hk' : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12
                \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23
                \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
  unfold canon_regs, getr.
  repeat (destruct Hk' as [-> | Hk']); try (subst k); reflexivity.
Qed.

Section Canon.
Context {fx : FPState}.
Variable SEGS : list Segment.

Definition canon_cfg (R : bvmap 5 word) (p : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (mkst (canon_regs R) (Z_to_bv 64 p) M (seg_rom SEGS)) model.

Lemma canon_cfg_eqv : forall R p M model, cfg_eqv (canon_cfg R p M model) (mkCfg (mkst R (Z_to_bv 64 p) M (seg_rom SEGS)) model).
Proof.
  intros R p M model. split; [|reflexivity]. cbn [cfg_ms].
  repeat split; cbn; try reflexivity. apply canon_regs_eqv.
Qed.

Theorem hole_of_canon : forall R p M model T,
  realizes SEGS (canon_cfg R p M model) T -> srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 p) M (seg_rom SEGS)) model) T.
Proof. intros R p M model T H. exact (srealizes_of_realizes_eqv SEGS _ _ T H (canon_cfg_eqv R p M model)). Qed.
End Canon.

Notation AS_rdn := OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS.PropExec.rdn.
Notation L_rdn := OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Common.PropExec.rdn.

Lemma rdn_AS_Lib : forall segs m a n, AS_rdn segs m a n = L_rdn segs m a n.
Proof. intros segs m a n. reflexivity. Qed.

Lemma rdn_length : forall segs m n (a : word) bs, L_rdn segs m a n = Some bs -> length bs = n.
Proof.
  intros segs m n. induction n as [|n IH]; intros a bs H; [cbn in H; injection H as <-; reflexivity|].
  rewrite rdn_unfold in H. cbv beta iota in H.
  destruct (mrd segs m a) as [b|]; [|discriminate].
  destruct (L_rdn segs m (a + 1) n) as [r|] eqn:Hr; [|discriminate]. injection H as <-. cbn. rewrite (IH _ _ Hr). reflexivity.
Qed.

Lemma rdn_bytes_at : forall segs m n (a : word) bs,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 -> L_rdn segs m a n = Some bs -> bytes_at segs m (bv_unsigned a) bs.
Proof.
  intros segs m n. induction n as [|n IH]; intros a bs Hn H.
  - cbn in H. injection H as <-. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
    split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - rewrite rdn_unfold in H. cbv beta iota in H.
    destruct (mrd segs m a) as [b|] eqn:Hb; [|discriminate].
    destruct (L_rdn segs m (a + 1) n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
    assert (Hu : bv_unsigned (a + 1)%bv = bv_unsigned a + 1 \/ (bv_unsigned a + 1 = 2 ^ 64 /\ n = O)).
    { destruct (Z.eq_dec (bv_unsigned a + 1) (2 ^ 64)) as [E1|E1]; [right; split; [exact E1 | lia]|].
      left. rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1. unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. lia. }
    pose proof (rdn_length segs m n (a + 1) r Hr) as Hlr.
    split; [lia|]. split; [cbn [length]; rewrite Hlr; lia|].
    intros i Hi. destruct i as [|i].
    + cbn. unfold wa. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hb.
    + destruct Hu as [Hu | [Hu ->]]; [|cbn in Hr; injection Hr as <-; cbn [length] in Hi; lia].
      assert (IHb : bytes_at segs m (bv_unsigned (a + 1)%bv) r) by (apply (IH (a + 1)%bv r); [rewrite Hu; lia | exact Hr]).
      destruct IHb as (_ & _ & Hr'). rewrite Hu in Hr'. cbn [nth_error]. cbn [length] in Hi.
      rewrite <- (Hr' i ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

Section HK.
Variables (SEGS : list Segment) (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok SEGS A nx0 LIMIT SINV argH FS0 E ch R FULL model.

Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

Let dHS : nat -> option acs := fun _ => None.
Let dXN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let dXE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let dXB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.

#[local] Notation MR := (APS.Mr A argH E ch model FULL).
#[local] Notation HIDc := (APS.hid A argH E ch model).

Definition mH : word -> option byte := mrestrict (HID A' model) FULL.

Lemma hk_not_mkH : forall a : word, HIDc a = false -> mkH (m_vm_lazy model) A' a = false.
Proof.
  intros a Ha. unfold mkH.
  destruct (page_in_ranges (page_base a) (m_vm_lazy model)) eqn:Hl; [|reflexivity]. cbn [andb].
  pose proof (APS.lazy_cover_cs SEGS A nx0 LIMIT dHS dXN dXE dXB HULL_ok SINV argH FS0 O E ch R FULL model HC a Hl Ha) as Hp.
  rewrite (HA' _ Hp). reflexivity.
Qed.

Lemma hk_not_hid : forall a : word, HIDc a = false -> bv_unsigned a < 2 ^ 47 -> HID A' model a = false.
Proof.
  intros a Ha Hlt. unfold HID. rewrite (hk_not_mkH a Ha). cbn [orb]. apply Z.leb_gt. exact Hlt.
Qed.

Lemma hk_mr_some : forall a : word, MR a <> None -> bv_unsigned a < 2 ^ 47 -> mH a = MR a.
Proof.
  intros a Ha Hlt. unfold APS.Mr, mrestrict in *. destruct (HIDc a) eqn:Hh; [exfalso; apply Ha; reflexivity|].
  unfold mH, mrestrict. rewrite (hk_not_hid a Hh Hlt). reflexivity.
Qed.

Lemma hk_hull : forall a : word, APS.in_hull A (bv_unsigned a) = true -> mH a = FULL a /\ MR a = FULL a.
Proof.
  intros a Ha. pose proof (APS.hid_hull A HULL_ok argH argH_high E ch model a Ha) as Hh.
  assert (Hlt : bv_unsigned a < 2 ^ 47).
  { pose proof HULL_ok as (H0 & H1 & H2 & H3). unfold APS.in_hull in Ha. apply andb_prop in Ha as [_ Ha]. apply Z.ltb_lt in Ha.
    unfold KHI in H3. lia. }
  unfold APS.Mr, mH, mrestrict. rewrite Hh, (hk_not_hid a Hh Hlt). split; reflexivity.
Qed.

Lemma hk_mrd : forall a : word, mrd SEGS MR a <> None -> bv_unsigned a < 2 ^ 47 -> mrd SEGS mH a = mrd SEGS MR a.
Proof.
  intros a Ha Hlt. unfold mrd in *.
  destruct (APS.in_hull A (bv_unsigned a)) eqn:Hin.
  - destruct (hk_hull a Hin) as [E1 E2]. rewrite E1, E2. reflexivity.
  - destruct (MR a) as [b|] eqn:Hm.
    + rewrite (hk_mr_some a ltac:(rewrite Hm; discriminate) Hlt), Hm. reflexivity.
    + exfalso. apply Ha. unfold PropExec.seg_rom, memory_read. cbn [Z.of_N]. rewrite (SEGS_in_hull a Hin). reflexivity.
Qed.

Lemma hk_kentry : forall K, In K (kn ch) -> kentry_ok SEGS E MR K.
Proof. intros K HK. exact (proj1 (Forall_forall _ _) (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) K HK). Qed.

Lemma hk_bytes_at : forall a bs, a + Z.of_nat (length bs) <= 2 ^ 47 -> bytes_at SEGS MR a bs -> bytes_at SEGS mH a bs.
Proof.
  intros a bs Hlt (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite (hk_mrd (wa (a + Z.of_nat i))); [exact (H3 i Hi)| |].
  - rewrite (H3 i Hi). destruct (nth_error bs i) eqn:Hn; [discriminate|]. apply nth_error_None in Hn. lia.
  - rewrite (wa_unsigned (a + Z.of_nat i)) by lia. lia.
Qed.

Lemma hk_kword : forall a w v, In (KWord a w v) (kn ch) -> estart E a + Z.of_nat w <= 2 ^ 47 ->
  bytes_at SEGS mH (estart E a) (word_to_le_bytes w (edenot E v)).
Proof.
  intros a w v HK Hlt. destruct (hk_kentry _ HK) as (Hw & Hfl & Hr).
  rewrite rdn_AS_Lib in Hr. apply hk_bytes_at; [rewrite length_N_to_le_bytes; exact Hlt|]. rewrite <- (flat_u E a (Z.of_nat w) Hfl).
  apply (rdn_bytes_at SEGS MR w (adenot E a)); [rewrite (flat_u E a (Z.of_nat w) Hfl); unfold flat in Hfl; lia | exact Hr].
Qed.

Lemma hk_kimg : forall lo hi, In (KImg lo hi) (kn ch) -> forall i, lo <= i < hi -> MR (Z_to_bv 64 i) = None.
Proof. intros lo hi HK i Hi. destruct (hk_kentry _ HK) as (_ & _ & H). exact (H i Hi). Qed.

Lemma hk_kzero : forall a n, In (KZero a n) (kn ch) -> estart E a + elenZ E n <= 2 ^ 47 ->
  forall i, 0 <= i < elenZ E n -> mH (Z_to_bv 64 (estart E a + i)) = Some (Z_to_bv 8 0).
Proof.
  intros a n HK Hlt i Hi. destruct (hk_kentry _ HK) as (Hfl & H). specialize (H i Hi).
  unfold flat in Hfl.
  rewrite (hk_mr_some _ ltac:(rewrite H; discriminate)); [exact H|]. change (Z_to_bv 64 (estart E a + i)) with (wa (estart E a + i)). rewrite (wa_unsigned (estart E a + i)) by lia. lia.
Qed.

Lemma hk_allow_page : forall (a : word),
  (APS.in_allow A E ch (bv_unsigned a) = true \/ APS.in_ghost E ch (bv_unsigned a) = true) ->
  page_allowedb (APS.allowA A E ch) (page_base a) = true.
Proof.
  intros a Ha.
  pose proof (page_base_le' a) as (P1 & P2 & P3).
  unfold page_allowedb, APS.allowA. apply existsb_exists. unfold page_size.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  destruct Ha as [Ha|Ha].
  - unfold APS.in_allow in Ha. apply orb_prop in Ha as [Hv|Hv].
    + unfold APS.in_vis in Hv. apply existsb_exists in Hv as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      exists (APS.pagedown (APS.uE E (fst p)), APS.pageup (APS.uE E (fst p) + APS.uE E (snd p))). split.
      * apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. left. reflexivity.
      * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold APS.pagedown, APS.pageup; lia.
    + unfold APS.in_sh in Hv. apply existsb_exists in Hv as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      exists (APS.pagedown (APS.sh_lo A E p), APS.pageup (APS.sh_hi A E p)). split.
      * apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. right. left. reflexivity.
      * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold APS.pagedown, APS.pageup; lia.
  - unfold APS.in_ghost in Ha. apply existsb_exists in Ha as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
    exists (APS.pagedown (APS.uE E (fst p)), APS.pageup (APS.uE E (fst p) + APS.uE E (snd p))). split.
    + apply in_flat_map. exists p. split; [apply in_or_app; right; exact Hin|]. left. reflexivity.
    + cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold APS.pagedown, APS.pageup; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Theorem hk_HZ : forall a : word, mkH (m_vm_lazy model) A' a = true ->
  page_in_ranges (page_base a) (vm_noaccess (m_vmmaps model)) = false -> FULL a = Some (Z_to_bv 8 0).
Proof.
  intros a Hh Hna. unfold mkH in Hh. apply andb_prop in Hh as [Hlz Hna'].
  apply negb_true_iff in Hna'.
  pose proof (APS.co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ HC) as LB.
  pose proof (APS.co_lazyin _ _ _ _ _ _ _ _ _ _ _ _ HC) as LI.
  pose proof (APS.co_naal _ _ _ _ _ _ _ _ _ _ _ _ HC) as NA.
  pose proof HULL_ok as (H0 & H1 & H2 & H3).

  destruct (APS.page_in_ranges_in dHS dXN dXE dXB O a _ Hlz) as (iv & Hiv & Ha).
  pose proof (proj1 (Forall_forall _ _) LB iv Hiv) as [L1 L2].
  assert (Hpos : 0 < bv_unsigned (snd iv)) by lia.
  destruct (LI iv Hiv Hpos) as (e & He & E1 & E2).

  assert (Hnall : APS.in_allow A E ch (bv_unsigned a) = false /\ APS.in_ghost E ch (bv_unsigned a) = false).
  { split.
    - destruct (APS.in_allow A E ch (bv_unsigned a)) eqn:X; [|reflexivity]. exfalso.
      rewrite (HA' _ (hk_allow_page a (or_introl X))) in Hna'. discriminate.
    - destruct (APS.in_ghost E ch (bv_unsigned a)) eqn:X; [|reflexivity]. exfalso.
      rewrite (HA' _ (hk_allow_page a (or_intror X))) in Hna'. discriminate. }
  destruct Hnall as [Hnall Hngh].

  assert (Hnab : APS.in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false).
  { destruct (APS.in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model))) eqn:X; [|reflexivity]. exfalso.
    apply APS.in_ivs_true in X as (jv & Hjv & Hx).
    pose proof (proj1 (Forall_forall _ _) NA jv Hjv) as [A1 A2].
    pose proof (page_base_le' a) as (P1 & P2 & P3).
    assert (Hp : page_in_ranges (page_base a) (vm_noaccess (m_vmmaps model)) = true).
    { unfold page_in_ranges. apply existsb_exists. exists jv. split; [exact Hjv|]. unfold page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      apply andb_true_intro; split; apply Z.leb_le; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    rewrite Hp in Hna. discriminate. }

  assert (Hhc : HIDc a = true).
  { unfold APS.hid. apply orb_true_iff. right. apply negb_true_iff. unfold APS.vis.
    rewrite Hlz, Hnall, Hnab. cbn [negb orb andb].
    replace (APS.in_hull A (bv_unsigned a)) with false by (symmetry; unfold APS.in_hull; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    replace (alloc_top (m_vmmaps model) <=? bv_unsigned a) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite andb_false_r. reflexivity. }
  apply (APS.co_zero _ _ _ _ _ _ _ _ _ _ _ _ HC a Hhc); [| exact Hnab | exact Hlz | exact (or_introl Hngh)].
  apply (proj2 (APS.in_ivs_true _ _)). exists e. split; [exact He | lia].
Qed.

Lemma hk_halted : m_halted model = None.
Proof. exact (APS.co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hk_ranges_from : ranges_from_b (m_vm_lazy model) (img_hi A) = true.
Proof.
  unfold ranges_from_b. apply forallb_forall. intros iv Hiv. apply Z.leb_le.
  exact (proj1 (proj1 (Forall_forall _ _) (APS.co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ HC) iv Hiv)).
Qed.

Lemma hk_MInv : MInv (APS.allowA A E ch) model.
Proof. exact (APS.co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

End HK.
