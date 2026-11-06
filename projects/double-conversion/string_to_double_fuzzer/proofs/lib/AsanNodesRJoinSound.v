(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanSoundSums AsanNodesRJoin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Lemma xrj_pow2_of_sound : forall c s, XRJ.pow2_of c = Some s -> c = 2 ^ s /\ 0 <= s < 64.
Proof.
  intros c s H. unfold XRJ.pow2_of in H.
  destruct (Z.ltb 0 c && Z.eqb c (2 ^ Z.log2 c) && Z.ltb (Z.log2 c) 64)%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Z.eqb_eq in H2. apply Z.ltb_lt in H3. split; [exact H2|]. split; [apply Z.log2_nonneg | exact H3].
Qed.

Lemma xrj_ones_sub : forall k, 0 <= k <= 64 -> 2 ^ 64 - 2 ^ k = Z.ldiff (Z.ones 64) (Z.ones k).
Proof.
  intros k Hk. rewrite <- Z.sub_nocarry_ldiff.
  - rewrite !Z.ones_equiv. lia.
  - apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [H|H].
    + rewrite Z.ones_spec_low by lia. rewrite Z.ones_spec_low by lia. reflexivity.
    + rewrite Z.ones_spec_high by lia. reflexivity.
Qed.
Lemma xrj_land_negpow2 : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k <= 64 -> Z.land x (2 ^ 64 - 2 ^ k) = 2 ^ k * (x / 2 ^ k).
Proof.
  intros x k Hx Hk. rewrite xrj_ones_sub by lia.
  assert (E : Z.land x (Z.ldiff (Z.ones 64) (Z.ones k)) = Z.ldiff x (Z.ones k)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.ldiff_spec.
    destruct (Z.lt_ge_cases i 64) as [H|H].
    - rewrite (Z.ones_spec_low 64 i) by lia. rewrite Bool.andb_true_l. reflexivity.
    - rewrite (Z.ones_spec_high 64 i) by lia.
      assert (Hb : Z.testbit x i = false).
      { apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec x 0) as [->|Hn0]; [cbn; lia|].
        assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). lia. }
      rewrite Hb. reflexivity. }
  rewrite E. rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. lia.
Qed.

Section FPW. Context {fx : PropExec.FPState}.

Lemma xrj_negpow2_denot : forall (x : word) c s, XRJ.negpow2 c = Some s ->
  mul_div M_MUL (Z_to_bv 64 (2 ^ s)) (alu64 ALU_SRL x (Z_to_bv 64 s)) = alu64 ALU_AND x (Z_to_bv 64 c).
Proof.
  intros x c s H. unfold XRJ.negpow2 in H. apply xrj_pow2_of_sound in H as [Hc Hs].
  apply bv_eq. rewrite u_mul64, u_and64, u_srl64. rewrite !u_lit64a.
  pose proof (u64_range x) as Rx.
  assert (Hcm : c mod 2 ^ 64 = 2 ^ 64 - 2 ^ s) by lia. rewrite Hcm.
  rewrite xrj_land_negpow2 by lia.
  rewrite (Z.mod_small s (2 ^ 64)) by lia. rewrite (Z.mod_small s 64) by lia.
  rewrite (Z.mod_small (2 ^ s)) by (split; [lia|]; apply Z.pow_lt_mono_r; lia).
  apply Z.mod_small. split.
  - apply Z.mul_nonneg_nonneg; [lia|]. apply Z.div_pos; lia.
  - pose proof (Z.mul_div_le (bv_unsigned x) (2 ^ s) ltac:(lia)). lia.
Qed.

Section Sound.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable LINV : (word -> option byte) -> Prop.
  Variable FS0 : Fs.Fs.
  Hypothesis NX0_7 : nx0_ok nx0.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Hypothesis SEGS_wr : APSX.segs_wr_ok SEGS.

  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH LINV FS0) (only parsing).
  #[local] Notation N1 := (node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always) (only parsing).

  Lemma esimp_denot : forall E M k e, know_ok SEGS E M k -> edenot E (XRJ.esimp k e) = edenot E e.
  Proof.
    intros E M k e HK. induction e as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n];
      cbn [XRJ.esimp]; try reflexivity.
    - assert (Hgen : edenot E (mkAluK k op (XRJ.esimp k a) (XRJ.esimp k b)) = edenot E (EAlu op a b)).
      { rewrite (mkAluK_denot SEGS E M k op _ _ HK), IHa, IHb. reflexivity. }
      destruct op; try exact Hgen.
      destruct b as [c| | | | | | |]; try exact Hgen.
      destruct (XRJ.negpow2 c) as [s|] eqn:Hn; [|exact Hgen].
      rewrite mkMd_denot, (mkAluK_denot SEGS E M k ALU_SRL _ _ HK), IHa. cbn [edenot].
      exact (xrj_negpow2_denot (edenot E a) c s Hn).
    - rewrite mkMd_denot, IHa, IHb. reflexivity.
    - destruct (Nat.leb n 8) eqn:Hn; [|reflexivity]. apply Nat.leb_le in Hn.
      rewrite (extK0_denot SEGS E M k _ HK), (mkExt_denot E sx lo n _ Hn), IHa. reflexivity.
  Qed.

  Lemma respellw_ok_sound : forall E M k a e,
    know_ok SEGS E M k -> XRJ.respellw_ok k a e = true -> edenot E a = edenot E e.
  Proof.
    intros E M k a e HK H. unfold XRJ.respellw_ok in H. cbv zeta in H.
    rewrite <- (extK0_denot SEGS E M k a HK), <- (esimp_denot E M k (extK0 k a) HK), <- (esimp_denot E M k e HK).
    apply orb_prop in H as [H|H].
    - apply expr_eqb_eq in H. rewrite H. reflexivity.
    - exact (respell_ok_sound SEGS E M k _ _ HK H).
  Qed.

  Lemma spell_cut_ok : forall E M k b off n,
    know_ok SEGS E M k -> know_ok SEGS E M (XRJ.spell_cut k b off n).
  Proof.
    intros E M k b off n HK. unfold XRJ.spell_cut. rewrite kn_cutoutM_eq.
    assert (HK1 : know_ok SEGS E M (match b with ELit z => kimg_cut k (z + off) n | _ => k end)).
    { destruct b; try exact HK. exact (APSX.kimg_cut_sound SEGS E M k _ n HK). }
    assert (FF : forall (f : kentry -> bool) l, know_ok SEGS E M l -> know_ok SEGS E M (List.filter f l)).
    { intros f l Hl. unfold know_ok in *. apply Forall_forall. intros K HKin. apply filter_In in HKin as [HKin _].
      exact (proj1 (Forall_forall _ _) Hl K HKin). }
    apply Forall_app. split.
    - apply FF. exact HK1.
    - apply FF. apply (know_ok_cutout SEGS E M M _ b off (ELit n)); [exact HK1 | intros; reflexivity].
  Qed.

  Lemma node_spellw_inv : forall cs args cs',
    XRJ.node_spellw SEGS cs args = Some cs' ->
    exists addr n e b off v nx, args = [addr; ELit n; e] /\ split_lit addr = (b, off)
      /\ (Z.leb 1 n && Z.leb n 8 && expr_vars_lt (nxt cs) e && flat_x (kn cs) b off (ELit n))%bool = true
      /\ know_lookup SEGS (kn cs) b off (Z.to_nat n) false [] [] = LHit v [] nx
      /\ XRJ.respellw_ok (kn cs) v e = true
      /\ cs' = set_kn cs (KWord (SA b off) (Z.to_nat n) e :: XRJ.spell_cut (kn cs) b off n).
  Proof.
    intros cs args cs' H. unfold XRJ.node_spellw in H.
    repeat (match type of H with
            | (match ?x with _ => _ end) = Some _ => is_var x; destruct x; try discriminate
            end).
    rename e into addr, e0 into e, z into n.
    destruct (split_lit addr) as [b off] eqn:Hsl.
    destruct (Z.leb 1 n && Z.leb n 8 && expr_vars_lt (nxt cs) e && flat_x (kn cs) b off (ELit n))%bool eqn:Ht; [|discriminate].
    destruct (know_lookup SEGS (kn cs) b off (Z.to_nat n) false [] []) as [v scs nx| |] eqn:Hl; try discriminate.
    destruct scs; [|discriminate].
    destruct (XRJ.respellw_ok (kn cs) v e) eqn:Hok; [|discriminate].
    injection H as <-. exists addr, n, e, b, off, v, nx. repeat split; assumption.
  Qed.

  Theorem node_spellw_sound : forall args, N1 (fun cs => XRJ.node_spellw SEGS cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn.
    destruct (node_spellw_inv cs args cs' Hn) as (addr & n & e & b & off & v & nx & -> & Hsl & Ht & Hl & Hok & ->). clear Hn.
    apply andb_prop in Ht as [Ht Hfx]. apply andb_prop in Ht as [Ht Hve]. apply andb_prop in Ht as [H1 H8].
    apply Z.leb_le in H1. apply Z.leb_le in H8.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (flat_x_sound SEGS E _ (kn cs) b off (ELit n) HK Hfx) as (F1 & F2 & F3).
    rewrite edenot_lit, u64_lit in F2, F3 by lia.
    assert (Hnn : Z.of_nat (Z.to_nat n) = n) by lia.
    assert (Hfl : flat E (SA b off) (Z.of_nat (Z.to_nat n))) by (unfold flat; rewrite Hnn; lia).
    pose proof (know_lookup_sound SEGS E _ (kn cs) b off (Z.to_nat n) false [] [] HK ltac:(lia) ltac:(lia)) as KL.
    rewrite Hl in KL. destruct (KL ltac:(constructor) Hfl) as (bs & HRD & Lb & Hv). clear KL.
    pose proof (respellw_ok_sound E _ (kn cs) v e HK Hok) as Heq.
    assert (HC' : CSOK E (set_kn cs (KWord (SA b off) (Z.to_nat n) e :: XRJ.spell_cut (kn cs) b off n)) R FULL model).
    { apply cs_ok_set_kn; [exact HC|]. constructor; [|exact (spell_cut_ok E _ (kn cs) b off n HK)].
      cbn [kentry_ok]. split; [lia|]. split; [exact Hfl|].
      rewrite HRD. f_equal. rewrite <- Heq, <- Hv. cbn [extz].
      unfold word_to_le_bytes.
      pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Lb in Bb.
      assert (2 ^ (8 * Z.of_nat (Z.to_nat n)) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
      rewrite u64_lit by lia. rewrite <- Lb. symmetry. apply Z_to_le_bytes_to_Z. }
    rewrite <- (pc_set_kn cs (KWord (SA b off) (Z.to_nat n) e :: XRJ.spell_cut (kn cs) b off n)).
    apply (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' eq_refl).
  Qed.

  Theorem node_respellr_sound : forall args, N1 (fun cs => XRJ.node_respellr cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold XRJ.node_respellr in Hn.
    repeat (match type of Hn with
            | (match ?x with _ => _ end) = Some _ => is_var x; destruct x; try discriminate
            end).
    rename z into r.
    destruct (Z.ltb 0 r && Z.ltb r 32 && expr_vars_lt (nxt cs) e && XRJ.respellw_ok (kn cs) (reg cs (Z.to_nat r)) e)%bool eqn:Hc; [|discriminate].
    injection Hn as <-.
    apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2].
    apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
    pose proof (respellw_ok_sound E _ (kn cs) (reg cs (Z.to_nat r)) e (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hok) as Heq.
    assert (HC' : CSOK E (set_reg cs (Z.to_nat r) e) R FULL model).
    { destruct HC; constructor; cbn [set_reg with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
        try assumption; try reflexivity.
      apply regs_ok_respell; [assumption | lia | unfold reg in Heq; symmetry; exact Heq]. }
    change (pc cs) with (pc (set_reg cs (Z.to_nat r) e)).
    apply (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma freshw_core : forall cs E R FULL model T b off n (cut : list kentry),
    CSOK E cs R FULL model ->
    1 <= n -> n <= 8 -> expr_vars_lt (nxt cs) b = true -> kwritable A (kn cs) (kn cs) b off n = true -> fresh_ok nx0 cs = true ->
    (forall E' M, know_ok SEGS E' M (kn cs) -> know_ok SEGS E' M cut) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        CSOK E' (bump (set_kn cs (KWord (SA b off) (Z.to_nat n) (EVar (nxt cs)) :: cut)) 1) R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg_of SEGS R' (pc (bump (set_kn cs (KWord (SA b off) (Z.to_nat n) (EVar (nxt cs)) :: cut)) 1)) FULL' model') T) ->
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T.
  Proof.
    intros cs E R FULL model T b off n cut HC H1 H8 Hbv Hw Hf Hcut Hk.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (fresh_ok_parts nx0 cs Hf) as (_ & _ & _ & Fallow & _ & _ & Fle).
    destruct (APSX.kwritable_sound SEGS A E _ (kn cs) (kn cs) b off n HK HK Hw ltac:(lia)) as (Hst & F1 & F2).
    assert (Hnn : Z.of_nat (Z.to_nat n) = n) by lia.
    destruct (APSX.store_ok_rdn SEGS SEGS_wr (Z.to_nat n) (Mr A argH E cs model FULL) (Z_to_bv 64 (estart E (SA b off))))
      as (bs & HRD & Lb).
    { rewrite u64_lit by lia. rewrite Hnn. lia. }
    { exact Hst. }
    set (v := Z_to_bv 64 (bytes_le_to_Z bs)).
    set (E' := upd E (nxt cs) v).
    assert (Hag : env_agree (nxt cs) E E') by apply upd_agree.
    pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree NX0_7 SINV_agree LINV FS0 E E' cs R FULL model Hag Hf HC) as HC2.
    apply (Hk E' R FULL model (conj (env_agree_le _ _ E E' Hag Fle) Hag)); [|reflexivity].
    change (bump (set_kn cs (KWord (SA b off) (Z.to_nat n) (EVar (nxt cs)) :: cut)) 1)
      with (set_kn (bump cs 1) (KWord (SA b off) (Z.to_nat n) (EVar (nxt cs)) :: cut)).
    apply cs_ok_set_kn.
    - destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
        try assumption; reflexivity.
    - unfold Mr. change (hid A argH E' (bump cs 1) model) with (hid A argH E' cs model).
      rewrite (hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow).
      change (mrestrict (hid A argH E cs model) FULL) with (Mr A argH E cs model FULL).
      pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC2) as HK2. unfold Mr in HK2.
      rewrite (hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow) in HK2.
      assert (Es : estart E' (SA b off) = estart E (SA b off)).
      { unfold estart. cbn [a_base a_off]. f_equal. f_equal. symmetry. exact (edenot_agree' (nxt cs) E E' b Hag Hbv). }
      constructor.
      + cbn [kentry_ok]. split; [lia|]. split.
        * unfold flat. rewrite Es, Hnn. lia.
        * unfold adenot. replace (edenot E' (a_base (SA b off))) with (edenot E (a_base (SA b off)))
            by (cbn [a_base]; exact (edenot_agree' (nxt cs) E E' b Hag Hbv)).
          assert (Ha : adenot E (SA b off) = Z_to_bv 64 (estart E (SA b off))).
          { apply bv_eq. rewrite (flat_u E (SA b off) n) by (unfold flat; lia). rewrite u64_lit by lia. reflexivity. }
          change (v_addi (edenot E (a_base (SA b off))) (a_off (SA b off))) with (adenot E (SA b off)).
          rewrite Ha. rewrite HRD. f_equal.
          change (edenot E' (EVar (nxt cs))) with (ev E' (nxt cs)). unfold E', upd. cbn [ev]. rewrite Nat.eqb_refl.
          unfold v, word_to_le_bytes.
          pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Lb in Bb.
          assert (2 ^ (8 * Z.of_nat (Z.to_nat n)) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
          rewrite u64_lit by lia. rewrite <- Lb. symmetry. apply Z_to_le_bytes_to_Z.
      + apply Hcut. exact HK2.
  Qed.

  Theorem node_freshw_sound : forall args, N1 (fun cs => XRJ.node_freshw A nx0 cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold XRJ.node_freshw in Hn.
    repeat (match type of Hn with
            | (match ?x with _ => _ end) = Some _ => is_var x; destruct x; try discriminate
            end).
    rename e into addr, z into n.
    destruct (split_lit addr) as [b off] eqn:Hsl.
    destruct (Z.leb 1 n && Z.leb n 8 && expr_vars_lt (nxt cs) b && kwritable A (kn cs) (kn cs) b off n && fresh_ok nx0 cs)%bool eqn:Ht; [|discriminate].
    injection Hn as <-.
    apply andb_prop in Ht as [Ht Hf]. apply andb_prop in Ht as [Ht Hw]. apply andb_prop in Ht as [Ht Hbv]. apply andb_prop in Ht as [H1 H8].
    apply Z.leb_le in H1. apply Z.leb_le in H8.
    apply (freshw_core cs E R FULL model T b off n (kn_cutoutM (kn cs) b off (ELit n)) HC H1 H8 Hbv Hw Hf); [|exact Hk].
    intros E' M HK2. rewrite kn_cutoutM_eq. apply (know_ok_cutout SEGS E' M M (kn cs) b off (ELit n)); [exact HK2 | intros; reflexivity].
  Qed.

  Theorem node_freshwk_sound : forall args, N1 (fun cs => XRJ.node_freshwk A nx0 cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold XRJ.node_freshwk in Hn.
    repeat (match type of Hn with
            | (match ?x with _ => _ end) = Some _ => is_var x; destruct x; try discriminate
            end).
    rename e into addr, z into n.
    destruct (split_lit addr) as [b off] eqn:Hsl.
    destruct (Z.leb 1 n && Z.leb n 8 && expr_vars_lt (nxt cs) b && kwritable A (kn cs) (kn cs) b off n && fresh_ok nx0 cs)%bool eqn:Ht; [|discriminate].
    injection Hn as <-.
    apply andb_prop in Ht as [Ht Hf]. apply andb_prop in Ht as [Ht Hw]. apply andb_prop in Ht as [Ht Hbv]. apply andb_prop in Ht as [H1 H8].
    apply Z.leb_le in H1. apply Z.leb_le in H8.
    apply (freshw_core cs E R FULL model T b off n (XRJ.spell_cut (kn cs) b off n) HC H1 H8 Hbv Hw Hf); [|exact Hk].
    intros E' M HK2. apply spell_cut_ok. exact HK2.
  Qed.

  Theorem xrj_xn_ref_sound : forall id args, N1 (XRJ.xn_ref SEGS A nx0 id args).
  Proof.
    intros id args. unfold XRJ.xn_ref.
    destruct (Nat.eqb id 203). { apply node_spellw_sound. }
    destruct (Nat.eqb id 204). { apply node_freshw_sound. }
    destruct (Nat.eqb id 205). { apply node_respellr_sound. }
    destruct (Nat.eqb id 215). { apply node_freshwk_sound. }
    intros cs cs' E R FULL model TT _ _ H. discriminate H.
  Qed.
  (* [comment removed for export] *)
  Theorem xrj_xn_sound : forall id args, N1 (XRJ.xn SEGS A nx0 id args).
  Proof.
    intros id args cs cs' E R FULL model TT HC HX H. rewrite XRJ.xn_eq in H.
    exact (xrj_xn_ref_sound id args cs cs' E R FULL model TT HC HX H).
  Qed.
End Sound.
End FPW.
