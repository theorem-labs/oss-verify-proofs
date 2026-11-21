(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput, the CONFIG_RSEQ flag, the new auxv layout and the init stack window). *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Mem Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require RzCPS.
From OSSVerify.Proofs.openssl.bignum.lib.P Require InitMem.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxMem AxZZ AxState AxSys AxAcct AxMeasure AxLz AxEntryRel AxFd AxModelRel.
(* RESTORED.  An earlier edit rerouted this file through VCommon/Ax and removed this line
   with the names it was replacing, but two names in the body are still AxA's and not
   VCommon's: [AF] at Section Argv's [Local Notation AFx] (AxA/AxExportV.v:37, a Section
   ExportV definition discharged over rho W J X) and the qualified [AxExport.mX]
   (AxA/AxExport.v).  Without the line rocq stops at the first of them with
   "The reference AF was not found in the current environment"
   (BgAxA|BgAxB/AxExportA.v:106).  It is placed BEFORE the
   AsanW* line below on purpose: the body is written against VCommon/Ax's [eb_*] names,
   so VCommon/Ax must be the later Import and win any clash. *)
From OSSVerify.Proofs.openssl.bignum.lib.AxA Require Import AxExport AxExportH AxExportV.
(* The entry block is now described in the valuation world by [VCommon/Ax]: [AsanWEntry] gives
   [rdB]/[pre]/[tab], [AsanWEb] the byte-level readings [R1_..R7_] of [eb_image] and the named
   [facts_*] accessors, [AsanWEbLoad] [AUX_OFF], and [AxSumLibc]/[AxSumStr] the spans
   [eb_span]/[eb_layout].  [P/InitMem] is no longer the route: its lemmas are now stated over a
   [ProcInput], and [build_stack_bytes_length], [raw_len_nonneg], [raw_len] and [struct_size] are
   gone from the model at LPS 75d69e00. *)
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWEntry AsanWEb AsanWEbLoad AxSumLibc AxSumStr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(** The launch's rseq flag [r] is not pinned, so every [eb_*] name carries it.  It is left
    implicit here: it is always fixed by the [eb_facts] argument, and callers outside this file
    pass that argument positionally. *)
Lemma dec_argvB_eq {r : bool} (ρ : valuation) : eb_facts r ρ -> dec_argvB ρ = dec_argv ρ.
Proof.
  intros Hf. pose proof Hf as (Hc & _ & Hl & _).
  unfold dec_argvB, dec_argv, dec_strs. rewrite Z.mod_small by lia.
  apply map_ext_in. intros k Hk. apply in_seq in Hk. destruct (Hl (Z.of_nat k) ltac:(lia)) as [Hlen _].
  unfold dec_str. replace ((0 <=? Z.of_nat k) && (Z.of_nat k <? 1048576))%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma nth_of_nth_error {T : Type} : forall (l : list T) (n : nat) (x d : T),
  nth_error l n = Some x -> nth n l d = x.
Proof.
  induction l as [|y l IH]; intros [|n] x d H; cbn [nth_error] in H; try discriminate H.
  - injection H as <-. reflexivity.
  - cbn [nth]. exact (IH n x d H).
Qed.

Lemma firstn_plus {T : Type} : forall (k1 k2 : nat) (l : list T),
  firstn (k1 + k2) l = firstn k1 l ++ firstn k2 (skipn k1 l).
Proof.
  induction k1 as [|k1 IH]; intros k2 l; [reflexivity|].
  destruct l as [|x l].
  - cbn [skipn]. rewrite !firstn_nil. reflexivity.
  - cbn [Nat.add firstn skipn app]. rewrite IH. reflexivity.
Qed.

Lemma nth_skipn' {T : Type} (d : T) : forall (o j : nat) (l : list T), nth j (skipn o l) d = nth (o + j) l d.
Proof.
  induction o as [|o IH]; intros j l; [reflexivity|].
  destruct l as [|x l].
  - cbn [skipn]. rewrite !nth_overflow by (cbn [length]; lia). reflexivity.
  - cbn [skipn Nat.add nth]. apply IH.
Qed.

Lemma nth_firstn' {T : Type} (d : T) : forall (k j : nat) (l : list T), (j < k)%nat -> nth j (firstn k l) d = nth j l d.
Proof.
  induction k as [|k IH]; intros j l Hj; [lia|].
  destruct l as [|x l]; [cbn [firstn]; reflexivity|].
  destruct j as [|j]; cbn [firstn nth]; [reflexivity | apply IH; lia].
Qed.

Lemma nth_rdB (d : byte) (bs : list byte) (o k j : nat) : (j < k)%nat ->
  nth j (rdB bs o k) d = nth (o + j) bs d.
Proof. intros Hj. unfold rdB. rewrite (nth_firstn' d k j _ Hj). apply nth_skipn'. Qed.

Lemma rdB_split (bs : list byte) (o k1 k2 : nat) :
  rdB bs o (k1 + k2) = rdB bs o k1 ++ rdB bs (o + k1) k2.
Proof.
  unfold rdB. rewrite firstn_plus, skipn_skipn.
  replace (k1 + o)%nat with (o + k1)%nat by lia. reflexivity.
Qed.

(** [q] rounded up to a multiple of eight stays under a multiple of eight that is nine above it. *)
Lemma round_up_8 (q M : Z) : M mod 8 = 0 -> q + 9 <= M -> q + (- q) mod 8 <= M - 8.
Proof.
  intros HM Hq. pose proof (Z.mod_pos_bound (- q) 8 ltac:(lia)) as Hr.
  Z.div_mod_to_equations. lia.
Qed.

Section Argv.
Hypothesis Hlow : segs_low bgbsegs.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R bgbsegs amodel (MR bgbsegs fs0 ρ) LIM ρ B (mkCfg ms model).
Variable W : list (lin * Z).
Variable J : Z.
Variable X : list (Z * Z).

Local Notation AFx := (AF ρ W J X).
Local Notation m := (AxExport.mX ms model AFx).
Let HM : MR bgbsegs fs0 ρ (a_model B) model := r_model _ _ _ _ _ _ _ HR.

Hypothesis Hent : existsb is_entry (a_mem B) = true.

Hypothesis Hat : alloc_top (m_vmmaps model) <= sp_val ρ.

Local Notation usp := (sp_val ρ).
Local Notation spw := (Z_to_bv 64 (sp_val ρ)).
Local Notation argv := (dec_argv ρ).

(** [KEntry] now carries the rseq flag beside the phdr info, so the block's description is
    [eb_rel r ph ρ _ _ _] and both are existential here. *)
Lemma entry_block : exists (rq : bool) (ph : PhdrInfo), eb_facts rq ρ
  /\ forall z, 0 <= z < Z.of_nat (length (eb_image rq ph ρ)) ->
       ms_mem ms (Z_to_bv 64 (usp + z)) = Some (nth (Z.to_nat z) (eb_image rq ph ρ) (Z_to_bv 8 0)).
Proof.
  apply existsb_exists in Hent as [Rq [HIn He]]. pose proof (r_mem _ _ _ _ _ _ _ HR) as [_ HF]. cbn [cfg_ms] in HF.
  pose proof (proj1 (Forall_forall _ _) HF Rq HIn) as HRq. unfold RRegion in HRq. unfold is_entry in He.
  destruct (rg_kind Rq) as [| | | | rq ph]; try discriminate He. exists rq, ph.
  destruct HRq as (Hf & Hb & _ & Hm). split; [exact Hf|].
  intros z Hz. rewrite Hb in Hm. exact (Hm z Hz).
Qed.

Lemma eb_sp {rq : bool} : eb_facts rq ρ -> bv_unsigned spw = usp /\ sp_window_lo <= usp.
Proof.
  intros Hf. destruct (eb_span rq (mkPhdrInfo 0 0 0) ρ Hf) as (H1 & H2 & HL). split; [|exact H1].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64).
  pose proof (Zle_0_nat (length (eb_image rq (mkPhdrInfo 0 0 0) ρ))).
  unfold sp_window_lo, sp_window_hi in *. lia.
Qed.

Lemma high_vis (z : Z) : 0 <= usp -> usp <= z < 2 ^ 47 -> RzCPS.HID AFx model (wz z) = false.
Proof.
  intros H0 Hz. apply (not_in_entries_vis bgbsegs fs0 LIM ρ B ms model HR W J X z); [lia|].
  intros e He _ Hin.
  pose proof (mr_top bgbsegs fs0 ρ _ model HM (ent_val ρ e) (MR_ent_in bgbsegs fs0 ρ _ model e HM He)) as Ht.
  pose proof (MR_ent bgbsegs fs0 ρ _ model e HM He) as Hok.
  rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok) in Ht. unfold ent_lo, ent_hi in Hin. lia.
Qed.

Lemma argc_len {rq : bool} : eb_facts rq ρ -> Z.of_nat (length (dec_argvB ρ)) = ρ v_argc.
Proof.
  intros Hf. rewrite (dec_argvB_eq ρ Hf). pose proof Hf as (Hc & _).
  unfold dec_argv, dec_strs. rewrite length_map, length_seq. lia.
Qed.

Theorem ex_argv_rep : argv_rep (dec_argvB ρ) m (usp + 8).
Proof.
  destruct entry_block as (rq & ph & Hf & Hmem).
  destruct (eb_sp Hf) as [Eu Hlo].
  rewrite (dec_argvB_eq ρ Hf).

  (* --- the block's shape, all read off [VCommon/Ax] --- *)
  pose proof (eb_span rq ph ρ Hf) as (Hw1 & Hw2 & HL).
  pose proof (eb_layout rq ρ Hf) as (_ & Hargc & Henvc & Hl0 & Hta0 & Hta1 & _).
  pose proof (facts_g rq ph ρ Hf) as Hg.
  pose proof (facts_par rq ph ρ Hf) as Hpar.
  pose proof (facts_xl rq ph ρ Hf) as Hxl.
  pose proof (facts_top8 rq ph ρ Hf) as Htop8.
  pose proof (len_av rq ph ρ Hf) as Lav.
  pose proof (AUX_OFF_rng rq) as Haux.
  pose proof (Z.mod_pos_bound (ρ v_argc + ρ v_envc + 1) 2 ltac:(lia)) as Hmod2.
  assert (Hta00 : 0 <= ρ v_ta)
    by (pose proof Hf as (_ & _ & _ & _ & Hta & _); rewrite Hta; apply total_arg_bytes_nonneg).
  assert (Hte0 : 0 <= ρ v_te)
    by (pose proof Hf as (_ & _ & _ & _ & _ & Hte & _); rewrite Hte; apply total_arg_bytes_nonneg).
  unfold AUX_OFF, sp_window_lo, sp_window_hi in *.
  set (img := eb_image rq ph ρ) in *.
  remember (Z.of_nat (length img)) as LB eqn:ELB.
  pose proof (len_k rq ph ρ Hf 0 ltac:(lia)) as L0. change (Z.to_nat 0) with 0%nat in L0.

  assert (Hhi : usp + LB <= 2 ^ 47) by lia.
  assert (Hlo0 : 0 <= usp) by lia.
  (* [usp + LB] is the block's top, and the launch pins the top to eight. *)
  assert (HM8 : (usp + LB) mod 8 = 0).
  { replace (usp + LB) with (dec_top rq ρ) by (unfold dec_top, str_off; lia). exact Htop8. }

  assert (Hmz : forall z, 0 <= z < LB -> m (wz (usp + z)) = Some (nth (Z.to_nat z) img (Z_to_bv 8 0))).
  { intros z Hz. unfold AxExport.mX, mrestrict.
    rewrite (high_vis (usp + z) ltac:(lia) ltac:(lia)). exact (Hmem z Hz). }

  (* any run of bytes inside the block, read through the restricted memory *)
  assert (SLICE : forall (off : Z) (bs : list byte),
            0 <= off -> off + Z.of_nat (length bs) <= LB ->
            (forall j, (j < length bs)%nat ->
               nth (Z.to_nat (off + Z.of_nat j)) img (Z_to_bv 8 0) = nth j bs (Z_to_bv 8 0)) ->
            bytes_at bgbsegs m (usp + off) bs).
  { intros off bs H0 H1 Hnth. unfold bytes_at. split; [lia|]. split; [lia|].
    intros i Hi. unfold mrd.
    change (wa (usp + off + Z.of_nat i)) with (wz (usp + off + Z.of_nat i)).
    replace (usp + off + Z.of_nat i) with (usp + (off + Z.of_nat i)) by lia.
    rewrite (Hmz (off + Z.of_nat i) ltac:(lia)), (Hnth i Hi).
    symmetry. apply nth_error_nth'. exact Hi. }

  assert (WX : forall a n, usp <= a -> 0 <= n -> a + n <= usp + LB -> wr_at bgbsegs m a n).
  { intros a n H1 H2 H3. unfold wr_at. split; [lia|]. split; [lia|].
    intros i Hi. unfold wview. change (wa (a + i)) with (wz (a + i)).
    replace (a + i) with (usp + (a + i - usp)) by lia. rewrite (Hmz (a + i - usp) ltac:(lia)). discriminate. }

  (* the two obligations [argv_rep] places on one visible argv pointer *)
  assert (POINT : forall (A : Z) (s : list byte),
            usp + 8 + 8 * ρ v_argc <= A ->
            A + Z.of_nat (length s) + 1 + 9 <= usp + LB ->
            bytes_at bgbsegs m A (s ++ [Z_to_bv 8 0]) ->
            (bytes_at bgbsegs m A (s ++ [Z_to_bv 8 0])
             /\ usp + 8 + 8 * Z.of_nat (length argv) <= A
             /\ A + Z.of_nat (length s) + 1 <= USTACK_TOP - 9)
            /\ (exists slack, bytes_at bgbsegs m (A + Z.of_nat (length s) + 1) slack
                  /\ (- (A + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
                  /\ A + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 8)).
  { intros A s HAlo HAend HB.
    pose proof (Z.mod_pos_bound (- (A + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hr.
    pose proof (round_up_8 (A + Z.of_nat (length s) + 1) (usp + LB) HM8 HAend) as Hqr.
    split.
    - split; [exact HB|]. split; [lia|]. unfold USTACK_TOP. lia.
    - set (RR := (- (A + Z.of_nat (length s) + 1)) mod 8) in *.
      set (OFFq := A + Z.of_nat (length s) + 1 - usp).
      assert (EOFFq : OFFq = A + Z.of_nat (length s) + 1 - usp) by reflexivity.
      assert (Hsl : length (rdB img (Z.to_nat OFFq) (Z.to_nat RR)) = Z.to_nat RR).
      { unfold rdB. rewrite firstn_length, skipn_length. lia. }
      assert (HBs : bytes_at bgbsegs m (usp + OFFq) (rdB img (Z.to_nat OFFq) (Z.to_nat RR))).
      { apply (SLICE OFFq); [lia | rewrite Hsl; lia |].
        intros j Hj. rewrite Hsl in Hj.
        rewrite (nth_rdB (Z_to_bv 8 0) img (Z.to_nat OFFq) (Z.to_nat RR) j Hj). f_equal. lia. }
      exists (rdB img (Z.to_nat OFFq) (Z.to_nat RR)).
      split; [|split].
      + replace (A + Z.of_nat (length s) + 1) with (usp + OFFq) by lia. exact HBs.
      + rewrite Hsl. lia.
      + rewrite Hsl. unfold USTACK_TOP. lia. }

  pose proof (R2_argv0 rq ph ρ Hf) as HP0. fold img in HP0.
  pose (A0 := usp + (24 + Z.of_nat (auxv_size rq) + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g)).
  assert (EA0 : A0 = usp + (24 + Z.of_nat (auxv_size rq) + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g))
    by reflexivity.
  assert (U0 : bv_unsigned (Z_to_bv 64 A0) = A0).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }

  assert (S0 : bytes_at bgbsegs m A0 (nth 0 argv [] ++ [Z_to_bv 8 0])).
  { assert (Elen : length (nth 0 argv [] ++ [Z_to_bv 8 0]) = Z.to_nat (ρ (lenvar 0) + 1))
      by (rewrite length_app; cbn [length]; lia).
    rewrite EA0.
    apply (SLICE (24 + Z.of_nat (auxv_size rq) + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g));
      [lia | rewrite Elen; lia |].
    intros j Hj. rewrite Elen in Hj.
    pose proof (R5_str0 rq ph ρ Hf (Z.of_nat j) ltac:(lia)) as HS. fold img in HS. rewrite HS.
    destruct (Z.ltb_spec (Z.of_nat j) (ρ (lenvar 0))) as [Hlt|Hge].
    - rewrite app_nth1 by lia.
      rewrite <- (nth_k rq ph ρ Hf 0 (Z.of_nat j) ltac:(lia) ltac:(lia)).
      change (Z.to_nat 0) with 0%nat. rewrite Nat2Z.id. reflexivity.
    - rewrite app_nth2 by lia.
      replace (j - length (nth 0 argv []))%nat with 0%nat by lia. reflexivity. }

  destruct (Z.le_gt_cases 2 (ρ v_argc)) as [HA2 | HA1].
  - (* argv[0] and argv[1] are both visible *)
    pose proof (R2_argv1 rq ph ρ Hf HA2) as HP1. fold img in HP1.
    pose proof (len_k rq ph ρ Hf 1 ltac:(lia)) as L1. change (Z.to_nat 1) with 1%nat in L1.
    destruct (Hta1 HA2) as [Hl1 Hta2].
    pose (A1 := A0 + ρ (lenvar 0) + 1).
    assert (EA1 : A1 = A0 + ρ (lenvar 0) + 1) by reflexivity.
    assert (U1 : bv_unsigned (Z_to_bv 64 A1) = A1).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }

    assert (S1 : bytes_at bgbsegs m A1 (nth 1 argv [] ++ [Z_to_bv 8 0])).
    { assert (Elen1 : length (nth 1 argv [] ++ [Z_to_bv 8 0]) = Z.to_nat (ρ (lenvar 1) + 1))
        by (rewrite length_app; cbn [length]; lia).
      replace A1 with (usp + (24 + Z.of_nat (auxv_size rq) + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g
                              + ρ (lenvar 0) + 1)) by lia.
      apply (SLICE (24 + Z.of_nat (auxv_size rq) + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g
                    + ρ (lenvar 0) + 1)); [lia | rewrite Elen1; lia |].
      intros j Hj. rewrite Elen1 in Hj.
      pose proof (R5_str1 rq ph ρ Hf HA2 (Z.of_nat j) ltac:(lia)) as HS1. fold img in HS1. rewrite HS1.
      destruct (Z.ltb_spec (Z.of_nat j) (ρ (lenvar 1))) as [Hlt|Hge].
      - rewrite app_nth1 by lia.
        rewrite <- (nth_k rq ph ρ Hf 1 (Z.of_nat j) ltac:(lia) ltac:(lia)).
        change (Z.to_nat 1) with 1%nat. rewrite Nat2Z.id. reflexivity.
      - rewrite app_nth2 by lia.
        replace (j - length (nth 1 argv []))%nat with 0%nat by lia. reflexivity. }

    assert (HPA : bytes_at bgbsegs m (usp + 8) (u64s [Z_to_bv 64 A0; Z_to_bv 64 A1])).
    { assert (ESP : rdB img 8 16 = rdB img 8 8 ++ rdB img 16 8) by exact (rdB_split img 8 8 8).
      assert (EU : u64s [Z_to_bv 64 A0; Z_to_bv 64 A1] = rdB img 8 16).
      { rewrite ESP, HP0, HP1, !InitMem.word_le8_le8. cbn [u64s]. rewrite app_nil_r.
        f_equal; f_equal; f_equal; lia. }
      rewrite EU. apply (SLICE 8 (rdB img 8 16)).
      - lia.
      - unfold rdB. rewrite firstn_length, skipn_length. lia.
      - intros j Hj. unfold rdB in Hj. rewrite firstn_length, skipn_length in Hj.
        rewrite (nth_rdB (Z_to_bv 8 0) img 8 16 j ltac:(lia)). f_equal. lia. }

    unfold argv_rep. exists [Z_to_bv 64 A0; Z_to_bv 64 A1].
    split; [|split; [|split]].
    + unfold u64arr. split; [exact HPA|]. cbn [length]. apply WX; [lia | lia | lia].
    + cbn [length]. lia.
    + intros i s p Hs Hp. pose proof (nth_error_lt _ _ _ Hp) as Hi. cbn [length] in Hi.
      destruct i as [|[|i]]; [| | lia]; cbn [nth_error] in Hp; injection Hp as <-.
      * rewrite U0. assert (Es : nth 0 argv [] = s) by (apply nth_of_nth_error; exact Hs).
        rewrite <- Es. exact (proj1 (POINT A0 (nth 0 argv []) ltac:(lia) ltac:(lia) S0)).
      * rewrite U1. assert (Es : nth 1 argv [] = s) by (apply nth_of_nth_error; exact Hs).
        rewrite <- Es. exact (proj1 (POINT A1 (nth 1 argv []) ltac:(lia) ltac:(lia) S1)).
    + intros i s p Hs Hp. pose proof (nth_error_lt _ _ _ Hp) as Hi. cbn [length] in Hi.
      destruct i as [|[|i]]; [| | lia]; cbn [nth_error] in Hp; injection Hp as <-.
      * rewrite U0. assert (Es : nth 0 argv [] = s) by (apply nth_of_nth_error; exact Hs).
        rewrite <- Es. exact (proj2 (POINT A0 (nth 0 argv []) ltac:(lia) ltac:(lia) S0)).
      * rewrite U1. assert (Es : nth 1 argv [] = s) by (apply nth_of_nth_error; exact Hs).
        rewrite <- Es. exact (proj2 (POINT A1 (nth 1 argv []) ltac:(lia) ltac:(lia) S1)).

  - (* argc = 1: argv[0] alone *)
    assert (HPA : bytes_at bgbsegs m (usp + 8) (u64s [Z_to_bv 64 A0])).
    { assert (EU : u64s [Z_to_bv 64 A0] = rdB img 8 8).
      { rewrite HP0, InitMem.word_le8_le8. cbn [u64s]. rewrite app_nil_r. f_equal; f_equal; lia. }
      rewrite EU. apply (SLICE 8 (rdB img 8 8)).
      - lia.
      - unfold rdB. rewrite firstn_length, skipn_length. lia.
      - intros j Hj. unfold rdB in Hj. rewrite firstn_length, skipn_length in Hj.
        rewrite (nth_rdB (Z_to_bv 8 0) img 8 8 j ltac:(lia)). f_equal. lia. }

    unfold argv_rep. exists [Z_to_bv 64 A0].
    split; [|split; [|split]].
    + unfold u64arr. split; [exact HPA|]. cbn [length]. apply WX; [lia | lia | lia].
    + cbn [length]. lia.
    + intros i s p Hs Hp. pose proof (nth_error_lt _ _ _ Hp) as Hi. cbn [length] in Hi.
      destruct i as [|i]; [|lia]. cbn [nth_error] in Hp. injection Hp as <-.
      rewrite U0. assert (Es : nth 0 argv [] = s) by (apply nth_of_nth_error; exact Hs).
      rewrite <- Es. exact (proj1 (POINT A0 (nth 0 argv []) ltac:(lia) ltac:(lia) S0)).
    + intros i s p Hs Hp. pose proof (nth_error_lt _ _ _ Hp) as Hi. cbn [length] in Hi.
      destruct i as [|i]; [|lia]. cbn [nth_error] in Hp. injection Hp as <-.
      rewrite U0. assert (Es : nth 0 argv [] = s) by (apply nth_of_nth_error; exact Hs).
      rewrite <- Es. exact (proj2 (POINT A0 (nth 0 argv []) ltac:(lia) ltac:(lia) S0)).
Qed.

End Argv.
