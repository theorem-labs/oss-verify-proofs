(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes
  MmapSim AllocSim FileSim AgentLib ShapeLaws Spec LibWritev RefNodes UbExitBase UbLibCas UbLibCas2 Hoare Frame
  RefMemcpyLib UbMemcpyBase UbMemcpy SymExec
  MallocDefs UbEnframeBase RefEnframeArith UbEnframe UbGetMeta UbFreePro.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan UbSymSlots UbSymPlanSoundA UbSymPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := ImgU.M.loaded_segments.
Section NX0.
Variable nx0 : nat.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

Lemma kread8e_rdn : forall E M k b off v,
  know_ok RSEGS E M k -> kread8e RSEGS k b off = Some v -> flat E (SA b off) 8 ->
  rdn RSEGS M (adenot E (SA b off)) 8 = Some (word_to_le_bytes 8 (edenot E v)).
Proof.
  intros E M k b off v HK H Hfl. apply (kread_rdn RSEGS E M k b off 8 v HK); [exact H | lia | lia | exact Hfl].
Qed.

Lemma times16_denot : forall E e, edenot E (times16 e) = Z_to_bv 64 (16 * bv_unsigned (edenot E e)).
Proof.
  intros E e. unfold times16. rewrite mkMd_denot. apply bv_eq. rewrite u_mul64. cbn [edenot].
  rewrite (u64_lit 16) by lia. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity.
Qed.

Lemma flat_sub : forall E b k n k' n', flat E (SA b k) n -> k <= k' -> 0 < n' -> k' + n' <= k + n -> flat E (SA b k') n'.
Proof. intros E b k n k' n' (F1 & F2 & F3 & F4) H1 H2 H3. unfold flat, estart in *. cbn [a_base a_off] in *. lia. Qed.

Lemma adenot_Z : forall E b k, adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof. intros. reflexivity. Qed.

Lemma wle_low4 : forall z, word_to_le_bytes 4 (Z_to_bv 64 z) = word_to_le_bytes 4 (Z_to_bv 64 (z mod 2 ^ 32)).
Proof.
  intros z. unfold word_to_le_bytes. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- (Z_to_le_bytes_mod 4 (z mod 2 ^ 64)), <- (Z_to_le_bytes_mod 4 ((z mod 2 ^ 32) mod 2 ^ 64)).
  f_equal. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  assert (D : (2 ^ 32 | 2 ^ 64)) by (exists (2 ^ 32); reflexivity).
  rewrite (Z.mod_mod_divide z (2 ^ 64) (2 ^ 32)) by exact D.
  rewrite (Z.mod_mod_divide (z mod 2 ^ 32) (2 ^ 64) (2 ^ 32)) by exact D.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.



(* [comment removed for export] *)
Fixpoint sr_upds (sr : list expr) (ovr : list (nat * expr)) : list expr :=
  match ovr with [] => sr | (i, e) :: r => sr_upds (sr_upd sr i e) r end.

Lemma nth_sr_upds_out : forall ovr sr i, ~ In i (map fst ovr) -> nth i (sr_upds sr ovr) (ELit 0) = nth i sr (ELit 0).
Proof.
  induction ovr as [|[j e] r IH]; intros sr i Hn; cbn [sr_upds]; [reflexivity|].
  rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
  destruct (Nat.eqb_spec i j) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.

Lemma nth_sr_upds_in : forall ovr sr i e, List.NoDup (map fst ovr) -> In (i, e) ovr -> nth i (sr_upds sr ovr) (ELit 0) = e.
Proof.
  induction ovr as [|[j e'] r IH]; intros sr i e Hnd Hin; [destruct Hin|].
  cbn [map fst] in Hnd. inversion Hnd as [|j' r' Hnotin Hnd']; subst.
  cbn [sr_upds]. destruct Hin as [Hin|Hin].
  - injection Hin as -> ->. rewrite nth_sr_upds_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. reflexivity.
  - apply IH; assumption.
Qed.

Lemma regs_after_ovr : forall E sr R R' nx (ovr : list (nat * expr)),
  regs_ok E sr R -> SP.sr_vars_lt nx sr = true ->
  List.NoDup (map fst ovr) ->
  (forall io, In io ovr -> SP.expr_vars_lt nx (snd io) = true /\ getr R' (Z_to_bv 5 (Z.of_nat (fst io))) = edenot E (snd io)) ->
  (forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> ~ In (ridx r) (map fst ovr) -> getr R' r = getr R r) ->
  regs_ok (ext_call E nx R') (sr_upds (sr_fresh sr caller_saved nx) ovr) R'.
Proof.
  intros E sr R R' nx ovr HR Hsv Hnd Hovr Hkept.
  pose proof (ext_call_agree E nx R') as Hag.
  assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (edenot_agree nx); [exact Hag|].
    rewrite <- expr_vars_lt_eq. clear -Hsv Hi. revert i Hi. induction sr as [|e t IH]; intros i Hi; [destruct i; reflexivity|].
    cbn [SP.sr_vars_lt] in Hsv. apply andb_prop in Hsv as [H1 H2]. destruct i; [exact H1 | apply IH; [exact H2 | lia]]. }
  apply regs_ok_pointwise. intros r Hr0. pose proof (ridx_range r) as Hrr.
  destruct (in_dec Nat.eq_dec (ridx r) (map fst ovr)) as [Hin|Hnin].
  - apply in_map_iff in Hin as ([i e] & Hi & Hin). cbn [fst] in Hi. subst i.
    rewrite (nth_sr_upds_in ovr _ (ridx r) e Hnd Hin).
    destruct (Hovr _ Hin) as [Hv Hg]. cbn [fst snd] in Hv, Hg.
    rewrite <- (reg_of_ridx r _ eq_refl) in Hg. rewrite Hg. apply (edenot_agree nx); [exact Hag | rewrite <- expr_vars_lt_eq; exact Hv].
  - rewrite nth_sr_upds_out by exact Hnin.
    destruct (in_dec Nat.eq_dec (ridx r) caller_saved) as [Hcs|Hncs].
    + destruct (In_nth caller_saved (ridx r) 0%nat Hcs) as (j & Hj & Hnth).
      rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
      cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
    + rewrite nth_sr_fresh_out by exact Hncs. rewrite OLD by exact Hrr.
      rewrite (Hkept r Hr0 Hncs Hnin). pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      exact X.
Qed.

(* [comment removed for export] *)
Lemma flat_abs : forall E k n, 0 <= k -> 0 <= n -> k + n < 2 ^ 64 -> flat E (SA (ELit 0) k) n.
Proof.
  intros E k n Hk Hn Hkn. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia.
Qed.

Lemma testbit_mod32 : forall a i, 0 <= i < 32 -> Z.testbit (a mod 2 ^ 32) i = Z.testbit a i.
Proof. intros a i Hi. apply Z.mod_pow2_bits_low. lia. Qed.


(* [comment removed for export] *)
Lemma decode_W_sound : forall E We Se c,
  decode_W We = Some (Se, c) ->
  (4096 * bv_unsigned (edenot E Se) + c < 2 ^ 64)%Z ->
  bv_unsigned (edenot E We) = (4096 * bv_unsigned (edenot E Se) + c)%Z /\ (0 <= c < 4096)%Z.
Proof.
  intros E We Se c H Hb. unfold decode_W in H.
  destruct We as [w|v|op a b|op a b|op a b|op a b|sx lo n a|sx k i n]; try discriminate.
  - (* [comment removed for export] *) injection H as <- <-. cbn [edenot]. rewrite !u_lit64.
    pose proof (Z.mod_pos_bound w two64 ltac:(unfold two64; lia)) as Hw. unfold two64 in *.
    pose proof (Z.div_mod (w mod 2 ^ 64) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (w mod 2 ^ 64) 4096 ltac:(lia)).
    pose proof (Z.div_pos (w mod 2 ^ 64) 4096 ltac:(lia) ltac:(lia)).
    rewrite (Z.mod_small ((w mod 2 ^ 64) / 4096)) by nia. lia.
  - (* [comment removed for export] *)
    destruct op; try discriminate. destruct a as [| | | |mo ma mb| | |]; try discriminate.
    destruct mo; try discriminate. destruct ma as [z| | | | | | |]; try discriminate.
    destruct z as [|pz|pz]; try discriminate.
    repeat (destruct pz as [pz|pz|]; try discriminate).
    destruct b as [c'| | | | | | |]; try discriminate.
    destruct (Z.leb 0 c' && Z.ltb c' 4096)%bool eqn:Hc; [|discriminate]. injection H as <- <-.
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    split; [|lia]. cbn [edenot]. rewrite alu_add, m_mul. unfold v_add, v_mul. rewrite !u_lit64. unfold two64.
    pose proof (u64_range (edenot E mb)).
    rewrite (Z.mod_small (4096 * _)) by lia. rewrite (Z.mod_small c') by lia. apply Z.mod_small. lia.
  - (* [comment removed for export] *)
    destruct op; try discriminate. destruct a as [z| | | | | | |]; try discriminate.
    destruct z as [|pz|pz]; try discriminate.
    repeat (destruct pz as [pz|pz|]; try discriminate).
    injection H as <- <-. split; [|lia]. cbn [edenot]. rewrite m_mul. unfold v_mul. rewrite !u_lit64. unfold two64.
    pose proof (u64_range (edenot E b)). rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.

Lemma decode_W_range : forall We Se c, decode_W We = Some (Se, c) -> (0 <= c < 4096)%Z.
Proof.
  intros We Se c H. unfold decode_W in H.
  destruct We as [w|v|op a b|op a b|op a b|op a b|sx lo n a|sx k i n]; try discriminate.
  - injection H as <- <-. pose proof (Z.mod_pos_bound (w mod two64) 4096 ltac:(lia)). lia.
  - destruct op; try discriminate. destruct a as [| | | |mo ma mb| | |]; try discriminate.
    destruct mo; try discriminate. destruct ma as [z| | | | | | |]; try discriminate.
    destruct z as [|pz|pz]; try discriminate.
    repeat (destruct pz as [pz|pz|]; try discriminate).
    destruct b as [c'| | | | | | |]; try discriminate.
    destruct (Z.leb 0 c' && Z.ltb c' 4096)%bool eqn:Hc; [|discriminate]. injection H as <- <-.
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  - destruct op; try discriminate. destruct a as [z| | | | | | |]; try discriminate.
    destruct z as [|pz|pz]; try discriminate.
    repeat (destruct pz as [pz|pz|]; try discriminate).
    injection H as <- <-. lia.
Qed.

Lemma W_fields : forall m c, (0 <= m)%Z -> (0 <= c < 4096)%Z ->
  w_maplen (4096 * m + c) = m /\ w_lastidx (4096 * m + c) = (c mod 32)%Z /\ w_sizeclass (4096 * m + c) = ((c / 64) mod 64)%Z.
Proof.
  intros m c Hm Hc. unfold w_maplen, w_lastidx, w_sizeclass.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  repeat split; nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End NX0.
