(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require PropExec CatExec SymExec3 SymExec3Sound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BLPropExec BMState BMem BCells BStep BLFrame BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsStack0.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_Kit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma wbytes_eq : forall bs m a, CatExec.wbytes m a bs = write_to_mem m a bs.
Proof. induction bs as [|b bs IH]; intros m a; [reflexivity|]. cbn [CatExec.wbytes write_to_mem]. apply IH. Qed.

Lemma rdn_of_ov : forall segs m a n, ov_read_bytes segs m a n = PropExec.rdn segs m a n.
Proof. intros. apply PropExec.ov_rdn. Qed.

Lemma rdn1_of_mrd : forall segs m a b, mrd segs m a = Some b -> PropExec.rdn segs m a 1 = Some [b].
Proof.
  intros segs m a b H. unfold mrd in H. cbn [PropExec.rdn].
  destruct (m a) as [b'|]; [injection H as ->; reflexivity|].
  unfold PropExec.seg_rom. unfold BLPropExec.seg_rom in H. rewrite H. reflexivity.
Qed.

Lemma adenot_of_estart : forall E (a : saddr) (z : Z), estart E a = z -> 0 <= z < 2 ^ 64 -> adenot E a = Z_to_bv 64 z.
Proof.
  intros E a z Hs Hz. unfold adenot, PropExec.v_addi. unfold estart in Hs. rewrite Hs. reflexivity.
Qed.

Lemma kword_of_cells : forall segs E m A cs (k : nat) c (a : saddr) (e : expr) (w : nat),
  cells_at segs m A cs -> cell_at cs k = Some c -> csize c = w -> (1 <= w <= 8)%nat ->
  estart E a = A + Z.of_nat k -> 0 <= A + Z.of_nat k -> A + Z.of_nat k + Z.of_nat w <= 2 ^ 64 ->
  cbytes c = word_to_le_bytes w (edenot E e) ->
  kentry_ok segs E m (KWord a w e).
Proof.
  intros segs E m A cs k c a e w HC Hk Hw Hw8 Hs H0 H1 Hb. cbn [kentry_ok].
  split; [lia|]. split.
  - unfold flat. rewrite Hs. lia.
  - rewrite (adenot_of_estart E a (A + Z.of_nat k) Hs ltac:(lia)). rewrite <- Hb, <- rdn_of_ov, <- Hw.
    exact (cells_at_read segs m A cs k c HC Hk).
Qed.

Lemma kword_of_rw_cells : forall segs E m A cs (k : nat) c (a : saddr) (e : expr) (w : nat),
  rw_cells segs m A cs -> cell_at cs k = Some c -> csize c = w -> (1 <= w <= 8)%nat ->
  estart E a = A + Z.of_nat k -> 0 <= A + Z.of_nat k -> A + Z.of_nat k + Z.of_nat w <= 2 ^ 64 ->
  cbytes c = word_to_le_bytes w (edenot E e) ->
  kentry_ok segs E m (KWord a w e).
Proof. intros segs E m A cs k c a e w [HC _]. eapply kword_of_cells; eassumption. Qed.

Lemma seg0_ro : seg_writable AsanUbsan_segment_000 = false.
Proof. reflexivity. Qed.
Lemma seg1_ro : seg_writable AsanUbsan_segment_001 = false.
Proof. reflexivity. Qed.
Lemma ro_addr_seg01 : forall i, 0x10000 <= i < 0x17e000 -> ro_addr asegs (Z_to_bv 64 i) = true.
Proof.
  intros i Hi. unfold ro_addr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite Z.mod_small by lia.
  (unfold asegs, RefMemImage.Ref.loaded_segments, AsanUbsan.M.loaded_segments,
    AsanUbsan_loaded_segments).
  (cbn [find_segment]).
  (change (seg_base AsanUbsan_segment_000) with 0x10000%N;
  change (seg_size AsanUbsan_segment_000) with 0x81000%N;
  change (seg_base AsanUbsan_segment_001) with 0x91000%N;
  change (seg_size AsanUbsan_segment_001) with 0xed000%N).
  cbn [Z.of_N].
  destruct (Z.ltb_spec i 0x91000) as [H|H].
  - (replace ((65536 <=? i) && (i + 1 <=? 65536 + 528384))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia)).
    (rewrite seg0_ro). reflexivity.
  - replace ((65536 <=? i) && (i + 1 <=? 65536 + 528384))%bool with false
      by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
    replace ((593920 <=? i) && (i + 1 <=? 593920 + 970752))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    rewrite seg1_ro. reflexivity.
Qed.

Lemma kimg_of_mem_inv : forall E m lo hi, mem_inv asegs m -> 0x10000 <= lo -> hi <= 0x17e000 ->
  kentry_ok asegs E m (KImg lo hi).
Proof.
  intros E m lo hi MI H1 H2. cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (m (Z_to_bv 64 i)) as [b|] eqn:Eb; [|reflexivity].
  exfalso. pose proof (MI _ _ Eb) as R. rewrite (ro_addr_seg01 i ltac:(lia)) in R. discriminate.
Qed.

Lemma kwr_of_wr_at : forall segs E m A n (a : saddr) (en : expr),
  wr_at segs m A n -> A <= estart E a -> estart E a + elenZ E en <= A + n -> 0 < elenZ E en ->
  kentry_ok segs E m (KWr a en).
Proof.
  intros segs E m A n a en HW H1 H2 H3. pose proof HW as (HA & HAn & _). cbn [kentry_ok].
  split; [unfold flat; lia|]. intros d mm Hd Hdm.
  replace (estart E a + d) with (A + (estart E a - A + d)) by lia.
  apply (wr_at_store_ok segs m A n); [exact HW | lia | lia].
Qed.

Lemma wr_at_of_stk : forall segs m lo hi, stk segs m lo hi -> wr_at segs m lo (hi - lo).
Proof.
  intros segs m lo hi (H1 & H2 & H). split; [lia|]. split; [lia|]. intros i Hi.
  exact (proj1 (H (lo + i) ltac:(lia))).
Qed.

Lemma kwr_of_stk : forall segs E m lo hi (a : saddr) (en : expr),
  stk segs m lo hi -> lo <= estart E a -> estart E a + elenZ E en <= hi -> 0 < elenZ E en ->
  kentry_ok segs E m (KWr a en).
Proof.
  intros segs E m lo hi a en HS H1 H2 H3. eapply kwr_of_wr_at; [exact (wr_at_of_stk _ _ _ _ HS) | lia | lia | lia].
Qed.

Lemma sh_kit : forall x, 0 <= x -> x / 8 + LbB_Kit.SHBASE = sh x.
Proof. intros x Hx. unfold sh, LbB_Kit.SHBASE. rewrite ASHADOW_BASE_val. lia. Qed.

Lemma shk_of_mrd : forall m x b, 0 <= x -> mrd asegs m (wa (sh x)) = Some b -> LbB_Kit.shk m x (bv_unsigned b).
Proof.
  intros m x b Hx H. unfold LbB_Kit.shk. rewrite (sh_kit x Hx).
  replace (Z_to_bv 8 (bv_unsigned b)) with b
    by (apply bv_eq; rewrite Z_to_bv_unsigned; rewrite bv_wrap_small; [reflexivity | apply bv_unsigned_in_range]).
  exact (rdn1_of_mrd asegs m (wa (sh x)) b H).
Qed.

Lemma sh0_of_mrd : forall m x, 0 <= x -> mrd asegs m (wa (sh x)) = Some (b8 0) -> LbB_Kit.sh0 m x.
Proof. intros m x Hx H. pose proof (shk_of_mrd m x (b8 0) Hx H) as K. exact K. Qed.

Lemma shk_of_SHAD : forall m A sbs x,
  SHAD m A sbs -> A <= x < A + 8 * Z.of_nat (length sbs) ->
  exists b, nth_error sbs (Z.to_nat ((x - A) / 8)) = Some b /\ LbB_Kit.shk m x (bv_unsigned b).
Proof.
  intros m A sbs x (HA & HA8 & [(H0 & H1 & HB) _]) Hx.
  assert (Hi : (Z.to_nat ((x - A) / 8) < length sbs)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_lt_upper_bound; lia. }
  destruct (nth_error sbs (Z.to_nat ((x - A) / 8))) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  exists b. split; [reflexivity|]. apply shk_of_mrd; [lia|].
  rewrite <- E, <- HB by exact Hi. f_equal. f_equal. rewrite Z2Nat.id by (apply Z.div_pos; lia).
  unfold sh. Z.div_mod_to_equations. nia.
Qed.

Lemma sh0_of_SHAD0 : forall m A k x,
  SHAD m A (repeat (b8 0) k) -> A <= x < A + 8 * Z.of_nat k -> LbB_Kit.sh0 m x.
Proof.
  intros m A k x H Hx. rewrite <- (repeat_length (b8 0) k) in Hx.
  destruct (shk_of_SHAD m A _ x H Hx) as (b & Hb & K). apply nth_error_In in Hb. apply repeat_spec in Hb. subst b.
  exact K.
Qed.

Lemma sh0_of_addressable : forall m A n x,
  addressable m A n -> A <= x < A + 8 * (n / 8) -> LbB_Kit.sh0 m x.
Proof.
  intros m A n x (Hn & H) Hx. unfold shadow_of in H.
  assert (HS : SHAD m A (repeat (b8 0) (Z.to_nat (n / 8)))).
  { destruct H as (HA & HA8 & [B W]). split; [exact HA|]. split; [exact HA8|]. split.
    - exact (proj1 (proj1 (bytes_at_app asegs m (sh A) _ _) B)).
    - destruct W as (W1 & W2 & W). split; [lia|]. rewrite repeat_length. split; [rewrite length_app, repeat_length in W2; lia|].
      intros i Hi. apply W. rewrite length_app, repeat_length. lia. }
  eapply sh0_of_SHAD0; [exact HS|]. rewrite Z2Nat.id by (apply Z.div_pos; lia). exact Hx.
Qed.

Section S0.
  Context {HCEIL : HeapCeil}.
  Lemma sh0_of_stack0 : forall m lo hi x, stack0 m lo hi -> lo <= x < hi -> LbB_Kit.sh0 m x.
  Proof.
    intros m lo hi x (g & H1 & H2 & H3 & AD) Hx. eapply sh0_of_addressable; [exact AD|].
    Z.div_mod_to_equations. nia.
  Qed.
End S0.

Lemma munch_mem_denot : forall W E M log,
  log_flat E log ->
  Forall (fun se => inside W (estart E (e_addr se)) (Z.of_nat (e_width se))) log ->
  munch W M (mem_denot E M log).
Proof.
  intros W E M log. induction log as [|[a w v] rest IH]; intros Hf Hin; cbn [mem_denot]; [apply munch_refl|].
  cbn [log_flat] in Hf. destruct Hf as (Hw & Hfl & Hf). inversion Hin as [|? ? Hin0 Hin1]; subst. cbn [e_addr e_width] in Hin0.
  rewrite wbytes_eq.
  pose proof (flat_u E a (Z.of_nat w) Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  replace (adenot E a) with (wa (estart E a)) by (apply bv_eq; rewrite Hu; unfold wa; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; apply Z.mod_small; lia).
  apply munch_write; [exact (IH Hf Hin1) | lia | |].
  - rewrite CatExec.length_N_to_le_bytes. lia.
  - rewrite CatExec.length_N_to_le_bytes. exact Hin0.
Qed.

Lemma wmono_mem_denot : forall E M log, wmono asegs M (mem_denot E M log).
Proof.
  intros E M log. induction log as [|[a w v] rest IH]; cbn [mem_denot]; [apply wmono_refl|].
  rewrite wbytes_eq. apply wmono_write. exact IH.
Qed.

Lemma mem_denot_cases : forall E M log x, mem_denot E M log x = M x \/ exists b, mem_denot E M log x = Some b.
Proof.
  intros E M log. induction log as [|[a w v] rest IH]; intros x; cbn [mem_denot]; [left; reflexivity|].
  rewrite wbytes_eq. generalize (word_to_le_bytes w (edenot E v)) (adenot E a) (mem_denot E M rest) (IH x).
  clear IH. intros bs. induction bs as [|b bs IHb]; intros ad M' HM'; cbn [write_to_mem]; [exact HM'|].
  apply IHb. cbn. destruct (bv_eqb x ad); [right; eexists; reflexivity | exact HM'].
Qed.

Lemma stk_mem_denot : forall E M log lo hi, stk asegs M lo hi -> stk asegs (mem_denot E M log) lo hi.
Proof.
  intros E M log lo hi (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hw (b & Hb)]. split.
  - exact (wmono_mem_denot E M log _ Hw).
  - unfold mrd in *. destruct (mem_denot_cases E M log (wa a)) as [Ee|(b' & Ee)]; rewrite Ee; [exists b; exact Hb | exists b'; reflexivity].
Qed.

Lemma rdn_HL : forall segs m n a, PropExec.rdn segs m a n = BLPropExec.rdn segs m a n.
Proof.
  intros segs m n. induction n as [|n IH]; intros a; [reflexivity|]. cbn [PropExec.rdn BLPropExec.rdn].
  unfold PropExec.seg_rom, BLPropExec.seg_rom. rewrite IH. reflexivity.
Qed.

Lemma bytes_at_of_rdn : forall segs m (a : Z) bs,
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  PropExec.rdn segs m (Z_to_bv 64 a) (length bs) = Some bs -> bytes_at segs m a bs.
Proof.
  intros segs m a bs H0 H1 H. split; [lia|]. split; [lia|].
  revert a H0 H1 H. induction bs as [|b bs IH]; intros a H0 H1 H i Hi; [cbn in Hi; lia|].
  cbn [length PropExec.rdn] in H.
  destruct (match m (Z_to_bv 64 a) with Some b0 => Some b0 | None => PropExec.seg_rom segs (Z_to_bv 64 a) end) as [b0|] eqn:E0; [|discriminate].
  destruct (PropExec.rdn segs m (Z_to_bv 64 a + 1) (length bs)) as [r|] eqn:E1; [|discriminate].
  injection H as <- <-.
  destruct i as [|i].
  - cbn. rewrite Z.add_0_r. unfold mrd, wa. unfold PropExec.seg_rom in E0. unfold BLPropExec.seg_rom. exact E0.
  - cbn [nth_error]. cbn [length] in H1.
    assert (Ea : (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1)).
    { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
      replace (bv_unsigned (1 : bv 64)) with 1 by reflexivity. rewrite Zplus_mod_idemp_l. reflexivity. }
    rewrite Ea in E1.
    pose proof (IH (a + 1) ltac:(lia) ltac:(lia) E1 i ltac:(cbn in Hi; lia)) as K.
    replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. exact K.
Qed.

Lemma rdn_mem_denot_hit8 : forall segs E M pre (a : saddr) (v : expr) post,
  log_flat E (pre ++ SE a 8 v :: post) ->
  Forall (fun e' => estart E (e_addr e') + Z.of_nat (e_width e') <= estart E a \/ estart E a + 8 <= estart E (e_addr e')) pre ->
  PropExec.rdn segs (mem_denot E M (pre ++ SE a 8 v :: post)) (adenot E a) 8 = Some (word_to_le_bytes 8 (edenot E v)).
Proof.
  intros segs E M pre a v post. induction pre as [|[a' w' v'] pre IH]; intros Hf Hd.
  - cbn [app mem_denot]. cbn [log_flat] in Hf. destruct Hf as (_ & Hfl & _).
    pose proof (flat_u E a 8 Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
    apply SeqExec.rdn_wbytes_hit8. rewrite Hu. cbn in F4. lia.
  - cbn [app mem_denot]. cbn [app log_flat] in Hf. destruct Hf as (Hw' & Hfl' & Hf).
    inversion Hd as [|? ? Hd0 Hd1]; subst. cbn [e_addr e_width] in Hd0.
    pose proof (flat_u E a' (Z.of_nat w') Hfl') as Hu'. destruct Hfl' as (F1 & F2 & F3 & F4).
    assert (Hfa : flat E a 8).
    { clear - Hf. induction pre as [|[x y z] pre IH]; cbn [app log_flat] in Hf; [exact (proj1 (proj2 Hf)) | exact (IH (proj2 (proj2 Hf)))]. }
    pose proof (flat_u E a 8 Hfa) as Hu. destruct Hfa as (G1 & G2 & G3 & G4).
    rewrite CatExec.rdn_wbytes_out.
    + exact (IH Hf Hd1).
    + rewrite Hu, Hu', CatExec.length_N_to_le_bytes. lia.
    + rewrite Hu. lia.
    + rewrite Hu', CatExec.length_N_to_le_bytes. lia.
Qed.

Lemma rw_cells_mem_denot_C8 : forall E M pre (a : saddr) (v : expr) post (A : Z),
  log_flat E (pre ++ SE a 8 v :: post) ->
  Forall (fun e' => estart E (e_addr e') + Z.of_nat (e_width e') <= estart E a \/ estart E a + 8 <= estart E (e_addr e')) pre ->
  estart E a = A -> wr_at asegs M A 8 ->
  rw_cells asegs (mem_denot E M (pre ++ SE a 8 v :: post)) A [C8 (edenot E v)].
Proof.
  intros E M pre a v post A Hf Hd Hs HW.
  assert (Hfa : flat E a 8).
  { clear - Hf. induction pre as [|[x y z] pre IH]; cbn [app log_flat] in Hf; [exact (proj1 (proj2 Hf)) | exact (IH (proj2 (proj2 Hf)))]. }
  pose proof (flat_u E a 8 Hfa) as Hu. pose proof Hfa as (G1 & G2 & G3 & G4).
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le8.
    apply bytes_at_of_rdn; [lia | rewrite CatExec.length_N_to_le_bytes; cbn in G4; lia |].
    rewrite CatExec.length_N_to_le_bytes. replace (Z_to_bv 64 A) with (adenot E a).
    + apply rdn_mem_denot_hit8; assumption.
    + apply bv_eq. rewrite Hu, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small; lia.
  - cbn [cells_size csize]. destruct HW as (W1 & W2 & W). split; [lia|]. split; [lia|].
    intros i Hi. exact (wmono_mem_denot E M _ _ (W i Hi)).
Qed.

Lemma rdn_mem_denot_hit : forall segs E M pre (a : saddr) (w : nat) (v : expr) post,
  log_flat E (pre ++ SE a w v :: post) ->
  Forall (fun e' => estart E (e_addr e') + Z.of_nat (e_width e') <= estart E a \/ estart E a + Z.of_nat w <= estart E (e_addr e')) pre ->
  PropExec.rdn segs (mem_denot E M (pre ++ SE a w v :: post)) (adenot E a) w = Some (word_to_le_bytes w (edenot E v)).
Proof.
  intros segs E M pre a w v post. induction pre as [|[a' w' v'] pre IH]; intros Hf Hd.
  - cbn [app mem_denot]. cbn [log_flat] in Hf. destruct Hf as (_ & Hfl & _).
    pose proof (flat_u E a (Z.of_nat w) Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
    pose proof (SeqExec.rdn_wbytes_hit segs (word_to_le_bytes w (edenot E v)) (mem_denot E M post) (adenot E a)) as K.
    rewrite CatExec.length_N_to_le_bytes in K. apply K. rewrite Hu. lia.
  - cbn [app mem_denot]. cbn [app log_flat] in Hf. destruct Hf as (Hw' & Hfl' & Hf).
    inversion Hd as [|? ? Hd0 Hd1]; subst. cbn [e_addr e_width] in Hd0.
    pose proof (flat_u E a' (Z.of_nat w') Hfl') as Hu'. destruct Hfl' as (F1 & F2 & F3 & F4).
    assert (Hfa : flat E a (Z.of_nat w)).
    { clear - Hf. induction pre as [|[x y z] pre IH]; cbn [app log_flat] in Hf; [exact (proj1 (proj2 Hf)) | exact (IH (proj2 (proj2 Hf)))]. }
    pose proof (flat_u E a (Z.of_nat w) Hfa) as Hu. destruct Hfa as (G1 & G2 & G3 & G4).
    rewrite CatExec.rdn_wbytes_out.
    + exact (IH Hf Hd1).
    + rewrite Hu, Hu', CatExec.length_N_to_le_bytes. lia.
    + rewrite Hu. lia.
    + rewrite Hu', CatExec.length_N_to_le_bytes. lia.
Qed.

Lemma log_flat_mid : forall E pre (a : saddr) (w : nat) (v : expr) post,
  log_flat E (pre ++ SE a w v :: post) -> (w <= 8)%nat /\ flat E a (Z.of_nat w).
Proof.
  intros E pre a w v post Hf.
  induction pre as [|[x y z] pre IH]; cbn [app log_flat] in Hf; [exact (conj (proj1 Hf) (proj1 (proj2 Hf))) | exact (IH (proj2 (proj2 Hf)))].
Qed.

Lemma rw_cells_mem_denot_w : forall E M pre (a : saddr) (w : nat) (v : expr) post (A : Z) (c : cell),
  log_flat E (pre ++ SE a w v :: post) ->
  Forall (fun e' => estart E (e_addr e') + Z.of_nat (e_width e') <= estart E a \/ estart E a + Z.of_nat w <= estart E (e_addr e')) pre ->
  estart E a = A -> wr_at asegs M A (Z.of_nat w) ->
  csize c = w -> cell_wf c -> cbytes c = word_to_le_bytes w (edenot E v) ->
  rw_cells asegs (mem_denot E M (pre ++ SE a w v :: post)) A [c].
Proof.
  intros E M pre a w v post A c Hf Hd Hs HW Hc Hwf Hb.
  pose proof (log_flat_mid E pre a w v post Hf) as [Hw8 Hfa].
  pose proof (flat_u E a (Z.of_nat w) Hfa) as Hu. pose proof Hfa as (G1 & G2 & G3 & G4).
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes]. rewrite app_nil_r, Hb.
    apply bytes_at_of_rdn; [lia | rewrite CatExec.length_N_to_le_bytes; lia |].
    rewrite CatExec.length_N_to_le_bytes. replace (Z_to_bv 64 A) with (adenot E a).
    + apply rdn_mem_denot_hit; assumption.
    + apply bv_eq. rewrite Hu, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small; lia.
  - cbn [cells_size]. rewrite Hc, Nat.add_0_r. destruct HW as (W1 & W2 & W). split; [lia|]. split; [lia|].
    intros i Hi. exact (wmono_mem_denot E M _ _ (W i Hi)).
Qed.

Lemma rw_cells_to_CB : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs [[Hwf HB] HW]. split; [split|].
  - cbn. split; [exact (cells_bytes_length cs Hwf) | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma rw_cells_log_nth : forall E M lg (k : nat) (a : saddr) (w : nat) (v : expr) (A : Z) (c : cell),
  log_flat E lg -> nth_error lg k = Some (SE a w v) ->
  Forall (fun e' => estart E (e_addr e') + Z.of_nat (e_width e') <= estart E a \/ estart E a + Z.of_nat w <= estart E (e_addr e')) (firstn k lg) ->
  estart E a = A -> wr_at asegs M A (Z.of_nat w) ->
  csize c = w -> cell_wf c -> cbytes c = word_to_le_bytes w (edenot E v) ->
  rw_cells asegs (mem_denot E M lg) A [c].
Proof.
  intros E M lg k a w v A c Hf Hn Hd Hs HW Hc Hwf Hb.
  assert (Hlg : lg = firstn k lg ++ SE a w v :: skipn (S k) lg).
  { clear - Hn. revert k Hn. induction lg as [|x lg IH]; intros k Hn; [destruct k; discriminate|].
    destruct k as [|k]; cbn in Hn |- *; [injection Hn as ->; reflexivity|]. f_equal. exact (IH k Hn). }
  rewrite Hlg in Hf |- *. eapply (rw_cells_mem_denot_w E M (firstn k lg) a w v (skipn (S k) lg) A c); eassumption.
Qed.

Definition sb_disj (b : expr) (off : Z) (w : nat) (l : list sentry) : bool :=
  forallb (fun e' => expr_eqb (a_base (e_addr e')) b
                     && ((a_off (e_addr e') + Z.of_nat (e_width e') <=? off) || (off + Z.of_nat w <=? a_off (e_addr e')))) l.

Lemma rw_cells_log_nth_sb : forall E M lg (k : nat) (b : expr) (off : Z) (w : nat) (v : expr) (A : Z) (c : cell),
  log_flat E lg -> nth_error lg k = Some (SE (SA b off) w v) ->
  sb_disj b off w (firstn k lg) = true ->
  bv_unsigned (edenot E b) + off = A -> wr_at asegs M A (Z.of_nat w) ->
  csize c = w -> cell_wf c -> cbytes c = word_to_le_bytes w (edenot E v) ->
  rw_cells asegs (mem_denot E M lg) A [c].
Proof.
  intros E M lg k b off w v A c Hf Hn Hd HA HW Hc Hwf Hb.
  eapply (rw_cells_log_nth E M lg k (SA b off) w v A c Hf Hn); [| unfold estart; cbn [a_base a_off]; exact HA | exact HW | exact Hc | exact Hwf | exact Hb].
  apply Forall_forall. intros e' He'. unfold sb_disj in Hd. rewrite forallb_forall in Hd. specialize (Hd e' He').
  apply andb_true_iff in Hd as [Hbe Ho]. apply expr_eqb_true in Hbe.
  unfold estart. cbn [a_base a_off]. rewrite Hbe.
  apply orb_true_iff in Ho. destruct Ho as [Ho|Ho]; apply Z.leb_le in Ho; [left|right]; lia.
Qed.

Fixpoint ff_val (b : expr) (o : Z) (lg : list sentry) : option expr :=
  match lg with
  | [] => None
  | SE (SA b' o') w v :: t =>
      if expr_eqb b' b then
        (if (o' =? o) && Nat.eqb w 8 then Some v
         else if (o' + Z.of_nat w <=? o) || (o + 8 <=? o') then ff_val b o t else None)
      else ff_val b o t
  end.

Lemma ff_val_spec : forall b o lg v, ff_val b o lg = Some v ->
  exists k, nth_error lg k = Some (SE (SA b o) 8 v)
    /\ Forall (fun e' => expr_eqb (a_base (e_addr e')) b = true ->
                         a_off (e_addr e') + Z.of_nat (e_width e') <= o \/ o + 8 <= a_off (e_addr e')) (firstn k lg).
Proof.
  intros b o lg v. induction lg as [|[[b' o'] w v'] t IH]; intros Hf; cbn [ff_val] in Hf; [discriminate|].
  destruct (expr_eqb b' b) eqn:Eb.
  - destruct ((o' =? o) && Nat.eqb w 8) eqn:Eo.
    + injection Hf as <-. apply andb_true_iff in Eo as [E1 E2]. apply Z.eqb_eq in E1. apply Nat.eqb_eq in E2. subst.
      apply expr_eqb_true in Eb. subst. exists 0%nat. split; [reflexivity|]. constructor.
    + destruct ((o' + Z.of_nat w <=? o) || (o + 8 <=? o')) eqn:Ed; [|discriminate].
      destruct (IH Hf) as (k & Hn & Hd). exists (S k). split; [exact Hn|].
      cbn [firstn]. constructor; [|exact Hd]. cbn [e_addr a_base a_off e_width]. intros _.
      apply orb_true_iff in Ed. destruct Ed as [Ed|Ed]; apply Z.leb_le in Ed; [left|right]; lia.
  - destruct (IH Hf) as (k & Hn & Hd). exists (S k). split; [exact Hn|].
    cbn [firstn]. constructor; [|exact Hd]. cbn [e_addr a_base]. rewrite Eb. discriminate.
Qed.

Definition lit_eqb (v : expr) (w : Z) : bool := match v with ELit z => z =? w | _ => false end.
Lemma lit_eqb_true : forall v w, lit_eqb v w = true -> v = ELit w.
Proof. intros v w. destruct v; cbn; intros Hv; try discriminate. apply Z.eqb_eq in Hv. subst. reflexivity. Qed.

Lemma in_firstn_l : forall (A : Type) (x : A) k l, In x (firstn k l) -> In x l.
Proof. intros A x k. induction k as [|k IH]; intros l Hin; [destruct Hin|]. destruct l as [|y l]; [destruct Hin|].
  cbn in Hin. destruct Hin as [Hin|Hin]; [left; exact Hin | right; exact (IH l Hin)]. Qed.

Lemma rw_cells_cons8_c : forall m A (w : word) cs, rw_cells asegs m A [C8 w] -> rw_cells asegs m (A + 8) cs -> rw_cells asegs m A (C8 w :: cs).
Proof. intros m A w cs H1 H2. change (C8 w :: cs) with ([C8 w] ++ cs). apply rw_cells_app. split; [exact H1|]. exact H2. Qed.

Fixpoint blk_ok (b : expr) (o : Z) (ws : list Z) (lg : list sentry) : bool :=
  match ws with
  | [] => true
  | w :: ws' => match ff_val b o lg with Some v => lit_eqb v w && blk_ok b (o + 8) ws' lg | None => false end
  end.

Lemma rw_cells_log_block : forall E M lg (b : expr) (ws : list Z) (o0 A : Z),
  log_flat E lg ->
  blk_ok b o0 ws lg = true ->
  bv_unsigned (edenot E b) + o0 = A ->
  wr_at asegs M A (8 * Z.of_nat (length ws)) ->
  Forall (fun e' => expr_eqb (a_base (e_addr e')) b = false ->
                    estart E (e_addr e') + Z.of_nat (e_width e') <= A \/ A + 8 * Z.of_nat (length ws) <= estart E (e_addr e')) lg ->
  rw_cells asegs (mem_denot E M lg) A (map (fun z => C8 (wz z)) ws).
Proof.
  intros E M lg b ws. induction ws as [|w ws IH]; intros o0 A Hf Hb HA HW HO.
  - destruct HW as (W1 & W2 & W). cbn [length Z.of_nat] in W2.
    split; [split; [exact I | split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]] |].
    cbn. split; [lia|]. split; [lia|]. intros i Hi; lia.
  - cbn [blk_ok] in Hb. destruct (ff_val b o0 lg) as [v|] eqn:Ev; [|discriminate].
    apply andb_true_iff in Hb as [Hz Hb]. apply lit_eqb_true in Hz. subst v.
    cbn [map]. apply rw_cells_cons8_c.
    + destruct (ff_val_spec b o0 lg (ELit w) Ev) as (k & Hn & Hd).
      eapply (rw_cells_log_nth E M lg k (SA b o0) 8 (ELit w) A (C8 (wz w)) Hf Hn).
      * apply Forall_forall. intros e' He'. destruct (expr_eqb (a_base (e_addr e')) b) eqn:Eb'.
        -- rewrite Forall_forall in Hd. specialize (Hd e' He' Eb'). apply expr_eqb_true in Eb'.
           unfold estart. rewrite Eb'. cbn [a_base a_off]. lia.
        -- rewrite Forall_forall in HO. pose proof (in_firstn_l _ _ _ _ He') as He2.
           specialize (HO e' He2 Eb'). unfold estart at 2 3. cbn [a_base a_off]. cbn [length] in HO. lia.
      * unfold estart. cbn [a_base a_off]. exact HA.
      * destruct HW as (W1 & W2 & W). cbn [length] in W2, W. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
      * reflexivity.
      * exact I.
      * reflexivity.
    + apply (IH (o0 + 8) (A + 8) Hf Hb); [lia | |].
      * destruct HW as (W1 & W2 & W). cbn [length] in W2, W. split; [lia|]. split; [lia|]. intros i Hi.
        replace (A + 8 + i) with (A + (8 + i)) by lia. apply W. lia.
      * eapply Forall_impl; [| exact HO]. intros e' K Hb'. specialize (K Hb'). cbn [length] in K. lia.
Qed.

Definition tb_ok (b b' : expr) (off : Z) (w : nat) (lo' hi' : Z) (l : list sentry) : bool :=
  forallb (fun e' => if expr_eqb (a_base (e_addr e')) b
                     then (a_off (e_addr e') + Z.of_nat (e_width e') <=? off) || (off + Z.of_nat w <=? a_off (e_addr e'))
                     else expr_eqb (a_base (e_addr e')) b' && (lo' <=? a_off (e_addr e')) && (a_off (e_addr e') + Z.of_nat (e_width e') <=? hi')) l.

Lemma rw_cells_log_nth_2b : forall E M lg (k : nat) (b b' : expr) (off : Z) (w : nat) (v : expr) (lo' hi' A : Z) (c : cell),
  log_flat E lg -> nth_error lg k = Some (SE (SA b off) w v) ->
  tb_ok b b' off w lo' hi' (firstn k lg) = true ->
  bv_unsigned (edenot E b) + off = A ->
  (A + Z.of_nat w <= bv_unsigned (edenot E b') + lo' \/ bv_unsigned (edenot E b') + hi' <= A) ->
  wr_at asegs M A (Z.of_nat w) ->
  csize c = w -> cell_wf c -> cbytes c = word_to_le_bytes w (edenot E v) ->
  rw_cells asegs (mem_denot E M lg) A [c].
Proof.
  intros E M lg k b b' off w v lo' hi' A c Hf Hn Hd HA HD HW Hc Hwf Hb.
  eapply (rw_cells_log_nth E M lg k (SA b off) w v A c Hf Hn); [| unfold estart; cbn [a_base a_off]; exact HA | exact HW | exact Hc | exact Hwf | exact Hb].
  apply Forall_forall. intros e' He'. unfold tb_ok in Hd. rewrite forallb_forall in Hd. specialize (Hd e' He').
  destruct (expr_eqb (a_base (e_addr e')) b) eqn:Eb.
  - apply expr_eqb_true in Eb. unfold estart. rewrite Eb. cbn [a_base a_off].
    apply orb_true_iff in Hd. destruct Hd as [Ho|Ho]; apply Z.leb_le in Ho; [left|right]; lia.
  - apply andb_true_iff in Hd as [Hd H2]. apply andb_true_iff in Hd as [Hb' H1]. apply expr_eqb_true in Hb'.
    apply Z.leb_le in H1, H2. unfold estart. rewrite Hb'. cbn [a_base a_off]. lia.
Qed.

Fixpoint sb_inside (W : list (Z * Z)) (o : Z) (w : Z) : bool :=
  match W with [] => false | (lo, hi) :: W' => ((lo <=? o) && (o + w <=? hi)) || sb_inside W' o w end.

Lemma sb_inside_sound : forall W base o w, sb_inside W o w = true ->
  inside (map (fun iv : Z * Z => (base + fst iv, base + snd iv)) W) (base + o) w.
Proof.
  induction W as [|[lo hi] W IH]; intros base o w Hs; cbn in Hs |- *; [discriminate|].
  apply orb_true_iff in Hs. destruct Hs as [Hs|Hs].
  - left. apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1, H2. lia.
  - right. apply IH. exact Hs.
Qed.

Lemma munch_mem_denot_sb : forall (W : list (Z * Z)) (b : expr) E M log,
  log_flat E log ->
  forallb (fun se => expr_eqb (a_base (e_addr se)) b && sb_inside W (a_off (e_addr se)) (Z.of_nat (e_width se))) log = true ->
  munch (map (fun iv : Z * Z => (bv_unsigned (edenot E b) + fst iv, bv_unsigned (edenot E b) + snd iv)) W) M (mem_denot E M log).
Proof.
  intros W b E M log Hf Hb. apply munch_mem_denot; [exact Hf|].
  apply Forall_forall. intros se Hse. rewrite forallb_forall in Hb. specialize (Hb se Hse).
  apply andb_true_iff in Hb as [Hbe Hi]. apply expr_eqb_true in Hbe.
  unfold estart. rewrite Hbe. apply sb_inside_sound. exact Hi.
Qed.

Ltac kword_cell CELLS k c :=
  eapply (kword_of_rw_cells _ _ _ _ _ k c);
  [ exact CELLS | reflexivity | reflexivity | lia
  | unfold SymExec3Sound.SX2S.estart; HLib.evs; rewrite ?HLib.u64_of_Z by lia; cbn [SymExec3.SX2.a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
  | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | reflexivity ].

Lemma munch_mem_denot_2b : forall (W W' : list (Z * Z)) (b b' : expr) E M log,
  log_flat E log ->
  forallb (fun se => (expr_eqb (a_base (e_addr se)) b && sb_inside W (a_off (e_addr se)) (Z.of_nat (e_width se)))
                     || (expr_eqb (a_base (e_addr se)) b' && sb_inside W' (a_off (e_addr se)) (Z.of_nat (e_width se)))) log = true ->
  munch (map (fun iv : Z * Z => (bv_unsigned (edenot E b) + fst iv, bv_unsigned (edenot E b) + snd iv)) W
         ++ map (fun iv : Z * Z => (bv_unsigned (edenot E b') + fst iv, bv_unsigned (edenot E b') + snd iv)) W') M (mem_denot E M log).
Proof.
  intros W W' b b' E M log Hf Hb. apply munch_mem_denot; [exact Hf|].
  apply Forall_forall. intros se Hse. rewrite forallb_forall in Hb. specialize (Hb se Hse).
  assert (IA : forall X Y a n, inside X a n \/ inside Y a n -> inside (X ++ Y) a n).
  { induction X as [|[lo hi] X IH]; intros Y a n [K|K]; cbn in *; [destruct K | exact K | destruct K as [K|K]; [left; exact K | right; apply IH; left; exact K]
      | right; apply IH; right; exact K]. }
  apply IA. apply orb_true_iff in Hb. destruct Hb as [Hb|Hb]; apply andb_true_iff in Hb as [Hbe Hi]; apply expr_eqb_true in Hbe;
    [left | right]; unfold estart; rewrite Hbe; apply sb_inside_sound; exact Hi.
Qed.

Lemma other_disj_of_2b : forall E lg (b b' : expr) (lo' hi' A len : Z),
  forallb (fun e' => expr_eqb (a_base (e_addr e')) b
                     || (expr_eqb (a_base (e_addr e')) b' && (lo' <=? a_off (e_addr e')) && (a_off (e_addr e') + Z.of_nat (e_width e') <=? hi'))) lg = true ->
  (A + len <= bv_unsigned (edenot E b') + lo' \/ bv_unsigned (edenot E b') + hi' <= A) ->
  Forall (fun e' => expr_eqb (a_base (e_addr e')) b = false ->
                    estart E (e_addr e') + Z.of_nat (e_width e') <= A \/ A + len <= estart E (e_addr e')) lg.
Proof.
  intros E lg b b' lo' hi' A len Hb HD. apply Forall_forall. intros e' He' Hne. rewrite forallb_forall in Hb. specialize (Hb e' He').
  rewrite Hne in Hb. cbn [orb] in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [Hbe H1].
  apply expr_eqb_true in Hbe. apply Z.leb_le in H1, H2. unfold estart. rewrite Hbe. lia.
Qed.

Lemma munch_eqW : forall W W' (m m' : word -> option byte), munch W m m' -> W = W' -> munch W' m m'.
Proof. intros W W' m m' M E. subst W'. exact M. Qed.

Ltac lgcell2 Hlf HB WS k :=
  eapply (rw_cells_log_nth_sb _ _ _ k);
  [ exact Hlf | reflexivity | vm_cast_no_check (@eq_refl bool true) | rewrite HB; lia
  | apply WS; lia | reflexivity | exact I
  | first [ reflexivity
          | HLib.evs; rewrite ?HLib.w_mul, ?HLib.w_add by lia; reflexivity
          | HLib.evs; match goal with HRx : ?R = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite HRx; reflexivity end ] ].

Ltac lgcell3 Hlf HB b' lo' hi' WS k :=
  eapply (rw_cells_log_nth_2b _ _ _ k _ b' _ _ _ lo' hi');
  [ exact Hlf | reflexivity | vm_compute; reflexivity | rewrite HB; lia | HLib.evs; rewrite ?HLib.u64_of_Z by lia; lia
  | apply WS; lia | reflexivity | exact I
  | first [ reflexivity
          | HLib.evs; rewrite ?HLib.w_mul, ?HLib.w_add by lia; reflexivity
          | HLib.evs; match goal with HRx : ?R = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite HRx; reflexivity end ] ].

Lemma outside_app : forall W W' x, outside (W ++ W') x -> outside W x /\ outside W' x.
Proof.
  induction W as [|[lo hi] W IH]; cbn [app outside]; intros W' x Hx; [split; [exact I | exact Hx]|].
  destruct Hx as [N Hx]. destruct (IH W' x Hx) as [A B]. split; [split; [exact N | exact A] | exact B].
Qed.

Lemma munch_app : forall W W' (m1 m2 m3 : mem), munch W m1 m2 -> munch W' m2 m3 -> munch (W ++ W') m1 m3.
Proof.
  intros W W' m1 m2 m3 H1 H2 x Hx. destruct (outside_app W W' _ Hx) as [A B]. rewrite (H2 x B). exact (H1 x A).
Qed.
