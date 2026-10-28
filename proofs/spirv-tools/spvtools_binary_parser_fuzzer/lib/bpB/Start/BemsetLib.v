(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStepTac BHoare BStoreOk BMemSplit BMmapSim BRefMemcpyLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition ms_inb (i : Z) (iv : Z * Z) : bool := (fst iv <=? i) && (i <? fst iv + snd iv).
Definition ms_cov (L : list (Z * Z)) (i : Z) : bool := existsb (ms_inb i) L.

Lemma ms_inb_true : forall i o m, ms_inb i (o, m) = true <-> o <= i < o + m.
Proof.
  intros i o m. unfold ms_inb. cbn [fst snd]. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma ms_cov_cons : forall iv L i, ms_cov (iv :: L) i = ms_inb i iv || ms_cov L i.
Proof. reflexivity. Qed.

Lemma ms_cov_In : forall L i o m, In (o, m) L -> o <= i < o + m -> ms_cov L i = true.
Proof.
  intros L i o m Hin Hi. unfold ms_cov. apply existsb_exists. exists (o, m). split; [exact Hin|].
  apply ms_inb_true. exact Hi.
Qed.

Fixpoint ms_chain (from to : Z) (L : list (Z * Z)) : Prop :=
  match L with
  | [] => to <= from
  | (o, m) :: L' => o <= from /\ ms_chain (o + m) to L'
  end.

Lemma ms_chain_cov : forall L from to i,
  ms_chain from to L -> from <= i < to -> exists o m, In (o, m) L /\ o <= i < o + m.
Proof.
  induction L as [|[o m] L IH]; intros from to i Hc Hi; cbn [ms_chain] in Hc.
  - lia.
  - destruct Hc as [Ho Hc].
    destruct (Z.lt_ge_cases i (o + m)) as [Hlt|Hge].
    + exists o, m. split; [left; reflexivity | lia].
    + destruct (IH (o + m) to i Hc ltac:(lia)) as (o' & m' & Hin & Hi').
      exists o', m'. split; [right; exact Hin | exact Hi'].
Qed.

Lemma ms_cov_by_chain : forall (L L' : list (Z * Z)) n,
  incl L' L -> ms_chain 0 n L' -> forall i, 0 <= i < n -> ms_cov L i = true.
Proof.
  intros L L' n Hincl Hc i Hi.
  destruct (ms_chain_cov L' 0 n i Hc Hi) as (o & m & Hin & Hom).
  apply (ms_cov_In L i o m); [apply Hincl, Hin | exact Hom].
Qed.

Section CFill.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable c : byte.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.

  Definition cfill (L : list (Z * Z)) : word -> option byte :=
    fun x => if (bv_unsigned d <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned d + n)
                && ms_cov L (bv_unsigned x - bv_unsigned d)
             then Some c else mem0 x.

  Lemma cfill_nil : cfill [] = mem0.
  Proof.
    apply functional_extensionality. intro x. unfold cfill. cbn [ms_cov existsb].
    rewrite andb_false_r. reflexivity.
  Qed.

  Lemma cfill_grows : forall L, mem_grows mem0 (cfill L).
  Proof.
    intros L x Hx. unfold cfill. destruct (_ && _); [discriminate | exact Hx].
  Qed.

  Lemma cfill_ext : forall L1 L2,
    (forall i, 0 <= i < n -> ms_cov L1 i = ms_cov L2 i) -> cfill L1 = cfill L2.
  Proof.
    intros L1 L2 H. apply functional_extensionality. intro x. unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|reflexivity].
    destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|reflexivity].
    cbn [andb]. rewrite H by lia. reflexivity.
  Qed.

  Lemma cfill_store : forall L o (m : nat),
    0 <= o -> o + Z.of_nat m <= n ->
    wbytes (cfill L) (at_ d o) (repeat c m) = cfill ((o, Z.of_nat m) :: L).
  Proof.
    intros L o m Ho Hm. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    assert (Ha : bv_unsigned (at_ d o) = bv_unsigned d + o) by (apply at_u; lia).
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o)) as [Hlo|Hge];
      [| destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o + Z.of_nat m)) as [Hin|Hhi]].
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
    - rewrite wbytes_inside by (rewrite repeat_length, Ha; lia).
      rewrite nth_repeat_lt by (rewrite Ha; lia). unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with true
        by (symmetry; apply ms_inb_true; lia).
      destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|lia].
      destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|lia].
      reflexivity.
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
  Qed.

  Lemma cfill_full : forall L,
    (forall i, 0 <= i < n -> ms_cov L i = true) ->
    cfill L = wbytes mem0 d (repeat c (Z.to_nat n)).
  Proof.
    intros L Hcov. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)) as [H1|H1].
    - destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)) as [H2|H2]; cbn [andb].
      + rewrite Hcov by lia. rewrite wbytes_inside by (rewrite repeat_length; lia).
        rewrite nth_repeat_lt by lia. reflexivity.
      + rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
    - cbn [andb]. rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
  Qed.

  Lemma cfill_full_chain : forall L L',
    incl L' L -> ms_chain 0 n L' ->
    cfill L = wbytes mem0 d (repeat c (Z.to_nat n)).
  Proof. intros L L' Hi Hc. apply cfill_full. apply (ms_cov_by_chain L L'); assumption. Qed.

  Lemma cfill_store_ok : forall segs L o (m : nat),
    store_ok segs mem0 d (Z.to_nat n) = true ->
    0 <= o -> o + Z.of_nat m <= n ->
    store_ok segs (cfill L) (at_ d o) m = true.
  Proof.
    intros segs L o m Hok Ho Hm. pose proof (u64_range d).
    apply (store_ok_mono segs m mem0); [apply cfill_grows|].
    apply (store_ok_sub segs mem0 d (at_ d o) (Z.to_nat n) m); try (rewrite ?at_u; lia). exact Hok.
  Qed.
End CFill.

Definition cbyte (cv : word) : byte := Z_to_bv 8 (bv_unsigned cv).

Definition cbz (cv : word) : Z := bv_unsigned cv mod 256.

Definition c32 (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009).

Definition c32h (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009 * 2 ^ 32).

Definition c64 (cv : word) : word := Z_to_bv 64 (cbz cv * 72340172838076673).

Lemma cbz_range : forall cv, 0 <= cbz cv < 256.
Proof. intros cv. unfold cbz. apply Z.mod_pos_bound. lia. Qed.

Lemma cbyte_mod : forall cv, Z_to_bv 8 (bv_unsigned cv mod 256) = cbyte cv.
Proof.
  intros cv. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. apply Z.mod_mod. lia.
Qed.

Lemma cbyte_cbz : forall cv, cbyte cv = Z_to_bv 8 (cbz cv).
Proof. intros cv. unfold cbz. symmetry. apply cbyte_mod. Qed.

Fixpoint ms_repl (k : nat) : Z := match k with O => 0 | S k' => 1 + 256 * ms_repl k' end.

Lemma ms_repl_nonneg : forall k, 0 <= ms_repl k.
Proof. induction k; cbn [ms_repl]; lia. Qed.

Lemma Z_to_le_bytes_ms_repl : forall k z, 0 <= z < 256 ->
  Z_to_le_bytes k (z * ms_repl k) = repeat (Z_to_bv 8 z) k.
Proof.
  induction k as [|k IH]; intros z Hz; [reflexivity|].
  cbn [Z_to_le_bytes ms_repl repeat]. pose proof (ms_repl_nonneg k). f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. apply IH. exact Hz.
Qed.

Lemma u_c32 : forall cv, bv_unsigned (c32 cv) = cbz cv * 16843009.
Proof. intros cv. pose proof (cbz_range cv). unfold c32. apply u_Z2bv; lia. Qed.

Lemma u_c32h : forall cv, bv_unsigned (c32h cv) = cbz cv * 16843009 * 2 ^ 32.
Proof. intros cv. pose proof (cbz_range cv). unfold c32h. apply u_Z2bv; lia. Qed.

Lemma u_c64 : forall cv, bv_unsigned (c64 cv) = cbz cv * 72340172838076673.
Proof. intros cv. pose proof (cbz_range cv). unfold c64. apply u_Z2bv; lia. Qed.

Lemma wleb4_c32 : forall cv, word_to_le_bytes 4 (c32 cv) = repeat (cbyte cv) 4.
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c32, cbyte_cbz.
  change 16843009 with (ms_repl 4). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

Lemma wleb8_c64 : forall cv, word_to_le_bytes 8 (c64 cv) = repeat (cbyte cv) 8.
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c64, cbyte_cbz.
  change 72340172838076673 with (ms_repl 8). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

Lemma u_slli56 : forall cv, bv_unsigned (v_slli cv 56) = cbz cv * 2 ^ 56.
Proof.
  intros cv. unfold v_slli, cbz. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia.
  pose proof (u64_range cv).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 56 * 256).
  rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. lia.
Qed.

Lemma mulhu_c32 : forall cv (m : word), bv_unsigned m = 4311810304 ->
  v_mulhu (v_slli cv 56) m = c32 cv.
Proof.
  intros cv m Hm. unfold v_mulhu, c32. f_equal. rewrite u_slli56, Hm.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (cbz cv * 2 ^ 56 * 4311810304) with ((cbz cv * 16843009) * 2 ^ 64) by lia.
  apply Z.div_mul. lia.
Qed.

Lemma slli32_c32 : forall cv, v_slli (c32 cv) 32 = c32h cv.
Proof.
  intros cv. unfold v_slli, c32h. f_equal. rewrite u_c32, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma srli32_c32h : forall cv, v_srli (c32h cv) 32 = c32 cv.
Proof.
  intros cv. unfold v_srli, c32. f_equal. rewrite u_c32h, Z.shiftr_div_pow2 by lia.
  apply Z.div_mul. lia.
Qed.

Lemma lor_disjoint_shift32 : forall a b, 0 <= a -> 0 <= b < 2 ^ 32 ->
  Z.lor (a * 2 ^ 32) b = a * 2 ^ 32 + b.
Proof.
  intros a b Ha Hb.
  assert (Hl : Z.land (a * 2 ^ 32) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32).
    - rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r a) by lia. reflexivity.
    - rewrite (Z_testbit_high 32 b) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.

Lemma or_c64 : forall cv, v_or (c32h cv) (c32 cv) = c64 cv.
Proof.
  intros cv. pose proof (cbz_range cv). unfold v_or, c64. f_equal. rewrite u_c32h, u_c32.
  rewrite lor_disjoint_shift32 by lia. lia.
Qed.

Lemma mod4_mod_pow2' : forall t k, 2 <= k -> (t mod 2 ^ k) mod 4 = t mod 4.
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2 ^ (k - 2)). change 4 with (2 ^ 2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma negw_and3 : forall x : word,
  v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 ((- bv_unsigned x) mod 4).
Proof.
  intros x. unfold v_andi, v_subw. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 32) with (2 ^ 31).
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (2 ^ 2) with 4.
  rewrite mod4_mod_pow2' by lia.
  rewrite <- Zminus_mod_idemp_l.
  rewrite mod4_mod_pow2' by lia.
  replace (0 - bv_unsigned x + 2 ^ 31) with ((- bv_unsigned x) + 536870912 * 4) by lia.
  rewrite Z.mod_add by lia.
  rewrite Zminus_mod_idemp_l.
  replace (- bv_unsigned x - 2 ^ 31) with ((- bv_unsigned x) + (- 536870912) * 4) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma neg_mod4_range : forall u, 0 <= (- u) mod 4 <= 3.
Proof. intros u. pose proof (Z.mod_pos_bound (- u) 4). lia. Qed.

Lemma land_trunc4 : forall a, 0 <= a < 2 ^ 64 -> Z.land a (2 ^ 64 - 4) = a - a mod 4.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 4) with (Z.ldiff (Z.ones 64) (Z.ones 2)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  pose proof (Z.div_mod a 4 ltac:(lia)). lia.
Qed.

Lemma andi_m4 : forall m, 0 <= m < 2 ^ 64 ->
  v_andi (Z_to_bv 64 m) (-4) = Z_to_bv 64 (m - m mod 4).
Proof.
  intros m Hm. unfold v_andi. f_equal. rewrite u_Z2bv by lia.
  change (bv_wrap 64 (-4)) with (2 ^ 64 - 4). apply land_trunc4. exact Hm.
Qed.

Lemma land_4_cases : forall a, 0 <= a -> Z.land a 4 = 0 \/ Z.land a 4 = 4.
Proof.
  intros a Ha.
  destruct (Z.testbit a 2) eqn:E; [right|left];
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec;
    change 4 with (2 ^ 2); rewrite Z.pow2_bits_eqb by lia;
    destruct (Z.eqb_spec 2 i) as [<-|Hne]; rewrite ?E, ?Z.bits_0; try reflexivity;
    apply andb_false_r.
Qed.

Lemma andi_4_cases : forall x : word, exists s4, v_andi x 4 = Z_to_bv 64 s4 /\ (s4 = 0 \/ s4 = 4).
Proof.
  intros x. exists (Z.land (bv_unsigned x) 4). split.
  - unfold v_andi. f_equal.
  - apply land_4_cases. apply u64_range.
Qed.

Lemma ms_v_add_Z : forall (x : word) z, 0 <= z < 2 ^ 64 ->
  v_add x (Z_to_bv 64 z) = at_ x z.
Proof. intros x z Hz. unfold v_add, at_. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_add_at_Z : forall (x : word) o z, 0 <= z < 2 ^ 64 ->
  v_add (at_ x o) (Z_to_bv 64 z) = at_ x (o + z).
Proof. intros x o z Hz. rewrite ms_v_add_Z by lia. apply at_at. Qed.

Lemma ms_v_sub_ZZ : forall a b, 0 <= b <= a -> a < 2 ^ 64 ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H1 H2. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_addi_Z : forall a i, 0 <= a < 2 ^ 64 ->
  v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i Ha. unfold v_addi. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma ms_step_mulhu_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MULHU rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_mulhu (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mulhu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma ms_step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Section Stores.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable cv : word.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.
  Hypothesis Hok : store_ok segs mem0 d (Z.to_nat n) = true.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).

  Lemma cf_sb : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = cv ->
    0 <= o -> o + 1 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 1) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o Hf He Hdc Hrs1 Ho Hrs2 H0 H1.
    replace ((o, 1) :: L) with ((o, Z.of_nat 1) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 1) by lia.
    eapply step_sb_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 | reflexivity |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  Lemma cf_sw : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o v,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 4 v = repeat (cbyte cv) 4 ->
    0 <= o -> o + 4 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 4) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 4) :: L) with ((o, Z.of_nat 4) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 4) by lia.
    rewrite <- Hv.
    eapply step_sw_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  Lemma cf_sd : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o v,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 8 v = repeat (cbyte cv) 8 ->
    0 <= o -> o + 8 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 8) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 8) :: L) with ((o, Z.of_nat 8) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 8) by lia.
    rewrite <- Hv.
    eapply step_sd_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.
End Stores.

Definition ms_clob : list reg := [11; 12; 13; 14; 15; 16]%bv.
Definition ms_agree (regs regs' : bvmap 5 word) : Prop :=
  regs_agree (fun r => In r ms_clob) regs regs'.

Lemma ms_agree_refl : forall regs, ms_agree regs regs.
Proof. intros regs. apply regs_agree_refl. Qed.

Lemma ms_agree_trans : forall r1 r2 r3, ms_agree r1 r2 -> ms_agree r2 r3 -> ms_agree r1 r3.
Proof. intros r1 r2 r3. apply regs_agree_trans. Qed.

Lemma ms_agree_upd : forall regs regs' (rd : reg) v,
  ms_agree regs regs' -> In rd ms_clob -> ms_agree regs (regupd regs' rd v).
Proof. intros regs regs' rd v H Hin. apply regs_agree_upd; assumption. Qed.

Ltac in_clob := cbn [ms_clob In]; repeat first [ left; reflexivity | right ].
Ltac solve_ms_agree :=
  repeat (apply ms_agree_upd; [| in_clob]); first [apply ms_agree_refl | assumption].
