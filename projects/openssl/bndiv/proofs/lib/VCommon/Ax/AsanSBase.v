(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
Definition nul_free (bs : list byte) : Prop := forall x, In x bs -> bv_unsigned x <> 0%Z.

(* [comment removed for export] *)
Definition cstr (segs : list Segment) (mem : word -> option byte) (s : word) (bs : list byte) : Prop :=
  rdn segs mem s (S (length bs)) = Some (bs ++ [Z_to_bv 8 0]) /\ nul_free bs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_nth : forall segs mem n (a : word) l j,
  rdn segs mem a n = Some l -> (j < n)%nat ->
  rdn segs mem (a + Z_to_bv 64 (Z.of_nat j)) 1 = Some [nth j l (Z_to_bv 8 0)].
Proof.
  intros segs mem n. induction n as [|n IH]; intros a l j H Hj; [lia|].
  cbn [rdn] in H.
  destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [x|] eqn:Ex; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest|] eqn:Er; [|discriminate].
  injection H as <-.
  destruct j as [|j].
  - cbn [nth]. change (Z.of_nat 0) with 0%Z.
    replace (a + Z_to_bv 64 0) with a by (apply bv_eq; rewrite bv_add_unsigned, Z_to_bv_unsigned;
      change (bv_wrap 64 0) with 0%Z; rewrite Z.add_0_r; symmetry; apply bv_wrap_bv_unsigned).
    cbn [rdn]. rewrite Ex. reflexivity.
  - cbn [nth]. specialize (IH (a + 1) rest j Er ltac:(lia)).
    replace (a + Z_to_bv 64 (Z.of_nat (S j))) with ((a + 1) + Z_to_bv 64 (Z.of_nat j)); [exact IH|].
    apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
    rewrite ?bv_wrap_add_idemp_l, ?bv_wrap_add_idemp_r.
    change (bv_unsigned (1 : word)) with 1%Z. apply (f_equal (bv_wrap 64)). lia.
Qed.

Lemma nth_app_l : forall (l : list byte) x j, (j < length l)%nat -> nth j (l ++ [x]) (Z_to_bv 8 0) = nth j l (Z_to_bv 8 0).
Proof. intros l x j Hj. apply app_nth1. exact Hj. Qed.

Lemma nth_app_last : forall (l : list byte) x, nth (length l) (l ++ [x]) (Z_to_bv 8 0) = x.
Proof. intros l x. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma nul_free_nth : forall bs j, nul_free bs -> (j < length bs)%nat -> bv_unsigned (nth j bs (Z_to_bv 8 0)) <> 0%Z.
Proof. intros bs j H Hj. apply H. apply nth_In. exact Hj. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lbu_val : forall x : byte, load_word SZ1 false [x] = Z_to_bv 64 (bv_unsigned x).
Proof.
  intros x. apply bv_eq. cbn [load_word]. unfold zext.
  rewrite bv_zero_extend_unsigned by lia. rewrite bv_extract_unsigned, Z.shiftr_0_r.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256%Z in R.
  rewrite (bv_wrap_small 64 (bv_unsigned x)) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  rewrite (bv_wrap_small 8 (bv_unsigned x)) by (change (bv_modulus 8) with 256%Z; lia).
  reflexivity.
Qed.

Lemma byte_range : forall x : byte, (0 <= bv_unsigned x < 256)%Z.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256%Z in R. exact R. Qed.

Lemma u_add_small : forall (s : word) (j : Z), (0 <= j)%Z -> (bv_unsigned s + j < 2 ^ 64)%Z ->
  bv_unsigned (s + Z_to_bv 64 j) = (bv_unsigned s + j)%Z.
Proof.
  intros s j Hj H. rewrite bv_add_unsigned, Z_to_bv_unsigned, bv_wrap_add_idemp_r.
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. pose proof (bv_unsigned_in_range 64 s). lia.
Qed.

(* [comment removed for export] *)
Lemma ret_even : forall x : word, (bv_unsigned x mod 2 = 0)%Z ->
  bv_and (x + sext 64 (@BV 12 0 I)) (bv_not w1) = x.
Proof.
  intros x Hev. rewrite sext64_Z_to_bv. change (bv_signed (@BV 12 0 I)) with 0%Z.
  replace (x + Z_to_bv 64 0) with x
    by (apply bv_eq; rewrite bv_add_unsigned, Z_to_bv_unsigned; change (bv_wrap 64 0) with 0%Z;
        rewrite Z.add_0_r; symmetry; apply bv_wrap_bv_unsigned).
  apply bv_eq. rewrite bv_and_unsigned, bv_not_unsigned. unfold w1.
  rewrite bvu_z by lia. change (bv_wrap 64 (Z.lnot 1)) with (Z.ones 64 - 1)%Z.
  pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64)%Z in R.
  set (v := bv_unsigned x) in *.
  change (Z.ones 64 - 1)%Z with (Z.lxor (Z.ones 64) 1).
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec.
  destruct (Z.eq_dec n 0) as [->|Hn0].
  - assert (Hq : (v = 2 * (v / 2))%Z) by (pose proof (Z.div_mod v 2 ltac:(lia)); lia).
    rewrite Hq, Z.testbit_even_0. reflexivity.
  - rewrite (Z.testbit_ones 64 n) by lia. rewrite Z.bits_above_log2 with (a := 1%Z) by (cbn; lia).
    destruct (Z_lt_ge_dec n 64) as [Hlt|Hge].
    + replace ((0 <=? n) && (n <? 64))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt || apply Z.leb_le; lia).
      cbn [xorb]. rewrite andb_true_r. reflexivity.
    + replace ((0 <=? n) && (n <? 64))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
      cbn [xorb]. rewrite andb_false_r. symmetry.
      destruct (Z.eq_dec v 0) as [E0|E0]; [rewrite E0; apply Z.testbit_0_l|].
      apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
      pose proof (Z.pow_le_mono_r 2 64 n ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma branch_ne_byte : forall x : byte,
  branch_taken BC_NE (Z_to_bv 64 (bv_unsigned x)) w0 = negb (bv_unsigned x =? 0)%Z.
Proof.
  intros x. pose proof (byte_range x). unfold w0. apply branch_ne_z; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Lemma wacc_Auipc : forall ms w isz rd (imm : bv 20),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (ms_pc_val ms + sext 64 (bv_concat 32 imm (Z_to_bv 12 0)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)) []).
Proof.
  intros ms w isz rd imm Hfetch Hecall Hdecode.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma wacc_Mul : forall ms w isz op rd rs1 rs2,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (mul_div op (rg ms rs1) (rg ms rs2))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)) []).
Proof.
  intros ms w isz op rd rs1 rs2 Hfetch Hecall Hdecode.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bat (segs : list Segment) (mem : word -> option byte) (a : word) : option byte :=
  match mem a with Some b => Some b | None => seg_rom segs a end.

Lemma rdn_1 : forall segs mem a x, bat segs mem a = Some x -> rdn segs mem a 1 = Some [x].
Proof. intros segs mem a x H. cbn [rdn]. unfold bat in H. rewrite H. reflexivity. Qed.

Lemma bat_of_rdn : forall segs mem n (a : word) l j,
  rdn segs mem a n = Some l -> (j < n)%nat ->
  bat segs mem (a + Z_to_bv 64 (Z.of_nat j)) = Some (nth j l (Z_to_bv 8 0)).
Proof.
  intros segs mem n a l j H Hj. pose proof (rdn_nth segs mem n a l j H Hj) as H1.
  cbn [rdn] in H1. unfold bat.
  destruct (match mem (a + Z_to_bv 64 (Z.of_nat j)) with Some b => Some b | None => seg_rom segs _ end); [|discriminate].
  injection H1 as <-. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_of_bats : forall segs mem n (a : word),
  (forall j, (j < n)%nat -> exists x, bat segs mem (a + Z_to_bv 64 (Z.of_nat j)) = Some x) ->
  exists l, rdn segs mem a n = Some l /\ length l = n.
Proof.
  intros segs mem n. induction n as [|n IH]; intros a H; [exists []; split; reflexivity|].
  destruct (H 0%nat ltac:(lia)) as [x Hx].
  replace (a + Z_to_bv 64 (Z.of_nat 0)) with a in Hx
    by (apply bv_eq; rewrite bv_add_unsigned, Z_to_bv_unsigned; change (bv_wrap 64 (Z.of_nat 0)) with 0%Z;
        rewrite Z.add_0_r; symmetry; apply bv_wrap_bv_unsigned).
  destruct (IH (a + 1)) as [l [Hl Hlen]].
  { intros j Hj. destruct (H (S j) ltac:(lia)) as [y Hy]. exists y.
    replace ((a + 1) + Z_to_bv 64 (Z.of_nat j)) with (a + Z_to_bv 64 (Z.of_nat (S j))); [exact Hy|].
    apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
    rewrite ?bv_wrap_add_idemp_l, ?bv_wrap_add_idemp_r.
    change (bv_unsigned (1 : word)) with 1%Z. apply (f_equal (bv_wrap 64)). lia. }
  exists (x :: l). split; [|cbn [length]; rewrite Hlen; reflexivity].
  cbn [rdn]. unfold bat in Hx. rewrite Hx, Hl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w_add_assoc : forall (a : word) (i j : Z), (a + Z_to_bv 64 i) + Z_to_bv 64 j = a + Z_to_bv 64 (i + j).
Proof.
  intros a i j. rewrite <- (bv_add_assoc a (Z_to_bv 64 i) (Z_to_bv 64 j)). rewrite zw_add. reflexivity.
Qed.

Lemma w_add_sext_z : forall (a : word) (i : Z) {n} (imm : bv n), (a + Z_to_bv 64 i) + sext 64 imm = a + Z_to_bv 64 (i + bv_signed imm).
Proof. intros a i n imm. rewrite sext64_Z_to_bv. apply w_add_assoc. Qed.

Lemma w_add_0 : forall (a : word), a + Z_to_bv 64 0 = a.
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0%Z.
  rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma add_sext0 : forall x : word, x + sext 64 (@BV 12 0 I) = x.
Proof.
  intros x. rewrite sext64_Z_to_bv. change (bv_signed (@BV 12 0 I)) with 0%Z.
  apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0%Z.
  rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

Lemma zw_succ : forall k : nat, Z_to_bv 64 (Z.of_nat k) + sext 64 (@BV 12 1 I) = Z_to_bv 64 (Z.of_nat (S k)).
Proof.
  intros k. rewrite zw_add_sext. change (bv_signed (@BV 12 1 I)) with 1%Z. f_equal. lia.
Qed.

Lemma zw_pred : forall k : nat, Z_to_bv 64 (Z.of_nat (S k)) + sext 64 (@BV 12 4095 I) = Z_to_bv 64 (Z.of_nat k).
Proof.
  intros k. rewrite zw_add_sext. change (bv_signed (@BV 12 4095 I)) with (-1)%Z. f_equal. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac nrm := rewrite ?resv_setx, ?mem_setx.
Ltac wsx ACC F D := wst ACC F D; nrm.

Lemma FR_setxn : forall rs S S1 rd v p r m,
  FR rs S S1 -> (rd = 0 \/ In rd rs) -> r = ms_resv S1 -> m = ms_mem S1 -> FR rs S (setx S1 rd v p r m).
Proof. exact FR_setx. Qed.

(* [comment removed for export] *)
Ltac memb := repeat (first [ left; reflexivity | right ]).

(* [comment removed for export] *)
Ltac frs HF :=
  repeat first [ exact HF
               | apply FR_setxn; [ | first [ left; reflexivity | right; memb ] | reflexivity | reflexivity ] ].

Lemma w0_add_sext : forall {n} (imm : bv n), w0 + sext 64 imm = Z_to_bv 64 (bv_signed imm).
Proof. intros n imm. unfold w0. rewrite zw_add_sext. f_equal. Qed.

Lemma mul_w0 : forall x : word, mul_div M_MUL w0 x = w0.
Proof.
  intros x. apply bv_eq. cbn [mul_div]. rewrite bv_mul_unsigned. unfold w0.
  rewrite bvu_z by lia. rewrite Z.mul_0_l. reflexivity.
Qed.

Lemma and_w0 : forall {n} (imm : bv n), alu64 ALU_AND w0 (sext 64 imm) = w0.
Proof.
  intros n imm. apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned. unfold w0.
  rewrite bvu_z by lia. rewrite Z.land_0_l. reflexivity.
Qed.

Lemma and7 : forall x : word, alu64 ALU_AND x (sext 64 (@BV 12 7 I)) = Z_to_bv 64 (bv_unsigned x mod 8).
Proof.
  intros x. apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned. rewrite sext64_Z_to_bv.
  change (bv_signed (@BV 12 7 I)) with 7%Z. rewrite (bvu_z 7) by lia.
  pose proof (u64_range x) as R.
  rewrite bvu_z by (pose proof (Z.mod_pos_bound (bv_unsigned x) 8 ltac:(lia)); lia).
  change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma sltu0 : forall n : Z, (0 < n < 2 ^ 64)%Z -> alu64 ALU_SLTU w0 (Z_to_bv 64 n) = Z_to_bv 64 1.
Proof. intros n Hn. unfold w0. rewrite alu_sltu_z by lia. rewrite (proj2 (Z.ltb_lt 0 n)) by lia. reflexivity. Qed.

Lemma br_eq0 : forall z : Z, (0 <= z < 2 ^ 64)%Z -> branch_taken BC_EQ (Z_to_bv 64 z) w0 = (z =? 0)%Z.
Proof. intros z Hz. unfold w0. apply branch_eq_z; lia. Qed.
Lemma br_ne0 : forall z : Z, (0 <= z < 2 ^ 64)%Z -> branch_taken BC_NE (Z_to_bv 64 z) w0 = negb (z =? 0)%Z.
Proof. intros z Hz. unfold w0. apply branch_ne_z; lia. Qed.

Lemma w_add_sext : forall (a : word) {n} (imm : bv n), a + sext 64 imm = a + Z_to_bv 64 (bv_signed imm).
Proof. intros a n imm. rewrite sext64_Z_to_bv. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint wlookup (o : Z) (ws : list (Z * Z)) : option Z :=
  match ws with
  | [] => None
  | (o', w) :: r => if Z.eqb o o' then Some w else wlookup o r
  end.

Lemma wlookup_In : forall o ws w, wlookup o ws = Some w -> In (o, w) ws.
Proof.
  intros o ws. induction ws as [|[o' w'] r IH]; intros w H; cbn in H; [discriminate|].
  destruct (Z.eqb_spec o o') as [->|N]; [injection H as <-; left; reflexivity | right; exact (IH w H)].
Qed.

Lemma words_get_l : forall segs base ws (o w : Z),
  words_ok segs base ws = true -> wlookup o ws = Some w -> ((0 <=? w) && (w <? 2 ^ 32))%Z = true ->
  fetch_word segs (Z_to_bv 64 (base + o)) = Some (Z_to_bv 32 w).
Proof.
  intros segs base ws o w H1 H2 H3. apply andb_prop in H3 as [H3 H4]. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
  apply (words_get segs base ws); [exact H1 | apply wlookup_In; exact H2 | lia].
Qed.

(* [comment removed for export] *)
Definition cell8 (segs : list Segment) (mem : word -> option byte) (a v : Z) : Prop :=
  exists l, rdn segs mem (Z_to_bv 64 a) 8 = Some l /\ load_word SZ8 true l = Z_to_bv 64 v.
