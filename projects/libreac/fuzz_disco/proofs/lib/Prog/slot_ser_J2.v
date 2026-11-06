From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib printf_facts_c slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import json_scalar_c jtok_is_c tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_tokb slot_ser_Pq slot_ser_ws slot_ser_J0 slot_ser_J1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser.
Import ListNotations.
Open Scope Z_scope.

Lemma le_inv : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|x bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 x) as Hx. change (bv_modulus 8) with 256 in Hx.
  pose proof (bytes_le_to_Z_nonneg bs) as Hs.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    replace (bv_unsigned x + 256 * bytes_le_to_Z bs) with (bv_unsigned x + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned x + 256 * bytes_le_to_Z bs) with (bv_unsigned x + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. exact IH.
Qed.

Lemma le8_inv : forall bs, length bs = 8%nat -> le8 (bv_extract 0 64 (le_bytes_to_word bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes.
  rewrite bv_extract_unsigned, Z.shiftr_0_r. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite L in Hb.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hb.
  assert (E : bv_wrap 64 (bytes_le_to_Z bs) = bytes_le_to_Z bs)
    by (apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite !E. rewrite <- L at 1. apply le_inv.
Qed.

Lemma le8_inv2 : forall bs, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite L in Hb.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hb.
  rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). rewrite <- L at 1. apply le_inv.
Qed.

Lemma jscalar_kind : forall B i j k s l, jscalar B i = Some (j, k, s, l) -> 1 <= k <= 3.
Proof.
  intros B i j k s l H. unfold jscalar in H.
  destruct (jlen B <=? i) eqn:E1; cbv beta iota in H; [discriminate|].
  destruct (jbyte B i =? 34) eqn:E2; cbv beta iota in H.
  - apply jstr_bnd in H. destruct H as (jc & _ & Heq). injection Heq; intros; subst. lia.
  - destruct (jlit B i jlit_words) as [t|] eqn:E3; cbv beta iota in H.
    + injection H; intros; subst. apply jlit_bnd in E3. destruct E3 as (n & _ & Heq).
      injection Heq; intros; subst. lia.
    + apply jnum_bnd in H. destruct H as (j3 & _ & Heq). injection Heq; intros; subst. lia.
Qed.

Lemma slot_of_lt : forall B t k, slot_of B t = Some k -> (k < 6)%nat.
Proof.
  intros B t k H. unfold slot_of, keys in H. cbn [slot_from] in H. revert H.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    intros H; try discriminate H; injection H; intros; subst; lia.
Qed.

Lemma set_nth_length : forall k o t, length (set_nth k o t) = length o.
Proof.
  intros k o. revert k. induction o as [|x o IH]; intros [|k] t; cbn [set_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma obj_split : forall b vpad o k, (k < length o)%nat ->
  obj_bytes b vpad o =
  obj_bytes b vpad (firstn k o) ++ slot24 b vpad (nth k o tok_none) ++ obj_bytes b vpad (skipn (S k) o).
Proof.
  intros b vpad o. unfold obj_bytes. induction o as [|x o IH]; intros k Hk; [cbn [length] in Hk; lia|].
  destruct k as [|k]; cbn [firstn skipn nth map concat app]; [reflexivity|].
  rewrite (IH k) by (cbn [length] in Hk; lia). rewrite <- !app_assoc. reflexivity.
Qed.

Lemma obj_set : forall b vpad o k t, (k < length o)%nat ->
  obj_bytes b vpad (set_nth k o t) =
  obj_bytes b vpad (firstn k o) ++ slot24 b vpad t ++ obj_bytes b vpad (skipn (S k) o).
Proof.
  intros b vpad o. unfold obj_bytes. induction o as [|x o IH]; intros k t Hk; [cbn [length] in Hk; lia|].
  destruct k as [|k]; cbn [set_nth firstn skipn map concat app]; [reflexivity|].
  rewrite (IH k t) by (cbn [length] in Hk; lia). rewrite <- !app_assoc. reflexivity.
Qed.

Lemma obj_pre_len : forall b vpad o k, length vpad = 4%nat -> (k <= length o)%nat ->
  length (obj_bytes b vpad (firstn k o)) = (24 * k)%nat.
Proof.
  intros b vpad o k Lv Hk. unfold obj_bytes. rewrite (concat_len (slot24 b vpad) 24 (firstn k o)).
  - rewrite length_firstn. lia.
  - apply Forall_forall. intros x _. apply slot24_len. exact Lv.
Qed.

Lemma slot24_zero : forall b vpad t, tv_kind t = 0 -> slot24 b vpad t = repeat (Z_to_bv 8 0) 24.
Proof. intros b vpad t H. unfold slot24. rewrite H. reflexivity. Qed.

Lemma slot24_val : forall b vpad k s l, k <> 0 ->
  slot24 b vpad (k, s, l) = le8 (Z_to_bv 64 (b + s)) ++ le8 (Z_to_bv 64 l) ++ le4 (Z_to_bv 64 k) ++ vpad.
Proof. intros b vpad k s l H. unfold slot24, tv_kind. cbn [fst snd]. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma cb_app2 : forall m A n1 n2 b1 b2, length b1 = n1 ->
  rw_cells rsegs m A [CB (n1 + n2) (b1 ++ b2)] ->
  rw_cells rsegs m A [CB n1 b1] /\ rw_cells rsegs m (A + Z.of_nat n1) [CB n2 b2].
Proof.
  intros m A n1 n2 b1 b2 L H.
  destruct (ser_split m A (A + Z.of_nat n1) n1 n2 (n1 + n2) (b1 ++ b2) eq_refl eq_refl H) as [H1 H2].
  subst n1. rewrite firstn_app, firstn_all, Nat.sub_diag in H1. cbn [firstn] in H1. rewrite app_nil_r in H1.
  rewrite skipn_app, skipn_all, Nat.sub_diag in H2. cbn [skipn app] in H2. split; assumption.
Qed.

Lemma cb_join : forall m A n1 n2 b1 b2,
  rw_cells rsegs m A [CB n1 b1] -> rw_cells rsegs m (A + Z.of_nat n1) [CB n2 b2] ->
  rw_cells rsegs m A [CB (n1 + n2) (b1 ++ b2)].
Proof. intros m A n1 n2 b1 b2 H1 H2. exact (ser_join m A (A + Z.of_nat n1) n1 n2 (n1 + n2) b1 b2 eq_refl eq_refl H1 H2). Qed.

Lemma rw_addr : forall m A A' cs, rw_cells rsegs m A cs -> A = A' -> rw_cells rsegs m A' cs.
Proof. intros m A A' cs H E. subst A'. exact H. Qed.

Lemma ba_addr : forall m A A' bs, bytes_at rsegs m A bs -> A = A' -> bytes_at rsegs m A' bs.
Proof. intros m A A' bs H E. subst A'. exact H. Qed.

Lemma rd_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  cbn [Z.of_nat skipn] in R. rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

Lemma zslot : forall m SA, rw_cells rsegs m SA [CB 24 (repeat (Z_to_bv 8 0) 24)] ->
  rw_cells rsegs m SA [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m SA [[_ B] W]. split; [split|].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes] in B |- *.
    replace (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ [])
      with (repeat (Z_to_bv 8 0) 24 ++ []) by (vm_compute; reflexivity).
    exact B.
  - exact W.
Qed.

Lemma zslot_rd : forall m SA, rw_cells rsegs m SA [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  ov_read_bytes rsegs m (wa (SA + 16)) 4 = Some (le4 (Z_to_bv 64 0)).
Proof.
  intros m SA [[_ B] _].
  rewrite (bytes_at_read rsegs m SA _ 16 4 B)
    by first [lia | (cbn [cells_bytes cbytes]; rewrite !length_app, !length_le8; cbn [length]; lia)].
  vm_compute. reflexivity.
Qed.

Lemma tok_cells : forall m V w0 w1 w2, bytes_at rsegs m V (le8 w0 ++ le8 w1 ++ le4 w2) -> wr_at rsegs m V 20 ->
  rw_cells rsegs m V [C8 w0; C8 w1; C4 w2].
Proof.
  intros m V w0 w1 w2 B W. split; [split|].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - exact W.
Qed.

Lemma cells_cb3 : forall m V w0 w1 w2, rw_cells rsegs m V [C8 w0; C8 w1; C4 w2] ->
  rw_cells rsegs m V [CB 20 (le8 w0 ++ le8 w1 ++ le4 w2)].
Proof.
  intros m V w0 w1 w2 [[_ B] W]. apply ser_cb. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  split; [rewrite !length_app, !length_le8, length_le4; reflexivity|]. split; [exact B|exact W].
Qed.

Lemma cells_c83 : forall m V w0 w1 w2, rw_cells rsegs m V [C8 w0; C8 w1; C8 w2] ->
  rw_cells rsegs m V [CB 24 (le8 w0 ++ le8 w1 ++ le8 w2)].
Proof.
  intros m V w0 w1 w2 [[_ B] W]. apply ser_cb. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  split; [rewrite !length_app, !length_le8; reflexivity|]. split; [exact B|exact W].
Qed.

Lemma ws_past : forall B i, 0 <= i -> jlen B <= i -> json_ws B i = i.
Proof.
  intros B i Hi H. rewrite ws_unfold by exact Hi. replace (i <? jlen B) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Ltac if_vm :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let c' := eval vm_compute in c in
      replace c with c' by (vm_compute; reflexivity); cbv iota
  end.

Lemma ws12w : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> a0 = Z_to_bv 64 i ->
  0 <= i < jlen B -> 0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (json_ws B (i + 1))) a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13a90) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a64) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 E3 E4 Ea Hi Hb HbB FB BB.
  subst s3 s4 a0.
  step. step. rewrite ltu_lit by lia.
  destruct (Z.ltb_spec (i + 1) (jlen B)) as [Lt|Ge]; cbn [negb]; cbv iota.
  - eapply ws_L12; first [reflexivity | (f_equal; lia) | lia | assumption].
  - apply evt_done. exists (Z_to_bv 64 i). rewrite (ws_past B (i + 1)) by lia. reflexivity.
Qed.

Lemma ws13w : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> a0 = Z_to_bv 64 i ->
  0 <= i <= jlen B -> 0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 (Z_to_bv 64 (json_ws B i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13ad4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13aa8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 E3 E4 Ea Hi Hb HbB FB BB.
  subst s3 s4 a0.
  step. step. rewrite ltu_lit by lia.
  destruct (Z.ltb_spec i (jlen B)) as [Lt|Ge]; cbn [negb]; cbv iota.
  - eapply ws_L13; first [reflexivity | (f_equal; lia) | lia | assumption].
  - apply evt_done. exists (Z_to_bv 64 i). rewrite (ws_past B i) by lia. reflexivity.
Qed.

Lemma ws14w : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s6 = Z_to_bv 64 i ->
  0 <= i < jlen B -> 0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (json_ws B (i + 1))) a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13bdc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13bb0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 E3 E4 E6 Hi Hb HbB FB BB.
  subst s3 s4 s6.
  step. step. rewrite ltu_lit by lia.
  destruct (Z.ltb_spec (i + 1) (jlen B)) as [Lt|Ge]; cbn [negb]; cbv iota.
  - eapply ws_L14; first [reflexivity | (f_equal; lia) | lia | assumption].
  - apply evt_done. exists a0. rewrite (ws_past B (i + 1)) by lia. reflexivity.
Qed.

Lemma slot_put : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA V : Z) (w0 w1 : word) (bs2 : list byte),
  a1 = Z_to_bv 64 SA -> s8 = Z_to_bv 64 (V + 16) -> length bs2 = 8%nat ->
  0 <= SA -> SA + 24 < 2 ^ 63 -> 0 <= V -> V + 24 < 2 ^ 63 ->
  rw_cells rsegs m SA [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  ov_read_bytes rsegs m (wa V) 8 = Some (le8 w0) ->
  ov_read_bytes rsegs m (wa (V + 8)) 8 = Some (le8 w1) ->
  ov_read_bytes rsegs m (wa (V + 16)) 8 = Some bs2 ->
  mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (a0' a2' a3' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13b9c) fc None m' (seg_rom rsegs) /\
       munch [(SA, SA + 24)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' SA [CB 24 (le8 w0 ++ le8 w1 ++ bs2)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b7c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SA V w0 w1
    bs2 Ea1 Es8 L2 H1 H2 H3 H4 C R0 R1 R2 MI.
  subst a1 s8.
  pose proof (zslot_rd m SA C) as R16.
  pose proof (munch_refl [(SA, SA + 24)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  step. step. if_vm.
  step. step. step.
  step. step. step.
  apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  apply cells_c83 in C.
  first [rewrite (le8_inv bs2 L2) in C | rewrite (le8_inv2 bs2 L2) in C]. exact C.
Qed.

Ltac js_side := unfold JSON_SCALAR_K in *; first [ reflexivity | assumption | (f_equal; lia) | lia ].

Lemma key_head : json_scalar_contract -> jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo X b cur i j ks kl r : Z) (B : list Z) (o o' : jobj) (f : nat) (vpk vpad jv : list byte),
  sp = Z_to_bv 64 X -> s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b ->
  s4 = Z_to_bv 64 (jlen B) -> s5 = Z_to_bv 64 cur -> s7 = Z_to_bv 64 (- jlen B) -> s8 = Z_to_bv 64 (X + 2336) ->
  s9 = Z_to_bv 64 (cur + 48) -> s10 = Z_to_bv 64 (cur + 24) -> s11 = Z_to_bv 64 (cur + 72) -> a0 = Z_to_bv 64 j ->
  0 <= i -> jscalar B i = Some (j, 1, ks, kl) -> json_pairs B i o (S f) = Some (r, o') ->
  length o = 6%nat -> Forall (tok_inb B) o -> length vpk = 4%nat -> length vpad = 4%nat -> length jv = 20%nat ->
  0 < b -> b + jlen B + 1 <= lo -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 992) [CB 20 (le8 (Z_to_bv 64 (b + ks)) ++ le8 (Z_to_bv 64 kl) ++ le4 (Z_to_bv 64 1))] ->
  rw_cells rsegs m (X + 1012) [CB 4 vpk] ->
  rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 (cur + 96))] -> rw_cells rsegs m (X + 192) [C8 (Z_to_bv 64 (cur + 120))] ->
  rw_cells rsegs m cur [CB 144 (obj_bytes b vpad o)] ->
  rw_cells rsegs m (X + 2320) [CB 20 jv] -> rw_cells rsegs m (X + 2340) [CB 4 vpad] ->
  X + 1024 <= cur -> cur + 144 <= X + 2320 ->
  bytes_at rsegs m JSON_SCALAR_L js_table -> mem_inv rsegs m -> stk rsegs m lo X -> lo + 112 <= X -> 0x51d38 <= lo ->
  X + 2592 < 2 ^ 63 ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (i3 : Z) (o1 : jobj) (jv' : list byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 (Z_to_bv 64 i3) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x13b9c) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (cur, cur + 144); (X + 2320, X + 2340)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       stk rsegs m' lo X /\
       rw_cells rsegs m' cur [CB 144 (obj_bytes b vpad o1)] /\ rw_cells rsegs m' (X + 2320) [CB 20 jv'] /\
       0 <= i3 <= jlen B /\ length o1 = 6%nat /\ Forall (tok_inb B) o1 /\
       ((at_byte B i3 44 = true /\ json_pairs B (json_ws B (i3 + 1)) o1 f = Some (r, o')) \/
        (at_byte B i3 44 = false /\ at_byte B i3 125 = true /\ r = i3 + 1 /\ o' = o1)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a1c) fc None m (seg_rom rsegs)).
Proof.
  intros JS JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo X b cur i j ks kl r B o o' f vpk vpad jv
    Esp Es0 Es2 Es3 Es4 Es5 Es7 Es8 Es9 Es10 Es11 Ea0 Hi JSk JP Lo Io Lk Lv Ljv Hb Hbl FB BB CK CV C216 C192 CO CJ CP
    Hc1 Hc2 JTB MI ST HK HI HX.
  assert (HJL : JSON_SCALAR_L = 0x1fe28) by reflexivity.
  assert (LJS : Z.of_nat (length js_table) = 24) by reflexivity.
  assert (LBB : Z.of_nat (length (pf_bytes (B ++ [0]))) = jlen B + 1)
    by (rewrite length_pf_bytes, length_app; unfold jlen; cbn [length]; lia).
  pose proof (jscalar_bnd B i j 1 ks kl JSk Hi) as (Hks & Hkl & Hkb & Hj0).
  cbn [json_pairs] in JP. rewrite JSk in JP. cbv iota zeta in JP. rewrite Z.eqb_refl in JP. cbn [negb] in JP.
  cbv iota in JP.
  set (i1 := json_ws B j) in *.
  destruct (at_byte B i1 58) eqn:A1; cbn [negb] in JP; cbv iota in JP; [|discriminate JP].
  set (i2 := json_ws B (i1 + 1)) in *.
  destruct (jscalar B i2) as [[[[j2 vk] vs] vl]|] eqn:JS2; cbv iota in JP; [|discriminate JP].
  set (i3 := json_ws B j2) in *.
  pose proof (ws_ge B j Hj0) as G1. fold i1 in G1.
  destruct (at_byte_true B i1 58 A1) as [L1 C1].
  pose proof (ws_ge B (i1 + 1) ltac:(lia)) as G2. fold i2 in G2.
  pose proof (ws_le B (i1 + 1) ltac:(lia)) as G2'. fold i2 in G2'.
  pose proof (js_rng B i2 j2 vk vs vl JS2) as [L2 G3].
  pose proof (jscalar_bnd B i2 j2 vk vs vl JS2 ltac:(lia)) as (Hvs & Hvl & Hvb & _).
  pose proof (jscalar_kind B i2 j2 vk vs vl JS2) as Hvk.
  pose proof (ws_ge B j2 ltac:(lia)) as G4. fold i3 in G4.
  pose proof (ws_le B j2 ltac:(lia)) as G4'. fold i3 in G4'.
  pose proof CJ as CJw. apply ser_cb in CJw as (_ & _ & WV).
  subst sp s0 s2 s3 s4 s5 s7 s8 s9 s10 s11 a0.
  pose proof (munch_refl [(lo, X); (cur, cur + 144); (X + 2320, X + 2340)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite ltu_lit by lia. replace (j <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
  step. step.
  eapply evt_cut.
  { eapply (ws_L11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m b j B);
      first [reflexivity | (f_equal; lia) | (rewrite neg_lit; f_equal; lia) | lia | assumption]. }
  intros ms' [a2x E]. subst ms'. fold i1.
  step. rewrite !neg_lit. replace (- - i1) with i1 by lia.
  step. rewrite ltu_lit by lia. replace (i1 <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
  pose proof (ws_rd m b B i1 BB ltac:(lia)) as RD1. pose proof (ws_byte B i1 FB) as HC1.
  step. step. rewrite ws_zxb by lia. step. step. rewrite eqb_lit by lia. rewrite C1, Z.eqb_refl. cbn [negb]. cbv iota.
  eapply evt_cut.
  { eapply ws12w with (b := b) (i := i1) (B := B); first [reflexivity | lia | assumption]. }
  intros ms' [a0x E]. subst ms'. fold i2.
  step. step. step. step. step.
  eapply (js_call JS) with (lo := lo) (X := X) (b := b) (i := i2) (V := X + 2320) (B := B) (j := j2) (k := vk)
    (s := vs) (l := vl); [js_side .. | ].
  intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU1 WM1 MI1 ST1 BV.
  rewrite (ret_pc_even 0x13aa4) by (first [lia | reflexivity]).
  unfold JSON_SCALAR_K in MU1.
  transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
  assert (CJ1 : rw_cells rsegs m1 (X + 2320)
                  [CB 20 (le8 (Z_to_bv 64 (b + vs)) ++ le8 (Z_to_bv 64 vl) ++ le4 (Z_to_bv 64 vk))]).
  { apply ser_cb. split; [rewrite !length_app, !length_le8, length_le4; reflexivity|]. split; [exact BV | exact WV]. }
  clear BV.
  step. rewrite eqb_lit by lia. replace (j2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
  eapply evt_cut.
  { eapply ws13w with (b := b) (i := j2) (B := B); first [reflexivity | lia | assumption]. }
  intros ms' [a0y E]. subst ms'. fold i3.
  eapply evt_cut.
  { eapply (slot_jt JT) with (lo := lo) (X := X) (b := b) (cur := cur) (ks := ks) (kl := kl) (B := B) (vpk := vpk);
      first [reflexivity | lia | assumption]. }
  intros ms' (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 & m2 &
              MU2 & WM2 & MI2 & ST2 & E).
  subst ms'. transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2 MI1.
  destruct (slot_of B (1, ks, kl)) as [k|] eqn:SO; cbv iota in JP |- *.
  - pose proof (slot_of_lt B (1, ks, kl) k SO) as Hk6.
    destruct (tv_kind (nth k o tok_none) =? 0) eqn:K0; cbv iota in JP; [|discriminate JP].
    apply Z.eqb_eq in K0.
    assert (Hko : (k < length o)%nat) by lia.
    assert (MD : (at_byte B i3 44 = true /\ json_pairs B (json_ws B (i3 + 1)) (set_nth k o (vk, vs, vl)) f = Some (r, o')) \/
                 (at_byte B i3 44 = false /\ at_byte B i3 125 = true /\ r = i3 + 1 /\ o' = set_nth k o (vk, vs, vl))).
    { destruct (at_byte B i3 44) eqn:A3; cbv iota in JP; [left; split; [reflexivity|exact JP]|].
      destruct (at_byte B i3 125) eqn:A4; cbv iota in JP; [|discriminate JP].
      injection JP as Er Eo. right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. symmetry. exact Eo. }
    clear JP.
    rewrite (obj_split b vpad o k Hko) in CO.
    pose proof (obj_pre_len b vpad o k Lv ltac:(lia)) as LA.
    rewrite (slot24_zero b vpad _ K0) in CO.
    replace 144%nat with (24 * k + (24 + (120 - 24 * k)))%nat in CO by lia.
    apply cb_app2 in CO as [CA CO']; [|exact LA].
    apply cb_app2 in CO' as [CZ CPo]; [|apply repeat_length].
    apply zslot in CZ.
    pose proof (rw_addr _ _ (cur + 24 * Z.of_nat k) _ CZ ltac:(lia)) as CZ'. clear CZ.
    pose proof (ser_cb_bytes _ _ _ _ CJ1) as BJ. pose proof (ser_cb_bytes _ _ _ _ CP) as BP.
    apply bytes_at_app in BJ as [B0 BJ']. apply bytes_at_app in BJ' as [B1 B2].
    assert (R0 : ov_read_bytes rsegs m2 (wa (X + 2320)) 8 = Some (le8 (Z_to_bv 64 (b + vs)))).
    { pose proof (rd_all _ _ _ B0) as R. rewrite length_le8 in R. exact R. }
    assert (R1 : ov_read_bytes rsegs m2 (wa (X + 2320 + 8)) 8 = Some (le8 (Z_to_bv 64 vl))).
    { pose proof (rd_all _ _ _ (ba_addr _ _ (X + 2320 + 8) _ B1 ltac:(rewrite length_le8; lia))) as R.
      rewrite length_le8 in R. exact R. }
    assert (R2 : ov_read_bytes rsegs m2 (wa (X + 2320 + 16)) 8 = Some (le4 (Z_to_bv 64 vk) ++ vpad)).
    { assert (B2' : bytes_at rsegs m2 (X + 2320 + 16) (le4 (Z_to_bv 64 vk) ++ vpad)).
      { apply bytes_at_app. split.
        - apply (ba_addr _ _ _ _ B2). rewrite !length_le8. lia.
        - apply (ba_addr _ _ _ _ BP). rewrite length_le4. lia. }
      pose proof (rd_all _ _ _ B2') as R. rewrite length_app, length_le4, Lv in R. exact R. }
    clear B0 B1 B2 BP.
    eapply evt_cut.
    { eapply slot_put with (SA := cur + 24 * Z.of_nat k) (V := X + 2320) (w0 := Z_to_bv 64 (b + vs))
        (w1 := Z_to_bv 64 vl) (bs2 := le4 (Z_to_bv 64 vk) ++ vpad);
        first [reflexivity | (f_equal; lia) | (rewrite length_app, length_le4, Lv; reflexivity) | lia | assumption]. }
    intros ms' (a0z & a2z & a3z & m3 & E & MU3 & WM3 & MI3 & CS3). subst ms'.
    transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
    pose proof (rw_addr _ _ (cur + Z.of_nat (24 * k)) _ CS3 ltac:(lia)) as CS4.
    pose proof (cb_join _ _ _ _ _ _ CS4 CPo) as CJ2.
    pose proof (cb_join _ _ _ _ _ _ CA CJ2) as CO2.
    assert (CO3 : rw_cells rsegs m3 cur [CB 144 (obj_bytes b vpad (set_nth k o (vk, vs, vl)))]).
    { rewrite (obj_set b vpad o k (vk, vs, vl) Hko). rewrite (slot24_val b vpad vk vs vl ltac:(lia)).
      replace 144%nat with (24 * k + (24 + (120 - 24 * k)))%nat by lia. exact CO2. }
    apply evt_done. do 18 eexists.
    exists (set_nth k o (vk, vs, vl)), (le8 (Z_to_bv 64 (b + vs)) ++ le8 (Z_to_bv 64 vl) ++ le4 (Z_to_bv 64 vk)).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST2|].
    split; [exact CO3|]. split; [exact CJ1|]. split; [lia|].
    split; [rewrite set_nth_length; exact Lo|].
    split; [apply set_nth_forall; [exact Io | right; cbn [fst snd]; lia]|].
    exact MD.
  - assert (MD : (at_byte B i3 44 = true /\ json_pairs B (json_ws B (i3 + 1)) o f = Some (r, o')) \/
                 (at_byte B i3 44 = false /\ at_byte B i3 125 = true /\ r = i3 + 1 /\ o' = o)).
    { destruct (at_byte B i3 44) eqn:A3; cbv iota in JP; [left; split; [reflexivity|exact JP]|].
      destruct (at_byte B i3 125) eqn:A4; cbv iota in JP; [|discriminate JP].
      injection JP as Er Eo. right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. symmetry. exact Eo. }
    clear JP.
    apply evt_done. do 18 eexists.
    exists o, (le8 (Z_to_bv 64 (b + vs)) ++ le8 (Z_to_bv 64 vl) ++ le4 (Z_to_bv 64 vk)).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact CO|]. split; [exact CJ1|]. split; [lia|]. split; [exact Lo|]. split; [exact Io|].
    exact MD.
Qed.
