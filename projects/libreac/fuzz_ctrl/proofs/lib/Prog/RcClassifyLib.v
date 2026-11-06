From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBoxLib RcParse RcClassify.
Import ListNotations.
Open Scope Z_scope.

Definition cl_tail (k : Z) (fr : list byte) : option Z :=
  if k =? 7 then Some 3
  else if (k =? 2) && (cp_v fr 19 =? 3) then Some 4
  else if k =? 9 then Some 5
  else Some 2.

Definition cl_d9 (k : Z) (fr us : list byte) : option Z :=
  if negb (cl_eq6 fr us) then None else cl_tail k fr.

Definition cl_d7 (k : Z) (fr us : list byte) : option Z :=
  if cp_bcast fr then (if k =? 1 then Some 0 else None) else cl_d9 k fr us.

Definition cl_d5 (k : Z) (fr us : list byte) : option Z :=
  if k =? 5 then (if cl_join fr then Some 1 else None) else cl_d7 k fr us.

Definition cl_d4 (k : Z) (fr us : list byte) : option Z :=
  if negb (k =? 1) && negb (cl_bsum fr =? 0) then None else cl_d5 k fr us.

Definition cl_d3 (k : Z) (fr us : list byte) : option Z :=
  if cl_eq6 (skipn 6 fr) us then None else cl_d4 k fr us.

Definition cl_d2 (k : Z) (fr us : list byte) : option Z :=
  if negb (cl_oui fr) then None else cl_d3 k fr us.

Lemma classify_d1 : forall n fr us,
  classify n fr us = if fst (ctrlparse n fr) =? 0 then None else cl_d2 (fst (ctrlparse n fr)) fr us.
Proof. reflexivity. Qed.

Lemma classify_some : forall n fr us e, classify n fr us = Some e ->
  fst (ctrlparse n fr) <> 0 /\ 50 <= n /\ cl_oui fr = true /\ cl_eq6 (skipn 6 fr) us = false /\
  (fst (ctrlparse n fr) = 1 \/ cl_bsum fr = 0) /\ 0 <= e <= 5.
Proof.
  intros n fr us e. rewrite classify_d1.
  destruct (Z.eqb_spec (fst (ctrlparse n fr)) 0) as [K0|K0]; [discriminate|].
  assert (HN : 50 <= n).
  { destruct (Z.le_gt_cases 50 n) as [L|L]; [exact L|]. exfalso. apply K0. apply ctrlparse_none. lia. }
  unfold cl_d2, cl_d3, cl_d4, cl_d5, cl_d7, cl_d9, cl_tail.
  destruct (cl_oui fr); cbn [negb]; [|discriminate].
  destruct (cl_eq6 (skipn 6 fr) us); [discriminate|].
  destruct (Z.eqb_spec (fst (ctrlparse n fr)) 1) as [K1|K1];
    destruct (Z.eqb_spec (cl_bsum fr) 0) as [B0|B0]; cbn [negb andb]; [ | | | discriminate];
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    intros H; inversion H; subst; repeat split; try lia; tauto.
Qed.

Lemma cl_hdr : forall n fr, fst (ctrlparse n fr) <> 0 ->
  50 <= n /\ snd (ctrlparse n fr) = cp_struct fr (fst (ctrlparse n fr)).
Proof.
  intros n fr H. unfold ctrlparse in *. destruct (cp_hdr n fr) eqn:E; cbn [fst snd] in *.
  - split; [apply cp_hdr_spec in E; tauto | reflexivity].
  - exfalso. apply H. reflexivity.
Qed.

Lemma cl_struct_length : forall fr k, length (cp_struct fr k) = 36%nat.
Proof. intros fr k. unfold cp_struct. destruct (cp_rec fr), (k =? 6); reflexivity. Qed.

Lemma cl_nth_skipn : forall (l : list byte) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l i d; [reflexivity|].
  destruct l as [|x l]; cbn [skipn].
  - destruct i; reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma cl_eq6_src : forall fr us,
  cl_eq6 [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11] us = cl_eq6 (skipn 6 fr) us.
Proof.
  intros fr us. unfold cl_eq6. cbn [seq forallb]. rewrite !cl_nth_skipn. reflexivity.
Qed.

Lemma cl_eq6_dst : forall fr us,
  cl_eq6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5] us = cl_eq6 fr us.
Proof. reflexivity. Qed.

Lemma cl_memcmp6 : forall ls rs, length ls = 6%nat -> length rs = 6%nat ->
  exists w, memcmp_model ls rs 6 = Some w /\ -256 < w < 256 /\ (w =? 0) = cl_eq6 ls rs.
Proof.
  intros ls rs Hl Hr.
  destruct ls as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; cbn in Hl; try lia.
  destruct rs as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|? ?]]]]]]]; cbn in Hr; try lia.
  pose proof (byte_range x0). pose proof (byte_range x1). pose proof (byte_range x2).
  pose proof (byte_range x3). pose proof (byte_range x4). pose proof (byte_range x5).
  pose proof (byte_range y0). pose proof (byte_range y1). pose proof (byte_range y2).
  pose proof (byte_range y3). pose proof (byte_range y4). pose proof (byte_range y5).
  unfold cl_eq6. cbn [memcmp_model seq forallb nth].
  destruct (bv_unsigned x0 =? bv_unsigned y0) eqn:E0; cbn [andb];
    [|eexists; split; [reflexivity|]; apply Z.eqb_neq in E0; split; [lia|]; apply Z.eqb_neq; lia].
  destruct (bv_unsigned x1 =? bv_unsigned y1) eqn:E1; cbn [andb];
    [|eexists; split; [reflexivity|]; apply Z.eqb_neq in E1; split; [lia|]; apply Z.eqb_neq; lia].
  destruct (bv_unsigned x2 =? bv_unsigned y2) eqn:E2; cbn [andb];
    [|eexists; split; [reflexivity|]; apply Z.eqb_neq in E2; split; [lia|]; apply Z.eqb_neq; lia].
  destruct (bv_unsigned x3 =? bv_unsigned y3) eqn:E3; cbn [andb];
    [|eexists; split; [reflexivity|]; apply Z.eqb_neq in E3; split; [lia|]; apply Z.eqb_neq; lia].
  destruct (bv_unsigned x4 =? bv_unsigned y4) eqn:E4; cbn [andb];
    [|eexists; split; [reflexivity|]; apply Z.eqb_neq in E4; split; [lia|]; apply Z.eqb_neq; lia].
  destruct (bv_unsigned x5 =? bv_unsigned y5) eqn:E5; cbn [andb];
    [|eexists; split; [reflexivity|]; apply Z.eqb_neq in E5; split; [lia|]; apply Z.eqb_neq; lia].
  eexists; split; [reflexivity|]. split; [lia|]. reflexivity.
Qed.

Lemma cl_eqb0 : forall w, -2^64 < w < 2^64 -> bv_eqb (Z_to_bv 64 w) (Z_to_bv 64 0) = (w =? 0).
Proof.
  intros w Hw. unfold bv_eqb. rewrite unsigned_lit_wrap. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.eqb_spec w 0) as [E|E]; [subst; reflexivity|].
  apply Z.eqb_neq. intros M. apply E. Z.div_mod_to_equations. lia.
Qed.

Lemma cl_zxb_eqb : forall (b : byte) c, 0 <= c < 2^64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof. intros b c Hc. unfold zxb. pose proof (byte_range b). apply rc_eqb_lit; lia. Qed.

Lemma cl_lw_small : forall x, 0 <= x < 128 ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word [Z_to_bv 8 x; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0])) = Z_to_bv 64 x.
Proof.
  intros x Hx.
  replace [Z_to_bv 8 x; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] with (le4 (Z_to_bv 64 x)).
  - rewrite sext_extract_le4. unfold sx32. rewrite unsigned_lit by lia. rewrite rc_swrap_small by lia. reflexivity.
  - unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
    rewrite !Z.shiftr_div_pow2 by lia. rewrite (Z.div_small x (2^8)) by lia.
    rewrite !Z.div_0_l by lia. reflexivity.
Qed.

Lemma cl_lhu : forall b0 b1 : byte,
  zext 64 (bv_extract 0 16 (le_bytes_to_word [b0; b1])) = Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1).
Proof.
  intros b0 b1. pose proof (byte_range b0) as R0. pose proof (byte_range b1) as R1.
  replace [b0; b1] with (le2 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1))).
  - rewrite zext_extract_le2. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
  - unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
    f_equal; [|f_equal];
    apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
    rewrite ?Z.shiftr_div_pow2 by lia; change (2^8) with 256; Z.div_mod_to_equations; lia.
Qed.

Lemma cl_join_lhu : forall fr, 
  cl_join fr = (cp_v fr 22 =? 0) &&
    ((cp_v fr 35 + 256 * cp_v fr 34 =? 256) || (cp_v fr 35 + 256 * cp_v fr 34 =? 770)).
Proof.
  intros fr. unfold cl_join, cp_v. pose proof (byte_range (cp_b fr 34)). pose proof (byte_range (cp_b fr 35)).
  f_equal.
  destruct (Z.eqb_spec (bv_unsigned (cp_b fr 34)) 1), (Z.eqb_spec (bv_unsigned (cp_b fr 35)) 0),
    (Z.eqb_spec (bv_unsigned (cp_b fr 34)) 3), (Z.eqb_spec (bv_unsigned (cp_b fr 35)) 2),
    (Z.eqb_spec (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 256),
    (Z.eqb_spec (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 770); cbn [andb orb]; lia.
Qed.

Lemma cl_rd : forall segs m A (bs out : list byte) (k j : nat), bytes_at segs m A bs -> (k + j <= length bs)%nat ->
  firstn j (skipn k bs) = out -> ov_read_bytes segs m (wa (A + Z.of_nat k)) j = Some out.
Proof. intros segs m A bs out k j H Hl E. subst out. apply bytes_at_ov_read; assumption. Qed.

Lemma cl_rw_c4 : forall segs m A (w : word), rw_cells segs m A [C4 w] -> rw_cells segs m A [CB 4 (le4 w)].
Proof.
  intros segs m A w [[_ HBy] HW]. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact (length_le4 w)|exact I].
  - exact HBy.
  - exact HW.
Qed.

Lemma cl_rw_of : forall segs m A bs, bytes_at segs m A bs -> wr_at segs m A (Z.of_nat (length bs)) ->
  rw_cells segs m A [CB (length bs) bs].
Proof.
  intros segs m A bs HBy HW. split; [split|].
  - cbn. split; [reflexivity|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HBy.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma cl_hk : forall n fr, fst (ctrlparse n fr) <> 0 ->
  50 <= n /\ snd (ctrlparse n fr) = cp_struct fr (fst (ctrlparse n fr)) /\
  (fst (ctrlparse n fr) = 5 -> cp_rec fr = true).
Proof.
  intros n fr H. destruct (cl_hdr n fr H) as [HN EB]. split; [exact HN|]. split; [exact EB|].
  intros K5. apply (ctrlparse_rec n fr (or_introl K5)).
Qed.

Lemma cl_bc16 : forall fr k, firstn 4 (skipn 16 (cp_struct fr k)) =
  [Z_to_bv 8 (if cp_bcast fr then 1 else 0); Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof. intros fr k. unfold cp_struct. destruct (cp_bcast fr); reflexivity. Qed.

Lemma cl_land3 : forall x, x mod 4 = 0 -> 0 <= x < 2^64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 3) = Z_to_bv 64 0.
Proof.
  intros x H R. rewrite unsigned_lit by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
  change (2^2) with 4. rewrite H. reflexivity.
Qed.

Lemma cl_le4_small : forall x, 0 <= x < 256 ->
  le4 (Z_to_bv 64 x) = [Z_to_bv 8 x; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  intros x Hx. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_div_pow2 by lia. rewrite (Z.div_small x (2^8)) by lia.
  rewrite !Z.div_0_l by lia. reflexivity.
Qed.

Lemma cl_sx32 : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold sx32. rewrite unsigned_lit by lia. rewrite rc_swrap_small by lia. reflexivity. Qed.

Lemma cl_le2 : forall b0 b1 : byte, le2 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1)) = [b0; b1].
Proof.
  intros b0 b1. pose proof (byte_range b0) as R0. pose proof (byte_range b1) as R1.
  unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  f_equal; [|f_equal];
  apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
  rewrite ?Z.shiftr_div_pow2 by lia; change (2^8) with 256; symmetry; Z.div_mod_to_equations; lia.
Qed.

Lemma cl_zx16 : forall x, 0 <= x < 65536 -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
