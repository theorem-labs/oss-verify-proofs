(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import STRW_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope bv_scope.
Definition stpcpy_entry := 0x56a088%Z.
Definition strcpy_entry := 0x56a060%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stpcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D Sa : Z) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (D + Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + Z.of_nat (length str) + 1)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [CB (S (length str)) (str ++ [Z_to_bv 8 0])]
    /\ bytes_at asegs m' Sa (str ++ Z_to_bv 8 0 :: slack).

(* [comment removed for export] *)
Lemma le8_le_val : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (le_val (map bv_unsigned bs))) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as R. rewrite length_map, Hl in R. change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in R.
  rewrite unsigned_lit by lia. rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma firstn1_nth (l : list byte) i b : nth_error l i = Some b -> [b] = firstn 1 (skipn i l).
Proof.
  revert l. induction i as [|i IH]; intros [|x l] H; cbn in H |- *; try discriminate.
  - inversion H. reflexivity.
  - apply IH. exact H.
Qed.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack junk : list byte) (D Sa : Z).
  Notation L := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation cpy := (str ++ [Z_to_bv 8 0]).
  Notation W := [(D, D + L + 1)]%Z.
  Hypothesis STR : bytes_at asegs m Sa full.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (Sa + L + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis DST0 : rw_cells asegs m D [CB (S (length str)) junk].
  Hypothesis SEP : (Sa + Z.of_nat (length full) <= D \/ D + L + 1 <= Sa)%Z.
  Hypothesis MI0 : mem_inv asegs m.

  Notation POST := (stpcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D Sa str slack m).
  (* [comment removed for export] *)
  Notation ST pc mm x10 x11 x12 x13 x14 x15 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
    bytes_at asegs m1 Sa full /\ u8arr asegs m1 D bs /\ copied cpy bs (Z.to_nat P)
    /\ mem_inv asegs m1 /\ munch W m m1 /\ wmono asegs m m1.

  Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof. rewrite length_app. cbn. lia. Qed.
  Lemma cpy_length : length cpy = S (length str).
  Proof. rewrite length_app. cbn. lia. Qed.

  Lemma AB : (0 <= Sa /\ Sa + L + 1 + Z.of_nat (length slack) <= 2^64 /\ 0 <= D /\ D + L + 1 <= 2^64)%Z.
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B.
    pose proof (rw_cells_bound _ _ _ _ DST0) as B2. cbn [cells_size csize Nat.add] in B2. lia.
  Qed.

  Lemma full_nth_lt : forall i, (0 <= i < L)%Z -> exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.
  Lemma full_nth_len : nth_error full (Z.to_nat L) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.
  Lemma cpy_prefix : forall k, (k <= S (length str))%nat -> firstn k cpy = firstn k full.
  Proof.
    intros k Hk. replace full with (cpy ++ slack) by (rewrite <- app_assoc; reflexivity).
    rewrite !firstn_app. replace (k - length cpy)%nat with 0%nat by (rewrite cpy_length; lia). cbn [firstn]. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma inv_init : INV m junk 0.
  Proof.
    split; [exact STR|]. split; [exact (u8arr_of_rw_cells _ _ _ _ _ DST0)|].
    split; [apply copied_0; rewrite cpy_length; exact (rw_cells_CB_length _ _ _ _ _ DST0)|].
    split; [exact MI0|]. split; [apply munch_refl| apply wmono_refl].
  Qed.

  (* [comment removed for export] *)
  Lemma inv_read1 : forall m1 bs P (i : Z) b a, INV m1 bs P -> nth_error full (Z.to_nat i) = Some b -> (0 <= i)%Z -> a = wa (Sa + i) ->
    ov_read_bytes asegs m1 a 1 = Some [b].
  Proof. intros m1 bs P i b a (SRC & _) Hn Hi Ha. eapply u8ro_read; eauto. Qed.

  Lemma inv_read8 : forall m1 bs P (j : Z) a, INV m1 bs P -> (0 <= j)%Z -> (Z.to_nat j + 8 <= length full)%nat -> a = wa (Sa + j) ->
    ov_read_bytes asegs m1 a 8 = Some (firstn 8 (skipn (Z.to_nat j) full)) /\ length (firstn 8 (skipn (Z.to_nat j) full)) = 8%nat.
  Proof.
    intros m1 bs P j a (SRC & _) Hj HW ->. split; [apply (bytes_at_read asegs m1 Sa full j 8 SRC); lia|].
    rewrite firstn_length, skipn_length. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma inv_store : forall m1 bs P xs, INV m1 bs P -> (0 <= P)%Z -> (Z.to_nat P + length xs <= S (length str))%nat ->
    xs = firstn (length xs) (skipn (Z.to_nat P) full) ->
    store_ok asegs m1 (wa (D + P)) (length xs) = true
    /\ INV (write_to_mem m1 (wa (D + P)) xs) (upd_bytes bs (Z.to_nat P) xs) (P + Z.of_nat (length xs)).
  Proof.
    intros m1 bs P xs (SRC & DST & CP & MI & MU & WM) HP Hk Hxs. pose proof AB as B. pose proof (proj1 CP) as Lbs. rewrite cpy_length in Lbs.
    assert (SOK : store_ok asegs m1 (wa (D + P)) (length xs) = true).
    { eapply (u8arr_store_ok_n asegs m1 D bs P (length xs)); [exact DST| lia| rewrite Lbs; lia| reflexivity]. }
    split; [exact SOK|].
    split. { apply bytes_at_write_other; [exact SRC| lia| lia| rewrite full_length; rewrite full_length in SEP; lia]. }
    split. { apply (u8arr_write_bytes asegs m1 D bs P xs DST); [lia|]. rewrite Lbs. lia. }
    split. { apply copied_updZ; [exact CP| lia| | rewrite cpy_length; lia]. rewrite Hxs at 2.
             rewrite !firstn_skipn_comm. rewrite cpy_prefix by lia. reflexivity. }
    split. { apply mem_inv_store; assumption. }
    split. { apply munch_write; [exact MU| lia| lia|]. cbn [inside]. left. lia. }
    apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma inv_fin : forall m1 bs P, INV m1 bs P -> (S (length str) <= Z.to_nat P)%nat ->
    munch W m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 D [CB (S (length str)) cpy] /\ bytes_at asegs m1 Sa full.
  Proof.
    intros m1 bs P (SRC & DST & CP & MI & MU & WM) HP.
    pose proof (copied_all _ _ _ CP ltac:(rewrite cpy_length; exact HP)) as E. rewrite E in DST.
    apply rw_cells_of_u8arr in DST. rewrite cpy_length in DST. auto 6.
  Qed.

  (* [comment removed for export] *)
  Ltac rd1 I i b Hn :=
    let a := cur_mem_addr in let RD := fresh "RD" in
    pose proof (inv_read1 _ _ _ i b a I Hn ltac:(lia) ltac:(addr_tac)) as RD; zstep; try clear RD;
    lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.

  (* [comment removed for export] *)
  Lemma sc_tail : forall (k : nat) (P : Z) m1 bs x11 x13 x14 x15,
    Z.to_nat (L + 1 - P) = k -> (1 <= P <= L)%Z -> INV m1 bs P ->
    evt asegs POST (ST 0x56a124 m1 (Z_to_bv 64 (D + P + -1)) x11 (Z_to_bv 64 (Sa + P)) x13 x14 x15).
  Proof.
    induction k as [|k IH]; intros P m1 bs x11 x13 x14 x15 Hk HP I; [lia|].
    pose proof AB as B.
    destruct (Z.eq_dec P L) as [EQ|NE].
    - (* [comment removed for export] *)
      pose proof full_nth_len as HN. rewrite <- EQ in HN.
      rd1 I P (Z_to_bv 8 0) HN. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
      (* [comment removed for export] *)
      zstep.
      destruct (inv_store m1 bs P [Z_to_bv 8 0] I ltac:(lia) ltac:(cbn; lia) (firstn1_nth _ _ _ HN)) as [SOK I'].
      change (wa (D + P)) with (Z_to_bv 64 (D + P)) in SOK, I'. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in SOK, I'.
      zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. clear SOK.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (m2 := mc) in * end. clearbody m2. clear I.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_false. zstep. zstep.
      destruct (inv_fin _ _ _ I' ltac:(lia)) as (MU & WM & MI & CH & BY).
      replace (D + P)%Z with (D + L)%Z by lia. finish.
    - (* [comment removed for export] *)
      destruct (full_nth_lt P ltac:(lia)) as (b & HN & Hb).
      rd1 I P b HN.
      zstep.
      destruct (inv_store m1 bs P [b] I ltac:(lia) ltac:(cbn; lia) (firstn1_nth _ _ _ HN)) as [SOK I'].
      change (wa (D + P)) with (Z_to_bv 64 (D + P)) in SOK, I'. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in SOK, I'.
      zstep. rewrite (le1_zxb b). clear SOK.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (m2 := mc) in * end. clearbody m2. clear I.
      zstep. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
      replace (D + P)%Z with (D + (P + 1) + -1)%Z by lia. replace (Sa + P + 1)%Z with (Sa + (P + 1))%Z by lia.
      apply (IH (P + 1)%Z _ _ _ _ _ _ ltac:(lia) ltac:(lia) I').
  Qed.

  (* [comment removed for export] *)
  Lemma le_val_low : forall (b : byte) (bs : list byte), Z.land (le_val (map bv_unsigned (b :: bs))) 255 = bv_unsigned b.
  Proof.
    intros b bs. cbn [map le_val]. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8)%Z with 256%Z.
    pose proof (byte_range b). pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)).
    replace (bv_unsigned b + 256 * le_val (map bv_unsigned bs))%Z with (bv_unsigned b + le_val (map bv_unsigned bs) * 256)%Z by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_zero : forall (j : Z) m1 bs x13 x14 x15,
    (0 <= j <= L)%Z -> INV m1 bs j -> (Z.to_nat j + 8 <= length full)%nat ->
    evt asegs POST (ST 0x56a114 m1 (Z_to_bv 64 (D + j)) (Z_to_bv 64 (Sa + j)) (Z_to_bv 64 (le_val (map bv_unsigned (firstn 8 (skipn (Z.to_nat j) full))))) x13 x14 x15).
  Proof.
    intros j m1 bs x13 x14 x15 Hj I HW. pose proof AB as B.
    destruct (firstn 8 (skipn (Z.to_nat j) full)) as [|b rest] eqn:EC.
    { exfalso. apply (f_equal (@length byte)) in EC. rewrite length_firstn, length_skipn in EC. cbn [length] in EC. lia. }
    assert (HN : nth_error full (Z.to_nat j) = Some b).
    { rewrite <- (Nat.add_0_r (Z.to_nat j)), <- nth_error_skipn. destruct (skipn (Z.to_nat j) full) as [|x y]; [discriminate|]. cbn in EC |- *. congruence. }
    (* [comment removed for export] *)
    assert (R : (0 <= le_val (map bv_unsigned (b :: rest)) < 2^64)%Z).
    { pose proof (le_val_range (map bv_unsigned (b :: rest)) (bytes_ok_map (b :: rest))) as R. rewrite length_map in R.
      apply (f_equal (@length byte)) in EC. rewrite length_firstn, length_skipn in EC. rewrite <- EC in R.
      replace (Nat.min 8 (length full - Z.to_nat j)) with 8%nat in R by lia. exact R. }
    zstep. rewrite ?unsigned_lit, ?(Z.mod_small _ _ R) by lia. rewrite le_val_low. pose proof (byte_range b) as BR.
    (* [comment removed for export] *)
    destruct (inv_store m1 bs j [b] I ltac:(lia) ltac:(cbn; lia) (firstn1_nth _ _ _ HN)) as [SOK I'].
    change (wa (D + j)) with (Z_to_bv 64 (D + j)) in SOK, I'. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in SOK, I'.
    zstep. rewrite (le1_zxb b). clear SOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (m2 := mc) in * end. clearbody m2. clear I.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (EJ : j = L). { destruct (Z.eq_dec j L) as [E|NE]; [exact E|]. exfalso. destruct (full_nth_lt j ltac:(lia)) as (b' & HN' & Hb'). rewrite HN in HN'. inversion HN'. subst. exact (Hb' K). }
      zstep. destruct (inv_fin _ _ _ I' ltac:(lia)) as (MU & WM & MI & CH & BY).
      replace (D + j)%Z with (D + L)%Z by lia. finish.
    - (* [comment removed for export] *)
      assert (NJ : j <> L). { intros E. apply K. pose proof full_nth_len as X. rewrite <- E, HN in X. inversion X. reflexivity. }
      zstep. replace (D + j)%Z with (D + (j + 1) + -1)%Z by lia. replace (Sa + j + 1)%Z with (Sa + (j + 1))%Z by lia.
      apply (sc_tail (Z.to_nat (L + 1 - (j + 1))) (j + 1)%Z _ _ _ _ _ _ eq_refl ltac:(lia) I').
  Qed.

  Ltac rd8 I j CH CL :=
    let a := cur_mem_addr in let RD := fresh "RD" in
    destruct (inv_read8 _ _ _ j a I ltac:(lia) ltac:(rewrite full_length; Z.div_mod_to_equations; lia) ltac:(addr_tac)) as [RD CL];
    set (CH := firstn 8 (skipn (Z.to_nat j) full)) in RD, CL;
    zstep; try clear RD; rewrite ?(load8_le_val CH CL).

  (* [comment removed for export] *)
  Lemma chunk_noz : forall j, (0 <= j <= L)%Z -> (Z.to_nat j + 8 <= length full)%nat ->
    ~ In 0%Z (map bv_unsigned (firstn 8 (skipn (Z.to_nat j) full))) -> (j + 8 <= L)%Z.
  Proof.
    intros j Hj HW K. rewrite In0_map_unsigned in K.
    destruct (Z.lt_ge_cases L (j + 8)); [|assumption]. exfalso. apply K.
    apply nth_error_In with (n := (Z.to_nat L - Z.to_nat j)%nat).
    rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_skipn, <- full_nth_len. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_words : forall (k : nat) (j : Z) m1 bs x15,
    Z.to_nat (L - j) = k -> (0 <= j <= L)%Z -> ((Sa + j) mod 8 = 0)%Z -> INV m1 bs j -> (Z.to_nat j + 8 <= length full)%nat ->
    ~ In 0%Z (map bv_unsigned (firstn 8 (skipn (Z.to_nat j) full))) ->
    evt asegs POST (ST 0x56a0f4 m1 (Z_to_bv 64 (D + j)) (Z_to_bv 64 (Sa + j)) (Z_to_bv 64 (le_val (map bv_unsigned (firstn 8 (skipn (Z.to_nat j) full)))))
                      (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) x15).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros j m1 bs x15 Hk Hj Hal I HW NZ; pose proof AB as B.
    pose proof (chunk_noz j Hj HW NZ) as J8.
    set (CH := firstn 8 (skipn (Z.to_nat j) full)) in *.
    assert (CL : length CH = 8%nat) by (subst CH; rewrite length_firstn, length_skipn; lia).
    pose proof (le_val_range (map bv_unsigned CH) (bytes_ok_map CH)) as R. rewrite length_map, CL in R. change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in R.
    (* [comment removed for export] *)
    destruct (inv_store m1 bs j CH I ltac:(lia) ltac:(rewrite CL; lia) ltac:(rewrite CL; reflexivity)) as [SOK I'].
    change (wa (D + j)) with (Z_to_bv 64 (D + j)) in SOK, I'. rewrite CL in SOK, I'. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in I'.
    zstep. rewrite (le8_le_val CH CL). clear SOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (m2 := mc) in * end. clearbody m2. clear I.
    (* [comment removed for export] *)
    rd8 I' (j + 8)%Z CH2 CL2.
    pose proof (le_val_range (map bv_unsigned CH2) (bytes_ok_map CH2)) as R2. rewrite length_map, CL2 in R2. change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in R2.
    replace (bv_extract 0 64 (le_bytes_to_word CH2)) with (Z_to_bv 64 (le_val (map bv_unsigned CH2))).
    2:{ apply bv_eq. rewrite (load8_le_val CH2 CL2), unsigned_lit by lia. reflexivity. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply (haszero64_clang _ (bytes_ok_map CH2) ltac:(rewrite length_map; exact CL2)) in K.
      pose proof (chunk_noz (j + 8) ltac:(lia) ltac:(subst CH2; rewrite full_length; Z.div_mod_to_equations; lia) K) as J16.
      replace (D + j + 8)%Z with (D + (j + 8))%Z by lia. replace (Sa + j + 8)%Z with (Sa + (j + 8))%Z by lia.
      apply (IH (Z.to_nat (L - (j + 8))) ltac:(lia) (j + 8)%Z _ _ _ eq_refl ltac:(lia) ltac:(Z.div_mod_to_equations; lia) I' ltac:(rewrite full_length; Z.div_mod_to_equations; lia) K).
    - (* [comment removed for export] *)
      replace (D + j + 8)%Z with (D + (j + 8))%Z by lia. replace (Sa + j + 8)%Z with (Sa + (j + 8))%Z by lia.
      apply (sc_zero (j + 8)%Z _ _ _ _ _ ltac:(lia) I' ltac:(rewrite full_length; Z.div_mod_to_equations; lia)).
  Qed.


  (* [comment removed for export] *)
  Lemma sc_wentry : forall (j : Z) m1 bs x12 x13 x14 x15,
    (0 <= j <= L)%Z -> ((Sa + j) mod 8 = 0)%Z -> INV m1 bs j ->
    evt asegs POST (ST 0x56a0d0 m1 (Z_to_bv 64 (D + j)) (Z_to_bv 64 (Sa + j)) x12 x13 x14 x15).
  Proof.
    intros j m1 bs x12 x13 x14 x15 Hj Hal I. pose proof AB as B. pose proof I as (SRCx & DSTx & CPx & MI & MUx & WMx).
    (* [comment removed for export] *)
    zstep. zstep.
    rd8 I j CH CL.
    pose proof (le_val_range (map bv_unsigned CH) (bytes_ok_map CH)) as R. rewrite length_map, CL in R. change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in R.
    replace (bv_extract 0 64 (le_bytes_to_word CH)) with (Z_to_bv 64 (le_val (map bv_unsigned CH))).
    2:{ apply bv_eq. rewrite (load8_le_val CH CL), unsigned_lit by lia. reflexivity. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply (sc_zero j _ _ _ _ _ Hj I ltac:(rewrite full_length; Z.div_mod_to_equations; lia)).
    - apply (haszero64_clang _ (bytes_ok_map CH) ltac:(rewrite length_map; exact CL)) in K.
      apply (sc_words (Z.to_nat (L - j)) j _ _ _ eq_refl Hj Hal I ltac:(rewrite full_length; Z.div_mod_to_equations; lia) K).
  Qed.

  (* [comment removed for export] *)
  Lemma sc_head : forall (k : nat) (i : Z) m1 bs x13 x14 x15,
    Z.to_nat (L + 1 - i) = k -> (0 <= i <= L)%Z -> INV m1 bs i ->
    evt asegs POST (ST 0x56a0b0 m1 (Z_to_bv 64 (D + i)) (Z_to_bv 64 (Sa + i)) (Z_to_bv 64 (Sa + i + 1)) x13 x14 x15).
  Proof.
    induction k as [|k IH]; intros i m1 bs x13 x14 x15 Hk Hi I; [lia|]. pose proof AB as B.
    destruct (Z.eq_dec i L) as [EQ|NE].
    - pose proof full_nth_len as HN. rewrite <- EQ in HN.
      rd1 I i (Z_to_bv 8 0) HN. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
      destruct (inv_store m1 bs i [Z_to_bv 8 0] I ltac:(lia) ltac:(cbn; lia) (firstn1_nth _ _ _ HN)) as [SOK I'].
      change (wa (D + i)) with (Z_to_bv 64 (D + i)) in SOK, I'. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in SOK, I'.
      zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. clear SOK.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (m2 := mc) in * end. clearbody m2. clear I.
      zstep. if_true. zstep.
      destruct (inv_fin _ _ _ I' ltac:(lia)) as (MU & WM & MI & CH & BY).
      replace (D + i)%Z with (D + L)%Z by lia. finish.
    - destruct (full_nth_lt i ltac:(lia)) as (b & HN & Hb). pose proof (byte_range b) as BR.
      rd1 I i b HN.
      destruct (inv_store m1 bs i [b] I ltac:(lia) ltac:(cbn; lia) (firstn1_nth _ _ _ HN)) as [SOK I'].
      change (wa (D + i)) with (Z_to_bv 64 (D + i)) in SOK, I'. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in SOK, I'.
      zstep. rewrite (le1_zxb b). clear SOK.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (m2 := mc) in * end. clearbody m2. clear I.
      zstep. if_cases K0; zify_cond K0. { exfalso. exact (Hb K0). }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
      + replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (Sa + i + 2)%Z with (Sa + (i + 1) + 1)%Z by lia. replace (Sa + i + 1)%Z with (Sa + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z _ _ _ _ _ ltac:(lia) ltac:(lia) I').
      + replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (Sa + i + 1)%Z with (Sa + (i + 1))%Z by lia.
        apply (sc_wentry (i + 1)%Z _ _ _ _ _ _ ltac:(lia) ltac:(revert Kal; zb_masks; intros Kal; Z.div_mod_to_equations; lia) I').
  Qed.

  (* [comment removed for export] *)
  Lemma stpcpy_body : forall (x10 x11 x12 x13 x14 x15 : word),
    bv_unsigned x10 = D -> bv_unsigned x11 = Sa ->
    evt asegs POST (ST 0x56a088 m x10 x11 x12 x13 x14 x15).
  Proof.
    intros x10 x11 x12 x13 x14 x15 HD HS. pose proof AB as B. pose proof inv_init as I.
    assert (E10 : x10 = Z_to_bv 64 (D + 0)) by (rewrite Z.add_0_r, <- HD; symmetry; apply Z_to_bv_bv_unsigned).
    assert (E11 : x11 = Z_to_bv 64 (Sa + 0)) by (rewrite Z.add_0_r, <- HS; symmetry; apply Z_to_bv_bv_unsigned).
    subst x10 x11. clear HD HS.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KX; zify_cond KX.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia.
      + replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + 0)) by (f_equal; lia). replace (Z_to_bv 64 Sa) with (Z_to_bv 64 (Sa + 0)) by (f_equal; lia).
        apply (sc_wentry 0 _ _ _ _ _ _ ltac:(lia) ltac:(revert KA; zb_masks; intros KA; Z.div_mod_to_equations; lia) I).
      + (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + 0)) by (f_equal; lia). replace (Z_to_bv 64 Sa) with (Z_to_bv 64 (Sa + 0)) by (f_equal; lia).
        replace (Sa + 1)%Z with (Sa + 0 + 1)%Z by lia.
        apply (sc_head (Z.to_nat (L + 1 - 0)) 0 _ _ _ _ _ eq_refl ltac:(lia) I).
    - (* [comment removed for export] *)
      destruct (Z.eq_dec 0 L) as [EQ|NE].
      + pose proof full_nth_len as HN. rewrite <- EQ in HN.
        rd1 I 0%Z (Z_to_bv 8 0) HN. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        destruct (inv_store m junk 0 [Z_to_bv 8 0] I ltac:(lia) ltac:(cbn; lia) (firstn1_nth _ _ _ HN)) as [SOK I'].
        change (wa (D + 0)) with (Z_to_bv 64 (D + 0)) in SOK, I'. rewrite (Z.add_0_r D) in SOK, I'. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in SOK, I'.
        zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. clear SOK.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (m2 := mc) in * end. clearbody m2. clear I.
        zstep. if_false. zstep. zstep.
        destruct (inv_fin _ _ _ I' ltac:(lia)) as (MU & WM & MI & CH & BY).
        replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + L)) by (f_equal; lia). finish.
      + destruct (full_nth_lt 0 ltac:(lia)) as (b & HN & Hb). pose proof (byte_range b) as BR.
        rd1 I 0%Z b HN.
        destruct (inv_store m junk 0 [b] I ltac:(lia) ltac:(cbn; lia) (firstn1_nth _ _ _ HN)) as [SOK I'].
        change (wa (D + 0)) with (Z_to_bv 64 (D + 0)) in SOK, I'. rewrite (Z.add_0_r D) in SOK, I'. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in SOK, I'.
        zstep. rewrite (le1_zxb b). clear SOK.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (m2 := mc) in * end. clearbody m2. clear I.
        zstep. if_cases K0; zify_cond K0. 2:{ exfalso. exact (Hb K0). }
        (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + 1 + -1)) by (f_equal; lia).
        apply (sc_tail (Z.to_nat (L + 1 - 1)) 1 _ _ _ _ _ _ eq_refl ltac:(lia) I').
  Qed.
End Proofs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stpcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack junk : list byte),
  bytes_at asegs m (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a1 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  rw_cells asegs m (bv_unsigned a0) [CB (S (length str)) junk] ->
  (bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned a0
   \/ bv_unsigned a0 + Z.of_nat (length str) + 1 <= bv_unsigned a1)%Z ->
  mem_inv asegs m ->
  evt asegs (stpcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (bv_unsigned a1) str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x56a088) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros STR NONUL PAD DST SEP MI.
  eapply stpcpy_body; try eassumption; try reflexivity.
  rewrite length_app. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
Definition strcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (Sa : Z) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (S (length str)) (str ++ [Z_to_bv 8 0])]
    /\ bytes_at asegs m' Sa (str ++ Z_to_bv 8 0 :: slack).

Lemma strcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack junk : list byte) (lo : Z),
  bytes_at asegs m (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a1 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  rw_cells asegs m (bv_unsigned a0) [CB (S (length str)) junk] ->
  (bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned a0
   \/ bv_unsigned a0 + Z.of_nat (length str) + 1 <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 <= lo)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> (bv_unsigned sp + 8 <= 2^64)%Z ->
  mem_inv asegs m ->
  evt asegs (strcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 (bv_unsigned a1) str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x56a060) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros STR NONUL PAD DST SEP HS HD ST LO SPH MI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. eapply evt_cut.
  { eapply (stpcpy_spec _ _ gp tp t0 t1 t2 a0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 str slack junk);
      [exact STR| exact NONUL| exact PAD| exact DST| exact SEP| exact MI]. }
  intros ms2 PC. unfold stpcpy_post in PC.
  destruct PC as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & CH2 & BY2).
  replace (ret_pc (Z_to_bv 64 5677172)) with (Z_to_bv 64 5677172) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR| exact MU2| exact WM2|]. cbn. lia. }
  assert (ST2 : stk asegs m2 lo (bv_unsigned sp + -16)).
  { eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2|]. cbn. pose proof (proj1 ST). lia. }
  assert (MU' : munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1)]%Z m m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x Hx. cbn in Hx |- *. lia. }
  assert (WM' : wmono asegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2 FR ST MI STR DST.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.
  release_frame FR2 ST2 (bv_unsigned sp).
  finish.
Qed.
