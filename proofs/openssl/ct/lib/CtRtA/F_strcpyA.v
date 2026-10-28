(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_cpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition strcpy_entry := 0x52b730%Z.
Definition STRCPY_STACK := 16%Z.

Definition strcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (str : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1); (bv_unsigned sp - 16, bv_unsigned sp)]%Z m m'
    /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ rw_cells ctasegs m' (bv_unsigned a0) [CB (length str + 1)%nat (str ++ [Z_to_bv 8 0])].

(* [comment removed for export] *)
Lemma u8arr_store_ok_n : forall m A bs (P : Z) (k : nat) a,
  u8arr ctasegs m A bs -> (0 <= P)%Z -> (P + Z.of_nat k <= Z.of_nat (length bs))%Z -> a = wa (A + P) -> store_ok ctasegs m a k = true.
Proof. intros m A bs P k a [_ Hw] HP Hk ->. eapply wr_at_store_ok; [exact Hw|lia|lia]. Qed.

Lemma u8arr_write_bytes : forall m A bs (P : Z) xs,
  u8arr ctasegs m A bs -> (0 <= P)%Z -> (Z.to_nat P + length xs <= length bs)%nat ->
  u8arr ctasegs (write_to_mem m (wa (A + P)) xs) A (upd_bytes bs (Z.to_nat P) xs).
Proof.
  intros m A bs P xs [Hb Hw] HP Hl. split.
  - apply (bytes_at_write_inside ctasegs m A bs P xs Hb); [lia|exact Hl].
  - rewrite upd_bytes_length by exact Hl. apply wr_at_write. exact Hw.
Qed.

Lemma nth_error_first1 : forall {X} (l : list X) i b, nth_error l i = Some b -> firstn 1 (skipn i l) = [b].
Proof.
  intros X l i b H. revert l H. induction i as [|i IH]; intros [|x l] H; cbn in *; try discriminate; [injection H as ->; reflexivity|]. apply IH. exact H.
Qed.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack junk : list byte) (lo : Z).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1); (bv_unsigned sp - 16, bv_unsigned sp)]%Z.
  Hypothesis MI0 : mem_inv ctasegs m.
  Hypothesis STR : bytes_at ctasegs m S full.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (S + len + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis DST0 : rw_cells ctasegs m D [CB (length str + 1)%nat junk].
  Hypothesis ST0 : stk ctasegs m lo SP.
  Hypothesis AB : (0 <= lo /\ lo <= SP - 16 /\ SP <= 2^64)%Z.
  Hypothesis SEP_SD : (S + len + 1 + Z.of_nat (length slack) <= D \/ D + len + 1 <= S)%Z.
  Hypothesis SEP_SF : (S + len + 1 + Z.of_nat (length slack) <= SP - 16 \/ SP <= S)%Z.
  Hypothesis SEP_DF : (D + len + 1 <= lo \/ SP <= D)%Z.

  Notation POST := (strcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str lo m).
  (* [comment removed for export] *)
  Notation ST pc mm x10 x11 x12 x13 x14 x15 :=
    (MS (mkR (Z_to_bv 64 0x52b744) (Z_to_bv 64 (SP + -16)) gp tp t0 t1 t2 a0 s1 x10 x11 x12 x13 x14 x15 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom ctasegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)

  Definition INV (mX : word -> option byte) (bs : list byte) (P : Z) : Prop :=
    bytes_at ctasegs mX S full /\ u8arr ctasegs mX D bs /\ length bs = (length str + 1)%nat /\
    firstn (Z.to_nat P) bs = firstn (Z.to_nat P) full /\
    mem_inv ctasegs mX /\ munch W m mX /\ wmono ctasegs m mX /\
    rw_cells ctasegs mX (SP + -16) [C8 s0; C8 ra] /\ stk ctasegs mX lo (SP + -16).

  Ltac open_inv H := destruct H as (SRC & DST & LBS & PFX & MI & MU & WM & FR & ST).
  (* [comment removed for export] *)
  Ltac sret := zstep; change (ret_pc (Z_to_bv 64 5420868)) with (Z_to_bv 64 5420868).

  Lemma full_length : length full = (length str + Datatypes.S (length slack))%nat.
  Proof. rewrite length_app. cbn. lia. Qed.

  Lemma S_bound : (0 <= S /\ S + len + 1 + Z.of_nat (length slack) <= 2^64)%Z.
  Proof. pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B. lia. Qed.

  Lemma D_bound : (0 <= D /\ D + len + 1 <= 2^64)%Z.
  Proof. pose proof (rw_cells_bound _ _ _ _ DST0) as B. cbn [cells_size csize Nat.add] in B. lia. Qed.

  Lemma full_nth_lt : forall i, (0 <= i < len)%Z -> exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  Lemma full_nth_le : forall i, (0 <= i <= len)%Z -> exists b, nth_error full (Z.to_nat i) = Some b /\ (bv_unsigned b = 0%Z <-> i = len).
  Proof.
    intros i Hi. destruct (Z.eq_dec i len) as [->|NE].
    - exists (Z_to_bv 8 0). split; [apply full_nth_len|]. split; intros; [reflexivity|reflexivity].
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb). exists b. split; [exact Hn|]. split; intros; [contradiction|lia].
  Qed.

  (* [comment removed for export] *)
  Lemma cp_store_ok : forall mX bs P (k : nat) a,
    INV mX bs P -> (0 <= P)%Z -> (P + Z.of_nat k <= len + 1)%Z -> a = wa (D + P) -> store_ok ctasegs mX a k = true.
  Proof.
    intros mX bs P k a I HP Hk Ha; open_inv I.
    eapply (u8arr_store_ok_n mX D bs P k a DST); [lia| rewrite LBS; lia | exact Ha].
  Qed.

  Lemma cp_store : forall mX bs P xs a,
    INV mX bs P -> (0 <= P)%Z -> (P + Z.of_nat (length xs) <= len + 1)%Z ->
    (Z.to_nat P + length xs <= length full)%nat ->
    firstn (length xs) (skipn (Z.to_nat P) full) = xs -> a = wa (D + P) ->
    INV (write_to_mem mX a xs) (upd_bytes bs (Z.to_nat P) xs) (P + Z.of_nat (length xs)).
  Proof.
    intros mX bs P xs a I HP Hk Hkb Hxs Ha. pose proof I as I'. open_inv I. pose proof S_bound as SB. pose proof D_bound as DB.
    pose proof (cp_store_ok mX bs P (length xs) a I' HP Hk Ha) as SOK. subst a.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    - apply bytes_at_write_other; [exact SRC| lia| lia| rewrite full_length; lia].
    - apply (u8arr_write_bytes mX D bs P xs DST); [lia|]. rewrite LBS. lia.
    - rewrite upd_bytes_length; [exact LBS|]. rewrite LBS. lia.
    - replace (Z.to_nat (P + Z.of_nat (length xs))) with (Z.to_nat P + length xs)%nat by lia.
      apply upd_bytes_prefix; [exact PFX| exact Hxs| rewrite LBS; lia| lia].
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU| lia| lia|]. cbn [inside]. left. lia.
    - apply wmono_write. exact WM.
    - apply rw_cells_frame; [exact FR| lia| lia|]. cbn [cells_size csize Nat.add]. lia.
    - apply stk_write; [exact ST| lia| lia].
  Qed.

  Lemma INV_weaken : forall mX bs P Q, INV mX bs P -> (0 <= Q <= P)%Z -> INV mX bs Q.
  Proof.
    intros mX bs P Q I HQ; open_inv I. repeat (split; [assumption|]).
    split; [|split; [assumption|]; repeat (split; [assumption|]); assumption].
    replace (Z.to_nat Q) with (Nat.min (Z.to_nat Q) (Z.to_nat P)) by lia. rewrite <- !firstn_firstn, PFX. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac rd1 I i b Hn :=
    lazymatch type of I with INV ?mX _ _ =>
      let RD := fresh "RD" in
      pose proof (u8ro_read ctasegs mX S full i b _ (proj1 I) Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      zstep; try clear RD
    end.

  (* [comment removed for export] *)
  Ltac st1 I i b Hn AD :=
    lazymatch type of I with INV ?mX ?bs _ =>
      let SOK := fresh "SOK" in
      pose proof (cp_store_ok mX bs i 1 AD I ltac:(lia) ltac:(lia) ltac:(unfold wa; first [f_equal; lia | rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned])) as SOK;
      zstep; clear SOK; cbv beta;
      try change (Z_to_bv 64 (bv_unsigned b)) with (zxb b); rewrite ?(le1_zxb b); try change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0];
      let I2 := fresh "I" in
      pose proof (cp_store mX bs i [b] AD I ltac:(lia) ltac:(cbn [length]; lia)
                    ltac:(pose proof (nth_error_lt _ _ _ Hn); cbn [length]; lia)
                    ltac:(apply nth_error_first1; exact Hn) ltac:(unfold wa; first [f_equal; lia | rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned])) as I2;
      cbn [length] in I2; change (Z.of_nat 1) with 1%Z in I2;
      let m2 := fresh "m" in let bs2 := fresh "bs" in
      remember (write_to_mem mX AD [b]) as m2 eqn:Em; clear Em;
      remember (upd_bytes bs (Z.to_nat i) [b]) as bs2 eqn:Ebs; clear Ebs;
      clear I; try clear mX; try clear bs; rename I2 into I
    end.

  (* [comment removed for export] *)
  Lemma sc_ret : forall mX bs x10 x11 x12 x13 x14 x15,
    INV mX bs (len + 1) ->
    evt ctasegs POST (ST 0x52b744 mX x10 x11 x12 x13 x14 x15).
  Proof.
    intros mX bs x10 x11 x12 x13 x14 x15 I. open_inv I. pose proof D_bound as DB.
    zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold strcpy_post.
    do 14 eexists. exists mX. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    assert (EBS : bs = str ++ [Z_to_bv 8 0]).
    { rewrite <- (firstn_all2 bs (n := Z.to_nat (len + 1))) by (rewrite LBS; lia). rewrite PFX.
      replace (Z.to_nat (len + 1)) with (length str + 1)%nat by lia. rewrite firstn_app, firstn_all2 by lia.
      replace (length str + 1 - length str)%nat with 1%nat by lia. reflexivity. }
    rewrite <- EBS, <- LBS. apply rw_cells_of_u8arr. exact DST.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_tail : forall (k : nat) (i : Z) mX bs x11 x13 x14 x15,
    Z.to_nat (len - i) = k -> (1 <= i <= len)%Z -> INV mX bs i ->
    evt ctasegs POST (ST 0x52b7f4 mX (Z_to_bv 64 (D + i - 1)) x11 (Z_to_bv 64 (S + i)) x13 x14 x15).
  Proof.
    induction k as [|k IH]; intros i mX bs x11 x13 x14 x15 Hk Hi I; pose proof S_bound as SB; pose proof D_bound as DB.
    - assert (Ei : i = len) by lia. subst i.
      rd1 I (Z.of_nat (length str)) (Z_to_bv 8 0) full_nth_len. zstep.
      st1 I (Z.of_nat (length str)) (Z_to_bv 8 0) full_nth_len (Z_to_bv 64 (D + Z.of_nat (length str) - 1 + 1)).
      zstep. zstep. zstep. if_false. zstep. sret.
      eapply sc_ret. exact I.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb).
      rd1 I i b Hn. zstep.
      st1 I i b Hn (Z_to_bv 64 (D + i - 1 + 1)).
      zstep. zstep. zstep. if_cases K; zify_cond K; [|exfalso; exact (Hb K)].
      replace (D + i - 1 + 1)%Z with (D + (i + 1) - 1)%Z by lia. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [lia|lia|exact I].
  Qed.

  Lemma low_byte_of_word : forall (chunk : list byte) b, length chunk = 8%nat -> nth_error chunk 0 = Some b ->
    Z.land (bv_unsigned (bv_extract 0 64 (le_bytes_to_word chunk))) 255 = bv_unsigned b.
  Proof.
    intros chunk b CL H0. rewrite (load8_le_val chunk CL). destruct chunk as [|c0 cr]; [discriminate|]. injection H0 as ->. cbn [map le_val].
    pose proof (le_val_range _ (bytes_ok_map cr)) as R. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb.
    change (2 ^ Z.of_N 8)%Z with 256%Z in Rb.
    change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8)%Z with 256%Z.
    rewrite (Z.mul_comm 256), Z_mod_plus_full. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_last : forall (j : Z) mX bs (chunk : list byte) x13 x14 x15,
    (0 <= j <= len)%Z -> INV mX bs j -> length chunk = 8%nat -> chunk = firstn 8 (skipn (Z.to_nat j) full) ->
    evt ctasegs POST (ST 0x52b7e4 mX (Z_to_bv 64 (D + j)) (Z_to_bv 64 (S + j)) (bv_extract 0 64 (le_bytes_to_word chunk)) x13 x14 x15).
  Proof.
    intros j mX bs chunk x13 x14 x15 Hj I CL Hch; pose proof S_bound as SB; pose proof D_bound as DB.
    destruct (full_nth_le j Hj) as (b & Hn & Hb0).
    assert (HC0 : nth_error chunk 0 = Some b). { rewrite Hch, nth_error_firstn. cbn [Nat.ltb Nat.leb]. rewrite nth_error_skipn, Nat.add_0_r. exact Hn. }
    zstep. rewrite (low_byte_of_word chunk b CL HC0). change (Z_to_bv 64 (bv_unsigned b)) with (zxb b).
    st1 I j b Hn (Z_to_bv 64 (D + j)).
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (Ej : j = len) by (apply Hb0; exact K). subst j. sret. eapply sc_ret. exact I.
    - assert (Hjl : (j < len)%Z) by (destruct (Z.eq_dec j len) as [E|NE]; [exfalso; apply K; apply Hb0; exact E|lia]).
      zstep. replace (S + j + 1)%Z with (S + (j + 1))%Z by lia. replace (D + j)%Z with (D + (j + 1) - 1)%Z by lia.
      eapply (sc_tail (Z.to_nat (len - (j + 1))) (j + 1)%Z); [lia|lia|exact I].
  Qed.

  Lemma readable8 : forall j, (0 <= j <= len)%Z -> ((S + j) mod 8 = 0)%Z -> (Z.to_nat j + 8 <= length full)%nat.
  Proof. intros j Hj Hal. rewrite full_length. pose proof PAD. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma sc_words : forall (k : nat) (j : Z) mX bs (chunk : list byte) x15,
    Z.to_nat (len - j) = k -> (0 <= j <= len)%Z -> ((S + j) mod 8 = 0)%Z -> INV mX bs j ->
    length chunk = 8%nat -> chunk = firstn 8 (skipn (Z.to_nat j) full) -> ~ In (Z_to_bv 8 0) chunk ->
    evt ctasegs POST (ST 0x52b7c4 mX (Z_to_bv 64 (D + j)) (Z_to_bv 64 (S + j)) (bv_extract 0 64 (le_bytes_to_word chunk))
                         (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) x15).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros j mX bs chunk x15 Hk Hj Hal I CL Hch Hnz; pose proof S_bound as SB; pose proof D_bound as DB.
    (* [comment removed for export] *)
    assert (Hj8 : (j + 8 <= len)%Z).
    { destruct (Z.lt_ge_cases len (j + 8)); [|assumption]. exfalso. apply Hnz. rewrite Hch.
      apply nth_error_In with (n := (Z.to_nat len - Z.to_nat j)%nat).
      rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
    (* [comment removed for export] *)
    pose proof (cp_store_ok mX bs j 8 (Z_to_bv 64 (D + j)) I ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep. clear SOK. rewrite (le8_ld chunk CL).
    pose proof (cp_store mX bs j chunk (Z_to_bv 64 (D + j)) I ltac:(lia) ltac:(rewrite CL; lia)
                  ltac:(rewrite CL, full_length; lia) ltac:(rewrite CL, Hch; reflexivity) ltac:(unfold wa; f_equal; lia)) as I2.
    rewrite CL in I2. change (Z.of_nat 8) with 8%Z in I2.
    remember (write_to_mem mX (Z_to_bv 64 (D + j)) chunk) as m2 eqn:Em; clear Em.
    remember (upd_bytes bs (Z.to_nat j) chunk) as bs2 eqn:Ebs; clear Ebs. clear I.
    (* [comment removed for export] *)
    pose proof (readable8 (j + 8) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as HW.
    pose proof (bytes_at_read ctasegs m2 S full (j + 8) 8 (proj1 I2) ltac:(lia) HW) as RD.
    set (chunk2 := firstn 8 (skipn (Z.to_nat (j + 8)) full)) in RD.
    assert (CL2 : length chunk2 = 8%nat). { subst chunk2. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk2)) as WR. rewrite length_map, CL2 in WR. change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    replace (S + j + 8)%Z with (S + (j + 8))%Z by lia. zstep. clear RD.
    do 5 zstep. rewrite (load8_le_val chunk2 CL2).
    replace (S + j + 8)%Z with (S + (j + 8))%Z by lia. replace (D + j + 8)%Z with (D + (j + 8))%Z by lia.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply (haszero64_clang _ (bytes_ok_map chunk2) ltac:(rewrite length_map; exact CL2)) in K. rewrite In0_map_unsigned in K.
      rewrite <- (load8_le_val chunk2 CL2) || idtac.
      eapply (IH (Z.to_nat (len - (j + 8))) ltac:(lia) (j + 8)%Z m2 bs2 chunk2); [lia|lia|Z.div_mod_to_equations; lia|exact I2|exact CL2|reflexivity|exact K].
    - (* [comment removed for export] *)
      rewrite <- (load8_le_val chunk2 CL2) || idtac.
      eapply (sc_last (j + 8)%Z m2 bs2 chunk2); [lia|exact I2|exact CL2|reflexivity].
  Qed.
  (* [comment removed for export] *)
  Lemma sc_wentry : forall (j : Z) mX bs x12 x13 x14 x15,
    (0 <= j <= len)%Z -> ((S + j) mod 8 = 0)%Z -> INV mX bs j ->
    evt ctasegs POST (ST 0x52b7a0 mX (Z_to_bv 64 (D + j)) (Z_to_bv 64 (S + j)) x12 x13 x14 x15).
  Proof.
    intros j mX bs x12 x13 x14 x15 Hj Hal I; pose proof S_bound as SB; pose proof D_bound as DB. pose proof I as I'. open_inv I'.
    pose proof (readable8 j Hj Hal) as HW.
    pose proof (bytes_at_read ctasegs mX S full j 8 SRC ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat j) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR. change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    zstep. zstep. zstep. clear RD. zstep. zstep. zstep. zstep. zstep.
    rewrite (load8_le_val chunk CL).
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite <- (load8_le_val chunk CL) || idtac.
      eapply (sc_last j mX bs chunk); [lia|exact I|exact CL|reflexivity].
    - apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K. rewrite In0_map_unsigned in K.
      rewrite <- (load8_le_val chunk CL) || idtac.
      eapply (sc_words (Z.to_nat (len - j)) j mX bs chunk); [lia|lia|exact Hal|exact I|exact CL|reflexivity|exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma sc_head : forall (k : nat) (i : Z) mX bs x13 x14 x15,
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z -> INV mX bs i ->
    evt ctasegs POST (ST 0x52b780 mX (Z_to_bv 64 (D + i)) (Z_to_bv 64 (S + i)) (Z_to_bv 64 (S + i + 1)) x13 x14 x15).
  Proof.
    induction k as [|k IH]; intros i mX bs x13 x14 x15 Hk Hi I; pose proof S_bound as SB; pose proof D_bound as DB.
    - assert (Ei : i = len) by lia. subst i.
      rd1 I (Z.of_nat (length str)) (Z_to_bv 8 0) full_nth_len.
      st1 I (Z.of_nat (length str)) (Z_to_bv 8 0) full_nth_len (Z_to_bv 64 (D + Z.of_nat (length str))).
      zstep. if_true. sret. eapply sc_ret. exact I.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb).
      rd1 I i b Hn.
      st1 I i b Hn (Z_to_bv 64 (D + i)).
      zstep. if_cases K; zify_cond K; [exfalso; exact (Hb K)|].
      do 5 zstep. if_cases Kal; zify_cond Kal.
      + replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (S + i + 2)%Z with (S + (i + 1) + 1)%Z by lia.
        replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
        eapply (IH (i + 1)%Z); [lia|lia|exact I].
      + replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
        eapply (sc_wentry (i + 1)%Z); [lia| |exact I].
        revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_entry : forall mX bs x12 x13 x14 x15,
    INV mX bs 0 ->
    evt ctasegs POST (ST 0x52b758 mX a0 a1 x12 x13 x14 x15).
  Proof.
    intros mX bs x12 x13 x14 x15 I; pose proof S_bound as SB; pose proof D_bound as DB.
    zstep. zstep. zstep. if_cases Kx; zify_cond Kx.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases Kal; zify_cond Kal.
      + eapply evt_eq; [|eapply (sc_wentry 0 mX bs); [lia| |exact I]].
        * rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
        * rewrite Z.add_0_r. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
      + zstep. eapply evt_eq; [|eapply (sc_head (Z.to_nat len) 0 mX bs); [lia|lia|exact I]].
        rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
    - (* [comment removed for export] *)
      destruct (full_nth_le 0 ltac:(lia)) as (b & Hn & Hb0).
      pose proof (u8ro_read ctasegs mX S full 0 b a1 (proj1 I) Hn ltac:(lia) ltac:(unfold wa; rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD.
      zstep. clear RD.
      st1 I 0%Z b Hn a0.
      zstep. if_cases K; zify_cond K.
      + assert (Hl : (0 < len)%Z) by (destruct (Z.eq_dec 0 len) as [E|NE]; [exfalso; apply K; apply Hb0; exact E|lia]).
        zstep. eapply evt_eq; [|eapply (sc_tail (Z.to_nat (len - 1)) 1); [lia|lia|exact I]].
        replace (D + 1 - 1)%Z with D by lia. rewrite !Z_to_bv_bv_unsigned. reflexivity.
      + assert (El : len = 0%Z) by (symmetry; apply Hb0; exact K).
        zstep. sret. eapply sc_ret. rewrite El. exact I.
  Qed.
End Proofs.

(* [comment removed for export] *)
Theorem strcpy_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack junk : list byte) (lo : Z),
  mem_inv ctasegs m ->
  bytes_at ctasegs m (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a1 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  rw_cells ctasegs m (bv_unsigned a0) [CB (length str + 1)%nat junk] ->
  stk ctasegs m lo (bv_unsigned sp) -> (0 <= lo)%Z -> (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length str) + 1 <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt ctasegs (strcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 strcpy_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros MI STR NONUL PAD DST ST Hlo LO SEP_SD SEP_SF SEP_DF. unfold strcpy_entry.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1); (bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  pose proof (conj STR DST) as ORIG.
  carve_frame 16%nat ST. do 5 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  eapply (sc_entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack junk lo
            (proj1 ORIG) NONUL PAD (proj2 ORIG) ltac:(lia) SEP_SD SEP_SF SEP_DF m1 junk).
  (* [comment removed for export] *)
  split; [eassumption|]. split; [eapply u8arr_of_rw_cells; exact DST|].
  split; [destruct DST as [[Hwf _] _]; cbn in Hwf; destruct Hwf as [Hn _]; exact Hn|]. split; [reflexivity|].
  split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [exact FR|exact ST].
Qed.
