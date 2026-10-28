(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac Arr Bytes.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition stpcpy_post (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1' a2' a3' a4' a5' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat (length str)))
                 a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (S (length str)) (str ++ [Z_to_bv 8 0])]
    /\ bytes_at asegs m' (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1)]%Z.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (S + len + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis AB : (0 <= S /\ S + Z.of_nat (length full) <= 2^64 /\ 0 <= D /\ D + len + 1 <= 2^64)%Z.
  Hypothesis SEP : (S + Z.of_nat (length full) <= D \/ D + len + 1 <= S)%Z.

  Notation POST := (stpcpy_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc a0 a1 str slack m).
  (* [comment removed for export] *)
  Notation ST pc mm x10 x11 x12 x13 x14 x15 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)

  Lemma full_length : length full = (length str + Datatypes.S (length slack))%nat.
  Proof. rewrite length_app. cbn. lia. Qed.

  Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition INV (mX : word -> option byte) (bs : list byte) (P : Z) : Prop :=
    bytes_at asegs mX S full /\ u8arr asegs mX D bs /\ length bs = Datatypes.S (length str) /\
    firstn (Z.to_nat P) bs = firstn (Z.to_nat P) full /\
    mem_inv asegs mX /\ munch W m mX /\ wmono asegs m mX.

  Ltac open_inv H := destruct H as (SRC & DST & LBS & PFX & MI & MU & WM).

  Lemma cp_store_ok : forall mX bs P (k : nat) a,
    INV mX bs P -> (0 <= P)%Z -> (P + Z.of_nat k <= len + 1)%Z -> a = wa (D + P) -> store_ok asegs mX a k = true.
  Proof.
    intros mX bs P k a I HP Hk Ha; open_inv I.
    eapply (u8arr_store_ok_n asegs mX D bs P k a DST); [lia| rewrite LBS; lia | exact Ha].
  Qed.

  Lemma cp_store : forall mX bs P xs a,
    INV mX bs P -> (0 <= P)%Z -> (P + Z.of_nat (length xs) <= len + 1)%Z ->
    firstn (length xs) (skipn (Z.to_nat P) full) = xs -> a = wa (D + P) ->
    INV (write_to_mem mX a xs) (upd_bytes bs (Z.to_nat P) xs) (P + Z.of_nat (length xs)).
  Proof.
    intros mX bs P xs a I HP Hk Hxs Ha. pose proof I as I'. open_inv I.
    pose proof (cp_store_ok mX bs P (length xs) a I' HP Hk Ha) as SOK. subst a.
    pose proof full_length as FL.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - apply bytes_at_write_other; [exact SRC| lia| lia| lia].
    - apply (u8arr_write_bytes asegs mX D bs P xs DST); [lia|]. rewrite LBS. lia.
    - rewrite upd_bytes_length; [exact LBS|]. rewrite LBS. lia.
    - replace (Z.to_nat (P + Z.of_nat (length xs))) with (Z.to_nat P + length xs)%nat by lia.
      apply upd_bytes_prefix; [exact PFX| exact Hxs| rewrite LBS; lia| lia].
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU| lia| lia|]. cbn [inside]. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma sp_done : forall mX bs x11 x12 x13 x14 x15,
    INV mX bs (len + 1) ->
    POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (D + len)) x11 x12 x13 x14 x15 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None mX (seg_rom asegs)).
  Proof.
    intros mX bs x11 x12 x13 x14 x15 I; open_inv I.
    exists x11, x12, x13, x14, x15, mX.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [|exact SRC].
    apply rw_cells_of_u8arr in DST. rewrite LBS in DST.
    replace (str ++ [Z_to_bv 8 0]) with bs; [exact DST|].
    replace (Z.to_nat (len + 1)) with (length bs) in PFX by lia.
    rewrite firstn_all in PFX. rewrite PFX, LBS.
    replace (Datatypes.S (length str)) with (length str + 1)%nat by lia.
    rewrite firstn_app. rewrite (firstn_all2 str) by lia. replace (length str + 1 - length str)%nat with 1%nat by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac rd1 I i b Hn :=
    lazymatch type of I with INV ?mX _ _ =>
      let RD := fresh "RD" in
      pose proof (u8ro_read asegs mX S full i b _ (proj1 I) Hn ltac:(lia) eq_refl) as RD;
      zstep; try clear RD
    end.

  (* [comment removed for export] *)
  Ltac st1 I P ADDR b Hn :=
    lazymatch type of I with INV ?mX ?bs _ =>
      let SOK := fresh "SOK" in
      pose proof (cp_store_ok mX bs P 1 (Z_to_bv 64 ADDR) I ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
      zstep; clear SOK;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bytes) _) =>
        replace bytes with [b] by first [reflexivity | symmetry; apply le1_zxb] end;
      let I2 := fresh "I" in
      pose proof (cp_store mX bs P [b] (Z_to_bv 64 ADDR) I ltac:(lia) ltac:(cbn [length]; lia)
                    ltac:(apply nth_error_first1; exact Hn) ltac:(unfold wa; f_equal; lia)) as I2;
      cbn [length] in I2; change (Z.of_nat 1) with 1%Z in I2;
      let m2 := fresh "m" in let bs2 := fresh "bs" in
      remember (write_to_mem mX (Z_to_bv 64 ADDR) [b]) as m2 eqn:Em; clear Em;
      remember (upd_bytes bs (Z.to_nat P) [b]) as bs2 eqn:Ebs; clear Ebs;
      clear I; try clear mX; try clear bs; rename I2 into I
    end.

  (* [comment removed for export] *)
  Lemma sp_tail : forall (K : nat) mX bs j x11 x13 x14 x15,
    INV mX bs (j + 1) -> Z.to_nat (len - j) = K -> (0 <= j < len)%Z ->
    evt asegs POST (ST 0x526c28 mX (Z_to_bv 64 (D + j)) x11 (Z_to_bv 64 (S + (j + 1))) x13 x14 x15).
  Proof.
    induction K as [|K IH]; intros mX bs j x11 x13 x14 x15 I HK Hj; [lia|].
    pose proof full_length as FL.
    destruct (Z.eq_dec (j + 1) len) as [E|NE].
    - pose proof full_nth_len as Hn. rewrite <- E in Hn.
      rd1 I (j + 1)%Z (Z_to_bv 8 0) Hn.
      zstep.
      st1 I (j + 1)%Z (D + j + 1)%Z (Z_to_bv 8 0) Hn.
      do 3 zstep. if_false. do 2 zstep.
      apply evt_done. replace (D + j + 1)%Z with (D + len)%Z by lia.
      eapply sp_done. replace (len + 1)%Z with (j + 1 + 1)%Z by lia. exact I.
    - destruct (full_nth_lt (j + 1) ltac:(lia)) as (b & Hn & Hb).
      rd1 I (j + 1)%Z b Hn.
      zstep.
      st1 I (j + 1)%Z (D + j + 1)%Z b Hn.
      do 3 zstep. if_cases Kb; zify_cond Kb. 2:{ exfalso. exact (Hb Kb). }
      replace (S + (j + 1) + 1)%Z with (S + (j + 1 + 1))%Z by lia.
      replace (D + j + 1)%Z with (D + (j + 1))%Z by lia.
      eapply (IH _ _ (j + 1)%Z); [exact I| lia| lia].
  Qed.
  (* [comment removed for export] *)
  Lemma sp_bentry : forall mX bs i x12 x13 x14 x15,
    INV mX bs (i + 1) -> (0 <= i < len)%Z ->
    evt asegs POST (ST 0x526c24 mX (Z_to_bv 64 (D + i)) (Z_to_bv 64 (S + i)) x12 x13 x14 x15).
  Proof.
    intros mX bs i x12 x13 x14 x15 I Hi.
    zstep. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
    eapply (sp_tail (Z.to_nat (len - i)) _ _ i); [exact I| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma sp_ret : forall mX bs x11 x12 x13 x14 x15,
    INV mX bs (len + 1) ->
    evt asegs POST (ST 0x526c48 mX (Z_to_bv 64 (D + len)) x11 x12 x13 x14 x15).
  Proof. intros mX bs x11 x12 x13 x14 x15 I. zstep. apply evt_done. eapply sp_done. exact I. Qed.

  Lemma low_byte : forall (b : byte) (rest : list byte),
    Z.land (le_val (map bv_unsigned (b :: rest))) 255 = bv_unsigned b.
  Proof.
    intros b rest. cbn [map le_val].
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8)%Z with 256%Z.
    rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sp_wexit : forall mX bs i chunk x13 x14 x15,
    INV mX bs i -> (0 <= i <= len)%Z -> chunk = firstn 8 (skipn (Z.to_nat i) full) -> length chunk = 8%nat ->
    evt asegs POST (ST 0x526c18 mX (Z_to_bv 64 (D + i)) (Z_to_bv 64 (S + i)) (bv_extract 0 64 (le_bytes_to_word chunk)) x13 x14 x15).
  Proof.
    intros mX bs i chunk x13 x14 x15 I Hi EC CL. pose proof full_length as FL.
    destruct (skipn (Z.to_nat i) full) as [|b tl] eqn:ES; [subst chunk; cbn in CL; discriminate|].
    apply skipn_cons_nth in ES. destruct ES as [Hn _].
    zstep. rewrite (load8_le_val chunk CL). subst chunk. cbn [firstn]. rewrite low_byte.
    st1 I i (D + i)%Z b Hn.
    zstep. if_cases Kb; zify_cond Kb.
    - (* [comment removed for export] *)
      assert (E : i = len).
      { destruct (Z.eq_dec i len) as [|NE]; [assumption|]. exfalso.
        destruct (full_nth_lt i ltac:(lia)) as (b' & Hn' & Hb'). rewrite Hn in Hn'. injection Hn' as <-. exact (Hb' Kb). }
      subst i. eapply sp_ret. exact I.
    - assert (NE : i <> len).
      { intros ->. rewrite full_nth_len in Hn. injection Hn as <-. apply Kb. reflexivity. }
      eapply sp_bentry; [exact I | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma chunk_below : forall i chunk, (0 <= i <= len)%Z -> chunk = firstn 8 (skipn (Z.to_nat i) full) -> ~ In (Z_to_bv 8 0) chunk -> (i + 8 <= len)%Z.
  Proof.
    intros i chunk Hi EC K. pose proof full_length as FL.
    destruct (Z.lt_ge_cases len (i + 8)); [|assumption]. exfalso. apply K. subst chunk.
    apply nth_error_In with (n := (Z.to_nat len - Z.to_nat i)%nat).
    rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_skipn, <- full_nth_len. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma chunk_readable : forall i, (0 <= i <= len)%Z -> ((S + i) mod 8 = 0)%Z -> (Z.to_nat i + 8 <= length full)%nat.
  Proof. intros i Hi Hal. rewrite full_length. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma sp_words : forall (K : nat) mX bs i chunk x15,
    INV mX bs i -> Z.to_nat (len - i) = K -> (0 <= i <= len)%Z -> ((S + i) mod 8 = 0)%Z ->
    chunk = firstn 8 (skipn (Z.to_nat i) full) -> length chunk = 8%nat -> ~ In (Z_to_bv 8 0) chunk ->
    evt asegs POST (ST 0x526bf8 mX (Z_to_bv 64 (D + i)) (Z_to_bv 64 (S + i)) (bv_extract 0 64 (le_bytes_to_word chunk))
                       (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) x15).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros mX bs i chunk x15 I HK Hi Hal EC CL NZ.
    pose proof full_length as FL.
    pose proof (chunk_below i chunk Hi EC NZ) as Hi8.
    pose proof (cp_store_ok mX bs i 8 (Z_to_bv 64 (D + i)) I ltac:(lia) ltac:(lia) eq_refl) as SOK.
    zstep. clear SOK.
    rewrite (le8_ld chunk CL).
    pose proof (cp_store mX bs i chunk (Z_to_bv 64 (D + i)) I ltac:(lia) ltac:(rewrite CL; lia)
                  ltac:(rewrite CL; symmetry; exact EC) eq_refl) as I2.
    rewrite CL in I2. change (Z.of_nat 8) with 8%Z in I2.
    remember (write_to_mem mX (Z_to_bv 64 (D + i)) chunk) as m2 eqn:Em; clear Em.
    remember (upd_bytes bs (Z.to_nat i) chunk) as bs2 eqn:Ebs; clear Ebs.
    clear I.
    assert (Hal8 : ((S + (i + 8)) mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
    pose proof (chunk_readable (i + 8) ltac:(lia) Hal8) as HW.
    pose proof (bytes_at_read asegs m2 S full (i + 8) 8 (proj1 I2) ltac:(lia) HW) as RD.
    set (chunk2 := firstn 8 (skipn (Z.to_nat (i + 8)) full)) in RD.
    assert (CL2 : length chunk2 = 8%nat). { subst chunk2. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk2)) as WR. rewrite length_map, CL2 in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    replace (S + (i + 8))%Z with (S + i + 8)%Z in RD by lia.
    do 6 zstep. clear RD.
    zstep. rewrite (load8_le_val chunk2 CL2).
    replace (D + i + 8)%Z with (D + (i + 8))%Z by lia. replace (S + i + 8)%Z with (S + (i + 8))%Z by lia.
    if_cases Kz; zify_cond Kz.
    - apply (haszero64_clang _ (bytes_ok_map chunk2) ltac:(rewrite length_map; exact CL2)) in Kz.
      rewrite In0_map_unsigned in Kz.
      pose proof (chunk_below (i + 8) chunk2 ltac:(lia) eq_refl Kz) as Hi16.
      eapply (IH (Z.to_nat (len - (i + 8))) ltac:(lia) _ _ (i + 8)%Z chunk2); [exact I2| lia| lia| exact Hal8| reflexivity| exact CL2| exact Kz].
    - eapply (sp_wexit _ _ (i + 8)%Z chunk2); [exact I2| lia| reflexivity| exact CL2].
  Qed.

  (* [comment removed for export] *)
  Lemma sp_wentry : forall mX bs i x12 x13 x14 x15,
    INV mX bs i -> (0 <= i <= len)%Z -> ((S + i) mod 8 = 0)%Z ->
    evt asegs POST (ST 0x526bd4 mX (Z_to_bv 64 (D + i)) (Z_to_bv 64 (S + i)) x12 x13 x14 x15).
  Proof.
    intros mX bs i x12 x13 x14 x15 I Hi Hal. pose proof full_length as FL.
    pose proof I as Ic; open_inv Ic. (* [comment removed for export] *)
    pose proof (chunk_readable i Hi Hal) as HW.
    pose proof (bytes_at_read asegs mX S full i 8 SRC ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat i) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 8 zstep. clear RD.
    zstep. rewrite (load8_le_val chunk CL).
    if_cases Kz; zify_cond Kz.
    - eapply (sp_wexit _ _ i chunk); [exact I| lia| reflexivity| exact CL].
    - apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in Kz.
      rewrite In0_map_unsigned in Kz.
      eapply (sp_words (Z.to_nat (len - i)) _ _ i chunk); [exact I| reflexivity| lia| exact Hal| reflexivity| exact CL| exact Kz].
  Qed.

  (* [comment removed for export] *)
  Lemma sp_align : forall (K : nat) mX bs i x13 x14 x15,
    INV mX bs i -> Z.to_nat (len - i) = K -> (0 <= i <= len)%Z ->
    evt asegs POST (ST 0x526bb4 mX (Z_to_bv 64 (D + i)) (Z_to_bv 64 (S + i)) (Z_to_bv 64 (S + i + 1)) x13 x14 x15).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros mX bs i x13 x14 x15 I HK Hi. pose proof full_length as FL.
    destruct (Z.eq_dec i len) as [E|NE].
    - pose proof full_nth_len as Hn. rewrite <- E in Hn.
      rd1 I i (Z_to_bv 8 0) Hn.
      st1 I i (D + i)%Z (Z_to_bv 8 0) Hn.
      zstep. if_true.
      rewrite E in *. eapply sp_ret. exact I.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb).
      rd1 I i b Hn.
      st1 I i (D + i)%Z b Hn.
      zstep. if_cases Kb; zify_cond Kb. { exfalso. exact (Hb Kb). }
      do 5 zstep. if_cases Kal; zify_cond Kal.
      + replace (S + i + 2)%Z with (S + (i + 1) + 1)%Z by lia.
        replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
        eapply (IH (Z.to_nat (len - (i + 1))) ltac:(lia) _ _ (i + 1)%Z); [exact I| reflexivity| lia].
      + replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
        eapply (sp_wentry _ _ (i + 1)%Z); [exact I| lia|].
        revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
  Qed.
  (* [comment removed for export] *)
  Ltac st1_0 I b Hn :=
    lazymatch type of I with INV ?mX ?bs _ =>
      let SOK := fresh "SOK" in
      pose proof (cp_store_ok mX bs 0 1 a0 I ltac:(lia) ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as SOK;
      zstep; clear SOK;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bytes) _) =>
        replace bytes with [b] by first [reflexivity | symmetry; apply le1_zxb] end;
      let I2 := fresh "I" in
      pose proof (cp_store mX bs 0 [b] a0 I ltac:(lia) ltac:(cbn [length]; lia)
                    ltac:(apply nth_error_first1; exact Hn) ltac:(symmetry; apply Z_to_bv_plus0)) as I2;
      cbn [length] in I2; change (Z.of_nat 1) with 1%Z in I2;
      let m2 := fresh "m" in let bs2 := fresh "bs" in
      remember (write_to_mem mX a0 [b]) as m2 eqn:Em; clear Em;
      remember (upd_bytes bs (Z.to_nat 0) [b]) as bs2 eqn:Ebs; clear Ebs;
      clear I; rename I2 into I
    end.

  (* [comment removed for export] *)
  Lemma stpcpy_body : forall junk x12 x13 x14 x15,
    bytes_at asegs m S full -> rw_cells asegs m D [CB (Datatypes.S (length str)) junk] -> mem_inv asegs m ->
    evt asegs POST (ST 0x526b8c m a0 a1 x12 x13 x14 x15).
  Proof.
    intros junk x12 x13 x14 x15 SRC DST MI. pose proof full_length as FL.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (rw_cells_CB_length asegs _ _ _ _ DST) as LBS. apply u8arr_of_rw_cells in DST.
    assert (I : INV m junk 0).
    { split; [exact SRC|]. split; [exact DST|]. split; [exact LBS|]. split; [reflexivity|]. split; [exact MI|]. split; [exact MU| exact WM]. }
    clear SRC DST MI MU WM.
    do 3 zstep. if_cases Kx.
    - (* [comment removed for export] *)
      do 2 zstep. if_cases Kal; zify_cond Kal.
      + eapply evt_eq.
        2:{ eapply (sp_wentry _ _ 0 (Z_to_bv 64 (Z.land S 7)) x13 x14 x15); [exact I| lia|].
            revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
        unfold mkR. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
      + zstep.
        eapply evt_eq.
        2:{ eapply (sp_align (Z.to_nat len) _ _ 0 x13 x14 x15); [exact I| f_equal; lia| lia]. }
        unfold mkR. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec len 0) as [E0|N0].
      + pose proof full_nth_len as Hn. rewrite E0 in Hn.
        pose proof (u8ro_read asegs m S _ 0 _ a1 (proj1 I) Hn ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
        zstep. clear RD.
        st1_0 I (Z_to_bv 8 0) Hn.
        zstep. if_false. zstep.
        eapply evt_eq.
        2:{ eapply (sp_ret _ _ a1 (Z_to_bv 64 0) x13 x14 x15). rewrite E0. exact I. }
        unfold mkR. rewrite E0, !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
      + destruct (full_nth_lt 0 ltac:(lia)) as (b & Hn & Hb).
        pose proof (u8ro_read asegs m S _ 0 _ a1 (proj1 I) Hn ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
        zstep. clear RD.
        st1_0 I b Hn.
        zstep. if_cases Kb; zify_cond Kb. 2:{ exfalso. exact (Hb Kb). }
        eapply evt_eq.
        2:{ eapply (sp_bentry _ _ 0 (zxb b) x13 x14 x15); [exact I| lia]. }
        unfold mkR. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  Qed.
End Proofs.

Definition stpcpy_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack junk : list byte),
  bytes_at asegs m (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a1 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  rw_cells asegs m (bv_unsigned a0) [CB (S (length str)) junk] ->
  (bv_unsigned a1 + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= bv_unsigned a0
   \/ bv_unsigned a0 + Z.of_nat (length str) + 1 <= bv_unsigned a1)%Z ->
  mem_inv asegs m ->
  evt asegs (stpcpy_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc a0 a1 str slack m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x526b8c) fc None m (seg_rom asegs)).

Theorem stpcpy_proof : stpcpy_stmt.
Proof.
  unfold stpcpy_stmt. intros until junk. intros SRC NONUL PAD DST SEP MI.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  eapply stpcpy_body; try eassumption; rewrite length_app; cbn [length]; lia.
Qed.

(* [comment removed for export] *)
Definition strcpy_post (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1' a2' a3' a4' a5' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1); (bv_unsigned sp - 16, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (S (length str)) (str ++ [Z_to_bv 8 0])]
    /\ bytes_at asegs m' (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).

Definition strcpy_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack junk : list byte) (lo : Z),
  bytes_at asegs m (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a1 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  rw_cells asegs m (bv_unsigned a0) [CB (S (length str)) junk] ->
  (bv_unsigned a1 + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= bv_unsigned a0
   \/ bv_unsigned a0 + Z.of_nat (length str) + 1 <= bv_unsigned a1)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (0 <= lo)%Z -> (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a1 + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= lo \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  mem_inv asegs m ->
  evt asegs (strcpy_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc a0 a1 str slack lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x526b64) fc None m (seg_rom asegs)).

Theorem strcpy_proof : strcpy_stmt.
Proof.
  unfold strcpy_stmt. intros until lo. intros SRC NONUL PAD DST SEP ST LO0 LO SEPS SEPD MI.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat (length str) + 1); (bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16%nat junk0 [] [8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 5 step.
  call (stpcpy_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str slack junk).
  1-6: first [eassumption | lia].
  cbv delta [mkR].
  do 5 step.
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.
