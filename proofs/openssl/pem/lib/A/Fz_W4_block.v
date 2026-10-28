(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac Arr SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_W4_kit Fz_W4_defs Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition dblock_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C T : Z) (K : nat) (n0 : Z) (num ln : word) (ed : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (dl : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (bs' : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dl) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (T, T + 3 * (n0 / 4))] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ (dl = -1 \/ 0 <= dl <= 3 * (n0 / 4))
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ ro_cells asegs m' C (ectx_cells num ed ln (Z_to_bv 64 0))
    /\ rw_cells asegs m' T [CB K bs'].

Section Proofs.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (C T : Z) (K : nat) (n0 : Z) (num ln : word) (ed : list byte) (lo : Z).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 64, bv_unsigned sp); (T, T + 3 * (n0 / 4))]%Z.
  Hypothesis AB : 0 <= n0 <= 80 /\ 3 * (n0 / 4) <= Z.of_nat K /\ 0 < C /\ C + 92 <= lo /\ 0 < T /\ T + Z.of_nat K <= lo
                  /\ 0x10007fff8000 <= lo /\ lo <= SP - 64 /\ SP <= 2 ^ 47.
  Hypothesis SEP_CT : C + 92 <= T \/ T + Z.of_nat K <= C.
  Hypothesis TIM : T + Z.of_nat K <= 0x10000 \/ 0xbc6000 <= T.
  Hypothesis TSH : T + Z.of_nat K <= 0x7fff8000 \/ 0x10007fff8000 <= T.
  Hypothesis LED : length ed = 80%nat.
  Hypothesis CAL : C mod 8 = 0.
  (* [comment removed for export] *)
  Hypothesis ACC_C : acc asegs m C 92.
  Hypothesis ACC_T : acc asegs m T (Z.of_nat K).
  Hypothesis ACC_B : acc asegs m 672160 128.

  Lemma HWS : sh_fp W.
  Proof. clear LED CAL ACC_C ACC_T ACC_B SEP_CT TIM. sh_fp_lia. Qed.
  Lemma TAL : 672160 mod 8 = 0.
  Proof. reflexivity. Qed.

  Notation POST := (dblock_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C T K n0 num ln ed lo m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation SHBv := (Z_to_bv 64 2147450880).
  Notation TBL := (Z_to_bv 64 672160).

  (* [comment removed for export] *)
  Definition INV (mX : mem) : Prop :=
    ro_cells asegs mX C (ectx_cells num ed ln (Z_to_bv 64 0)) /\ bytes_at asegs mX (C + 4) ed
    /\ (exists bs, u8arr asegs mX T bs /\ length bs = K)
    /\ rw_cells asegs mX (SP + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ stk asegs mX lo (SP + -40)
    /\ mem_inv asegs mX /\ munch W m mX /\ wmono asegs m mX.

  Ltac open_inv H := destruct H as (CTX & FB & (bs & DST & LBS) & FR & ST & MI & MU & WM).

  Lemma inv_store_ok : forall mX k a, INV mX -> 0 <= k < 3 * (n0 / 4) -> a = wa (T + k) -> store_ok asegs mX a 1 = true.
  Proof.
    intros mX k a I Hk Ha; open_inv I.
    eapply (u8arr_store_ok_n asegs mX T bs k 1 a DST); [lia | rewrite LBS; lia | exact Ha].
  Qed.

  Lemma inv_store : forall mX k a b, INV mX -> 0 <= k < 3 * (n0 / 4) -> a = wa (T + k) -> INV (write_to_mem mX a [b]).
  Proof.
    intros mX k a b I Hk Ha. pose proof (inv_store_ok mX k a I Hk Ha) as SOK. open_inv I. subst a.
    assert (HED : 0 <= C + 4 /\ C + 4 + Z.of_nat (length ed) <= 2 ^ 64) by (rewrite LED; lia).
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - apply ro_cells_frame; [exact CTX | lia | cbn [length]; lia | cbn [length cells_size ectx_cells csize Nat.add]; lia].
    - apply bytes_at_write_other; [exact FB | lia | cbn [length]; lia | cbn [length]; rewrite LED; lia].
    - exists (upd_bytes bs (Z.to_nat k) [b]). split.
      + apply (u8arr_write_bytes asegs mX T bs k [b] DST); [lia | cbn [length]; rewrite LBS; lia].
      + rewrite upd_bytes_length; [exact LBS | cbn [length]; rewrite LBS; lia].
    - apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [length cells_size csize Nat.add]; lia].
    - apply stk_write; [exact ST | lia | cbn [length]; lia].
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU | lia | cbn [length]; lia |]. cbn [inside length]. right. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma db_ret : forall mX dl x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV mX -> (dl = -1 \/ 0 <= dl <= 3 * (n0 / 4)) ->
    evt asegs POST (ST 0x31fe68 mX x5 x6 x7 x9 (Z_to_bv 64 dl) x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31).
  Proof.
    intros mX dl x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 I Hdl; open_inv I.
    do 5 zstep.
    release_frame FR ST (bv_unsigned sp). zstep.
    apply rw_cells_of_u8arr in DST. rewrite LBS in DST.
    zstep. apply evt_done. exists dl. do 14 eexists. exists bs. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact Hdl|]. split; [exact ST|]. split; [exact CTX | exact DST].
  Qed.

  (* [comment removed for export] *)
  Lemma db_fin : forall mX q e x5 x6 x7 x9 x10 x11 x12 x13 x15 x18 x19 x28 x29 x30 x31,
    INV mX -> 0 <= q -> q + 1 <= n0 / 4 -> 0 <= e <= 2 ->
    evt asegs POST (ST 0x31fe64 mX x5 x6 x7 x9 x10 x11 x12 x13 (Z_to_bv 64 e) x15 SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 x28 x29 x30 x31).
  Proof.
    intros mX q e x5 x6 x7 x9 x10 x11 x12 x13 x15 x18 x19 x28 x29 x30 x31 I Hq HQ He.
    assert (HD : n0 / 4 <= 20) by (apply Z.div_le_upper_bound; lia).
    zstep.
    rewrite (ubs_sw32 (3 * q + 3 - e)) by lia.
    eapply db_ret; [exact I | right; lia].
  Qed.

  (* [comment removed for export] *)
  Ltac stb I k ADDR :=
    lazymatch type of I with INV ?mX =>
      let SOK := fresh "SOK" in
      pose proof (inv_store_ok mX k (Z_to_bv 64 ADDR) I ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
      zstep; clear SOK;
      rewrite t_le1_word;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?b]) _) =>
        let I2 := fresh "I" in
        pose proof (inv_store mX k (Z_to_bv 64 ADDR) b I ltac:(lia) ltac:(unfold wa; f_equal; lia)) as I2;
        let m2 := fresh "m" in
        remember (write_to_mem mX (Z_to_bv 64 ADDR) [b]) as m2 eqn:Em; clear Em;
        clear I; try clear mX; rename I2 into I
      end
    end.
  (* [comment removed for export] *)
  Ltac chk_stb I k ADDR fast r1 r2 :=
    lazymatch type of I with INV ?mX =>
      let MUx := fresh "MU" in pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 I))))))) as MUx;
      chk_pass ACC_T ADDR 1 fast r1 r2; clear MUx
    end.


  (* [comment removed for export] *)
  Lemma db_last_sw : forall mX q e x5 x6 x7 x9 x10 x12 x13 x15 x18 x19 x28 x29 x30 x31,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> 0 <= e <= 2 ->
    evt asegs POST (ST 0x31fdc4 mX x5 x6 x7 x9 x10 (Z_to_bv 64 (T + 3 * q)) x12 x13 (Z_to_bv 64 e) x15 SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 x28 x29 x30 x31).
  Proof.
    intros mX q e x5 x6 x7 x9 x10 x12 x13 x15 x18 x19 x28 x29 x30 x31 I Hq Hn He.
    pose proof HWS as HWS.
    assert (HQ : q + 1 <= n0 / 4) by (apply Z.div_le_lower_bound; lia).
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      chk_stb I (3 * q) (T + 3 * q) 0x31fe14 5 10.
      zstep. stb I (3 * q) (T + 3 * q).
      chk_stb I (3 * q + 1) (T + 3 * q + 1) 0x31fe2c 5 13.
      zstep. zstep. stb I (3 * q + 1) (T + 3 * q + 1).
      chk_stb I (3 * q + 2) (T + 3 * q + 2) 0x31fe48 12 10.
      stb I (3 * q + 2) (T + 3 * q + 2).
      zstep. eapply db_fin; [exact I | lia | lia | lia].
    - zstep. zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        chk_stb I (3 * q) (T + 3 * q) 0x31fe60 12 10.
        stb I (3 * q) (T + 3 * q).
        eapply db_fin; [exact I | lia | lia | lia].
      + (* [comment removed for export] *)
        chk_stb I (3 * q) (T + 3 * q) 0x31fde0 15 10.
        zstep. stb I (3 * q) (T + 3 * q).
        chk_stb I (3 * q + 1) (T + 3 * q + 1) 0x31fdf8 13 11.
        zstep. stb I (3 * q + 1) (T + 3 * q + 1).
        zstep. eapply db_fin; [exact I | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Ltac prep I :=
    pose proof HWS as HWS'; pose proof TAL as TAL';
    let I' := fresh "Ic" in pose proof I as I'; open_inv I'.

  (* [comment removed for export] *)
  Lemma db_last_tail : forall mX q eofv zA zB zC zD x5 x7 x9 x18 x19 x28 x29 x30 x31,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 ->
    0 <= zA <= 255 -> 0 <= zB <= 255 -> 0 <= zC <= 255 -> 0 <= zD <= 255 ->
    evt asegs POST (ST 0x31fd78 mX x5 (Z_to_bv 64 zB) x7 x9 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 zD) (Z_to_bv 64 zC) (Z_to_bv 64 eofv)
                       (Z_to_bv 64 zA) SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 x28 x29 x30 x31).
  Proof.
    intros mX q eofv zA zB zC zD x5 x7 x9 x18 x19 x28 x29 x30 x31 I Hq Hn He HA HB HC HD.
    do 5 zstep. if_cases KS.
    - eapply db_ret; [exact I | left; reflexivity].
    - do 6 zstep.
      destruct (Z.eq_dec eofv (-1)) as [-> | NE].
      + zstep. th_if_lit.
        do 5 zstep. zstep. zstep.

        eapply (db_last_sw mX q); [exact I | exact Hq | exact Hn |].
        destruct (Z.land (zC + -61) 18446744073709551615 <? 1); destruct (Z.land (zD + -61) 18446744073709551615 <? 1); cbn [Z.b2z]; lia.
      + zstep. if_cases KE; zify_cond KE. 2:{ exfalso. lia. }
        zstep. zstep.
        eapply (db_last_sw mX q eofv); [exact I | exact Hq | exact Hn | lia].
  Qed.

  (* [comment removed for export] *)
  Ltac conv_site I chk jj ADDR kont :=
    chk; zstep; th_if_lit;
    let b := fresh "b" in let Hb := fresh "Hb" in
    destruct (nth_error ed (Z.to_nat jj)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia];
    let Rb := fresh "Rb" in pose proof (bv_unsigned_in_range 8 b) as Rb; unfold bv_modulus in Rb; change (2 ^ Z.of_N 8) with 256 in Rb;
    let RD := fresh "RD" in
    pose proof (u8ro_read asegs _ (C + 4) ed jj b (Z_to_bv 64 ADDR) (proj1 (proj2 I)) Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
    zstep; clear RD; zstep;
    let SB := fresh "SB" in let HB := fresh "HB" in let EQ := fresh "EQ" in
    destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota;
    [ zstep; kont 255
    | rewrite EQ; zstep;
      do 3 zstep; zstep; th_if_lit;
      let v := fresh "v" in let Hv := fresh "Hv" in
      destruct (b64A_table_nth (bv_unsigned b) ltac:(pose proof (bv_unsigned_in_range 8 b); lia)) as [v Hv];
      let RD2 := fresh "RD" in
      pose proof (u8ro_read asegs _ 672160 b64A_table (bv_unsigned b) v (Z_to_bv 64 (672160 + bv_unsigned b))
                    (b64A_table_at _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 I))))))) Hv ltac:(pose proof (bv_unsigned_in_range 8 b); lia) eq_refl) as RD2;
      zstep; clear RD2;
      let R := fresh "R" in
      pose proof (bv_unsigned_in_range 8 v) as R; unfold bv_modulus in R; change (2 ^ Z.of_N 8) with 256 in R;
      zstep; kont (bv_unsigned v) ].

  (* [comment removed for export] *)
  Lemma db_last_s4 : forall mX q eofv j zA zB zC x7 x9 x18 x19 x28 x29 x30 x31,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 -> 0 <= j -> j + 4 <= n0 ->
    0 <= zA <= 255 -> 0 <= zB <= 255 -> 0 <= zC <= 255 ->
    evt asegs POST (ST 0x31fd3c mX TBL (Z_to_bv 64 zB) x7 x9 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j)) (Z_to_bv 64 zC) (Z_to_bv 64 eofv)
                       (Z_to_bv 64 zA) SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 x28 x29 x30 x31).
  Proof.
    intros mX q eofv j zA zB zC x7 x9 x18 x19 x28 x29 x30 x31 I Hq Hn He Hj Hj4 HA HB HC. prep I.
    conv_site I ltac:(do 4 zstep) (j + 3) (C + 4 + j + 3) ltac:(fun z => eapply (db_last_tail mX q eofv zA zB zC z); first [exact I | lia]).
  Qed.

  Lemma db_last_s3 : forall mX q eofv j zA zB x7 x9 x13 x18 x19 x28 x29 x30 x31,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 -> 0 <= j -> j + 4 <= n0 ->
    0 <= zA <= 255 -> 0 <= zB <= 255 ->
    evt asegs POST (ST 0x31fd00 mX TBL (Z_to_bv 64 zB) x7 x9 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j)) x13 (Z_to_bv 64 eofv)
                       (Z_to_bv 64 zA) SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 x28 x29 x30 x31).
  Proof.
    intros mX q eofv j zA zB x7 x9 x13 x18 x19 x28 x29 x30 x31 I Hq Hn He Hj Hj4 HA HB. prep I.
    conv_site I ltac:(do 4 zstep) (j + 2) (C + 4 + j + 2) ltac:(fun z => eapply (db_last_s4 mX q eofv j zA zB z); first [exact I | lia]).
  Qed.
  Lemma db_last_s2 : forall mX q eofv j zA x6 x7 x9 x13 x18 x19 x28 x29 x30 x31,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 -> 0 <= j -> j + 4 <= n0 ->
    0 <= zA <= 255 ->
    evt asegs POST (ST 0x31fcc4 mX TBL x6 x7 x9 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j)) x13 (Z_to_bv 64 eofv)
                       (Z_to_bv 64 zA) SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 x28 x29 x30 x31).
  Proof.
    intros mX q eofv j zA x6 x7 x9 x13 x18 x19 x28 x29 x30 x31 I Hq Hn He Hj Hj4 HA. prep I.
    conv_site I ltac:(do 4 zstep) (j + 1) (C + 4 + j + 1) ltac:(fun z => eapply (db_last_s3 mX q eofv j zA z); first [exact I | lia]).
  Qed.
  (* [comment removed for export] *)
  Lemma db_last : forall mX q eofv j x6 x7 x9 x13 x15 x18 x19 x28 x29 x30 x31,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 -> 0 <= j -> j + 4 <= n0 ->
    evt asegs POST (ST 0x31fc8c mX TBL x6 x7 x9 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j)) x13 (Z_to_bv 64 eofv)
                       x15 SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 x28 x29 x30 x31).
  Proof.
    intros mX q eofv j x6 x7 x9 x13 x15 x18 x19 x28 x29 x30 x31 I Hq Hn He Hj Hj4. prep I.
    conv_site I ltac:(do 3 zstep) j (C + 4 + j) ltac:(fun z => eapply (db_last_s2 mX q eofv j z); first [exact I | lia]).
  Qed.

  (* [comment removed for export] *)
  Definition LOOPH (Q j0 eofv q : Z) : Prop :=
    forall mX x9 x15 x18 x19 x29 x30 x31,
      INV mX -> 0 <= q -> q + 1 < Q ->
      evt asegs POST (ST 0x31fa54 mX TBL (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (4 * q)) x9 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 (T + 3 * q))
                         (Z_to_bv 64 eofv) x15 SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 (Z_to_bv 64 (4 * Q - 4)) x29 x30 x31).

  Section Loop.
    Variables (Q j0 eofv q : Z).
    Hypothesis HQ : 0 <= q /\ q + 1 < Q /\ 0 <= j0 /\ j0 + 4 * Q <= n0 /\ -1 <= eofv <= 2.
    Hypothesis NEXT : LOOPH Q j0 eofv (q + 1).
    Notation J := (j0 + 4 * q).

    (* [comment removed for export] *)
    Lemma db_loop_tail : forall mX zA zB zC zD x11 x18 x19,
      INV mX -> 0 <= zA <= 255 -> 0 <= zB <= 255 -> 0 <= zC <= 255 -> 0 <= zD <= 255 ->
      evt asegs POST (ST 0x31fb48 mX TBL (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 zC) (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 (T + 3 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 zD) SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 (Z_to_bv 64 (4 * Q - 4)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 zA) (Z_to_bv 64 zB)).
    Proof.
      intros mX zA zB zC zD x11 x18 x19 I H1 H2 H3 H4. pose proof HWS as HWS'.
      assert (HQ4 : q + 1 <= n0 / 4) by (apply Z.div_le_lower_bound; lia).
      do 4 zstep. zstep. if_cases KS.
      - eapply db_ret; [exact I | left; reflexivity].
      - chk_stb I (3 * q) (T + 3 * q) 0x31fb6c 18 11.
        do 5 zstep. stb I (3 * q) (T + 3 * q).
        chk_stb I (3 * q + 1) (T + 3 * q + 1) 0x31fb94 18 30.
        do 4 zstep. stb I (3 * q + 1) (T + 3 * q + 1).
        chk_stb I (3 * q + 2) (T + 3 * q + 2) 0x31fbb8 31 30.
        do 6 zstep. stb I (3 * q + 2) (T + 3 * q + 2).
        zstep.
        rewrite (ubs_sw32 (4 * q + 4)) by lia.
        zstep. if_cases KL; zify_cond KL; signed_lits_in KL.
        + replace (T + 3 * q + 3) with (T + 3 * (q + 1)) by lia. replace (3 * q + 6) with (3 * (q + 1) + 3) by lia.
          replace (4 * q + 4) with (4 * (q + 1)) by lia.
          eapply NEXT; [exact I | lia | lia].
        + do 3 zstep.
          replace (T + 3 * q + 3) with (T + 3 * (q + 1)) by lia. replace (3 * q + 6) with (3 * (q + 1) + 3) by lia.
          replace (C + 4 + j0 + (4 * q + 4)) with (C + 4 + (j0 + 4 * (q + 1))) by lia.
          eapply (db_last _ (q + 1) eofv (j0 + 4 * (q + 1))); first [exact I | lia].
    Qed.

    Lemma db_loop_s4 : forall mX zA zB zC x11 x18 x19,
      INV mX -> 0 <= zA <= 255 -> 0 <= zB <= 255 -> 0 <= zC <= 255 ->
      evt asegs POST (ST 0x31fb0c mX TBL (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 zC) (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 (T + 3 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 (C + 4 + j0 + 4 * q)) SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 (Z_to_bv 64 (4 * Q - 4)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 zA) (Z_to_bv 64 zB)).
    Proof.
      intros mX zA zB zC x11 x18 x19 I H1 H2 H3. prep I.
      conv_site I ltac:(do 4 zstep) (J + 3) (C + 4 + j0 + 4 * q + 3) ltac:(fun z => eapply (db_loop_tail mX zA zB zC z); first [exact I | lia]).
    Qed.

    Lemma db_loop_s3 : forall mX zA zB x9 x11 x18 x19,
      INV mX -> 0 <= zA <= 255 -> 0 <= zB <= 255 ->
      evt asegs POST (ST 0x31fad0 mX TBL (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (4 * q)) x9 (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 (T + 3 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 (C + 4 + j0 + 4 * q)) SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 (Z_to_bv 64 (4 * Q - 4)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 zA) (Z_to_bv 64 zB)).
    Proof.
      intros mX zA zB x9 x11 x18 x19 I H1 H2. prep I.
      conv_site I ltac:(do 4 zstep) (J + 2) (C + 4 + j0 + 4 * q + 2) ltac:(fun z => eapply (db_loop_s4 mX zA zB z); first [exact I | lia]).
    Qed.

    Lemma db_loop_s2 : forall mX zA x9 x11 x18 x19 x31,
      INV mX -> 0 <= zA <= 255 ->
      evt asegs POST (ST 0x31fa94 mX TBL (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (4 * q)) x9 (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 (T + 3 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 (C + 4 + j0 + 4 * q)) SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 (Z_to_bv 64 (4 * Q - 4)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 zA) x31).
    Proof.
      intros mX zA x9 x11 x18 x19 x31 I H1. prep I.
      conv_site I ltac:(do 4 zstep) (J + 1) (C + 4 + j0 + 4 * q + 1) ltac:(fun z => eapply (db_loop_s3 mX zA z); first [exact I | lia]).
    Qed.

    Lemma db_loop_head : forall mX x9 x15 x18 x19 x29 x30 x31,
      INV mX ->
      evt asegs POST (ST 0x31fa54 mX TBL (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (4 * q)) x9 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 (T + 3 * q))
                         (Z_to_bv 64 eofv) x15 SHBv (Z_to_bv 64 (3 * q + 3)) x18 x19 (Z_to_bv 64 (4 * Q - 4)) x29 x30 x31).
    Proof.
      intros mX x9 x15 x18 x19 x29 x30 x31 I. prep I.
      conv_site I ltac:(do 5 zstep) (j0 + 4 * q) (C + 4 + j0 + 4 * q) ltac:(fun z => eapply (db_loop_s2 mX z); first [exact I | lia]).
    Qed.
  End Loop.

  Lemma db_loop : forall (k : nat) Q j0 eofv q, Z.to_nat (Q - q) = k ->
    0 <= j0 -> j0 + 4 * Q <= n0 -> -1 <= eofv <= 2 -> LOOPH Q j0 eofv q.
  Proof.
    induction k as [k IH] using lt_wf_ind; intros Q j0 eofv q HK Hj0 HjQ He.
    intros mX x9 x15 x18 x19 x29 x30 x31 I Hq HqQ.
    eapply (db_loop_head Q j0 eofv q); [lia | | exact I].
    eapply (IH (Z.to_nat (Q - (q + 1)))); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma db_chk : forall mX nn j0 eofv x6 x7 x9 x10 x15 x17 x18 x19 x28 x29 x30 x31,
    INV mX -> 0 <= nn -> 0 <= j0 -> j0 + nn <= n0 -> -1 <= eofv <= 2 ->
    evt asegs POST (ST 0x31fa28 mX TBL x6 x7 x9 x10 (Z_to_bv 64 T) (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 nn) (Z_to_bv 64 eofv) x15 SHBv x17
                       x18 x19 x28 x29 x30 x31).
  Proof.
    intros mX nn j0 eofv x6 x7 x9 x10 x15 x17 x18 x19 x28 x29 x30 x31 I Hnn Hj0 Hj He.
    assert (HD : 0 <= n0 / 4) by (apply Z.div_pos; lia).
    zstep. zstep. zstep. if_cases K3; zify_cond K3.
    - eapply db_ret; [exact I | left; reflexivity].
    - assert (HM : nn = 4 * (nn / 4)).
      { revert K3. rewrite ?unsigned_lit by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. intros K3.
        pose proof (Z.div_mod nn 4 ltac:(lia)). lia. }
      zstep. if_cases K0; zify_cond K0.
      + do 2 zstep. eapply db_ret; [exact I | right; rewrite ?unsigned_lit in K0 by lia; lia].
      + zstep. zstep. if_cases K5; zify_cond K5; signed_lits_in K5.
        * do 2 zstep.
          replace (Z_to_bv 64 T) with (Z_to_bv 64 (T + 3 * 0)) by (f_equal; lia).
          change (Z_to_bv 64 3) with (Z_to_bv 64 (3 * 0 + 3)).
          eapply (db_last _ 0 eofv j0); first [exact I | lia].
        * do 5 zstep.
          assert (SW : bv_swrap 32 (nn + -4) = 4 * (nn / 4) - 4) by (rewrite ubs_sw32 by lia; lia). rewrite SW.
          replace (Z_to_bv 64 T) with (Z_to_bv 64 (T + 3 * 0)) by (f_equal; lia).
          change (Z_to_bv 64 3) with (Z_to_bv 64 (3 * 0 + 3)). change (Z_to_bv 64 0) with (Z_to_bv 64 (4 * 0)).
          eapply (db_loop (Z.to_nat (nn / 4 - 0)) (nn / 4) j0 eofv 0); first [exact I | reflexivity | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma db_tt : forall (k : nat) mX nn j0 eofv x9 x13 x15 x18 x19 x28 x29 x30 x31,
    INV mX -> Z.to_nat nn = k -> 4 <= nn -> 0 <= j0 -> j0 + nn <= n0 -> -1 <= eofv <= 2 ->
    evt asegs POST (ST 0x31f9a8 mX TBL (Z_to_bv 64 4) (Z_to_bv 64 224) x9 (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4 + j0)) x13 (Z_to_bv 64 eofv)
                       x15 SHBv (Z_to_bv 64 nn) x18 x19 x28 x29 x30 x31).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros mX nn j0 eofv x9 x13 x15 x18 x19 x28 x29 x30 x31 I HK Hnn Hj0 Hj He. prep I.
    assert (L32 : Z.land nn 4294967295 = nn).
    { change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    do 3 zstep. rewrite ?L32. do 2 zstep.
    do 3 zstep. zstep. th_if_lit.
    zstep.
    destruct (nth_error ed (Z.to_nat (j0 + nn - 1))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
    pose proof (u8ro_read asegs _ (C + 4) ed (j0 + nn - 1) b (Z_to_bv 64 (C + 4 + j0 + nn + -1)) FB Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep.
    destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota.
    - eapply (db_chk _ nn j0 eofv); first [exact I | lia].
    - rewrite EQ. zstep. do 3 zstep. zstep. th_if_lit.
      destruct (b64A_table_nth (bv_unsigned b) ltac:(lia)) as [v Hv].
      pose proof (u8ro_read asegs _ 672160 b64A_table (bv_unsigned b) v (Z_to_bv 64 (672160 + bv_unsigned b)) (b64A_table_at _ MI) Hv ltac:(lia) eq_refl) as RD2.
      zstep. clear RD2.
      zstep. zstep. if_cases KB.
      + eapply (db_chk _ nn j0 eofv); first [exact I | lia].
      + zstep.
        assert (SW : bv_swrap 32 (nn + -1) = nn - 1) by (rewrite ubs_sw32 by lia; lia). rewrite SW.
        zstep. if_cases K4; zify_cond K4; signed_lits_in K4.
        * eapply (IH (Z.to_nat (nn - 1))); first [exact I | reflexivity | lia].
        * do 3 zstep. eapply db_ret; [exact I | left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma db_tt_entry : forall mX nn j0 eofv x6 x7 x9 x13 x15 x18 x19 x28 x29 x30 x31,
    INV mX -> 0 <= nn -> 0 <= j0 -> j0 + nn <= n0 -> -1 <= eofv <= 2 ->
    evt asegs POST (ST 0x31f99c mX TBL x6 x7 x9 (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4 + j0)) x13 (Z_to_bv 64 eofv)
                       x15 SHBv (Z_to_bv 64 nn) x18 x19 x28 x29 x30 x31).
  Proof.
    intros mX nn j0 eofv x6 x7 x9 x13 x15 x18 x19 x28 x29 x30 x31 I Hnn Hj0 Hj He.
    zstep. zstep. if_cases K3; zify_cond K3; signed_lits_in K3; rewrite ?signed_of_Z in K3 by lia.
    - zstep. eapply (db_chk _ nn j0 eofv); first [exact I | lia].
    - zstep. eapply (db_tt (Z.to_nat nn) _ nn j0 eofv); first [exact I | reflexivity | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma db_ws : forall (k : nat) mX i eofv x7 x9 x17 x18 x19 x28 x29 x30 x31,
    INV mX -> Z.to_nat (n0 - i) = k -> 0 <= i < n0 -> -1 <= eofv <= 2 ->
    evt asegs POST (ST 0x31f930 mX TBL (Z_to_bv 64 1) x7 x9 (Z_to_bv 64 (C + 4 + i)) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4 + i)) (Z_to_bv 64 (n0 - i)) (Z_to_bv 64 eofv)
                       (Z_to_bv 64 224) SHBv x17 x18 x19 x28 x29 x30 x31).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros mX i eofv x7 x9 x17 x18 x19 x28 x29 x30 x31 I HK Hi He. prep I.
    assert (HD : 0 <= n0 / 4) by (apply Z.div_pos; lia).
    do 3 zstep. zstep. zstep. th_if_lit.
    destruct (nth_error ed (Z.to_nat i)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
    pose proof (u8ro_read asegs _ (C + 4) ed i b (Z_to_bv 64 (C + 4 + i)) FB Hb ltac:(lia) eq_refl) as RD.
    zstep. clear RD. zstep.
    destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota.
    - eapply (db_tt_entry _ (n0 - i) i eofv); first [exact I | lia].
    - rewrite EQ. zstep. do 3 zstep. zstep. th_if_lit.
      destruct (b64A_table_nth (bv_unsigned b) ltac:(lia)) as [v Hv].
      pose proof (u8ro_read asegs _ 672160 b64A_table (bv_unsigned b) v (Z_to_bv 64 (672160 + bv_unsigned b)) (b64A_table_at _ MI) Hv ltac:(lia) eq_refl) as RD2.
      zstep. clear RD2.
      zstep. if_cases KW.
      + eapply (db_tt_entry _ (n0 - i) i eofv); first [exact I | lia].
      + zstep. zstep.
        assert (SW : bv_swrap 32 (n0 - i + -1) = n0 - (i + 1)) by (rewrite ubs_sw32 by lia; lia).
        rewrite SW. zstep. replace (C + 4 + i + 1) with (C + 4 + (i + 1)) by lia.
        zstep. if_cases K1; zify_cond K1; signed_lits_in K1; rewrite ?signed_of_Z in K1 by lia.
        * eapply (IH (Z.to_nat (n0 - (i + 1)))); first [exact I | reflexivity | lia].
        * do 3 zstep. eapply db_ret; [exact I | right; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dblock_body : forall bs0 eofv t0 t1 t2 a5 a6 a7 t3 t4 t5 t6,
    ro_cells asegs m C (ectx_cells num ed ln (Z_to_bv 64 0)) -> rw_cells asegs m T [CB K bs0] -> stk asegs m lo SP -> mem_inv asegs m ->
    img_untouched m -> ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
    -1 <= eofv <= 2 ->
    evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4)) (Z_to_bv 64 n0) (Z_to_bv 64 eofv) a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x31f8bc) fc None m (seg_rom asegs)).
  Proof.
    intros bs0 eofv t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 CTX DST ST MI UT SHC He.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM. pose proof HWS as HWS'.
    assert (HWU : ut_fp W) by (clear - AB TIM; ut_fp_lia).
    pose proof (rw_cells_CB_length asegs _ _ _ _ DST) as LBS. apply u8arr_of_rw_cells in DST.
    pose proof (ectxA_data m C num ed ln _ LED CTX) as FB.
    pose proof CTX as CTXb.
    apply (ro_cells_congr asegs m C _ [C4 num; CB 80 ed; C4 ln; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in CTXb;
      [| reflexivity | cbn; rewrite LED; tauto].
    unfold ectx_cells in CTX.
    th_frame 40%nat [8; 8; 8; 8; 8]%nat ST.
    do 7 ths.
    do 3 zstep.
    zstep. if_cases KC; zify_cond KC. { exfalso. lia. }
    zstep. chk_pass ACC_C (C + 88) 4 0x31f8fc 15 17.
    do 2 zstep. zstep. th_if_lit.
    do 2 zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (I : INV mX) end.
    { fold (ectx_cells num ed ln (Z_to_bv 64 0)) in CTX.
      split; [exact CTX|]. split; [exact FB|]. split; [exists bs0; split; [exact DST | exact LBS]|]. split; [exact FR|]. split; [exact ST|].
      split; [exact MI|]. split; [|exact WM]. exact MU. }
    clear CTX CTXb FB DST FR ST MI MU WM.
    zstep. if_cases KN; zify_cond KN; signed_lits_in KN.
    - do 3 zstep.
      replace (Z_to_bv 64 (C + 4)) with (Z_to_bv 64 (C + 4 + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 n0) with (Z_to_bv 64 (n0 - 0)) by (f_equal; lia).
      eapply (db_ws (Z.to_nat (n0 - 0)) _ 0 eofv); first [exact I | reflexivity | lia].
    - zstep.
      replace (Z_to_bv 64 (C + 4)) with (Z_to_bv 64 (C + 4 + 0)) by (f_equal; lia).
      eapply (db_chk _ n0 0 eofv); first [exact I | lia].
  Qed.
End Proofs.

(* [comment removed for export] *)
Definition dblock_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (C T : Z) (K : nat) (n0 eofv : Z) (num ln : word) (ed bs0 : list byte) (lo : Z),
    a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 T -> a2 = Z_to_bv 64 (C + 4) -> a3 = Z_to_bv 64 n0 -> a4 = Z_to_bv 64 eofv ->
    ro_cells asegs m C (ectx_cells num ed ln (Z_to_bv 64 0)) -> length ed = 80%nat -> 0 < C -> C mod 8 = 0 -> C + 92 <= lo -> acc asegs m C 92 ->
    rw_cells asegs m T [CB K bs0] -> 0 < T -> T + Z.of_nat K <= lo -> acc asegs m T (Z.of_nat K) ->
    (T + Z.of_nat K <= 0x10000 \/ 0xbc6000 <= T) -> (T + Z.of_nat K <= 0x7fff8000 \/ 0x10007fff8000 <= T) ->
    (C + 92 <= T \/ T + Z.of_nat K <= C) ->
    0 <= n0 <= 80 -> 3 * (n0 / 4) <= Z.of_nat K -> -1 <= eofv <= 2 ->
    acc asegs m 672160 128 ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (dblock_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C T K n0 num ln ed lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_evp_decodeblock_int) fc None m (seg_rom asegs)).

Theorem dblock_proof : dblock_stmt.
Proof.
  unfold dblock_stmt, g_shadow_memory_dynamic_address, SHB, e_evp_decodeblock_int. intros until lo.
  intros -> -> -> -> -> CTX LED HC CAL CLO ACC_C DST HT0 TLO ACC_T TIM TSH SEP HN HK HE ACC_B UT SHC ST LO0 LO HTOP MI.
  pose proof (rw_cells_bound _ _ _ _ DST) as TB. cbn [cells_size csize Nat.add] in TB.
  eapply (dblock_body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m C T K n0 num ln ed lo); try eassumption; lia.
Qed.

