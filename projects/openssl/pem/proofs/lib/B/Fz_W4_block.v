(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac Arr SFModel.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_W4_kit Fz_W4_defs Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition dblock_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C T : Z) (K : nat) (n0 : Z) (num ln : word) (ed : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (dl : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (bs' : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dl) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (T, T + 3 * (n0 / 4))] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ (dl = -1 \/ 0 <= dl <= 3 * (n0 / 4))
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ ro_cells bsegs m' C (ectx_cells num ed ln (Z_to_bv 64 0))
    /\ rw_cells bsegs m' T [CB K bs'].

Section Proofs.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (C T : Z) (K : nat) (n0 : Z) (num ln : word) (ed : list byte) (lo : Z).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 64, bv_unsigned sp); (T, T + 3 * (n0 / 4))]%Z.
  Hypothesis AB : 0 <= n0 <= 80 /\ 3 * (n0 / 4) <= Z.of_nat K /\ 0 < C /\ C + 92 <= lo /\ 0 < T /\ T + Z.of_nat K <= lo
                  /\ 0x10007fff8000 <= lo /\ lo <= SP - 64 /\ SP <= 2 ^ 47.
  Hypothesis SEP_CT : C + 92 <= T \/ T + Z.of_nat K <= C.
  Hypothesis TIM : T + Z.of_nat K <= 0x10000 \/ 0xbf8000 <= T.
  Hypothesis TSH : T + Z.of_nat K <= 0x7fff8000 \/ 0x10007fff8000 <= T.
  Hypothesis LED : length ed = 80%nat.
  Hypothesis CAL : C mod 8 = 0.
  (* [comment removed for export] *)
  Hypothesis ACC_C : acc bsegs m C 92.
  Hypothesis ACC_T : acc bsegs m T (Z.of_nat K).
  Hypothesis ACC_B : acc bsegs m 660960 128.

  Lemma HWS : sh_fp W.
  Proof. clear LED CAL ACC_C ACC_T ACC_B SEP_CT TIM. sh_fp_lia. Qed.
  Lemma TAL : 660960 mod 8 = 0.
  Proof. reflexivity. Qed.

  Notation POST := (dblock_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C T K n0 num ln ed lo m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -64)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SHBv := (Z_to_bv 64 2147450880).
  Notation TBL := (Z_to_bv 64 660960).

  (* [comment removed for export] *)
  Definition INV (mX : mem) : Prop :=
    ro_cells bsegs mX C (ectx_cells num ed ln (Z_to_bv 64 0)) /\ bytes_at bsegs mX (C + 4) ed
    /\ (exists bs, u8arr bsegs mX T bs /\ length bs = K)
    /\ rw_cells bsegs mX (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ stk bsegs mX lo (SP + -56)
    /\ mem_inv bsegs mX /\ munch W m mX /\ wmono bsegs m mX.

  Ltac open_inv H := destruct H as (CTX & FB & (bs & DST & LBS) & FR & ST & MI & MU & WM).

  Lemma inv_store_ok : forall mX k a, INV mX -> 0 <= k < 3 * (n0 / 4) -> a = wa (T + k) -> store_ok bsegs mX a 1 = true.
  Proof.
    intros mX k a I Hk Ha; open_inv I.
    eapply (u8arr_store_ok_n bsegs mX T bs k 1 a DST); [lia | rewrite LBS; lia | exact Ha].
  Qed.

  Lemma inv_store : forall mX k a b, INV mX -> 0 <= k < 3 * (n0 / 4) -> a = wa (T + k) -> INV (write_to_mem mX a [b]).
  Proof.
    intros mX k a b I Hk Ha. pose proof (inv_store_ok mX k a I Hk Ha) as SOK. open_inv I. subst a.
    assert (HED : 0 <= C + 4 /\ C + 4 + Z.of_nat (length ed) <= 2 ^ 64) by (rewrite LED; lia).
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - apply ro_cells_frame; [exact CTX | lia | cbn [length]; lia | cbn [length cells_size ectx_cells csize Nat.add]; lia].
    - apply bytes_at_write_other; [exact FB | lia | cbn [length]; lia | cbn [length]; rewrite LED; lia].
    - exists (upd_bytes bs (Z.to_nat k) [b]). split.
      + apply (u8arr_write_bytes bsegs mX T bs k [b] DST); [lia | cbn [length]; rewrite LBS; lia].
      + rewrite upd_bytes_length; [exact LBS | cbn [length]; rewrite LBS; lia].
    - apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [length cells_size csize Nat.add]; lia].
    - apply stk_write; [exact ST | lia | cbn [length]; lia].
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU | lia | cbn [length]; lia |]. cbn [inside length]. right. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma sextw_lit : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 (Z.land z 18446744073709551615 + 0) = z.
  Proof.
    clear. intros z Hz. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32 `div` 2) with (2 ^ 31). change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
    destruct (Z.neg_nonneg_cases z) as [NEG|POS].
    - replace (z `mod` (2 ^ 32 * 2 ^ 32)) with (z + 1 * (2 ^ 32 * 2 ^ 32)) by (apply Z.mod_unique with (q := -1); lia).
      replace (z + 1 * (2 ^ 32 * 2 ^ 32) + 0 + 2 ^ 31) with (z + 2 ^ 31 + (2 ^ 32) * 2 ^ 32) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
    - rewrite (Z.mod_small z) by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma db_ret : forall mX dl x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mX -> (dl = -1 \/ 0 <= dl <= 3 * (n0 / 4)) ->
    evt bsegs POST (ST 0x332c7c mX x5 x6 x7 x9 (Z_to_bv 64 dl) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mX dl x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 I Hdl; open_inv I.
    assert (HD : 0 <= n0 / 4 <= 20) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    zstep. rewrite (sextw_lit dl) by lia.
    do 7 zstep.
    release_frame FR ST (bv_unsigned sp). zstep.
    apply rw_cells_of_u8arr in DST. rewrite LBS in DST.
    zstep. apply evt_done. exists dl. do 14 eexists. exists bs. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact Hdl|]. split; [exact ST|]. split; [exact CTX | exact DST].
  Qed.

  (* [comment removed for export] *)
  Lemma land_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x.
  Proof. clear. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

  (* [comment removed for export] *)
  Lemma db_fin : forall mX q e x5 x6 x7 x9 x10 x11 x12 x13 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mX -> 0 <= q -> q + 1 <= n0 / 4 -> 0 <= e <= 2 ->
    evt bsegs POST (ST 0x333174 mX x5 x6 x7 x9 x10 x11 x12 x13 (Z_to_bv 64 e) (Z_to_bv 64 (3 * q)) x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mX q e x5 x6 x7 x9 x10 x11 x12 x13 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 I Hq HQ He.
    assert (HD : n0 / 4 <= 20) by (apply Z.div_le_upper_bound; lia).
    zstep. zstep. zstep. zstep.

    rewrite (ubs_sw32 (3 - e)) by lia. rewrite (land_ones64 (3 - e)) by lia. rewrite (ubs_sw32 (3 * q + (3 - e))) by lia.
    zstep. if_cases KF; zify_cond KF; [| exfalso; rewrite ?unsigned_lit in KF by lia; lia].
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
  Lemma db_last_sw : forall mX q e x5 x6 x7 x9 x10 x12 x13 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> 0 <= e <= 2 ->
    evt bsegs POST (ST 0x3330ac mX x5 x6 x7 x9 x10 (Z_to_bv 64 (T + 3 * q)) x12 x13 (Z_to_bv 64 e) (Z_to_bv 64 (3 * q)) SHBv x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mX q e x5 x6 x7 x9 x10 x12 x13 x17 x18 x19 x20 x21 x28 x29 x30 x31 I Hq Hn He.
    pose proof HWS as HWS.
    assert (HQ : q + 1 <= n0 / 4) by (apply Z.div_le_lower_bound; lia).
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. rewrite ?unsigned_lit in KU by lia. lia. }
      chk_stb I (3 * q) (T + 3 * q) 0x333114 5 6.

      zstep. zstep. stb I (3 * q) (T + 3 * q).
      zstep. if_cases KV; zify_cond KV. { exfalso. rewrite ?unsigned_lit in KV by lia. lia. }
      chk_stb I (3 * q + 1) (T + 3 * q + 1) 0x333134 12 5.
      zstep. zstep. stb I (3 * q + 1) (T + 3 * q + 1).
      chk_stb I (3 * q + 2) (T + 3 * q + 2) 0x333150 10 12.
      stb I (3 * q + 2) (T + 3 * q + 2).
      zstep. eapply db_fin; [exact I | lia | lia | lia].
    - zstep. zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        zstep. if_cases KN; zify_cond KN. { exfalso. rewrite ?unsigned_lit in KN by lia. lia. }
        chk_stb I (3 * q) (T + 3 * q) 0x33316c 10 13.
        zstep. stb I (3 * q) (T + 3 * q).
        eapply db_fin; [exact I | lia | lia | lia].
      + (* [comment removed for export] *)
        zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. rewrite ?unsigned_lit in KU by lia. lia. }
        chk_stb I (3 * q) (T + 3 * q) 0x3330d4 17 5.
        zstep. stb I (3 * q) (T + 3 * q).
        chk_stb I (3 * q + 1) (T + 3 * q + 1) 0x3330ec 11 12.
        zstep. stb I (3 * q + 1) (T + 3 * q + 1).
        zstep. eapply db_fin; [exact I | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Ltac prep I :=
    pose proof HWS as HWS'; pose proof TAL as TAL';
    let I' := fresh "Ic" in pose proof I as I'; open_inv I'.

  (* [comment removed for export] *)
  Lemma db_last_tail : forall mX q eofv zA zB zC zD x5 x9 x12 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 ->
    0 <= zA <= 255 -> 0 <= zB <= 255 -> 0 <= zC <= 255 -> 0 <= zD <= 255 ->
    evt bsegs POST (ST 0x333064 mX x5 (Z_to_bv 64 zB) (Z_to_bv 64 zC) x9 (Z_to_bv 64 zD) (Z_to_bv 64 (T + 3 * q)) x12 (Z_to_bv 64 zA) (Z_to_bv 64 eofv)
                       (Z_to_bv 64 (3 * q)) SHBv x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mX q eofv zA zB zC zD x5 x9 x12 x17 x18 x19 x20 x21 x28 x29 x30 x31 I Hq Hn He HA HB HC HD.
    do 5 zstep. if_cases KS.
    - zstep. eapply db_ret; [exact I | left; reflexivity].
    - do 6 zstep.
      destruct (Z.eq_dec eofv (-1)) as [-> | NE].
      + zstep. th_if_lit.
        do 5 zstep. zstep.

        eapply (db_last_sw mX q); [exact I | exact Hq | exact Hn |].
        destruct (Z.land (zC + -61) 18446744073709551615 <? 1); destruct (Z.land (zD + -61) 18446744073709551615 <? 1); cbn [Z.b2z]; lia.
      + zstep. if_cases KE; zify_cond KE. 2:{ exfalso. lia. }
        zstep.
        eapply (db_last_sw mX q eofv); [exact I | exact Hq | exact Hn | lia].
  Qed.

  (* [comment removed for export] *)
  Ltac conv_site I chk jj ADDR kont :=
    chk; zstep; th_if_lit;
    let b := fresh "b" in let Hb := fresh "Hb" in
    destruct (nth_error ed (Z.to_nat jj)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia];
    let Rb := fresh "Rb" in pose proof (bv_unsigned_in_range 8 b) as Rb; unfold bv_modulus in Rb; change (2 ^ Z.of_N 8) with 256 in Rb;
    let RD := fresh "RD" in
    pose proof (u8ro_read bsegs _ (C + 4) ed jj b (Z_to_bv 64 ADDR) (proj1 (proj2 I)) Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
    zstep; clear RD; zstep;
    let SB := fresh "SB" in let HB := fresh "HB" in let EQ := fresh "EQ" in
    destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota;
    [ zstep; kont 255
    | rewrite EQ; zstep;
      (let KO := fresh "KO" in if_cases KO; zify_cond KO; [exfalso; rewrite ?unsigned_lit in KO by lia; lia|]);
      zstep;
      do 3 zstep; zstep; th_if_lit;
      let v := fresh "v" in let Hv := fresh "Hv" in
      destruct (b64A_table_nth (bv_unsigned b) ltac:(pose proof (bv_unsigned_in_range 8 b); lia)) as [v Hv];
      let RD2 := fresh "RD" in
      pose proof (u8ro_read bsegs _ 660960 b64A_table (bv_unsigned b) v (Z_to_bv 64 (660960 + bv_unsigned b))
                    (b64A_table_at _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 I))))))) Hv ltac:(pose proof (bv_unsigned_in_range 8 b); lia) eq_refl) as RD2;
      zstep; clear RD2;
      let R := fresh "R" in
      pose proof (bv_unsigned_in_range 8 v) as R; unfold bv_modulus in R; change (2 ^ Z.of_N 8) with 256 in R;
      zstep; kont (bv_unsigned v) ].

  (* [comment removed for export] *)
  Lemma db_last_s4 : forall mX q eofv j zA zB zC x9 x12 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 -> 0 <= j -> j + 4 <= n0 ->
    0 <= zA <= 255 -> 0 <= zB <= 255 -> 0 <= zC <= 255 ->
    evt bsegs POST (ST 0x33301c mX (Z_to_bv 64 18446744073708890655) (Z_to_bv 64 zB) (Z_to_bv 64 zC) x9 (Z_to_bv 64 (C + 4 + j)) (Z_to_bv 64 (T + 3 * q)) x12 (Z_to_bv 64 zA) (Z_to_bv 64 eofv)
                       (Z_to_bv 64 (3 * q)) SHBv TBL x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mX q eofv j zA zB zC x9 x12 x18 x19 x20 x21 x28 x29 x30 x31 I Hq Hn He Hj Hj4 HA HB HC. prep I.
    zstep. zstep. zstep. if_cases KV; zify_cond KV. { exfalso. rewrite ?unsigned_lit in KV by lia. lia. }
    conv_site I ltac:(do 3 zstep) (j + 3) (C + 4 + j + 3) ltac:(fun z => eapply (db_last_tail mX q eofv zA zB zC z); first [exact I | lia]).
  Qed.

  Notation NTBL := (Z_to_bv 64 18446744073708890655).
  Lemma db_last_s3 : forall mX q eofv j zA zB x7 x9 x12 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 -> 0 <= j -> j + 4 <= n0 ->
    0 <= zA <= 255 -> 0 <= zB <= 255 ->
    evt bsegs POST (ST 0x332fd4 mX NTBL (Z_to_bv 64 zB) x7 x9 (Z_to_bv 64 (C + 4 + j)) (Z_to_bv 64 (T + 3 * q)) x12 (Z_to_bv 64 zA) (Z_to_bv 64 eofv)
                       (Z_to_bv 64 (3 * q)) SHBv TBL x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mX q eofv j zA zB x7 x9 x12 x18 x19 x20 x21 x28 x29 x30 x31 I Hq Hn He Hj Hj4 HA HB. prep I.
    zstep. zstep. zstep. if_cases KV; zify_cond KV. { exfalso. rewrite ?unsigned_lit in KV by lia. lia. }
    conv_site I ltac:(do 3 zstep) (j + 2) (C + 4 + j + 2) ltac:(fun z => eapply (db_last_s4 mX q eofv j zA zB z); first [exact I | lia]).
  Qed.
  Lemma db_last_s2 : forall mX q eofv j zA x6 x7 x9 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 -> 0 <= j -> j + 4 <= n0 ->
    0 <= zA <= 255 ->
    evt bsegs POST (ST 0x332f90 mX NTBL x6 x7 x9 (Z_to_bv 64 (C + 4 + j)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j + 1)) (Z_to_bv 64 zA) (Z_to_bv 64 eofv)
                       (Z_to_bv 64 (3 * q)) SHBv TBL x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mX q eofv j zA x6 x7 x9 x18 x19 x20 x21 x28 x29 x30 x31 I Hq Hn He Hj Hj4 HA. prep I.
    zstep. zstep. if_cases KV; zify_cond KV. { exfalso. rewrite ?unsigned_lit in KV by lia. lia. }
    conv_site I ltac:(do 3 zstep) (j + 1) (C + 4 + j + 1) ltac:(fun z => eapply (db_last_s3 mX q eofv j zA z); first [exact I | lia]).
  Qed.
  (* [comment removed for export] *)
  Lemma db_last : forall mX q eofv j x6 x7 x9 x12 x13 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 -> 0 <= j -> j + 4 <= n0 ->
    evt bsegs POST (ST 0x332f48 mX NTBL x6 x7 x9 (Z_to_bv 64 (C + 4 + j)) (Z_to_bv 64 (T + 3 * q)) x12 x13 (Z_to_bv 64 eofv)
                       (Z_to_bv 64 (3 * q)) SHBv TBL x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mX q eofv j x6 x7 x9 x12 x13 x18 x19 x20 x21 x28 x29 x30 x31 I Hq Hn He Hj Hj4. prep I.
    zstep. zstep. zstep. if_cases KV; zify_cond KV. { exfalso. rewrite ?unsigned_lit in KV by lia. lia. }
    conv_site I ltac:(do 3 zstep) j (C + 4 + j) ltac:(fun z => eapply (db_last_s2 mX q eofv j z); first [exact I | lia]).
  Qed.

  (* [comment removed for export] *)
  Definition LOOPH (Q j0 eofv q : Z) : Prop :=
    forall mX x9 x13 x15 x18 x19 x20 x21,
      INV mX -> 0 <= q -> q + 1 < Q ->
      evt bsegs POST (ST 0x332cd0 mX NTBL (Z_to_bv 64 (4 * Q - 4)) (Z_to_bv 64 (4 * q)) x9 (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (T + 3 * q)) x13
                         (Z_to_bv 64 eofv) x15 SHBv TBL x18 x19 x20 x21 (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (3 * q)) (Z_to_bv 64 2) (Z_to_bv 64 (-1))).

  Section Loop.
    Variables (Q j0 eofv q : Z).
    Hypothesis HQ : 0 <= q /\ q + 1 < Q /\ 0 <= j0 /\ j0 + 4 * Q <= n0 /\ -1 <= eofv <= 2.
    Hypothesis NEXT : LOOPH Q j0 eofv (q + 1).
    Notation J := (j0 + 4 * q).

    (* [comment removed for export] *)
    Lemma db_loop_tail : forall mX zA zB zC zD x11 x20 x21,
      INV mX -> 0 <= zA <= 255 -> 0 <= zB <= 255 -> 0 <= zC <= 255 -> 0 <= zD <= 255 ->
      evt bsegs POST (ST 0x332df0 mX NTBL (Z_to_bv 64 (4 * Q - 4)) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j0)) x11 (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 zD)
                         (Z_to_bv 64 eofv) (Z_to_bv 64 zC) SHBv TBL (Z_to_bv 64 zA) (Z_to_bv 64 zB) x20 x21 (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (3 * q)) (Z_to_bv 64 2) (Z_to_bv 64 (-1))).
    Proof.
      intros mX zA zB zC zD x11 x20 x21 I H1 H2 H3 H4. pose proof HWS as HWS'.
      assert (HQ4 : q + 1 <= n0 / 4) by (apply Z.div_le_lower_bound; lia).
      do 4 zstep. zstep. if_cases KS.
      - zstep. eapply db_ret; [exact I | left; reflexivity].
      - zstep. zstep. if_cases KU; zify_cond KU. { exfalso. rewrite ?unsigned_lit in KU by lia. lia. }
        chk_stb I (3 * q) (T + 3 * q) 0x332e1c 20 21.

        do 5 zstep. stb I (3 * q) (T + 3 * q).
        zstep. if_cases KV1; zify_cond KV1. { exfalso. rewrite ?unsigned_lit in KV1 by lia. lia. }
        chk_stb I (3 * q + 1) (T + 3 * q + 1) 0x332e48 20 21.
        do 4 zstep. stb I (3 * q + 1) (T + 3 * q + 1).
        zstep. if_cases KV2; zify_cond KV2. { exfalso. rewrite ?unsigned_lit in KV2 by lia. lia. }
        zstep.
        chk_stb I (3 * q + 2) (T + 3 * q + 2) 0x332e74 19 20.
        do 3 zstep.

        assert (SW3 : bv_swrap 32 (3 * q + 3) = 3 * q + 3) by (apply ubs_sw32; lia). rewrite SW3.
        stb I (3 * q + 2) (T + 3 * q + 2).
        zstep. if_cases KOV; zify_cond KOV. { exfalso. rewrite ?unsigned_lit in KOV by lia. rewrite ?signed_of_Z in KOV by lia. lia. }
        do 5 zstep.

        assert (SW4 : bv_swrap 32 (4 * q + 4) = 4 * q + 4) by (apply ubs_sw32; lia). rewrite SW4.
        zstep. if_cases KL; zify_cond KL; signed_lits_in KL.
        + do 2 zstep.
          replace (T + 3 * q + 3) with (T + 3 * (q + 1)) by lia. replace (3 * q + 3) with (3 * (q + 1)) by lia.
          replace (C + 4 + j0 + (4 * q + 4)) with (C + 4 + (j0 + 4 * (q + 1))) by lia.
          eapply (db_last _ (q + 1) eofv (j0 + 4 * (q + 1))); first [exact I | lia].
        + zstep.
          replace (T + 3 * q + 3) with (T + 3 * (q + 1)) by lia. replace (3 * q + 3) with (3 * (q + 1)) by lia.
          replace (4 * q + 4) with (4 * (q + 1)) by lia.
          eapply NEXT; [exact I | lia | lia].
    Qed.

    (* [comment removed for export] *)
    Ltac conv_siteX I chk jj ADDR tneg tpos kont :=
      chk; zstep; th_if_lit;
      let b := fresh "b" in let Hb := fresh "Hb" in
      destruct (nth_error ed (Z.to_nat jj)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia];
      let Rb := fresh "Rb" in pose proof (bv_unsigned_in_range 8 b) as Rb; unfold bv_modulus in Rb; change (2 ^ Z.of_N 8) with 256 in Rb;
      let RD := fresh "RD" in
      pose proof (u8ro_read bsegs _ (C + 4) ed jj b (Z_to_bv 64 ADDR) (proj1 (proj2 I)) Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      zstep; clear RD; zstep;
      let SB := fresh "SB" in let HB := fresh "HB" in let EQ := fresh "EQ" in
      destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota;
      [ zstep; tneg; kont 255
      | rewrite EQ; zstep;
        (let KO := fresh "KO" in if_cases KO; zify_cond KO; [exfalso; rewrite ?unsigned_lit in KO by lia; lia|]);
        zstep;
        do 3 zstep; zstep; th_if_lit;
        let v := fresh "v" in let Hv := fresh "Hv" in
        destruct (b64A_table_nth (bv_unsigned b) ltac:(pose proof (bv_unsigned_in_range 8 b); lia)) as [v Hv];
        let RD2 := fresh "RD" in
        pose proof (u8ro_read bsegs _ 660960 b64A_table (bv_unsigned b) v (Z_to_bv 64 (660960 + bv_unsigned b))
                      (b64A_table_at _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 I))))))) Hv ltac:(pose proof (bv_unsigned_in_range 8 b); lia) eq_refl) as RD2;
        zstep; clear RD2;
        let R := fresh "R" in
        pose proof (bv_unsigned_in_range 8 v) as R; unfold bv_modulus in R; change (2 ^ Z.of_N 8) with 256 in R;
        tpos; kont (bv_unsigned v) ].

    Lemma db_loop_s4 : forall mX zA zB zC x11 x21,
      INV mX -> 0 <= zA <= 255 -> 0 <= zB <= 255 -> 0 <= zC <= 255 ->
      evt bsegs POST (ST 0x332da8 mX NTBL (Z_to_bv 64 (4 * Q - 4)) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j0)) x11 (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j0 + 4 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 zC) SHBv TBL (Z_to_bv 64 zA) (Z_to_bv 64 zB) (Z_to_bv 64 (C + 4 + j0 + 4 * q + 2)) x21 (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (3 * q)) (Z_to_bv 64 2) (Z_to_bv 64 (-1))).
    Proof.
      intros mX zA zB zC x11 x21 I H1 H2 H3. prep I.
      zstep. zstep. if_cases KV; zify_cond KV. { exfalso. rewrite ?unsigned_lit in KV by lia. lia. }
      zstep.

      conv_siteX I ltac:(do 3 zstep) (J + 3) (C + 4 + j0 + 4 * q + 3) ltac:(idtac) ltac:(idtac; zstep) ltac:(fun z => eapply (db_loop_tail mX zA zB zC z); first [exact I | lia]).
    Qed.

    Lemma db_loop_s3 : forall mX zA zB x11 x12' x21,
      INV mX -> 0 <= zA <= 255 -> 0 <= zB <= 255 ->
      evt bsegs POST (ST 0x332d60 mX NTBL (Z_to_bv 64 (4 * Q - 4)) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j0)) x11 (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j0 + 4 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 (C + 4 + j0 + 4 * q + 1)) SHBv TBL (Z_to_bv 64 zA) (Z_to_bv 64 zB) x12' x21 (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (3 * q)) (Z_to_bv 64 2) (Z_to_bv 64 (-1))).
    Proof.
      intros mX zA zB x11 x12' x21 I H1 H2. prep I.
      zstep. zstep. if_cases KV; zify_cond KV. { exfalso. rewrite ?unsigned_lit in KV by lia. lia. }
      zstep.
      conv_siteX I ltac:(do 3 zstep) (J + 2) (C + 4 + j0 + 4 * q + 2) ltac:(idtac) ltac:(idtac; zstep) ltac:(fun z => eapply (db_loop_s4 mX zA zB z); first [exact I | lia]).
    Qed.

    Lemma db_loop_s2 : forall mX zA x11 x19 x20 x21,
      INV mX -> 0 <= zA <= 255 ->
      evt bsegs POST (ST 0x332d24 mX NTBL (Z_to_bv 64 (4 * Q - 4)) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j0)) x11 (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j0 + 4 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 (C + 4 + j0 + 4 * q + 1)) SHBv TBL (Z_to_bv 64 zA) x19 x20 x21 (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (3 * q)) (Z_to_bv 64 2) (Z_to_bv 64 (-1))).
    Proof.
      intros mX zA x11 x19 x20 x21 I H1. prep I.
      conv_siteX I ltac:(do 3 zstep) (J + 1) (C + 4 + j0 + 4 * q + 1) ltac:(idtac) ltac:(idtac; zstep) ltac:(fun z => eapply (db_loop_s3 mX zA z); first [exact I | lia]).
    Qed.

    Lemma db_loop_head : forall mX x9 x13 x15 x18 x19 x20 x21,
      INV mX ->
      evt bsegs POST (ST 0x332cd0 mX NTBL (Z_to_bv 64 (4 * Q - 4)) (Z_to_bv 64 (4 * q)) x9 (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (T + 3 * q)) x13
                         (Z_to_bv 64 eofv) x15 SHBv TBL x18 x19 x20 x21 (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (3 * q)) (Z_to_bv 64 2) (Z_to_bv 64 (-1))).
    Proof.
      intros mX x9 x13 x15 x18 x19 x20 x21 I. prep I.
      zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. rewrite ?unsigned_lit in KU by lia. lia. }
      zstep.
      conv_siteX I ltac:(do 3 zstep) (j0 + 4 * q) (C + 4 + j0 + 4 * q)
        ltac:(idtac; zstep; (let KV := fresh "KV" in if_cases KV; zify_cond KV; [exfalso; rewrite ?unsigned_lit in KV by lia; lia|]))
        ltac:(idtac; zstep; (let KV := fresh "KV" in if_cases KV; zify_cond KV; [exfalso; rewrite ?unsigned_lit in KV by lia; lia|]); zstep)
        ltac:(fun z => eapply (db_loop_s2 mX z); first [exact I | lia]).
    Qed.
  End Loop.

  Lemma db_loop : forall (k : nat) Q j0 eofv q, Z.to_nat (Q - q) = k ->
    0 <= j0 -> j0 + 4 * Q <= n0 -> -1 <= eofv <= 2 -> LOOPH Q j0 eofv q.
  Proof.
    induction k as [k IH] using lt_wf_ind; intros Q j0 eofv q HK Hj0 HjQ He.
    intros mX x9 x13 x15 x18 x19 x20 x21 I Hq HqQ.
    eapply (db_loop_head Q j0 eofv q); [lia | | exact I].
    eapply (IH (Z.to_nat (Q - (q + 1)))); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma db_chk : forall mX nn j0 eofv x7 x9 x12 x13 x15 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mX -> 0 <= nn -> 0 <= j0 -> j0 + nn <= n0 -> -1 <= eofv <= 2 ->
    evt bsegs POST (ST 0x332c70 mX NTBL (Z_to_bv 64 nn) x7 x9 (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 T) x12 x13 (Z_to_bv 64 eofv) x15 SHBv TBL
                       x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mX nn j0 eofv x7 x9 x12 x13 x15 x18 x19 x20 x21 x28 x29 x30 x31 I Hnn Hj0 Hj He.
    assert (HD : 0 <= n0 / 4) by (apply Z.div_pos; lia).
    zstep. zstep. if_cases K3; zify_cond K3.
    - assert (HM : nn = 4 * (nn / 4)).
      { revert K3. rewrite ?unsigned_lit by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. intros K3.
        pose proof (Z.div_mod nn 4 ltac:(lia)). lia. }
      zstep.

      assert (SW0 : bv_swrap 32 (nn + 0) = nn) by (rewrite Z.add_0_r; apply ubs_sw32; lia). rewrite SW0.
      zstep. if_cases K0; zify_cond K0.
      + do 2 zstep. eapply db_ret; [exact I | right; rewrite ?unsigned_lit in K0 by lia; lia].
      + zstep.
        assert (SW : bv_swrap 32 (nn + -4) = 4 * (nn / 4) - 4) by (rewrite ubs_sw32 by lia; lia). rewrite SW.
        zstep. if_cases KT; zify_cond KT; signed_lits_in KT. { exfalso. rewrite ?signed_of_Z in KT by lia. lia. }
        zstep. if_cases K5; zify_cond K5; signed_lits_in K5.
        * do 2 zstep.
          replace (Z_to_bv 64 T) with (Z_to_bv 64 (T + 3 * 0)) by (f_equal; lia).
          change (Z_to_bv 64 0) with (Z_to_bv 64 (3 * 0)).
          eapply (db_last _ 0 eofv j0); first [exact I | lia].
        * do 6 zstep.
          replace (Z_to_bv 64 T) with (Z_to_bv 64 (T + 3 * 0)) by (f_equal; lia).
          change (Z_to_bv 64 0) with (Z_to_bv 64 (4 * 0)).

          eapply (db_loop (Z.to_nat (nn / 4 - 0)) (nn / 4) j0 eofv 0); first [exact I | reflexivity | lia].
    - zstep. eapply db_ret; [exact I | left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma db_tt : forall (k : nat) mX nn j0 eofv t1v x9 x18 x19 x20 x21 x31,
    INV mX -> Z.to_nat nn = k -> 0 <= nn -> t1v = Z.min nn 3 -> 0 <= j0 -> j0 + nn <= n0 -> -1 <= eofv <= 2 ->
    evt bsegs POST (ST 0x332bd8 mX NTBL (Z_to_bv 64 t1v) (Z_to_bv 64 4) x9 (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4 + j0 + nn + -1)) (Z_to_bv 64 nn) (Z_to_bv 64 eofv)
                       (Z_to_bv 64 nn) SHBv TBL x18 x19 x20 x21 (Z_to_bv 64 (C + 4 + j0 + nn + -1)) (Z_to_bv 64 1) (Z_to_bv 64 224) x31).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros mX nn j0 eofv t1v x9 x18 x19 x20 x21 x31 I HK Hnn HT1 Hj0 Hj He. prep I.
    zstep. if_cases K4; zify_cond K4; signed_lits_in K4.
    - rewrite ?signed_of_Z in K4 by lia. replace t1v with nn by lia. eapply (db_chk _ nn j0 eofv); first [exact I | lia].
    - rewrite ?signed_of_Z in K4 by lia.
      zstep. if_cases KU1; zify_cond KU1. { exfalso. rewrite ?unsigned_lit in KU1 by lia. lia. }
      zstep. zstep.

      replace (C + 4 + j0 + nn + -1 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      zstep. zstep. th_if_lit.
      zstep. if_cases KU2; zify_cond KU2. { exfalso. rewrite ?unsigned_lit in KU2 by lia. lia. }
      do 3 zstep. zstep. th_if_lit.
      destruct (nth_error ed (Z.to_nat (j0 + nn - 1))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      pose proof (u8ro_read bsegs _ (C + 4) ed (j0 + nn - 1) b (Z_to_bv 64 (C + 4 + j0 + nn + -1)) FB Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep.
      destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota.
      + do 2 zstep. eapply (db_chk _ nn j0 eofv); first [exact I | lia].
      + rewrite EQ. zstep. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
        zstep. do 3 zstep. zstep. th_if_lit.
        destruct (b64A_table_nth (bv_unsigned b) ltac:(lia)) as [v Hv].
        pose proof (u8ro_read bsegs _ 660960 b64A_table (bv_unsigned b) v (Z_to_bv 64 (660960 + bv_unsigned b)) (b64A_table_at _ MI) Hv ltac:(lia) eq_refl) as RD2.
        zstep. clear RD2.
        do 5 zstep.

        assert (SW : bv_swrap 32 (nn + -1) = nn - 1) by (rewrite ubs_sw32 by lia; lia). rewrite SW.
        zstep. if_cases KB.
        * replace (nn + -1) with (nn - 1) by lia. replace (C + 4 + j0 + nn + -2) with (C + 4 + j0 + (nn - 1) + -1) by lia.
          eapply (IH (Z.to_nat (nn - 1))); first [exact I | reflexivity | lia].
        * do 2 zstep. eapply (db_chk _ nn j0 eofv); first [exact I | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma db_tt_entry : forall mX nn j0 eofv x6 x7 x9 x12 x15 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mX -> 0 <= nn -> 0 <= j0 -> j0 + nn <= n0 -> -1 <= eofv <= 2 ->
    evt bsegs POST (ST 0x332ba8 mX NTBL x6 x7 x9 (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 T) x12 (Z_to_bv 64 nn) (Z_to_bv 64 eofv)
                       x15 SHBv TBL x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mX nn j0 eofv x6 x7 x9 x12 x15 x18 x19 x20 x21 x28 x29 x30 x31 I Hnn Hj0 Hj He.
    assert (L32 : Z.land nn 4294967295 = nn).
    { change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    do 4 zstep. rewrite ?L32.
    zstep.

    if_cases K3; zify_cond K3; signed_lits_in K3; rewrite ?signed_of_Z in K3 by lia.
    - do 4 zstep. replace (0 <? C + 4 + j0) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. do 2 zstep.
      eapply (db_tt (Z.to_nat nn) _ nn j0 eofv nn); first [exact I | reflexivity | lia].
    - zstep. do 4 zstep. replace (0 <? C + 4 + j0) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. do 2 zstep.
      eapply (db_tt (Z.to_nat nn) _ nn j0 eofv 3); first [exact I | reflexivity | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma db_ws : forall (k : nat) mX i eofv x9 x18 x19 x20 x21 x29 x30 x31,
    INV mX -> Z.to_nat (n0 - i) = k -> 0 <= i < n0 -> -1 <= eofv <= 2 ->
    evt bsegs POST (ST 0x332b18 mX NTBL (Z_to_bv 64 224) (Z_to_bv 64 (-1)) x9 (Z_to_bv 64 (C + 4 + n0)) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4 + i)) (Z_to_bv 64 (n0 - i)) (Z_to_bv 64 eofv)
                       (Z_to_bv 64 (C + 4 + i)) SHBv TBL x18 x19 x20 x21 (Z_to_bv 64 1) x29 x30 x31).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros mX i eofv x9 x18 x19 x20 x21 x29 x30 x31 I HK Hi He. prep I.
    assert (HD : 0 <= n0 / 4) by (apply Z.div_pos; lia).
    zstep. if_cases KN; zify_cond KN. { exfalso. rewrite ?unsigned_lit in KN by lia. lia. }
    zstep. do 3 zstep. zstep. th_if_lit.
    destruct (nth_error ed (Z.to_nat i)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
    pose proof (u8ro_read bsegs _ (C + 4) ed i b (Z_to_bv 64 (C + 4 + i)) FB Hb ltac:(lia) eq_refl) as RD.
    zstep. clear RD. zstep.
    destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota.
    - do 3 zstep. eapply (db_tt_entry _ (n0 - i) i eofv); first [exact I | lia].
    - rewrite EQ. zstep. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
      zstep. do 3 zstep. zstep. th_if_lit.
      destruct (b64A_table_nth (bv_unsigned b) ltac:(lia)) as [v Hv].
      pose proof (u8ro_read bsegs _ 660960 b64A_table (bv_unsigned b) v (Z_to_bv 64 (660960 + bv_unsigned b)) (b64A_table_at _ MI) Hv ltac:(lia) eq_refl) as RD2.
      zstep. clear RD2.
      zstep. if_cases KW.
      + do 3 zstep. eapply (db_tt_entry _ (n0 - i) i eofv); first [exact I | lia].
      + zstep. if_cases KV; zify_cond KV. { exfalso. rewrite ?unsigned_lit in KV by lia. lia. }
        do 3 zstep.
        assert (SW : bv_swrap 32 (n0 - i + -1) = n0 - (i + 1)) by (rewrite ubs_sw32 by lia; lia).
        rewrite SW. replace (C + 4 + i + 1) with (C + 4 + (i + 1)) by lia.
        zstep. if_cases K1; zify_cond K1; signed_lits_in K1; rewrite ?signed_of_Z in K1 by lia.
        * eapply (IH (Z.to_nat (n0 - (i + 1)))); first [exact I | reflexivity | lia].
        * do 2 zstep. replace (n0 - (i + 1)) with 0 by lia.
          eapply (db_tt_entry _ 0 n0 eofv); first [exact I | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dblock_body : forall bs0 eofv t0 t1 t2 a5 a6 a7 t3 t4 t5 t6,
    ro_cells bsegs m C (ectx_cells num ed ln (Z_to_bv 64 0)) -> rw_cells bsegs m T [CB K bs0] -> stk bsegs m lo SP -> mem_inv bsegs m ->
    img_untouched m -> ro_cells bsegs m 6943544 [C8 (Z_to_bv 64 2147450880)] ->
    -1 <= eofv <= 2 ->
    evt bsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4)) (Z_to_bv 64 n0) (Z_to_bv 64 eofv) a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x332a8c) fc None m (seg_rom bsegs)).
  Proof.
    intros bs0 eofv t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 CTX DST ST MI UT SHC He.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM. pose proof HWS as HWS'.
    assert (HWU : ut_fp W) by (clear - AB TIM; ut_fp_lia).
    pose proof (rw_cells_CB_length bsegs _ _ _ _ DST) as LBS. apply u8arr_of_rw_cells in DST.
    pose proof (ectxA_data m C num ed ln _ LED CTX) as FB.
    pose proof CTX as CTXb.
    apply (ro_cells_congr bsegs m C _ [C4 num; CB 80 ed; C4 ln; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in CTXb;
      [| reflexivity | cbn; rewrite LED; tauto].
    unfold ectx_cells in CTX.
    th_frame 56%nat [8; 8; 8; 8; 8; 8; 8]%nat ST.
    do 9 ths.
    do 3 zstep.
    zstep. if_cases KC; zify_cond KC. { exfalso. lia. }
    zstep. zstep. ubs_if.
    zstep. chk_pass ACC_C (C + 88) 4 0x332adc 15 17.
    do 2 zstep. zstep. th_if_lit.
    do 3 zstep. zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (I : INV mX) end.
    { fold (ectx_cells num ed ln (Z_to_bv 64 0)) in CTX.
      split; [exact CTX|]. split; [exact FB|]. split; [exists bs0; split; [exact DST | exact LBS]|]. split; [exact FR|]. split; [exact ST|].
      split; [exact MI|]. split; [|exact WM]. exact MU. }
    clear CTX CTXb FB DST FR ST MI MU WM.
    zstep. if_cases KN; zify_cond KN; signed_lits_in KN.
    - do 2 zstep.
      replace (Z_to_bv 64 (C + 4)) with (Z_to_bv 64 (C + 4 + 0)) by (f_equal; lia).
      eapply (db_tt_entry _ n0 0 eofv); first [exact I | lia].
    - do 5 zstep.
      replace (Z_to_bv 64 (C + 4)) with (Z_to_bv 64 (C + 4 + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 n0) with (Z_to_bv 64 (n0 - 0)) by (f_equal; lia).
      eapply (db_ws (Z.to_nat (n0 - 0)) _ 0 eofv); first [exact I | reflexivity | lia].
  Qed.
End Proofs.

(* [comment removed for export] *)
Definition dblock_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (C T : Z) (K : nat) (n0 eofv : Z) (num ln : word) (ed bs0 : list byte) (lo : Z),
    a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 T -> a2 = Z_to_bv 64 (C + 4) -> a3 = Z_to_bv 64 n0 -> a4 = Z_to_bv 64 eofv ->
    ro_cells bsegs m C (ectx_cells num ed ln (Z_to_bv 64 0)) -> length ed = 80%nat -> 0 < C -> C mod 8 = 0 -> C + 92 <= lo -> acc bsegs m C 92 ->
    rw_cells bsegs m T [CB K bs0] -> 0 < T -> T + Z.of_nat K <= lo -> acc bsegs m T (Z.of_nat K) ->
    (T + Z.of_nat K <= 0x10000 \/ 0xbf8000 <= T) -> (T + Z.of_nat K <= 0x7fff8000 \/ 0x10007fff8000 <= T) ->
    (C + 92 <= T \/ T + Z.of_nat K <= C) ->
    0 <= n0 <= 80 -> 3 * (n0 / 4) <= Z.of_nat K -> -1 <= eofv <= 2 ->
    acc bsegs m 660960 128 ->
    img_untouched m -> ro_cells bsegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk bsegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv bsegs m ->
    evt bsegs (dblock_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C T K n0 num ln ed lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_evp_decodeblock_int) fc None m (seg_rom bsegs)).

Theorem dblock_proof : dblock_stmt.
Proof.
  unfold dblock_stmt, g_shadow_memory_dynamic_address, SHB, e_evp_decodeblock_int. intros until lo.
  intros -> -> -> -> -> CTX LED HC CAL CLO ACC_C DST HT0 TLO ACC_T TIM TSH SEP HN HK HE ACC_B UT SHC ST LO0 LO HTOP MI.
  pose proof (rw_cells_bound _ _ _ _ DST) as TB. cbn [cells_size csize Nat.add] in TB.
  eapply (dblock_body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m C T K n0 num ln ed lo); try eassumption; lia.
Qed.

