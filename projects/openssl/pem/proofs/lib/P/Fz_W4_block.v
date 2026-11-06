(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Arr SFModel.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_W4_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition dblock_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (C T : Z) (K : nat) (n0 : Z) (num ln : word) (ed : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (dl : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 (bs' : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dl) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (T, T + 3 * (n0 / 4))] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ (dl = -1 \/ 0 <= dl <= 3 * (n0 / 4))
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ ro_cells psegs m' C (ectx_cells num ed ln (Z_to_bv 64 0))
    /\ rw_cells psegs m' T [CB K bs'].

Section Proofs.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (C T : Z) (K : nat) (n0 : Z) (num ln : word) (ed : list byte) (lo : Z).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 16, bv_unsigned sp); (T, T + 3 * (n0 / 4))]%Z.
  Hypothesis AB : 0 <= n0 <= 80 /\ 3 * (n0 / 4) <= Z.of_nat K /\ 0 < C /\ C + 92 <= 2 ^ 64 /\ 0 <= T /\ T + Z.of_nat K <= 2 ^ 64
                  /\ 0 <= lo /\ lo <= SP - 16 /\ SP < 2 ^ 64.
  Hypothesis SEP_CT : C + 92 <= T \/ T + Z.of_nat K <= C.
  Hypothesis SEP_CS : C + 92 <= lo \/ SP <= C.
  Hypothesis SEP_TS : T + Z.of_nat K <= lo \/ SP <= T.
  Hypothesis LED : length ed = 80%nat.

  Notation POST := (dblock_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc C T K n0 num ln ed lo m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 sp s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition INV (mX : mem) : Prop :=
    ro_cells psegs mX C (ectx_cells num ed ln (Z_to_bv 64 0)) /\ bytes_at psegs mX (C + 4) ed
    /\ (exists bs, u8arr psegs mX T bs /\ length bs = K)
    /\ rw_cells psegs mX (SP + -16) [C8 s0; C8 ra] /\ stk psegs mX lo (SP + -16)
    /\ mem_inv psegs mX /\ munch W m mX /\ wmono psegs m mX.

  Ltac open_inv H := destruct H as (CTX & FB & (bs & DST & LBS) & FR & ST & MI & MU & WM).

  Lemma inv_store_ok : forall mX k a, INV mX -> 0 <= k < 3 * (n0 / 4) -> a = wa (T + k) -> store_ok psegs mX a 1 = true.
  Proof.
    intros mX k a I Hk Ha; open_inv I.
    eapply (u8arr_store_ok_n psegs mX T bs k 1 a DST); [lia | rewrite LBS; lia | exact Ha].
  Qed.

  Lemma inv_store : forall mX k a b, INV mX -> 0 <= k < 3 * (n0 / 4) -> a = wa (T + k) -> INV (write_to_mem mX a [b]).
  Proof.
    intros mX k a b I Hk Ha. pose proof (inv_store_ok mX k a I Hk Ha) as SOK. open_inv I. subst a.
    assert (HED : 0 <= C + 4 /\ C + 4 + Z.of_nat (length ed) <= 2 ^ 64) by (rewrite LED; lia).
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - apply ro_cells_frame; [exact CTX | lia | cbn [length]; lia | cbn [length cells_size ectx_cells csize Nat.add]; lia].
    - apply bytes_at_write_other; [exact FB | lia | cbn [length]; lia | cbn [length]; rewrite LED; lia].
    - exists (upd_bytes bs (Z.to_nat k) [b]). split.
      + apply (u8arr_write_bytes psegs mX T bs k [b] DST); [lia | cbn [length]; rewrite LBS; lia].
      + rewrite upd_bytes_length; [exact LBS | cbn [length]; rewrite LBS; lia].
    - apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [length cells_size csize Nat.add]; lia].
    - apply stk_write; [exact ST | lia | cbn [length]; lia].
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU | lia | cbn [length]; lia |]. cbn [inside length]. right. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma db_ret : forall mX dl x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30,
    INV mX -> (dl = -1 \/ 0 <= dl <= 3 * (n0 / 4)) ->
    evt psegs POST (ST 0x174cb8 mX x5 x6 x7 (Z_to_bv 64 dl) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30).
  Proof.
    intros mX dl x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 I Hdl; open_inv I.
    do 4 ths.
    release_frame FR ST (bv_unsigned sp).
    apply rw_cells_of_u8arr in DST. rewrite LBS in DST.
    apply evt_done. exists dl. do 13 eexists. exists bs. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact Hdl|]. split; [exact ST|]. split; [exact CTX | exact DST].
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
  Lemma db_last_sw : forall mX q e x5 x6 x7 x10 x12 x15 x16 x17 x28 x29 x30,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> 0 <= e <= 2 ->
    evt psegs POST (ST 0x174c78 mX x5 x6 x7 x10 (Z_to_bv 64 (T + 3 * q)) x12 (Z_to_bv 64 (3 + 3 * q)) (Z_to_bv 64 e) x15 x16 x17 x28 x29 x30).
  Proof.
    intros mX q e x5 x6 x7 x10 x12 x15 x16 x17 x28 x29 x30 I Hq Hn He.
    assert (HQ : q + 1 <= n0 / 4) by (apply Z.div_le_lower_bound; lia).
    assert (SW : bv_swrap 32 (3 + 3 * q - e) = 3 + 3 * q - e).
    { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
      rewrite Z.mod_small by lia. lia. }
    do 3 zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep.
      stb I (3 * q) (T + 3 * q).
      stb I (3 * q + 1) (T + 3 * q + 1).
      stb I (3 * q + 2) (T + 3 * q + 2).
      do 2 zstep. rewrite SW.
      eapply db_ret; [exact I | right; lia].
    - do 2 zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        stb I (3 * q) (T + 3 * q).
        zstep. rewrite SW.
        eapply db_ret; [exact I | right; lia].
      + (* [comment removed for export] *)
        zstep.
        stb I (3 * q) (T + 3 * q).
        stb I (3 * q + 1) (T + 3 * q + 1).
        do 2 zstep. rewrite SW.
        eapply db_ret; [exact I | right; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma db_last_tail : forall mX q eofv z1 z2 z3 z4 x7 x12 x15 x28 x29 x30,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 ->
    0 <= z1 <= 255 -> 0 <= z2 <= 255 -> 0 <= z3 <= 255 -> 0 <= z4 <= 255 ->
    evt psegs POST (ST 0x174c34 mX (Z_to_bv 64 z4) (Z_to_bv 64 z3) x7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) x12 (Z_to_bv 64 (3 + 3 * q))
                       (Z_to_bv 64 eofv) x15 (Z_to_bv 64 z2) (Z_to_bv 64 z1) x28 x29 x30).
  Proof.
    intros mX q eofv z1 z2 z3 z4 x7 x12 x15 x28 x29 x30 I Hq Hn He H1 H2 H3 H4.
    do 5 zstep. if_cases KS.
    - eapply db_ret; [exact I | left; reflexivity].
    - do 6 zstep.
      destruct (Z.eq_dec eofv (-1)) as [-> | NE].
      + zstep. th_if_lit.
        do 5 zstep.
        eapply (db_last_sw mX q); [exact I | exact Hq | exact Hn |].
        destruct (Z.land (z4 + -61) 18446744073709551615 <? 1); destruct (Z.land (z3 + -61) 18446744073709551615 <? 1); cbn [Z.b2z]; lia.
      + zstep. if_cases KE; zify_cond KE. 2:{ exfalso. lia. }
        eapply (db_last_sw mX q eofv); [exact I | exact Hq | exact Hn | lia].
  Qed.
  (* [comment removed for export] *)
  Ltac conv_site I jj ADDR pre kont :=
    let b := fresh "b" in let Hb := fresh "Hb" in
    destruct (nth_error ed (Z.to_nat jj)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia];
    let RD := fresh "RD" in
    pose proof (u8ro_read psegs _ (C + 4) ed jj b (Z_to_bv 64 ADDR) (proj1 (proj2 I)) Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
    zstep; clear RD; pre; zstep;
    let SB := fresh "SB" in let HB := fresh "HB" in let EQ := fresh "EQ" in
    destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota;
    [ kont 255
    | rewrite EQ; zstep;
      let v := fresh "v" in let Hv := fresh "Hv" in
      destruct (b64_table_nth (bv_unsigned b) ltac:(pose proof (bv_unsigned_in_range 8 b); lia)) as [v Hv];
      let RD2 := fresh "RD" in
      pose proof (u8ro_read psegs _ B64_TABLE b64_table (bv_unsigned b) v (Z_to_bv 64 (B64_TABLE + bv_unsigned b))
                    (b64_table_at _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 I))))))) Hv ltac:(pose proof (bv_unsigned_in_range 8 b); lia) eq_refl) as RD2;
      zstep; clear RD2;
      let R := fresh "R" in
      pose proof (bv_unsigned_in_range 8 v) as R; unfold bv_modulus in R; change (2 ^ Z.of_N 8) with 256 in R;
      kont (bv_unsigned v) ].

  (* [comment removed for export] *)
  Lemma db_last_s4 : forall mX q eofv j z1 z2 z3 x7 x28 x29 x30,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 -> 0 <= j -> j + 4 <= n0 ->
    0 <= z1 <= 255 -> 0 <= z2 <= 255 -> 0 <= z3 <= 255 ->
    evt psegs POST (ST 0x174c24 mX (Z_to_bv 64 255) (Z_to_bv 64 z3) x7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j)) (Z_to_bv 64 (3 + 3 * q))
                       (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 z2) (Z_to_bv 64 z1) x28 x29 x30).
  Proof.
    intros mX q eofv j z1 z2 z3 x7 x28 x29 x30 I Hq Hn He Hj Hj4 H1 H2 H3.
    conv_site I (j + 3) (C + 4 + j + 3) ltac:(idtac) ltac:(fun z => eapply (db_last_tail mX q eofv z1 z2 z3 z); first [exact I | lia]).
  Qed.
  Lemma db_last_s3 : forall mX q eofv j z1 z2 x5 x6 x7 x28 x29 x30,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 -> 0 <= j -> j + 4 <= n0 ->
    0 <= z1 <= 255 -> 0 <= z2 <= 255 ->
    evt psegs POST (ST 0x174c0c mX x5 x6 x7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j)) (Z_to_bv 64 (3 + 3 * q))
                       (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 z2) (Z_to_bv 64 z1) x28 x29 x30).
  Proof.
    intros mX q eofv j z1 z2 x5 x6 x7 x28 x29 x30 I Hq Hn He Hj Hj4 H1 H2.
    conv_site I (j + 2) (C + 4 + j + 2) ltac:(do 2 zstep) ltac:(fun z => eapply (db_last_s4 mX q eofv j z1 z2 z); first [exact I | lia]).
  Qed.

  Lemma db_last_s2 : forall mX q eofv j z1 x5 x6 x7 x28 x29 x30,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 -> 0 <= j -> j + 4 <= n0 ->
    0 <= z1 <= 255 ->
    evt psegs POST (ST 0x174bfc mX x5 x6 x7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j)) (Z_to_bv 64 (3 + 3 * q))
                       (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 255) (Z_to_bv 64 z1) x28 x29 x30).
  Proof.
    intros mX q eofv j z1 x5 x6 x7 x28 x29 x30 I Hq Hn He Hj Hj4 H1.
    conv_site I (j + 1) (C + 4 + j + 1) ltac:(idtac) ltac:(fun z => eapply (db_last_s3 mX q eofv j z1 z); first [exact I | lia]).
  Qed.

  (* [comment removed for export] *)
  Lemma db_last : forall mX q eofv j x5 x6 x7 x16 x17 x28 x29 x30,
    INV mX -> 0 <= q -> 4 * (q + 1) <= n0 -> -1 <= eofv <= 2 -> 0 <= j -> j + 4 <= n0 ->
    evt psegs POST (ST 0x174be4 mX x5 x6 x7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + j)) (Z_to_bv 64 (3 + 3 * q))
                       (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE) x16 x17 x28 x29 x30).
  Proof.
    intros mX q eofv j x5 x6 x7 x16 x17 x28 x29 x30 I Hq Hn He Hj Hj4.
    conv_site I j (C + 4 + j) ltac:(do 2 zstep) ltac:(fun z => eapply (db_last_s2 mX q eofv j z); first [exact I | lia]).
  Qed.
  (* [comment removed for export] *)
  Definition LOOPH (Q j0 eofv q : Z) : Prop :=
    forall mX x5 x6 x7 x28 x29 x30,
      INV mX -> 0 <= q -> q + 1 < Q ->
      evt psegs POST (ST 0x174b28 mX x5 x6 x7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + (j0 + 4 * q))) (Z_to_bv 64 (3 + 3 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (4 * Q - 4)) x28 x29 x30).

  Section Loop.
    Variables (Q j0 eofv q : Z).
    Hypothesis HQ : 0 <= q /\ q + 1 < Q /\ 0 <= j0 /\ j0 + 4 * Q <= n0 /\ -1 <= eofv <= 2.
    Hypothesis NEXT : LOOPH Q j0 eofv (q + 1).

    (* [comment removed for export] *)
    Lemma db_loop_tail : forall mX z1 z2 z3 z4 x29 x30,
      INV mX -> 0 <= z1 <= 255 -> 0 <= z2 <= 255 -> 0 <= z3 <= 255 -> 0 <= z4 <= 255 ->
      evt psegs POST (ST 0x174b78 mX (Z_to_bv 64 z2) (Z_to_bv 64 z1) (Z_to_bv 64 z4) (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q))
                         (Z_to_bv 64 (C + 4 + (j0 + 4 * q))) (Z_to_bv 64 (3 + 3 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (4 * Q - 4)) (Z_to_bv 64 z3) x29 x30).
    Proof.
      intros mX z1 z2 z3 z4 x29 x30 I H1 H2 H3 H4.
      assert (HQ4 : q + 1 <= n0 / 4) by (apply Z.div_le_lower_bound; lia).
      do 5 zstep. if_cases KS.
      - eapply db_ret; [exact I | left; reflexivity].
      - do 11 zstep.
        stb I (3 * q) (T + 3 * q).
        stb I (3 * q + 1) (T + 3 * q + 1).
        stb I (3 * q + 2) (T + 3 * q + 2).
        do 3 zstep.
        assert (SW : bv_swrap 32 (4 * q + 4) = 4 * q + 4).
        { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
          rewrite Z.mod_small by lia. lia. }
        rewrite SW.
        replace (T + 3 * q + 3) with (T + 3 * (q + 1)) by lia.
        replace (3 + 3 * q + 3) with (3 + 3 * (q + 1)) by lia.
        replace (C + 4 + (j0 + 4 * q) + 4) with (C + 4 + (j0 + 4 * (q + 1))) by lia.
        replace (4 * q + 4) with (4 * (q + 1)) by lia.
        if_cases KL; zify_cond KL; signed_lits_in KL.
        + eapply NEXT; [exact I | lia | lia].
        + do 2 zstep.
          eapply (db_last _ (q + 1) eofv (j0 + 4 * (q + 1))); first [exact I | lia].
    Qed.
    Notation J := (j0 + 4 * q).

    Lemma db_loop_s4 : forall mX z1 z2 z3 x29 x30,
      INV mX -> 0 <= z1 <= 255 -> 0 <= z2 <= 255 -> 0 <= z3 <= 255 ->
      evt psegs POST (ST 0x174b68 mX (Z_to_bv 64 z2) (Z_to_bv 64 z1) (Z_to_bv 64 255) (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q))
                         (Z_to_bv 64 (C + 4 + J)) (Z_to_bv 64 (3 + 3 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (4 * Q - 4)) (Z_to_bv 64 z3) x29 x30).
    Proof.
      intros mX z1 z2 z3 x29 x30 I H1 H2 H3.
      conv_site I (J + 3) (C + 4 + J + 3) ltac:(idtac) ltac:(fun z => eapply (db_loop_tail mX z1 z2 z3 z); first [exact I | lia]).
    Qed.

    Lemma db_loop_s3 : forall mX z1 z2 x7 x28 x29 x30,
      INV mX -> 0 <= z1 <= 255 -> 0 <= z2 <= 255 ->
      evt psegs POST (ST 0x174b50 mX (Z_to_bv 64 z2) (Z_to_bv 64 z1) x7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q))
                         (Z_to_bv 64 (C + 4 + J)) (Z_to_bv 64 (3 + 3 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (4 * Q - 4)) x28 x29 x30).
    Proof.
      intros mX z1 z2 x7 x28 x29 x30 I H1 H2.
      conv_site I (J + 2) (C + 4 + J + 2) ltac:(do 2 zstep) ltac:(fun z => eapply (db_loop_s4 mX z1 z2 z); first [exact I | lia]).
    Qed.

    Lemma db_loop_s2 : forall mX z1 x7 x28 x29 x30,
      INV mX -> 0 <= z1 <= 255 ->
      evt psegs POST (ST 0x174b40 mX (Z_to_bv 64 255) (Z_to_bv 64 z1) x7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q))
                         (Z_to_bv 64 (C + 4 + J)) (Z_to_bv 64 (3 + 3 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (4 * Q - 4)) x28 x29 x30).
    Proof.
      intros mX z1 x7 x28 x29 x30 I H1.
      conv_site I (J + 1) (C + 4 + J + 1) ltac:(idtac) ltac:(fun z => eapply (db_loop_s3 mX z1 z); first [exact I | lia]).
    Qed.

    Lemma db_loop_head : forall mX x5 x6 x7 x28 x29 x30,
      INV mX ->
      evt psegs POST (ST 0x174b28 mX x5 x6 x7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (T + 3 * q)) (Z_to_bv 64 (C + 4 + J)) (Z_to_bv 64 (3 + 3 * q))
                         (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE) (Z_to_bv 64 (4 * q)) (Z_to_bv 64 (4 * Q - 4)) x28 x29 x30).
    Proof.
      intros mX x5 x6 x7 x28 x29 x30 I.
      conv_site I (j0 + 4 * q) (C + 4 + J) ltac:(do 2 zstep) ltac:(fun z => eapply (db_loop_s2 mX z); first [exact I | lia]).
    Qed.
  End Loop.
  Lemma db_loop : forall (k : nat) Q j0 eofv q, Z.to_nat (Q - q) = k ->
    0 <= j0 -> j0 + 4 * Q <= n0 -> -1 <= eofv <= 2 -> LOOPH Q j0 eofv q.
  Proof.
    induction k as [k IH] using lt_wf_ind; intros Q j0 eofv q HK Hj0 HjQ He.
    intros mX x5 x6 x7 x28 x29 x30 I Hq HqQ.
    eapply (db_loop_head Q j0 eofv q); [lia | | exact I].
    eapply (IH (Z.to_nat (Q - (q + 1)))); lia.
  Qed.
  (* [comment removed for export] *)
  Lemma db_chk : forall mX nn j0 eofv x5 x6 x7 x10 x16 x17 x28 x29 x30,
    INV mX -> 0 <= nn -> 0 <= j0 -> j0 + nn <= n0 -> -1 <= eofv <= 2 ->
    evt psegs POST (ST 0x174b04 mX x5 x6 x7 x10 (Z_to_bv 64 T) (Z_to_bv 64 (C + 4 + j0)) (Z_to_bv 64 nn) (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE)
                       x16 x17 x28 x29 x30).
  Proof.
    intros mX nn j0 eofv x5 x6 x7 x10 x16 x17 x28 x29 x30 I Hnn Hj0 Hj He.
    assert (HD : 0 <= n0 / 4) by (apply Z.div_pos; lia).
    do 3 zstep. if_cases K3; zify_cond K3.
    - eapply db_ret; [exact I | left; reflexivity].
    - assert (HM : nn = 4 * (nn / 4)).
      { revert K3. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. intros K3.
        pose proof (Z.div_mod nn 4 ltac:(lia)). lia. }
      zstep. if_cases K0; zify_cond K0.
      + do 2 zstep. eapply db_ret; [exact I | right; lia].
      + do 2 zstep. if_cases K5; zify_cond K5; signed_lits_in K5.
        * zstep.
          replace (Z_to_bv 64 T) with (Z_to_bv 64 (T + 3 * 0)) by (f_equal; lia).
          change (Z_to_bv 64 3) with (Z_to_bv 64 (3 + 3 * 0)).
          eapply (db_last _ 0 eofv j0); first [exact I | lia].
        * do 3 zstep.
          assert (SW : bv_swrap 32 (nn + -4) = 4 * (nn / 4) - 4).
          { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
            rewrite Z.mod_small by lia. lia. }
          rewrite SW.
          replace (Z_to_bv 64 T) with (Z_to_bv 64 (T + 3 * 0)) by (f_equal; lia).
          replace (C + 4 + j0) with (C + 4 + (j0 + 4 * 0)) by lia.
          eapply (db_loop (Z.to_nat (nn / 4 - 0)) (nn / 4) j0 eofv 0); first [exact I | reflexivity | lia].
  Qed.
  (* [comment removed for export] *)
  Lemma db_tt : forall (k : nat) mX nn j0 eofv x5 x6 x7 x13 x28 x29 x30,
    INV mX -> Z.to_nat nn = k -> 4 <= nn -> 0 <= j0 -> j0 + nn <= n0 -> -1 <= eofv <= 2 ->
    evt psegs POST (ST 0x174ac8 mX x5 x6 x7 (Z_to_bv 64 nn) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4 + j0)) x13 (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE)
                       (Z_to_bv 64 4) (Z_to_bv 64 224) x28 x29 x30).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros mX nn j0 eofv x5 x6 x7 x13 x28 x29 x30 I HK Hnn Hj0 Hj He.
    do 4 zstep.
    assert (L32 : Z.land nn 4294967295 = nn).
    { change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    rewrite L32.
    destruct (nth_error ed (Z.to_nat (j0 + nn - 1))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (u8ro_read psegs _ (C + 4) ed (j0 + nn - 1) b (Z_to_bv 64 (C + 4 + j0 + nn + -1)) (proj1 (proj2 I)) Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep.
    destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota.
    - eapply (db_chk _ nn j0 eofv); first [exact I | lia].
    - rewrite EQ. zstep.
      destruct (b64_table_nth (bv_unsigned b) ltac:(pose proof (bv_unsigned_in_range 8 b); lia)) as [v Hv].
      pose proof (u8ro_read psegs _ B64_TABLE b64_table (bv_unsigned b) v (Z_to_bv 64 (B64_TABLE + bv_unsigned b))
                    (b64_table_at _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 I))))))) Hv ltac:(pose proof (bv_unsigned_in_range 8 b); lia) eq_refl) as RD2.
      zstep. clear RD2.
      do 2 zstep. if_cases KB.
      + eapply (db_chk _ nn j0 eofv); first [exact I | lia].
      + do 2 zstep.
        assert (SW : bv_swrap 32 (nn + -1) = nn - 1).
        { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
          rewrite Z.mod_small by lia. lia. }
        rewrite SW.
        if_cases K4; zify_cond K4; signed_lits_in K4.
        * eapply (IH (Z.to_nat (nn - 1))); first [exact I | reflexivity | lia].
        * do 2 zstep. eapply db_ret; [exact I | left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma db_tt_entry : forall mX nn j0 eofv x5 x6 x7 x13 x16 x17 x28 x29 x30,
    INV mX -> 0 <= nn -> 0 <= j0 -> j0 + nn <= n0 -> -1 <= eofv <= 2 ->
    evt psegs POST (ST 0x174abc mX x5 x6 x7 (Z_to_bv 64 nn) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4 + j0)) x13 (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE)
                       x16 x17 x28 x29 x30).
  Proof.
    intros mX nn j0 eofv x5 x6 x7 x13 x16 x17 x28 x29 x30 I Hnn Hj0 Hj He.
    do 2 zstep. if_cases K4; zify_cond K4.
    - zstep. eapply (db_chk _ nn j0 eofv); first [exact I | lia].
    - zstep. eapply (db_tt (Z.to_nat nn) _ nn j0 eofv); first [exact I | reflexivity | lia].
  Qed.
  (* [comment removed for export] *)
  Lemma db_ws : forall (k : nat) mX i eofv x5 x6 x7 x10 x28 x29 x30,
    INV mX -> Z.to_nat (n0 - i) = k -> 0 <= i < n0 -> -1 <= eofv <= 2 ->
    evt psegs POST (ST 0x174a94 mX x5 x6 x7 x10 (Z_to_bv 64 T) (Z_to_bv 64 (C + 4 + i)) (Z_to_bv 64 (n0 - i)) (Z_to_bv 64 eofv) (Z_to_bv 64 B64_TABLE)
                       (Z_to_bv 64 224) (Z_to_bv 64 1) x28 x29 x30).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros mX i eofv x5 x6 x7 x10 x28 x29 x30 I HK Hi He.
    assert (HD : 0 <= n0 / 4) by (apply Z.div_pos; lia).
    destruct (nth_error ed (Z.to_nat i)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (u8ro_read psegs _ (C + 4) ed i b (Z_to_bv 64 (C + 4 + i)) (proj1 (proj2 I)) Hb ltac:(lia) eq_refl) as RD.
    zstep. clear RD. do 2 zstep.
    destruct (sxb_cases b) as [[SB HB]|[SB [HB EQ]]]; rewrite SB; cbv iota.
    - eapply (db_tt_entry _ (n0 - i) i eofv); first [exact I | lia].
    - rewrite EQ. zstep.
      destruct (b64_table_nth (bv_unsigned b) ltac:(pose proof (bv_unsigned_in_range 8 b); lia)) as [v Hv].
      pose proof (u8ro_read psegs _ B64_TABLE b64_table (bv_unsigned b) v (Z_to_bv 64 (B64_TABLE + bv_unsigned b))
                    (b64_table_at _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 I))))))) Hv ltac:(pose proof (bv_unsigned_in_range 8 b); lia) eq_refl) as RD2.
      zstep. clear RD2.
      zstep. if_cases KW.
      + eapply (db_tt_entry _ (n0 - i) i eofv); first [exact I | lia].
      + do 3 zstep.
        assert (SW : bv_swrap 32 (n0 - i + -1) = n0 - (i + 1)).
        { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 / 2)%Z with (2^31)%Z.
          rewrite Z.mod_small by lia. lia. }
        rewrite SW. replace (C + 4 + i + 1) with (C + 4 + (i + 1)) by lia.
        if_cases K1; zify_cond K1; signed_lits_in K1.
        * eapply (IH (Z.to_nat (n0 - (i + 1)))); first [exact I | reflexivity | lia].
        * do 3 zstep. eapply db_ret; [exact I | right; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma dblock_body : forall bs0 eofv t0 t1 t2 a5 a6 a7 t3 t4 t5,
    ro_cells psegs m C (ectx_cells num ed ln (Z_to_bv 64 0)) -> rw_cells psegs m T [CB K bs0] -> stk psegs m lo SP -> mem_inv psegs m ->
    -1 <= eofv <= 2 ->
    evt psegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 T) (Z_to_bv 64 (C + 4)) (Z_to_bv 64 n0) (Z_to_bv 64 eofv) a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x174a50) fc None m (seg_rom psegs)).
  Proof.
    intros bs0 eofv t0 t1 t2 a5 a6 a7 t3 t4 t5 CTX DST ST MI He.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (rw_cells_CB_length psegs _ _ _ _ DST) as LBS. apply u8arr_of_rw_cells in DST.
    pose proof (ectx_data m C num ed ln _ LED CTX) as FB.
    pose proof CTX as CTXb.
    apply (ro_cells_congr psegs m C _ [C4 num; CB 80 ed; C4 ln; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in CTXb;
      [| reflexivity | cbn; rewrite LED; tauto].
    unfold ectx_cells in CTX.
    th_frame 16%nat [8; 8]%nat ST.
    do 4 ths.
    ths. if_cases KC; zify_cond KC. { exfalso. lia. }
    do 3 ths. th_if_lit.
    do 3 ths.
    assert (I : INV m1).
    { fold (ectx_cells num ed ln (Z_to_bv 64 0)) in CTX.
      split; [exact CTX|]. split; [exact FB|]. split; [exists bs0; split; [exact DST | exact LBS]|]. split; [exact FR|]. split; [exact ST|].
      split; [exact MI|]. split; [|exact WM]. replace (SP - 16) with (SP + -16) by lia. exact MU. }
    clear CTX CTXb FB DST FR ST MI MU WM.
    if_cases KN; zify_cond KN; signed_lits_in KN.
    - do 2 zstep.
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
    ro_cells psegs m C (ectx_cells num ed ln (Z_to_bv 64 0)) -> length ed = 80%nat -> 0 < C ->
    rw_cells psegs m T [CB K bs0] ->
    0 <= n0 <= 80 -> 3 * (n0 / 4) <= Z.of_nat K -> -1 <= eofv <= 2 ->
    stk psegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
    (C + 92 <= T \/ T + Z.of_nat K <= C) ->
    (C + 92 <= lo \/ bv_unsigned sp <= C) ->
    (T + Z.of_nat K <= lo \/ bv_unsigned sp <= T) ->
    mem_inv psegs m ->
    evt psegs (dblock_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc C T K n0 num ln ed lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x174a50) fc None m (seg_rom psegs)).

Theorem dblock_proof : dblock_stmt.
Proof.
  unfold dblock_stmt. intros until lo. intros -> -> -> -> -> CTX LED HC DST HN HK HE ST LO0 LO S1 S2 S3 MI.
  pose proof (ro_cells_bound _ _ _ _ CTX) as CB. unfold ectx_cells in CB. cbn [cells_size csize Nat.add] in CB.
  pose proof (rw_cells_bound _ _ _ _ DST) as TB. cbn [cells_size csize Nat.add] in TB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply (dblock_body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m C T K n0 num ln ed lo); try eassumption; lia.
Qed.
