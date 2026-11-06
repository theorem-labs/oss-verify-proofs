(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BgWords.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW2 Require W_sqr_words.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_sqr_words_aentry := 0x22b584%Z.

Notation sqr64_lo_eqm := W_sqr_words.sqr64_lo_eqm.
Notation sqr64_hi_eq := W_sqr_words.sqr64_hi_eq.
Notation sqr_words_length := W_sqr_words.sqr_words_length.
Notation sqr_words_nth_lo := W_sqr_words.sqr_words_nth_lo.
Notation sqr_words_nth_hi := W_sqr_words.sqr_words_nth_hi.
Notation firstn_S_snoc := W_sqr_words.firstn_S_snoc.

Definition aptrs2 (rp ap n lo : Z) : Prop :=
  (rp mod 8 = 0 /\ ap mod 8 = 0 /\ (rp + 8 * n <= SHLO \/ SHHI <= rp) /\ SHHI <= lo)%Z.

Definition sq_pure (rp ap n SP : Z) : Prop :=
  ((rp mod 8 = 0 /\ ap mod 8 = 0)
   /\ (0 <= rp /\ rp + 16 * n <= 140737488355328) /\ (0 <= ap /\ ap + 8 * n <= 140737488355328)
   /\ offshW [(rp, rp + 16 * n); (SP - 48, SP)])%Z.

Definition sqw_apost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rp : Z) (a : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgasegs)
    /\ munch [(rp, rp + 16 * Z.of_nat (length a)); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m m'
    /\ wmono bgasegs m m' /\ mem_inv bgasegs m'
    /\ limbs_at bgasegs m' rp (sqr_words a)
    /\ stk bgasegs m' lo (bv_unsigned sp).

Ltac cur_store_val :=
  lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Store _ _ ?rs2 _, _) =>
        let rz := eval vm_compute in (bv_unsigned rs2) in
        reg_val rz
    end end end.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + 16 * Z.of_nat (length a)); (bv_unsigned sp - 48, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A2 : bv_unsigned a2 = n.
  Hypothesis RA : limbs_at bgasegs m ap a.
  Hypothesis WR : wr_at bgasegs m rp (16 * n).
  Hypothesis DISJ : (ap + 8 * n <= rp \/ rp + 16 * n <= ap)%Z.
  Hypothesis STK : stk bgasegs m lo SP.
  Hypothesis LO : (lo <= SP - 48)%Z.
  Hypothesis SEPR : (rp + 16 * n <= SP - 48 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 48 \/ SP <= ap)%Z.
  Hypothesis MI0 : mem_inv bgasegs m.

  Hypothesis SHBC : shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACR : acc bgasegs m rp (16 * n).
  Hypothesis ACA : acc bgasegs m ap (8 * n).
  Hypothesis APT : aptrs2 rp ap (2 * n) lo.

  Notation POST := (sqw_apost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) a lo m).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Notation FCELLS jb := [CB 8 jb; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation PB := (sq_pure (bv_unsigned a0) (bv_unsigned a1) (Z.of_nat (length a)) (bv_unsigned sp)).

  Definition SINV (jb : list byte) (m1 : word -> option byte) (k : nat) : Prop :=
    limbs_at bgasegs m1 rp (firstn k (sqr_words a)) /\ limbs_at bgasegs m1 ap a /\ wr_at bgasegs m1 rp (16 * n) /\
    rw_cells bgasegs m1 (SP + -48) (FCELLS jb) /\ stk bgasegs m1 lo (SP + -48) /\ mem_inv bgasegs m1 /\
    munch W m m1 /\ wmono bgasegs m m1.

  Lemma SINV_mu : forall jb m1 k, SINV jb m1 k -> munch W m m1.
  Proof. intros jb m1 k I. unfold SINV in I. tauto. Qed.

  Lemma SINV_store : forall jb m1 k wv ad,
    SINV jb m1 k -> (Z.of_nat k < 2 * n)%Z -> wv = Z_to_bv 64 (nth k (sqr_words a) 0%Z) -> ad = (rp + 8 * Z.of_nat k)%Z ->
    store_ok bgasegs m1 (Z_to_bv 64 ad) 8 = true /\
    SINV jb (write_to_mem m1 (Z_to_bv 64 ad) (le8 wv)) (k + 1)%nat.
  Proof.
    intros jb m1 k wv ad (HW & HA & WT & FR & ST & MI & MU & WM) Hk -> ->. rewrite Nat.add_1_r.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA.
    assert (T0 : (0 <= rp)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below bgasegs m1 rp (16 * n) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    pose proof (sqr_words_length a) as LS.
    assert (L8 : length (le8 (Z_to_bv 64 (nth k (sqr_words a) 0%Z))) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bgasegs m1 (Z_to_bv 64 (rp + 8 * Z.of_nat k)) 8 = true).
    { change (Z_to_bv 64 (rp + 8 * Z.of_nat k)) with (wa (rp + 8 * Z.of_nat k)). apply (wr_at_store_ok bgasegs m1 rp (16 * n)); [exact WT | lia | lia]. }
    split; [exact SOK|].
    change (Z_to_bv 64 (rp + 8 * Z.of_nat k)) with (wa (rp + 8 * Z.of_nat k)).
    pose proof (zr_word sp) as RSP. unfold inr64 in RSP.
    unfold SINV.
    split. { rewrite firstn_S_snoc by (rewrite LS; lia).
             replace (rp + 8 * Z.of_nat k)%Z with (rp + 8 * Z.of_nat (length (firstn k (sqr_words a))))%Z by (rewrite length_firstn, LS; f_equal; lia).
             apply limbs_at_snoc_write; [exact HW | rewrite length_firstn, LS; lia]. }
    split. { apply limbs_at_write_other; [exact HA | lia | rewrite L8; lia | rewrite L8; lia]. }
    split. { apply wr_at_write. exact WT. }
    split. { apply rw_cells_frame; [exact FR | lia | rewrite L8; lia | rewrite L8; cbn; lia]. }
    split. { apply stk_write; [exact ST | lia | rewrite L8; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
    apply wmono_write. exact WM.
  Qed.

  Lemma sq_shA : forall jb m1 j (k : nat) ad,
    PB -> SINV jb m1 j -> (k < length a)%nat -> ad = wa (shad (ap + 8 * Z.of_nat k)) ->
    ov_read_bytes bgasegs m1 ad 1 = Some [z8].
  Proof.
    intros jb m1 j k ad ((R8 & A8) & BR & BA & OFF) I Hk ->.
    apply (acc_rd_limb bgasegs W m m1 ap n 0 (Z.of_nat k) _ ACA (SINV_mu _ _ _ I) OFF A8 BA);
      [ reflexivity | lia | lia | lia | rewrite Z.add_0_r; reflexivity ].
  Qed.

  Lemma sq_shR : forall jb m1 j (k : nat) ad,
    PB -> SINV jb m1 j -> (k < 2 * length a)%nat -> ad = wa (shad (rp + 8 * Z.of_nat k)) ->
    ov_read_bytes bgasegs m1 ad 1 = Some [z8].
  Proof.
    intros jb m1 j k ad ((R8 & A8) & BR & BA & OFF) I Hk ->.
    assert (ACR' : acc bgasegs m rp (8 * (2 * n))) by (replace (8 * (2 * n))%Z with (16 * n)%Z by lia; exact ACR).
    apply (acc_rd_limb bgasegs W m m1 rp (2 * n) 0 (Z.of_nat k) _ ACR' (SINV_mu _ _ _ I) OFF R8 ltac:(lia));
      [ reflexivity | lia | lia | lia | rewrite Z.add_0_r; reflexivity ].
  Qed.

  Notation ST pc mm x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 :=
    (MS (mkR ra x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgasegs)).

  Ltac sq_load I k Rx :=
    let HA := fresh "HA" in let NI := fresh "NI" in let RD := fresh "RD" in
    pose proof (proj1 (proj2 I)) as HA;
    assert (NI : nth_error a k = Some (nth k a 0%Z)) by (apply nth_error_nth'; lia);
    assert (Rx : (0 <= nth k a 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LA);
    (let ad := cur_mem_addr in
     pose proof (limbs_at_read_nth bgasegs _ ap a k _ ad HA NI ltac:(unfold wa; f_equal; lia)) as RD);
    zstep; clear RD NI HA.

  Ltac sq_store I j tac :=
    let ad := cur_mem_addr in
    let wv := cur_store_val in
    let E := lazymatch ad with Z_to_bv 64 ?E => E end in
    let SOK := fresh "SOK" in let I2 := fresh "I" in
    destruct (SINV_store _ _ j wv E I ltac:(lia) ltac:(tac) ltac:(lia)) as [SOK I2];
    zstep; clear SOK; clear I;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => let m' := fresh "m" in gen_mem mx m' end;
    rename I2 into I.
  Ltac sq_lo i Rx := rewrite (sqr_words_nth_lo a i) by lia; apply (sqr64_lo_eqm _ Rx).
  Ltac sq_hi i Rx := rewrite (sqr_words_nth_hi a i) by lia; apply (sqr64_hi_eq _ Rx).

  Ltac shA P I k := let ad := cur_mem_addr in let RD := fresh "RD" in
    pose proof (sq_shA _ _ _ k ad P I ltac:(lia) ltac:(sh_addr_k)) as RD; zstep; clear RD.
  Ltac shR P I k := let ad := cur_mem_addr in let RD := fresh "RD" in
    pose proof (sq_shR _ _ _ k ad P I ltac:(lia) ltac:(sh_addr_k)) as RD; zstep; clear RD.

  Lemma sqw_epi : forall jb m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    limbs_at bgasegs m1 rp (sqr_words a) ->
    rw_cells bgasegs m1 (SP + -48)%Z (FCELLS jb) -> stk bgasegs m1 lo (SP + -48)%Z ->
    mem_inv bgasegs m1 -> munch W m m1 -> wmono bgasegs m m1 ->
    evt bgasegs POST (ST 0x22b850 m1 SPF x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31).
  Proof.
    intros until x31. intros HP FR ST MI MU WM.
    do 6 zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    unfold sqw_apost. finish.
  Qed.

  Lemma sqw_done : forall jb m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    SINV jb m1 (2 * length a) ->
    evt bgasegs POST (ST 0x22b850 m1 SPF x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31).
  Proof.
    intros until x31. intros (HW & HA & WT & FR & ST & MI & MU & WM).
    rewrite firstn_all2 in HW by (rewrite sqr_words_length; lia).
    eapply sqw_epi; eassumption.
  Qed.

  Lemma sqw_tail : forall K (i : nat) jb m1 x7 x8 x9 x13 x18 x19 x28 x29 x30 x31,
    PB -> (length a - i = K)%nat -> (i < length a)%nat -> SINV jb m1 (2 * i) ->
    evt bgasegs POST (ST 0x22b7d4 m1 SPF (Z_to_bv 64 (rp + 16 * Z.of_nat i)) (Z_to_bv 64 (ap + 8 * Z.of_nat i)) x7 x8 x9
                         (Z_to_bv 64 (rp + 16 * Z.of_nat i)) (Z_to_bv 64 (ap + 8 * Z.of_nat i)) (Z_to_bv 64 (n - Z.of_nat i))
                         x13 (Z_to_bv 64 (shad (rp + 16 * Z.of_nat i))) (Z_to_bv 64 (shad (ap + 8 * Z.of_nat i)))
                         (Z_to_bv 64 SHB) (Z_to_bv 64 4294967295) x18 x19 x28 x29 x30 x31).
  Proof.
    induction K as [|K IH]; intros i jb m1 x7 x8 x9 x13 x18 x19 x28 x29 x30 x31 P HK Hi I; [lia|].
    pose proof P as (_ & BR & BA & _).
    shA P I i. chk0.
    shR P I (2 * i)%nat. chk0.
    sq_load I i Rx.
    do 8 zstep.
    sq_store I (2 * i)%nat ltac:(sq_lo i Rx).
    zstep.
    shR P I (2 * i + 1)%nat. chk0.
    do 4 zstep.
    zstep. rewrite (bn_swrap32_small (n - Z.of_nat i + -1)) by lia.
    do 6 zstep.
    sq_store I (2 * i + 1)%nat ltac:(sq_hi i Rx).
    zstep.
    replace (rp + 16 * Z.of_nat i + 16)%Z with (rp + 16 * Z.of_nat (S i))%Z by lia.
    replace (ap + 8 * Z.of_nat i + 8)%Z with (ap + 8 * Z.of_nat (S i))%Z by lia.
    replace (n - Z.of_nat i + -1)%Z with (n - Z.of_nat (S i))%Z by lia.
    replace (2 * i + 1 + 1)%nat with (2 * S i)%nat in I by lia.
    setreg 14%Z (Z_to_bv 64 (shad (rp + 16 * Z.of_nat (S i)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    setreg 15%Z (Z_to_bv 64 (shad (ap + 8 * Z.of_nat (S i)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
    zstep. if_cases KB; zify_cond KB.
    - eapply IH; [exact P | lia | | exact I]. rewrite ?unsigned_lit in KB by lia. lia.
    - assert (Ei : S i = length a) by (rewrite ?unsigned_lit in KB by lia; lia).
      rewrite Ei in I. eapply sqw_done. exact I.
  Qed.

  Lemma sqw_tail_setup : forall (i : nat) jb m1 x5 x6 x7 x8 x9 x13 x14 x15 x18 x19 x28 x29 x30 x31,
    PB -> (i < length a)%nat -> SINV jb m1 (2 * i) ->
    evt bgasegs POST (ST 0x22b7bc m1 SPF x5 x6 x7 x8 x9
                         (Z_to_bv 64 (rp + 16 * Z.of_nat i)) (Z_to_bv 64 (ap + 8 * Z.of_nat i)) (Z_to_bv 64 (n - Z.of_nat i))
                         x13 x14 x15 (Z_to_bv 64 SHB) (Z_to_bv 64 4294967295) x18 x19 x28 x29 x30 x31).
  Proof.
    intros i jb m1 x5 x6 x7 x8 x9 x13 x14 x15 x18 x19 x28 x29 x30 x31 P Hi I.
    pose proof P as (_ & BR & BA & _).
    do 6 zstep.
    setreg 14%Z (Z_to_bv 64 (shad (rp + 16 * Z.of_nat i))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    setreg 15%Z (Z_to_bv 64 (shad (ap + 8 * Z.of_nat i))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; clear; lia).
    eapply (sqw_tail (length a - i)); [exact P | reflexivity | exact Hi | exact I].
  Qed.

  Lemma sqw_loop4 : forall K (i : nat) jb m1 x8 x9 x13 x14 x15 x18 x19 x30 x31,
    PB -> (length a - i = K)%nat -> (i + 4 <= length a)%nat -> SINV jb m1 (2 * i) ->
    evt bgasegs POST (ST 0x22b5d8 m1 SPF (Z_to_bv 64 (8 * Z.of_nat i)) (Z_to_bv 64 4) (Z_to_bv 64 (16 * Z.of_nat i)) x8 x9
                         a0 a1 (Z_to_bv 64 (n - Z.of_nat i))
                         x13 x14 x15 (Z_to_bv 64 SHB) (Z_to_bv 64 4294967295) x18 x19
                         (Z_to_bv 64 (shad (rp + 16 * Z.of_nat i))) (Z_to_bv 64 (shad (ap + 8 * Z.of_nat i))) x30 x31).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros i jb m1 x8 x9 x13 x14 x15 x18 x19 x30 x31 P HK Hi I.
    pose proof P as (_ & BR & BA & _).
    pose proof (zr_word a0) as Z0. pose proof (zr_word a1) as Z1. unfold inr64 in Z0, Z1.

    shA P I i. zstep. chk0.
    shR P I (2 * i)%nat. zstep. chk0.
    sq_load I i Rx0.
    do 8 zstep.
    sq_store I (2 * i)%nat ltac:(sq_lo i Rx0).
    zstep.
    shR P I (2 * i + 1)%nat. chk0.
    do 7 zstep.
    sq_store I (2 * i + 1)%nat ltac:(sq_hi i Rx0).
    replace (2 * i + 1 + 1)%nat with (2 * (i + 1))%nat in I by lia.

    zstep.
    shA P I (i + 1)%nat. chk0.
    do 3 zstep.
    shR P I (2 * (i + 1))%nat. chk0.
    sq_load I (i + 1)%nat Rx1.
    do 8 zstep.
    sq_store I (2 * (i + 1))%nat ltac:(sq_lo (i + 1)%nat Rx1).
    zstep.
    shR P I (2 * (i + 1) + 1)%nat. chk0.
    do 7 zstep.
    sq_store I (2 * (i + 1) + 1)%nat ltac:(sq_hi (i + 1)%nat Rx1).
    replace (2 * (i + 1) + 1 + 1)%nat with (2 * (i + 2))%nat in I by lia.

    zstep.
    shA P I (i + 2)%nat. chk0.
    do 3 zstep.
    shR P I (2 * (i + 2))%nat. chk0.
    sq_load I (i + 2)%nat Rx2.
    do 8 zstep.
    sq_store I (2 * (i + 2))%nat ltac:(sq_lo (i + 2)%nat Rx2).
    zstep.
    shR P I (2 * (i + 2) + 1)%nat. chk0.
    do 7 zstep.
    sq_store I (2 * (i + 2) + 1)%nat ltac:(sq_hi (i + 2)%nat Rx2).
    replace (2 * (i + 2) + 1 + 1)%nat with (2 * (i + 3))%nat in I by lia.

    zstep.
    shA P I (i + 3)%nat. chk0.
    do 3 zstep.
    shR P I (2 * (i + 3))%nat. chk0.
    sq_load I (i + 3)%nat Rx3.
    do 8 zstep.
    sq_store I (2 * (i + 3))%nat ltac:(sq_lo (i + 3)%nat Rx3).
    zstep.
    shR P I (2 * (i + 3) + 1)%nat. chk0.
    do 3 zstep.
    zstep. rewrite (bn_swrap32_small (n - Z.of_nat i + -4)) by lia.
    do 5 zstep.
    sq_store I (2 * (i + 3) + 1)%nat ltac:(sq_hi (i + 3)%nat Rx3).
    zstep.
    replace (2 * (i + 3) + 1 + 1)%nat with (2 * (i + 4))%nat in I by lia.
    replace (n - Z.of_nat i + -4)%Z with (n - Z.of_nat (i + 4))%Z by lia.
    zstep. if_cases K1; zify_cond K1.
    - setreg 5%Z (Z_to_bv 64 (8 * Z.of_nat (i + 4))) ltac:(f_equal; clear; lia).
      setreg 7%Z (Z_to_bv 64 (16 * Z.of_nat (i + 4))) ltac:(f_equal; clear; lia).
      setreg 28%Z (Z_to_bv 64 (shad (rp + 16 * Z.of_nat (i + 4)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      setreg 29%Z (Z_to_bv 64 (shad (ap + 8 * Z.of_nat (i + 4)))) ltac:(f_equal; unfold shad; clear; Z.div_mod_to_equations; lia).
      eapply (IH (length a - (i + 4))%nat); [lia | exact P | reflexivity | | exact I]. rewrite ?unsigned_lit in K1 by lia. lia.
    - zstep. if_cases K2; zify_cond K2.
      + assert (Ei : (i + 4)%nat = length a) by (rewrite ?unsigned_lit in K2 by lia; lia).
        rewrite Ei in I. eapply sqw_done. exact I.
      + do 2 zstep.
        setreg 10%Z (Z_to_bv 64 (rp + 16 * Z.of_nat (i + 4))) ltac:(f_equal; clear; lia).
        setreg 11%Z (Z_to_bv 64 (ap + 8 * Z.of_nat (i + 4))) ltac:(f_equal; clear; lia).
        eapply sqw_tail_setup; [exact P | | exact I]. rewrite ?unsigned_lit in K1, K2 by lia. lia.
  Qed.

  Lemma sq_pure_intro : (0 < n)%Z -> PB.
  Proof.
    intros Hn. destruct APT as (A1 & A2' & A4 & A5).
    pose proof (wr_at_below bgasegs m rp _ MI0 WR ltac:(lia)) as TR. unfold UTOP in TR.
    assert (NA : lbytes a <> []).
    { intros E. pose proof (lbytes_lengthZ a) as L. rewrite E in L. cbn [length] in L. lia. }
    pose proof (bytes_at_below bgasegs m ap _ MI0 RA NA) as TA. rewrite lbytes_lengthZ in TA. unfold UTOP in TA.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA.
    destruct WR as (W0 & _).
    unfold sq_pure. split; [tauto|]. split; [lia|]. split; [lia|].
    cbn [offshW]. unfold SHLO, SHHI in *. split; [lia|]. split; [right; lia | exact I].
  Qed.

  Lemma bn_sqr_words_aspec :
    evt bgasegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x22b584) fc None m (seg_rom bgasegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    pose proof (zr_word a0) as R0. pose proof (zr_word a1) as R1. pose proof (zr_word sp) as RSP. unfold inr64 in R0, R1, RSP.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA.
    assert (PBn : hide ((0 < n)%Z -> PB)) by (apply hide_intro; exact sq_pure_intro).
    assert (LOHI : (17594333495296 <= lo)%Z) by (clear - APT; unfold aptrs2, SHHI in APT; tauto).
    destruct SHBC as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    carve_frame 48%nat STK.
    apply (rw_cells_split_CB bgasegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 7 zstep.
    zstep. if_cases K; zify_cond K.
    -
      assert (Ea : a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]).
      eapply sqw_epi; try eassumption.
      rewrite Ea. cbn. apply limbs_at_nil. lia.
    - assert (Hn : (0 < n)%Z) by lia.
      pose proof (hide_elim _ PBn Hn) as P. clear PBn.
      do 6 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jb :: _) =>
        assert (I : SINV jb mm (2 * 0));
        [ unfold SINV; cbn [Nat.mul firstn]; split; [apply limbs_at_nil; lia|];
          split; [eapply limbs_at_transport; [exact RA | exact MU |]; cbn [disjoint_from]; lia|]; split; [exact WR|];
          split; [exact FR|]; split; [exact STK|]; split; [exact MI0|]; split; [exact MU | exact WM] | ]
      end end.
      clear RA WR FR STK MI0 MU WM G1 G2.
      zstep. if_cases K4; zify_cond K4.
      +
        eapply evt_eq; [ | eapply (sqw_tail_setup 0%nat); [ exact P | lia | exact I ] ].
        rewrite <- A2, !Z.mul_0_r, !Z.add_0_r, Z.sub_0_r, !Z_to_bv_bv_unsigned. reflexivity.
      +
        do 6 zstep.
        setreg 28%Z (Z_to_bv 64 (shad (rp + 16 * Z.of_nat 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.mul_0_r, Z.add_0_r; clear; lia).
        setreg 29%Z (Z_to_bv 64 (shad (ap + 8 * Z.of_nat 0))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z; rewrite Z.mul_0_r, Z.add_0_r; clear; lia).
        eapply evt_eq; [ | eapply (sqw_loop4 (length a - 0)%nat 0%nat); [ exact P | reflexivity | lia | exact I ] ].
        rewrite <- A2, !Z.mul_0_r, Z.sub_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  Qed.
End Proofs.

