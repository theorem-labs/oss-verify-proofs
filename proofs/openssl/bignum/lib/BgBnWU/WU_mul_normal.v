(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import W_mul_normal.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_mul_words WU_mul_add_words WU_cmp_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_mul_normal_uentry := 0x101b9c%Z.

Section Core.
  Variables (sp a0 : word) (m : word -> option byte) (lo : Z) (A B : list Z) (PA PB : Z).
  Notation rp := (bv_unsigned a0).
  Notation SP := (bv_unsigned sp).
  Notation NA := (Z.of_nat (length A)).
  Notation NB := (Z.of_nat (length B)).
  Notation NN := (Z.of_nat (length A) + Z.of_nat (length B))%Z.
  Notation Wfin := [(bv_unsigned a0, bv_unsigned a0 + 8 * (Z.of_nat (length A) + Z.of_nat (length B))); (bv_unsigned sp - 224, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs A.
  Hypothesis LB : limbs B.
  Hypothesis DRA : (rp + 8 * NN <= PA \/ PA + 8 * NA <= rp)%Z.
  Hypothesis DRB : (rp + 8 * NN <= PB \/ PB + 8 * NB <= rp)%Z.
  Hypothesis SEPR : (rp + 8 * NN <= SP - 224 \/ SP <= rp)%Z.
  Hypothesis SEPA : (PA + 8 * NA <= SP - 224 \/ SP <= PA)%Z.
  Hypothesis SEPB : (PB + 8 * NB <= SP - 224 \/ SP <= PB)%Z.

  (* [comment removed for export] *)
  Definition UMNB (cells : list cell) (m1 : word -> option byte) : Prop :=
    limbs_at bgusegs m1 PA A /\ limbs_at bgusegs m1 PB B /\ wr_at bgusegs m1 rp (8 * NN) /\
    rw_cells bgusegs m1 (SP + -112) cells /\ stk bgusegs m1 lo (SP + -112) /\
    mem_inv bgusegs m1 /\ munch Wfin m m1 /\ wmono bgusegs m m1.
  Definition UMNI (cells : list cell) (m1 : word -> option byte) (R : list Z) : Prop :=
    limbs R /\ limbs_at bgusegs m1 rp R /\ UMNB cells m1.

  (* [comment removed for export] *)
  Lemma umn_round : forall cells m1 m2 P (i : nat) seg c fsz,
    Z.of_nat (cells_size cells) = 112%Z ->
    UMNB cells m1 -> limbs P -> limbs_at bgusegs m1 rp P -> length P = i -> (Z.of_nat i + 1 <= NB)%Z ->
    (0 <= fsz <= 112)%Z ->
    munch [(rp + 8 * Z.of_nat i, rp + 8 * Z.of_nat i + 8 * NA); (SP + -112 - fsz, SP + -112)]%Z m1 m2 ->
    wmono bgusegs m1 m2 -> mem_inv bgusegs m2 -> limbs_at bgusegs m2 (rp + 8 * Z.of_nat i) seg -> stk bgusegs m2 lo (SP + -112) ->
    limbs seg -> length seg = length A -> (0 <= c < 18446744073709551616)%Z ->
    store_ok bgusegs m2 (wa (rp + 8 * (NA + Z.of_nat i))) 8 = true /\
    UMNI cells (write_to_mem m2 (wa (rp + 8 * (NA + Z.of_nat i))) (le8 (Z_to_bv 64 c))) (P ++ seg ++ [c]).
  Proof using LA LB DRA DRB SEPR SEPA SEPB.
    intros cells m1 m2 P i seg c fsz CS (HA & HB & HW & FR & ST & MI & MU & WM) LP HP EP Hi Hf MUc WMc MIc HS STc LS ES Hc.
    subst i.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA. pose proof (limbs_at_bound _ _ _ _ HB) as BB.
    destruct HW as (W0 & W1 & HW'). pose proof (conj W0 (conj W1 HW')) as HW.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    assert (L8 : length (le8 (Z_to_bv 64 c)) = 8%nat) by apply length_le8.
    assert (HW2 : wr_at bgusegs m2 rp (8 * NN)) by (eapply wr_at_transport; [exact HW | exact WMc]).
    assert (SOK : store_ok bgusegs m2 (wa (rp + 8 * (NA + Z.of_nat (length P)))) 8 = true).
    { apply (wr_at_store_ok bgusegs m2 rp (8 * NN)); [exact HW2 | lia | lia]. }
    split; [exact SOK|].
    assert (HP2 : limbs_at bgusegs m2 rp (P ++ seg)).
    { apply limbs_at_app. split; [|exact HS].
      eapply limbs_at_transport; [exact HP | exact MUc | cbn [disjoint_from]; clear - SEPR Hi Hf; lia]. }
    split. { apply limbs_app; [exact LP|]. apply limbs_app; [exact LS|]. constructor; [unfold limb, BW; exact Hc | constructor]. }
    split.
    { rewrite app_assoc. replace (rp + 8 * (NA + Z.of_nat (length P)))%Z with (rp + 8 * Z.of_nat (length (P ++ seg)))%Z
        by (rewrite length_app, ES; lia).
      apply limbs_at_snoc_write; [exact HP2 | rewrite length_app, ES; lia]. }
    split. { apply limbs_at_write_other; [ eapply limbs_at_transport; [exact HA | exact MUc | cbn [disjoint_from]; clear - DRA SEPA Hi Hf; lia] | lia | rewrite L8; lia | rewrite L8; clear - DRA Hi; lia ]. }
    split. { apply limbs_at_write_other; [ eapply limbs_at_transport; [exact HB | exact MUc | cbn [disjoint_from]; clear - DRB SEPB Hi Hf; lia] | lia | rewrite L8; lia | rewrite L8; clear - DRB Hi; lia ]. }
    split. { apply wr_at_write. exact HW2. }
    split. { apply rw_cells_frame; [ eapply rw_cells_transport; [exact FR | exact MUc | exact WMc | cbn [disjoint_from]; rewrite CS; clear - SEPR Hi Hf; lia] | lia | rewrite L8; lia | rewrite L8, CS; clear - SEPR Hi; lia ]. }
    split. { apply stk_write; [exact STc | lia | rewrite L8; lia]. }
    split. { apply mem_inv_store; [exact MIc | rewrite L8; exact SOK]. }
    split.
    { apply munch_write; [ | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; clear - Hi; lia ].
      eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
      unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx Hi Hf. lia. }
    apply wmono_write. eapply wmono_trans; [exact WM | exact WMc].
  Qed.
End Core.

Section Mach.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A B : list Z) (wPA wPB wNA : word).
  Notation rp := (bv_unsigned a0).
  Notation SP := (bv_unsigned sp).
  Notation PA := (bv_unsigned wPA).
  Notation PB := (bv_unsigned wPB).
  Notation NA := (Z.of_nat (length A)).
  Notation NB := (Z.of_nat (length B)).
  Notation NN := (Z.of_nat (length A) + Z.of_nat (length B))%Z.
  Notation Wfin := [(bv_unsigned a0, bv_unsigned a0 + 8 * (Z.of_nat (length A) + Z.of_nat (length B))); (bv_unsigned sp - 224, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs A.
  Hypothesis LB : limbs B.
  Hypothesis N31 : (NN < 2147483648)%Z.
  Hypothesis ENA : bv_unsigned wNA = NA.
  Hypothesis DRA : (rp + 8 * NN <= PA \/ PA + 8 * NA <= rp)%Z.
  Hypothesis DRB : (rp + 8 * NN <= PB \/ PB + 8 * NB <= rp)%Z.
  Hypothesis LO : (lo <= SP - 224)%Z.
  Hypothesis SEPR : (rp + 8 * NN <= SP - 224 \/ SP <= rp)%Z.
  Hypothesis SEPA : (PA + 8 * NA <= SP - 224 \/ SP <= PA)%Z.
  Hypothesis SEPB : (PB + 8 * NB <= SP - 224 \/ SP <= PB)%Z.
  (* [comment removed for export] *)
  Hypothesis UBR : ub_ptr_ok 1 (bv_unsigned a0).
  Hypothesis UBA : ub_ptr_ok 1 (bv_unsigned wPA).
  Hypothesis UBB : ub_ptr_ok 1 (bv_unsigned wPB).
  Variable RES : list Z.

  Notation POST := (vl_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) NN 224%Z RES lo m).
  Notation FCELLS jb := [CB 8 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation KMNB jb := (UMNB sp a0 m lo A B (bv_unsigned wPA) (bv_unsigned wPB) (FCELLS jb)).
  Notation KMNI jb := (UMNI sp a0 m lo A B (bv_unsigned wPA) (bv_unsigned wPB) (FCELLS jb)).
  Notation ROUND := (umn_round sp a0 m lo A B (bv_unsigned wPA) (bv_unsigned wPB) LA LB DRA DRB SEPR SEPA SEPB).

  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 sp wPA x10 x11 x12 x13 x14 x15 x16 x17 x18 wNA x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  (* [comment removed for export] *)
  Lemma umn_ret : forall jb m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KMNI jb m1 RES ->
    evt bgusegs POST (ST 0x101c68 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros (LR & HR & HA & HB & HW & FR & ST & MI & MU & WM).
    do 15 zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  Lemma ESPc : (112 <= SP)%Z -> bv_unsigned (Z_to_bv 64 (SP + -112)) = (SP + -112)%Z.
  Proof.
    intros H. apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma umn_call : forall (ij : nat) R jb m1 w (retaddr : Z) (wr0 : word)
      x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    (ij < length B)%nat -> KMNI jb m1 R -> length R = (length A + ij)%nat -> nth_error B ij = Some w ->
    wr0 = Z_to_bv 64 (rp + 8 * Z.of_nat ij) -> ret_pc (Z_to_bv 64 retaddr) = Z_to_bv 64 retaddr ->
    (forall m2 seg c u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       mul_add_words (skipn ij R) A w = (seg, c) -> length (firstn ij R ++ seg ++ [c]) = (length A + S ij)%nat ->
       store_ok bgusegs m2 (wa (rp + 8 * (NA + Z.of_nat ij))) 8 = true ->
       KMNI jb (write_to_mem m2 (wa (rp + 8 * (NA + Z.of_nat ij))) (le8 (Z_to_bv 64 c))) (firstn ij R ++ seg ++ [c]) ->
       evt bgusegs POST
         (MS (mkR (Z_to_bv 64 retaddr) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp u0 u1 u2 x8 x9 (Z_to_bv 64 c) v1 v2 v3 v4 v5 v6 v7
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6)
             F (Z_to_bv 64 retaddr) fc None m2 (seg_rom bgusegs))) ->
    evt bgusegs POST
      (MS (mkR (Z_to_bv 64 retaddr) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 wr0 wPA wNA (Z_to_bv 64 w) x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1029c4) fc None m1 (seg_rom bgusegs)).
  Proof.
    intros until x31. intros Hi I LR Ew Ewr Eret K. subst wr0.
    pose proof I as (LRl & HR & HA & HB & HW & FR & ST & MI & MU & WM).
    pose proof (proj1 ST) as LO0.
    assert (SP112 : (112 <= SP)%Z) by (clear - LO LO0; lia).
    pose proof (ESPc SP112) as ESP.
    assert (E0 : bv_unsigned (Z_to_bv 64 (rp + 8 * Z.of_nat ij)) = (rp + 8 * Z.of_nat ij)%Z).
    { apply inr64_unsigned_lit. unfold inr64. destruct HW as (W0 & W1 & _). clear - W0 W1 Hi. lia. }
    assert (LS : length (skipn ij R) = length A) by (rewrite length_skipn; clear - LR; lia).
    pose proof (limbs_nth_error_lit B ij w LB Ew) as Rw.
    assert (Ew64 : bv_unsigned (Z_to_bv 64 w) = w) by (apply inr64_unsigned_lit; unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; exact Rw).
    eapply evt_cut.
    { eapply bn_mul_add_words_uspec with (a := A) (r := skipn ij R) (lo := lo) (m := m1).
      - exact LA.
      - apply limbs_skipn. exact LRl.
      - exact LS.
      - clear - N31. lia.
      - exact ENA.
      - exact HA.
      - rewrite E0. rewrite <- (firstn_skipn ij R) in HR. apply limbs_at_app in HR. destruct HR as [_ HR2].
        rewrite length_firstn in HR2. replace (Nat.min ij (length R)) with ij in HR2 by (clear - LR; lia). exact HR2.
      - rewrite E0. apply (wr_at_sub bgusegs m1 rp (8 * NN) (8 * Z.of_nat ij) (8 * NA) HW); clear - Hi; lia.
      - rewrite E0. unfold alias_ok. clear - DRA Hi. lia.
      - rewrite ESP. exact ST.
      - rewrite ESP. clear - LO. lia.
      - rewrite E0, ESP. clear - SEPR Hi. lia.
      - rewrite ESP. clear - SEPA. lia.
      - exact MI.
      - rewrite E0. intros _. destruct (UBR ltac:(lia)) as (NZ & AL). destruct HW as (W0 & _). split; [clear - NZ; lia | clear - AL; Z.div_mod_to_equations; lia].
      - intros _. apply UBA. lia. }
    intros ms' PO. unfold maw_upost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
    subst ms'. rewrite E0, ESP, Ew64 in *. rewrite Eret.
    pose proof (mul_add_words_spec (skipn ij R) A w (limbs_skipn _ _ LRl) LA LS Rw) as MSP.
    destruct (mul_add_words (skipn ij R) A w) as [seg c] eqn:EMA. cbn [fst snd] in *.
    destruct MSP as (Lseg & Eseg & Lc & _). unfold limb, BW in Lc.
    assert (HP1 : limbs_at bgusegs m1 rp (firstn ij R)).
    { rewrite <- (firstn_skipn ij R) in HR. apply limbs_at_app in HR. exact (proj1 HR). }
    assert (LP1 : length (firstn ij R) = ij) by (rewrite length_firstn; clear - LR; lia).
    pose proof (ROUND (FCELLS jb) m1 m2 (firstn ij R) ij seg c 112%Z eq_refl
                  (conj HA (conj HB (conj HW (conj FR (conj ST (conj MI (conj MU WM)))))))
                  (limbs_firstn _ _ LRl) HP1 LP1 ltac:(clear - Hi; lia) ltac:(lia) MUc WMc MIc HS STc Lseg Eseg Lc) as (SOK0 & I2).
    eapply K; [reflexivity | rewrite !length_app, LP1, Eseg; cbn [length]; clear; lia | exact SOK0 | exact I2].
  Qed.

  (* [comment removed for export] *)
  Ltac mn_store SOK0 I2 :=
    lazymatch type of SOK0 with
    | store_ok _ ?m2 ?a0' _ = true =>
        let ad := cur_mem_addr in
        let SOK := fresh "SOK" in
        assert (SOK : store_ok bgusegs m2 ad 8 = true) by (replace ad with a0' by (unfold wa; f_equal; lia); exact SOK0);
        replace a0' with ad in I2 by (unfold wa; f_equal; lia);
        zstep; clear SOK SOK0;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => let m' := fresh "m" in gen_mem mm m' end
    end.
  (* [comment removed for export] *)
  Ltac mn_model_step ER Ew EMA :=
    rewrite (skipn_nth_error_cons B _ _ Ew) in ER; cbn [mul_normal_loop] in ER; rewrite EMA in ER.
  Ltac mn_exit ER I2 :=
    rewrite skipn_all2 in ER by lia; cbn [mul_normal_loop] in ER; rewrite <- ER in I2; eapply umn_ret; exact I2.

  (* [comment removed for export] *)
  Lemma UPF : forall jb m1, KMNB jb m1 -> (0 < NN)%Z ->
    (0 <= rp /\ rp + 8 * NN <= 140737488355328 /\ 0 <= PB /\ PB + 8 * NB <= 18446744073709551616)%Z.
  Proof.
    intros jb m1 (HA & HB & HW & FR & ST & MI & MU & WM) HN.
    pose proof (wr_at_below bgusegs m1 rp (8 * NN) MI HW ltac:(lia)) as T. unfold UTOP in T.
    pose proof (limbs_at_bound _ _ _ _ HB) as BB. change (2 ^ 64)%Z with 18446744073709551616%Z in BB.
    destruct HW as (W0 & _). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma umn_loop : forall (K : nat) (i : nat) R jb m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    (length B - i = K)%nat -> (1 <= i < length B)%nat -> KMNI jb m1 R -> length R = (length A + i)%nat ->
    RES = mul_normal_loop A (skipn i B) R i ->
    evt bgusegs POST (ST 0x101d00 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (NB - Z.of_nat i + 1))
                       (Z_to_bv 64 (rp + 8 * (Z.of_nat i - 1))) (Z_to_bv 64 (PB + 8 * (Z.of_nat i - 1))) x22 (Z_to_bv 64 (-33)) (Z_to_bv 64 (-9))
                       (Z_to_bv 64 (8 * NA)) (Z_to_bv 64 (-17)) (Z_to_bv 64 (-25)) x28 x29 x30 x31).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros i R jb m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 HK Hi I LR ER.
    pose proof (UPF jb m1 (proj2 (proj2 I)) ltac:(clear - Hi; lia)) as P.
    (* [comment removed for export] *)
    destruct (nth_error B i) as [w0|] eqn:Ew0; [|apply nth_error_None in Ew0; exfalso; clear - Ew0 Hi; lia].
    pose proof I as (_ & _ & _ & HB & _).
    chk ltac:(fun C => clear - C P Hi; lia).
    chk ltac:(fun C => clear - C P Hi; lia).
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgusegs m1 PB B i w0 ad HB Ew0 ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD HB.
    do 6 zstep.
    eapply (umn_call i R jb m1 w0); [ clear - Hi; lia | exact I | exact LR | exact Ew0 | f_equal; clear; lia | apply ret_pc_even; [lia | reflexivity] | ].
    intros m2 seg0 c0 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 EMA0 LR0 SOK0 I2.
    mn_model_step ER Ew0 EMA0. clear I EMA0 Ew0 LR.
    chk ltac:(fun C => clear - C P Hi; lia).
    mn_store SOK0 I2.
    zstep.
    zstep. rewrite lts_signed by (clear - Hi N31; lia).
    if_cases K0; zify_cond K0.
    { mn_exit ER I2. }
    (* [comment removed for export] *)
    destruct (nth_error B (S i)) as [w1|] eqn:Ew1; [|apply nth_error_None in Ew1; exfalso; clear - Ew1 K0 Hi; lia].
    pose proof I2 as (_ & _ & _ & HB & _).
    zstep. setreg 20%Z (Z_to_bv 64 (rp + 8 * (Z.of_nat i - 1))) ltac:(f_equal; clear; lia).
    chk ltac:(fun C => clear - C P Hi K0; lia).
    chk ltac:(fun C => clear - C P Hi K0; lia).
    (let ad := cur_mem_addr in lazymatch type of HB with limbs_at _ ?mc _ _ =>
       pose proof (limbs_at_read_nth bgusegs mc PB B (S i) w1 ad HB Ew1 ltac:(unfold wa; f_equal; clear; lia)) as RD end); zstep; clear RD HB.
    do 5 zstep.
    eapply (umn_call (S i) _ jb _ w1); [ clear - K0 Hi; lia | exact I2 | exact LR0 | exact Ew1 | f_equal; clear; lia | apply ret_pc_even; [lia | reflexivity] | ].
    intros m3 seg1 c1 p0 p1 p2 q1 q2 q3 q4 q5 q6 q7 p3 p4 p5 p6 EMA1 LR1 SOK1 I3.
    mn_model_step ER Ew1 EMA1. clear I2 EMA1 Ew1 LR0.
    chk ltac:(fun C => clear - C P Hi K0; lia).
    mn_store SOK1 I3.
    zstep.
    zstep. if_cases K1; zify_cond K1.
    { mn_exit ER I3. }
    (* [comment removed for export] *)
    destruct (nth_error B (S (S i))) as [w2|] eqn:Ew2; [|apply nth_error_None in Ew2; exfalso; clear - Ew2 K0 K1 Hi; lia].
    pose proof I3 as (_ & _ & _ & HB & _).
    zstep. setreg 20%Z (Z_to_bv 64 (rp + 8 * (Z.of_nat i - 1))) ltac:(f_equal; clear; lia).
    chk ltac:(fun C => clear - C P Hi K0 K1; lia).
    chk ltac:(fun C => clear - C P Hi K0 K1; lia).
    (let ad := cur_mem_addr in lazymatch type of HB with limbs_at _ ?mc _ _ =>
       pose proof (limbs_at_read_nth bgusegs mc PB B (S (S i)) w2 ad HB Ew2 ltac:(unfold wa; f_equal; clear; lia)) as RD end); zstep; clear RD HB.
    do 5 zstep.
    eapply (umn_call (S (S i)) _ jb _ w2); [ clear - K0 K1 Hi; lia | exact I3 | exact LR1 | exact Ew2 | f_equal; clear; lia | apply ret_pc_even; [lia | reflexivity] | ].
    intros m5 seg2 c2 pp0 pp1 pp2 qq1 qq2 qq3 qq4 qq5 qq6 qq7 pp3 pp4 pp5 pp6 EMA2 LR2 SOK2 I4.
    mn_model_step ER Ew2 EMA2. clear I3 EMA2 Ew2 LR1.
    chk ltac:(fun C => clear - C P Hi K0 K1; lia).
    zstep. rewrite bn_swrap32_small by (clear - Hi N31 K0 K1; lia).
    mn_store SOK2 I4.
    zstep. if_cases K2; zify_cond K2.
    { mn_exit ER I4. }
    (* [comment removed for export] *)
    destruct (nth_error B (S (S (S i)))) as [w3|] eqn:Ew3; [|apply nth_error_None in Ew3; exfalso; clear - Ew3 K0 K1 K2 Hi; lia].
    pose proof I4 as (_ & _ & _ & HB & _).
    zstep. setreg 20%Z (Z_to_bv 64 (rp + 8 * (Z.of_nat i - 1))) ltac:(f_equal; clear; lia).
    chk ltac:(fun C => clear - C P Hi K0 K1 K2; lia).
    chk ltac:(fun C => clear - C P Hi K0 K1 K2; lia).
    (let ad := cur_mem_addr in lazymatch type of HB with limbs_at _ ?mc _ _ =>
       pose proof (limbs_at_read_nth bgusegs mc PB B (S (S (S i))) w3 ad HB Ew3 ltac:(unfold wa; f_equal; clear; lia)) as RD end); zstep; clear RD HB.
    do 5 zstep.
    eapply (umn_call (S (S (S i))) _ jb _ w3); [ clear - K0 K1 K2 Hi; lia | exact I4 | exact LR2 | exact Ew3 | f_equal; clear; lia | apply ret_pc_even; [lia | reflexivity] | ].
    intros m7 seg3 c3 ppp0 ppp1 ppp2 qqq1 qqq2 qqq3 qqq4 qqq5 qqq6 qqq7 ppp3 ppp4 ppp5 ppp6 EMA3 LR3 SOK3 I5.
    mn_model_step ER Ew3 EMA3. clear I4 EMA3 Ew3 LR2.
    chk ltac:(fun C => clear - C P Hi K0 K1 K2; lia).
    mn_store SOK3 I5.
    do 2 zstep.
    zstep. if_cases K3; zify_cond K3.
    - (* [comment removed for export] *)
      setreg 18%Z (Z_to_bv 64 (NB - Z.of_nat (S (S (S (S i)))) + 1)) ltac:(f_equal; clear; lia).
      setreg 20%Z (Z_to_bv 64 (rp + 8 * (Z.of_nat (S (S (S (S i)))) - 1))) ltac:(f_equal; clear; lia).
      setreg 21%Z (Z_to_bv 64 (PB + 8 * (Z.of_nat (S (S (S (S i)))) - 1))) ltac:(f_equal; clear; lia).
      eapply (IH (length B - S (S (S (S i))))%nat); [ clear - HK Hi; lia | reflexivity | clear - K3 K2 K1 K0 Hi; lia | exact I5 | exact LR3 | exact ER ].
    - zstep. mn_exit ER I5.
  Qed.

  (* [comment removed for export] *)
  Lemma umn_first : forall (wNB : word) jb m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x26 x27 x28 x29 x30 x31,
    bv_unsigned wNB = NB -> (1 <= length B)%nat -> KMNB jb m1 -> RES = mn_model A B ->
    evt bgusegs POST (ST 0x101c30 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 wNB a0 wPB (Z_to_bv 64 (rp + 8 * NA)) x23 x24
                       (Z_to_bv 64 (8 * NA)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros ENB HB1 IB ER.
    pose proof IB as (HA & HB & HW & FR & ST & MI & MU & WM).
    pose proof (proj1 ST) as LO0.
    assert (SP112 : (112 <= SP)%Z) by (clear - LO LO0; lia).
    pose proof (ESPc SP112) as ESP.
    pose proof (UPF jb m1 IB ltac:(clear - HB1; lia)) as P.
    destruct (UBR ltac:(lia)) as (NZR & ALR). destruct (UBA ltac:(lia)) as (NZA & ALA). destruct (UBB ltac:(lia)) as (NZB & ALB).
    destruct B as [|w0 B'] eqn:EB; [exfalso; cbn [length] in HB1; lia|]. rewrite <- EB in *.
    assert (Ew0 : nth_error B 0 = Some w0) by (rewrite EB; reflexivity).
    pose proof (limbs_nth_error_lit B 0 w0 LB Ew0) as Rw0.
    assert (Ew64 : bv_unsigned (Z_to_bv 64 w0) = w0) by (apply inr64_unsigned_lit; unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; exact Rw0).
    chk ltac:(fun C => clear - C NZB; lia).
    zstep. rewrite land7 by exact ALB.
    zstep. if_false.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgusegs m1 PB B 0 w0 ad HB Ew0
        ltac:(unfold wa; change (Z.of_nat 0) with 0%Z; rewrite Z.mul_0_r, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as RD); zstep; clear RD.
    do 4 zstep.
    eapply evt_cut.
    { eapply bn_mul_words_uspec with (a := A) (lo := lo) (m := m1).
      - exact LA.
      - clear - N31. lia.
      - exact ENA.
      - exact HA.
      - apply (wr_at_sub bgusegs m1 rp (8 * NN) 0 (8 * NA)) in HW; [rewrite Z.add_0_r in HW; exact HW | lia | lia | lia].
      - unfold alias_ok. clear - DRA. lia.
      - rewrite ESP. exact ST.
      - rewrite ESP. clear - LO. lia.
      - rewrite ESP. clear - SEPR. lia.
      - rewrite ESP. clear - SEPA. lia.
      - exact MI.
      - intros _. split; assumption.
      - intros _. split; assumption. }
    intros ms' PO. unfold mw_upost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
    subst ms'. rewrite ESP, Ew64 in *.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    pose proof (mul_words_spec A w0 LA Rw0) as MSP.
    destruct (mul_words A w0) as [seg c] eqn:EMW. cbn [fst snd] in *.
    destruct MSP as (Lseg & Eseg & Lc & _). unfold limb, BW in Lc.
    assert (MUc' : munch [(rp + 8 * Z.of_nat 0, rp + 8 * Z.of_nat 0 + 8 * NA); (SP + -112 - 96, SP + -112)]%Z m1 m2).
    { change (Z.of_nat 0) with 0%Z. rewrite Z.mul_0_r, Z.add_0_r. exact MUc. }
    assert (HS' : limbs_at bgusegs m2 (rp + 8 * Z.of_nat 0) seg) by (change (Z.of_nat 0) with 0%Z; rewrite Z.mul_0_r, Z.add_0_r; exact HS).
    pose proof (ROUND (FCELLS jb) m1 m2 [] 0%nat seg c 96%Z eq_refl IB limbs_nil
                  ltac:(apply limbs_at_nil; destruct HW as (W0 & W1 & _); lia) eq_refl ltac:(clear - HB1; lia) ltac:(lia)
                  MUc' WMc MIc HS' STc Lseg Eseg Lc) as (SOK0 & I2).
    cbn [app] in I2.
    chk ltac:(fun C => clear - C NZR; lia).
    zstep. rewrite land7 by (clear - ALR; Z.div_mod_to_equations; lia).
    zstep. if_false.
    zstep. mn_store SOK0 I2.
    assert (ER1 : RES = mul_normal_loop A (skipn 1 B) (seg ++ [c]) 1).
    { rewrite ER. unfold mn_model. rewrite EB. rewrite <- EB. rewrite EMW. rewrite EB. reflexivity. }
    assert (LR1 : length (seg ++ [c]) = (length A + 1)%nat) by (rewrite length_app, Eseg; reflexivity).
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite ENB in K.
      do 4 zstep.
      eapply evt_eq; [ | eapply (umn_loop (length B - 1)%nat 1%nat (seg ++ [c]) jb); [ reflexivity | clear - K HB1; lia | exact I2 | exact LR1 | exact ER1 ] ].
      replace (NB - Z.of_nat 1 + 1)%Z with NB by (clear; lia). rewrite <- ENB, Z_to_bv_bv_unsigned.
      change (8 * (Z.of_nat 1 - 1))%Z with 0%Z. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
    - rewrite ENB in K.
      assert (ERf : RES = seg ++ [c]).
      { rewrite ER1. rewrite skipn_all2 by (clear - K; lia). reflexivity. }
      rewrite <- ERf in I2. eapply umn_ret. exact I2.
  Qed.

  (* [comment removed for export] *)
  Lemma umn_zero : forall jb m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    length B = 0%nat -> KMNB jb m1 -> RES = mn_model A B ->
    evt bgusegs POST (ST 0x101ca4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 a0 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros HB0 IB ER.
    pose proof IB as (HA & HB & HW & FR & ST & MI & MU & WM).
    do 19 zstep.
    release_frame FR ST (bv_unsigned sp).
    eapply evt_mono.
    - eapply bn_mul_words_uspec with (a := A) (lo := lo).
      + exact LA.
      + clear - N31. lia.
      + exact ENA.
      + exact HA.
      + apply (wr_at_sub bgusegs _ rp (8 * NN) 0 (8 * NA)) in HW; [rewrite Z.add_0_r in HW; exact HW | lia | lia | lia].
      + unfold alias_ok. clear - DRA. lia.
      + exact ST.
      + clear - LO. lia.
      + clear - SEPR. lia.
      + clear - SEPA. lia.
      + exact MI.
      + intros _. apply UBR. lia.
      + intros _. apply UBA. lia.
    - intros ms' PO. unfold mw_upost, wl_post in PO.
      destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
      exists u0, u1, u2, (Z_to_bv 64 (snd (mul_words A (bv_unsigned (Z_to_bv 64 0))))), v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m2.
      split; [exact E|].
      split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
               unfold sub_fp. cbn [outside]. intros x Hx. rewrite HB0 in Hx. clear - Hx. lia. }
      split. { eapply wmono_trans; [exact WM | exact WMc]. }
      split; [exact MIc|]. split; [|exact STc].
      rewrite ER. unfold mn_model. destruct B; [|discriminate HB0]. exact HS.
  Qed.

  (* [comment removed for export] *)
  Lemma umn_mid : forall (wNB : word) jb m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    bv_unsigned wNB = NB -> KMNB jb m1 -> RES = mn_model A B ->
    evt bgusegs POST (ST 0x101c04 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 wNB a0 wPB x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros ENB IB ER.
    destruct (UBR ltac:(lia)) as (NZR & ALR).
    assert (P : (rp + 8 * NA < 18446744073709551616)%Z).
    { destruct (Z.eq_dec NN 0) as [E0|NE0].
      - pose proof (zr_word a0) as R0. unfold inr64 in R0. change (2 ^ 64)%Z with 18446744073709551616%Z in R0. clear - E0 R0. lia.
      - pose proof (UPF jb m1 IB ltac:(clear - NE0; lia)) as P. clear - P. lia. }
    zstep. rewrite ENA. replace (NA ≪ 3)%Z with (8 * NA)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    do 3 zstep.
    setreg 10%Z (Z_to_bv 64 1) ltac:(replace (0 <? rp)%Z with true by (symmetry; apply Z.ltb_lt; clear - NZR; lia); reflexivity).
    setreg 11%Z (Z_to_bv 64 0) ltac:(replace (rp + 8 * NA <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - NZR; lia); reflexivity).
    zstep. if_false.
    do 4 zstep.
    setreg 10%Z (Z_to_bv 64 1) ltac:(
      rewrite ENA;
      replace (rp + 8 * NA <? rp)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia);
      rewrite lxor_signbit' by (clear - N31; lia);
      replace (NA + 9223372036854775808 <? 9223372036854775808)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia);
      reflexivity).
    zstep. if_false.
    assert (Lw : (bv_unsigned wNB < 9223372036854775808)%Z) by (rewrite ENB; clear - N31; lia).
    assert (L0 : (bv_unsigned (Z_to_bv 64 0) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    zstep. rewrite (lts_words_small (Z_to_bv 64 0) wNB L0 Lw). rewrite ENB.
    if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      assert (HB0 : length B = 0%nat) by (clear - K2; lia).
      eapply umn_zero; [exact HB0 | exact IB | exact ER].
    - assert (HB1 : (1 <= length B)%nat) by (clear - K2; lia).
      eapply (umn_first wNB); [exact ENB | exact HB1 | exact IB | exact ER].
  Qed.
End Mach.

Section Main.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation bp := (bv_unsigned a3).
  Notation SP := (bv_unsigned sp).
  Notation NN := (Z.of_nat (length a) + Z.of_nat (length b))%Z.
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
  Hypothesis N31 : (NN < 2147483648)%Z.
  Hypothesis A2 : bv_unsigned a2 = Z.of_nat (length a).
  Hypothesis A4 : bv_unsigned a4 = Z.of_nat (length b).
  Hypothesis RA : limbs_at bgusegs m ap a.
  Hypothesis RB : limbs_at bgusegs m bp b.
  Hypothesis WR : wr_at bgusegs m rp (8 * NN).
  Hypothesis DRA : (rp + 8 * NN <= ap \/ ap + 8 * Z.of_nat (length a) <= rp)%Z.
  Hypothesis DRB : (rp + 8 * NN <= bp \/ bp + 8 * Z.of_nat (length b) <= rp)%Z.
  Hypothesis STK : stk bgusegs m lo SP.
  Hypothesis LO : (lo <= SP - 224)%Z.
  Hypothesis SEPR : (rp + 8 * NN <= SP - 224 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * Z.of_nat (length a) <= SP - 224 \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * Z.of_nat (length b) <= SP - 224 \/ SP <= bp)%Z.
  Hypothesis MI0 : mem_inv bgusegs m.
  Hypothesis UBR : ub_ptr_ok 1 (bv_unsigned a0).
  Hypothesis UBA : ub_ptr_ok 1 (bv_unsigned a1).
  Hypothesis UBB : ub_ptr_ok 1 (bv_unsigned a3).

  (* [comment removed for export] *)
  Lemma bn_mul_normal_uspec :
    evt bgusegs (vl_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) NN 224%Z (mul_normal a b) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x101b9c) fc None m (seg_rom bgusegs)).
  Proof.
    pose proof (munch_refl [(rp, rp + 8 * NN); (SP - 224, SP)]%Z m) as MU. pose proof (munch_refl [(SP - 224, SP)]%Z m) as MUF.
    pose proof (wmono_refl bgusegs m) as WM.
    carve_frame 112%nat STK.
    do 18 zstep.
    assert (RA1 : limbs_at bgusegs m0 ap a) by (eapply limbs_at_transport; [exact RA | exact MUF | cbn [disjoint_from]; clear - SEPA; lia]).
    assert (RB1 : limbs_at bgusegs m0 bp b) by (eapply limbs_at_transport; [exact RB | exact MUF | cbn [disjoint_from]; clear - SEPB; lia]).
    clear MUF.
    pose proof (zr_word a2) as R2. pose proof (zr_word a4) as R4. unfold inr64 in R2, R4.
    zstep. rewrite lts_words_small by (rewrite ?A2, ?A4; clear - N31; lia). rewrite A2, A4.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (EM : mul_normal a b = mn_model a b).
      { rewrite mul_normal_mn. destruct (Nat.ltb_spec (length a) (length b)) as [H|H]; [exfalso; clear - H K; lia | reflexivity]. }
      do 4 zstep.
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jbv :: _) =>
        eapply (umn_mid) with (A := a) (B := b) (wPA := a1) (wPB := a3) (wNA := a2) (wNB := a4) (jb := jbv) end;
        try assumption; try (clear - N31; lia).
      split; [exact RA1|]. split; [exact RB1|]. split; [exact WR|]. split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM].
    - (* [comment removed for export] *)
      assert (EM : mul_normal a b = mn_model b a).
      { rewrite mul_normal_mn. destruct (Nat.ltb_spec (length a) (length b)) as [H|H]; [reflexivity | exfalso; clear - H K; lia]. }
      do 3 zstep.
      assert (WR' : wr_at bgusegs m0 rp (8 * (Z.of_nat (length b) + Z.of_nat (length a)))).
      { replace (Z.of_nat (length b) + Z.of_nat (length a))%Z with NN by (clear; lia). exact WR. }
      assert (MU' : munch [(rp, rp + 8 * (Z.of_nat (length b) + Z.of_nat (length a))); (SP - 224, SP)]%Z m m0).
      { replace (Z.of_nat (length b) + Z.of_nat (length a))%Z with NN by (clear; lia). exact MU. }
      assert (CONV : forall ms', vl_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp
                                   (Z.of_nat (length b) + Z.of_nat (length a)) 224%Z (mul_normal a b) lo m ms' ->
                                 vl_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp NN 224%Z (mul_normal a b) lo m ms').
      { intros ms' H. replace NN with (Z.of_nat (length b) + Z.of_nat (length a))%Z by (clear; lia). exact H. }
      eapply evt_mono; [ | exact CONV ].
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jbv :: _) =>
        eapply (umn_mid) with (A := b) (B := a) (wPA := a3) (wPB := a1) (wNA := a4) (wNB := a2) (jb := jbv) end;
        try assumption; try (clear - N31; lia); try (clear - DRA DRB; lia); try (clear - SEPR; lia).
      split; [exact RB1|]. split; [exact RA1|]. split; [exact WR'|]. split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU' | exact WM].

  Qed.
End Main.
