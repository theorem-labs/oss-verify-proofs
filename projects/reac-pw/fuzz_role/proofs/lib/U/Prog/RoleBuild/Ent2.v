(** ent_build's kind 2 in the UBSan image (pod.h:298-302): an Int, m = fuzz_u8; odd m: v = fuzz_u32 (its bytes
    read ahead one at a time, 0x13aa4, 0x13bb8, 0x13cbc, 0x13d04, joined at 0x13be0); even m: v = ints[(m >> 1) % 14]
    (0x13468, the index by mulhu with the UBSan bound check on &ints[i] not taken; the load at 0x13748). From the jump
    table's target 0x13444 to the join 0x13c48 through the stores of 0x13bf0 / 0x13c38.

    Also here, shared with [Ent3]: the stores of an Int / Float ent from 0x13c38 (size 4, the 4-byte body, s9 and
    s1), a byte function of the code proved on all 256 values, and the 32-bit loads of .rodata words. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** ** Words and bytes *)
Lemma lit_eqm : forall a b, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

(** A function of the byte d (only [bv_unsigned d] in the goal), checked on its 256 values. Unlike [byte_eq] it
    abstracts d in the goal only, so hypotheses on d may stay. *)
Ltac byte_eq' d :=
  cbv delta [zxb]; unfold bv_signed; rewrite ?Z_to_bv_unsigned;
  generalize (byte_range d); generalize (bv_unsigned d);
  first [apply byte_check | apply byte_checkb]; vm_compute; reflexivity.

(** The branch condition of the goal as f, a boolean of the byte d. *)
Ltac brb d f :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => replace cnd with f by (unfold_cond; byte_eq' d)
  end.

(** The register value of the goal that is a function of d alone, written as E. *)
Ltac byte_reg d E :=
  match goal with
  | |- context [Z_to_bv 64 ?X] =>
      lazymatch X with context [d] => idtac end;
      replace (Z_to_bv 64 X) with (Z_to_bv 64 E) by (apply lit_eqm; byte_eq' d)
  end.

(** `lw` sign-extends; `sw` stores the low 32 bits, the same bytes. *)
Lemma le4_sx32 : forall w : word, le4 (sx32 w) = le4 w.
Proof.
  intros w. unfold le4, sx32. rewrite unsigned_lit_wrap.
  rewrite (Z_to_le_bytes_mod 4 _ 64) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 (bv_unsigned w)) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned w) 32) by (cbn; lia).
  f_equal. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 32) with 4294967296. change (2^32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

(** Two bytes laid side by side: an `or` of a value below 2^k and a multiple of 2^k is their sum. *)
Lemma lor_low : forall x y k, 0 <= k -> 0 <= x < 2^k -> 0 <= y -> Z.lor x (y * 2^k) = x + y * 2^k.
Proof.
  intros x y k Hk Hx Hy. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i k) as [Hl|Hg].
  - rewrite <- (Z.mod_pow2_bits_low (x + y * 2^k) k i) by lia.
    rewrite Z.mod_add by (apply Z.pow_nonzero; lia). rewrite Z.mod_small by lia.
    rewrite <- (Z.shiftl_mul_pow2 y k Hk). rewrite Z.shiftl_spec_low by lia. apply orb_false_r.
  - assert (Ex : Z.testbit x i = false).
    { destruct (Z.eq_dec x 0) as [->|Hn]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply Z.lt_le_trans with k; [apply Z.log2_lt_pow2; lia | lia]. }
    rewrite Ex, orb_false_l.
    rewrite <- (Z.shiftl_mul_pow2 y k Hk) at 1. rewrite Z.shiftl_spec by lia.
    replace i with ((i - k) + k) at 2 by lia. rewrite <- Z.div_pow2_bits by lia.
    rewrite Z.div_add by (apply Z.pow_nonzero; lia). rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma lor_byte : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor (256 * y) x = x + 256 * y.
Proof.
  intros x y Hx Hy. rewrite Z.lor_comm. replace (256 * y) with (y * 2^8) by lia.
  rewrite lor_low by (cbn; lia). lia.
Qed.

(** The value the `or`s of 0x13be0 / 0x13c20 build from four bytes (a2 and a4 shifted by 8 already). *)
Lemma or_value : forall (a1 a2 a3 a4 : word) x1 x2 x3 x4,
  bv_unsigned a1 = x1 -> bv_unsigned a2 = 256 * x2 -> bv_unsigned a3 = x3 -> bv_unsigned a4 = 256 * x4 ->
  0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> 0 <= x4 < 256 ->
  le4 (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned a2) (bv_unsigned a1))))
                         (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64
                                         (Z.lor (bv_unsigned a4) (bv_unsigned a3)))) 16)))))
  = le32 (x1 + 256 * x2 + 65536 * (x3 + 256 * x4)).
Proof.
  intros a1 a2 a3 a4 x1 x2 x3 x4 H1 H2 H3 H4 R1 R2 R3 R4.
  rewrite H1, H2, H3, H4, (lor_byte x1 x2), (lor_byte x3 x4) by lia.
  rewrite (unsigned_lit (x1 + 256 * x2)), (unsigned_lit (x3 + 256 * x4)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2^16) with 65536.
  rewrite (unsigned_lit ((x3 + 256 * x4) * 65536)) by lia.
  replace 65536 with (2^16) at 1 by reflexivity.
  rewrite lor_low by (try change (2^16) with 65536; lia).
  rewrite le4_le32. f_equal. change (2^16) with 65536. lia.
Qed.

(** ** .rodata words *)
Lemma ints_ok : ro4_ok 0x1056c ints = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ints_read : forall m1 x, mem_inv rsegs m1 -> 0 <= x < 14 ->
  ov_read_bytes rsegs m1 (wa (0x1056c + 4 * x)) 4 = Some (le4 (Z_to_bv 64 (nth (Z.to_nat x) ints 0))).
Proof.
  intros m1 x MI Hx.
  pose proof (ro4_read m1 0x1056c ints (Z.to_nat x) MI ints_ok ltac:(rewrite ints_length; lia) ltac:(lia)
                ltac:(rewrite ints_length; lia)) as H.
  rewrite Z2Nat.id in H by lia. exact H.
Qed.

(** ** The model of kind 2 *)
Lemma eb2_nil : forall b, bv_unsigned b mod 10 = 2 -> ent_build [b] = (Ent POD_INT 4 (le32 (nth 0 ints 0)), []).
Proof. intros b Hk. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity. Qed.

Lemma eb2_even : forall b c rest, bv_unsigned b mod 10 = 2 -> Z.odd (bv_unsigned c) = false ->
  ent_build (b :: c :: rest) = (Ent POD_INT 4 (le32 (nth (Z.to_nat ((bv_unsigned c / 2) mod 14)) ints 0)), rest).
Proof. intros b c rest Hk Ho. unfold ent_build. cbn [fuzz_u8]. rewrite Hk, Ho. reflexivity. Qed.

Lemma eb2_odd : forall b c rest, bv_unsigned b mod 10 = 2 -> Z.odd (bv_unsigned c) = true ->
  ent_build (b :: c :: rest) = (Ent POD_INT 4 (le32 (fst (fuzz_u32 rest))), snd (fuzz_u32 rest)).
Proof.
  intros b c rest Hk Ho. unfold ent_build. cbn [fuzz_u8]. rewrite Hk, Ho. cbn -[fuzz_u32].
  destruct (fuzz_u32 rest). reflexivity.
Qed.

(** ** The ent's stores *)
Section Tail.
Variables (sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Local Abbreviation QE := (QJ sp gp tp s11 F fc m r src pp lo (ent_build r)).

(** 0x13c38: size 4, the body word, s9 = s5, s1 = a0, the join. *)
Lemma tail_13c38 : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s9 t3 t4 t5 t6 : word) m1 ty v r',
  ent_build r = (Ent ty 4 (le32 v), r') ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  le4 a1 = le32 v ->
  MemC sp m lo m1 (Z_to_bv 64 ty) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 95) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (0xcccccccd * 2^32))
             (Z_to_bv 64 4) s4 s5 s6 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c38) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s9 t3 t4 t5 t6 m1 ty v r' Eb -> -> Ha1 MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13c38 sw s3,0xbc(sp); sw a1,0xc0(sp); mv s9,s5; mv s1,a0 *)
  est_sz HE MC. est_bd HE MC (bv_unsigned sp + 192) 0%nat 4%nat.
  do 2 step.
  eapply join_13c48; [exact Eb | reflexivity | reflexivity | reflexivity | exact MC | | | ].
  - apply le4_le32.
  - apply le4_le32.
  - cbn [e_body]. rewrite Ha1, length_le32. apply upd_zeros0. rewrite length_le32. lia.
Qed.

(** 0x13bf0: type 4 (POD_INT), then [tail_13c38]. *)
Lemma tail_13bf0 : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s9 t3 t4 t5 t6 : word) m1 v r',
  ent_build r = (Ent POD_INT 4 (le32 v), r') ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  le4 a1 = le32 v ->
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 95) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (0xcccccccd * 2^32))
             (Z_to_bv 64 4) s4 s5 s6 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13bf0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s9 t3 t4 t5 t6 m1 v r' Eb Ea0 Es5 Ha1 MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13bf0 sw s3,0xb8(sp); j 0x13c38 *)
  est_t HE MC. step.
  eapply tail_13c38; [exact Eb | exact Ea0 | exact Es5 | exact Ha1 | exact MC].
Qed.

(** 0x13be0: v = a1 | a2 | (a3 | a4) << 16 with a1, a3 bytes and a2, a4 bytes shifted by 8 (fuzz.h:49, :55). *)
Lemma or_13be0 : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s9 t3 t4 t5 t6 : word) m1 x1 x2 x3 x4 r',
  ent_build r = (Ent POD_INT 4 (le32 (x1 + 256 * x2 + 65536 * (x3 + 256 * x4))), r') ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  bv_unsigned a1 = x1 -> bv_unsigned a2 = 256 * x2 -> bv_unsigned a3 = x3 -> bv_unsigned a4 = 256 * x4 ->
  0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> 0 <= x4 < 256 ->
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 95) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (0xcccccccd * 2^32))
             (Z_to_bv 64 4) s4 s5 s6 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13be0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s9 t3 t4 t5 t6 m1 x1 x2 x3 x4 r' Eb Ea0 Es5
    H1 H2 H3 H4 R1 R2 R3 R4 MC.
  (* 0x13be0 or a1,a2,a1; or a3,a4,a3; slli a3,a3,0x10; or a1,a1,a3 *)
  do 4 step.
  eapply tail_13bf0; [exact Eb | exact Ea0 | exact Es5 | | exact MC].
  apply or_value; assumption.
Qed.

End Tail.

(** ** Walk tactics of the kind 2 / 3 cases *)
(** A zero register, a byte, or a byte shifted by 8. *)
Ltac uv := first [ reflexivity | rewrite unsigned_lit by lia; lia
                 | match goal with |- context [bv_unsigned ?d] =>
                     lazymatch type of d with byte => byte_eq' d end end ].
Ltac rg := first [ apply byte_range | lia ].
Ltac weq := first [ reflexivity | f_equal; cbn [length]; lia ].
(** After a destruct of the input's tail: the length facts with [] computed. *)
Ltac fixlen := repeat match goal with H : context [length (@nil _)] |- _ => cbn [length] in H end.

(** Input byte j, for the next lbu. *)
Ltac inb HE Er MC j :=
  let HB := fresh "HB" in
  pose proof (MemC_in_byte _ _ _ _ _ _ HE _ _ _ _ j MC ltac:(lia)) as HB;
  rewrite Er in HB; cbn [nth] in HB.

Section Case2.
Variables (sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Lemma case2_ok_sec : case_at sp gp tp s11 F fc m r src pp lo 2 0x13444.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof MC as (_ & _ & MI & _).
  destruct rest as [|c rest].
  - (* no byte for m: m = 0, ints[0] *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x13444 beqz s6 -> 0x1373c mv a0,zero; auipc/addi a1 = ints; 0x13748 lw a1,0(a1); j 0x13bf0 *)
    step. brt. do 3 step.
    pose proof (ints_read m1 0 MI ltac:(lia)) as HR. rewrite Z.mul_0_r, Z.add_0_r in HR.
    step. clear HR. step.
    eapply (tail_13bf0 sp gp tp s11 F fc m r src pp lo HE) with (v := nth 0 ints 0) (r' := []);
      [rewrite Er; apply eb2_nil; exact Hk | weq | f_equal; rewrite L; cbn [length]; lia
      | rewrite le4_sx32; apply le4_le32 | exact MC].
  - assert (L : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    (* 0x13444 beqz s6; addi s5,s5,1; addi a0,zero,1; bgeu a0,s5 (trap) *)
    step. brf. do 2 step. step. brf.
    (* 0x13454 lbu a1,1(s9); addi a0,s1,-2; andi a2,a1,1; addi s5,s9,2; bnez a2 *)
    inb HE Er MC 1%nat. step. clear HB.
    do 4 step. brb c (Z.odd (bv_unsigned c)).
    destruct (Z.odd (bv_unsigned c)) eqn:Eo; cbv iota.
    + (* odd m: fuzz_u32 *)
      destruct rest as [|d1 rest].
      * (* 0x13aa4 beqz a0 -> 0x13b5c: v = 0 *)
        fixlen. step. brt. do 5 step.
        eapply (or_13be0 sp gp tp s11 F fc m r src pp lo HE) with (x1 := 0) (x2 := 0) (x3 := 0) (x4 := 0) (r' := []);
          [rewrite Er, eb2_odd by assumption; reflexivity | weq | weq | uv | uv | uv | uv | rg | rg | rg | rg | exact MC].
      * assert (L3 : length r = S (S (S (length rest)))) by (rewrite Er; reflexivity).
        (* 0x13aa8 addi s5; addi a0,zero,1; bgeu (trap); lbu a1,2(s9); addi s5,s9,3; addi a0,zero,3; bne s1,a0 *)
        step. brf. do 2 step. step. brf.
        inb HE Er MC 2%nat. step. clear HB.
        do 3 step.
        destruct rest as [|d2 rest].
        -- (* |r| = 3: v = d1 *)
           fixlen. brf. do 5 step.
           eapply (or_13be0 sp gp tp s11 F fc m r src pp lo HE) with (x1 := bv_unsigned d1) (x2 := 0) (x3 := 0)
             (x4 := 0) (r' := []);
             [rewrite Er, eb2_odd by assumption; reflexivity | weq | weq | uv | uv | uv | uv | rg | rg | rg | rg
             | exact MC].
        -- assert (L4 : length r = S (S (S (S (length rest))))) by (rewrite Er; reflexivity).
           (* 0x13bb8 addi s5; addi a0; bgeu (trap); lbu a2,3(s9); addi s5,s9,4; slli a2,a2,8; bne s1,s3 *)
           brt. step. step. step. brf.
           inb HE Er MC 3%nat. step. clear HB.
           do 3 step.
           destruct rest as [|d3 rest].
           ++ (* |r| = 4: v = d1 + 256 d2 *)
              fixlen. brf. do 3 step.
              eapply (or_13be0 sp gp tp s11 F fc m r src pp lo HE) with (x1 := bv_unsigned d1) (x2 := bv_unsigned d2)
                (x3 := 0) (x4 := 0) (r' := []);
                [rewrite Er, eb2_odd by assumption; reflexivity | weq | weq | uv | uv | uv | uv | rg | rg | rg | rg
                | exact MC].
           ++ assert (L5 : length r = S (S (S (S (S (length rest)))))) by (rewrite Er; reflexivity).
              (* 0x13cbc addi s5; addi a0; bgeu (trap); lbu a3,4(s9); addi s5,s9,5; addi a0,zero,5; bne s1,a0 *)
              brt. step. step. step. brf.
              inb HE Er MC 4%nat. step. clear HB.
              do 3 step.
              destruct rest as [|d4 rest].
              ** (* |r| = 5: v = d1 + 256 d2 + 65536 d3 *)
                 fixlen. brf. do 3 step.
                 eapply (or_13be0 sp gp tp s11 F fc m r src pp lo HE) with (x1 := bv_unsigned d1)
                   (x2 := bv_unsigned d2) (x3 := bv_unsigned d3) (x4 := 0) (r' := []);
                   [rewrite Er, eb2_odd by assumption; reflexivity | weq | weq | uv | uv | uv | uv | rg | rg | rg
                   | rg | exact MC].
              ** assert (L6 : length r = S (S (S (S (S (S (length rest))))))) by (rewrite Er; reflexivity).
                 (* 0x13d04 addi s5; addi a0; bgeu (trap); lbu a4,5(s9); addi a0,s1,-6; addi s5,s9,6;
                    slli a4,a4,8; j 0x13be0 *)
                 brt. step. step. step. brf.
                 inb HE Er MC 5%nat. step. clear HB.
                 do 4 step.
                 eapply (or_13be0 sp gp tp s11 F fc m r src pp lo HE) with (x1 := bv_unsigned d1)
                   (x2 := bv_unsigned d2) (x3 := bv_unsigned d3) (x4 := bv_unsigned d4) (r' := rest);
                   [rewrite Er, eb2_odd by assumption; reflexivity | weq | weq | uv | uv | uv | uv | rg | rg | rg
                   | rg | exact MC].
    + (* even m: ints[(m >> 1) % 14] *)
      pose proof (Z.mod_pos_bound (bv_unsigned c / 2) 14 ltac:(lia)) as Hi.
      (* 0x13468 .. 0x13494: the index by mulhu, &ints[i], not a3,a1 *)
      do 12 step.
      byte_reg c (4 * ((bv_unsigned c / 2) mod 14)).
      (* 0x13498 bltu a3,a2 (trap); add a1,a1,a2; j 0x13748; lw a1,0(a1); j 0x13bf0 *)
      step. brf. do 2 step.
      pose proof (ints_read m1 ((bv_unsigned c / 2) mod 14) MI Hi) as HR.
      step. clear HR. step.
      eapply (tail_13bf0 sp gp tp s11 F fc m r src pp lo HE)
        with (v := nth (Z.to_nat ((bv_unsigned c / 2) mod 14)) ints 0) (r' := rest);
        [rewrite Er; apply eb2_even; assumption | weq | weq | rewrite le4_sx32; apply le4_le32 | exact MC].
Qed.

End Case2.

Theorem case2_ok : forall (sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z),
  ent_pre sp m r src pp lo -> case_at sp gp tp s11 F fc m r src pp lo 2 0x13444.
Proof. intros. apply case2_ok_sec; assumption. Qed.
