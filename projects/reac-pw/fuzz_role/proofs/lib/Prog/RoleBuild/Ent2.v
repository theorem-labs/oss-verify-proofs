(** ent_build's kind 2 (pod.h:297-305): an Int of m = fuzz_u8; an odd m reads v = fuzz_u32 (its missing bytes 0),
    an even m takes v = ints[(m / 2) % 14]. From the jump table's target 0x13668 to the join 0x1350c (the table
    through 0x13884 / 0x13890 .. 0x138c8, fuzz_u32 through 0x13690 .. 0x13c80, both through 0x13c90). The value
    of the four input bytes and the cursor model of fuzz_u32 are proved here too (kind 3 reads them the same way). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** ** fuzz_u32's value from its four bytes (fuzz.h:47-56), as the code joins them *)
Definition u32v (c0 c1 c2 c3 : byte) : Z :=
  bv_unsigned c0 + 256 * bv_unsigned c1 + 65536 * (bv_unsigned c2 + 256 * bv_unsigned c3).

Lemma u32_nth : forall l, fst (fuzz_u32 l) = u32v (nth 0 l NUL) (nth 1 l NUL) (nth 2 l NUL) (nth 3 l NUL).
Proof.
  intros l. destruct l as [|c0 [|c1 [|c2 [|c3 l]]]]; cbn [fuzz_u32 fuzz_u16 fuzz_u8 nth fst snd]; unfold u32v;
    try change (bv_unsigned NUL) with 0; lia.
Qed.

Lemma zxb_u : forall c : byte, bv_unsigned (zxb c) = bv_unsigned c.
Proof. intros c. unfold zxb. apply unsigned_lit. pose proof (byte_range c). lia. Qed.

Lemma lor_add : forall x y k, 0 <= k -> 0 <= x < 2^k -> 0 <= y -> Z.lor x (y * 2^k) = x + y * 2^k.
Proof.
  intros x y k Hk Hx Hy.
  assert (L : Z.land x (y * 2^k) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [Hlt|Hge].
    - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - assert (Tx : Z.testbit x i = false).
      { rewrite <- (Z.mod_small x (2^k)) by lia. apply Z.mod_pow2_bits_high. lia. }
      rewrite Tx. reflexivity. }
  rewrite <- (Z.lxor_lor _ _ L). rewrite <- (Z.add_nocarry_lxor _ _ L). reflexivity.
Qed.

(** 0x13c80 `or a1,a2,a1; or a3,a4,a3; slli a3,a3,16; or a1,a1,a3` on the bytes c0, c1 << 8, c2, c3 << 8. *)
Lemma or4_val : forall c0 c1 c2 c3 : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb c1)) 8)))
                                        (bv_unsigned (zxb c0)))))
        (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.lor
           (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb c3)) 8))) (bv_unsigned (zxb c2))))) 16)))
  = u32v c0 c1 c2 c3.
Proof.
  intros c0 c1 c2 c3.
  pose proof (byte_range c0) as B0. pose proof (byte_range c1) as B1.
  pose proof (byte_range c2) as B2. pose proof (byte_range c3) as B3.
  rewrite !zxb_u. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (bv_unsigned c1 * 2^8)) by lia.
  rewrite (unsigned_lit (bv_unsigned c3 * 2^8)) by lia.
  rewrite (Z.lor_comm (bv_unsigned c1 * 2^8)), (Z.lor_comm (bv_unsigned c3 * 2^8)).
  rewrite !lor_add by lia.
  rewrite (unsigned_lit (bv_unsigned c0 + bv_unsigned c1 * 2^8)) by lia.
  rewrite (unsigned_lit (bv_unsigned c2 + bv_unsigned c3 * 2^8)) by lia.
  rewrite (unsigned_lit ((bv_unsigned c2 + bv_unsigned c3 * 2^8) * 2^16)) by lia.
  rewrite lor_add by lia.
  unfold u32v. change (2^8) with 256. change (2^16) with 65536. lia.
Qed.

(** Two 32-bit stores of values equal mod 2^32 write the same bytes. *)
Lemma le32_mod : forall a b, a mod 2^32 = b mod 2^32 -> le32 a = le32 b.
Proof.
  intros a b H. unfold le32.
  rewrite <- (Z_to_le_bytes_mod 4 a 32), <- (Z_to_le_bytes_mod 4 b 32) by (cbn; lia). rewrite H. reflexivity.
Qed.

(** ** The model's kind 2, by the bytes the code reads *)
Lemma ent2_nil : forall b, bv_unsigned b mod 10 = 2 ->
  ent_build [b] = (Ent 4 4 (le32 (nth (Z.to_nat ((bv_unsigned NUL / 2) mod 14)) ints 0)), []).
Proof. intros b Hk. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity. Qed.

Lemma ent2_even : forall b v rest, bv_unsigned b mod 10 = 2 -> Z.odd (bv_unsigned v) = false ->
  ent_build (b :: v :: rest) = (Ent 4 4 (le32 (nth (Z.to_nat ((bv_unsigned v / 2) mod 14)) ints 0)), rest).
Proof. intros b v rest Hk Ho. unfold ent_build. cbn [fuzz_u8]. rewrite Hk, Ho. reflexivity. Qed.

Lemma ent2_odd : forall b v rest, bv_unsigned b mod 10 = 2 -> Z.odd (bv_unsigned v) = true ->
  ent_build (b :: v :: rest) =
  (Ent 4 4 (le32 (u32v (nth 0 rest NUL) (nth 1 rest NUL) (nth 2 rest NUL) (nth 3 rest NUL))), skipn 4 rest).
Proof.
  intros b v rest Hk Ho. unfold ent_build. cbn [fuzz_u8]. rewrite Hk, Ho.
  rewrite <- u32_nth, <- fuzz_u32_rest. destruct (fuzz_u32 rest). reflexivity.
Qed.

(** A register equation of a cut: literal, or arithmetic on |r|. *)
Local Ltac regeq Lr := first [ reflexivity | f_equal; rewrite ?Lr; cbn [length]; lia ].

Section Case2.
Variables (sp gp tp s7 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Local Abbreviation QE := (QJ sp gp tp s7 s9 F fc m r src pp lo (ent_build r)).
Local Abbreviation S0 := (Z_to_bv 64 (bv_unsigned sp + 0x128)).
Local Abbreviation S1 := (Z_to_bv 64 (bv_unsigned sp + 0xf0)).
Local Abbreviation S2 := (Z_to_bv 64 (0xcccccccd * 2^32)).
Local Abbreviation S8 := (Z_to_bv 64 95).
Local Abbreviation S10 := (Z_to_bv 64 10).

(** 0x13c90: type, size and the value v into e, the bytes left into 0x78(sp), to the join 0x1350c. *)
Lemma c2_fin : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1 val r',
  ent_build r = (Ent 4 4 (le32 val), r') -> le4 a1 = le32 val ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) -> a5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  t0 = Z_to_bv 64 (-0x4001) -> a6 = Z_to_bv 64 (pp + POD_LEN_OFF) -> a7 = Z_to_bv 64 (-0x3ffd) ->
  s5 = Z_to_bv 64 0x4000 -> s11 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 s4 s5 s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c90) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 m1 val r' Eb Ha1 -> -> -> -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13c90 li s3,4; sd a0,0x78(sp); mv s6,a5 *)
  step.
  pre_store HE (bv_unsigned sp + 120) 8%nat. step. mstore_out HE.
  step.
  (* sw s3,0x88(sp); sw s3,0x8c(sp); sw a1,0x90(sp) *)
  pre_store HE (bv_unsigned sp + 136) 4%nat. step. mstore_e HE 0.
  pre_store HE (bv_unsigned sp + 140) 4%nat. step. mstore_e HE 4.
  pre_store HE (bv_unsigned sp + 144) 4%nat. step. mstore_e HE 8.
  (* li s4,4; j 0x1350c *)
  do 2 step.
  eapply join_1350c; [exact Eb | reflexivity .. | | exact HW].
  eapply MemC_e_ext; [eassumption|]. rewrite Ha1, !le4_any. reflexivity.
Qed.

(** 0x138b8, the index i = (m / 2) % 14 in a1: the load of ints[i], to 0x13c90. *)
Lemma c2_tbl : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1 i r',
  0 <= i < 14 -> ent_build r = (Ent 4 4 (le32 (nth (Z.to_nat i) ints 0)), r') ->
  a1 = Z_to_bv 64 i -> a3 = Z_to_bv 64 0x108b0 ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) -> a5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  t0 = Z_to_bv 64 (-0x4001) -> a6 = Z_to_bv 64 (pp + POD_LEN_OFF) -> a7 = Z_to_bv 64 (-0x3ffd) ->
  s5 = Z_to_bv 64 0x4000 -> s11 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 s4 s5 s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x138b8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 m1 i r' Hi Eb -> -> -> -> -> -> -> -> -> MC.
  mmi.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/
               i = 11 \/ i = 12 \/ i = 13) by lia.
  clear Hi.
  (* slli a1,a1,2; addi a2,a3,-0x354; add a1,a2,a1; lw a1,0(a1); j 0x13c90 *)
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]];
    do 5 step;
    (eapply c2_fin; [exact Eb | rewrite le4_any; apply le32_mod; reflexivity | reflexivity .. | eassumption]).
Qed.

(** 0x13890, m (a byte x) in a1: s5 = 0x4000, i = (m >> 1) % 14 by the multiply (0x13894-0x138b4). *)
Lemma c2_even : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1 (x : byte) r',
  ent_build r = (Ent 4 4 (le32 (nth (Z.to_nat ((bv_unsigned x / 2) mod 14)) ints 0)), r') ->
  a1 = zxb x ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) -> a5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  t0 = Z_to_bv 64 (-0x4001) -> a6 = Z_to_bv 64 (pp + POD_LEN_OFF) -> a7 = Z_to_bv 64 (-0x3ffd) ->
  s11 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 s4 s5 s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13890) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 m1 x r' Eb -> -> -> -> -> -> -> MC.
  mmi.
  do 10 step.
  eapply c2_tbl with (i := (bv_unsigned x / 2) mod 14).
  - pose proof (Z.mod_pos_bound (bv_unsigned x / 2) 14 ltac:(lia)). lia.
  - exact Eb.
  - apply bv_eq. rewrite (unsigned_lit ((bv_unsigned x / 2) mod 14))
      by (pose proof (Z.mod_pos_bound (bv_unsigned x / 2) 14 ltac:(lia)); lia).
    clear - x. revert x. byte_eq.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - eassumption.
Qed.

(** 0x13c80, fuzz_u32's bytes c0, c1 << 8, c2, c3 << 8 in a1, a2, a3, a4 (the missing ones 0). *)
Lemma c2_or : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1
    (c0 c1 c2 c3 : byte) r',
  ent_build r = (Ent 4 4 (le32 (u32v c0 c1 c2 c3)), r') ->
  a1 = zxb c0 -> a2 = Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb c1)) 8) -> a3 = zxb c2 ->
  a4 = Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb c3)) 8) ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) -> a5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  t0 = Z_to_bv 64 (-0x4001) -> a6 = Z_to_bv 64 (pp + POD_LEN_OFF) -> a7 = Z_to_bv 64 (-0x3ffd) ->
  s5 = Z_to_bv 64 0x4000 -> s11 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 s3 s4 s5 s6 s7 S8 s9 S10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c80) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 m1 c0 c1 c2 c3 r' Eb
    -> -> -> -> -> -> -> -> -> -> -> MC.
  do 4 step.
  eapply c2_fin; [exact Eb | rewrite le4_any, or4_val; reflexivity | reflexivity .. | eassumption].
Qed.

Lemma case2_ok : case_at sp gp tp s7 s9 F fc m r src pp lo 2 0x13668.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 b rest m1 Er Hk Hs -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  mcells.
  (* 0x13668 ld a6,0x80(sp); ld a7,0x68(sp); ld t0,0x60(sp); beqz s5 *)
  do 4 step.
  unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) - 1)) by (rewrite Er in *; cbn [length] in *; lia).
  destruct rest as [|v rest].
  - (* no byte left: m = 0, ints[0]; 0x13884 mv a0,zero; mv a1,zero; ld s11,0x50(sp) *)
    assert (Lr : length r = 1%nat) by (rewrite Er; reflexivity).
    if_true.
    do 3 step.
    eapply c2_even with (x := NUL) (r' := []);
      [rewrite Er; apply ent2_nil; exact Hk | regeq Lr .. | eassumption].
  - assert (Lr : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    if_false.
    (* 0x13678 lbu a1,1(s6); addi a0,s4,-2; andi a2,a1,1; addi a5,s6,2; ld s11,0x50(sp); beqz a2 *)
    assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 1)) 1 = Some [v]).
    { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 1 MC) by lia. rewrite Er. reflexivity. }
    step. clear HR.
    do 5 step.
    match goal with |- context [Z.land ?E 1] =>
      replace (Z.land E 1) with (if Z.odd (bv_unsigned v) then 1 else 0) by (clear - v; revert v; byte_eq) end.
    destruct (Z.odd (bv_unsigned v)) eqn:Ho.
    + (* m odd: v = fuzz_u32; 0x13690 lui s5,4; beqz a0 *)
      if_false.
      do 2 step.
      unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) + -2)) by lia.
      destruct rest as [|c0 rest]; cbn [length] in Lr.
      * (* no byte: 0x13b8c mv a2,zero; mv a1,zero; mv a3,zero; mv a4,zero; j 0x13c80 *)
        if_true. do 5 step.
        eapply c2_or with (c0 := NUL) (c1 := NUL) (c2 := NUL) (c3 := NUL) (r' := []);
          [rewrite Er, ent2_odd by assumption; reflexivity | regeq Lr .. | eassumption].
      * (* 0x13698 lbu a1,2(s6); li a0,3; bne s4,a0 *)
        if_false.
        assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 2)) 1 = Some [c0]).
        { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 2 MC) by lia. rewrite Er. reflexivity. }
        step. clear HR. do 2 step.
        unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r))) by lia.
        destruct rest as [|c1 rest]; cbn [length] in Lr.
        -- (* one byte: 0x136a4 mv a0,zero; mv a2,zero; mv a3,zero; mv a4,zero; addi a5,s6,3; j 0x13c80 *)
           if_false. do 6 step.
           eapply c2_or with (c0 := c0) (c1 := NUL) (c2 := NUL) (c3 := NUL) (r' := []);
             [rewrite Er, ent2_odd by assumption; reflexivity | regeq Lr .. | eassumption].
        -- (* 0x13bf0 lbu a2,3(s6); slli a2,a2,8; li a0,4; bne s4,a0 *)
           if_true.
           assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 3)) 1 = Some [c1]).
           { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 3 MC) by lia. rewrite Er. reflexivity. }
           step. clear HR. do 3 step.
           unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r))) by lia.
           destruct rest as [|c2 rest]; cbn [length] in Lr.
           ++ (* two bytes: 0x13c00 mv a0,zero; mv a3,zero; mv a4,zero; addi a5,s6,4; j 0x13c80 *)
              if_false. do 5 step.
              eapply c2_or with (c0 := c0) (c1 := c1) (c2 := NUL) (c3 := NUL) (r' := []);
                [rewrite Er, ent2_odd by assumption; reflexivity | regeq Lr .. | eassumption].
           ++ (* 0x13c38 lbu a3,4(s6); li a0,5; bne s4,a0 *)
              if_true.
              assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 4)) 1 = Some [c2]).
              { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 4 MC) by lia. rewrite Er. reflexivity. }
              step. clear HR. do 2 step.
              unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r))) by lia.
              destruct rest as [|c3 rest]; cbn [length] in Lr.
              ** (* three bytes: 0x13c44 mv a0,zero; mv a4,zero; addi a5,s6,5; j 0x13c80 *)
                 if_false. do 4 step.
                 eapply c2_or with (c0 := c0) (c1 := c1) (c2 := c2) (c3 := NUL) (r' := []);
                   [rewrite Er, ent2_odd by assumption; reflexivity | regeq Lr .. | eassumption].
              ** (* four bytes: 0x13c70 lbu a4,5(s6); addi a0,s4,-6; addi a5,s6,6; slli a4,a4,8 *)
                 if_true.
                 assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 5)) 1 = Some [c3]).
                 { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 5 MC) by lia. rewrite Er. reflexivity. }
                 step. clear HR. do 3 step.
                 eapply c2_or with (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (r' := rest);
                   [rewrite Er, ent2_odd by assumption; reflexivity | regeq Lr .. | eassumption].
    + (* m even: ints[(m / 2) % 14]; to 0x13890 *)
      if_true.
      eapply c2_even with (x := v) (r' := rest);
        [rewrite Er, ent2_even by assumption; reflexivity | regeq Lr .. | eassumption].
Qed.

End Case2.
