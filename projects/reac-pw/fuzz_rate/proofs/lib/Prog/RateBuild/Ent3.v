(** ent_build's kind 3 (pod.h:306-326): a Float of m = fuzz_u8; an odd m reads the bits b = fuzz_u32 (its missing
    bytes 0), m = 0xfe gives the NaN 0x7fc00000, m = 0xfc gives inf 0x7f800000, any other even m the bits
    float_bits[(m / 2) % 21]. From the jump table's target 0x13804 to the join 0x13cec (the table through 0x13a18 /
    0x13e38 .. 0x13e68, fuzz_u32 through 0x13be8 .. 0x13f3c, all through 0x13f4c). fuzz_u32's bytes as the code
    joins them: Ent2.v. Ported from reac-pw/fuzz_role's Prog/RoleBuild/Ent3.v at rate's registers (role s3 s4 s5 s6 s11 = rate s5 s6 s7 s8 s1 in the turn), frame cells (role's
    cell + 0x30) and pcs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild Require Import EntCut EntFacts Ent2.
Import ListNotations.
Open Scope Z_scope.

(** ** The model's kind 3, by the bytes the code reads *)
Lemma ent3_nil : forall b, bv_unsigned b mod 10 = 3 ->
  ent_build [b] = (Ent 6 4 (le32 (nth (Z.to_nat ((bv_unsigned NUL / 2) mod 21)) float_bits 0)), []).
Proof. intros b Hk. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity. Qed.

Lemma ent3_odd : forall b v rest, bv_unsigned b mod 10 = 3 -> Z.odd (bv_unsigned v) = true ->
  ent_build (b :: v :: rest) =
  (Ent 6 4 (le32 (u32v (nth 0 rest NUL) (nth 1 rest NUL) (nth 2 rest NUL) (nth 3 rest NUL))), skipn 4 rest).
Proof.
  intros b v rest Hk Ho. unfold ent_build. cbn [fuzz_u8]. rewrite Hk, Ho.
  rewrite <- u32_nth, <- fuzz_u32_rest. destruct (fuzz_u32 rest). reflexivity.
Qed.

Lemma ent3_nan : forall b v rest, bv_unsigned b mod 10 = 3 -> bv_unsigned v = 254 ->
  ent_build (b :: v :: rest) = (Ent 6 4 (le32 0x7fc00000), rest).
Proof. intros b v rest Hk Hv. unfold ent_build. cbn [fuzz_u8]. rewrite Hk, Hv. reflexivity. Qed.

Lemma ent3_inf : forall b v rest, bv_unsigned b mod 10 = 3 -> bv_unsigned v = 252 ->
  ent_build (b :: v :: rest) = (Ent 6 4 (le32 0x7f800000), rest).
Proof. intros b v rest Hk Hv. unfold ent_build. cbn [fuzz_u8]. rewrite Hk, Hv. reflexivity. Qed.

Lemma ent3_tbl : forall b v rest, bv_unsigned b mod 10 = 3 -> Z.odd (bv_unsigned v) = false ->
  bv_unsigned v <> 254 -> bv_unsigned v <> 252 ->
  ent_build (b :: v :: rest) = (Ent 6 4 (le32 (nth (Z.to_nat ((bv_unsigned v / 2) mod 21)) float_bits 0)), rest).
Proof.
  intros b v rest Hk Ho H254 H252. pose proof (byte_range v) as B.
  assert (E1 : (bv_unsigned v / 2 =? 127) = false).
  { apply Z.eqb_neq. intros E. assert (H : bv_unsigned v = 254 \/ bv_unsigned v = 255) by lia.
    destruct H as [H|H]; [contradiction|]. rewrite H in Ho. discriminate. }
  assert (E2 : (bv_unsigned v / 2 =? 126) = false).
  { apply Z.eqb_neq. intros E. assert (H : bv_unsigned v = 252 \/ bv_unsigned v = 253) by lia.
    destruct H as [H|H]; [contradiction|]. rewrite H in Ho. discriminate. }
  unfold ent_build. cbn [fuzz_u8]. rewrite Hk, Ho, E1, E2. reflexivity.
Qed.

(** A register equation of a cut: literal, or arithmetic on |r|. *)
Local Ltac regeq Lr := first [ reflexivity | f_equal; rewrite ?Lr; cbn [length]; lia ].

Section Case3.
Variables (sp gp tp s2 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Local Abbreviation QE := (QJ sp gp tp s2 s9 F fc m r src pp lo (ent_build r)).
Local Abbreviation S0 := (Z_to_bv 64 95).
Local Abbreviation S3 := (Z_to_bv 64 10).
Local Abbreviation S4 := (Z_to_bv 64 (0xcccccccd * 2^32)).
Local Abbreviation S10 := (Z_to_bv 64 (bv_unsigned sp + 0x158)).
Local Abbreviation S11 := (Z_to_bv 64 (bv_unsigned sp + 0x120)).

(** 0x13f4c: type, size and the bits b into e, the bytes left into 0xa8(sp), to the join 0x13cec. *)
Lemma c3_fin : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 : word) m1 val r',
  ent_build r = (Ent 6 4 (le32 val), r') -> le4 a1 = le32 val ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) -> a5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  t0 = Z_to_bv 64 (-0x4001) -> a6 = Z_to_bv 64 (pp + POD_LEN_OFF) -> a7 = Z_to_bv 64 (-0x3ffd) ->
  s7 = Z_to_bv 64 0x4000 -> s1 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 S3 S4 s5 s6 s7 s8 s9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f4c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 m1 val r' Eb Ha1 -> -> -> -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13f4c li s5,6; li s6,4; sw s5,0xb8(sp); sw s6,0xbc(sp); sw a1,0xc0(sp) *)
  do 2 step.
  pre_store HE (bv_unsigned sp + 184) 4%nat. step. mstore_e HE 0.
  pre_store HE (bv_unsigned sp + 188) 4%nat. step. mstore_e HE 4.
  pre_store HE (bv_unsigned sp + 192) 4%nat. step. mstore_e HE 8.
  (* sd a0,0xa8(sp); mv s8,a5; j 0x13cec *)
  pre_store HE (bv_unsigned sp + 168) 8%nat. step. mstore_out HE.
  do 2 step.
  eapply join_13cec; [exact Eb | reflexivity .. | | exact HW].
  eapply MemC_e_ext; [eassumption|]. rewrite Ha1, !le4_any. reflexivity.
Qed.

(** 0x13e54, the index i = (m / 2) % 21 in a1: the load of float_bits[i], to 0x13f4c. *)
Lemma c3_tbl : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 : word) m1 i r',
  0 <= i < 21 -> ent_build r = (Ent 6 4 (le32 (nth (Z.to_nat i) float_bits 0)), r') ->
  a1 = Z_to_bv 64 i ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) -> a5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  t0 = Z_to_bv 64 (-0x4001) -> a6 = Z_to_bv 64 (pp + POD_LEN_OFF) -> a7 = Z_to_bv 64 (-0x3ffd) ->
  s7 = Z_to_bv 64 0x4000 -> s1 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 S3 S4 s5 s6 s7 s8 s9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e54) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 m1 i r' Hi Eb -> -> -> -> -> -> -> -> MC.
  mmi.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/
               i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20)
    by lia.
  clear Hi.
  (* auipc a2; slli a1,a1,2; addi a2,a2,0x750; add a1,a2,a1; lw a1,0(a1); j 0x13f4c *)
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
                  [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]]];
    do 6 step;
    (eapply c3_fin; [exact Eb | rewrite le4_any; apply le32_mod; reflexivity | reflexivity .. | eassumption]).
Qed.

(** 0x13e3c, m >> 1 (m a byte x) in a1: i = (m >> 1) % 21 by the multiply (0x13e3c-0x13e50). *)
Lemma c3_half : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 : word) m1 (x : byte) r',
  ent_build r = (Ent 6 4 (le32 (nth (Z.to_nat ((bv_unsigned x / 2) mod 21)) float_bits 0)), r') ->
  a1 = Z_to_bv 64 (Z.shiftr (bv_unsigned (zxb x)) 1) ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) -> a5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  t0 = Z_to_bv 64 (-0x4001) -> a6 = Z_to_bv 64 (pp + POD_LEN_OFF) -> a7 = Z_to_bv 64 (-0x3ffd) ->
  s7 = Z_to_bv 64 0x4000 -> s1 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 S3 S4 s5 s6 s7 s8 s9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e3c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 m1 x r' Eb -> -> -> -> -> -> -> -> MC.
  mmi.
  (* auipc a2; ld a2,0x694(a2); mulhu a2,a1,a2; li a3,21; mul a2,a2,a3; sub a1,a1,a2 *)
  do 6 step.
  eapply c3_tbl with (i := (bv_unsigned x / 2) mod 21).
  - pose proof (Z.mod_pos_bound (bv_unsigned x / 2) 21 ltac:(lia)). lia.
  - exact Eb.
  - apply bv_eq. rewrite (unsigned_lit ((bv_unsigned x / 2) mod 21))
      by (pose proof (Z.mod_pos_bound (bv_unsigned x / 2) 21 ltac:(lia)); lia).
    clear - x. revert x. byte_eq.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - eassumption.
Qed.

(** 0x13f3c, fuzz_u32's bytes c0, c1 << 8, c2, c3 << 8 in a1, a2, a3, a4 (the missing ones 0). *)
Lemma c3_or : forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 : word) m1
    (c0 c1 c2 c3 : byte) r',
  ent_build r = (Ent 6 4 (le32 (u32v c0 c1 c2 c3)), r') ->
  a1 = zxb c0 -> a2 = Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb c1)) 8) -> a3 = zxb c2 ->
  a4 = Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb c3)) 8) ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) -> a5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  t0 = Z_to_bv 64 (-0x4001) -> a6 = Z_to_bv 64 (pp + POD_LEN_OFF) -> a7 = Z_to_bv 64 (-0x3ffd) ->
  s7 = Z_to_bv 64 0x4000 -> s1 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 S3 S4 s5 s6 s7 s8 s9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f3c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 m1 c0 c1 c2 c3 r' Eb
    -> -> -> -> -> -> -> -> -> -> -> MC.
  (* or a1,a2,a1; or a3,a4,a3; slli a3,a3,16; or a1,a1,a3 *)
  do 4 step.
  eapply c3_fin; [exact Eb | rewrite le4_any, or4_val; reflexivity | reflexivity .. | eassumption].
Qed.

Lemma case3_ok : case_at sp gp tp s2 s9 F fc m r src pp lo 3 0x13804.
Proof.
  intros ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 t3 t4 t5 t6 b rest m1 Er Hk Hs -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  mcells.
  (* 0x13804 ld a6,0xb0(sp); ld a7,0x98(sp); ld t0,0x90(sp); beqz s7 *)
  do 4 step.
  unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) - 1)) by (rewrite Er in *; cbn [length] in *; lia).
  destruct rest as [|v rest].
  - (* no byte left: m = 0, float_bits[0]; 0x13a18 mv a0,zero; mv a1,zero; ld s1,0x80(sp); lui s7,4;
       j 0x13e3c *)
    assert (Lr : length r = 1%nat) by (rewrite Er; reflexivity).
    if_true.
    do 5 step.
    eapply c3_half with (x := NUL) (r' := []);
      [rewrite Er; apply ent3_nil; exact Hk | regeq Lr .. | eassumption].
  - assert (Lr : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    if_false.
    (* 0x13814 lbu a1,1(s8); addi a0,s6,-2; andi a2,a1,1; addi a5,s8,2; ld s1,0x80(sp); lui s7,4; bnez a2 *)
    assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 1)) 1 = Some [v]).
    { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 1 MC) by lia. rewrite Er. reflexivity. }
    step. clear HR.
    do 6 step.
    match goal with |- context [Z.land ?E 1] =>
      replace (Z.land E 1) with (if Z.odd (bv_unsigned v) then 1 else 0) by (clear - v; revert v; byte_eq) end.
    destruct (Z.odd (bv_unsigned v)) eqn:Ho.
    + (* m odd: b = fuzz_u32; 0x13be8 beqz a0 *)
      if_true.
      step.
      unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) + -2)) by lia.
      destruct rest as [|c0 rest]; cbn [length] in Lr.
      * (* no byte: 0x13e1c mv a2,zero; mv a1,zero; mv a3,zero; mv a4,zero; j 0x13f3c *)
        if_true. do 5 step.
        eapply c3_or with (c0 := NUL) (c1 := NUL) (c2 := NUL) (c3 := NUL) (r' := []);
          [rewrite Er, ent3_odd by assumption; reflexivity | regeq Lr .. | eassumption].
      * (* 0x13bec lbu a1,2(s8); li a0,3; bne s6,a0 *)
        if_false.
        assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 2)) 1 = Some [c0]).
        { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 2 MC) by lia. rewrite Er. reflexivity. }
        step. clear HR. do 2 step.
        unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r))) by lia.
        destruct rest as [|c1 rest]; cbn [length] in Lr.
        -- (* one byte: 0x13bf8 mv a0,zero; mv a2,zero; mv a3,zero; mv a4,zero; addi a5,s8,3; j 0x13f3c *)
           if_false. do 6 step.
           eapply c3_or with (c0 := c0) (c1 := NUL) (c2 := NUL) (c3 := NUL) (r' := []);
             [rewrite Er, ent3_odd by assumption; reflexivity | regeq Lr .. | eassumption].
        -- (* 0x13e90 lbu a2,3(s8); slli a2,a2,8; li a0,4; bne s6,a0 *)
           if_true.
           assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 3)) 1 = Some [c1]).
           { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 3 MC) by lia. rewrite Er. reflexivity. }
           step. clear HR. do 3 step.
           unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r))) by lia.
           destruct rest as [|c2 rest]; cbn [length] in Lr.
           ++ (* two bytes: 0x13ea0 mv a0,zero; mv a3,zero; mv a4,zero; addi a5,s8,4; j 0x13f3c *)
              if_false. do 5 step.
              eapply c3_or with (c0 := c0) (c1 := c1) (c2 := NUL) (c3 := NUL) (r' := []);
                [rewrite Er, ent3_odd by assumption; reflexivity | regeq Lr .. | eassumption].
           ++ (* 0x13ed0 lbu a3,4(s8); li a0,5; bne s6,a0 *)
              if_true.
              assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 4)) 1 = Some [c2]).
              { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 4 MC) by lia. rewrite Er. reflexivity. }
              step. clear HR. do 2 step.
              unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r))) by lia.
              destruct rest as [|c3 rest]; cbn [length] in Lr.
              ** (* three bytes: 0x13edc mv a0,zero; mv a4,zero; addi a5,s8,5; j 0x13f3c *)
                 if_false. do 4 step.
                 eapply c3_or with (c0 := c0) (c1 := c1) (c2 := c2) (c3 := NUL) (r' := []);
                   [rewrite Er, ent3_odd by assumption; reflexivity | regeq Lr .. | eassumption].
              ** (* four bytes: 0x13f2c lbu a4,5(s8); addi a0,s6,-6; addi a5,s8,6; slli a4,a4,8 *)
                 if_true.
                 assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 5)) 1 = Some [c3]).
                 { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 5 MC) by lia. rewrite Er. reflexivity. }
                 step. clear HR. do 3 step.
                 eapply c3_or with (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (r' := rest);
                   [rewrite Er, ent3_odd by assumption; reflexivity | regeq Lr .. | eassumption].
    + (* m even: 0x13830 li a2,0xfe; beq a1,a2 *)
      if_false.
      do 2 step.
      unfold bv_eqb. rewrite zxb_u.
      destruct (Z.eq_dec (bv_unsigned v) 254) as [H254|H254].
      * (* NaN: 0x13e30 lui a1,0x7fc00; j 0x13f4c *)
        if_true. do 2 step.
        eapply c3_fin;
          [rewrite Er; apply ent3_nan; assumption | rewrite le4_any; apply le32_mod; reflexivity
          | regeq Lr .. | eassumption].
      * (* 0x13838 li a2,0xfc; bne a1,a2 *)
        if_false. do 2 step.
        unfold bv_eqb. rewrite zxb_u.
        destruct (Z.eq_dec (bv_unsigned v) 252) as [H252|H252].
        -- (* inf: 0x13840 lui a1,0x7f800; j 0x13f4c *)
           if_false. do 2 step.
           eapply c3_fin;
             [rewrite Er; apply ent3_inf; assumption | rewrite le4_any; apply le32_mod; reflexivity
             | regeq Lr .. | eassumption].
        -- (* float_bits[(m / 2) % 21]: 0x13e38 srli a1,a1,1 *)
           if_true. step.
           eapply c3_half with (x := v) (r' := rest);
             [rewrite Er; apply ent3_tbl; assumption | regeq Lr .. | eassumption].
Qed.

End Case3.
