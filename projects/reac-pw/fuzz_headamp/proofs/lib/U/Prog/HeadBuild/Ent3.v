(** ent_build's kind 3 in the UBSan image (pod.h:308-322): a Float, m = fuzz_u8; odd m: its bits = fuzz_u32 (read
    ahead at 0x13c78, 0x13da0, 0x13e88, 0x13ecc, joined at 0x13dc8); m = 0xfe: NaN 0x7fc00000; m = 0xfc: +inf
    0x7f800000 (the model's -inf arm needs bit 1 of m, so it is dead for the even m that reach it); other even m:
    floats[(m >> 1) % 21] (0x13d24, the index by mulhu, the UBSan bound check on &floats[i] not taken). From the
    jump table's target 0x13614 to the join 0x13df0 through the stores of 0x13dd8 / 0x13de0 (Ent2.tail_13de0). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import EntCut EntFacts Ent2.
Import ListNotations.
Open Scope Z_scope.

(** ** .rodata words *)
Lemma floats_ok : ro4_ok 0x1057c float_bits = true.
Proof. vm_compute. reflexivity. Qed.

Lemma floats_read : forall m1 x, mem_inv rsegs m1 -> 0 <= x < 21 ->
  ov_read_bytes rsegs m1 (wa (0x1057c + 4 * x)) 4 = Some (le4 (Z_to_bv 64 (nth (Z.to_nat x) float_bits 0))).
Proof.
  intros m1 x MI Hx.
  pose proof (ro4_read m1 0x1057c float_bits (Z.to_nat x) MI floats_ok ltac:(rewrite float_bits_length; lia)
                ltac:(lia) ltac:(rewrite float_bits_length; lia)) as H.
  rewrite Z2Nat.id in H by lia. exact H.
Qed.

(** ** The model of kind 3 *)
Lemma eb3_nil : forall b, bv_unsigned b mod 10 = 3 ->
  ent_build [b] = (Ent POD_FLOAT 4 (le32 (nth 0 float_bits 0)), []).
Proof. intros b Hk. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity. Qed.

Lemma eb3_odd : forall b c rest, bv_unsigned b mod 10 = 3 -> Z.odd (bv_unsigned c) = true ->
  ent_build (b :: c :: rest) = (Ent POD_FLOAT 4 (le32 (fst (fuzz_u32 rest))), snd (fuzz_u32 rest)).
Proof.
  intros b c rest Hk Ho. unfold ent_build. cbn [fuzz_u8]. rewrite Hk, Ho. cbn -[fuzz_u32].
  destruct (fuzz_u32 rest). reflexivity.
Qed.

Lemma eb3_nan : forall b c rest, bv_unsigned b mod 10 = 3 -> bv_unsigned c = 254 ->
  ent_build (b :: c :: rest) = (Ent POD_FLOAT 4 (le32 0x7fc00000), rest).
Proof. intros b c rest Hk Hc. unfold ent_build. cbn [fuzz_u8]. rewrite Hk, Hc. reflexivity. Qed.

Lemma eb3_inf : forall b c rest, bv_unsigned b mod 10 = 3 -> bv_unsigned c = 252 ->
  ent_build (b :: c :: rest) = (Ent POD_FLOAT 4 (le32 0x7f800000), rest).
Proof. intros b c rest Hk Hc. unfold ent_build. cbn [fuzz_u8]. rewrite Hk, Hc. reflexivity. Qed.

(** An even m other than 0xfe, 0xfc: m >> 1 is neither 127 nor 126. *)
Lemma half_other : forall x, Z.odd x = false -> (x =? 254) = false -> (x =? 252) = false ->
  (x / 2 =? 127) = false /\ (x / 2 =? 126) = false.
Proof.
  intros x Ho H1 H2. apply Z.eqb_neq in H1, H2.
  assert (He : Z.even x = true) by (rewrite <- Z.negb_odd, Ho; reflexivity).
  apply Z.even_spec in He. destruct He as [k Hk].
  split; apply Z.eqb_neq; intro; lia.
Qed.

Lemma eb3_tbl : forall b c rest, bv_unsigned b mod 10 = 3 -> Z.odd (bv_unsigned c) = false ->
  (bv_unsigned c =? 254) = false -> (bv_unsigned c =? 252) = false ->
  ent_build (b :: c :: rest) = (Ent POD_FLOAT 4 (le32 (nth (Z.to_nat ((bv_unsigned c / 2) mod 21)) float_bits 0)), rest).
Proof.
  intros b c rest Hk Ho H1 H2. destruct (half_other _ Ho H1 H2) as [E1 E2].
  unfold ent_build. cbn [fuzz_u8]. rewrite Hk, Ho, E1, E2. reflexivity.
Qed.

(** ** The ent's stores *)
Section Tail3.
Variables (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Local Abbreviation QE := (QJ sp gp tp s1 F fc m r src pp lo (ent_build r)).

(** 0x13dd8: type 6 (POD_FLOAT), then Ent2.tail_13de0. *)
Lemma tail_13dd8 : forall (ra t0 t1 t2 s2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s10 t3 t4 t5 t6 : word) m1 v r',
  ent_build r = (Ent POD_FLOAT 4 (le32 v), r') ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  le4 a1 = le32 v ->
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (Z_to_bv 64 (0xcccccccd * 2^32)) s4 s5 s6 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 95)
             s10 (Z_to_bv 64 4) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13dd8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s10 t3 t4 t5 t6 m1 v r' Eb Ea0 Es5 Ha1 MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13dd8 addi a2,zero,6; sw a2,0xb8(sp) *)
  step. est_t HE MC.
  eapply (tail_13de0 sp gp tp s1 F fc m r src pp lo HE); [exact Eb | exact Ea0 | exact Es5 | exact Ha1 | exact MC].
Qed.

(** 0x13dc8: the bits a1 | a2 | (a3 | a4) << 16, as Ent2.or_13d88. *)
Lemma or_13dc8 : forall (ra t0 t1 t2 s2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s10 t3 t4 t5 t6 : word) m1 x1 x2 x3 x4 r',
  ent_build r = (Ent POD_FLOAT 4 (le32 (x1 + 256 * x2 + 65536 * (x3 + 256 * x4))), r') ->
  a0 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  bv_unsigned a1 = x1 -> bv_unsigned a2 = 256 * x2 -> bv_unsigned a3 = x3 -> bv_unsigned a4 = 256 * x4 ->
  0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> 0 <= x4 < 256 ->
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (Z_to_bv 64 (0xcccccccd * 2^32)) s4 s5 s6 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 95)
             s10 (Z_to_bv 64 4) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13dc8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s10 t3 t4 t5 t6 m1 x1 x2 x3 x4 r' Eb Ea0 Es5
    H1 H2 H3 H4 R1 R2 R3 R4 MC.
  (* 0x13dc8 or a1,a2,a1; or a3,a4,a3; slli a3,a3,0x10; or a1,a1,a3 *)
  do 4 step.
  eapply tail_13dd8; [exact Eb | exact Ea0 | exact Es5 | | exact MC].
  apply or_value; assumption.
Qed.

End Tail3.

Section Case3.
Variables (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Lemma case3_ok_sec : case_at sp gp tp s1 F fc m r src pp lo 3 0x13614.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof MC as (_ & _ & MI & _).
  destruct rest as [|c rest].
  - (* no byte for m: m = 0, floats[0] *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x13614 beqz s6 -> 0x138f8 mv a0,zero; auipc/addi a1 = floats; j 0x13d58; lw a1,0(a1); j 0x13dd8 *)
    step. brt. do 4 step.
    pose proof (floats_read m1 0 MI ltac:(lia)) as HR. rewrite Z.mul_0_r, Z.add_0_r in HR.
    step. clear HR. step.
    eapply (tail_13dd8 sp gp tp s1 F fc m r src pp lo HE) with (v := nth 0 float_bits 0) (r' := []);
      [rewrite Er; apply eb3_nil; exact Hk | weq | f_equal; rewrite L; cbn [length]; lia
      | rewrite le4_sx32; apply le4_le32 | exact MC].
  - assert (L : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    (* 0x13614 beqz s6; addi s5,s5,1; addi a0,zero,1; bltu a0,s5,8 over the trap (taken) *)
    step. brf. do 2 step. step. brt.
    (* 0x13628 lbu a1,1(s10); addi a0,s2,-2; andi a2,a1,1; addi s5,s10,2; bnez a2 *)
    inb HE Er MC 1%nat. step. clear HB.
    do 4 step. brb c (Z.odd (bv_unsigned c)).
    destruct (Z.odd (bv_unsigned c)) eqn:Eo; cbv iota.
    + (* odd m: fuzz_u32 *)
      destruct rest as [|d1 rest].
      * (* 0x13c78 beqz a0 -> 0x13d10: bits 0 *)
        fixlen. step. brt. do 5 step.
        eapply (or_13dc8 sp gp tp s1 F fc m r src pp lo HE) with (x1 := 0) (x2 := 0) (x3 := 0) (x4 := 0) (r' := []);
          [rewrite Er, eb3_odd by assumption; reflexivity | weq | weq | uv | uv | uv | uv | rg | rg | rg | rg | exact MC].
      * assert (L3 : length r = S (S (S (length rest)))) by (rewrite Er; reflexivity).
        (* 0x13c7c addi s5; addi a0,zero,1; bgeu (trap); lbu a1,2(s10); addi s5,s10,3; addi a0,zero,3; bne s2,a0 *)
        step. brf. do 2 step. step. brf.
        inb HE Er MC 2%nat. step. clear HB.
        do 3 step.
        destruct rest as [|d2 rest].
        -- (* |r| = 3: 0x13c98 mv a0; mv a2; j 0x13dc0; mv a3; mv a4 *)
           fixlen. brf. do 5 step.
           eapply (or_13dc8 sp gp tp s1 F fc m r src pp lo HE) with (x1 := bv_unsigned d1) (x2 := 0) (x3 := 0)
             (x4 := 0) (r' := []);
             [rewrite Er, eb3_odd by assumption; reflexivity | weq | weq | uv | uv | uv | uv | rg | rg | rg | rg
             | exact MC].
        -- assert (L4 : length r = S (S (S (S (length rest))))) by (rewrite Er; reflexivity).
           (* 0x13da0 addi s5; addi a0; bgeu (trap); lbu a2,3(s10); addi s5,s10,4; slli a2,a2,8; bne s2,s11 *)
           brt. step. step. step. brf.
           inb HE Er MC 3%nat. step. clear HB.
           do 3 step.
           destruct rest as [|d3 rest].
           ++ (* |r| = 4: 0x13dbc mv a0; mv a3; mv a4 *)
              fixlen. brf. do 3 step.
              eapply (or_13dc8 sp gp tp s1 F fc m r src pp lo HE) with (x1 := bv_unsigned d1) (x2 := bv_unsigned d2)
                (x3 := 0) (x4 := 0) (r' := []);
                [rewrite Er, eb3_odd by assumption; reflexivity | weq | weq | uv | uv | uv | uv | rg | rg | rg | rg
                | exact MC].
           ++ assert (L5 : length r = S (S (S (S (S (length rest)))))) by (rewrite Er; reflexivity).
              (* 0x13e88 addi s5; addi a0; bgeu (trap); lbu a3,4(s10); addi s5,s10,5; addi a0,zero,5; bne s2,a0 *)
              brt. step. step. step. brf.
              inb HE Er MC 4%nat. step. clear HB.
              do 3 step.
              destruct rest as [|d4 rest].
              ** (* |r| = 5: 0x13ea4 mv a0; j 0x13dc4; mv a4 *)
                 fixlen. brf. do 3 step.
                 eapply (or_13dc8 sp gp tp s1 F fc m r src pp lo HE) with (x1 := bv_unsigned d1)
                   (x2 := bv_unsigned d2) (x3 := bv_unsigned d3) (x4 := 0) (r' := []);
                   [rewrite Er, eb3_odd by assumption; reflexivity | weq | weq | uv | uv | uv | uv | rg | rg | rg
                   | rg | exact MC].
              ** assert (L6 : length r = S (S (S (S (S (S (length rest))))))) by (rewrite Er; reflexivity).
                 (* 0x13ecc addi s5; addi a0; bgeu (trap); lbu a4,5(s10); addi a0,s2,-6; addi s5,s10,6;
                    slli a4,a4,8; j 0x13dc8 *)
                 brt. step. step. step. brf.
                 inb HE Er MC 5%nat. step. clear HB.
                 do 4 step.
                 eapply (or_13dc8 sp gp tp s1 F fc m r src pp lo HE) with (x1 := bv_unsigned d1)
                   (x2 := bv_unsigned d2) (x3 := bv_unsigned d3) (x4 := bv_unsigned d4) (r' := rest);
                   [rewrite Er, eb3_odd by assumption; reflexivity | weq | weq | uv | uv | uv | uv | rg | rg | rg
                   | rg | exact MC].
    + (* even m: 0x1363c addi a2,zero,0xfe; beq a1,a2 *)
      step. step. brb c (bv_unsigned c =? 254).
      destruct (bv_unsigned c =? 254) eqn:E254; cbv iota.
      * (* NaN: 0x13d1c lui a1,0x7fc00; j 0x13dd8 *)
        do 2 step.
        eapply (tail_13dd8 sp gp tp s1 F fc m r src pp lo HE) with (v := 0x7fc00000) (r' := rest);
          [rewrite Er; apply eb3_nan; [exact Hk | apply Z.eqb_eq; exact E254] | weq | weq | apply le4_le32
          | exact MC].
      * (* 0x13644 addi a2,zero,0xfc; bne a1,a2 *)
        step. step. brb c (negb (bv_unsigned c =? 252)).
        destruct (bv_unsigned c =? 252) eqn:E252; cbv beta iota delta [negb].
        -- (* +inf: 0x1364c lui a1,0x7f800; j 0x13dd8 *)
           do 2 step.
           eapply (tail_13dd8 sp gp tp s1 F fc m r src pp lo HE) with (v := 0x7f800000) (r' := rest);
             [rewrite Er; apply eb3_inf; [exact Hk | apply Z.eqb_eq; exact E252] | weq | weq | apply le4_le32
             | exact MC].
        -- (* floats[(m >> 1) % 21] *)
           pose proof (Z.mod_pos_bound (bv_unsigned c / 2) 21 ltac:(lia)) as Hi.
           (* 0x13d24 .. 0x13d4c: the index by mulhu, &floats[i], not a3,a1 *)
           do 11 step.
           byte_reg c (4 * ((bv_unsigned c / 2) mod 21)).
           (* 0x13d50 bltu a3,a2 (trap); add a1,a1,a2; lw a1,0(a1); j 0x13dd8 *)
           step. brf. step.
           pose proof (floats_read m1 ((bv_unsigned c / 2) mod 21) MI Hi) as HR.
           step. clear HR. step.
           eapply (tail_13dd8 sp gp tp s1 F fc m r src pp lo HE)
             with (v := nth (Z.to_nat ((bv_unsigned c / 2) mod 21)) float_bits 0) (r' := rest);
             [rewrite Er; apply eb3_tbl; assumption | weq | weq | rewrite le4_sx32; apply le4_le32 | exact MC].
Qed.

End Case3.

Theorem case3_ok : forall (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z),
  ent_pre sp m r src pp lo -> case_at sp gp tp s1 F fc m r src pp lo 3 0x13614.
Proof. intros. apply case3_ok_sec; assumption. Qed.
