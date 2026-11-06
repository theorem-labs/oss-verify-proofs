(** ent_build's kind 8 (pod.h:359-365): the type t8[t % 4], t = fuzz_u8; a String has size 0, any other type
    has size s % 4 (s = fuzz_u8) and memset(body, 0, size). From the jump table's target 0x138a4 to the join
    0x1360c (through 0x13b6c when no byte is left, 0x13c88 when no size byte is left, 0x13c80 when the type is a
    String, and the memset call at 0x13ca0). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** ** The model's kind 8, by the bytes the code reads *)
Lemma ent8_nil : forall b, bv_unsigned b mod 10 = 8 -> ent_build [b] = (Ent 4 0 (zeros (Z.to_nat 0)), []).
Proof. intros b Hk. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. reflexivity. Qed.

Lemma ent8_one : forall b v, bv_unsigned b mod 10 = 8 ->
  ent_build [b; v] = (Ent (nth (Z.to_nat (bv_unsigned v mod 4)) t8 0) 0 (zeros (Z.to_nat 0)), []).
Proof.
  intros b v Hk. pose proof (Z.mod_pos_bound (bv_unsigned v) 4 ltac:(lia)) as H.
  assert (E : bv_unsigned v mod 4 = 0 \/ bv_unsigned v mod 4 = 1 \/ bv_unsigned v mod 4 = 2 \/
              bv_unsigned v mod 4 = 3) by lia.
  unfold ent_build. cbn [fuzz_u8]. rewrite Hk.
  destruct E as [E|[E|[E|E]]]; rewrite E; reflexivity.
Qed.

Lemma ent8_str : forall b v rest, bv_unsigned b mod 10 = 8 -> bv_unsigned v mod 4 = 3 ->
  ent_build (b :: v :: rest) = (Ent (nth (Z.to_nat (bv_unsigned v mod 4)) t8 0) 0 (zeros (Z.to_nat 0)), rest).
Proof. intros b v rest Hk E. unfold ent_build. cbn [fuzz_u8]. rewrite Hk, E. reflexivity. Qed.

Lemma ent8_sz : forall b v w rest, bv_unsigned b mod 10 = 8 -> bv_unsigned v mod 4 <> 3 ->
  ent_build (b :: v :: w :: rest) =
  (Ent (nth (Z.to_nat (bv_unsigned v mod 4)) t8 0) (bv_unsigned w mod 4) (zeros (Z.to_nat (bv_unsigned w mod 4))),
   rest).
Proof.
  intros b v w rest Hk H3. pose proof (Z.mod_pos_bound (bv_unsigned v) 4 ltac:(lia)) as H.
  assert (E : bv_unsigned v mod 4 = 0 \/ bv_unsigned v mod 4 = 1 \/ bv_unsigned v mod 4 = 2) by lia.
  unfold ent_build. cbn [fuzz_u8]. rewrite Hk.
  destruct E as [E|[E|E]]; rewrite E; reflexivity.
Qed.

Section Case8.
Variables (sp gp tp s1 s8 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MSET : memset_contract.

Local Abbreviation QE := (QJ sp gp tp s1 s8 F fc m r src pp lo (ent_build r)).
Local Abbreviation S0 := (Z_to_bv 64 (bv_unsigned sp + 0x150)).
Local Abbreviation S7 := (Z_to_bv 64 95).
Local Abbreviation S9 := (Z_to_bv 64 (0xcccccccd * 2^32)).
Local Abbreviation S10 := (Z_to_bv 64 (bv_unsigned sp + 0x118)).
Local Abbreviation S11 := (Z_to_bv 64 10).

(** 0x13c90 `sw s4,0x94(sp)`, memset(e->body, 0, size), `sd s2,0x88(sp)`, to the join 0x1360c. *)
Lemma c8_tail : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word) m1 ty n r',
  ent_build r = (Ent ty n (zeros (Z.to_nat n)), r') -> 0 <= n <= 3 ->
  s3 = Z_to_bv 64 ty -> s4 = Z_to_bv 64 n -> s2 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s6 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) -> s5 = Z_to_bv 64 pp ->
  MemC sp m r src pp lo m1 (upd_bytes (zeros 104) 0 (le4 s3)) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 S7 s8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c90) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 m1 ty n r' Eb Hn -> -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13c90 sw s4,0x94(sp) *)
  pre_store HE (bv_unsigned sp + 148) 4%nat. step. mstore_e HE 4.
  (* addi a0,sp,0x98; mv a1,zero; mv a2,s4; jal memset *)
  do 4 step.
  lazymatch goal with MC : MemC _ _ _ _ _ _ _ _ |- _ =>
    destruct (MemC_cells sp m r src pp lo HE _ _ (bv_unsigned sp + 152) (Z.to_nat n) MC
                ltac:(unfold FRAME_LOCALS; lia) ltac:(unfold FRAME_LOCALS; lia)) as (junk & Lj & CJ);
    eapply evt_cut;
    [ eapply MSET with (junk := junk);
      [ rewrite !unsigned_lit by lia; exact CJ | exact (MemC_mem_inv _ _ _ _ _ _ _ _ MC) ]
    | intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 &
                  E & MU1 & WM1 & MI1 & RC1);
      subst ms'; rewrite !unsigned_lit in MU1, RC1 by lia;
      apply rw_CB_bytes in RC1 as [B1 L1];
      pose proof (MemC_call_e sp m r src pp lo HE _ _ _ _ _ _ MC MU1 WM1 MI1 B1
                    ltac:(rewrite L1; lia) ltac:(lia) ltac:(lia)) as MC1;
      clear MU1 WM1 MI1 B1 L1 MC CJ Lj junk ]
  end.
  replace (Z.to_nat (bv_unsigned sp + 152 - (bv_unsigned sp + 144))) with 8%nat in MC1 by lia.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x13ca4 sd s2,0x88(sp); j 0x1360c *)
  pre_store HE (bv_unsigned sp + 136) 8%nat. step. mstore_out HE.
  step.
  eapply join_1360c; [exact Eb | reflexivity | reflexivity | reflexivity | reflexivity | | exact HW].
  eapply MemC_e_ext; [eassumption|].
  rewrite !le4_any. unfold ent_mem. cbn [e_type e_size e_body].
  assert (En : n = 0 \/ n = 1 \/ n = 2 \/ n = 3) by lia.
  destruct En as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

(** 0x138cc, after the type's load: `sw s3,0x90(sp)`, then the size (0x13c88, 0x13c80 or the byte s, 0x138ec). *)
Lemma c8_mid : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word) b v rest m1,
  r = b :: v :: rest -> bv_unsigned b mod 10 = 8 ->
  a0 = Z_to_bv 64 (bv_unsigned v mod 4) -> s3 = Z_to_bv 64 (nth (Z.to_nat (bv_unsigned v mod 4)) t8 0) ->
  s4 = Z_to_bv 64 0 -> s2 = Z_to_bv 64 (Z.of_nat (length r)) -> s6 = Z_to_bv 64 src ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 S7 s8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x138cc) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 b v rest m1 Er Hk -> -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (Z.mod_pos_bound (bv_unsigned v) 4 ltac:(lia)) as Hv.
  assert (Lr : length r = S (S (length rest))) by (rewrite Er; reflexivity).
  (* 0x138cc mv a2,s2; addi s2,s2,-2; addi a3,s6,2; sw s3,0x90(sp) *)
  do 3 step.
  pre_store HE (bv_unsigned sp + 144) 4%nat. step. mstore_e HE 0.
  (* 0x138dc beqz s2 *)
  step.
  unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) + -2)) by lia.
  destruct rest as [|w rest]; cbn [length] in Lr.
  - (* no byte left for s: size 0; 0x13c88 mv s6,a3; ld s5,0x58(sp) *)
    if_true.
    step. mcells. step.
    eapply c8_tail.
    + rewrite Er. apply ent8_one. exact Hk.
    + lia.
    + reflexivity.
    + reflexivity.
    + f_equal. rewrite Lr. cbn [length]. lia.
    + f_equal. rewrite Lr. cbn [length]. lia.
    + reflexivity.
    + eassumption.
  - if_false.
    (* 0x138e0 ld s5,0x58(sp); addi a1,zero,3; beq a0,a1 *)
    mcells. step.
    do 2 step.
    unfold bv_eqb. rewrite (unsigned_lit (bv_unsigned v mod 4)) by lia.
    destruct (Z.eq_dec (bv_unsigned v mod 4) 3) as [H3|H3].
    + (* a String: size 0; 0x13c80 mv s6,a3; j 0x13c90 *)
      if_true.
      do 2 step.
      eapply c8_tail.
      * rewrite Er. apply ent8_str; assumption.
      * lia.
      * reflexivity.
      * reflexivity.
      * f_equal. rewrite Lr. cbn [length]. lia.
      * f_equal. rewrite Lr. cbn [length]. lia.
      * reflexivity.
      * eassumption.
    + if_false.
      (* 0x138ec lbu a0,2(s6); addi s2,a2,-3; addi s6,s6,3; andi s4,a0,3; j 0x13c90 *)
      lazymatch goal with MC : MemC _ _ _ _ _ _ ?m2 ?eb |- _ =>
        assert (HR : ov_read_bytes rsegs m2 (wa (src + Z.of_nat 2)) 1 = Some [w])
          by (rewrite (MemC_in_byte sp m r src pp lo m2 eb 2 MC) by lia; rewrite Er; reflexivity) end.
      step. clear HR.
      do 3 step.
      match goal with |- context [Z.land ?E 3] =>
        replace (Z.land E 3) with (bv_unsigned w mod 4) by (clear - w; revert w; byte_eq) end.
      step.
      pose proof (Z.mod_pos_bound (bv_unsigned w) 4 ltac:(lia)) as Hw.
      eapply c8_tail.
      * rewrite Er. apply ent8_sz; assumption.
      * lia.
      * reflexivity.
      * reflexivity.
      * f_equal. rewrite Lr. cbn [length]. lia.
      * f_equal. rewrite Lr. cbn [length]. lia.
      * reflexivity.
      * eassumption.
Qed.

Lemma case8_ok : case_at sp gp tp s1 s8 F fc m r src pp lo 8 0x138a4.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 b rest m1 Er Hk Hs -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x138a4 beqz s5 *)
  step.
  unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r) - 1)) by (rewrite Er in *; cbn [length] in *; lia).
  destruct rest as [|v rest].
  - (* no byte left: t = 0, an Int of size 0; 0x13b6c mv s6,a5; mv s2,zero; mv s4,zero; li s3,4;
       sw s3,0x90(sp); j 0x13c8c; ld s5,0x58(sp) *)
    assert (Lr : length r = 1%nat) by (rewrite Er; reflexivity).
    if_true.
    do 4 step.
    pre_store HE (bv_unsigned sp + 144) 4%nat. step. mstore_e HE 0.
    step. mcells. step.
    eapply c8_tail.
    + rewrite Er. apply ent8_nil. exact Hk.
    + lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal. rewrite Lr. cbn [length]. lia.
    + reflexivity.
    + eassumption.
  - assert (Lr : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    if_false.
    (* 0x138a8 mv s2,s4; mv s4,zero; lbu a0,1(s6) *)
    assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 1)) 1 = Some [v]).
    { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 1 MC) by lia. rewrite Er. reflexivity. }
    do 3 step. clear HR.
    (* 0x138b4 auipc a1; andi a0,a0,3 *)
    do 2 step.
    match goal with |- context [Z.land ?E 3] =>
      replace (Z.land E 3) with (bv_unsigned v mod 4) by (clear - v; revert v; byte_eq) end.
    pose proof (Z.mod_pos_bound (bv_unsigned v) 4 ltac:(lia)) as Hv.
    assert (Hv4 : bv_unsigned v mod 4 = 0 \/ bv_unsigned v mod 4 = 1 \/ bv_unsigned v mod 4 = 2 \/
                  bv_unsigned v mod 4 = 3) by lia.
    clear Hv. mmi.
    (* 0x138bc slli a2,a0,2; addi a1,a1,-0x2e4; add a1,a1,a2; lw s3,0(a1): t8[t % 4] *)
    destruct Hv4 as [Hv|[Hv|[Hv|Hv]]]; rewrite Hv; do 4 step;
      (eapply c8_mid; [exact Er | exact Hk | rewrite Hv; reflexivity | rewrite Hv; reflexivity | reflexivity
                      | reflexivity | reflexivity | eassumption]).
Qed.

End Case8.
