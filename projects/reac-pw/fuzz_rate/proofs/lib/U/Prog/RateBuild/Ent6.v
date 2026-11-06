(** ent_build's kind 6 in the UBSan image (pod.h:341-347): a pod of the type t[kind & 3] (LONG, DOUBLE, ID, NONE)
    whose body is the next size bytes of the input, zero-padded. From the jump table's target 0x137f4 to the join
    0x13ee4: through 0x13a70 when no byte is left for t, the type load and store and the size at 0x13a80 .. 0x13ab8,
    then Ent6T.v's tail (0x13da4 / 0x13da8). The form is reac-pw/fuzz_role's U/Prog/RoleBuild/Ent6.v
    at rate's registers and addresses. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac Image ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import EntCut EntFacts Ent6T.
Import ListNotations.
Open Scope Z_scope.

(** `t & 3` is t mod 4. *)
Lemma e6_land3 : forall z, Z.land z 3 = z mod 4.
Proof. intros z. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

(** The type and the size kind 6 gives for the table index (pod.h:342-345). *)
Definition ty6 (idx : Z) : Z := nth (Z.to_nat idx) t6 0.
Definition sz6 (idx : Z) : Z := if idx =? 3 then 0 else if idx =? 2 then 4 else 8.

(** ent_build's kind 6, by the table index (the model's type test on t[] is the index test). *)
Lemma eb6 : forall (b c : byte) (rest2 : list byte), bv_unsigned b mod 10 = 6 ->
  ent_build (b :: c :: rest2) =
  (Ent (ty6 (bv_unsigned c mod 4)) (sz6 (bv_unsigned c mod 4))
     (firstn (Z.to_nat (sz6 (bv_unsigned c mod 4))) rest2
      ++ zeros (Z.to_nat (sz6 (bv_unsigned c mod 4)) - length (firstn (Z.to_nat (sz6 (bv_unsigned c mod 4))) rest2))),
   skipn (Z.to_nat (sz6 (bv_unsigned c mod 4))) rest2).
Proof.
  intros b c rest2 Hk. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. cbn [Z.to_nat].
  unfold fuzz_take, ty6, sz6.
  assert (H : bv_unsigned c mod 4 = 0 \/ bv_unsigned c mod 4 = 1 \/ bv_unsigned c mod 4 = 2
              \/ bv_unsigned c mod 4 = 3) by lia.
  destruct H as [E | [E | [E | E]]]; rewrite E; cbn [Z.eqb Z.to_nat nth t6 Z.of_nat]; reflexivity.
Qed.

Lemma eb6_nil : forall (b : byte), bv_unsigned b mod 10 = 6 ->
  ent_build [b] =
  (Ent (ty6 0) (sz6 0)
     (firstn (Z.to_nat (sz6 0)) (@nil byte)
      ++ zeros (Z.to_nat (sz6 0) - length (firstn (Z.to_nat (sz6 0)) (@nil byte)))),
   skipn (Z.to_nat (sz6 0)) (@nil byte)).
Proof.
  intros b Hk. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. cbn [Z.to_nat].
  unfold fuzz_take, ty6, sz6. cbn [Z.eqb Z.to_nat nth t6 firstn skipn Z.of_nat length]. reflexivity.
Qed.

Section Case6.
Variables (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.

Local Abbreviation QE := (QJ sp gp tp s3 F fc m r src pp lo (ent_build r)).
Local Abbreviation S0 := (Z_to_bv 64 (bv_unsigned sp + 0x188)).
Local Abbreviation S1 := (Z_to_bv 64 4).
Local Abbreviation S2 := (Z_to_bv 64 95).
Local Abbreviation S4 := (Z_to_bv 64 (0xcccccccd * 2^32)).
Local Abbreviation S5 := (Z_to_bv 64 10).
Local Abbreviation S6 := (Z_to_bv 64 0x4000).

(** 0x13ab8 `bgeu a2,a0`: sz >= left takes 0x13da4 (n = left), else `j 0x13da8` (n = sz). *)
Lemma br6 : forall (ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 t szw : word) m1
    (j : nat) (cur left sz : Z) (p r' : list byte) (e : ent),
  ent_build r = (e, r') -> e_size e = sz -> e_body e = p ++ zeros (Z.to_nat sz - length p) ->
  0 <= sz <= 96 -> (j <= length r)%nat -> cur = src + Z.of_nat j -> left = Z.of_nat (length r - j) ->
  p = firstn (Z.to_nat sz) (skipn j r) -> r' = skipn (Z.to_nat sz) (skipn j r) ->
  MemC sp m lo m1 t szw (zeros 96) -> le4 t = le32 (e_type e) -> le4 szw = le32 sz ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (Z_to_bv 64 left) a1 (Z_to_bv 64 sz) a3 a4 a5 a6 a7
             S2 s3 S4 S5 S6 (Z_to_bv 64 cur) (Z_to_bv 64 pp) s9 s10 (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ab8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 t szw m1 j cur left sz p r' e EB Esz Ebd Hsz Hj
    Ecur Eleft Ep Er' MC Et Eszw.
  pose proof (ep_range sp m r src pp lo HE) as R.
  step.
  destruct (Z_lt_ge_dec sz left) as [X|X].
  - brf. step.
    eapply (tail_13da8 sp gp tp s3 F fc m r src pp lo HE MCPY ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6
              t szw m1 j cur left sz sz p r' e);
      first [ eassumption | lia ].
  - brt.
    eapply (tail_13da4 sp gp tp s3 F fc m r src pp lo HE MCPY ra t0 t1 t2 a1 (Z_to_bv 64 sz) a3 a4 a5 a6 a7 s9
              s10 t3 t4 t5 t6 t szw m1 j cur left sz p r' e);
      first [ eassumption | lia ].
Qed.

(** 0x13a80 -> the join: the type from the table t[] of .rodata (0x10608), stored; s8 reloaded; the size the
    type fixes, stored; s11 reloaded; then [br6]. *)
Lemma mid6 : forall (ra t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m1 (j : nat) (idx cur left : Z),
  0 <= idx < 4 -> (j <= length r)%nat -> cur = src + Z.of_nat j -> left = Z.of_nat (length r - j) ->
  ent_build r =
    (Ent (ty6 idx) (sz6 idx)
       (firstn (Z.to_nat (sz6 idx)) (skipn j r)
        ++ zeros (Z.to_nat (sz6 idx) - length (firstn (Z.to_nat (sz6 idx)) (skipn j r)))),
     skipn (Z.to_nat (sz6 idx)) (skipn j r)) ->
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (Z_to_bv 64 left) (Z_to_bv 64 idx) (Z_to_bv 64 (67080 + 4 * idx)) a3
             a4 a5 a6 a7 S2 s3 S4 S5 S6 (Z_to_bv 64 cur) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a80) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 m1 j idx cur left Hidx Hj Ecur Eleft EB MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI1.
  assert (Hcases : idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3) by lia.
  destruct Hcases as [ -> | [ -> | [ -> | -> ] ] ]; unfold ty6, sz6 in *; cbn [Z.eqb Z.to_nat nth Tables.t6] in *;
    [ pose proof (ro4_read m1 67080 Tables.t6 0%nat MI1 ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
                    ltac:(lia) ltac:(cbn; lia)) as HT
    | pose proof (ro4_read m1 67080 Tables.t6 1%nat MI1 ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
                    ltac:(lia) ltac:(cbn; lia)) as HT
    | pose proof (ro4_read m1 67080 Tables.t6 2%nat MI1 ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
                    ltac:(lia) ltac:(cbn; lia)) as HT
    | pose proof (ro4_read m1 67080 Tables.t6 3%nat MI1 ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
                    ltac:(lia) ltac:(cbn; lia)) as HT ];
    cbn [Z.of_nat nth Tables.t6] in HT;
    (* 0x13a80 lw a2,0(a2); 0x13a84 sw a2,0xe8(sp) *)
    (step; clear HT; est_t HE MC;
     (* 0x13a88 ld s8,0xd8(sp) *)
     let R8 := fresh "R8" in
     pose proof (MemC_cd8 sp m r src pp lo HE _ _ _ _ MC) as R8; step; clear R8;
     (* 0x13a8c addi a2,zero,2; 0x13a90 beq a1,a2 *)
     step; step; first [ brt | brf ];
     (* 0x13a94 addi a2,zero,8; j / 0x13a9c addi a2,zero,4; 0x13aa0 .. 0x13aac the NONE test *)
     repeat step;
     (* 0x13ab0 sw a2,0xec(sp) *)
     est_sz HE MC;
     (* 0x13ab4 ld s11,0xc8(sp) *)
     let RC8 := fresh "RC8" in
     pose proof (MemC_cc8 sp m r src pp lo HE _ _ _ _ MC) as RC8; step; clear RC8;
     (* the size `and a2,a1,a2` (closed: the index is a literal here) as a literal, in the goal and in MC *)
     lazymatch goal with
     | |- context [Z_to_bv 64 (Z.land ?X ?Y)] =>
         let v := eval vm_compute in (Z.land X Y) in
         let Ea := fresh "Ea" in
         assert (Ea : Z.land X Y = v) by (vm_compute; reflexivity);
         rewrite Ea in *; clear Ea
     end;
     eapply br6;
       [ exact EB | reflexivity | reflexivity | lia | exact Hj | exact Ecur | exact Eleft | reflexivity
       | reflexivity | exact MC | first [ apply le4_le32 | vm_compute; reflexivity ] | apply le4_le32 ]).
Qed.

Lemma case6_ok_sec : case_at sp gp tp s3 F fc m r src pp lo 6 0x137f4.
Proof.
  intros ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (byte_range b) as Rb.
  destruct rest as [|c rest2].
  - (* no byte for the type index *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x137f4 beqz s8 (taken); 0x13a70 mv a0,zero; mv a1,zero; auipc a2; addi a2 *)
    step. brt. do 4 step.
    replace (Z_to_bv 64 67080) with (Z_to_bv 64 (67080 + 4 * 0)) by (f_equal; lia).
    eapply (mid6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 1%nat 0 (src + 1) 0);
      [ lia | lia | cbn [Z.of_nat]; lia | rewrite L; cbn [Z.of_nat]; lia
      | rewrite Er; cbn [skipn]; exact (eb6_nil b Hk) | exact MC ].
  - (* the type index from the next byte *)
    assert (L : length r = S (S (length rest2))) by (rewrite Er; reflexivity).
    pose proof (byte_range c) as Rc.
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB1.
    rewrite Er in HB1. cbn [nth] in HB1.
    (* 0x137f4 beqz s8 (not taken); addi s7,s7,1; addi a0,zero,1; bgeu a0,s7 (trap); lbu a1,1(s9) *)
    step. brf. do 2 step. step. brf. step.
    (* 0x13808 auipc a0; addi a2,a0,-0x200; andi a1,a1,3; slli a3,a1,2 *)
    do 4 step. rewrite e6_land3, t67_zxb_un, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    rewrite (unsigned_lit (bv_unsigned c mod 4)) by lia.
    (* 0x13818 not a0,a2; 0x1381c bltu a0,a3 (trap) *)
    step. step. brf.
    (* 0x13820 addi a0,t1,-2; addi s7,s9,2; add a2,a2,a3; j 0x13a80 *)
    do 4 step.
    replace (Z_to_bv 64 (67080 + bv_unsigned c mod 4 * 4))
      with (Z_to_bv 64 (67080 + 4 * (bv_unsigned c mod 4))) by (f_equal; lia).
    eapply (mid6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 2%nat (bv_unsigned c mod 4) (src + 2)
              (Z.of_nat (length r) + -2));
      [ lia | lia | cbn [Z.of_nat]; lia | rewrite L; cbn [Z.of_nat]; lia
      | rewrite Er; cbn [skipn]; exact (eb6 b c rest2 Hk) | exact MC ].
Qed.

End Case6.

Theorem case6_ok : forall (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte) (src pp lo : Z), ent_pre sp m r src pp lo -> memcpy_contract -> case_at sp gp tp s3 F fc m r src pp lo 6 0x137f4.
Proof. intros. apply case6_ok_sec; assumption. Qed.
