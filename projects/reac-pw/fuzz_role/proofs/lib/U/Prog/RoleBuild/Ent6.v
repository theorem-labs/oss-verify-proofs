(** ent_build's kind 6 in the UBSan image (pod.h:341-347): a pod of the type t[kind & 3] (LONG, DOUBLE, ID,
    NONE) whose body is the next size bytes of the input, zero-padded. From the jump table's target 0x1361c to
    the join 0x13c48 (through 0x13830 when no byte is left for t, and the tail 0x13b30 that kind 7 shares). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleBuild Require Import EntCut EntFacts Ent5.
Import ListNotations.
Open Scope Z_scope.

(** `t & 3` is t mod 4. *)
Lemma land3 : forall z, Z.land z 3 = z mod 4.
Proof. intros z. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

(** The type and the size kind 6 gives for the table index (pod.h:342-345). *)
Definition ty6 (idx : Z) : Z := nth (Z.to_nat idx) t6 0.
Definition sz6 (idx : Z) : Z := if idx =? 3 then 0 else if idx =? 2 then 4 else 8.

(** The same pointer-overflow check when the base is a literal (the table's address). *)
Lemma not_lit_lt_false : forall x y, 0 <= x < 2^64 -> 0 <= y -> x + y < 2^64 ->
  bv_ltu (Z_to_bv 64 (Z.lxor x 18446744073709551615)) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy Hxy. unfold bv_ltu. rewrite !unsigned_lit_wrap. rewrite zb_lxor_ones by lia.
  rewrite (Z.mod_small (18446744073709551615 - x)) by lia. rewrite (Z.mod_small y) by lia.
  apply Z.ltb_ge. lia.
Qed.

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

(** The body of a pod whose size is sz and whose copied prefix is p, inside the 96-byte array. *)
Lemma body_pad : forall (p : list byte) (sz : Z), (length p <= Z.to_nat sz)%nat -> (Z.to_nat sz <= 96)%nat ->
  p ++ zeros (96 - length p) =
  (p ++ zeros (Z.to_nat sz - length p)) ++ zeros (96 - length (p ++ zeros (Z.to_nat sz - length p))).
Proof.
  intros p sz H1 H2. rewrite length_app, length_zeros, <- app_assoc. f_equal.
  rewrite <- zeros_app. f_equal. lia.
Qed.

Section Case6.
Variables (sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.

(** A slice of the input in any memory the turn reaches. *)
Lemma in_slice : forall mm t' sz' bd' (j n : nat), MemC sp m lo mm t' sz' bd' -> (j <= length r)%nat ->
  bytes_at rsegs mm (src + Z.of_nat j) (firstn n (skipn j r)).
Proof.
  intros mm t' sz' bd' j n MC Hj.
  pose proof (MemC_in sp m r src pp lo HE _ _ _ _ MC) as HI.
  rewrite <- (firstn_skipn j r) in HI. apply bytes_at_app in HI as [_ HS].
  rewrite length_firstn in HS. replace (Nat.min j (length r)) with j in HS by lia.
  rewrite <- (firstn_skipn n (skipn j r)) in HS. apply bytes_at_app in HS as [HP _]. exact HP.
Qed.

(** 0x13b30 -> the join (kinds 6 and 7): the size word, the clamp of the copy to the bytes left, and the copy
    of the next sz bytes of the input (from offset j) into the body. *)
Lemma tail67 : forall (ra t0 t1 t2 s1 a1 a3 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word) m1
    (j : nat) (cur left sz : Z) (p r' : list byte) (e : ent),
  ent_build r = (e, r') -> le4 (Z_to_bv 64 (e_type e)) = le32 (e_type e) -> e_size e = sz ->
  e_body e = p ++ zeros (Z.to_nat sz - length p) ->
  0 <= sz <= 96 -> (j <= length r)%nat -> cur = src + Z.of_nat j -> left = Z.of_nat (length r - j) ->
  p = firstn (Z.to_nat sz) (skipn j r) -> r' = skipn (Z.to_nat sz) (skipn j r) ->
  MemC sp m lo m1 (Z_to_bv 64 (e_type e)) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs (QJ sp gp tp s11 F fc m r src pp lo (ent_build r))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 95) s1 (Z_to_bv 64 (bv_unsigned sp + 192)) a1 (Z_to_bv 64 sz) a3
             (Z_to_bv 64 left) a5 a6 a7 (Z_to_bv 64 (0xcccccccd * 2^32)) (Z_to_bv 64 4) s4 (Z_to_bv 64 cur) s6
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 src)
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b30) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a1 a3 a5 a6 a7 s4 s6 t3 t4 t5 t6 m1 j cur left sz p r' e EB Et Esz Ebd Hsz Hj Ecur
    Eleft Ep Er' MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (Lp : length p = Nat.min (Z.to_nat sz) (length r - j)%nat)
    by (rewrite Ep, length_firstn, length_skipn; reflexivity).
  assert (Lr' : length r' = (length r - j - length p)%nat)
    by (rewrite Er', length_skipn, length_skipn; lia).
  assert (Hcl : cur + Z.of_nat (length p) <= lo) by lia.
  (* 0x13b30 sw a2,0xbc(sp) *)
  est_sz HE MC.
  (* 0x13b34 bltu a2,a4 (keep sz) else 0x13b38 a2 := a4 *)
  step. if_cases T; zify_cond T;
    [ replace (Z_to_bv 64 sz) with (Z_to_bv 64 (Z.of_nat (length p))) by (f_equal; lia)
    | step; replace (Z_to_bv 64 left) with (Z_to_bv 64 (Z.of_nat (length p))) by (f_equal; lia) ];
    (* both: 0x13b3c not a1,s5; 0x13b40 bltu a1,a2 (trap); the copy; the join *)
    (step; step; rewrite not_lt_false by lia; cbv iota;
     do 4 step;
     match goal with MCx : MemC _ _ _ ?mm _ _ _ |- _ =>
       pose proof (in_slice mm _ _ _ j (Z.to_nat sz) MCx Hj) as HB;
       destruct (MemC_cells sp m r src pp lo HE _ _ _ _ (bv_unsigned sp + 192) (length p) MCx
                   ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as (junk & Lj & CJ)
     end;
     rewrite <- Ecur, <- Ep in HB;
     eapply evt_cut;
       [ eapply MCPY;
           [ rewrite unsigned_lit by lia; exact HB
           | rewrite unsigned_lit by lia; lia
           | rewrite !unsigned_lit by lia; rewrite Nat2Z.id; exact CJ
           | rewrite !unsigned_lit by lia; lia
           | match goal with MCx : MemC _ _ _ _ _ _ _ |- _ => exact (MemC_mem_inv _ _ _ _ _ _ _ MCx) end ]
       | ];
     intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E &
                 MU2 & WM2 & MI2 & CE2 & SB2);
     subst ms'; rewrite ret_pc_even by (first [lia | reflexivity]);
     rewrite !unsigned_lit in MU2, CE2 by lia; rewrite Nat2Z.id in CE2;
     match goal with MCx : MemC _ _ _ _ _ _ _ |- _ =>
       assert (MC2 : MemC sp m lo m2 (Z_to_bv 64 (e_type e)) (Z_to_bv 64 sz) (upd_bytes (zeros 96) 0 p))
         by (eapply (MemC_call_bd sp m r src pp lo HE _ m2 (Z_to_bv 64 (e_type e)) (Z_to_bv 64 sz) (zeros 96)
                       (bv_unsigned sp + 192) 0%nat p MCx);
             [ exact MU2 | exact WM2 | exact MI2 | exact (proj1 (rw_CB_bytes m2 _ _ _ CE2))
             | cbn [Z.of_nat]; lia | cbn [length]; lia ]);
       clear MCx
     end;
     clear MU2 WM2 MI2 CE2 SB2;
     rewrite (upd_zeros0 p 96) in MC2 by lia;
     step; step;
     eapply join_13c48; [exact EB | | | reflexivity | exact MC2 | exact Et | | ];
     [ f_equal; rewrite !unsigned_lit by lia; lia
     | f_equal; lia
     | rewrite Esz; apply le4_le32
     | rewrite Ebd; apply body_pad; lia ]).
Qed.

(** 0x13840 -> the join: the type from the table t[] of .rodata, the size the type fixes, then [tail67]. *)
Lemma mid6 : forall (ra t0 t1 t2 s1 a0 a3 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word) m1 (j : nat) (idx cur left : Z),
  0 <= idx < 4 -> (j <= length r)%nat -> cur = src + Z.of_nat j -> left = Z.of_nat (length r - j) ->
  ent_build r =
    (Ent (ty6 idx) (sz6 idx)
       (firstn (Z.to_nat (sz6 idx)) (skipn j r)
        ++ zeros (Z.to_nat (sz6 idx) - length (firstn (Z.to_nat (sz6 idx)) (skipn j r)))),
     skipn (Z.to_nat (sz6 idx)) (skipn j r)) ->
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs (QJ sp gp tp s11 F fc m r src pp lo (ent_build r))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 95) s1 a0 (Z_to_bv 64 idx) (Z_to_bv 64 (67064 + 4 * idx)) a3
             (Z_to_bv 64 left) a5 a6 a7 (Z_to_bv 64 (0xcccccccd * 2^32)) (Z_to_bv 64 4) s4 (Z_to_bv 64 cur) s6
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 src)
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13840) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a0 a3 a5 a6 a7 s4 s6 t3 t4 t5 t6 m1 j idx cur left Hidx Hj Ecur Eleft EB MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI1.
  assert (Hcases : idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3) by lia.
  destruct Hcases as [ -> | [ -> | [ -> | -> ] ] ]; unfold ty6, sz6 in *; cbn [Z.eqb Z.to_nat nth Tables.t6] in *;
    [ pose proof (ro4_read m1 67064 Tables.t6 0%nat MI1 ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
                    ltac:(lia) ltac:(cbn; lia)) as HT
    | pose proof (ro4_read m1 67064 Tables.t6 1%nat MI1 ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
                    ltac:(lia) ltac:(cbn; lia)) as HT
    | pose proof (ro4_read m1 67064 Tables.t6 2%nat MI1 ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
                    ltac:(lia) ltac:(cbn; lia)) as HT
    | pose proof (ro4_read m1 67064 Tables.t6 3%nat MI1 ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
                    ltac:(lia) ltac:(cbn; lia)) as HT ];
    cbn [Z.of_nat nth Tables.t6] in HT;
    (* 0x13840 lw a2,0(a2); 0x13844 sw a2,0xb8(sp); 0x13848 addi a0,sp,0xc0; 0x1384c addi a2,zero,2 *)
    (step; est_t HE MC; step; step;
     (* 0x13850 beq a1,a2 *)
     step; first [ brt | brf ];
     (* 0x1385c / 0x13854-0x13858, then 0x13860-0x1386c and the jump *)
     repeat step;
     eapply tail67;
       [ exact EB | apply le4_le32 | vm_compute; reflexivity | reflexivity
       | vm_compute; split; intro Hx; discriminate Hx
       | exact Hj | exact Ecur | exact Eleft | reflexivity | reflexivity | exact MC ]).
Qed.

Lemma case6_ok_sec : case_at sp gp tp s11 F fc m r src pp lo 6 0x1361c.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (byte_range b) as Rb.
  destruct rest as [|c rest2].
  - (* no byte for the type index *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x1361c beqz s6 (taken); 0x13830 mv a4,zero; mv a1,zero; auipc a0; addi a2 *)
    step. brt. do 4 step.
    replace (Z_to_bv 64 67064) with (Z_to_bv 64 (67064 + 4 * 0)) by (f_equal; lia).
    eapply (mid6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 1%nat 0 (src + 1) 0);
      [ lia | lia | cbn [Z.of_nat]; lia | rewrite L; cbn [Z.of_nat]; lia
      | rewrite Er; cbn [skipn]; exact (eb6_nil b Hk) | exact MC ].
  - (* the type index from the next byte *)
    assert (L : length r = S (S (length rest2))) by (rewrite Er; reflexivity).
    pose proof (byte_range c) as Rc.
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB1.
    rewrite Er in HB1. cbn [nth] in HB1.
    (* 0x1361c beqz s6 (not taken); addi s5,s5,1; addi a0,zero,1; bgeu a0,s5 (trap); lbu a1,1(s9) *)
    step. brf. do 2 step. step. brf. step.
    (* 0x13630 auipc; addi a2; andi a1,a1,3; slli a3,a1,2 *)
    do 4 step. rewrite land3, zxb_un, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    rewrite (unsigned_lit (bv_unsigned c mod 4)) by lia.
    (* 0x13640 not a0,a2; 0x13644 bltu a0,a3 (trap) *)
    step. step. brf.
    (* 0x13648 addi a4,s1,-2; addi s5,s9,2; add a2,a2,a3; j 0x13840 *)
    do 4 step.
    replace (Z_to_bv 64 (67064 + bv_unsigned c mod 4 * 4))
      with (Z_to_bv 64 (67064 + 4 * (bv_unsigned c mod 4))) by (f_equal; lia).
    eapply (mid6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 2%nat (bv_unsigned c mod 4) (src + 2)
              (Z.of_nat (length r) + -2));
      [ lia | lia | cbn [Z.of_nat]; lia | rewrite L; cbn [Z.of_nat]; lia
      | rewrite Er; cbn [skipn]; exact (eb6 b c rest2 Hk) | exact MC ].
Qed.

End Case6.

Theorem case6_ok : forall (sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z),
  ent_pre sp m r src pp lo -> memcpy_contract -> case_at sp gp tp s11 F fc m r src pp lo 6 0x1361c.
Proof. intros. apply case6_ok_sec; assumption. Qed.
