(** ent_build's kind 8 in the UBSan image (pod.h:358-365): a scalar or a String with a body too short for its type.
    From the jump table's target 0x13830 to the join 0x13ee4: t = fuzz_u8 picks the type from t8 (0x10618), s =
    fuzz_u8 % 4 the size (none for a String), memset(e->body, 0, size) at 0x13c78; 0x13c60 when no byte is left,
    0x13c68 when no byte is left for s or the type is a String. The form is reac-pw/fuzz_role's
    U/Prog/RoleBuild/Ent8.v re-walked at rate's registers:
    |r'| in s8 and the cursor in s7 across memset, s11
    reloaded at 0x13884 / 0x13c68 and s8 at 0x13c84. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

Section Case8.
Variables (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MSET : memset_contract.

Local Abbreviation QE := (QJ sp gp tp s3 F fc m r src pp lo (ent_build r)).

(** The tail 0x13c6c: the size n stored, memset(e->body, 0, n), t1 = s8, s9 = s7, s8 reloaded, the join. The body
    bd is its own argument (a String's [] does not unify with zeros (Z.to_nat ?n) before n is known). *)
Lemma case8_tail : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m1 ty (n : Z) bd r',
  MemC sp m lo m1 (Z_to_bv 64 ty) (Z_to_bv 64 0) (zeros 96) ->
  ent_build r = (Ent ty n bd, r') -> bd = zeros (Z.to_nat n) -> 0 <= n < 4 ->
  a2 = Z_to_bv 64 n ->
  s8 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s7 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  s11 = Z_to_bv 64 (pp + POD_LEN_OFF) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x188)) (Z_to_bv 64 4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 95) s3 (Z_to_bv 64 (0xcccccccd * 2^32)) (Z_to_bv 64 10) (Z_to_bv 64 0x4000) s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c6c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1 ty n bd r' MC Eb Ebd Hn E2 E8 E7 E11.
  subst bd a2 s8 s7 s11.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13c6c sw a2,0xec(sp); addi a0,sp,0xf0; mv a1,zero; jal memset *)
  est_sz HE MC. do 3 step.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI1.
  destruct (MemC_cells sp m r src pp lo HE _ _ _ _ (bv_unsigned sp + 240) (Z.to_nat n) MC ltac:(lia)
    ltac:(unfold FRAME_LOCALS; lia)) as (junk & LJ & CJ).
  eapply evt_cut.
  { eapply MSET with (junk := junk). { rewrite !unsigned_lit by lia. exact CJ. } exact MI1. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mx &
              E & MU2 & WM2 & MI2 & CE2).
  subst ms'. rewrite ret_pc_even by (first [lia | reflexivity]).
  rewrite !unsigned_lit in MU2, CE2 by lia.
  replace (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat n)) with (zeros (Z.to_nat n)) in CE2 by reflexivity.
  apply rw_CB_bytes in CE2 as [B2 _].
  replace (bv_unsigned sp + 240 + n) with (bv_unsigned sp + 240 + Z.of_nat (length (zeros (Z.to_nat n)))) in MU2
    by (rewrite length_zeros; lia).
  pose proof (MemC_call_bd sp m r src pp lo HE _ mx _ _ _ _ 0 (zeros (Z.to_nat n)) MC MU2 WM2 MI2 B2 ltac:(lia)
    ltac:(rewrite length_zeros; lia)) as MC2.
  clear MC MU2 WM2 MI2 B2 MI1 CJ LJ junk. rename MC2 into MC.
  (* 0x13c7c mv t1,s8; mv s9,s7; ld s8,0xd8(sp); j 0x13ee4 *)
  do 2 step.
  pose proof (MemC_cd8 sp m r src pp lo HE _ _ _ _ MC) as Rd8. step. clear Rd8.
  step.
  eapply join_13ee4; [exact Eb | reflexivity | reflexivity | exact MC | | | ].
  - apply le4_le32.
  - apply le4_le32.
  - cbn [e_body]. apply upd_zeros0. rewrite length_zeros. lia.
Qed.

Lemma case8_ok_sec : case_at sp gp tp s3 F fc m r src pp lo 8 0x13830.
Proof.
  intros ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI1.
  destruct rest as [|c rest].
  - (* no byte for t: t = 0, type t8[0] = Int (s1 = 4), size 0 *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x13830 beqz s8 (taken); 0x13c60 mv a2,zero; sw s1,0xe8(sp); 0x13c68 ld s11,0xc8(sp) *)
    step. brt. step. est_t HE MC.
    pose proof (MemC_cc8 sp m r src pp lo HE _ _ _ _ MC) as Rc8. step. clear Rc8.
    eapply (case8_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 0 _ []); [exact MC | | reflexivity | lia | | | | ].
    + eb_tac Er Hk.
    + reflexivity.
    + f_equal. rewrite L. cbn [length]. lia.
    + f_equal. rewrite L. cbn [length]. lia.
    + reflexivity.
  - assert (L : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    (* 0x13830 beqz s8 (not taken); addi s7,s7,1; addi a0,zero,1; bgeu a0,s7 (trap) *)
    step. brf. do 2 step. step. brf.
    (* 0x13840 lbu a0,1(s9) *)
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB1. rewrite Er in HB1. cbn [nth] in HB1.
    step.
    (* 0x13844 auipc; addi a1 = t8 (0x10618); andi a0,a0,3 *)
    do 3 step.
    match goal with |- context [Z_to_bv 64 (Z.land ?X 3)] =>
      replace (Z.land X 3) with (bv_unsigned c mod 4) by (symmetry; byte_eq c) end.
    assert (Hc : bv_unsigned c mod 4 = 0 \/ bv_unsigned c mod 4 = 1 \/ bv_unsigned c mod 4 = 2 \/
                 bv_unsigned c mod 4 = 3) by (pose proof (Z.mod_pos_bound (bv_unsigned c) 4); lia).
    destruct Hc as [K|[K|[K|K]]]; rewrite K;
      (* 0x13850 slli a3,a0,2; not a2,a1; bltu a2,a3 (trap); mv a2,zero; add a1,a1,a3; lw a1 = t8[c % 4];
         addi s8,t1,-2; addi s7,s9,2 *)
      (do 2 step; step; brf; do 5 step;
       (* 0x13870 sw a1,0xe8(sp); beqz s8 *)
       est_t HE MC; step;
       destruct rest as [|d rest]; cbn [length] in L;
       [ (* no byte for s: size 0; 0x13c68 ld s11,0xc8(sp) *)
         brt;
         let Rc8 := fresh "Rc8" in
         pose proof (MemC_cc8 sp m r src pp lo HE _ _ _ _ MC) as Rc8; step; clear Rc8;
         eapply case8_tail;
         [ exact MC | rewrite Er; unfold ent_build; cbn [fuzz_u8]; rewrite Hk, K; reflexivity | reflexivity | lia
         | reflexivity | f_equal; rewrite L; cbn [length]; lia | f_equal; rewrite L; cbn [length]; lia
         | reflexivity ]
       | (* 0x13878 addi a1,zero,3; beq a0,a1 *)
         brf; step; step;
         lazymatch type of K with
         | _ = 3 =>
             (* a String: size 0, s not read; 0x13c68 ld s11,0xc8(sp) *)
             brt;
             let Rc8 := fresh "Rc8" in
             pose proof (MemC_cc8 sp m r src pp lo HE _ _ _ _ MC) as Rc8; step; clear Rc8;
             eapply case8_tail;
             [ exact MC | rewrite Er; unfold ent_build; cbn [fuzz_u8]; rewrite Hk, K; reflexivity | reflexivity | lia
             | reflexivity | f_equal; rewrite L; cbn [length]; lia | f_equal; rewrite L; cbn [length]; lia
             | reflexivity ]
         | _ =>
             (* 0x13880 addi s7,s7,1; ld s11,0xc8(sp); addi a0,zero,1; bgeu a0,s7 (trap) *)
             brf; step;
             let Rc8 := fresh "Rc8" in
             pose proof (MemC_cc8 sp m r src pp lo HE _ _ _ _ MC) as Rc8; step; clear Rc8;
             step; step; brf;
             (* 0x13890 lbu a2,2(s9); addi s8,t1,-3; addi s7,s9,3; andi a2,a2,3; j 0x13c6c *)
             let HB2 := fresh "HB2" in
             pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 2 MC ltac:(rewrite L; cbn [length]; lia)) as HB2;
             rewrite Er in HB2; cbn [nth] in HB2;
             step; do 3 step;
             match goal with |- context [Z_to_bv 64 (Z.land ?X 3)] =>
               replace (Z.land X 3) with (bv_unsigned d mod 4) by (symmetry; byte_eq d) end;
             step;
             eapply case8_tail;
             [ exact MC | rewrite Er; unfold ent_build; cbn [fuzz_u8]; rewrite Hk, K; reflexivity | reflexivity
             | pose proof (Z.mod_pos_bound (bv_unsigned d) 4); lia
             | reflexivity | f_equal; rewrite L; cbn [length]; lia | f_equal; rewrite L; cbn [length]; lia
             | reflexivity ]
         end ]).
Qed.

End Case8.

Theorem case8_ok : forall (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte) (src pp lo : Z), ent_pre sp m r src pp lo -> memset_contract -> case_at sp gp tp s3 F fc m r src pp lo 8 0x13830.
Proof. intros. apply case8_ok_sec; assumption. Qed.
