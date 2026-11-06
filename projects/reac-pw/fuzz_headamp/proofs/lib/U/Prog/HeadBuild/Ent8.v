(** ent_build's kind 8 in the UBSan image (pod.h:358-365): a scalar or a String with a body too short for its type.
    From the jump table's target 0x137ec to the join 0x13df0: t = fuzz_u8 picks the type from t[] (0x105e0), s =
    fuzz_u8 % 4 the size (none for a String), memset(e->body, 0, size) at 0x13bbc; 0x13ba4 when no byte is left. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

Section Case8.
Variables (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MSET : memset_contract.

Local Abbreviation QE := (QJ sp gp tp s1 F fc m r src pp lo (ent_build r)).

(** The tail 0x13bb4: the size n stored, memset(e->body, 0, n), s10 = s5, s2 = s4, the join. *)
Lemma case8_tail : forall (ra t0 t1 t2 s2 a1 a3 a4 a5 a6 a7 s4 s5 s6 s10 t3 t4 t5 t6 : word) m1 ty (n : Z) r',
  MemC sp m lo m1 (Z_to_bv 64 ty) (Z_to_bv 64 0) (zeros 96) ->
  ent_build r = (Ent ty n (zeros (Z.to_nat n)), r') -> 0 <= ty < 2^32 -> 0 <= n < 4 ->
  s4 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1 (Z_to_bv 64 (bv_unsigned sp + 192)) a1 (Z_to_bv 64 n)
             a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (0xcccccccd * 2^32)) s4 s5 s6
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 95) s10 (Z_to_bv 64 4) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13bb4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s2 a1 a3 a4 a5 a6 a7 s4 s5 s6 s10 t3 t4 t5 t6 m1 ty n r' MC Eb Hty Hn E4 E5.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13bb4 sw a2,0xbc(sp); mv a1,zero; jal memset *)
  est_sz HE MC. do 2 step.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI1.
  destruct (MemC_cells sp m r src pp lo HE _ _ _ _ (bv_unsigned sp + 192) (Z.to_nat n) MC ltac:(lia)
    ltac:(unfold FRAME_LOCALS; lia)) as (junk & LJ & CJ).
  eapply evt_cut.
  { eapply MSET with (junk := junk). { rewrite !unsigned_lit by lia. exact CJ. } exact MI1. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mx &
              E & MU2 & WM2 & MI2 & CE2).
  subst ms'. rewrite ret_pc_even by (first [lia | reflexivity]).
  rewrite !unsigned_lit in MU2, CE2 by lia.
  replace (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat n)) with (zeros (Z.to_nat n)) in CE2 by reflexivity.
  apply rw_CB_bytes in CE2 as [B2 _].
  replace (bv_unsigned sp + 192 + n) with (bv_unsigned sp + 192 + Z.of_nat (length (zeros (Z.to_nat n)))) in MU2
    by (rewrite length_zeros; lia).
  pose proof (MemC_call_bd sp m r src pp lo HE _ mx _ _ _ _ 0 (zeros (Z.to_nat n)) MC MU2 WM2 MI2 B2 ltac:(lia)
    ltac:(rewrite length_zeros; lia)) as MC2.
  clear MC MU2 WM2 MI2 B2 MI1 CJ LJ junk. rename MC2 into MC.
  (* 0x13bc0 mv s10,s5; mv s2,s4; j *)
  do 3 step.
  eapply join_13df0; [exact Eb | exact E4 | exact E5 | reflexivity | exact MC | | | ].
  - apply le4_le32.
  - apply le4_le32.
  - cbn [e_body]. apply upd_zeros0. rewrite length_zeros. lia.
Qed.

Lemma case8_ok_sec : case_at sp gp tp s1 F fc m r src pp lo 8 0x137ec.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 b rest m1 Er Hk Hs MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI1.
  destruct rest as [|c rest].
  - (* no byte for t: t = 0, type t[0] = Int, size 0 *)
    assert (L : length r = 1%nat) by (rewrite Er; reflexivity).
    (* 0x137ec beqz s6; 0x13ba4 mv s4,zero; mv a2,zero; sw s11,0xb8(sp); addi a0,sp,0xc0 *)
    step. brt. do 2 step. est_t HE MC. step.
    eapply (case8_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 0 []); [exact MC | | lia | lia | | ].
    + eb_tac Er Hk.
    + reflexivity.
    + f_equal. rewrite L. cbn [length]. lia.
  - assert (L : length r = S (S (length rest))) by (rewrite Er; reflexivity).
    (* 0x137ec beqz s6; addi s5,s5,1; addi a0,zero,1; bltu a0,s5,8 over the trap (taken) *)
    step. brf. do 2 step. step. brt.
    (* 0x13800 lbu a0,1(s10) *)
    pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 1 MC ltac:(lia)) as HB1. rewrite Er in HB1. cbn [nth] in HB1.
    step.
    (* 0x13804 auipc; addi a1 = t[]; andi a4,a0,3 *)
    do 3 step.
    match goal with |- context [Z_to_bv 64 (Z.land ?X 3)] =>
      replace (Z.land X 3) with (bv_unsigned c mod 4) by (symmetry; byte_eq c) end.
    assert (Hc : bv_unsigned c mod 4 = 0 \/ bv_unsigned c mod 4 = 1 \/ bv_unsigned c mod 4 = 2 \/
                 bv_unsigned c mod 4 = 3) by (pose proof (Z.mod_pos_bound (bv_unsigned c) 4); lia).
    destruct Hc as [K|[K|[K|K]]]; rewrite K;
      (* 0x13810 slli; not; bgeu,8 over the trap (taken); mv a2,zero; add; lw a1 = t[c % 4]; addi s4,s2,-2;
         addi s5,s10,2 *)
      (do 2 step; step; brt; do 5 step;
       (* 0x13834 sw a1,0xb8(sp); beqz s4 *)
       est_t HE MC; step;
       destruct rest as [|d rest]; cbn [length] in L;
       [ (* no byte for s: size 0 *)
         brt; step;
         eapply case8_tail;
         [ exact MC | rewrite Er; unfold ent_build; cbn [fuzz_u8]; rewrite Hk, K; reflexivity | lia | lia
         | f_equal; rewrite L; cbn [length]; lia | f_equal; rewrite L; cbn [length]; lia ]
       | brf; do 2 step; step;
         lazymatch type of K with
         | _ = 3 =>
             (* a String: size 0, s not read *)
             brt;
             eapply case8_tail;
             [ exact MC | rewrite Er; unfold ent_build; cbn [fuzz_u8]; rewrite Hk, K; reflexivity | lia | lia
             | f_equal; rewrite L; cbn [length]; lia | f_equal; rewrite L; cbn [length]; lia ]
         | _ =>
             brf; do 2 step; step; brt;
             (* 0x13858 lbu a2,2(s10); addi s4,s2,-3; addi s5,s10,3; andi a2,a2,3; j 0x13bb4 *)
             let HB2 := fresh "HB2" in
             pose proof (MemC_in_byte sp m r src pp lo HE _ _ _ _ 2 MC ltac:(rewrite L; cbn [length]; lia)) as HB2;
             rewrite Er in HB2; cbn [nth] in HB2;
             step; do 3 step;
             match goal with |- context [Z_to_bv 64 (Z.land ?X 3)] =>
               replace (Z.land X 3) with (bv_unsigned d mod 4) by (symmetry; byte_eq d) end;
             step;
             eapply case8_tail;
             [ exact MC | rewrite Er; unfold ent_build; cbn [fuzz_u8]; rewrite Hk, K; reflexivity | lia
             | pose proof (Z.mod_pos_bound (bv_unsigned d) 4); lia
             | f_equal; rewrite L; cbn [length]; lia | f_equal; rewrite L; cbn [length]; lia ]
         end ]).
Qed.

End Case8.

Theorem case8_ok : forall (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z),
  ent_pre sp m r src pp lo -> memset_contract -> case_at sp gp tp s1 F fc m r src pp lo 8 0x137ec.
Proof. intros. apply case8_ok_sec; assumption. Qed.
