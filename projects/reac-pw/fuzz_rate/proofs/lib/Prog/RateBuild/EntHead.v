(** The head of one ent_build turn (0x13564 .. 0x135c4): memset(e, 0, 104), kind = fuzz_u8, kind % 10, and the
    dispatch (kind 9 by the branch to 0x1396c, kinds 0-8 by `jr a1` through the table at 0x10548, the empty input by
    the branch to 0x135e4), given the case entries of EntFacts.v as premises. Ported from reac-pw/fuzz_role's
    Prog/RoleBuild/EntHead.v at rate's registers, frame cells and pcs
    (role s4 s5 s6 s10 s11 = rate s6 s7 s8 s3 s1 here; e at sp + 0xb8). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** kind % 10 as the code computes it (0x13580-0x13594, s3 = 10), and the sign of (int8) kind (0x135b8, 0x135c0). *)
Lemma kind_mod10 : forall b : byte,
  Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (zxb b) -
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b) * 205)))
      11)) * 10)))))) 255
  = bv_unsigned b mod 10.
Proof. byte_eq. Qed.

Lemma kind_sign : forall b : byte,
  (bv_signed (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b)) 56))) 56)) <? 0)
  = Z.testbit (bv_unsigned b) 7.
Proof. byte_eq. Qed.

Lemma kind_sign_iff : forall b : byte,
  bv_signed (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b)) 56))) 56)) < 0 <->
  Z.testbit (bv_unsigned b) 7 = true.
Proof. intros b. rewrite <- kind_sign. rewrite Z.ltb_lt. reflexivity. Qed.

Section Head.
Variables (sp gp tp s2 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MSET : memset_contract.
Hypothesis C0N : case0_nil_at sp gp tp s2 s9 F fc m r src pp lo.
Hypothesis C0 : case_at sp gp tp s2 s9 F fc m r src pp lo 0 0x135c8.
Hypothesis C1 : case_at sp gp tp s2 s9 F fc m r src pp lo 1 0x138a4.
Hypothesis C2 : case_at sp gp tp s2 s9 F fc m r src pp lo 2 0x137b0.
Hypothesis C3 : case_at sp gp tp s2 s9 F fc m r src pp lo 3 0x13804.
Hypothesis C4 : case_at sp gp tp s2 s9 F fc m r src pp lo 4 0x13770.
Hypothesis C5 : case_at sp gp tp s2 s9 F fc m r src pp lo 5 0x138dc.
Hypothesis C6 : case_at sp gp tp s2 s9 F fc m r src pp lo 6 0x138f4.
Hypothesis C7 : case_at sp gp tp s2 s9 F fc m r src pp lo 7 0x13848.
Hypothesis C8 : case_at sp gp tp s2 s9 F fc m r src pp lo 8 0x13910.
Hypothesis C9 : case9_at sp gp tp s2 s9 F fc m r src pp lo.

(** At 0x13564 with rb_ent_contract's entry registers: s0 = 95, s1 = pp, s3 = 10, s4 = 0xcccccccd << 32, s6 = |r|,
    s8 = src, s10 = sp + 0x158, s11 = sp + 0x120; s2 and s9 kept for QJ; every other register arbitrary. *)
Lemma head_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 : word),
  evt rsegs (QJ sp gp tp s2 s9 F fc m r src pp lo (ent_build r))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 95) (Z_to_bv 64 pp)
             a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 10) (Z_to_bv 64 (0xcccccccd * 2^32)) s5
             (Z_to_bv 64 (Z.of_nat (length r))) s7 (Z_to_bv 64 src) s9
             (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 (bv_unsigned sp + 0x120)) t3 t4 t5 t6)
        F (Z_to_bv 64 ENT_HEAD) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6.
  pose proof (ep_range sp m r src pp lo HE) as R.
  destruct (MemC_init sp m r src pp lo HE) as (eb & MC).
  pose proof (MemC_len _ _ _ _ _ _ _ _ MC) as Leb.
  assert (CE : rw_cells rsegs m (bv_unsigned sp + 184) [CB 104 eb]).
  { rewrite <- Leb. apply (stk_bytes_rw m lo (bv_unsigned sp + FRAME_LOCALS));
      [exact (MemC_stk _ _ _ _ _ _ _ _ MC) | exact (MemC_e _ _ _ _ _ _ _ _ MC) | | rewrite Leb; unfold FRAME_LOCALS]; lia. }
  unfold ENT_HEAD.
  (* 0x13564 addi a0,sp,0xb8; addi a2,zero,0x68; mv a1,zero; jal memset *)
  do 4 step.
  eapply evt_cut.
  { eapply MSET with (junk := eb).
    - rewrite !unsigned_lit by lia. exact CE.
    - exact (MemC_mem_inv _ _ _ _ _ _ _ _ MC). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
              E & MU1 & WM1 & MI1 & RC1).
  subst ms'. rewrite !unsigned_lit in MU1, RC1 by lia.
  apply rw_CB_bytes in RC1 as [B1 L1].
  pose proof (MemC_call_e sp m r src pp lo HE m m1 eb _ 104 _ MC MU1 WM1 MI1 B1
                ltac:(rewrite L1; reflexivity) ltac:(lia) ltac:(lia)) as MC1.
  replace (bv_unsigned sp + 184 - (bv_unsigned sp + 184)) with 0 in MC1 by lia.
  apply (MemC_e_ext _ _ _ _ _ _ _ _ (zeros 104)) in MC1;
    [|rewrite upd_bytes_all by (rewrite L1, Leb; reflexivity); vm_compute; reflexivity].
  clear MU1 WM1 MI1 B1 L1 MC CE.
  rewrite ret_pc_even by (lia || reflexivity).
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ _ MC1) as MI1.
  (* 0x13574 beqz s6 *)
  step.
  assert (Hr : r = [] \/ exists b rest, r = b :: rest)
    by (destruct r as [|b rest]; [left; reflexivity | right; exists b, rest; reflexivity]).
  destruct Hr as [Er | (b & rest & Er)].
  - (* no byte left: kind = 0, to 0x135e4 *)
    replace (bv_eqb (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 0)) with true by (rewrite Er; reflexivity).
    cbv iota.
    eapply C0N; [exact Er | rewrite Er; reflexivity | reflexivity | exact MC1].
  - assert (Lr : length r = S (length rest)) by (rewrite Er; reflexivity).
    unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length r))) by lia.
    if_false.
    (* 0x13578 lbu a0,0(s8) .. 0x13594: kind % 10 *)
    assert (HR : ov_read_bytes rsegs m1 (wa (src + Z.of_nat 0)) 1 = Some [b]).
    { rewrite (MemC_in_byte sp m r src pp lo m1 (zeros 104) 0 MC1) by lia. rewrite Er. reflexivity. }
    do 8 step. clear HR.
    rewrite kind_mod10.
    pose proof (Z.mod_pos_bound (bv_unsigned b) 10 ltac:(lia)) as Hm.
    (* 0x13598 addi a5,s8,1; addi a2,zero,8; bltu a2,a1 *)
    do 3 step.
    unfold bv_ltu. rewrite (unsigned_lit (bv_unsigned b mod 10)) by lia.
    destruct (Z.le_gt_cases (bv_unsigned b mod 10) 8) as [Hle|Hgt].
    + if_false.
      (* 0x135a4 .. 0x135c4: the table's entry, (int8) kind to s1, `jr a1` *)
      assert (Hk : bv_unsigned b mod 10 = 0 \/ bv_unsigned b mod 10 = 1 \/ bv_unsigned b mod 10 = 2 \/
                   bv_unsigned b mod 10 = 3 \/ bv_unsigned b mod 10 = 4 \/ bv_unsigned b mod 10 = 5 \/
                   bv_unsigned b mod 10 = 6 \/ bv_unsigned b mod 10 = 7 \/ bv_unsigned b mod 10 = 8) by lia.
      pose proof (kind_sign_iff b) as KS.
      clear Hle Hm.
      destruct Hk as [Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|Hk]]]]]]]]; rewrite Hk; do 9 step;
        [ eapply C0 | eapply C1 | eapply C2 | eapply C3 | eapply C4 | eapply C5 | eapply C6 | eapply C7 | eapply C8 ];
        first [ exact Er | exact Hk | exact KS | reflexivity | f_equal; lia | exact MC1 ].
    + (* kind 9: 0x1396c *)
      if_true.
      eapply C9; [exact Er | lia | reflexivity | reflexivity | f_equal; lia | reflexivity | reflexivity | exact MC1].
Qed.

End Head.
