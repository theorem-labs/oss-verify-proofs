(* check_marks (fuzz_link.c:608-623), PLAIN build: the walk of its contract (lib/Prog/check_marks_c.v)
   on the plain image, 0x15e34, 120 bytes, frame 32.

   `lw s2, 0(a0)` (got->n) and the `lw a2` of a1 + 0x2294 (m->n_mark) agree by marks_are, so the
   first `bne` to abort (0x15e58) is not taken; `blez` returns at once for n = 0. The loop (head
   0x15e70) calls strcmp(a0 + 4 + 16 i, a1 + 0x2094 + 16 i): marks_wf / model_marks_wf put a NUL
   inside each 16-byte slot, and marks_are makes the two C strings equal, so strcmp answers 0 and
   the `bnez` to abort (0x15e7c) is not taken. strcmp leaves memory as it found it (its contract,
   lib/Prog/strcmp_c.v), so the function writes only the frame's four saved registers.
   The strcmp contract is the Section hypothesis of the walk; check_marks_holds discharges it with
   strcmp_holds (lib/Prog/strcmp.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf strcmp_c strcmp check_marks_c hp_ckc_kit.
Local Open Scope Z_scope.

Section Walk.
Hypothesis SC : strcmp_contract.

Theorem check_marks_walk : check_marks_contract.
Proof.
  unfold check_marks_contract. apply leaf_intro.
  - intros r1 r2 m E (gbs & mbs & H). exists gbs, mbs.
    unfold arg, apart_frame, spZ in *. rewrite <- !E. exact H.
  - intros r1 r2 m _. reflexivity.
  - intros r1 r2 m q1 q2 m' _ _ _. exact I.
  - unfold leaf_walk, CHECK_MARKS.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros HP MI ST LO SP. cbv beta in HP.
    destruct HP as (gbs & mbs & [HG LG] & [HM LM] & [GW1 GW2] & [MW1 MW2] & [MA1 MA2] & AF0 & AF1).
    unfold apart_frame in AF0, AF1. rewrite ?mkR_a0, ?mkR_a1, ?mkR_sp in *.
    unfold MK_SIZE, MD_SIZE, MARKS_MAX in *.
    unfold slots_terminated, MK_NAME, MD_MARK, MARK_LEN in GW2, MW2. change (Z.to_nat 16) with 16%nat in GW2, MW2.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
    pose proof (u8arr_bound rsegs m _ _ HG) as BG. pose proof (u8arr_bound rsegs m _ _ HM) as BM.
    rewrite LG in BG. rewrite LM in BM.
    carve_frame 32%nat ST.
    do 5 step.
    pose proof (ck_rd4 m1 _ gbs 0 HG ltac:(lia) ltac:(lia)) as HR0.
    replace (wa (bv_unsigned a0 + 0)) with a0 in HR0 by (unfold wa; rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self).
    pose proof (ck_rd4 m1 _ mbs 8852 HM ltac:(lia) ltac:(lia)) as HR1.
    change (rdn gbs 0 4) with (mk_n gbs) in HR0. change (rdn mbs 8852 4) with (md_n_mark mbs) in HR1.
    step. rewrite ck_sx32 by lia.
    step. step. step. rewrite ck_sx32 by lia. rewrite <- MA1.
    step. if_false.
    clear HR0 HR1.
    lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
    (* the epilogue: restore ra, s0, s1, s2 from the frame and return *)
    assert (EPI : forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
      evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
                            x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15e90) fc None m1 (seg_rom rsegs))).
    { intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31.
      do 5 step.
      release_frame FR ST (bv_unsigned sp).
      step.
      apply evt_done. unfold QQ.
      exists (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  x28 x29 x30 x31), m1.
      split; [reflexivity|].
      split; [exact (regs_preserved_mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                       s8 s9 s10 s11 t3 t4 t5 t6 ra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31)|].
      split; [unfold writes_nothing; exact MU|].
      split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact I. }
    (* the loop over the slots, from the head at 0x15e70 *)
    assert (LOOP : forall (k : nat) (i : Z)
        (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
      k = Z.to_nat (mk_n gbs - i) -> 0 <= i < mk_n gbs ->
      x8 = Z_to_bv 64 (bv_unsigned a0 + 4 + 16 * i) -> x9 = Z_to_bv 64 (bv_unsigned a1 + 8340 + 16 * i) ->
      x18 = Z_to_bv 64 (mk_n gbs - i) ->
      evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
                            x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15e70) fc None m1 (seg_rom rsegs))).
    { induction k as [|k IH];
        intros i x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 Hk Hi E8 E9 E18; [lia|].
      subst x8 x9 x18.
      set (gl := slice gbs (4 + 16 * i) 16).
      set (ml := slice mbs (8340 + 16 * i) 16).
      assert (LGl : length gl = 16%nat) by (unfold gl, slice; rewrite length_firstn, length_skipn; lia).
      assert (LMl : length ml = 16%nat) by (unfold ml, slice; rewrite length_firstn, length_skipn; lia).
      pose proof (GW2 i Hi) as NG. pose proof (MW2 i ltac:(lia)) as NM. fold gl in NG. fold ml in NM.
      destruct (ck_cstr_split gl ltac:(lia)) as [SG NZG].
      destruct (ck_cstr_split ml ltac:(lia)) as [SM NZM].
      assert (BGl : bytes_at rsegs m1 (bv_unsigned a0 + 4 + 16 * i) (cstr gl ++ [Z_to_bv 8 0])).
      { rewrite <- SG. replace (bv_unsigned a0 + 4 + 16 * i) with (bv_unsigned a0 + (4 + 16 * i)) by lia.
        apply ck_bytes_prefix; [| lia].
        apply ck_bytes_sub; [exact (proj1 HG) | lia | lia | lia]. }
      assert (BMl : bytes_at rsegs m1 (bv_unsigned a1 + 8340 + 16 * i) (cstr ml ++ [Z_to_bv 8 0])).
      { rewrite <- SM. replace (bv_unsigned a1 + 8340 + 16 * i) with (bv_unsigned a1 + (8340 + 16 * i)) by lia.
        apply ck_bytes_prefix; [| lia].
        apply ck_bytes_sub; [exact (proj1 HM) | lia | lia | lia]. }
      assert (EQ : cstr gl = cstr ml).
      { unfold mk_names, md_marks in MA2. rewrite <- MA1 in MA2.
        pose proof (ck_map_seq_eq _ _ _ (Z.to_nat i) MA2 ltac:(lia)) as E. cbv beta in E.
        rewrite Z2Nat.id in E by lia. exact E. }
      step. step. step.
      eapply evt_cut.
      { eapply SC with (sx := cstr gl) (sy := cstr ml).
        - rewrite unsigned_lit by lia. exact BGl.
        - exact NZG.
        - rewrite unsigned_lit by lia. exact BMl.
        - exact NZM. }
      intros ms' (r & y11 & y12 & y13 & -> & Hr).
      replace (ret_pc (Z_to_bv 64 0x15e7c)) with (Z_to_bv 64 0x15e7c)
        by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      assert (Er : r = Z_to_bv 64 0) by (apply Hr; exact EQ). subst r.
      step. if_false.
      step. step. step. step.
      if_cases HC2; zify_cond HC2.
      - eapply (IH (i + 1)); [lia | lia | word_eq_tac | word_eq_tac | word_eq_tac].
      - apply EPI. }
    step. if_cases HC; zify_cond HC.
    + apply EPI.
    + step. step. step. step.
      eapply (LOOP _ 0); [reflexivity | lia | word_eq_tac | word_eq_tac | word_eq_tac].
Qed.
End Walk.

(* the closed contract: strcmp's own walk (lib/Prog/strcmp.v) discharges the callee *)
Theorem check_marks_holds : check_marks_contract.
Proof. exact (check_marks_walk strcmp_holds). Qed.

Print Assumptions check_marks_walk.
Print Assumptions check_marks_holds.
