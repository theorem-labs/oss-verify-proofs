(* check_requests (fuzz_link.c:498-517), PLAIN build: the walk of its contract
   (lib/Prog/check_requests_c.v) on the plain image, 0x15284, 200 bytes, frame 48.

   The one argument a0 is the model (the k argument was folded to &g_nl, 0x31b80). `lw s3` of
   g_nl + 0x422a8 (n_sent) and `lw a1` of a0 + 0x2090 (n_req) agree by requests_are, so the first
   `bne` to abort (0x152c4) is not taken; `blez` returns at once for n = 0. The loop (head 0x152e8)
   loads the two lengths, g_nl + 0x42228 + 8 i and a0 + 0x2010 + 8 i, equal by requests_are (the
   `bne` at 0x152f0 is not taken), cuts the length at 0x200 (model_wf already bounds it by 0x200),
   and calls bcmp(g_nl + 0x40224 + 0x200 i, a0 + 0xc + 0x200 i, len): requests_are makes the two
   records equal, so bcmp answers 0 and the `bnez` to abort (0x1530c) is not taken. nlk_wf bounds
   n by 16, so every read stays inside g_nl and the model block. bcmp writes no byte (its contract,
   lib/Prog/bcmp_c.v: munch []), so the function writes only the frame's six saved registers.
   The bcmp contract is the Section hypothesis of the walk; check_requests_holds discharges it with
   bcmp_holds (lib/Prog/bcmp.v).
   Literal addresses below: g_nl = 0x31b80 = 203648; g_nl + NK_SENT = 466340;
   g_nl + NK_SENT_LEN = 474536; g_nl + NK_N_SENT = 474664. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf bcmp_c bcmp check_requests_c hp_ckc_kit.
Local Open Scope Z_scope.

Section Walk.
Hypothesis BC : bcmp_contract.

Theorem check_requests_walk : check_requests_contract.
Proof.
  unfold check_requests_contract. apply leaf_intro.
  - intros r1 r2 m E (kbs & mbs & H). exists kbs, mbs.
    unfold arg, apart_frame, frame_apart_gnl, spZ in *. rewrite <- !E. exact H.
  - intros r1 r2 m _. reflexivity.
  - intros r1 r2 m q1 q2 m' _ _ _. exact I.
  - unfold leaf_walk, CHECK_REQUESTS.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros HP MI ST LO SP. cbv beta in HP.
    destruct HP as (kbs & mbs & [HK LK] & FAG & [HM LM] & KW & MWf & [RA1 RA2] & AF & AG).
    destruct KW as (_ & _ & KW3 & _).
    destruct MWf as (MW1 & _ & _ & _ & MW5 & _).
    unfold frame_apart_gnl, apart_gnl, apart_frame in FAG, AF, AG.
    rewrite ?mkR_a0, ?mkR_sp in *.
    unfold nk_sent_one, md_req_one, NK_SENT, MD_REQ in RA2.
    unfold A_G_NL, NK_SIZE, MD_SIZE, NL_SENT_MAX, NL_SENT_LEN, NK_SENT_LEN, MD_REQ_LEN in *.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
    pose proof (u8arr_bound rsegs m _ _ HK) as BK. pose proof (u8arr_bound rsegs m _ _ HM) as BM.
    rewrite LK in BK. rewrite LM in BM.
    carve_frame 48%nat ST.
    do 7 step.
    pose proof (ck_rd4 m1 _ kbs 271016 HK ltac:(lia) ltac:(lia)) as HR0.
    change (203648 + 271016) with 474664 in HR0.
    pose proof (ck_rd4 m1 _ mbs 8336 HM ltac:(lia) ltac:(lia)) as HR1.
    change (rdn kbs 271016 4) with (nk_n_sent kbs) in HR0. change (rdn mbs 8336 4) with (md_n_req mbs) in HR1.
    do 7 step.
    step. rewrite ck_sx32 by lia.
    step. rewrite ck_sx32 by lia. rewrite <- RA1.
    step. if_false.
    clear HR0 HR1.
    lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
    (* the epilogue: restore ra, s0..s4 from the frame and return *)
    assert (EPI : forall (mm : word -> option byte)
        (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
      munch [] m1 mm -> wmono rsegs m1 mm -> mem_inv rsegs mm ->
      evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
                            x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15328) fc None mm (seg_rom rsegs))).
    { intros mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 MU0 WM0 MI0.
      pose proof (rw_cells_transport rsegs [] m1 mm _ _ FR MU0 WM0 I) as FR0.
      pose proof (stk_transport_disjoint rsegs [] m1 mm lo _ ST MU0 WM0 I) as ST0.
      clear FR ST.
      do 7 step.
      release_frame FR0 ST0 (bv_unsigned sp).
      step.
      apply evt_done. unfold QQ.
      exists (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  x28 x29 x30 x31), mm.
      split; [reflexivity|].
      split; [exact (regs_preserved_mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                       s8 s9 s10 s11 t3 t4 t5 t6 ra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31)|].
      split; [unfold writes_nothing; eapply munch_trans;
              [exact MU | eapply munch_weaken; [|exact MU0]; intros x _; exact I]|].
      split; [eapply wmono_trans; [exact WM | exact WM0]|].
      split; [exact MI0|]. split; [exact ST0|]. exact I. }
    (* the loop over the requests, from the head at 0x152e8 *)
    assert (LOOP : forall (k : nat) (i : Z) (mm : word -> option byte)
        (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
      k = Z.to_nat (nk_n_sent kbs - i) -> 0 <= i < nk_n_sent kbs ->
      x8 = Z_to_bv 64 (466340 + 512 * i) -> x9 = Z_to_bv 64 (bv_unsigned a0 + 12 + 512 * i) ->
      x18 = Z_to_bv 64 (bv_unsigned a0 + 8208 + 8 * i) -> x19 = Z_to_bv 64 (nk_n_sent kbs - i) ->
      x20 = Z_to_bv 64 (474536 + 8 * i) ->
      munch [] m1 mm -> wmono rsegs m1 mm -> mem_inv rsegs mm ->
      evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
                            x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x152e8) fc None mm (seg_rom rsegs))).
    { induction k as [|k IH];
        intros i mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31
          Hk Hi E8 E9 E18 E19 E20 MU0 WM0 MI0; [lia|].
      subst x8 x9 x18 x19 x20.
      pose proof (u8arr_transport rsegs [] m1 mm _ _ HK MU0 WM0 I) as HKm.
      pose proof (u8arr_transport rsegs [] m1 mm _ _ HM MU0 WM0 I) as HMm.
      destruct (RA2 i Hi) as [EL ES].
      pose proof (MW5 i ltac:(lia)) as BL.
      set (L := fld_u64 mbs (8208 + 8 * i)) in *.
      pose proof (ck_rd8 mm _ kbs (270888 + 8 * i) HKm ltac:(lia) ltac:(lia)) as HRa.
      replace (203648 + (270888 + 8 * i)) with (474536 + 8 * i) in HRa by lia.
      change (rdn kbs (270888 + 8 * i) 8) with (fld_u64 kbs (270888 + 8 * i)) in HRa. rewrite EL in HRa.
      pose proof (ck_rd8 mm _ mbs (8208 + 8 * i) HMm ltac:(lia) ltac:(lia)) as HRb.
      replace (bv_unsigned a0 + (8208 + 8 * i)) with (bv_unsigned a0 + 8208 + 8 * i) in HRb by lia.
      change (rdn mbs (8208 + 8 * i) 8) with L in HRb.
      rewrite EL in ES.
      set (ls := slice kbs (262692 + 512 * i) L) in *.
      assert (Lls : length ls = Z.to_nat L) by (unfold ls, slice; rewrite length_firstn, length_skipn; lia).
      assert (BKl : bytes_at rsegs mm (466340 + 512 * i) ls).
      { replace (466340 + 512 * i) with (203648 + (262692 + 512 * i)) by lia.
        apply ck_bytes_sub; [exact (proj1 HKm) | lia | lia | lia]. }
      assert (BMl : bytes_at rsegs mm (bv_unsigned a0 + 12 + 512 * i) ls).
      { rewrite ES. replace (bv_unsigned a0 + 12 + 512 * i) with (bv_unsigned a0 + (12 + 512 * i)) by lia.
        apply ck_bytes_sub; [exact (proj1 HMm) | lia | lia | lia]. }
      (* from the length cut at 0x15300 to the next head *)
      assert (TAIL : forall (z10 z11 z12 z13 : word), z12 = Z_to_bv 64 L ->
        evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 (466340 + 512 * i))
                              (Z_to_bv 64 (bv_unsigned a0 + 12 + 512 * i)) z10 z11 z12 z13 x14 x15 x16 x17
                              (Z_to_bv 64 (bv_unsigned a0 + 8208 + 8 * i)) (Z_to_bv 64 (nk_n_sent kbs - i))
                              (Z_to_bv 64 (474536 + 8 * i)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x15300) fc None mm (seg_rom rsegs))).
      { intros z10 z11 z12 z13 ->.
        step. step. step.
        eapply evt_cut.
        { eapply BC with (ls := ls) (rs := ls) (v := 0).
          - rewrite unsigned_lit by lia. exact BKl.
          - rewrite unsigned_lit by lia. exact BMl.
          - rewrite unsigned_lit by lia. apply ck_memcmp_self. lia.
          - exact MI0. }
        intros ms' PO. unfold memcmp_post in PO.
        destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & mm'
          & -> & MUc & WMc & MIc & _ & _).
        replace (ret_pc (Z_to_bv 64 0x1530c)) with (Z_to_bv 64 0x1530c)
          by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        pose proof (munch_trans [] m1 mm mm' MU0 MUc) as MU1.
        pose proof (wmono_trans rsegs m1 mm mm' WM0 WMc) as WM1.
        step. if_false.
        step. step. step. step. step. step.
        if_cases HC2; zify_cond HC2.
        - eapply (IH (i + 1) mm'); [lia | lia | word_eq_tac | word_eq_tac | word_eq_tac | word_eq_tac
                                  | word_eq_tac | exact MU1 | exact WM1 | exact MIc].
        - apply (EPI mm'); [exact MU1 | exact WM1 | exact MIc]. }
      step. step. step. if_false.
      step. step. if_cases HL; zify_cond HL.
      - apply TAIL. reflexivity.
      - step. apply TAIL. f_equal. lia. }
    step. if_cases HC; zify_cond HC.
    + apply (EPI m1); [apply munch_refl | apply wmono_refl | exact MI].
    + do 7 step.
      eapply (LOOP _ 0 m1); [reflexivity | lia | word_eq_tac | word_eq_tac | word_eq_tac | word_eq_tac
                            | word_eq_tac | apply munch_refl | apply wmono_refl | exact MI].
Qed.
End Walk.

(* the closed contract: bcmp's own walk (lib/Prog/bcmp.v) discharges the callee *)
Theorem check_requests_holds : check_requests_contract.
Proof. exact (check_requests_walk bcmp_holds). Qed.

Print Assumptions check_requests_walk.
Print Assumptions check_requests_holds.
