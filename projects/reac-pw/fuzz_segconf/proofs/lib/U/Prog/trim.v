(** The walk of trim (reac_segconf.c:50-59, static) in the UBSan image 1696d6c34ffd (U/Prog/trim_c.v); the same
    plan as Prog/trim.v, whose image-free lemmas (TrimSpine) it imports. strlen is a premise (strlen_contract,
    U/Prog/strlen_c.v, 0x1f5cc).

    Code (UBSan image; frame 32: ra at sp+24, s0 at sp+16, s1 at sp+8):
      0x15db4-0x15dc8  frame, s0 = s, s1 = s + 1; 0x15dcc-0x15ddc a0 = 0x20, a1 = 0x100002200, a2 = -1
      LEAD 0x15de0 lbu a3,0(s0); bltu a0,a3 -> 0x15e04; srl/andi; beqz -> 0x15e04; beq s0,a2 -> trap; s0++; s1++
      0x15e04 a0 = s0; jal strlen; a1 = -s1; bltu a1,a0 -> trap; a1 = s0 + a0; beqz a0 -> 0x15e58;
           0x15e1c-0x15e2c a0 = 1, a2 = 0x20, a3 = mask
      TRAIL 0x15e30 beq a1,a0 -> trap; a4 = a1 - 1; lbu a5,0(a4); bltu a2,a5 -> 0x15e58; srl/andi; beqz -> 0x15e58;
           a1 = a4; bltu s0,a4 -> TRAIL; j 0x15e5c
      0x15e58 a4 = a1; 0x15e5c sb zero,0(a4); a0 = s0; restore; ret; 0x15e78 unimp
    The three traps are dead: s0 < s + |s| <= 2^64 - 1 in LEAD; s0 + |s1| + 1 = s + |s| + 1 <= 2^64 (s1 = s0 + 1
    wraps to 0 only when s0 + 1 = 2^64, and then |s1| = 0); e >= s0 + 1 >= 2 in TRAIL since s <> 0. *)
From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strlen_c trim_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require trim.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.trim.TrimSpine.
Import ListNotations.
Open Scope Z_scope.

Theorem trim_holds : strlen_contract -> trim_contract.
Proof.
  intros SL. unfold trim_contract, TRIM, trim_pre, TRIM_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s
    (P0 & CS & WR & AP & SO & MI).
  destruct CS as (bs & sl0 & BY0 & ZS & NZ & SL80).
  assert (LB : length bs = length s) by (rewrite <- ZS; symmetry; apply len_zs).
  rewrite <- LB in SL80.
  destruct (slack_cut _ _ _ _ _ BY0 SL80) as (sl & BY & SL7 & SL8). clear BY0 SL80 sl0.
  destruct SO as (ST & D32 & AL & NR).
  unfold apart in AP.
  pose proof (bytes_at_bound _ _ _ _ BY) as B1. rewrite length_app in B1. cbn [length] in B1.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (lead_le s NZ) as LL.
  pose proof (s1_len s NZ) as S1L.
  pose proof (rtrim_len s NZ) as RTL.
  pose proof (te_le s (length (s1_of s))) as TEL.
  assert (HR : forall i, 0 <= nth i s 0 < 256) by (intros i; rewrite <- ZS; apply zs_range).
  assert (HB : forall i, (i <= length s)%nat -> nth_error (bs ++ ZERO :: sl) i = Some (Z_to_bv 8 (nth i s 0)))
    by (intros i Hi; rewrite <- ZS; apply byte_at; lia).
  assert (HE : trim_end_addr (bv_unsigned a0) s =
               bv_unsigned a0 + Z.of_nat (trim_lead s) + Z.of_nat (te s (length (s1_of s))))
    by (unfold trim_end_addr; rewrite RTL; lia).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp);
              (trim_end_addr (bv_unsigned a0) s, trim_end_addr (bv_unsigned a0) s + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 32%nat ST.
  zstep. zstep. zstep.
  zstep. zstep.
  zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mm _) => set (POST := QQ); rename mm into M1 end.
  (* 0x15e04: s0 = s + trim_lead s, s1 = s0 + 1; strlen(s0); the pointer-overflow check of s0 + |s1|; back over
     the trailing blanks; *e = 0; return s0. *)
  assert (AFTER : forall (x8 x9 x12 x13 : word), bv_unsigned x8 = bv_unsigned a0 + Z.of_nat (trim_lead s) ->
    bv_unsigned x9 = (bv_unsigned x8 + 1) mod 2 ^ 64 ->
    evt rsegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 32) (Z_to_bv 64 4294976000)
               x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15e04) fc None M1 (seg_rom rsegs))).
  { intros x8 x9 x12 x13 H8 H9.
    zstep. zstep.
    assert (BYL : bytes_at rsegs M1 (bv_unsigned x8) (skipn (trim_lead s) bs ++ ZERO :: sl)).
    { rewrite H8, <- skipn_app_le by lia. apply bytes_at_skip; [rewrite length_app; lia | exact BY]. }
    assert (NZL : ~ In (Z_to_bv 8 0) (skipn (trim_lead s) bs)).
    { intros Hin. apply in_skipn' in Hin. revert Hin. apply nz_bytes. rewrite ZS. exact NZ. }
    assert (SLK : (- (bv_unsigned x8 + Z.of_nat (length (skipn (trim_lead s) bs)) + 1)) mod 8 <= Z.of_nat (length sl)).
    { unfold hide in SL8. rewrite length_skipn, H8.
      replace (bv_unsigned a0 + Z.of_nat (trim_lead s) + Z.of_nat (length bs - trim_lead s))
        with (bv_unsigned a0 + Z.of_nat (length bs)) by lia. exact SL8. }
    eapply evt_cut; [eapply SL; [exact BYL | exact NZL | exact SLK | exact MI] |].
    intros ms' PO. unfold strlen_post in PO.
    destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & M2 & -> & MUc & WMc & MIc & BYc).
    transport_after_call rsegs M1 M2 MUc WMc.
    clear MUc WMc BYc BYL MI. rename MIc into MI.
    try replace (ret_pc (Z_to_bv 64 0x15e0c)) with (Z_to_bv 64 0x15e0c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (LN : length (skipn (trim_lead s) bs) = length (s1_of s)) by (rewrite length_skipn, LB, S1L; reflexivity).
    rewrite LN. clear LN NZL SLK.
    (* 0x15e5c: *e = 0, epilogue. *)
    assert (FINAL : forall (y10 y11 y12 y13 y14 y15 : word), bv_unsigned y14 = trim_end_addr (bv_unsigned a0) s ->
      evt rsegs POST
        (MS (mkR (Z_to_bv 64 0x15e0c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 x8 x9 y10 y11 y12 y13
                 y14 y15 ua6 ua7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x15e5c) fc None M2 (seg_rom rsegs))).
    { intros y10 y11 y12 y13 y14 y15 G14.
      assert (Y14 : y14 = wa (trim_end_addr (bv_unsigned a0) s))
        by (unfold wa; rewrite <- G14; symmetry; apply Z_to_bv_lit_self).
      subst y14. clear G14.
      assert (HS : store_ok rsegs M2 (wa (trim_end_addr (bv_unsigned a0) s)) 1 = true).
      { unfold trim_end_addr.
        apply (wr_at_store_ok rsegs M2 (bv_unsigned a0) (Z.of_nat (length s) + 1)
                 (Z.of_nat (trim_lead s + length (r_trim s))) 1 WR); lia. }
      zstep.
      replace (le1 (Z_to_bv 64 0)) with [ZERO] by reflexivity.
      assert (ZF : forall k, zb (firstn k s) = firstn k bs) by (intros k; rewrite <- ZS; apply zb_firstn).
      assert (NEW : bytes_at rsegs (write_to_mem M2 (wa (trim_end_addr (bv_unsigned a0) s)) [ZERO]) (bv_unsigned a0)
                      (zb (firstn (trim_lead s + length (r_trim s)) s) ++ [ZERO])).
      { rewrite ZF. unfold trim_end_addr.
        pose proof (bytes_at_write_inside rsegs M2 (bv_unsigned a0) (bs ++ ZERO :: sl)
                      (Z.of_nat (trim_lead s + length (r_trim s))) [ZERO] BY) as NW.
        specialize (NW ltac:(lia) ltac:(rewrite Nat2Z.id, length_app; cbn [length]; lia)).
        rewrite Nat2Z.id in NW. rewrite upd_prefix in NW by lia.
        apply bytes_at_prefix in NW. exact NW. }
      store_done.
      zstep. zstep. zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      replace x8 with (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat (trim_lead s))) by (rewrite <- H8; apply Z_to_bv_lit_self).
      unfold POST. finish. }
    (* 0x15e58: e = a1 when e[-1] is not blank (or the string is empty). *)
    assert (FIN58 : forall (y10 y11 y12 y13 y14 y15 : word), bv_unsigned y11 = trim_end_addr (bv_unsigned a0) s ->
      evt rsegs POST
        (MS (mkR (Z_to_bv 64 0x15e0c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 x8 x9 y10 y11 y12 y13
                 y14 y15 ua6 ua7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x15e58) fc None M2 (seg_rom rsegs))).
    { intros y10 y11 y12 y13 y14 y15 G11. zstep. eapply FINAL. exact G11. }
    (* LOOP 0x15e30: e = s0 + j, the bytes at j and after blank up to s0 + |s1|. *)
    assert (LOOP2 : forall (j : nat) (y11 y14 y15 : word), (1 <= j <= length (s1_of s))%nat ->
      te s j = te s (length (s1_of s)) -> bv_unsigned y11 = bv_unsigned x8 + Z.of_nat j ->
      evt rsegs POST
        (MS (mkR (Z_to_bv 64 0x15e0c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 x8 x9 (Z_to_bv 64 1) y11
                 (Z_to_bv 64 32) (Z_to_bv 64 4294976000) y14 y15 ua6 ua7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x15e30) fc None M2 (seg_rom rsegs))).
    { induction j as [|j IH]; intros y11 y14 y15 Hj Hte G11; [lia|].
      pose proof (HR (trim_lead s + j)%nat) as Rc.
      pose proof (te_S s j) as TS. rewrite (s1_nth s j NZ) in TS.
      zstep. if_cases K0; zify_cond K0.
      { exfalso. lia. }
      assert (RD : ov_read_bytes rsegs M2 (Z_to_bv 64 (bv_unsigned y11 + -1)) 1 =
                   Some [Z_to_bv 8 (nth (trim_lead s + j) s 0)]).
      { apply (u8ro_read rsegs M2 (bv_unsigned a0) (bs ++ ZERO :: sl) (Z.of_nat (trim_lead s + j)) _ _ BY);
          [rewrite Nat2Z.id; apply HB; lia | lia | unfold wa; f_equal; lia]. }
      zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?u8 in K by exact Rc.
      - destruct (blank (nth (trim_lead s + j) s 0)) eqn:Bc; [apply blank_le32 in Bc; lia|].
        eapply FIN58. rewrite HE, <- Hte, TS. lia.
      - zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?u8 in K2 by exact Rc.
        + apply blank_mask0 in K2; [|lia]. rewrite K2 in TS.
          eapply FIN58. rewrite HE, <- Hte, TS. lia.
        + apply blank_mask1 in K2; [|lia]. rewrite K2 in TS.
          zstep. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
          * eapply IH; [lia | rewrite <- TS; exact Hte | rewrite unsigned_lit by lia; lia].
          * assert (Ej : j = 0%nat) by lia. subst j.
            zstep. eapply FINAL. rewrite unsigned_lit by lia. rewrite HE, <- Hte, TS, te_0. lia. }
    zstep. zstep. if_cases KT; zify_cond KT.
    { exfalso. rewrite H9 in KT. Z.div_mod_to_equations. lia. }
    zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - assert (N0 : length (s1_of s) = 0%nat) by lia.
      eapply FIN58. rewrite ?unsigned_lit by lia. rewrite HE, N0, te_0. lia.
    - zstep. zstep. zstep. zstep. zstep.
      eapply (LOOP2 (length (s1_of s))); [lia | reflexivity | rewrite ?unsigned_lit by lia; lia]. }
  (* LOOP 0x15de0: s0 = s + i, s1 = s0 + 1, the bytes before i blank. *)
  assert (LOOP1 : forall (k i : nat) (x8 x9 x12 x13 : word), (trim_lead s - i = k)%nat -> (i <= trim_lead s)%nat ->
    bv_unsigned x8 = bv_unsigned a0 + Z.of_nat i -> bv_unsigned x9 = (bv_unsigned x8 + 1) mod 2 ^ 64 ->
    bv_unsigned x12 = 2 ^ 64 - 1 ->
    evt rsegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 32) (Z_to_bv 64 4294976000)
               x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15de0) fc None M1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i x8 x9 x12 x13 Hk Hi H8 H9 H12.
    - assert (Ei : i = trim_lead s) by lia. subst i.
      pose proof (HR (trim_lead s)) as Rc. pose proof (lead_stop s NZ) as Bc.
      assert (RD : ov_read_bytes rsegs M1 x8 1 = Some [Z_to_bv 8 (nth (trim_lead s) s 0)]).
      { apply (u8ro_read rsegs M1 (bv_unsigned a0) (bs ++ ZERO :: sl) (Z.of_nat (trim_lead s)) _ x8 BY);
          [rewrite Nat2Z.id; apply HB; lia | lia | unfold wa; rewrite <- H8; symmetry; apply Z_to_bv_lit_self]. }
      zstep. zstep. if_cases K; zify_cond K; rewrite ?u8 in K by exact Rc.
      + eapply AFTER; [exact H8 | exact H9].
      + zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?u8 in K2 by exact Rc.
        * eapply AFTER; [exact H8 | exact H9].
        * exfalso. apply blank_mask1 in K2; [|pose proof (HR (trim_lead s)); lia]. congruence.
    - assert (Il : (i < trim_lead s)%nat) by lia.
      pose proof (HR i) as Rc. pose proof (lead_blank s i NZ Il) as Bc. pose proof (blank_le32 _ Bc) as Lc.
      assert (RD : ov_read_bytes rsegs M1 x8 1 = Some [Z_to_bv 8 (nth i s 0)]).
      { apply (u8ro_read rsegs M1 (bv_unsigned a0) (bs ++ ZERO :: sl) (Z.of_nat i) _ x8 BY);
          [rewrite Nat2Z.id; apply HB; lia | lia | unfold wa; rewrite <- H8; symmetry; apply Z_to_bv_lit_self]. }
      zstep. zstep. if_cases K; zify_cond K; rewrite ?u8 in K by exact Rc.
      + exfalso. lia.
      + zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?u8 in K2 by exact Rc.
        * exfalso. apply blank_mask0 in K2; [|lia]. congruence.
        * zstep. if_cases K3; zify_cond K3.
          { exfalso. lia. }
          zstep. zstep. zstep.
          eapply (IH (S i)); [lia | lia | rewrite unsigned_lit by lia; lia | rewrite !unsigned_lit_wrap, H9; reflexivity
                             | exact H12]. }
  eapply (LOOP1 (trim_lead s - 0)%nat 0%nat); [reflexivity | lia | lia | apply unsigned_lit_wrap
                                               | vm_compute; reflexivity].
Qed.
