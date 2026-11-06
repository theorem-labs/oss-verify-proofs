From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Tac Bytes ZBridge Step Arr Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel SlotNeeds_c LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SegSetModel.
Import ListNotations.
Open Scope Z_scope.

Lemma header_0 : forall pl, length pl = 0%nat -> header pl = mkhdr 0 0 0 0.
Proof. intros pl H. unfold header, rd16. rewrite !rd8_ge by lia. reflexivity. Qed.

Lemma header_1 : forall pl, length pl = 1%nat -> header pl = mkhdr (pbz pl 0) 0 0 1.
Proof.
  intros pl H. unfold header, rd16. rewrite rd8_lt by lia. cbv beta iota zeta.
  rewrite !rd8_ge by lia. cbv beta iota zeta. f_equal. lia.
Qed.

Lemma header_2 : forall pl, length pl = 2%nat -> header pl = mkhdr (pbz pl 0 + 256 * pbz pl 1) 0 0 2.
Proof.
  intros pl H. unfold header, rd16. rewrite rd8_lt by lia. cbv beta iota zeta.
  rewrite rd8_lt by lia. cbv beta iota zeta. rewrite !rd8_ge by lia. reflexivity.
Qed.

Lemma header_3 : forall pl, length pl = 3%nat -> header pl = mkhdr (pbz pl 0 + 256 * pbz pl 1) (pbz pl 2) 0 3.
Proof.
  intros pl H. unfold header, rd16. rewrite rd8_lt by lia. cbv beta iota zeta.
  rewrite rd8_lt by lia. cbv beta iota zeta. rewrite rd8_lt by lia. cbv beta iota zeta.
  rewrite rd8_ge by lia. reflexivity.
Qed.

Lemma header_4 : forall pl, (4 <= length pl)%nat ->
  header pl = mkhdr (pbz pl 0 + 256 * pbz pl 1) (pbz pl 2) (pbz pl 3) 4.
Proof.
  intros pl H. unfold header, rd16. rewrite rd8_lt by lia. cbv beta iota zeta.
  rewrite rd8_lt by lia. cbv beta iota zeta. rewrite rd8_lt by lia. cbv beta iota zeta.
  rewrite rd8_lt by lia. reflexivity.
Qed.

Lemma pbz_range : forall pl k, 0 <= pbz pl k < 256.
Proof.
  intros pl k. unfold pbz. pose proof (bv_unsigned_in_range 8 (nth k pl (Z_to_bv 8 0))) as R.
  replace (bv_modulus 8) with 256 in R by reflexivity. lia.
Qed.

Lemma pl_read : forall m p pl k, bytes_at rsegs m p pl -> (k < length pl)%nat ->
  ov_read_bytes rsegs m (wa (p + Z.of_nat k)) 1 = Some [nth k pl (Z_to_bv 8 0)].
Proof.
  intros m p pl k HB Hk. rewrite (bytes_at_read rsegs m p pl (Z.of_nat k) 1 HB) by lia.
  rewrite Nat2Z.id. rewrite (firstn1_skipn_nth pl k (Z_to_bv 8 0)) by lia. reflexivity.
Qed.

Lemma sext16_small : forall u, 0 <= u < 32768 -> sext16 u = u.
Proof. intros u Hu. unfold sext16. rewrite (proj2 (Z.ltb_lt u 32768)) by lia. reflexivity. Qed.

Lemma lor16 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.lor (b1 ≪ 8 mod 18446744073709551616) b0 = b0 + 256 * b1.
Proof.
  intros b0 b1 H0 H1. rewrite (Z.mod_small (b1 ≪ 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm. apply lor_shiftl8_add; lia.
Qed.

Lemma sext16_mach : forall u, 0 <= u < 65536 ->
  Z_to_bv 64 (bv_signed (Z_to_bv 64 (u ≪ 48)) ≫ 48) = Z_to_bv 64 (sext16 u).
Proof.
  intros u Hu. f_equal. rewrite Z.shiftl_mul_pow2 by lia. rewrite zb_signed.
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. unfold sext16.
  destruct (Z.ltb_spec u 32768) as [Hs|Hs].
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply Z.div_mul. lia.
  - rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    replace (u * 2 ^ 48 - 2 ^ 64) with ((u - 65536) * 2 ^ 48) by lia. apply Z.div_mul. lia.
Qed.

Theorem seg_head_holds : seg_head.
Proof.
  unfold seg_head. intros x ms H.
  apply evt_canon; [eqv_inv_tac|].
  destruct H as ((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & HPL & HST & HMI & Hp0 & Hpn & Hpd & HRW & HRS & HRP) &
                 HS16 & Hsv12 & HS63 & Hsp & Hra & Hsr & Ha0 & Ha1 & _ & _ & _).
  remember (x_sv x) as sv eqn:Esv.
  destruct sv as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 [|v8 [|v9 [|v10 [|v11 [|v12 l]]]]]]]]]]]]];
    cbn in Hsv12; try discriminate.
  unfold sregs, SREGS in Hsr. cbn [map] in Hsr.
  injection Hsr as R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27.
  assert (Hsv : length (x_sv x) = 12%nat) by (rewrite <- Esv; reflexivity).
  rewrite canon_rg by exact Hsvc.
  rewrite Hpc, HF, Hfc, Hrv, Hro, Hsp, Hra, Ha0, Ha1, Hgp, Htp,
    R8, R9, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27.
  assert (ELS : LLVM_STACK = 8784) by reflexivity.
  assert (Exn : x_n x = Z.of_nat (length (x_pl x))) by reflexivity.
  assert (ESPL : SPL x = x_S x - 592) by reflexivity.
  set (mI := ms_mem ms) in *.
  assert (MU : munch [(x_S x - 8784, x_S x)] mI mI) by apply munch_refl.
  assert (WM : wmono rsegs mI mI) by apply wmono_refl.
  destruct (CB_bytes _ _ _ _ HPL) as (HPB & _ & _).
  assert (Slo : 0 <= x_S x - 8784) by (destruct HST as [Hz _]; lia).
  unfold w64, PC_ENTRY.
  zstep.
  remember (x_S x + -592) as SP eqn:ESP.
  rewrite ELS in HST.
  pose proof HRS as HRS8. rewrite ELS in HRS8.
  assert (HLB : length CTRL_HEADAMP_BYTES = 24%nat) by reflexivity.
  destruct (stk_split rsegs mI (x_S x - 8784) (SP + 488) (x_S x) HST ltac:(lia)) as [ST STU].
  destruct (stk_carve rsegs mI (SP + 488) (x_S x) 104 STU ltac:(lia)) as [_ [junk FR]]. clear STU.
  replace (x_S x - Z.of_nat 104) with (SP + 488) in FR by lia.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  match goal with H : rw_cells rsegs ?mf (SP + 488) _ |- _ =>
    assert (HSTK : stk rsegs mf (x_S x - LLVM_STACK) (x_S x))
      by (rewrite ELS; replace (x_S x) with (SP + 488 + Z.of_nat (cells_size
            [C8 v11; C8 v10; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 (x_ra x)]))
            at 2 by (cbn; lia); apply (stk_release rsegs mf _ _ _ ST H); lia);
    assert (HFR : rw_cells rsegs mf (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x])))
      by (rewrite <- Esv; cbn [rev app map]; replace (x_S x - 104) with (SP + 488) by lia; exact H)
  end.
  subst SP.
  zstep. zstep.
  if_cases HC1; zify_cond HC1; rewrite ?Z.shiftr_div_pow2 in HC1 by lia; change (2 ^ 26) with 67108864 in HC1.
  - assert (Hbig : 67108864 <= x_n x) by (Z.div_mod_to_equations; lia).
    apply evt_done. split; [unfold kept; cbn [ms_mem]; rewrite ELS; split; assumption|].
    left. split; [exact Hbig|].
    unfold At_ret0, body. rewrite ESPL. fin_at.
  - assert (Hsm : x_n x < 67108864) by (Z.div_mod_to_equations; lia).
    zstep. zstep.
    if_cases HC2; zify_cond HC2.
    + assert (Hn0 : length (x_pl x) = 0%nat) by lia.
      zstep. zstep. zstep. zstep. zstep. zstep.
      apply evt_done; split; [unfold kept; cbn [ms_mem]; rewrite ELS; split; assumption|];
        right; split; [exact Hsm|].
      unfold At_mallocT, hd. rewrite (header_0 (x_pl x) Hn0). unfold h_base; cbn [h_pos h_u16 h_in h_rows].
      rewrite sext16_small by lia. unfold body. rewrite ESPL. fin_at.
    + assert (HR0 := pl_read _ _ _ 0 HPB ltac:(lia)). rewrite Nat2Z.inj_0, Z.add_0_r in HR0.
      pose proof (pbz_range (x_pl x) 0) as B0. unfold pbz in B0.
      zstep. zstep. zstep.
      if_cases HC3; zify_cond HC3.
      * assert (HR1 := pl_read _ _ _ 1 HPB ltac:(lia)).
        pose proof (pbz_range (x_pl x) 1) as B1. unfold pbz in B1.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        rewrite lor16 by lia. rewrite sext16_mach by lia.
        if_cases HC4; zify_cond HC4.
        -- assert (HR2 := pl_read _ _ _ 2 HPB ltac:(lia)).
           pose proof (pbz_range (x_pl x) 2) as B2. unfold pbz in B2.
           zstep. zstep. zstep.
           if_cases HC5; zify_cond HC5.
           ++ assert (Hn4 : (4 <= length (x_pl x))%nat) by lia.
              assert (HR3 := pl_read _ _ _ 3 HPB ltac:(lia)).
              zstep. zstep. zstep. zstep. zstep.
              apply evt_done; split; [unfold kept; cbn [ms_mem]; rewrite ELS; split; assumption|];
        right; split; [exact Hsm|].
              unfold At_mallocT, hd. rewrite (header_4 (x_pl x) Hn4). unfold h_base; cbn [h_pos h_u16 h_in h_rows].
              unfold pbz. unfold body. rewrite ESPL. fin_at.
           ++ assert (Hn3 : length (x_pl x) = 3%nat) by lia.
              zstep. zstep. zstep. zstep. zstep.
              apply evt_done; split; [unfold kept; cbn [ms_mem]; rewrite ELS; split; assumption|];
        right; split; [exact Hsm|].
              unfold At_mallocT, hd. rewrite (header_3 (x_pl x) Hn3). unfold h_base; cbn [h_pos h_u16 h_in h_rows].
              unfold pbz. unfold body. rewrite ESPL. fin_at.
        -- assert (Hn2 : length (x_pl x) = 2%nat) by lia.
           zstep. zstep. zstep. zstep. zstep. zstep.
           apply evt_done; split; [unfold kept; cbn [ms_mem]; rewrite ELS; split; assumption|];
        right; split; [exact Hsm|].
           unfold At_mallocT, hd. rewrite (header_2 (x_pl x) Hn2). unfold h_base; cbn [h_pos h_u16 h_in h_rows].
           unfold pbz. unfold body. rewrite ESPL. fin_at.
      * assert (Hn1 : length (x_pl x) = 1%nat) by lia.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        apply evt_done; split; [unfold kept; cbn [ms_mem]; rewrite ELS; split; assumption|];
        right; split; [exact Hsm|].
        unfold At_mallocT, hd. rewrite (header_1 (x_pl x) Hn1). unfold h_base; cbn [h_pos h_u16 h_in h_rows].
        unfold pbz. rewrite sext16_small by lia. unfold body. rewrite ESPL. fin_at.
Qed.
