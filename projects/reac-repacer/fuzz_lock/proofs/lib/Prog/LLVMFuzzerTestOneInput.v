(* Walk of fuzz_lock's LLVMFuzzerTestOneInput (fuzz_lock.c:181-207) in fuzz_lock.plain, 0x12b78, against
   LLVMFuzzerTestOneInput_sr_contract, in the form of libreac/fuzz_decode's lib/Prog/LLVMFuzzerTestOneInput.v (release
   25e3d17bdb50). check_no_overread and check_lookup are taken through their contracts (Section hypotheses CNO and
   CL, discharged in LLVMFuzzerTestOneInput_link.v). Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import check_no_overread_c check_lookup_c
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_early lt_segs lt_glue.
Import ListNotations.
Open Scope Z_scope.

Lemma lt_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x NO. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply NO; cbn [outside]; (split; [lia | exact I]).
Qed.

Lemma lt_callee_cases : forall x, callee_saved x ->
  x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ x = 9 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/
  x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27.
Proof. intros x Hx. unfold callee_saved in Hx. lia. Qed.

(* a name with no bad byte holds no NUL *)
Lemma lt_no_nul : forall P, existsb lock_bad P = false -> ~ In (Z_to_bv 8 0) P.
Proof.
  intros P H Hin. assert (E : existsb lock_bad P = true) by (apply existsb_exists; exists (Z_to_bv 8 0); split;
    [exact Hin | reflexivity]). congruence.
Qed.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis CNO : forall fx' : YK11.FPState, @check_no_overread_contract fx' rc B API.
Hypothesis CL : forall fx' : YK11.FPState, @check_lookup_contract fx' rc B API.

Theorem LLVMFuzzerTestOneInput_holds_of : LLVMFuzzerTestOneInput_sr_contract B API.
Proof.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hnl Hpd Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  pose proof (llvm_n_bound B API stk empty L A regs mem md ra p n Hpre) as Hnb.
  destruct (Z_lt_le_dec n 2) as [H2|H2]; [| destruct (Z_lt_le_dec n (2 ^ 26)) as [H26|H26]].
  1, 3: exact (llvm_early B API SINK j stk empty L A regs mem md ra p n pl b BI Hk Hra Hpre Hnl Hsn Hres Hro Hfrm
    ltac:(lia)).
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn1 & Hpl & Hrod).
  pose proof (lf_fr_init B API stk empty L A regs mem md ra p n Hpre Hro) as FR0.
  unfold LLVM_K, LLVM_FRAME, CL_STACK, CL_FRAME, ALLOC_STACK in Hk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  assert (Esp : spZ regs = bv_unsigned (reg_get regs 2)) by reflexivity.
  pose proof (bv_unsigned_in_range _ (reg_get regs 2)) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  destruct Hpl as [[Hn0 _] | [_ (q & Hq & Hqp)]]; [lia|].
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
  assert (HinP : In (p, n) (blocks L A)) by (apply blocks_In; exists q; split; [exact Hqp | exact Hq]).
  assert (E10 : reg_get regs 10 = Z_to_bv 64 p) by exact Hp.
  assert (E11 : reg_get regs 11 = Z_to_bv 64 (Z.of_nat (length pl))) by (rewrite <- Hnl; exact Hn1).
  assert (E1 : YK11.getr regs 1 = reg_get regs 1) by reflexivity.
  assert (ST0 : Frame.stk rsegs (normalize rsegs mem) (spZ regs - stk) (bv_unsigned (reg_get regs 2))).
  { rewrite <- Esp. apply lf_stk; [lia | lia |].
    intros a Ha. unfold writable_at.
    assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
    rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)
               (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
    rewrite <- SEGS. exact (Hstw a Ha). }
  assert (BL0 : bytes_at rsegs (normalize rsegs mem) p pl).
  { apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact Hpd]. }
  rewrite SEGS.
  eapply g_run with (B := B) (API := API) (stk := stk) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (L := L) (A := A).
  - exact SEGS.
  - exact AX.
  - exact HGG.
  - exact FR0.
  - lia.
  - lia.
  - unfold Regs6ss.mkR_of, LLVM_ENTRY. rewrite E10, E11.
    eapply lt_main with (lo := spZ regs - stk); [lia | lia | lia | lia | exact ST0 | exact BL0 | apply mem_inv_normalize].
  - intros ms [(t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & MU & WM)
              | (t0' & a4' & a5' & a6' & a7' & w & SL & m' & _ & _ & _ & _ & -> & MU & WM & _)];
      do 5 eexists; exists [(bv_unsigned (reg_get regs 2) - 64, bv_unsigned (reg_get regs 2))];
      (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]);
      intros x Hx NO; left; apply lt_out1 in NO; lia.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel FR1.
    destruct HQ as [(t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m'' & HE & MU & WM)
                   | (t0' & a4' & a5' & a6' & a7' & w & SL & m'' & LR0 & Hk1 & Hk2 & HSL & HE & MU & WM & STm & FRm
                      & PBm & BLm)].
    + (* returned: 0 for a short input, -1 for a bad name *)
      injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
      apply SR_ret.
      assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 (lock_ret pl)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (RP : regs_preserved regs regs').
      { intros r Hr. rewrite (lf_getr_eqv _ _ _ Hx).
        destruct (lt_callee_cases r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          reflexivity. }
      destruct (lf_post B API SINK stk empty L A regs mem md ra p n L A regs' m' md (lock_ret pl) Hpre Hsn FR1 G10 RP)
        as (Hpost & Hsn' & Hpay & MI2).
      exists (mkFP fp_regs fp_csr), L, A, regs', m', md.
      split; [rewrite <- E1, Hra1, (lf_ret_pc _ Hra); reflexivity|].
      split; [exact Hfrm|]. split; [exact Hpost|]. split; [exact Hsn'|].
      split; [exact Hres|]. split; [rewrite SEGS in Hpay; exact Hpay|]. split; [exact MI2 | exact I].
    + (* the two checks *)
      injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
      pose proof (lk_k_range pl) as Hkr. pose proof (lk_port_length pl Hk2) as HPl.
      pose proof (bv_unsigned_in_range _ w) as Rw. unfold bv_modulus in Rw. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rw.
      assert (G1 : YK11.getr regs' 1 = Z_to_bv 64 0x12c70) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G2 : YK11.getr regs' 2 = Z_to_bv 64 (spZ regs - 64)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G4 : YK11.getr regs' 4 = YK11.getr regs 4) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 (p + 2 + lk_k pl))
        by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G11 : YK11.getr regs' 11 = Z_to_bv 64 (Z.of_nat (length pl) - 2 - lk_k pl))
        by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G12 : YK11.getr regs' 12 = Z_to_bv 64 (spZ regs - 56)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G13 : YK11.getr regs' 13 = Z_to_bv 64 (bv_unsigned w))
        by (rewrite (lf_getr_eqv _ _ _ Hx); symmetry; apply Z_to_bv_bv_unsigned).
      assert (Hsp1 : spZ regs' = spZ regs - 64) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
      assert (FRr : rw_cells rsegs m' (spZ regs - 40)
                      [C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                       C8 (reg_get regs 1)]) by exact (lf_rw_cells_rel m' m'' _ _ Hrel FRm).
      assert (PBr : bytes_at rsegs m' (spZ regs - 56) (lk_port pl ++ Z_to_bv 8 0 :: SL))
        by exact (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel) PBm).
      assert (BLr : bytes_at rsegs m' p pl) by exact (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel) BLm).
      assert (BT : blk_data B m' (p + 2 + lk_k pl)
                     (firstn (Z.to_nat (Z.of_nat (length pl) - 2 - lk_k pl)) (skipn (Z.to_nat (2 + lk_k pl)) pl))).
      { apply (bytes_at_blk B _ _ _ SEGS).
        pose proof (lt_bytes_sub m' p pl (Z.to_nat (2 + lk_k pl)) (Z.to_nat (Z.of_nat (length pl) - 2 - lk_k pl)) BLr
          ltac:(lia)) as H.
        rewrite Z2Nat.id in H by lia. replace (p + 2 + lk_k pl) with (p + (2 + lk_k pl)) by ring. exact H. }
      assert (HTl : Z.of_nat (length (firstn (Z.to_nat (Z.of_nat (length pl) - 2 - lk_k pl))
                      (skipn (Z.to_nat (2 + lk_k pl)) pl))) = Z.of_nat (length pl) - 2 - lk_k pl)
        by (rewrite length_firstn, length_skipn; lia).
      assert (BP : blk_data B m' (spZ regs - 56) (lk_port pl ++ Z_to_bv 8 0 :: SL)) by exact (bytes_at_blk B _ _ _ SEGS PBr).
      assert (NB : existsb lock_bad (lk_port pl) = false).
      { destruct (existsb lock_bad (lk_port pl)) eqn:E; [|reflexivity].
        rewrite (lock_ret_bad pl ltac:(lia) Hk2 ltac:(lia) E) in LR0. discriminate. }
      assert (G3 : YK11.getr regs' 3 = YK11.getr regs 3) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G8 : YK11.getr regs' 8 = Z_to_bv 64 (lk_k pl)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G9 : YK11.getr regs' 9 = w) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G18 : YK11.getr regs' 18 = Z_to_bv 64 (p + 2 + lk_k pl))
        by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G19 : YK11.getr regs' 19 = Z_to_bv 64 (Z.of_nat (length pl) - 2 - lk_k pl))
        by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      (* the registers check_no_overread keeps: s4..s11 *)
      assert (GS : forall x, 20 <= x <= 27 -> YK11.getr regs' (Z_to_bv 5 x) = YK11.getr regs (Z_to_bv 5 x)).
      { intros x Hx'. rewrite (lf_getr_eqv _ _ _ Hx).
        assert (C : x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27) by lia.
        repeat (destruct C as [-> | C]; [reflexivity|]). subst. reflexivity. }
      set (T := firstn (Z.to_nat (Z.of_nat (length pl) - 2 - lk_k pl)) (skipn (Z.to_nat (2 + lk_k pl)) pl)) in *.
      rewrite <- SEGS.
      eapply g_cno with (B := B) (API := API) (stk := stk) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem)
        (md0 := md) (L := L) (A := A) (t := p + 2 + lk_k pl) (n := Z.of_nat (length pl) - 2 - lk_k pl)
        (pa := spZ regs - 56) (rate := bv_unsigned w) (T := T) (P := lk_port pl) (SL := SL) (bres := b).
      { exact SEGS. } { exact AX. } { exact ERRNO_LOW. } { exact CNO. } { exact FR1. } { lia. } { lia. }
      { rewrite G1. apply ret_ok_even. reflexivity. }
      { rewrite Hsp1. Z.div_mod_to_equations. lia. }
      { rewrite Hsp1. unfold CNO_STACK, CNO_FRAME, ALLOC_STACK. lia. }
      { lia. } { lia. }
      { rewrite G4. exact Htp. }
      { exact G10. } { exact G11. } { exact G12. } { exact G13. }
      { lia. } { exact HTl. } { lia. }
      { exists p, n. split; [exact HinP | lia]. }
      { exact BT. }
      { lia. } { Z.div_mod_to_equations. lia. } { lia. }
      { rewrite length_app. cbn [length]. lia. }
      { exact (lt_no_nul _ NB). }
      { exact BP. } { exact Rw. } { exact Hfrm. } { exact Hres. }
      { destruct Hroom as (Hl1 & Hl2 & Hl3). repeat split; lia. }
      (* back from check_no_overread at 0x12c70 *)
      intros fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 RP2 Eb2 Hres2 Habove2 Hkept2.
      rewrite G1, SEGS.
      assert (P2 : forall x, callee_saved x -> YK11.getr regs2 (Z_to_bv 5 x) = YK11.getr regs' (Z_to_bv 5 x))
        by exact RP2.
      assert (E22 : reg_get regs2 2 = Z_to_bv 64 (spZ regs - 64))
        by exact (eq_trans (P2 2 ltac:(unfold callee_saved; lia)) G2).
      assert (E28 : reg_get regs2 8 = Z_to_bv 64 (lk_k pl))
        by exact (eq_trans (P2 8 ltac:(unfold callee_saved; lia)) G8).
      assert (E29 : reg_get regs2 9 = w)
        by exact (eq_trans (P2 9 ltac:(unfold callee_saved; lia)) G9).
      assert (E218 : reg_get regs2 18 = Z_to_bv 64 (p + 2 + lk_k pl))
        by exact (eq_trans (P2 18 ltac:(unfold callee_saved; lia)) G18).
      assert (E219 : reg_get regs2 19 = Z_to_bv 64 (Z.of_nat (length pl) - 2 - lk_k pl))
        by exact (eq_trans (P2 19 ltac:(unfold callee_saved; lia)) G19).
      pose proof FR2 as (HM2 & _). destruct (mr_model B _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
      eapply (llvm_run fx2 regs2 (Z_to_bv 64 0x12c70) mem2 md2); [exact Hh2 | exact Hl2 | | |].
      { unfold Regs6ss.mkR_of. apply lt_mid. }
      { intros ms ->. do 5 eexists. reflexivity. }
      intros R F pc' fc m3 HE3 regs3 Hx3.
      injection HE3 as ER EF EP EC EM. subst R F pc' fc m3.
      assert (H31 : YK11.getr regs3 1 = Z_to_bv 64 0x12c88) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
      assert (H34 : YK11.getr regs3 4 = YK11.getr regs 4).
      { rewrite (lf_getr_eqv _ _ _ Hx3). exact (eq_trans (P2 4 ltac:(unfold callee_saved; lia)) G4). }
      assert (H310 : YK11.getr regs3 10 = Z_to_bv 64 (p + 2 + lk_k pl))
        by (rewrite (lf_getr_eqv _ _ _ Hx3); exact E218).
      assert (H311 : YK11.getr regs3 11 = Z_to_bv 64 (Z.of_nat (length pl) - 2 - lk_k pl))
        by (rewrite (lf_getr_eqv _ _ _ Hx3); exact E219).
      assert (H312 : YK11.getr regs3 12 = Z_to_bv 64 (spZ regs - 56)).
      { rewrite (lf_getr_eqv _ _ _ Hx3). transitivity (Z_to_bv 64 (bv_unsigned (reg_get regs2 2) + 8)); [reflexivity|].
        rewrite E22, MState.unsigned_lit by lia. f_equal. lia. }
      assert (H313 : YK11.getr regs3 13 = Z_to_bv 64 (lk_k pl)) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact E28).
      assert (H314 : YK11.getr regs3 14 = Z_to_bv 64 (bv_unsigned w)).
      { rewrite (lf_getr_eqv _ _ _ Hx3). transitivity (reg_get regs2 9); [reflexivity|]. rewrite E29. symmetry.
        apply Z_to_bv_bv_unsigned. }
      assert (H32 : YK11.getr regs3 2 = Z_to_bv 64 (spZ regs - 64)) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact E22).
      assert (Hsp3 : spZ regs3 = spZ regs - 64) by (unfold spZ at 1; rewrite H32; apply MState.unsigned_lit; lia).
      assert (BT2 : blk_data B mem2 (p + 2 + lk_k pl) T).
      { intros i Hi. rewrite <- (BT i Hi). rewrite HTl in Hi.
        replace (p + 2 + lk_k pl + i) with (p + (2 + lk_k pl + i)) by ring.
        exact (Hkept2 p n (2 + lk_k pl + i) HinP (fun H => H) ltac:(lia)). }
      assert (BP2 : blk_data B mem2 (spZ regs - 56) (lk_port pl ++ Z_to_bv 8 0 :: SL)).
      { intros i Hi. rewrite <- (BP i Hi). rewrite length_app in Hi. cbn [length] in Hi.
        exact (proj1 (Habove2 (spZ regs - 56 + i) ltac:(rewrite Hsp1; lia))). }
      rewrite <- SEGS.
      eapply g_cl with (B := B) (API := API) (stk := stk) (S := spZ regs) (L0 := L) (A0 := A) (mem0 := mem)
        (md0 := md) (L := L2) (A := A2) (t := p + 2 + lk_k pl) (n := Z.of_nat (length pl) - 2 - lk_k pl)
        (pa := spZ regs - 56) (k := lk_k pl) (rate := bv_unsigned w) (T := T) (P := lk_port pl) (SL := SL)
        (bres := b).
      { exact SEGS. } { exact AX. } { exact ERRNO_LOW. } { exact CL. } { exact FR2. } { lia. } { lia. }
      { rewrite H31. apply ret_ok_even. reflexivity. }
      { rewrite Hsp3. Z.div_mod_to_equations. lia. }
      { rewrite Hsp3. unfold CL_STACK, CL_FRAME, ALLOC_STACK. lia. }
      { lia. } { lia. }
      { rewrite H34. exact Htp. }
      { exact H310. } { exact H311. } { exact H312. } { exact H313. } { exact H314. }
      { lia. } { exact HTl. } { lia. }
      { exists p, n. rewrite Eb2. split; [exact HinP | lia]. }
      { exact BT2. }
      { lia. } { Z.div_mod_to_equations. lia. } { lia. }
      { rewrite length_app. cbn [length]. lia. }
      { exact (lt_no_nul _ NB). }
      { exact HPl. }
      { exact BP2. } { exact Rw. } { exact Hfrm2. } { exact Hres2. }
      { destruct Hroom as (Hl1' & Hl2' & Hl3'). repeat split; lia. }
      (* back from check_lookup at 0x12c88 *)
      intros fx3 L3 A3 regs4 mem3 md3 Hfrm3 FR3 RP3 Eb3 Hres3 Habove3 Hkept3.
      rewrite H31, SEGS.
      assert (P4 : forall x, callee_saved x -> YK11.getr regs4 (Z_to_bv 5 x) = YK11.getr regs3 (Z_to_bv 5 x))
        by exact RP3.
      assert (E42 : reg_get regs4 2 = Z_to_bv 64 (spZ regs - 64))
        by exact (eq_trans (P4 2 ltac:(unfold callee_saved; lia)) H32).
      assert (FR3' : rw_cells rsegs mem3 (spZ regs - 40)
                       [C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                        C8 (reg_get regs 1)]).
      { apply (lf_rw_cells_frame mem2); [apply (lf_rw_cells_frame m'); [exact FRr|] |].
        - intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite <- SEGS. apply Habove2. rewrite Hsp1. lia.
        - intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite <- SEGS. apply Habove3. rewrite Hsp3. lia. }
      pose proof FR3 as (HM3 & _). destruct (mr_model B _ (aa_laws API) _ _ _ _ HM3) as (Hh3 & Hl3 & _).
      eapply (llvm_run fx3 regs4 (Z_to_bv 64 0x12c88) mem3 md3); [exact Hh3 | exact Hl3 | | |].
      { unfold Regs6ss.mkR_of. apply lt_tail. rewrite E42, MState.unsigned_lit by lia.
        replace (spZ regs - 64 + 24) with (spZ regs - 40) by lia. exact FR3'. }
      { intros ms ->. do 5 eexists. reflexivity. }
      intros R F pc' fc m4 HE4 regs5 Hx5.
      injection HE4 as ER EF EP EC EM. subst R F pc' fc m4.
      apply SR_ret.
      assert (G510 : YK11.getr regs5 10 = Z_to_bv 64 (lock_ret pl))
        by (rewrite LR0, (lf_getr_eqv _ _ _ Hx5); reflexivity).
      assert (RP : regs_preserved regs regs5).
      { intros x Hx'. rewrite (lf_getr_eqv _ _ _ Hx5).
        assert (KEEP : forall y, (y = 3 \/ y = 4 \/ 20 <= y <= 27) ->
                  reg_get regs4 (Z_to_bv 5 y) = YK11.getr regs (Z_to_bv 5 y)).
        { intros y Hy. assert (Hc : callee_saved y) by (unfold callee_saved; lia).
          pose proof (P4 y Hc) as Q4. pose proof (lf_getr_eqv _ _ (Z_to_bv 5 y) Hx3) as Q3.
          pose proof (P2 y Hc) as Q2. pose proof (lf_getr_eqv _ _ (Z_to_bv 5 y) Hx) as Q1.
          assert (Hy' : y = 3 \/ y = 4 \/ y = 20 \/ y = 21 \/ y = 22 \/ y = 23 \/ y = 24 \/ y = 25 \/ y = 26 \/
                        y = 27) by lia.
          destruct Hy' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]];
            (etransitivity; [exact Q4|]); (etransitivity; [exact Q3|]); (etransitivity; [exact Q2|]);
            (etransitivity; [exact Q1|]); reflexivity. }
        destruct (lt_callee_cases x Hx') as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
        - change (Z_to_bv 64 (bv_unsigned (reg_get regs4 2) + 64) = YK11.getr regs (Z_to_bv 5 2)).
          rewrite E42, MState.unsigned_lit by lia. apply lt_sp_back. change (spZ regs - 64 + 64 = spZ regs). lia.
        - exact (KEEP 3 ltac:(lia)).
        - exact (KEEP 4 ltac:(lia)).
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - exact (KEEP 20 ltac:(lia)).
        - exact (KEEP 21 ltac:(lia)).
        - exact (KEEP 22 ltac:(lia)).
        - exact (KEEP 23 ltac:(lia)).
        - exact (KEEP 24 ltac:(lia)).
        - exact (KEEP 25 ltac:(lia)).
        - exact (KEEP 26 ltac:(lia)).
        - exact (KEEP 27 ltac:(lia)). }
      destruct (lf_post B API SINK stk empty L A regs mem md ra p n L3 A3 regs5 mem3 md3 (lock_ret pl) Hpre Hsn FR3
        G510 RP) as (Hpost & Hsn' & Hpay & MI2).
      exists (mkFP fp_regs fp_csr), L3, A3, regs5, mem3, md3.
      split; [rewrite <- E1, Hra1, (lf_ret_pc _ Hra); reflexivity|].
      split; [exact Hfrm3|]. split; [exact Hpost|]. split; [exact Hsn'|].
      split; [exact Hres3|]. split; [rewrite SEGS in Hpay; exact Hpay|]. split; [exact MI2 | exact I].
Qed.

End M.
