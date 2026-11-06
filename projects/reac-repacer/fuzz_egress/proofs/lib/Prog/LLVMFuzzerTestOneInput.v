(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput.v
   at bc49657c087a and libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Prog/fd_entry.v and fd_exit.v at
   25e3d17bdb50; module path, this harness's body and its callees. *)
(* The plain-image walk of the harness body LLVMFuzzerTestOneInput (fuzz_egress.c:143-170), 0x12c60, 436 bytes,
   against LLVMFuzzerTestOneInput_c.v's LLVMFuzzerTestOneInput_sr_contract. size >= 64 MiB returns at once
   (LLVMFuzzerTestOneInput_early.v); otherwise the body is split at each SR call:
     lt_head.eA_evt   entry .. malloc(n ? n : 1)            (the frame, memset, memcpy of the head, the v loop)
     g_malloc         f = malloc(...)                       (fuzz_dup; the allocator contract never returns NULL)
     lt_segs.eB_evt   .. check_restamp                      (fuzz_dup's memcpy(f, data + 53, n) when size >= 54)
     g_cr             check_restamp(f, n, ctr)
     llvm_run         .. check_mute
     g_cm             check_mute(f, n)
     lt_segs.eD_evt   check_gate(f, n, slot) (evt) .. check_inject
     g_ci             check_inject(f, n, slot, v)
     llvm_run         .. free
     g_free           free(f)
     llvm_run         return 0 (the frame's saved registers back).
   The callee contracts are the Section hypotheses; LLVMFuzzerTestOneInput_link.v discharges them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import memset_c memcpy_c check_gate_c
  check_restamp_c check_mute_c check_inject_c FuzzDup LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_early lt_glue lt_head lt_segs.
Import ListNotations.
Open Scope Z_scope.

Lemma disj_mid : forall b1 x b2 y, pairwise ranges_disjoint (b1 ++ x :: b2) -> In y (b1 ++ b2) ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros b1 x b2 y HP Hin. destruct (pairwise_app_mid _ b1 x b2 y HP Hin) as [H|H];
    unfold ranges_disjoint in H; lia.
Qed.

Lemma bytes_at_sub : forall segs m a bs k len, bytes_at segs m a bs -> (k + len <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn len (skipn k bs)).
Proof.
  intros segs m a bs k len H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn len (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma bytes_of_rwc : forall segs m a n bs, rw_cells segs m a [CB n bs] -> bytes_at segs m a bs /\ length bs = n.
Proof.
  intros segs m a n bs [[[Hc _] Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  split; [exact Hb | exact Hc].
Qed.

(* the frame's saved registers, as eA_evt stores them at sp + 112 *)
Definition llvm_sv (r : bvmap 5 word) : list cell :=
  [C8 (reg_get r 24); C8 (reg_get r 23); C8 (reg_get r 22); C8 (reg_get r 21); C8 (reg_get r 20);
   C8 (reg_get r 19); C8 (reg_get r 18); C8 (reg_get r 9); C8 (reg_get r 8); C8 (reg_get r 1)].

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis MSET : memset_contract.
Hypothesis MC : memcpy_contract.
Hypothesis CG : check_gate_contract.
Hypothesis CR : forall fx' : YK11.FPState, @check_restamp_contract fx' rc B API.
Hypothesis CM : forall fx' : YK11.FPState, @check_mute_contract fx' rc B API.
Hypothesis CI : forall fx' : YK11.FPState, @check_inject_contract fx' rc B API.

Theorem LLVMFuzzerTestOneInput_holds_of : LLVMFuzzerTestOneInput_sr_contract B API.
Proof using MALLOC FREE ERRNO_LOW SINK MSET MC CG CR CM CI.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hn Hpl Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn11 & Hpl0 & Hrod).
  pose proof YM05.alloc_ceiling_value as Hac.
  assert (Hnb : 0 <= n < 2 ^ 47).
  { destruct Hpl0 as [[-> _] | [Hn0 (q & Hq & _)]]; [lia|].
    destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia. }
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig].
  2:{ apply (llvm_early B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
      rewrite Hn11. rewrite MState.unsigned_lit by lia. exact Hbig. }
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof Hk as Hk'. unfold LLVM_K, LLVM_FRAME, CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK in Hk'.
  pose proof lf_ceiling as Hrt. unfold LF_RES_TOP in Hrt.
  pose proof (lf_fr_init B API stk empty L A regs mem md ra p n Hpre Hro) as FR0.
  assert (Esp : spZ regs = bv_unsigned (reg_get regs 2)) by reflexivity.
  set (S := spZ regs) in *.
  set (p' := bv_unsigned (reg_get regs 10)).
  assert (HP01 : 0 <= p' < 2 ^ 64).
  { unfold p'. pose proof (bv_unsigned_in_range _ (reg_get regs 10)) as R. unfold bv_modulus in R.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in R. exact R. }
  assert (E10 : reg_get regs 10 = Z_to_bv 64 p') by (unfold p'; symmetry; apply Z_to_bv_bv_unsigned).
  assert (E11 : reg_get regs 11 = Z_to_bv 64 n) by exact Hn11.
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (S - 192 + 192)).
  { replace (S - 192 + 192) with S by lia. rewrite Esp. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (PAY : 0 < n -> In (p, n) (blocks L A) /\ 4096 <= p /\ p + n <= YM05.alloc_ceiling).
  { intros Hn0. destruct Hpl0 as [[-> _] | [_ (q & Hq & Hqp)]]; [lia|].
    pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
    split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia. }
  assert (Hpp : 0 < n -> p' = p).
  { intros Hn0. destruct (PAY Hn0) as (_ & R1 & R2). unfold p'.
    assert (E : reg_get regs 10 = Z_to_bv 64 p) by exact Hp. rewrite E. apply MState.unsigned_lit. lia. }
  assert (HS16 : S mod 16 = 0) by exact Hal.
  (* ---- entry .. malloc ---- *)
  rewrite SEGS.
  eapply (g_run B API SEGS AX HGG) with (stk := stk) (S := S) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (Q := qA (@fp_regs fx) (@fp_csr fx) (reg_get regs 3) (reg_get regs 4) (reg_get regs 19) (reg_get regs 25)
            (reg_get regs 26) (reg_get regs 27) (normalize rsegs mem) (S - 192) n p' (llvm_sv regs));
    [exact FR0 | lia | lia | | | ].
  { unfold Regs6ss.mkR_of. rewrite E10, E11, E2. unfold LLVM_ENTRY.
    apply (eA_evt MSET MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S - stk) (S - 192) p' n pl).
    - replace (S - 192 + 192) with S by lia.
      apply (norm_stk B SEGS mem (S - stk) S Hro); [unfold LF_RES_TOP; lia | lia | exact Hstw].
    - lia.
    - lia.
    - apply mem_inv_normalize.
    - lia.
    - exact HP01.
    - exact Hn.
    - intros Hn0. rewrite (Hpp Hn0). destruct (PAY Hn0) as (_ & R1 & R2).
      apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact Hpl].
    - intros Hn0. rewrite (Hpp Hn0). destruct (PAY Hn0) as (_ & R1 & R2). lia. }
  { intros ms HQ. destruct HQ as (R & m' & b0 & nn & -> & HQ).
    repeat match type of HQ with _ /\ _ => let H := fresh "QQ" in destruct HQ as [H HQ] end.
    exists R, (@fp_regs fx), (Z_to_bv 64 0x14010), (@fp_csr fx), m', [(S - 192, S - 192 + 192)].
    split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    intros x Hx NO. apply en_out1 in NO. left. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & m'' & b0 & nn & HE & Q1 & Q2 & Q3 & Q4 & Q8 & Q9 & Q10 & Q18 & Q19 & Q20 & Q25 & Q26 & Q27
    & Hnn & MU & WM & RW).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  assert (E1_1 : reg_get regs1 1 = Z_to_bv 64 0x12d58) by exact (xget _ _ _ _ Hx Q1 eq_refl).
  assert (E1_2 : reg_get regs1 2 = Z_to_bv 64 (S - 192)) by exact (xget _ _ _ _ Hx Q2 eq_refl).
  assert (E1_3 : reg_get regs1 3 = reg_get regs 3) by exact (xget _ _ _ _ Hx Q3 eq_refl).
  assert (E1_4 : reg_get regs1 4 = reg_get regs 4) by exact (xget _ _ _ _ Hx Q4 eq_refl).
  assert (E1_8 : reg_get regs1 8 = Z_to_bv 64 p') by exact (xget _ _ _ _ Hx Q8 eq_refl).
  assert (E1_9 : reg_get regs1 9 = Z_to_bv 64 n) by exact (xget _ _ _ _ Hx Q9 eq_refl).
  assert (E1_10 : reg_get regs1 10 = Z_to_bv 64 (fuzz_dup_size nn)) by exact (xget _ _ _ _ Hx Q10 eq_refl).
  assert (E1_18 : reg_get regs1 18 = Z_to_bv 64 nn) by exact (xget _ _ _ _ Hx Q18 eq_refl).
  assert (E1_19 : reg_get regs1 19 = reg_get regs 19) by exact (xget _ _ _ _ Hx Q19 eq_refl).
  assert (E1_20 : reg_get regs1 20 = Z_to_bv 64 (bv_unsigned b0)) by exact (xget _ _ _ _ Hx Q20 eq_refl).
  assert (E1_25 : reg_get regs1 25 = reg_get regs 25) by exact (xget _ _ _ _ Hx Q25 eq_refl).
  assert (E1_26 : reg_get regs1 26 = reg_get regs 26) by exact (xget _ _ _ _ Hx Q26 eq_refl).
  assert (E1_27 : reg_get regs1 27 = reg_get regs 27) by exact (xget _ _ _ _ Hx Q27 eq_refl).
  clear Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q18 Q19 Q20 Q25 Q26 Q27.
  assert (Hsp1 : spZ regs1 = S - 192).
  { assert (E : spZ regs1 = bv_unsigned (reg_get regs1 2)) by reflexivity. rewrite E, E1_2. apply unsigned_lit. lia. }
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel RW) as RW1. clear RW MU WM.
  clear Hx Hrel m0' R.
  assert (Hnn' : 0 <= nn <= 1600) by lia.
  pose proof (fuzz_dup_size_range nn ltac:(lia)) as (Hk1 & Hk2).
  set (k := fuzz_dup_size nn) in *.
  assert (Hnk : nn <= k) by (unfold k, fuzz_dup_size; destruct (Z.eqb_spec nn 0); lia).
  assert (Hkn : 0 < nn -> k = nn) by (intros Hn0; unfold k, fuzz_dup_size; destruct (Z.eqb_spec nn 0); lia).
  (* ---- f = malloc (n ? n : 1) ---- *)
  rewrite <- SEGS. change (Z_to_bv 64 0x14010) with (Z_to_bv 64 LLVM_MALLOC).
  eapply (g_malloc B API SEGS AX ERRNO_LOW HMAL MALLOC stk S L A mem md _ regs1 m1 md L A k b).
  { exact FR1. }
  { lia. }
  { lia. }
  { change (YK11.getr regs1 1) with (reg_get regs1 1). rewrite E1_1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp1. replace (S - 192) with (S + (-12) * 16) by lia. rewrite Z.mod_add by lia. exact HS16. }
  { rewrite Hsp1. unfold ALLOC_STACK. lia. }
  { rewrite Hsp1. lia. }
  { rewrite Hsp1. lia. }
  { change (YK11.getr regs1 4) with (reg_get regs1 4). rewrite E1_4. exact Htp. }
  { change (YK11.getr regs1 10) with (reg_get regs1 10). exact E1_10. }
  { exact Hres. }
  { destruct Hroom as (Hl1 & Hl2 & Hl3). apply fuzz_dup_room; unfold CAPMAX in *; lia. }
  intros L1 A1 regs2 mem2 md2 res FR2 Hrp2 G210 Hr1 Hr2 Hr16 Hnimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2.
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & _ & _ & _ & _ & _ & Hstw2 & _ & _ & Hro2).
  assert (Hres_in : In (res, k) (blocks L1 A1)) by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
  assert (PW : pairwise ranges_disjoint (b1 ++ (res, k) :: b2)).
  { rewrite <- Eb1. exact (mr_blocks_disjoint B _ (aa_laws API) L1 A1 mem2 md2 HM2). }
  assert (MINE : forall a jj, In (a, jj) (blocks L A) -> a + jj <= res \/ res + k <= a).
  { intros a jj Haj. rewrite Eb2 in Haj. pose proof (disj_mid b1 (res, k) b2 (a, jj) PW Haj) as H.
    cbn [fst snd] in H. lia. }
  assert (E2_ : forall x, callee_saved x -> reg_get regs2 (Z_to_bv 5 x) = reg_get regs1 (Z_to_bv 5 x))
    by (intros x Hx2; exact (rp_get regs1 regs2 x Hrp2 Hx2)).
  assert (E2_2 : reg_get regs2 2 = Z_to_bv 64 (S - 192))
    by exact (eq_trans (E2_ 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_3 : reg_get regs2 3 = reg_get regs 3)
    by exact (eq_trans (E2_ 3 ltac:(unfold callee_saved; lia)) E1_3).
  assert (E2_4 : reg_get regs2 4 = reg_get regs 4)
    by exact (eq_trans (E2_ 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (E2_8 : reg_get regs2 8 = Z_to_bv 64 p')
    by exact (eq_trans (E2_ 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (E2_9 : reg_get regs2 9 = Z_to_bv 64 n)
    by exact (eq_trans (E2_ 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (E2_18 : reg_get regs2 18 = Z_to_bv 64 nn)
    by exact (eq_trans (E2_ 18 ltac:(unfold callee_saved; lia)) E1_18).
  assert (E2_20 : reg_get regs2 20 = Z_to_bv 64 (bv_unsigned b0))
    by exact (eq_trans (E2_ 20 ltac:(unfold callee_saved; lia)) E1_20).
  assert (E2_25 : reg_get regs2 25 = reg_get regs 25)
    by exact (eq_trans (E2_ 25 ltac:(unfold callee_saved; lia)) E1_25).
  assert (E2_26 : reg_get regs2 26 = reg_get regs 26)
    by exact (eq_trans (E2_ 26 ltac:(unfold callee_saved; lia)) E1_26).
  assert (E2_27 : reg_get regs2 27 = reg_get regs 27)
    by exact (eq_trans (E2_ 27 ltac:(unfold callee_saved; lia)) E1_27).
  assert (RW2 : rw_cells rsegs mem2 (S - 192 + 112) (llvm_sv regs)).
  { apply (lf_rw_cells_frame m1 mem2 _ _ RW1). intros a Ha. rewrite <- SEGS. apply Habove2. rewrite Hsp1.
    cbn in Ha. lia. }
  clear RW1.
  assert (NI : forall a, LF_RES_TOP <= a -> ~ in_img B a)
    by (intros a Ha Hi; pose proof (lf_in_img_top B a SEGS Hi) as H; lia).
  (* the block f, in the memory the evt segments read *)
  destruct (norm_blk B API SEGS AX L1 A1 mem2 md2 res k HM2 Hres_in ltac:(lia) Hro2) as [jk HJK].
  destruct (rwc_cut rsegs _ res _ jk (Z.to_nat nn) HJK ltac:(lia)) as [HJN _].
  (* ---- .. check_restamp ---- *)
  change (YK11.getr regs1 1) with (reg_get regs1 1). rewrite E1_1. rewrite SEGS.
  eapply (g_run B API SEGS AX HGG) with (stk := stk) (S := S) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (Q := qB (@fp_regs fx) (@fp_csr fx) (reg_get regs 3) (reg_get regs 4) (reg_get regs 25) (reg_get regs 26)
            (reg_get regs 27) (normalize rsegs mem2) (S - 192) res nn (bv_unsigned b0 + -2) (llvm_sv regs));
    [exact FR2 | lia | lia | | | ].
  { unfold Regs6ss.mkR_of. rewrite E2_2, E2_3, E2_4, E2_8, E2_9, E2_18, E2_20, E2_25, E2_26, E2_27.
    change (reg_get regs2 10) with (YK11.getr regs2 10). rewrite G210.
    apply (eB_evt MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (llvm_sv regs) _ _ _ (S - 192) n p' res nn b0
      (firstn (Z.to_nat nn) (skipn 53 pl)) (firstn (Z.to_nat nn) jk)).
    - lia.
    - lia.
    - lia.
    - exact HP01.
    - exact Hr1.
    - lia.
    - exact Hnn.
    - intros H54. rewrite (Hpp ltac:(lia)). destruct (PAY ltac:(lia)) as (_ & R1 & R2). lia.
    - intros H54. rewrite (Hpp ltac:(lia)). destruct (PAY ltac:(lia)) as (Hin0 & R1 & R2).
      assert (BD : blk_data B mem2 p pl) by (eapply blk_keep; [exact FR2 | rewrite <- Hn; exact Hin0 | exact Hpl]).
      assert (BA : bytes_at rsegs (normalize rsegs mem2) p pl).
      { apply bytes_at_normalize; [exact Hro2|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact BD]. }
      pose proof (bytes_at_sub rsegs _ p pl 53 (Z.to_nat nn) BA ltac:(lia)) as BS. exact BS.
    - rewrite length_firstn, length_skipn. lia.
    - intros H54. exact HJN.
    - intros H54. rewrite (Hpp ltac:(lia)). destruct (PAY ltac:(lia)) as (Hin0 & R1 & R2).
      pose proof (MINE p n Hin0) as D. lia.
    - apply (lf_rw_cells_norm B mem2 _ _ SEGS Hro2); [|exact RW2].
      intros i Hi. apply NI. unfold LF_RES_TOP. cbn in Hi. lia.
    - reflexivity.
    - apply mem_inv_normalize. }
  { intros ms HQ. destruct HQ as (R & m' & cw & -> & HQ).
    repeat match type of HQ with _ /\ _ => let H := fresh "QQ" in destruct HQ as [H HQ] end.
    exists R, (@fp_regs fx), (Z_to_bv 64 0x12e14), (@fp_csr fx), m', [(res, res + nn)].
    split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    intros x Hx0 NO. apply en_out1 in NO. right. exists res, k. split; [|lia].
    unfold lf_mine. split; [exact Hres_in|]. split; [lia|]. exact MINE. }
  intros R F pc' fc m0' HQ regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ as (R' & m'' & cw & HE & Q1 & Q2 & Q3 & Q4 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q25 & Q26 & Q27
    & MU & WM & RW).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  assert (E3_1 : reg_get regs3 1 = Z_to_bv 64 0x12da4) by exact (xget _ _ _ _ Hx3 Q1 eq_refl).
  assert (E3_2 : reg_get regs3 2 = Z_to_bv 64 (S - 192)) by exact (xget _ _ _ _ Hx3 Q2 eq_refl).
  assert (E3_3 : reg_get regs3 3 = reg_get regs 3) by exact (xget _ _ _ _ Hx3 Q3 eq_refl).
  assert (E3_4 : reg_get regs3 4 = reg_get regs 4) by exact (xget _ _ _ _ Hx3 Q4 eq_refl).
  assert (E3_10 : reg_get regs3 10 = Z_to_bv 64 res) by exact (xget _ _ _ _ Hx3 Q10 eq_refl).
  assert (E3_11 : reg_get regs3 11 = Z_to_bv 64 nn) by exact (xget _ _ _ _ Hx3 Q11 eq_refl).
  assert (E3_12 : reg_get regs3 12 = cw) by exact (xget _ _ _ _ Hx3 Q12 eq_refl).
  assert (E3_18 : reg_get regs3 18 = Z_to_bv 64 nn) by exact (xget _ _ _ _ Hx3 Q18 eq_refl).
  assert (E3_19 : reg_get regs3 19 = Z_to_bv 64 res) by exact (xget _ _ _ _ Hx3 Q19 eq_refl).
  assert (E3_20 : reg_get regs3 20 = Z_to_bv 64 (bv_unsigned b0 + -2)) by exact (xget _ _ _ _ Hx3 Q20 eq_refl).
  assert (E3_25 : reg_get regs3 25 = reg_get regs 25) by exact (xget _ _ _ _ Hx3 Q25 eq_refl).
  assert (E3_26 : reg_get regs3 26 = reg_get regs 26) by exact (xget _ _ _ _ Hx3 Q26 eq_refl).
  assert (E3_27 : reg_get regs3 27 = reg_get regs 27) by exact (xget _ _ _ _ Hx3 Q27 eq_refl).
  clear Q1 Q2 Q3 Q4 Q10 Q11 Q12 Q18 Q19 Q20 Q25 Q26 Q27.
  assert (Hsp3 : spZ regs3 = S - 192).
  { assert (E : spZ regs3 = bv_unsigned (reg_get regs3 2)) by reflexivity. rewrite E, E3_2. apply unsigned_lit. lia. }
  pose proof (lf_rw_cells_rel m3 m0' _ _ Hrel3 RW) as RW3. clear RW MU WM.
  clear Hx3 Hrel3 m0' R.
  pose proof (bv_unsigned_in_range 8 b0) as Hb0. unfold bv_modulus in Hb0. change (2 ^ Z.of_N 8) with 256 in Hb0.
  (* ---- check_restamp (f, n, ctr) ---- *)
  rewrite <- SEGS. change (Z_to_bv 64 0x12e14) with (Z_to_bv 64 CHECK_RESTAMP).
  eapply (g_cr B API SEGS AX ERRNO_LOW CR stk S L A mem md _ regs3 m3 md2 L1 A1 res nn (bv_unsigned cw)
    (sb_malloc b k)).
  { exact FR3. }
  { lia. }
  { lia. }
  { change (YK11.getr regs3 1) with (reg_get regs3 1). rewrite E3_1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp3. replace (S - 192) with (S + (-12) * 16) by lia. rewrite Z.mod_add by lia. exact HS16. }
  { rewrite Hsp3. unfold CHECK_RESTAMP_STACK, CR_FRAME, ALLOC_STACK. lia. }
  { rewrite Hsp3. lia. }
  { rewrite Hsp3. lia. }
  { change (YK11.getr regs3 4) with (reg_get regs3 4). rewrite E3_4. exact Htp. }
  { change (YK11.getr regs3 10) with (reg_get regs3 10). exact E3_10. }
  { change (YK11.getr regs3 11) with (reg_get regs3 11). exact E3_11. }
  { change (YK11.getr regs3 12) with (reg_get regs3 12). rewrite E3_12. symmetry. apply Z_to_bv_bv_unsigned. }
  { lia. }
  { exists res, k. split; [exact Hres_in | lia]. }
  { exact Hfrm. }
  { exact Hres2. }
  { destruct Hroom as (Hl1 & Hl2 & Hl3). apply room_slots_big; unfold sb_malloc; cbn [sb_live sb_bytes sb_cap];
      unfold CAPMAX in *; lia. }
  intros fx4 L4 A4 regs4 mem4 md4 Hfrm4 FR4 Hrp4 Eb4 Hres4 Hab4.
  pose proof FR4 as (HM4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro4).
  assert (E4_ : forall x, callee_saved x -> reg_get regs4 (Z_to_bv 5 x) = reg_get regs3 (Z_to_bv 5 x))
    by (intros x Hx2; exact (rp_get regs3 regs4 x Hrp4 Hx2)).
  assert (RW4 : rw_cells rsegs mem4 (S - 192 + 112) (llvm_sv regs)).
  { apply (lf_rw_cells_frame m3 mem4 _ _ RW3). intros a Ha. rewrite <- SEGS. apply Hab4. rewrite Hsp3.
    cbn in Ha. lia. }
  clear RW3.
  (* ---- mv a0, s3; mv a1, s2; jal check_mute ---- *)
  change (YK11.getr regs3 1) with (reg_get regs3 1). rewrite E3_1. rewrite SEGS.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM4) as (Hh4 & Hl4 & _).
  apply (llvm_run fx4 regs4 (Z_to_bv 64 0x12da4) mem4 md4
    (fun ms => exists R2, ms = MS R2 (@fp_regs fx4) (Z_to_bv 64 0x12eec) (@fp_csr fx4) None mem4 (seg_rom rsegs) /\
       reg_get R2 1 = Z_to_bv 64 0x12db0 /\ reg_get R2 10 = reg_get regs4 19 /\ reg_get R2 11 = reg_get regs4 18 /\
       forall x, callee_saved x -> reg_get R2 (Z_to_bv 5 x) = reg_get regs4 (Z_to_bv 5 x))
    _ Hh4 Hl4).
  { unfold Regs6ss.mkR_of. do 3 step. apply evt_done. eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros x Hx2.
    destruct (lf_callee_cases x Hx2) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      reflexivity. }
  { intros ms (R2 & -> & _). do 5 eexists. reflexivity. }
  intros R2 F2 pc2 fc2 m2' (R2' & HE2 & M1 & M10 & M11 & Mcs) regsm Hxm.
  injection HE2 as ER2 EF2 EP2 EC2 EM2. subst R2' F2 pc2 fc2 m2'.
  assert (Em_ : forall x, callee_saved x -> reg_get regsm (Z_to_bv 5 x) = reg_get regs3 (Z_to_bv 5 x)).
  { intros x Hx3. rewrite (xget _ _ _ _ Hxm (Mcs x Hx3) (cs_nz x Hx3)). exact (E4_ x Hx3). }
  assert (Em_1 : reg_get regsm 1 = Z_to_bv 64 0x12db0) by exact (xget _ _ _ _ Hxm M1 eq_refl).
  assert (Em_10 : reg_get regsm 10 = Z_to_bv 64 res).
  { rewrite (xget _ _ _ _ Hxm M10 eq_refl). exact (eq_trans (E4_ 19 ltac:(unfold callee_saved; lia)) E3_19). }
  assert (Em_11 : reg_get regsm 11 = Z_to_bv 64 nn).
  { rewrite (xget _ _ _ _ Hxm M11 eq_refl). exact (eq_trans (E4_ 18 ltac:(unfold callee_saved; lia)) E3_18). }
  assert (Em_2 : reg_get regsm 2 = Z_to_bv 64 (S - 192))
    by exact (eq_trans (Em_ 2 ltac:(unfold callee_saved; lia)) E3_2).
  assert (Em_4 : reg_get regsm 4 = reg_get regs 4)
    by exact (eq_trans (Em_ 4 ltac:(unfold callee_saved; lia)) E3_4).
  assert (Hspm : spZ regsm = S - 192).
  { assert (E : spZ regsm = bv_unsigned (reg_get regsm 2)) by reflexivity. rewrite E, Em_2. apply unsigned_lit. lia. }
  clear Hxm Mcs M1 M10 M11 R2.
  (* ---- check_mute (f, n) ---- *)
  rewrite <- SEGS. change (Z_to_bv 64 0x12eec) with (Z_to_bv 64 CHECK_MUTE).
  eapply (g_cm B API SEGS AX ERRNO_LOW CM stk S L A mem md _ regsm mem4 md4 L4 A4 res nn (sb_malloc b k)).
  { exact FR4. }
  { lia. }
  { lia. }
  { change (YK11.getr regsm 1) with (reg_get regsm 1). rewrite Em_1. apply ret_ok_even. reflexivity. }
  { rewrite Hspm. replace (S - 192) with (S + (-12) * 16) by lia. rewrite Z.mod_add by lia. exact HS16. }
  { rewrite Hspm. unfold CHECK_MUTE_STACK, CHECK_MUTE_FRAME, ALLOC_STACK. lia. }
  { rewrite Hspm. lia. }
  { rewrite Hspm. lia. }
  { change (YK11.getr regsm 4) with (reg_get regsm 4). rewrite Em_4. exact Htp. }
  { change (YK11.getr regsm 10) with (reg_get regsm 10). exact Em_10. }
  { change (YK11.getr regsm 11) with (reg_get regsm 11). exact Em_11. }
  { lia. }
  { exists res, k. split; [rewrite Eb4; exact Hres_in | lia]. }
  { exact Hfrm4. }
  { exact Hres4. }
  { destruct Hroom as (Hl1 & Hl2 & Hl3). unfold sb_malloc; cbn [sb_live sb_bytes sb_cap]. unfold CAPMAX in *. lia. }
  intros fx5 L5 A5 regs5 mem5 md5 Hfrm5 FR5 Hrp5 Eb5 Hres5 Hab5.
  pose proof FR5 as (HM5 & _ & _ & _ & _ & _ & _ & _ & _ & Hstw5 & _ & _ & Hro5).
  assert (E5_ : forall x, callee_saved x -> reg_get regs5 (Z_to_bv 5 x) = reg_get regs3 (Z_to_bv 5 x))
    by (intros x Hx2; rewrite (rp_get regsm regs5 x Hrp5 Hx2); exact (Em_ x Hx2)).
  assert (E5_2 : reg_get regs5 2 = Z_to_bv 64 (S - 192))
    by exact (eq_trans (E5_ 2 ltac:(unfold callee_saved; lia)) E3_2).
  assert (E5_3 : reg_get regs5 3 = reg_get regs 3)
    by exact (eq_trans (E5_ 3 ltac:(unfold callee_saved; lia)) E3_3).
  assert (E5_4 : reg_get regs5 4 = reg_get regs 4)
    by exact (eq_trans (E5_ 4 ltac:(unfold callee_saved; lia)) E3_4).
  assert (E5_18 : reg_get regs5 18 = Z_to_bv 64 nn)
    by exact (eq_trans (E5_ 18 ltac:(unfold callee_saved; lia)) E3_18).
  assert (E5_19 : reg_get regs5 19 = Z_to_bv 64 res)
    by exact (eq_trans (E5_ 19 ltac:(unfold callee_saved; lia)) E3_19).
  assert (E5_20 : reg_get regs5 20 = Z_to_bv 64 (bv_unsigned b0 + -2))
    by exact (eq_trans (E5_ 20 ltac:(unfold callee_saved; lia)) E3_20).
  assert (E5_25 : reg_get regs5 25 = reg_get regs 25)
    by exact (eq_trans (E5_ 25 ltac:(unfold callee_saved; lia)) E3_25).
  assert (E5_26 : reg_get regs5 26 = reg_get regs 26)
    by exact (eq_trans (E5_ 26 ltac:(unfold callee_saved; lia)) E3_26).
  assert (E5_27 : reg_get regs5 27 = reg_get regs 27)
    by exact (eq_trans (E5_ 27 ltac:(unfold callee_saved; lia)) E3_27).
  assert (RW5 : rw_cells rsegs mem5 (S - 192 + 112) (llvm_sv regs)).
  { apply (lf_rw_cells_frame mem4 mem5 _ _ RW4). intros a Ha. rewrite <- SEGS. apply Hab5. rewrite Hspm.
    cbn in Ha. lia. }
  clear RW4.
  assert (Hres_in5 : In (res, k) (blocks L5 A5)) by (rewrite Eb5, Eb4; exact Hres_in).
  destruct (norm_blk B API SEGS AX L5 A5 mem5 md5 res k HM5 Hres_in5 ltac:(lia) Hro5) as [jk5 HJK5].
  destruct (rwc_cut rsegs _ res _ jk5 (Z.to_nat nn) HJK5 ltac:(lia)) as [HJN5 _].
  destruct (bytes_of_rwc _ _ _ _ _ HJN5) as [HBS5 HLB5].
  (* ---- check_gate (f, n, slot) .. check_inject ---- *)
  change (YK11.getr regsm 1) with (reg_get regsm 1). rewrite Em_1. rewrite SEGS.
  eapply (g_run B API SEGS AX HGG) with (stk := stk) (S := S) (L0 := L) (A0 := A) (mem0 := mem) (md0 := md)
    (Q := qD (@fp_regs fx5) (@fp_csr fx5) (reg_get regs 3) (reg_get regs 4) (reg_get regs 25) (reg_get regs 26)
            (reg_get regs 27) (normalize rsegs mem5) (S - 192) res nn (bv_unsigned b0 + -2) (llvm_sv regs));
    [exact FR5 | lia | lia | | | ].
  { unfold Regs6ss.mkR_of. rewrite E5_2, E5_3, E5_4, E5_18, E5_19, E5_20, E5_25, E5_26, E5_27.
    apply (eD_evt CG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (llvm_sv regs) _ _ _ (S - 192) (S - stk)
      res nn (bv_unsigned b0 + -2) (firstn (Z.to_nat nn) jk5)).
    - lia.
    - lia.
    - lia.
    - exact Hr1.
    - lia.
    - lia.
    - lia.
    - apply (norm_stk B SEGS mem5 (S - stk) (S - 192) Hro5); [unfold LF_RES_TOP; lia | lia |].
      intros a Ha. apply Hstw5. lia.
    - apply mem_inv_normalize.
    - exact HBS5.
    - exact HLB5.
    - apply (lf_rw_cells_norm B mem5 _ _ SEGS Hro5); [|exact RW5].
      intros i Hi. apply NI. unfold LF_RES_TOP. cbn in Hi. lia.
    - reflexivity. }
  { intros ms HQ. destruct HQ as (R & m' & -> & HQ).
    repeat match type of HQ with _ /\ _ => let H := fresh "QQ" in destruct HQ as [H HQ] end.
    exists R, (@fp_regs fx5), (Z_to_bv 64 0x13028), (@fp_csr fx5), m', [(S - 192 - 80, S - 192)].
    split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    intros x Hx0 NO. apply en_out1 in NO. left. lia. }
  intros R F pc' fc m0' HQ regs6 m6 Hx6 Hrel6 FR6.
  destruct HQ as (R' & m'' & HE & Q1 & Q2 & Q3 & Q4 & Q10 & Q11 & Q12 & Q13 & Q18 & Q19 & Q20 & Q25 & Q26 & Q27
    & MU & WM & RW).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  assert (E6_1 : reg_get regs6 1 = Z_to_bv 64 0x12dd4) by exact (xget _ _ _ _ Hx6 Q1 eq_refl).
  assert (E6_2 : reg_get regs6 2 = Z_to_bv 64 (S - 192)) by exact (xget _ _ _ _ Hx6 Q2 eq_refl).
  assert (E6_3 : reg_get regs6 3 = reg_get regs 3) by exact (xget _ _ _ _ Hx6 Q3 eq_refl).
  assert (E6_4 : reg_get regs6 4 = reg_get regs 4) by exact (xget _ _ _ _ Hx6 Q4 eq_refl).
  assert (E6_10 : reg_get regs6 10 = Z_to_bv 64 res) by exact (xget _ _ _ _ Hx6 Q10 eq_refl).
  assert (E6_11 : reg_get regs6 11 = Z_to_bv 64 nn) by exact (xget _ _ _ _ Hx6 Q11 eq_refl).
  assert (E6_12 : reg_get regs6 12 = Z_to_bv 64 (bv_unsigned b0 + -2)) by exact (xget _ _ _ _ Hx6 Q12 eq_refl).
  assert (E6_13 : reg_get regs6 13 = Z_to_bv 64 (S - 192 + 8)) by exact (xget _ _ _ _ Hx6 Q13 eq_refl).
  assert (E6_18 : reg_get regs6 18 = Z_to_bv 64 nn) by exact (xget _ _ _ _ Hx6 Q18 eq_refl).
  assert (E6_19 : reg_get regs6 19 = Z_to_bv 64 res) by exact (xget _ _ _ _ Hx6 Q19 eq_refl).
  assert (E6_25 : reg_get regs6 25 = reg_get regs 25) by exact (xget _ _ _ _ Hx6 Q25 eq_refl).
  assert (E6_26 : reg_get regs6 26 = reg_get regs 26) by exact (xget _ _ _ _ Hx6 Q26 eq_refl).
  assert (E6_27 : reg_get regs6 27 = reg_get regs 27) by exact (xget _ _ _ _ Hx6 Q27 eq_refl).
  clear Q1 Q2 Q3 Q4 Q10 Q11 Q12 Q13 Q18 Q19 Q20 Q25 Q26 Q27.
  assert (Hsp6 : spZ regs6 = S - 192).
  { assert (E : spZ regs6 = bv_unsigned (reg_get regs6 2)) by reflexivity. rewrite E, E6_2. apply unsigned_lit. lia. }
  pose proof (lf_rw_cells_rel m6 m0' _ _ Hrel6 RW) as RW6. clear RW MU WM.
  clear Hx6 Hrel6 m0' R.
  pose proof FR6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw6 & _ & _ & _).
  (* ---- check_inject (f, n, slot, v) ---- *)
  rewrite <- SEGS. change (Z_to_bv 64 0x13028) with (Z_to_bv 64 CHECK_INJECT).
  eapply (g_ci B API SEGS AX ERRNO_LOW CI stk S L A mem md _ regs6 m6 md5 L5 A5 res nn (bv_unsigned b0 + -2)
    (S - 192 + 8) (sb_malloc b k)).
  { exact FR6. }
  { lia. }
  { lia. }
  { change (YK11.getr regs6 1) with (reg_get regs6 1). rewrite E6_1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp6. replace (S - 192) with (S + (-12) * 16) by lia. rewrite Z.mod_add by lia. exact HS16. }
  { rewrite Hsp6. unfold CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK. lia. }
  { rewrite Hsp6. lia. }
  { rewrite Hsp6. lia. }
  { change (YK11.getr regs6 4) with (reg_get regs6 4). rewrite E6_4. exact Htp. }
  { change (YK11.getr regs6 10) with (reg_get regs6 10). exact E6_10. }
  { change (YK11.getr regs6 11) with (reg_get regs6 11). exact E6_11. }
  { change (YK11.getr regs6 12) with (reg_get regs6 12). exact E6_12. }
  { change (YK11.getr regs6 13) with (reg_get regs6 13). exact E6_13. }
  { lia. }
  { lia. }
  { exists res, k. split; [exact Hres_in5 | lia]. }
  { rewrite Hsp6. lia. }
  { lia. }
  { Z.div_mod_to_equations. lia. }
  { intros i Hi. apply (lf_present_of_writable B m6 _ SEGS); [apply NI; unfold LF_RES_TOP; lia | lia |].
    rewrite <- SEGS. apply Hstw6. lia. }
  { exact Hfrm5. }
  { exact Hres5. }
  { destruct Hroom as (Hl1 & Hl2 & Hl3). unfold sb_malloc; cbn [sb_live sb_bytes sb_cap]. unfold CAPMAX in *. lia. }
  intros fx7 L7 A7 regs7 mem7 md7 Hfrm7 FR7 Hrp7 Eb7 Hres7 Hab7.
  pose proof FR7 as (HM7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro7).
  assert (E7_ : forall x, callee_saved x -> reg_get regs7 (Z_to_bv 5 x) = reg_get regs6 (Z_to_bv 5 x))
    by (intros x Hx2; exact (rp_get regs6 regs7 x Hrp7 Hx2)).
  assert (RW7 : rw_cells rsegs mem7 (S - 192 + 112) (llvm_sv regs)).
  { apply (lf_rw_cells_frame m6 mem7 _ _ RW6). intros a Ha. rewrite <- SEGS. apply Hab7. rewrite Hsp6.
    cbn in Ha. lia. }
  clear RW6.
  (* ---- mv a0, s3; jal free ---- *)
  change (YK11.getr regs6 1) with (reg_get regs6 1). rewrite E6_1. rewrite SEGS.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM7) as (Hh7 & Hl7 & _).
  apply (llvm_run fx7 regs7 (Z_to_bv 64 0x12dd4) mem7 md7
    (fun ms => exists R2, ms = MS R2 (@fp_regs fx7) (Z_to_bv 64 0x13ed0) (@fp_csr fx7) None mem7 (seg_rom rsegs) /\
       reg_get R2 1 = Z_to_bv 64 0x12ddc /\ reg_get R2 10 = reg_get regs7 19 /\
       forall x, callee_saved x -> reg_get R2 (Z_to_bv 5 x) = reg_get regs7 (Z_to_bv 5 x))
    _ Hh7 Hl7).
  { unfold Regs6ss.mkR_of. do 2 step. apply evt_done. eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    intros x Hx2.
    destruct (lf_callee_cases x Hx2) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      reflexivity. }
  { intros ms (R2 & -> & _). do 5 eexists. reflexivity. }
  intros R2 F2 pc2 fc2 m2' (R2' & HE2 & M1 & M10 & Mcs) regsf Hxf.
  injection HE2 as ER2 EF2 EP2 EC2 EM2. subst R2' F2 pc2 fc2 m2'.
  assert (Ef_ : forall x, callee_saved x -> reg_get regsf (Z_to_bv 5 x) = reg_get regs6 (Z_to_bv 5 x)).
  { intros x Hx3. rewrite (xget _ _ _ _ Hxf (Mcs x Hx3) (cs_nz x Hx3)). exact (E7_ x Hx3). }
  assert (Ef_1 : reg_get regsf 1 = Z_to_bv 64 0x12ddc) by exact (xget _ _ _ _ Hxf M1 eq_refl).
  assert (Ef_10 : reg_get regsf 10 = Z_to_bv 64 res).
  { rewrite (xget _ _ _ _ Hxf M10 eq_refl). exact (eq_trans (E7_ 19 ltac:(unfold callee_saved; lia)) E6_19). }
  assert (Ef_2 : reg_get regsf 2 = Z_to_bv 64 (S - 192))
    by exact (eq_trans (Ef_ 2 ltac:(unfold callee_saved; lia)) E6_2).
  assert (Ef_4 : reg_get regsf 4 = reg_get regs 4)
    by exact (eq_trans (Ef_ 4 ltac:(unfold callee_saved; lia)) E6_4).
  assert (Hspf : spZ regsf = S - 192).
  { assert (E : spZ regsf = bv_unsigned (reg_get regsf 2)) by reflexivity. rewrite E, Ef_2. apply unsigned_lit. lia. }
  clear Hxf Mcs M1 M10 R2.
  (* ---- free (f) ---- *)
  rewrite <- SEGS. change (Z_to_bv 64 0x13ed0) with (Z_to_bv 64 LLVM_FREE).
  eapply (g_free B API SEGS AX ERRNO_LOW HFRE FREE stk S L A mem md _ regsf mem7 md7 L7 A7 res k (sb_malloc b k)).
  { exact FR7. }
  { lia. }
  { lia. }
  { change (YK11.getr regsf 1) with (reg_get regsf 1). rewrite Ef_1. apply ret_ok_even. reflexivity. }
  { rewrite Hspf. replace (S - 192) with (S + (-12) * 16) by lia. rewrite Z.mod_add by lia. exact HS16. }
  { rewrite Hspf. unfold ALLOC_STACK. lia. }
  { rewrite Hspf. lia. }
  { rewrite Hspf. lia. }
  { change (YK11.getr regsf 4) with (reg_get regsf 4). rewrite Ef_4. exact Htp. }
  { change (YK11.getr regsf 10) with (reg_get regsf 10). exact Ef_10. }
  { rewrite Eb7. exact Hres_in5. }
  { lia. }
  { exact MINE. }
  { exact Hres7. }
  intros L8 A8 regs8 mem8 md8 FR8 Hrp8 _ Hres8 Hab8 _.
  assert (E8_ : forall x, callee_saved x -> reg_get regs8 (Z_to_bv 5 x) = reg_get regs6 (Z_to_bv 5 x))
    by (intros x Hx2; rewrite (rp_get regsf regs8 x Hrp8 Hx2); exact (Ef_ x Hx2)).
  assert (E8_2 : reg_get regs8 2 = Z_to_bv 64 (S - 192))
    by exact (eq_trans (E8_ 2 ltac:(unfold callee_saved; lia)) E6_2).
  assert (E8_3 : reg_get regs8 3 = reg_get regs 3)
    by exact (eq_trans (E8_ 3 ltac:(unfold callee_saved; lia)) E6_3).
  assert (E8_4 : reg_get regs8 4 = reg_get regs 4)
    by exact (eq_trans (E8_ 4 ltac:(unfold callee_saved; lia)) E6_4).
  assert (E8_25 : reg_get regs8 25 = reg_get regs 25)
    by exact (eq_trans (E8_ 25 ltac:(unfold callee_saved; lia)) E6_25).
  assert (E8_26 : reg_get regs8 26 = reg_get regs 26)
    by exact (eq_trans (E8_ 26 ltac:(unfold callee_saved; lia)) E6_26).
  assert (E8_27 : reg_get regs8 27 = reg_get regs 27)
    by exact (eq_trans (E8_ 27 ltac:(unfold callee_saved; lia)) E6_27).
  assert (RW8 : rw_cells rsegs mem8 (S - 192 + 112) (llvm_sv regs)).
  { apply (lf_rw_cells_frame mem7 mem8 _ _ RW7). intros a Ha. rewrite <- SEGS. apply Hab8. rewrite Hspf.
    cbn in Ha. lia. }
  clear RW7.
  pose proof FR8 as (HM8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  (* ---- return 0 ---- *)
  change (YK11.getr regsf 1) with (reg_get regsf 1). rewrite Ef_1. rewrite SEGS.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM8) as (Hh8 & Hl8 & _).
  apply (llvm_run fx7 regs8 (Z_to_bv 64 0x12ddc) mem8 md8
    (fun ms => exists R2, ms = MS R2 (@fp_regs fx7) (ret_pc (reg_get regs 1)) (@fp_csr fx7) None mem8 (seg_rom rsegs) /\
       reg_get R2 10 = Z_to_bv 64 0 /\
       forall x, callee_saved x -> reg_get R2 (Z_to_bv 5 x) = reg_get regs (Z_to_bv 5 x))
    _ Hh8 Hl8).
  { unfold Regs6ss.mkR_of. rewrite E8_2, E8_3, E8_4, E8_25, E8_26, E8_27. unfold llvm_sv in RW8.
    do 13 step.
    apply evt_done. eexists. split; [reflexivity|]. split; [reflexivity|].
    intros x Hx2.
    destruct (lf_callee_cases x Hx2) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      try reflexivity.
    transitivity (Z_to_bv 64 (S - 192 + 192)); [reflexivity|].
    replace (S - 192 + 192) with S by lia. rewrite Esp. apply Z_to_bv_bv_unsigned. }
  { intros ms (R2 & -> & _). do 5 eexists. reflexivity. }
  intros R2 F2 pc2 fc2 m2' (R2' & HE2 & H10' & Hcs') regs9 Hx9.
  injection HE2 as ER2 EF2 EP2 EC2 EM2. subst R2' F2 pc2 fc2 m2'.
  apply SR_ret.
  assert (G10' : YK11.getr regs9 10 = Z_to_bv 64 0) by (rewrite (lf_getr_eqv _ _ _ Hx9); exact H10').
  assert (RP : regs_preserved regs regs9).
  { intros x Hx4. rewrite (lf_getr_eqv _ _ _ Hx9), lf_getr_cs by exact Hx4. rewrite lf_getr_cs by exact Hx4.
    exact (Hcs' x Hx4). }
  destruct (lf_post B API SINK stk empty L A regs mem md ra p n L8 A8 regs9 mem8 md8 Hpre Hsn FR8 G10' RP)
    as (Hpost2 & Hsn' & Hpay & MI2).
  exists (mkFP (@fp_regs fx7) (@fp_csr fx7)), L8, A8, regs9, mem8, md8.
  assert (E1 : YK11.getr regs 1 = reg_get regs 1) by reflexivity.
  split; [rewrite <- E1, Hra1, (lf_ret_pc _ Hra); reflexivity|].
  split; [exact Hfrm7|]. split; [exact Hpost2|]. split; [exact Hsn'|].
  split; [rewrite sb_free_malloc in Hres8; exact Hres8|].
  split; [rewrite <- SEGS; exact Hpay|]. split; [exact MI2 | exact I].
Qed.

End M.
