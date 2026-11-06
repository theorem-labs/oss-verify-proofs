From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import LLVMFuzzerTestOneInput_inv.
Import ListNotations.
Open Scope Z_scope.

Lemma lf_rw_cells_frame : forall m m' A cs,
  rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) ->
     mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (H0 & H1 & Hb)] (W0 & W1 & Hw)] HE.
  rewrite cells_bytes_length in H1 by exact Hwf.
  split; [split; [exact Hwf|] |].
  - split; [exact H0|]. split; [rewrite cells_bytes_length by exact Hwf; exact H1|].
    intros i Hi. rewrite <- (Hb i Hi). rewrite cells_bytes_length in Hi by exact Hwf.
    change (mrd rsegs m' (wa (A + Z.of_nat i)) = mrd rsegs m (wa (A + Z.of_nat i))).
    exact (proj1 (HE (A + Z.of_nat i) ltac:(lia))).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    apply (proj1 (proj2 (HE (A + i) ltac:(lia)))). exact (Hw i Hi).
Qed.

Lemma lf_callee_cases : forall x, callee_saved x ->
  x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ x = 9 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/
  x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27.
Proof. intros x Hx. unfold callee_saved in Hx. lia. Qed.

Lemma lf_getr_cs : forall R x, callee_saved x -> YK11.getr R (Z_to_bv 5 x) = reg_get R (Z_to_bv 5 x).
Proof.
  intros R x Hx.
  destruct (lf_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    reflexivity.
Qed.

Section X.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.

Theorem llvm_exit_holds : forall stk empty L0 A0 regs0 mem0 md0 ra p n b j k c,
  llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b ->
  llvm_X B API stk L0 A0 regs0 mem0 md0 b k c ->
  SR (ms_segs B) c (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b j k c CTX
    (fx' & regs & mem & md & L & A & r & jx & -> & Hfrm & Hsp & Hgp & Htp & Hs0 & HF & (FR & MINE & RES) & Hk).
  pose proof CTX as ((SEGS & HMAL & HFRE & HGG & HG & AX) & Hstk & Hra & Hpre & Hsn & Hsp47 & Hres0 & Hroom
    & Hro0 & Hrelro & Hfrm0 & Hn26).
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra0 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & Hp0 & Hn0
    & Hpl0 & Hrod0).
  unfold LLVM_K, LLVM_FRAME in Hstk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  destruct (llvm_md_ok B API _ _ _ _ _ _ _ _ _ _ FR) as [Hh Hl].
  destruct MINE as (Hrin & Hr288 & Hrd).
  pose proof Hrin as Hrin'. apply blocks_In in Hrin' as (q & Hq & Hqin).
  remember (spZ regs0) as S eqn:ES.
  assert (Hspv : bv_unsigned (YK11.getr regs 2) = S - 448).
  { rewrite Hsp. apply unsigned_lit. lia. }
  rewrite SEGS.
  apply (llvm_run fx' regs (Z_to_bv 64 LLVM_EXIT) mem md
    (fun ms => exists R, ms = MS R (@fp_regs fx') (Z_to_bv 64 0x14648) (@fp_csr fx') None mem (YK11.seg_rom rsegs) /\
       reg_get R 1 = Z_to_bv 64 0x13410 /\ reg_get R 10 = reg_get regs 8 /\
       forall x, callee_saved x -> reg_get R (Z_to_bv 5 x) = reg_get regs (Z_to_bv 5 x)));
    [exact Hh | exact Hl | | |].
  { unfold Regs6ss.mkR_of, LLVM_EXIT.
    step. step.
    apply evt_done. eexists. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros x Hx. destruct (lf_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      reflexivity. }
  { intros ms (R & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R' & HE & H1 & H10 & Hcs) regs' Hx.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  assert (G1 : YK11.getr regs' 1 = Z_to_bv 64 0x13410) by (rewrite (lf_getr_eqv _ _ _ Hx); exact H1).
  assert (G2 : YK11.getr regs' 2 = YK11.getr regs 2)
    by (rewrite (lf_getr_eqv _ _ _ Hx); exact (Hcs 2 ltac:(unfold callee_saved; lia))).
  assert (G3 : YK11.getr regs' 3 = YK11.getr regs 3)
    by (rewrite (lf_getr_eqv _ _ _ Hx); exact (Hcs 3 ltac:(unfold callee_saved; lia))).
  assert (G4 : YK11.getr regs' 4 = YK11.getr regs 4)
    by (rewrite (lf_getr_eqv _ _ _ Hx); exact (Hcs 4 ltac:(unfold callee_saved; lia))).
  assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 r)
    by (rewrite (lf_getr_eqv _ _ _ Hx); change (reg_get R' 10 = Z_to_bv 64 r); rewrite H10; exact Hs0).
  assert (Hsp' : spZ regs' = S - 448) by (unfold spZ; rewrite G2; exact Hspv).
  rewrite <- SEGS.
  eapply SR_bind.
  { replace (Z_to_bv 64 0x14648) with (Z_to_bv 64 (ms_free B)) by (rewrite HFRE; reflexivity).
    apply (FREE (mkFP (@fp_regs fx') (@fp_csr fx')) L A regs' mem md q 288 (sb_malloc b LLVM_REQ)).
    - split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [rewrite G1; apply ret_ok_even; reflexivity|].
      split; [rewrite Hsp'; subst S; lia|]. split; [unfold ALLOC_STACK; lia|]. split; [lia|].
      split; [intros a Ha; apply Hstw; unfold ALLOC_STACK in Ha; lia|].
      split; [rewrite G4, Htp; exact Htp0|]. split; [exact Herr|]. intros E. rewrite HID in E. discriminate.
    - rewrite SEGS. exact MI.
    - exact Hqin.
    - rewrite G10, Hq. reflexivity.
    - exact RES. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & -> & Hpost & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub & Hidt
    & Hlen & Hres2).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (Hfreed : forall a, ptr_addr L q <= a < ptr_addr L q + 288 -> a < YM05.alloc_ceiling /\ ~ in_img B a /\
             forall a0 k0, In (a0, k0) (blocks L0 A0) -> ~ (a0 <= a < a0 + k0)).
  { intros a Ha. rewrite Hq in Ha.
    destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 a HM (conj Hrin (conj Hr288 Hrd)) Ha)
      as (N1 & N2 & N3 & _ & N4). split; [lia|]. split; [exact N2 | exact N4]. }
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | rewrite Hsp'; unfold ALLOC_STACK; lia | rewrite Hsp'; lia | | | | | | exact (Hidt HID) | | ].
    - intros a Ha. right. destruct (Hfreed a Ha) as (N1 & N2 & _). auto.
    - intros a Ha. right. intros Hf. destruct (Hfreed a Hf) as (N1 & _). lia.
    - intros a Hf Ha. destruct (Hfreed a Hf) as (N1 & _). lia.
    - intros a0 k0 Hin. pose proof (Hblk a0 k0 Hin) as Hin2. rewrite Eb1 in Hin2. rewrite Eb2.
      apply in_app_or in Hin2. apply in_or_app. destruct Hin2 as [Hin2|[Hin2|Hin2]]; [left; exact Hin2 | | right; exact Hin2].
      exfalso. injection Hin2 as E1 E2. subst a0 k0. destruct (Hrd _ _ Hin); rewrite Hq in *; lia.
    - intros a0 k0 i Hin Hi. apply (Hkept a0 k0 i (Hblk a0 k0 Hin)); [|exact Hi].
      intros E. rewrite Hq in E. subst a0. destruct (Hrd _ _ Hin); lia.
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  assert (Hcs2 : forall x, callee_saved x -> YK11.getr regs2 (Z_to_bv 5 x) = YK11.getr regs (Z_to_bv 5 x)).
  { intros x Hx2. rewrite (Hrp x Hx2), (lf_getr_eqv _ _ _ Hx), !lf_getr_cs by exact Hx2. exact (Hcs x Hx2). }
  assert (E2 : reg_get regs2 2 = Z_to_bv 64 (S - 448)).
  { change (YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (S - 448)).
    rewrite (Hcs2 2 ltac:(unfold callee_saved; lia)). exact Hsp. }
  assert (E3 : reg_get regs2 3 = YK11.getr regs0 3).
  { change (YK11.getr regs2 (Z_to_bv 5 3) = YK11.getr regs0 3).
    rewrite (Hcs2 3 ltac:(unfold callee_saved; lia)). exact Hgp. }
  assert (E4 : reg_get regs2 4 = YK11.getr regs0 4).
  { change (YK11.getr regs2 (Z_to_bv 5 4) = YK11.getr regs0 4).
    rewrite (Hcs2 4 ltac:(unfold callee_saved; lia)). exact Htp. }
  assert (HF2 : rw_cells rsegs mem2 (S - 448) (CB 344 jx :: llvm_saved_cells regs0)).
  { apply (lf_rw_cells_frame mem); [exact HF|]. intros a Ha. cbn [cells_size csize llvm_saved_cells Nat.add] in Ha.
    rewrite <- SEGS. apply Hfr2.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
    - unfold scratch_k, scratch. rewrite Hsp'. unfold ALLOC_STACK.
      intros [Hs|Hs]; [lia | pose proof (lf_errno_low B ERRNO_LOW a Hs); lia].
    - intros Hf. destruct (Hfreed a Hf) as (N1 & _). lia. }
  rewrite G1, SEGS.
  apply (llvm_run (mkFP (@fp_regs fx') (@fp_csr fx')) regs2 (Z_to_bv 64 0x13410) mem2 md2
    (fun ms => exists R2, ms = MS R2 (@fp_regs fx') (ret_pc (YK11.getr regs0 1)) (@fp_csr fx') None mem2 (YK11.seg_rom rsegs) /\
       reg_get R2 10 = Z_to_bv 64 0 /\
       forall x, callee_saved x -> reg_get R2 (Z_to_bv 5 x) = YK11.getr regs0 (Z_to_bv 5 x)));
    [ | | | | ].
  { destruct (mr_model B _ (aa_laws API) _ _ _ _ HM2) as (H2h & _). exact H2h. }
  { destruct (mr_model B _ (aa_laws API) _ _ _ _ HM2) as (_ & H2l & _). exact H2l. }
  { unfold Regs6ss.mkR_of. rewrite E2, E3, E4. unfold llvm_saved_cells in HF2.
    do 16 step.
    apply evt_done. eexists. split; [reflexivity|]. split; [reflexivity|].
    intros x Hx2. destruct (lf_callee_cases x Hx2) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      try reflexivity.
    cbn. replace (S - 448 + 448) with S by lia. subst S. unfold spZ. apply Z_to_bv_bv_unsigned. }
  { intros ms (R2 & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R2 & HE & H10' & Hcs') regs3 Hx3.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  apply SR_ret. subst S.
  assert (G10' : YK11.getr regs3 10 = Z_to_bv 64 0) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact H10').
  assert (RP : regs_preserved regs0 regs3).
  { intros x Hx4. rewrite (lf_getr_eqv _ _ _ Hx3), lf_getr_cs by exact Hx4. exact (Hcs' x Hx4). }
  destruct (lf_post B API SINK stk empty L0 A0 regs0 mem0 md0 ra p n L2 A2 regs3 mem2 md2 Hpre Hsn FR2 G10' RP)
    as (Hpost2 & Hsn' & Hpay & MI2).
  exists (mkFP (@fp_regs fx') (@fp_csr fx')), L2, A2, regs3, mem2, md2.
  split; [rewrite Hra0, (lf_ret_pc _ Hra), SEGS; reflexivity|].
  split; [exact Hfrm|]. split; [exact Hpost2|]. split; [exact Hsn'|].
  split; [unfold LLVM_REQ in Hres2; rewrite sb_free_malloc in Hres2; exact Hres2|].
  split; [exact Hpay|]. split; [exact MI2 | exact I].
Qed.

End X.
