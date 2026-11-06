From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import check_round_trip_c LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_fr fd_glue.
Import ListNotations.
Open Scope Z_scope.

Definition llvm_saved_cells (regs0 : bvmap 5 word) : list cell :=
  [C8 (YK11.getr regs0 27); C8 (YK11.getr regs0 26); C8 (YK11.getr regs0 25); C8 (YK11.getr regs0 24);
   C8 (YK11.getr regs0 23); C8 (YK11.getr regs0 22); C8 (YK11.getr regs0 21); C8 (YK11.getr regs0 20);
   C8 (YK11.getr regs0 19); C8 (YK11.getr regs0 18); C8 (YK11.getr regs0 9); C8 (YK11.getr regs0 8);
   C8 (YK11.getr regs0 1)].

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

Theorem fx_exit_holds : forall stk empty L0 A0 regs0 mem0 md0 ra p n b j (fx' : YK11.FPState) regs mem md L A
    frame len jx,
  llvm_binds B API -> LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n -> sink_none B mem0 md0 ->
  frm_zero (@fp_csr fx') ->
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  In (frame, len) (blocks L A) -> (forall a k, In (a, k) (blocks L0 A0) -> a <> frame) ->
  res_ok_slots A (sb_malloc b len) ->
  YK11.getr regs 2 = Z_to_bv 64 (spZ regs0 - 160) -> YK11.getr regs 3 = YK11.getr regs0 3 ->
  YK11.getr regs 4 = YK11.getr regs0 4 -> YK11.getr regs 26 = Z_to_bv 64 frame ->
  rw_cells rsegs mem (spZ regs0 - 160) (CB 56 jx :: llvm_saved_cells regs0) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x132ac) mem (YK11.seg_rom (ms_segs B))) md)
    (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b j fx' regs mem md L A frame len jx
    (SEGS & HMAL & HFRE & HGG & HG & AX) Hstk Hra Hpre Hsn Hfrm FR Hin Hnf RES Hsp Hgp Htp Hs0 HF.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra0 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & Hp0 & Hn0
    & Hpl0 & Hrod0).
  unfold LLVM_K, LLVM_FRAME, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK in Hstk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof Hin as Hin'. apply blocks_In in Hin' as (q & Hq & Hqin).
  remember (spZ regs0) as S eqn:ES.
  assert (Hspv : bv_unsigned (YK11.getr regs 2) = S - 160).
  { rewrite Hsp. apply unsigned_lit. lia. }
  rewrite SEGS.
  apply (llvm_run fx' regs (Z_to_bv 64 0x132ac) mem md
    (fun ms => exists R, ms = MS R (@fp_regs fx') (Z_to_bv 64 0x14684) (@fp_csr fx') None mem (YK11.seg_rom rsegs) /\
       reg_get R 1 = Z_to_bv 64 0x132b4 /\ reg_get R 10 = reg_get regs 26 /\
       forall x, callee_saved x -> reg_get R (Z_to_bv 5 x) = reg_get regs (Z_to_bv 5 x)));
    [exact Hh | exact Hl | | |].
  { unfold Regs6ss.mkR_of.
    step. step.
    apply evt_done. eexists. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros x Hx. destruct (lf_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      reflexivity. }
  { intros ms (R & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R' & HE & H1 & H10 & Hcs) regs' Hx.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  assert (G1 : YK11.getr regs' 1 = Z_to_bv 64 0x132b4) by (rewrite (lf_getr_eqv _ _ _ Hx); exact H1).
  assert (G2 : YK11.getr regs' 2 = YK11.getr regs 2)
    by (rewrite (lf_getr_eqv _ _ _ Hx); exact (Hcs 2 ltac:(unfold callee_saved; lia))).
  assert (G3 : YK11.getr regs' 3 = YK11.getr regs 3)
    by (rewrite (lf_getr_eqv _ _ _ Hx); exact (Hcs 3 ltac:(unfold callee_saved; lia))).
  assert (G4 : YK11.getr regs' 4 = YK11.getr regs 4)
    by (rewrite (lf_getr_eqv _ _ _ Hx); exact (Hcs 4 ltac:(unfold callee_saved; lia))).
  assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 frame)
    by (rewrite (lf_getr_eqv _ _ _ Hx); change (reg_get R' 10 = Z_to_bv 64 frame); rewrite H10; exact Hs0).
  assert (Hsp' : spZ regs' = S - 160) by (unfold spZ; rewrite G2; exact Hspv).
  assert (Hfreed : forall a, ptr_addr L q <= a < ptr_addr L q + len -> a < YM05.alloc_ceiling /\ ~ in_img B a).
  { intros a Ha.
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md q len (a - ptr_addr L q) HM Hqin ltac:(lia))
      as (_ & R1 & R2 & _).
    pose proof (ax_blocks_img AX L A mem md q len (a - ptr_addr L q) HM Hqin ltac:(lia)) as Himgx.
    replace (ptr_addr L q + (a - ptr_addr L q)) with a in Himgx by lia. split; [lia | exact Himgx]. }
  rewrite <- SEGS.
  eapply SR_bind.
  { replace (Z_to_bv 64 0x14684) with (Z_to_bv 64 (ms_free B)) by (rewrite HFRE; reflexivity).
    apply (FREE (mkFP (@fp_regs fx') (@fp_csr fx')) L A regs' mem md q len (sb_malloc b len)).
    - split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [rewrite G1; apply ret_ok_even; reflexivity|].
      split; [rewrite Hsp'; replace (S - 160) with (S + (-10) * 16) by lia;
        rewrite Z.mod_add by lia; exact Hal0|].
      split; [unfold ALLOC_STACK; lia|]. split; [lia|].
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
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | rewrite Hsp'; unfold ALLOC_STACK; lia | rewrite Hsp'; lia | | | | | | exact (Hidt HID) | | ].
    - intros a Ha. right. exact (Hfreed a Ha).
    - intros a Ha. right. intros Hf. destruct (Hfreed a Hf) as (N1 & _). lia.
    - intros a Hf Ha. destruct (Hfreed a Hf) as (N1 & _). lia.
    - intros a0 k0 Hin0. pose proof (Hblk a0 k0 Hin0) as Hin2. rewrite Eb1 in Hin2. rewrite Eb2.
      apply in_app_or in Hin2. apply in_or_app. destruct Hin2 as [Hin2|[Hin2|Hin2]]; [left; exact Hin2 | | right; exact Hin2].
      exfalso. injection Hin2 as E1 E2. apply (Hnf a0 k0 Hin0). rewrite <- Hq. symmetry. exact E1.
    - intros a0 k0 i Hin0 Hi. apply (Hkept a0 k0 i (Hblk a0 k0 Hin0)); [|exact Hi].
      intros E. apply (Hnf a0 k0 Hin0). rewrite <- Hq. exact E.
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  assert (Hcs2 : forall x, callee_saved x -> YK11.getr regs2 (Z_to_bv 5 x) = YK11.getr regs (Z_to_bv 5 x)).
  { intros x Hx2. rewrite (Hrp x Hx2), (lf_getr_eqv _ _ _ Hx), !lf_getr_cs by exact Hx2. exact (Hcs x Hx2). }
  assert (E2 : reg_get regs2 2 = Z_to_bv 64 (S - 160)).
  { change (YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (S - 160)).
    rewrite (Hcs2 2 ltac:(unfold callee_saved; lia)). subst S. exact Hsp. }
  assert (E3 : reg_get regs2 3 = YK11.getr regs0 3).
  { change (YK11.getr regs2 (Z_to_bv 5 3) = YK11.getr regs0 3).
    rewrite (Hcs2 3 ltac:(unfold callee_saved; lia)). exact Hgp. }
  assert (E4 : reg_get regs2 4 = YK11.getr regs0 4).
  { change (YK11.getr regs2 (Z_to_bv 5 4) = YK11.getr regs0 4).
    rewrite (Hcs2 4 ltac:(unfold callee_saved; lia)). exact Htp. }
  assert (HF2 : rw_cells rsegs mem2 (S - 160) (CB 56 jx :: llvm_saved_cells regs0)).
  { apply (lf_rw_cells_frame mem); [exact HF|]. intros a Ha. cbn [cells_size csize llvm_saved_cells Nat.add] in Ha.
    rewrite <- SEGS. apply Hfr2.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
    - unfold scratch_k, scratch. rewrite Hsp'. unfold ALLOC_STACK.
      intros [Hs|Hs]; [lia | pose proof (lf_errno_low B ERRNO_LOW a Hs); lia].
    - intros Hf. destruct (Hfreed a Hf) as (N1 & _). lia. }
  rewrite G1, SEGS.
  apply (llvm_run (mkFP (@fp_regs fx') (@fp_csr fx')) regs2 (Z_to_bv 64 0x132b4) mem2 md2
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
    cbn. replace (S - 160 + 160) with S by lia. subst S. unfold spZ. apply Z_to_bv_bv_unsigned. }
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
  split; [rewrite sb_free_malloc in Hres2; exact Hres2|].
  split; [exact Hpay|]. split; [exact MI2 | exact I].
Qed.

End X.
