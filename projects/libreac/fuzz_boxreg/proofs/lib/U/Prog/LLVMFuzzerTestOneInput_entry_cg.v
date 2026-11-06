From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregInit reac_boxreg_init_c check_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import reac_boxreg_find.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv
LLVMFuzzerTestOneInput_exit LLVMFuzzerTestOneInput_top LLVMFuzzerTestOneInput_join.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import LLVMFuzzerTestOneInput_entry LLVMFuzzerTestOneInput_cfb read_name_ccf LLVMFuzzerTestOneInput_exit_cg LLVMFuzzerTestOneInput_top_cg LLVMFuzzerTestOneInput_join_cg.
Import ListNotations.
Open Scope Z_scope.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract_ag fx' rc B API.
Hypothesis INIT : reac_boxreg_init_contract.
Hypothesis CHECK : check_contract.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.

Theorem llvm_entry_holds_cf : forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
    llvm_ctx_cf B API stk empty L0 A0 regs0 mem0 md0 ra p n b ->
    SRcf B (mkCfg (YK11.mkst regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (YK11.seg_rom (ms_segs B))) md0)
      (fun c => llvm_J B API stk L0 A0 regs0 mem0 md0 p n b 0 1 c \/ llvm_X B API stk L0 A0 regs0 mem0 md0 b 1 c).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b CTX.
  pose proof CTX as ((SEGS & HMAL & HFRE & HGG & HG & AX) & Hk & Hra & Hpre & Hsn & Hsp47 & Hres & Hroom & Hro
    & Hrelro & Hfrm & Hn26).
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn1 & Hpl & Hrod).
  pose proof (lf_fr_init B API stk empty L0 A0 regs0 mem0 md0 ra p n Hpre Hro) as FR0.
  unfold LLVM_K, LLVM_FRAME in Hk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (Hn0 : 0 <= n) by (destruct Hpl as [[-> _] | [H _]]; lia).
  assert (E11 : bv_unsigned (reg_get regs0 11) = n).
  { change (reg_get regs0 11) with (YK11.getr regs0 11). rewrite Hn1. apply unsigned_lit. lia. }
  set (S := spZ regs0) in *.
  assert (ES : bv_unsigned (reg_get regs0 2) = S) by reflexivity.
  rewrite SEGS.
  eapply ((llvm_run_norm_cf B ltac:(segs_tac)) fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 md0); [exact Hh | exact Hl | exact Hro | | |].
  - unfold Regs6ss.mkR_of, LLVM_ENTRY.
    apply en_pro_evt with (lo := S - stk).
    + rewrite ES. apply lf_stk; [lia | lia |].
      intros a Ha. unfold writable_at.
      assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
      rewrite (wview_rel_rw rsegs mem0 (normalize rsegs mem0) _ (mem_rel_normalize rsegs mem0 Hro)
                 (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
      rewrite <- SEGS. exact (Hstw a Ha).
    + rewrite ES. lia.
    + exact (mem_inv_normalize rsegs mem0).
    + rewrite E11. lia.
  - intros ms (a1' & j1 & m'' & -> & _). do 5 eexists. reflexivity.
  - intros R F pc' fc m0' (a1' & j1 & m'' & HE & MU & WM & MI' & ST' & CF) regs1 m1 Hx Hrel Hsame.
    injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
    assert (MU' : munch [(S - 464, S)] mem0 m1)
      by exact (munch_rel rsegs _ mem0 (normalize rsegs mem0) m1 m'' (mem_rel_normalize rsegs mem0 Hro) Hrel Hsame MU).
    assert (WM' : wmono rsegs mem0 m1)
      by exact (wmono_rel rsegs mem0 (normalize rsegs mem0) m1 m'' (mem_rel_normalize rsegs mem0 Hro) Hrel Hsame WM).
    assert (Hro1 : ro_agree rsegs m1) by exact (ro_agree_same rsegs mem0 m1 Hro Hsame).
    assert (FR1 : lf_fr B API stk S L0 A0 mem0 md0 L0 A0 m1 md0).
    { eapply (lf_fr_evt B API SEGS AX HGG); [exact FR0 | lia | lia | exact MU' | exact WM' | exact Hro1 |].
      intros x Hx0 NO. left.
      destruct (Z_le_dec (S - 464) x); destruct (Z_lt_dec x S); try lia;
        exfalso; apply NO; cbn [Frame.outside]; (split; [lia | exact I]). }
    pose proof (lf_rw_cells_rel m1 m'' _ _ Hrel CF) as CF1.
    clear MU WM CF.
    assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 0x12d1c) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
    assert (G2 : YK11.getr regs1 2 = Z_to_bv 64 (S - 464)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
    assert (G3 : YK11.getr regs1 3 = YK11.getr regs0 3) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
    assert (G4 : YK11.getr regs1 4 = YK11.getr regs0 4) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
    assert (G9 : YK11.getr regs1 9 = Z_to_bv 64 p) by (rewrite (lf_getr_eqv _ _ _ Hx); exact Hp).
    assert (G10 : YK11.getr regs1 10 = Z_to_bv 64 288) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
    assert (G18 : YK11.getr regs1 18 = Z_to_bv 64 n) by (rewrite (lf_getr_eqv _ _ _ Hx); exact Hn1).
    assert (Hsp1 : spZ regs1 = S - 464) by (unfold spZ; rewrite G2; apply unsigned_lit; lia).
    pose proof FR1 as (HM1 & HW1 & HB1 & HID1 & Hmd1 & Hhigh1 & Himg1 & Hblk1 & Hbyt1 & Hstw1 & Herr1 & Hgd1 & MI1).
    rewrite <- SEGS.
    eapply (SRcf_bind B).
    { replace (Z_to_bv 64 0x14b88) with (Z_to_bv 64 (ms_malloc B)) by (rewrite HMAL; reflexivity).
      apply (MALLOC (mkFP (@fp_regs fx) (@fp_csr fx)) L0 A0 regs1 m1 md0 288 b).
      - split; [exact HM1|]. split; [exact HW1|]. split; [exact HB1|].
        split; [rewrite G1; apply ret_ok_even; reflexivity|].
        split; [rewrite Hsp1; replace (S - 464) with (S + (-29) * 16) by lia; rewrite Z.mod_add by lia; exact Hal|].
        split; [rewrite Hsp1; unfold ALLOC_STACK; lia|]. split; [rewrite Hsp1; lia|].
        split; [intros a Ha; apply Hstw1; rewrite Hsp1 in Ha; unfold ALLOC_STACK in Ha; lia|].
        split; [rewrite G4; exact Htp|]. split; [exact Herr1|].
        intros E. rewrite HID in E. discriminate.
      - rewrite SEGS. exact Hro1.
      - exact G10.
      - exact Hres.
      - exact (lf_room0_ag A0 b 288 Hres Hroom ltac:(unfold LLVM_REQ; lia)). }
    intros c2 (L2 & A2 & regs2 & mem2 & md2 & res & -> & Hpost & G10' & Hres0 & Hal16 & (Hf1 & Hf2 & Hf3)
      & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub & Hidt & Hlen & Hres2).
    pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
    destruct (mr_model B _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
    rewrite SEGS in Hro2.
    assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
    { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR1 | lia | lia | exact Hpost
        | rewrite Hsp1; unfold ALLOC_STACK; lia | rewrite Hsp1; lia | | | | | | exact Hidt | | ].
      - intros a Ha. exfalso. exact Ha.
      - intros a Ha. right. intros Hf. exact Hf.
      - intros a Hf Ha. exfalso. exact Hf.
      - intros a0 k0 Hin. rewrite Eb2 in Hin. rewrite Eb1.
        apply in_app_or in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin | right; right; exact Hin].
      - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i Hin (fun H => H) Hi).
      - exact Hro2.
      - exact Hgk. }
    assert (MINE : lf_mine L0 A0 L2 A2 res 288).
    { split; [rewrite Eb1; apply in_or_app; right; left; reflexivity|]. split; [lia|].
      intros a j Hin. rewrite Eb2 in Hin.
      pose proof (mr_blocks_disjoint B (aa_MR API) (aa_laws API) L2 A2 mem2 md2 HM2) as HP. rewrite Eb1 in HP.
      destruct (pairwise_app_mid _ b1 (res, 288) b2 (a, j) HP Hin) as [H|H];
        unfold ranges_disjoint in H; cbn [fst snd] in H; lia. }
    assert (CF2 : rw_cells rsegs mem2 (S - 464)
      [CB 344 j1; C8 (reg_get regs0 10); C8 (reg_get regs0 11); C8 (reg_get regs0 27); C8 (reg_get regs0 26);
       C8 (reg_get regs0 25); C8 (reg_get regs0 24); C8 (reg_get regs0 23); C8 (reg_get regs0 22);
       C8 (reg_get regs0 21); C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18);
       C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)]).
    { apply (lf_rw_cells_frame m1); [exact CF1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      rewrite <- SEGS. apply Hfr2.
      - left. lia.
      - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM1 Ho). lia.
      - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
      - unfold scratch_k. rewrite Hsp1. unfold ALLOC_STACK.
        intros [Hs|Hs]; [lia | pose proof (lf_errno_low B ERRNO_LOW a Hs); lia].
      - intros Hf. exact Hf. }
    change (reg_get regs0 10) with (YK11.getr regs0 10) in CF2. rewrite Hp in CF2.
    change (reg_get regs0 11) with (YK11.getr regs0 11) in CF2. rewrite Hn1 in CF2.
    pose proof FR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw2 & _).
    assert (CFn : rw_cells rsegs (normalize rsegs mem2) (S - 464)
      [CB 344 j1; C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 (reg_get regs0 27); C8 (reg_get regs0 26);
       C8 (reg_get regs0 25); C8 (reg_get regs0 24); C8 (reg_get regs0 23); C8 (reg_get regs0 22);
       C8 (reg_get regs0 21); C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18);
       C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)]).
    { apply (lf_rw_cells_norm B); [exact SEGS | exact Hro2 | | exact CF2].
      intros x Hx' Himg. pose proof (lf_in_img_top B _ SEGS Himg). lia. }
    assert (STn : Frame.stk rsegs (normalize rsegs mem2) (S - stk) (S - 464)).
    { apply lf_stk; [lia | lia |]. intros a Ha. unfold YP09.writable_at.
      assert (Hni : ~ in_img B a) by (intros Hi'; pose proof (lf_in_img_top B a SEGS Hi'); lia).
      rewrite (wview_rel_rw rsegs mem2 (normalize rsegs mem2) _ (mem_rel_normalize rsegs mem2 Hro2)
                 (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
      rewrite <- SEGS. exact (Hstw2 a ltac:(lia)). }
    assert (STr : Frame.stk rsegs (normalize rsegs mem2) res (res + 288)).
    { apply (en_stk_out B); [exact SEGS | lia | lia |]. intros a Ha.
      destruct (lf_mine_bytes B API AX L0 A0 L2 A2 mem2 md2 res 288 a HM2 MINE Ha) as (N1 & N2 & N3 & N4 & N5).
      split; [exact N2|]. unfold YP09.writable_at.
      rewrite (wview_rel_rw rsegs mem2 (normalize rsegs mem2) _ (mem_rel_normalize rsegs mem2 Hro2)
                 (lf_ro_addr_out B a SEGS N2 ltac:(lia))).
      apply YL01.present_writable. exact N4. }
    destruct (stk_carve rsegs _ res (res + 288) 288 STr ltac:(lia)) as [_ [junk HRj]].
    change (Z.of_nat 288) with 288 in HRj. replace (res + 288 - 288) with res in HRj by lia.
    assert (HPAY : exists vb, n = 0 \/
      (1 <= n /\ ov_read_bytes rsegs (normalize rsegs mem2) (Z_to_bv 64 p) 1 = Some [vb] /\ 1 <= p /\
       p + 1 <= S - stk /\ (p + 1 <= res \/ res + 288 <= p))).
    { destruct (Z.eq_dec n 0) as [E0|E0]; [exists (Z_to_bv 8 0); left; exact E0|].
      destruct (llvm_payload_read_cf B API stk empty L0 A0 regs0 mem0 md0 ra p n b L2 A2 mem2 md2 p CTX FR2
        ltac:(lia)) as [v Hv].
      destruct Hpl as [[E0' _] | [_ (q & Hq & Hqp)]]; [lia|].
      destruct (mr_blocks B _ (aa_laws API) L0 A0 mem0 md0 q n 0 HM Hq ltac:(lia)) as (_ & Hq1 & Hq2 & _).
      rewrite Hqp in Hq1, Hq2.
      assert (Hpb : In (p, n) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
      pose proof MINE as (_ & _ & Hdis). specialize (Hdis p n Hpb).
      exists v. right. split; [lia|]. split.
      { rewrite <- (ov_read_rel rsegs mem2 (normalize rsegs mem2) _ _ (mem_rel_normalize rsegs mem2 Hro2)). exact Hv. }
      split; [lia|]. split; [lia|]. lia. }
    destruct HPAY as [vb HPAY].
    assert (G2' : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (S - 464))
      by (rewrite (Hrp 2 ltac:(unfold callee_saved; lia)); exact G2).
    assert (G3' : YK11.getr regs2 (Z_to_bv 5 3) = YK11.getr regs0 3)
      by (rewrite (Hrp 3 ltac:(unfold callee_saved; lia)); exact G3).
    assert (G4' : YK11.getr regs2 (Z_to_bv 5 4) = YK11.getr regs0 4)
      by (rewrite (Hrp 4 ltac:(unfold callee_saved; lia)); exact G4).
    assert (G9' : YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 p)
      by (rewrite (Hrp 9 ltac:(unfold callee_saved; lia)); exact G9).
    assert (G18' : YK11.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 n)
      by (rewrite (Hrp 18 ltac:(unfold callee_saved; lia)); exact G18).
    rewrite G1, SEGS.
    eapply ((llvm_run_norm_cf B ltac:(segs_tac)) (mkFP (@fp_regs fx) (@fp_csr fx)) regs2 (Z_to_bv 64 0x12d1c) mem2 md2);
      [exact Hh2 | exact Hl2 | exact Hro2 | | |].
    + unfold Regs6ss.mkR_of.
      eapply (en_body_evt INIT CHECK) with (spv := S - 464) (r := res) (p := p) (n := n) (lo := S - stk) (hi := S)
        (junk := junk) (vb := vb);
        [ exact G2' | exact G10' | exact G9' | exact G18' | exact CFn | exact HRj | exact HPAY
        | exact (mem_inv_normalize rsegs mem2) | exact STn | lia | lia | lia | lia | lia | exact Hal16 | lia | lia ].
    + intros ms HQ. unfold en_Q in HQ.
      destruct HQ as (x1 & x5 & x6 & x7 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
        & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & pc & mq & fab & ip & inn & bs
        & j0 & j1' & -> & _).
      do 5 eexists. reflexivity.
    + intros R F pc' fc m0' HQ regs3 m3 Hx3 Hrel3 Hsame3. unfold en_Q in HQ.
      destruct HQ as (x1 & x5 & x6 & x7 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
        & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & pc & mq & fab & ip & inn & bs
        & j0 & j1' & HE & MU3 & WM3 & HR3 & INV3 & HFB3 & Hip & Hipn & HJX).
      injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
      assert (MU3' : munch [(S - stk, S); (res, res + 288)] mem2 m3)
        by exact (munch_rel rsegs _ mem2 (normalize rsegs mem2) m3 mq (mem_rel_normalize rsegs mem2 Hro2)
                    Hrel3 Hsame3 MU3).
      assert (WM3' : wmono rsegs mem2 m3)
        by exact (wmono_rel rsegs mem2 (normalize rsegs mem2) m3 mq (mem_rel_normalize rsegs mem2 Hro2)
                    Hrel3 Hsame3 WM3).
      assert (Hro3 : ro_agree rsegs m3) by exact (ro_agree_same rsegs mem2 m3 Hro2 Hsame3).
      assert (FR3 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 m3 md2).
      { eapply (lf_fr_evt B API SEGS AX HGG); [exact FR2 | lia | lia | exact MU3' | exact WM3' | exact Hro3 |].
        intros x Hx0 NO.
        destruct (Z_le_dec (S - stk) x); destruct (Z_lt_dec x S); try (left; lia).
        all: right; exists res, 288; split; [exact MINE|];
          destruct (Z_le_dec res x); destruct (Z_lt_dec x (res + 288)); try lia;
          exfalso; apply NO; cbn [Frame.outside]; repeat split; lia. }
      pose proof (lf_rw_cells_rel m3 mq _ _ Hrel3 HR3) as HR4.
      apply (SRcf_ret B).
      destruct HJX as [(Epc & Hinn & E10 & E18 & E22 & E23 & E24 & E25 & E26 & E27 & HF3) | (Epc & HF3)]; subst pc;
        pose proof (lf_rw_cells_rel m3 mq _ _ Hrel3 HF3) as HF4.
      * left. eexists. exists regs3, m3, md2, L2, A2, res, fab, ip, inn, bs, j0, j1',
          (cells_bytes [C8 (Z_to_bv 64 inn)]).
        split; [rewrite SEGS; reflexivity|].
        split; [exact Hfrm|].
        split.
        { unfold llvm_regs_base. rewrite !(lf_getr_eqv _ _ _ Hx3).
          split; [exact G2'|]. split; [exact G3'|]. split; [exact G4'|]. split; [reflexivity|].
          split; [exact E22|]. split; [exact E23|]. split; [exact E24|]. split; [exact E25|].
          split; [exact E26 | exact E27]. }
        split; [rewrite (lf_getr_eqv _ _ _ Hx3); exact E10|].
        split; [rewrite (lf_getr_eqv _ _ _ Hx3); exact E18|].
        split; [exact (rw_cells_merge rsegs m3 (S - 464)
          [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); CB 320 j1'; C8 (Z_to_bv 64 ip)]
          [C8 (Z_to_bv 64 inn)] _ HF4)|].
        split; [lia|]. split; [lia|]. split; [exact Hip|]. split; [exact Hipn|].
        split; [exact HR4|]. split; [exact INV3|]. split; [exact HFB3|].
        split; [split; [exact FR3 | split; [exact MINE | exact Hres2]] | cbn; lia].
      * right. eexists. exists regs3, m3, md2, L2, A2, res,
          (cells_bytes [CB 344 j1'; C8 (Z_to_bv 64 ip); C8 (Z_to_bv 64 inn)]).
        split; [rewrite SEGS; reflexivity|].
        split; [exact Hfrm|].
        rewrite !(lf_getr_eqv _ _ _ Hx3).
        split; [exact G2'|]. split; [exact G3'|]. split; [exact G4'|]. split; [reflexivity|].
        split; [exact (rw_cells_merge rsegs m3 (S - 464) [] [CB 344 j1'; C8 (Z_to_bv 64 ip); C8 (Z_to_bv 64 inn)] _ HF4)|].
        split; [split; [exact FR3 | split; [exact MINE | exact Hres2]] | lia].
Qed.

End E.
