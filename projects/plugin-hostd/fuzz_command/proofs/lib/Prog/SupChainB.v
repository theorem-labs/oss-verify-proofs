From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0 AllocSlots.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel printf_facts_c arg_i RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM06 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import arg_i_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import xstrdup_c rec_calls_free_c answer_c rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecInv RecInvP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecStep RecGlue RecAnsB RecTail RecStub.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import SupChainA.
Import ListNotations.
Open Scope Z_scope.

Lemma schb_pres_step : forall R2 R3 M3,
  Regs6ss.xregs_eqv M3 R3 ->
  (forall r, callee_saved r -> reg_get M3 (Z_to_bv 5 r) = reg_get R2 (Z_to_bv 5 r)) ->
  regs_preserved R2 R3.
Proof.
  intros R2 R3 M3 X3 K r Hr. pose proof (RecStub.getr_nz r Hr) as NZ.
  rewrite (getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ. exact (K r Hr).
Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis RCF : rec_calls_free_contract B API.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis SLACK : block_slack_present B API.
Hypothesis XSD : xstrdup_contract B API.

Lemma sch_copy : forall K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lp z x regs_c (P : config -> Prop),
  sinvx B API K S L A mem md O Lc Ac mc mdc (rec_record Rp fn As) Oc bc (lp, z) ->
  m_halted mdc = None -> m_vm_lazy mdc = [] ->
  length As = 2%nat ->
  bytes_at rsegs mc (rec_entry G_REC REC_SC Rp + 4) (le4 (Z_to_bv 64 2)) ->
  bytes_at rsegs mc lp (x ++ [Z_to_bv 8 0]) -> no0 x -> Z.of_nat (length x) <= LMAX ->
  Z.of_nat (length x) + 1 <= z ->
  room_slots (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length x) + 1)) (Z.of_nat (length x) + 1) ->
  spZ regs_c mod 16 = 0 -> S - K <= spZ regs_c - XSTRDUP_K -> spZ regs_c <= S ->
  getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
  getr regs_c 8 = Z_to_bv 64 (rec_entry G_REC REC_SC Rp) -> getr regs_c 19 = Z_to_bv 64 lp ->
  (forall L' A' regs' m' md' p,
     sinvx B API K S L A mem md O L' A' m' md' (rec_record Rp fn (As ++ [x]))
       (Oc ++ [(p, Z.of_nat (length x) + 1)]) bc (lp, z) ->
     st_init_done A' = true ->
     sb_shift bc A A' = sb_malloc (sb_shift bc A Ac) (Z.of_nat (length x) + 1) ->
     regs_preserved regs_c regs' ->
     getr regs' 1 = Z_to_bv 64 0x16c70 -> getr regs' 10 = Z_to_bv 64 lp ->
     (forall a, spZ regs_c <= a < S ->
        mbyte rsegs m' a = mbyte rsegs mc a /\ (writable_at rsegs mc a -> writable_at rsegs m' a)) ->
     SR rsegs (mkCfg (mkst regs' (Z_to_bv 64 0x188cc) m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 0x16c3c) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS GOWN AX ERRNO_LOW GOTG GRD GFACT SLACK XSD.
  intros K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc lp z x regs_c P SI Hh Hl HAs HN BX N0 LX HZ ROOM
    HAL HLO HHI E4 E8 E19 KC.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _).
  pose proof RJ as (HM & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  assert (ER : REC_SC <= rec_entry G_REC REC_SC Rp /\ rec_entry G_REC REC_SC Rp + CALL_SIZE <= G_REC + REC_SIZE).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls Rp)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold REC_SC, G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. lia. }
  set (e := rec_entry G_REC REC_SC Rp) in *.
  assert (EE : e = rec_entry G_REC REC_SC Rp) by reflexivity.
  assert (EB : 0x33d10 <= e /\ e + 56 <= 0x34108) by (unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE in ER; lia).
  assert (R8' : reg_get regs_c 8 = Z_to_bv 64 e) by exact E8.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R8'. eapply sch_cp. exact HN. }
  intros ms1 (can1 & Q1 & EQ1). cbv beta in Q1. subst can1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (P1 : regs_preserved regs_c R1).
  { apply (schb_pres_step regs_c R1 _ X1). intros rr Hrr. unfold callee_saved in Hrr.
    assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
                 rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    clear Hrr.
    repeat (destruct CC as [CC|CC]; [subst rr; simp_regs; first [reflexivity | symmetry; exact R8']|]).
    subst rr; simp_regs; reflexivity. }
  assert (E1 : getr R1 1 = Z_to_bv 64 0x16c50) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E10 : getr R1 10 = Z_to_bv 64 lp) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; exact E19).
  assert (SP1 : spZ R1 = spZ regs_c) by (unfold spZ; f_equal; exact (P1 2 ltac:(unfold callee_saved; lia))).
  apply (sch_xsd B API SEGS ERRNO_LOW GFACT GOWN AX GOTG GRD SLACK XSD K S L A mem md O Lc Ac mc mdc
           (rec_record Rp fn As) Oc bc lp z R1 x P SI).
  - apply (call_pre_k_of_rjr B _ K S rec_area _ L A mem md Lc Ac mc mdc XSTRDUP_K R1 RJ).
    + rewrite E1. apply bv_eq. vm_compute. reflexivity.
    + rewrite SP1. exact HAL.
    + unfold XSTRDUP_K, ALLOC_STACK. lia.
    + rewrite SP1. exact HLO.
    + rewrite SP1. exact HHI.
    + exact (eq_trans (P1 4 ltac:(unfold callee_saved; lia)) E4).
  - rewrite SP1. exact HLO.
  - rewrite SP1. exact HHI.
  - exact E10.
  - exact BX.
  - exact N0.
  - exact LX.
  - exact HZ.
  - exact ROOM.
  - intros L2 A2 R2 m2 md2 p POST2 A0' NZ FB2 BLK2 UB2 BK2 RGN2 BYT2 INI2 RS2 RA2 F182.
    pose proof POST2 as (PM2 & _ & _ & _ & _ & RP2 & _ & PF2 & _).
    pose proof FB2 as (FBa & FBb & FBc).
    assert (P2 : regs_preserved regs_c R2) by (intros r Hr; rewrite (RP2 r Hr); exact (P1 r Hr)).
    assert (R2_8' : reg_get R2 8 = Z_to_bv 64 e) by exact (eq_trans (P2 8 ltac:(unfold callee_saved; lia)) E8).
    assert (R2_10 : reg_get R2 10 = Z_to_bv 64 p) by exact A0'.
    assert (POST2' : call_post_k B (aa_MR API) XSTRDUP_K Lc Ac R1 mc mdc
                       (fun a => p <= a < p + (Z.of_nat (length x) + 1)) L2 A2 R2 m2 md2).
    { pose proof POST2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
      split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
      split; [exact Q6|]. split; [exact Q7|]. split; [|split; [exact Q9 | exact Q10]].
      intros a H1 H2 H3 H4 H5. apply Q8; [exact H1 | exact H2 | exact H3 | exact H4 | cbv beta in H5 |- *; lia]. }
    rewrite SEGS in PF2.
    assert (GK : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> mbyte rsegs m2 a = mbyte rsegs mc a).
    { intros a Ha. destruct (GFACT a (glob_in a Ha)) as (Gi & _ & _ & Ge).
      refine (proj1 (PF2 a (or_intror Gi) (GOWN Lc Ac mc mdc a HM (glob_in a Ha))
                      (GOWN L2 A2 m2 md2 a PM2 (glob_in a Ha)) _ _)).
      - unfold scratch_k. rewrite SP1. unfold XSTRDUP_K, ALLOC_STACK in *.
        intros [H|H]; [unfold GLOB_LO, GLOB_N in Ha; lia | exact (Ge H)].
      - cbv beta. intros H. apply (FBc (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Gi. }
    assert (NA2 : bytes_at rsegs m2 (e + 4) (le4 (Z_to_bv 64 2))).
    { apply (bytes_at_transfer rsegs mc); [exact HN|]. intros i Hi. rewrite length_le4 in Hi.
      apply GK. unfold GLOB_LO, GLOB_N; lia. }
    destruct (mr_model B _ LAWS L2 A2 m2 md2 PM2) as (Hh2 & Hl2 & _).
    rewrite E1.
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R2_8', R2_10.
      eapply sch_st; [exact NA2 | apply glob_wr_at; unfold GLOB_LO, GLOB_N; lia | lia | lia | lia]. }
    intros ms3 (can3 & Q3 & EQ3). cbv beta in Q3.
    destruct Q3 as (a1' & a2' & m3 & -> & MU3 & WM3 & B3 & B4).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    assert (P3 : regs_preserved regs_c R3).
    { assert (P23 : regs_preserved R2 R3).
      { apply (schb_pres_step R2 R3 _ X3). intros rr Hrr. unfold callee_saved in Hrr.
        assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
                     rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
        clear Hrr.
        repeat (destruct CC as [CC|CC]; [subst rr; simp_regs; first [reflexivity | symmetry; exact R2_8']|]).
        subst rr; simp_regs; reflexivity. }
      intros r Hr. rewrite (P23 r Hr). exact (P2 r Hr). }
    assert (E3_1 : getr R3 1 = Z_to_bv 64 0x16c70)
      by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
    assert (E3_10 : getr R3 10 = Z_to_bv 64 lp).
    { rewrite (getr_of_eqv _ _ 10 X3 eq_refl). simp_regs.
      exact (eq_trans (P2 19 ltac:(unfold callee_saved; lia)) E19). }
    assert (BN3 : bytes_at rsegs m3 (rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS)
                    (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1)))).
    { rewrite HAs. exact B3. }
    assert (BS3 : bytes_at rsegs m3 (rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As))
                    (le8 (Z_to_bv 64 p))).
    { rewrite <- EE, HAs. replace (e + CALL_OFF_ARGS + 8 * Z.of_nat 2) with (e + 24)
        by (unfold CALL_OFF_ARGS; lia). exact B4. }
    assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ outside [(e + 4, e + 8); (e + 24, e + 32)] a ->
              rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS + 4 \/
              rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
                rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8).
    { intros a Ra Hm. cbn [outside] in Hm. rewrite <- EE, HAs. unfold CALL_OFF_NARGS, CALL_OFF_ARGS. lia. }
    pose proof (sinvx_sarg B API SEGS ERRNO_LOW GFACT GOWN AX K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc (lp, z)
                  XSTRDUP_K R1 L2 A2 R2 m2 md2 m3 [(e + 4, e + 8); (e + 24, e + 32)] x p (Z.of_nat (length x) + 1)
                  SI ltac:(rewrite HAs; lia) ltac:(rewrite SP1; exact HLO) ltac:(rewrite SP1; exact HHI)
                  POST2' MU3 WM3 HW NZ FB2 BLK2 UB2 BK2 RGN2 BN3 BS3 BYT2 N0 LX ltac:(unfold LMAX in *; lia)
                  INI2 RS2 RA2 F182) as SI3.
    assert (SBE : sb_shift bc A A2 = sb_malloc (sb_shift bc A Ac) (Z.of_nat (length x) + 1)).
    { destruct BLK2 as (bl1 & bl2 & EB1 & EB2).
      rewrite <- (sb_shift_trans bc A Ac A2).
      rewrite <- (sb_shift_add (sb_shift bc A Ac) Lc Ac L2 A2 bl1 bl2 p _ EB1 EB2). reflexivity. }
    assert (STK : forall a, spZ regs_c <= a < S ->
              mbyte rsegs m3 a = mbyte rsegs mc a /\ (writable_at rsegs mc a -> writable_at rsegs m3 a)).
    { intros a Ha. unfold XSTRDUP_K, ALLOC_STACK in *.
      destruct (post_k_keep_hi B API SEGS ERRNO_LOW (8192 + 32) Lc Ac R1 mc mdc _ L2 A2 R2 m2 md2 a HM POST2
                  ltac:(lia) ltac:(rewrite SP1; lia) ltac:(intros H; cbv beta in H; lia)) as [K1 K2].
      assert (OW : outside [(e + 4, e + 8); (e + 24, e + 32)] a) by (cbn [outside]; repeat split; lia).
      split.
      - rewrite (munch_mbyte rsegs _ m2 m3 a MU3 ltac:(lia) OW). exact K1.
      - intros W0. pose proof (proj1 K2 W0) as W1. unfold writable_at in W1 |- *. exact (WM3 _ W1). }
    exact (KC L2 A2 R3 m3 md2 p SI3 INI2 SBE P3 E3_1 E3_10 STK).
Qed.

End G.
