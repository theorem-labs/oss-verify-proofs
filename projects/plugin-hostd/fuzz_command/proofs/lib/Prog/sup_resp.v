From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts printf_facts_c snprintf_c RecAns.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition sr_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo code : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' slack,
    ms' = MS (mkR (Z_to_bv 64 0x158f0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 s1
                  (Z_to_bv 64 (bv_unsigned sp + -40)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x15780) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k)
    /\ length slack = (31 - length (resp code))%nat
    /\ bytes_at rsegs m' (bv_unsigned sp + -40)%Z (resp code ++ Z_to_bv 8 0 :: slack)
    /\ rw_cells rsegs m' (bv_unsigned sp + -8)%Z [C8 ra].

Lemma sr_run1 : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo code : Z) (canary : word),
  (-2^31 <= code < 2^31)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 + SNPRINTF_K <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  (bv_unsigned sp < 2^63)%Z ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> (bv_unsigned sp <= TASK_SIZE)%Z ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (sr_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo code m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x158c8) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo code canary HC ST LO IE S63 FRM MI TM HTS GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 8%nat ST.
  rename FR into FRS.
  carve_frame 32%nat ST.
  carve_frame 8%nat ST.
  clear FR0.
  do 8 step.
  try rename m0 into m1.
  try replace (bv_unsigned sp + -48 + 8)%Z with (bv_unsigned sp + -40)%Z by ring.
  pose proof (resp_len code HC) as RL.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m1 (bv_unsigned sp + -40)%Z junk0).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary RESP_FMT RESP_PS
              [AInt code] (RESP_HEAD ++ pf_dec code) junk0).
    - rewrite unsigned_lit by lia. apply resp_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, RESP_FMT. cbn [length]. lia.
    - exact resp_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HC | apply lit_mod32].
    - exact (resp_text code).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. apply pf_img_free_hi. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact MI.
    - exact (task_mem_munch1 m m1 lo (bv_unsigned sp) TM MU HTS).
    - exact GG.
    - exact GW. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m2
    & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK & ST2 & BT).
  rewrite !unsigned_lit in MU2, BT by lia.
  change (Z.to_nat (32 - 1)) with 31%nat in BT, MU2.
  rewrite (firstn_all2 (n := 31%nat)) in MU2, BT by lia.
  replace (ret_pc (Z_to_bv 64 88296)) with (Z_to_bv 64 88296) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (JL : length junk0 = 32%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  assert (FRS2 : rw_cells rsegs m2 (bv_unsigned sp + -8)%Z [C8 ra]).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FRS MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | split; [lia | exact I]]. }
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (RESP_HEAD ++ pf_dec code))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + -40 + Z.of_nat (S (length (RESP_HEAD ++ pf_dec code))))%Z
                   (skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0)).
  { apply (bytes_at_transport rsegs _ m1 m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes ((RESP_HEAD ++ pf_dec code) ++ [0%Z]) = resp code ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (RESP_HEAD ++ pf_dec code)) with
      (pf_bytes (RESP_HEAD ++ pf_dec code)). rewrite pf_resp by exact HC. reflexivity. }
  assert (LR : length (resp code) = length (RESP_HEAD ++ pf_dec code)).
  { rewrite <- (pf_resp code HC). unfold pf_bytes. apply length_map. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp + -40)%Z
                  (resp code ++ Z_to_bv 8 0 :: skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0)).
  { replace (resp code ++ Z_to_bv 8 0 :: skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0) with
      ((resp code ++ [Z_to_bv 8 0]) ++ skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, LR. cbn [length].
    replace (Z.of_nat (length (RESP_HEAD ++ pf_dec code) + 1))
      with (Z.of_nat (S (length (RESP_HEAD ++ pf_dec code)))) by lia. exact BJT2. }
  clear BT BJT BJT2 BJ BJL FR.
  do 2 step.
  try replace (bv_unsigned sp + -48 + 8)%Z with (bv_unsigned sp + -40)%Z by ring.
  apply evt_done. unfold sr_mid.
  do 17 eexists. exists (skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0). split; [reflexivity|].
  split.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  split; [eapply wmono_trans; eassumption|].
  split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, LR; lia|].
  split; [exact BUF | exact FRS2].
Qed.

Lemma sr_run3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (rav : word),
  rw_cells rsegs m (bv_unsigned sp + 40)%Z [C8 rav] -> (bv_unsigned sp + 48 < 2 ^ 64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x158f0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m rav FR HB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 3 step. apply evt_done. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel RecInv RecInvP RecKindB RecAnsB
  xstrdup_c sup_resp_c.
Local Open Scope Z_scope.

Ltac sr_pres X5 X1 G2 R1 :=
  match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X5 eq_refl); simp_regs;
    transitivity (getr R1 (Z_to_bv 5 k)); [exact (G2 k ltac:(unfold callee_saved; lia))|];
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X1 eq_refl); simp_regs; reflexivity
  end.

Lemma sr_in_fG : forall a, 0x33d10 <= a < 0x33d10 + 1020 -> in_globals frame_G a.
Proof. intros a Ha. exists 0x33d10, 1020. split; [left; reflexivity | exact Ha]. Qed.

Section SR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GUARDG : ms_guard B = 0x54450.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis FGI : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis FGO : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis SNP : snprintf_contract.
Hypothesis XSTRDUP : forall fx' : YK11.FPState, @xstrdup_contract fx' rc B API.

Theorem sup_resp_holds : sup_resp_contract B API.
Proof using SEGS ERRNO_LOW GOTG GUARDG AX FGI FGO SNP XSTRDUP.
  unfold sup_resp_contract.
  intros L A regs mem md code b PRE A0 HC RA FZ F18 RES ROOM.
  destruct PRE as [PRE HTS].
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  assert (KV : SUP_RESP_K = 8272) by reflexivity.
  assert (XK : XSTRDUP_K = 8224) by reflexivity.
  rewrite KV in PRE |- *.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (resp_length code HC) as RL.
  rewrite SEGS in RA, HWS, HERR, F18.
  pose proof F18 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs mem snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs mem snprintf_c.GUARD (Mem.le8 canary)).
  { destruct GW as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (ST0 : stk rsegs (normalize_cj rsegs mem) (bv_unsigned sp - 8272) (bv_unsigned sp))
    by (apply stk_normalize_cj; [lia | exact HTS | intros a Ha; apply HWS; lia]).
  pose proof (bytes_at_normalize_cj_low rsegs mem snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RA
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs mem snprintf_c.GUARD (Mem.le8 canary) RA
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 code) by exact A0. rewrite R10.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA |].
    eapply (sr_run1 SNP) with (lo := bv_unsigned sp - 8272) (canary := canary);
      [exact HC | exact ST0 | unfold SNPRINTF_K; lia | lia | lia | exact FZ
      | exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mem))
      | exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs mem)) | exact HTS
      | exact GGn | exact GWn]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m1n
    & slack & -> & MU1n & WM1n & MI1n & FRM1 & FK1 & SL & BUF1n & FRS1n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
  pose proof (ro_agree_same_cj rsegs _ _ RA RO1) as RA1.
  pose proof (rw_cells_rel_cj rsegs _ _ _ _ MR1r FRS1n) as FRS1.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR1r BUF1n) as BUF1.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ1) as (R1 & -> & X1).
  clear MU1n WM1n MI1n FRS1n BUF1n EQ1 MR1r.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x158f0) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (bv_unsigned sp + -40))
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8272 <= a < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 8272, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & H4 & Hc & _).
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  assert (BRNG : forall q k, In (q, k) (blocks L A) -> 4096 <= q /\ q + k <= alloc_ceiling).
  { intros q k Hq. unfold blocks in Hq. apply in_map_iff in Hq as ([p k'] & E & Hp). cbn in E. injection E as <- <-.
    exact (mr_blocks_range B _ LAWS L A mem md p k' HMR Hp). }
  rewrite <- SEGS.
  eapply SR_bind.
  { eapply (XSTRDUP (mkFP F1 fc1) L A R1 m1 md (bv_unsigned sp - 40) (resp code) slack b).
    - rewrite XK. split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
      split; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP1; replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP1; lia|].
      split; [rewrite SP1; lia|].
      split; [intros a Ha; rewrite SP1 in Ha; rewrite SEGS; apply WM1; apply HWS; lia|].
      split; [rewrite E1_4; exact HTP|].
      split; [intros a Ha; rewrite SEGS; apply WM1; apply HERR; exact Ha|].
      intros HI. specialize (HAUX HI). rewrite SP1.
      destruct HAUX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
      exists av, ar.
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W1]. intros k Hk.
        assert (SO : owned B L A (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
        destruct (owned_low B _ LAWS _ _ _ _ _ HMR SO). split; [lia | apply OUT1; lia]. }
      split.
      { intros k Hk. eapply word_mem_munch; [exact MU1 | | exact (W2 k Hk)]. intros k' Hk'.
        split; [lia | apply OUT1; lia]. }
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W3]. intros k Hk. split; [lia | apply OUT1; lia]. }
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W4]. intros k Hk. split; [lia | apply OUT1; lia]. }
      lia.
    - rewrite E1_10. reflexivity.
    - rewrite SEGS. exact BUF1.
    - exact (resp_no0 code).
    - unfold LMAX. lia.
    - rewrite SL. pose proof (Z.mod_pos_bound (- (bv_unsigned sp - 40 + Z.of_nat (length (resp code)) + 1)) 8
        ltac:(lia)). lia.
    - right. rewrite SP1. lia.
    - left. rewrite SP1. lia.
    - exact RES.
    - exact ROOM.
    - rewrite SEGS. exact RA1. }
  intros c2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & p & -> & POST2 & A0' & NZ & AL & FRESH & (b1 & b2 & BL2 & BL1)
    & KEPT & UB & BP & BS & RA2 & GK2 & INIT2 & REG2 & RES2).
  destruct POST2 as (HMR2 & HWF2 & HBD2 & HLE2 & HSTAB2 & HP2 & HVM2 & HFR2 & HBLKS2 & HSCR2).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & Hmat2).
  pose proof FRESH as (FR_lo & FR_hi & FR_img).
  assert (G2 : forall r, callee_saved r -> reg_get R2 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r)).
  { intros r Hr. rewrite <- (HP2 r Hr). unfold getr.
    assert (NZr : bv_eqb (Z_to_bv 5 r) 0 = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 5) with 32. unfold callee_saved in Hr. rewrite Z.mod_small by lia.
      change (bv_unsigned 0) with 0. lia. }
    rewrite NZr. reflexivity. }
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by exact (eq_trans (G2 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (HF12 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8272 <= a < bv_unsigned sp - 48) ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha Hs.
    apply HFR2; [left; exact Ha | intro Ho; destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho); lia
      | intro Ho; destruct (owned_low B _ LAWS _ _ _ _ _ HMR2 Ho); lia
      | unfold scratch_k; rewrite SP1, XK; intros [H|H]; lia |].
    cbn beta. lia. }
  assert (FRS2 : rw_cells rsegs m2 (bv_unsigned sp + -8) [C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FRS1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
    destruct (HF12 (bv_unsigned sp + -8 + i) ltac:(lia) ltac:(lia)) as [E12 W12].
    split; [exact E12 | tauto]. }
  assert (GK : forall i, 0 <= i < 8 ->
     mbyte (ms_segs B) m2 (ms_got_guard B + i) = mbyte (ms_segs B) mem (ms_got_guard B + i)).
  { intros i Hi. rewrite (GK2 i Hi). rewrite GOTG.
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite E1_1, SEGS.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of. rewrite E2_2.
    eapply sr_run3 with (rav := reg_get regs 1).
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp + -48 + 40) with (bv_unsigned sp + -8) by ring. exact FRS2.
    - rewrite unsigned_lit by lia. lia. }
  intros ms5 (can5 & Q5 & EQ5). subst can5.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ5) as (R5 & -> & X5). clear EQ5.
  rewrite <- SEGS.
  apply SR_ret. cbv beta zeta.
  exists (mkFP F1 fc1), L2, A2, R5, m2, md2, p.
  split; [rewrite RP; reflexivity|].
  split.
  { unfold fp_kept. cbn [fp_regs fp_csr]. split; [exact FRM1|].
    intros r Hr. apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  split.
  { split; [exact HMR2|]. split; [exact HWF2|]. split; [exact HBD2|].
    split; [exact HLE2|].
    split; [exact HSTAB2|].
    split.
    { intros r Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold callee_saved in Hr; lia).
      destruct C as [C|C].
      { subst r. rewrite (getr_of_eqv _ _ (Z_to_bv 5 2) X5 eq_refl). simp_regs.
        rewrite unsigned_lit by lia. replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by ring.
        exact (Z_to_bv_lit_self sp). }
      repeat (destruct C as [C|C]; [subst r; sr_pres X5 X1 G2 R1|]).
      subst r. sr_pres X5 X1 G2 R1. }
    split; [exact HVM2|].
    split.
    { intros a Hd N1 N2 NS _. unfold scratch_k, spZ in NS. change (getr regs 2) with sp in NS.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct Hd as [Hd|Hd]; [lia | pose proof (in_img_low B SEGS a Hd); lia]).
      assert (NF : ~ (p <= a < p + Z.of_nat (length (resp code)) + 1)).
      { intros Hin. destruct Hd as [Hd|Hd]; [lia|]. apply (FR_img (a - p)); [lia|].
        replace (p + (a - p)) with a by ring. exact Hd. }
      assert (E01 : mbyte (ms_segs B) m1 a = mbyte (ms_segs B) mem a)
        by (apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; [lia | intro H; apply NS; left; exact H]]).
      assert (W01 : writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) m1 a)
        by (apply (munch_writable _ _ _ _ _ MU1); [lia | apply OUT1; [lia | intro H; apply NS; left; exact H]]).
      assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { apply HFR2; [exact Hd | exact N1 | exact N2 | | exact NF].
        unfold scratch_k. rewrite SP1, XK. intros [H|H]; apply NS; [left; lia | right; exact H]. }
      destruct H12 as [E12 W12].
      split; [rewrite E12, E01; reflexivity | tauto]. }
    split.
    { intros p' k i H1 H2 Hi.
      pose proof (mr_blocks_range B _ LAWS L A mem md p' k HMR H1) as Rg.
      rewrite (HBLKS2 p' k i H1 H2 Hi).
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
    destruct Ha as [Ha|Ha]; [|apply HSCR2; right; exact Ha].
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 48)) as [D|D].
    - apply HSCR2. unfold scratch_k. rewrite SP1, XK. left. lia.
    - apply (proj2 (HF12 a ltac:(lia) ltac:(lia))). rewrite SEGS. apply WM1. apply HWS. lia. }
  split; [rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; exact A0'|].
  split; [exact NZ|]. split; [exact AL|]. split; [exact FRESH|].
  split; [exists b1, b2; split; [exact BL2 | exact BL1]|].
  split.
  { intros a k i Hin _ Hi. pose proof (BRNG a k Hin) as Rg.
    rewrite (KEPT a k i Hin ltac:(cbn beta; tauto) Hi).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [exact UB|].
  split; [exact BP|].
  split.
  { intros R O REP. change (fst (sup_resp_m R code)) with R.
    unfold g_rec_rep in REP |- *. eapply (rec_rep_frame _ _ _ L A mem R O L2 A2 m2 REP).
    - intros a Ha.
      assert (GA : in_globals frame_G a)
        by (apply sr_in_fG; unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia).
      destruct (FGI a GA) as (Ii & _ & _ & NEr).
      pose proof (in_img_low B SEGS a Ii) as Hlo.
      assert (E01 : mbyte (ms_segs B) m1 a = mbyte (ms_segs B) mem a)
        by (apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]).
      assert (W01 : writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) m1 a)
        by (apply (munch_writable _ _ _ _ _ MU1); [lia | apply OUT1; lia]).
      assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { apply HFR2; [right; exact Ii | exact (FGO _ _ _ _ a HMR GA) | exact (FGO _ _ _ _ a HMR2 GA) | |].
        - unfold scratch_k. rewrite SP1, XK. intros [H|H]; [lia | exact (NEr H)].
        - cbn beta. intros H. apply (FR_img (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Ii. }
      destruct H12 as [E12 W12].
      split; [rewrite E12, E01; reflexivity | tauto].
    - intros q k i Hin Hi. pose proof (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin) as Hb.
      pose proof (BRNG q k Hb) as Rg.
      rewrite (KEPT q k i Hb ltac:(cbn beta; tauto) Hi).
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia].
    - intros pn Hin. pose proof (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin) as Hb. rewrite BL2.
      rewrite BL1 in Hb. apply in_mid_inv. exact Hb. }
  split; [exact RA2|].
  split.
  { rewrite SEGS. destruct (ax_statics AX L2 A2 m2 md2 HMR2) as (_ & (g & Hg & HGW) & _).
    apply (f18_words_after mem m2 g F18); [| exact Hg | rewrite SEGS, GUARDG in HGW; exact HGW].
    intros i Hi. unfold snprintf_c.GOT_GUARD. rewrite <- GOTG, <- SEGS. exact (GK i Hi). }
  split; [exact INIT2|].
  split; [exact REG2|].
  exact RES2.
Qed.

End SR.
