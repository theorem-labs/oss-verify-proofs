(* ARM 0 (op_read) at the SR level, part 2: the four allocator calls of the arm as LC0Defs' cuts see them.
   - g0_pc_* : each cut predicate fixes its program point (cut_evt's form premise);
   - g0_rg_* : the registers each call cut gives the callee (ra, sp, tp, a0);
   - g0_ad_* : the return adapters. From the call cut at m, the callee-saved registers the callee keeps,
     LFr.lcarry (lkeep ..) m m', LFr.lpost_mem m' and the callee's own facts, the return cut holds of the
     canonical mkR map, so eqv_cl of it holds of the state the step hands back:
       text_buf (kc) 0x13e4c -> c0_ret_kc (0x13e50)    text_buf (ac) 0x13e58 -> c0_ret_ac (0x13e5c)
       free (kind)   0x13f64 -> c0_ret_fk (0x13f68)    free (alias)  0x13f6c -> c0_ret_fa (0x13f70)
     with the free (NULL) forms g0_ad_fk0 / g0_ad_fa0 (the state is the call's, at the return address). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem text_buf_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LGlue LC0Defs LC45Call LG0Lib.
Import ListNotations.
Local Open Scope Z_scope.

(* the four parts of a state an MS equation fixes *)
Ltac g0_eq EQ :=
  let ER := fresh "ER" in let EF := fresh "EF" in let EC := fresh "EC" in let EM := fresh "EM" in
  pose proof (f_equal ms_regs EQ) as ER; pose proof (f_equal ms_fregs EQ) as EF;
  pose proof (f_equal ms_fcsr EQ) as EC; pose proof (f_equal ms_mem EQ) as EM;
  cbn [ms_regs ms_fregs ms_fcsr ms_mem MS] in ER, EF, EC, EM; clear EQ; subst.

(* ==========================================================================
   1. Program points
   ========================================================================== *)

Lemma g0_pc_kc : forall E i gp P N sel kc ac kbs mbs gbs ms, c0_cut_kc E i gp P N sel kc ac kbs mbs gbs ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 TEXT_BUF) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp P N sel kc ac kbs mbs gbs ms H. unfold c0_cut_kc in H. g0_ex H.
  destruct H as (EQ & FC & _). subst ms. do 4 eexists. split; [reflexivity | exact FC].
Qed.

Lemma g0_pc_ac : forall E i gp P N sel kc ac K kbs mbs gbs ms, c0_cut_ac E i gp P N sel kc ac K kbs mbs gbs ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 TEXT_BUF) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp P N sel kc ac K kbs mbs gbs ms H. unfold c0_cut_ac in H. g0_ex H.
  destruct H as (EQ & FC & _). subst ms. do 4 eexists. split; [reflexivity | exact FC].
Qed.

Lemma g0_pc_mid : forall E i gp P N sel kc ac K A op0 want rc kbs mbs gbs ms,
  c0_mid E i gp P N sel kc ac K A op0 want rc kbs mbs gbs ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 C0_MID) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp P N sel kc ac K A op0 want rc kbs mbs gbs ms H. unfold c0_mid in H. g0_ex H.
  destruct H as (EQ & FC & _). subst ms. do 4 eexists. split; [reflexivity | exact FC].
Qed.

Lemma g0_pc_fk : forall E i gp P N sel kc ac K A kbs mbs gbs ms, c0_cut_fk E i gp P N sel kc ac K A kbs mbs gbs ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp P N sel kc ac K A kbs mbs gbs ms H. unfold c0_cut_fk in H. g0_ex H.
  destruct H as (EQ & FC & _). subst ms. do 4 eexists. split; [reflexivity | exact FC].
Qed.

Lemma g0_pc_fa : forall E i gp P N ac A kbs mbs gbs ms, c0_cut_fa E i gp P N ac A kbs mbs gbs ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp P N ac A kbs mbs gbs ms H. unfold c0_cut_fa in H. g0_ex H.
  destruct H as (EQ & FC & _). subst ms. do 4 eexists. split; [reflexivity | exact FC].
Qed.

Lemma g0_pc_lh : forall E i gp ms, lh_ms E i gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 L_LH) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp ms H. unfold lh_ms in H. g0_ex H.
  destruct H as (EQ & FC & _). subst ms. do 4 eexists. split; [reflexivity | exact FC].
Qed.

Lemma g0_pc_ex : forall E gp ms, ex_ms E gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 L_EXIT) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E gp ms H. unfold ex_ms in H. g0_ex H.
  destruct H as (EQ & FC & _). subst ms. do 4 eexists. split; [reflexivity | exact FC].
Qed.

(* ==========================================================================
   2. The registers at each call, and the pure facts the glue reads off the cuts
   ========================================================================== *)

Lemma g0_rg_kc : forall E i gp P N sel kc ac kbs mbs gbs ms, c0_cut_kc E i gp P N sel kc ac kbs mbs gbs ms ->
  getr (ms_regs ms) 1 = Z_to_bv 64 C0_RA_KC /\ getr (ms_regs ms) 2 = Z_to_bv 64 (e_S E - SLOT_FRAME) /\
  getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\ getr (ms_regs ms) 10 = Z_to_bv 64 kc.
Proof.
  intros E i gp P N sel kc ac kbs mbs gbs ms H. unfold c0_cut_kc in H. g0_ex H.
  destruct H as (EQ & _). subst ms. cbn [ms_regs MS]. repeat split; reflexivity.
Qed.

Lemma g0_rg_ac : forall E i gp P N sel kc ac K kbs mbs gbs ms, c0_cut_ac E i gp P N sel kc ac K kbs mbs gbs ms ->
  getr (ms_regs ms) 1 = Z_to_bv 64 C0_RA_AC /\ getr (ms_regs ms) 2 = Z_to_bv 64 (e_S E - SLOT_FRAME) /\
  getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\ getr (ms_regs ms) 10 = Z_to_bv 64 ac.
Proof.
  intros E i gp P N sel kc ac K kbs mbs gbs ms H. unfold c0_cut_ac in H. g0_ex H.
  destruct H as (EQ & _). subst ms. cbn [ms_regs MS]. repeat split; reflexivity.
Qed.

Lemma g0_rg_fk : forall E i gp P N sel kc ac K A kbs mbs gbs ms, c0_cut_fk E i gp P N sel kc ac K A kbs mbs gbs ms ->
  getr (ms_regs ms) 1 = Z_to_bv 64 C0_RA_FK /\ getr (ms_regs ms) 2 = Z_to_bv 64 (e_S E - SLOT_FRAME) /\
  getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\ getr (ms_regs ms) 10 = Z_to_bv 64 K.
Proof.
  intros E i gp P N sel kc ac K A kbs mbs gbs ms H. unfold c0_cut_fk in H. g0_ex H.
  destruct H as (EQ & _). subst ms. cbn [ms_regs MS]. repeat split; reflexivity.
Qed.

Lemma g0_rg_fa : forall E i gp P N ac A kbs mbs gbs ms, c0_cut_fa E i gp P N ac A kbs mbs gbs ms ->
  getr (ms_regs ms) 1 = Z_to_bv 64 C0_RA_FA /\ getr (ms_regs ms) 2 = Z_to_bv 64 (e_S E - SLOT_FRAME) /\
  getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\ getr (ms_regs ms) 10 = Z_to_bv 64 A.
Proof.
  intros E i gp P N ac A kbs mbs gbs ms H. unfold c0_cut_fa in H. g0_ex H.
  destruct H as (EQ & _). subst ms. cbn [ms_regs MS]. repeat split; reflexivity.
Qed.

Lemma g0_kc_caps : forall E i gp P N sel kc ac kbs mbs gbs ms, c0_cut_kc E i gp P N sel kc ac kbs mbs gbs ms ->
  0 <= kc < 40 /\ 0 <= ac < 40.
Proof.
  intros E i gp P N sel kc ac kbs mbs gbs ms H. unfold c0_cut_kc in H. g0_ex H.
  destruct H as (_ & _ & _ & _ & Hkc & Hac & _). exact (conj Hkc Hac).
Qed.

Lemma g0_rkc_K : forall E i gp P N sel kc ac K kbs mbs gbs ms, c0_ret_kc E i gp P N sel kc ac K kbs mbs gbs ms ->
  (kc = 0 -> K = 0) /\ (kc <> 0 -> K <> 0).
Proof.
  intros E i gp P N sel kc ac K kbs mbs gbs ms H. unfold c0_ret_kc in H. g0_ex H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (H0 & H1) & _).
  split; [exact H0 | intros Hk; exact (proj1 (H1 Hk))].
Qed.

Lemma g0_rac_A : forall E i gp P N sel kc ac K A kbs mbs gbs ms,
  c0_ret_ac E i gp P N sel kc ac K A kbs mbs gbs ms -> (ac = 0 -> A = 0) /\ (ac <> 0 -> A <> 0).
Proof.
  intros E i gp P N sel kc ac K A kbs mbs gbs ms H. unfold c0_ret_ac in H. g0_ex H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H0 & H1) & _).
  split; [exact H0 | intros Ha; exact (proj1 (H1 Ha))].
Qed.

(* ==========================================================================
   3. free (NULL): the state of the call, at the return address
   ========================================================================== *)

Lemma g0_ad_fk0 : forall E i gp P N sel kc ac K A kbs mbs gbs R F fc m,
  c0_cut_fk E i gp P N sel kc ac K A kbs mbs gbs (MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs)) ->
  eqv_cl (c0_ret_fk E i gp P N ac A kbs mbs gbs) (MS R F (Z_to_bv 64 C0_RA_FK) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp P N sel kc ac K A kbs mbs gbs R F fc m H. unfold c0_cut_fk in H. g0_ex H.
  destruct H as (EQ & FC & Hi & Hkc & Hac & HN & HKr & HAr & Hop & Hoc & HKA & HK0 & HKb & HA0 & HAb & HF & HB).
  g0_eq EQ. apply c45_eqv_cl_of. unfold c0_ret_fk. do 25 eexists. split; [reflexivity|].
  exact (conj FC (conj Hi (conj Hac (conj HN (conj HAr (conj Hop (conj Hoc (conj HA0 (conj HAb (conj HF HB)))))))))).
Qed.

Lemma g0_ad_fa0 : forall E i gp P N ac A kbs mbs gbs R F fc m,
  c0_cut_fa E i gp P N ac A kbs mbs gbs (MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs)) ->
  eqv_cl (c0_ret_fa E i gp P N kbs mbs gbs) (MS R F (Z_to_bv 64 C0_RA_FA) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp P N ac A kbs mbs gbs R F fc m H. unfold c0_cut_fa in H. g0_ex H.
  destruct H as (EQ & FC & Hi & Hac & HN & HAr & Hop & Hoc & HA0 & HAb & HF & HB).
  g0_eq EQ. apply c45_eqv_cl_of. unfold c0_ret_fa. do 26 eexists. split; [reflexivity|].
  exact (conj FC (conj Hi (conj HN (conj Hop (conj Hoc (conj HF HB)))))).
Qed.

(* ==========================================================================
   4. The adapters of the four calls
   ========================================================================== *)

Section G0A.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

(* the result of a text_buf call as LC0Defs c0_buf states it, and its range *)
Lemma g0_buf : forall g md mk hb cap r m', LGV B API g -> lenv_ok (lg_E g md mk) ->
  In (md, MD_SIZE) hb -> In (mk, MK_SIZE) hb -> 0 <= cap < 40 ->
  (cap = 0 -> r = 0) ->
  (cap <> 0 -> r <> 0 /\ lfresh B g hb r (cap + 1) /\ tbuf_at m' r cap (repeat (zb GUARD_BYTE) (Z.to_nat cap))) ->
  c0_buf (lg_E g md mk) cap r m' /\ 0 <= r < 2 ^ 64.
Proof using B API FF.
  intros g md mk hb cap r m' HV HE Hmd Hmk Hc Z0 Z1.
  destruct (Z.eq_dec cap 0) as [H0|H0].
  - pose proof (Z0 H0) as Hr. subst r. split; [split; [intros _; reflexivity | intros H; contradiction] | lia].
  - destruct (Z1 H0) as (Hr & Hf & Ht). pose proof (g0_blk B API FF g md mk hb r (cap + 1) HV HE Hmd Hmk Hf) as Hb.
    split; [split; [intros H; contradiction | intros _; exact (conj Hr (conj Hb Ht))]|].
    destruct Hf as (_ & H4 & Htop & _). destruct HE as (_ & HS47 & _). unfold SLOT_STACK in Htop.
    change (e_S (lg_E g md mk)) with (lg_S g) in HS47. lia.
Qed.

Lemma g0_ad_kc : forall g md mk hb i gp P N sel kc ac kbs mbs gbs R F fc m regs' m' r,
  LGV B API g -> lenv_ok (lg_E g md mk) -> In (md, MD_SIZE) hb -> In (mk, MK_SIZE) hb ->
  c0_cut_kc (lg_E g md mk) i gp P N sel kc ac kbs mbs gbs (MS R F (Z_to_bv 64 TEXT_BUF) fc None m (seg_rom rsegs)) ->
  regs_preserved R regs' -> getr regs' 10 = Z_to_bv 64 r ->
  lcarry (lkeep B g hb) m m' -> lpost_mem g m' ->
  (kc = 0 -> r = 0) ->
  (kc <> 0 -> r <> 0 /\ lfresh B g hb r (kc + 1) /\ tbuf_at m' r kc (repeat (zb GUARD_BYTE) (Z.to_nat kc))) ->
  eqv_cl (c0_ret_kc (lg_E g md mk) i gp P N sel kc ac r kbs mbs gbs)
    (MS regs' F (Z_to_bv 64 C0_RA_KC) fc None m' (seg_rom rsegs)).
Proof using B API FF.
  intros g md mk hb i gp P N sel kc ac kbs mbs gbs R F fc m regs' m' r HV HE Hmd Hmk HC RP H10 CR PM Z0 Z1.
  unfold c0_cut_kc in HC. g0_ex HC.
  destruct HC as (EQ & FC & Hi & Hsel & Hkc & Hac & HN & Hop & HF & HB & HG).
  g0_eq EQ.
  destruct (g0_post_carry B API FF g md mk hb P N _ _ kbs mbs gbs _ m' HV HE Hmd Hmk HF HB CR PM) as [HF' HB'].
  destruct (g0_buf g md mk hb kc r m' HV HE Hmd Hmk Hkc Z0 Z1) as [HK HKr].
  assert (H10' : reg_get regs' (Z_to_bv 5 10) = Z_to_bv 64 r) by exact H10.
  eexists. split; [| apply g0_ms_eqv; eapply g0_canon; [exact RP | exact H10']].
  unfold c0_ret_kc. do 22 eexists. split; [reflexivity|].
  exact (conj FC (conj Hi (conj Hsel (conj Hkc (conj Hac (conj HN (conj HKr (conj Hop (conj HK
           (conj HF' (conj HB' HG))))))))))).
Qed.

Lemma g0_ad_ac : forall g md mk hb i gp P N sel kc ac K kbs mbs gbs R F fc m regs' m' r,
  LGV B API g -> lenv_ok (lg_E g md mk) -> In (md, MD_SIZE) hb -> In (mk, MK_SIZE) hb ->
  (kc <> 0 -> In (K, kc + 1) hb) ->
  c0_cut_ac (lg_E g md mk) i gp P N sel kc ac K kbs mbs gbs (MS R F (Z_to_bv 64 TEXT_BUF) fc None m (seg_rom rsegs)) ->
  regs_preserved R regs' -> getr regs' 10 = Z_to_bv 64 r ->
  lcarry (lkeep B g hb) m m' -> lpost_mem g m' ->
  (ac = 0 -> r = 0) ->
  (ac <> 0 -> r <> 0 /\ lfresh B g hb r (ac + 1) /\ tbuf_at m' r ac (repeat (zb GUARD_BYTE) (Z.to_nat ac))) ->
  eqv_cl (c0_ret_ac (lg_E g md mk) i gp P N sel kc ac K r kbs mbs gbs)
    (MS regs' F (Z_to_bv 64 C0_RA_AC) fc None m' (seg_rom rsegs)).
Proof using B API FF.
  intros g md mk hb i gp P N sel kc ac K kbs mbs gbs R F fc m regs' m' r HV HE Hmd Hmk HinK HC RP H10 CR PM
    Z0 Z1.
  unfold c0_cut_ac in HC. g0_ex HC.
  destruct HC as (EQ & FC & Hi & Hsel & Hkc & Hac & HN & HKr & Hop & HKb & HF & HB & HG).
  g0_eq EQ.
  destruct (g0_post_carry B API FF g md mk hb P N _ _ kbs mbs gbs _ m' HV HE Hmd Hmk HF HB CR PM) as [HF' HB'].
  assert (HKb' : c0_buf (lg_E g md mk) kc K m').
  { destruct HKb as (HK0 & HK1). split; [exact HK0|]. intros Hk. destruct (HK1 Hk) as (Hn & Hb & Ht).
    split; [exact Hn|]. split; [exact Hb|].
    exact (g0_tbuf_carry B API FF g hb K kc _ _ m' ltac:(lia) (HinK Hk) Ht CR). }
  assert (HKA : kc <> 0 -> ac <> 0 -> apart K (kc + 1) r (ac + 1)).
  { intros Hk Ha. destruct (Z1 Ha) as (_ & (_ & _ & _ & _ & Hhb & _) & _). unfold apart.
    destruct (Hhb K (kc + 1) (HinK Hk)); lia. }
  destruct (g0_buf g md mk hb ac r m' HV HE Hmd Hmk Hac Z0 Z1) as [HA HAr].
  assert (H10' : reg_get regs' (Z_to_bv 5 10) = Z_to_bv 64 r) by exact H10.
  eexists. split; [| apply g0_ms_eqv; eapply g0_canon; [exact RP | exact H10']].
  unfold c0_ret_ac. do 21 eexists. split; [reflexivity|].
  exact (conj FC (conj Hi (conj Hsel (conj Hkc (conj Hac (conj HN (conj HKr (conj HAr (conj Hop (conj HKA
           (conj HKb' (conj HA (conj HF' (conj HB' HG)))))))))))))).
Qed.

Lemma g0_ad_fk : forall g md mk hb i gp P N sel kc ac K A kbs mbs gbs R F fc m regs' m',
  LGV B API g -> lenv_ok (lg_E g md mk) -> In (md, MD_SIZE) hb -> In (mk, MK_SIZE) hb ->
  c0_cut_fk (lg_E g md mk) i gp P N sel kc ac K A kbs mbs gbs
    (MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs)) ->
  regs_preserved R regs' -> lcarry (lkeep B g hb) m m' -> lpost_mem g m' ->
  eqv_cl (c0_ret_fk (lg_E g md mk) i gp P N ac A kbs mbs gbs)
    (MS regs' F (Z_to_bv 64 C0_RA_FK) fc None m' (seg_rom rsegs)).
Proof using B API FF.
  intros g md mk hb i gp P N sel kc ac K A kbs mbs gbs R F fc m regs' m' HV HE Hmd Hmk HC RP CR PM.
  unfold c0_cut_fk in HC. g0_ex HC.
  destruct HC as (EQ & FC & Hi & Hkc & Hac & HN & HKr & HAr & Hop & Hoc & HKA & HK0 & HKb & HA0 & HAb & HF & HB).
  g0_eq EQ.
  destruct (g0_post_carry B API FF g md mk hb P N _ _ kbs mbs gbs _ m' HV HE Hmd Hmk HF HB CR PM) as [HF' HB'].
  eexists. split; [| apply g0_ms_eqv; eapply g0_canon; [exact RP | reflexivity]].
  unfold c0_ret_fk. do 25 eexists. split; [reflexivity|].
  exact (conj FC (conj Hi (conj Hac (conj HN (conj HAr (conj Hop (conj Hoc (conj HA0 (conj HAb
           (conj HF' HB')))))))))).
Qed.

Lemma g0_ad_fa : forall g md mk hb i gp P N ac A kbs mbs gbs R F fc m regs' m',
  LGV B API g -> lenv_ok (lg_E g md mk) -> In (md, MD_SIZE) hb -> In (mk, MK_SIZE) hb ->
  c0_cut_fa (lg_E g md mk) i gp P N ac A kbs mbs gbs (MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs)) ->
  regs_preserved R regs' -> lcarry (lkeep B g hb) m m' -> lpost_mem g m' ->
  eqv_cl (c0_ret_fa (lg_E g md mk) i gp P N kbs mbs gbs)
    (MS regs' F (Z_to_bv 64 C0_RA_FA) fc None m' (seg_rom rsegs)).
Proof using B API FF.
  intros g md mk hb i gp P N ac A kbs mbs gbs R F fc m regs' m' HV HE Hmd Hmk HC RP CR PM.
  unfold c0_cut_fa in HC. g0_ex HC.
  destruct HC as (EQ & FC & Hi & Hac & HN & HAr & Hop & Hoc & HA0 & HAb & HF & HB).
  g0_eq EQ.
  destruct (g0_post_carry B API FF g md mk hb P N _ _ kbs mbs gbs _ m' HV HE Hmd Hmk HF HB CR PM) as [HF' HB'].
  eexists. split; [| apply g0_ms_eqv; eapply g0_canon; [exact RP | reflexivity]].
  unfold c0_ret_fa. do 26 eexists. split; [reflexivity|].
  exact (conj FC (conj Hi (conj HN (conj Hop (conj Hoc (conj HF' HB')))))).
Qed.

End G0A.
