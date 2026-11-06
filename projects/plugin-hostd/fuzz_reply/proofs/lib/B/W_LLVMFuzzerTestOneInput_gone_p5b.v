(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: KF-COUNT F3: P5M carries gn_cst, gn_runc; RIstep at that bound *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput on image B,
   PHASE 5, part b: the two calls of the table-order loop, fuzz_reply.asan-ubsan 0x84c0c (check_no_loss(&g_s[k], &at),
   jal 0x84c14) to 0x84c18, and 0x84c18 (check_shape_ends(&g_s[k], prefix, &at), jal 0x84c24) to 0x84c28.  A PORT of
   image A's lib/A/W_LLVMFuzzerTestOneInput_gone_p5.v gp5_c8 / gp5_c3 (a working branch 32b23a20c3e),
   over part a (W_LLVMFuzzerTestOneInput_gone_p5a.v) and the base's two kit citations:
   - check_no_loss: GN_CNL, the kit's cnl_spec (W_contract.v Section w3n, a working branch 990666444ab), at
     G = gn_Gs k.  Its last premise (the caller's stack readable from sp up to ly_top) is [F, sp0) from the arm
     journal's own presence clause and [sp0, ly_top) from the cut's STKR (base gn_stkr), kept by the journal's view
     clause above the window (gp5_stk_rd).
   - check_shape_ends: GN_CSHE, the kit's cshe_spec (W_contract.v Section w3e); its PF premise is discharged by the
     fake-frame disjunct (PF = s3 = FF + 32 lies in the fake frame (1, fpos)), in gp5_c3 only.
   - errno: each kit post gives errno's view; its writability is the cut's errno_law (ERRL, part a). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListRep RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_gone_p5a.
(* The sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) rule 3): every sink argument is passed with @ or from the Context *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation LLVMF_STK := YCfn.LLVMF_STK.

Section gp5b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Hypothesis HGs : GN_HGs G_fr.
Hypothesis HGcells : GN_HGcells G_fr.
Hypothesis HROMPIN : GN_ROM_PIN B.
Hypothesis HZS : GN_HZS B.
Hypothesis HCE : GN_CELLS_ERRNO B.
Hypothesis RIend : GN_RI_end B MT LS RINV.
Hypothesis GWL : glob_wr_law G_fr.
Hypothesis ERRL : errno_law B.
Hypothesis HERR : GN_ERRNO_LOW B.
(* ---- the two callee texts and the loop's model obligation (A's p5 set: CNL, CSHE, RIstep, ML) ---- *)
Variable MMAX : Z.
Hypothesis CNL : GN_CNL B MT MMAX.
Hypothesis CSHE : GN_CSHE B MT.
Hypothesis RIstep : GN_RI_step B MT LS RINV MMAX.
Hypothesis ML : ameter_laws MT.
(* part a's names at this Section's variables *)
Local Notation p5st := (W_LLVMFuzzerTestOneInput_gone_p5a.p5st B MT G_fr fr_FP LS RINV).
Local Notation P5C := (W_LLVMFuzzerTestOneInput_gone_p5a.P5C B MT G_fr fr_FP LS RINV).
Local Notation P5T := (W_LLVMFuzzerTestOneInput_gone_p5a.P5T B MT G_fr fr_FP LS RINV).
Local Notation gp5_ly := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_ly B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP).
Local Notation gp5_aout_pre := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_aout_pre B LAWS).
Local Notation gp5_jk_AR := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_jk_AR B).
Local Notation gp5_jk_pres := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_jk_pres B).
Local Notation gp5_jk_faddr := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_jk_faddr B).
Local Notation gp5_split := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_split B fr_FP).
Local Notation gp5_surv := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_surv B).
Local Notation gp5_xport := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_xport B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP
  LAWS HG HGs HGcells HROMPIN GWL ERRL).
Local Notation gp5_sep_step := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_sep_step B G_fr fr_FP LAWS).
Local Notation gp5_rebuild := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_rebuild B G_fr fr_FP).
Local Notation gp5_tie_step := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_tie_step B).
Local Notation gp5_regs_call := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_regs_call B XM_LIB RLO).
Local Notation gp5_held_low := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_held_low B LAWS).
Local Notation gp5_ra_stack := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_ra_stack B LAWS).
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
(* part a's tactics (Section-local there) *)
Ltac gp5_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Ltac gp5_awr := repeat (apply awr_ok_x_cons; [intros ?a ?Ha; cbn in Ha; lia|]); apply awr_ok_x_nil.
Ltac gp5_inl := cbn [In gn_cells]; repeat (first [left; reflexivity | right]).
Definition P5M (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A h h1 E' H' ly0 S0 cst0 q,
    c = cfg_at segs (fr_B0 + AF_gn_ret1) regs mem md /\
    gst B G_fr fr_FP cx t (gn_kq cx m) (gn_set mc k h1) fake_shadow_open fpos ly S3 W mem md kk /\
    gdone RINV cx t m m1 /\ LS cx t m ly0 S0 /\ mo_le MT S0 S3 cst0 /\ gn_tie B cx m ly0 S0 (gn_set mc k h1) ly S3 /\
    gn_run (gn_pre cx m) m1 mc A i k /\
    (* KF-COUNT: the loop's calls before this one cost q; cst0 is within relay_instance_gone's cost + q + this
       check_no_loss's cnl_cost *)
    gn_runc MT (gn_pre cx m) m1 mc A i k q /\ gn_cst MT cx m m1 (q + cnl_cost MT (hs_expected h) (hs_held h)) cst0 /\
    0 <= A /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    nth k (lm_hs mc) None = Some h /\ hs_fd h = re_fd (nth i (lm_es m1) gn_e0) /\
    gn_cnl_ok h h1 E' H' /\
    Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
    hl_n (hs_held h1) < 2 ^ 26 /\
    gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
    (lm_gn m1 = 0 -> CheckRep.ends_run (gn_pre cx m) (hl_recs (hs_held h1))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (CheckRep.want_of (gn_pre cx m) (hl_recs (hs_held h1))) <> None) /\
    mo_ok MT S3 (hl_n (hs_held h1) * mo_free MT) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) (gn_at1 (lm_gn m1) A h) /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
    sv8 W mem (lf_F cx + 24) HI_G_NOUT /\ sv8 W mem (lf_F cx + 112) gp5_HI79 /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
(* the objects by the kit's names (W_contract.v's A_g_gone, A_g_nout, A_g_out, A_g_s) *)
Lemma gp5_objs : VAL A_g_gone = rg_gone fr_RG /\ VAL A_g_nout = rg_nout fr_RG /\ VAL A_g_out = rg_out fr_RG /\
  VAL A_g_s = rg_s fr_RG.
Proof. vm_compute. repeat split. Qed.
(* a present byte is readable *)
Lemma gp5_pres_view : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview segs H m a <> None.
Proof.
  intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
(* check_no_loss's last premise at sp = F: [F, sp0) is the arm journal's presence clause, [sp0, ly_top) is the
   entry's view (aview_above_of_journal) and the cut's STKR (gn_stkr) *)
Lemma gp5_stk_rd : forall cx fpos ly3 S3 (W : world segs) mem md k,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  forall a, lf_F cx <= a < ly_top ly3 -> aview segs (w_H W) mem a <> None.
Proof.
  intros cx fpos ly3 S3 W mem md k HB HJ a Ha.
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly3 S3 W mem md k fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  unfold LLVMF_STK in *.
  destruct (Z_lt_le_dec a (spZ (c_regs cx))) as [Hlo | Hhi].
  - pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
    apply gp5_pres_view. apply Hpres. lia.
  - rewrite (aview_above_of_journal (PI := PB_fr) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 a ltac:(lia)).
    rewrite Hmg.
    + apply (gn_stkr B MT XM_LIB RLO RHI fr_live_pre G_fr cx HB a). lia.
    + rewrite unsigned_lit_small by lia. intros HGa. pose proof (pa_segs_low a (proj1 (HG a HGa))).
      unfold kLowMemEnd in *. lia.
Qed.
Lemma gp5_c8 : forall cx t m m1 i k W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> P5C cx t m m1 i k W c ->
  SRr segs W c (P5M cx t m m1 i k).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & h & -> & HST & Hk & Hi & Hh & Hfd & HR & HIR).
  pose proof HST as (HGS & HDN & (ly0 & S0 & cst & qc & HLS & Hmle & HRUNC & Hcst & Htie) & HRUN & HAW & HAT & HPF & H24 &
    H112).
  pose proof HGS as ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP).
  pose proof HDN as (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys & Hcap0 & Hent & Hsrc &
    Hmpos & Hmsz & Hc2).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  (* every open source of the loop state has hl_n <= hl_cap on its held list (amodel_at mc's aslot -> asrc_at's held
     list, W_rep.v:115 -> alist_at, W_rep.v:84) *)
  assert (Hheld : forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)).
  { intros j hj Hj. pose proof HMOD as (HM1 & HM2 & _).
    assert (Hjl : (j < 4)%nat).
    { destruct (Nat.lt_ge_cases j (length (lm_hs mc))) as [Hlt | Hge]; [lia|].
      rewrite nth_overflow in Hj by exact Hge. discriminate Hj. }
    pose proof (HM2 j Hjl) as Hsl. unfold aslot in Hsl. rewrite Hj in Hsl.
    destruct Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHL & _).
    destruct HHL as (_ & _ & _ & _ & HN & _). lia. }
  destruct (RIstep cx t m ly0 S0 hs qs c2 O2 cap2 out2 m1 mc A i k h ly S3 cst qc HRI Hop Hkeys Hcap0 Hent Hsrc HLS
    Hpairs Hafter Hrok HRUN HRUNC Hmle Hcst (proj2 Htie) Hi Hk Hh Hfd Hheld)
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof (gp5_ly cx fpos ly S3 W mem md kk HB HJ) as (Ly1 & Ly2 & Ly3 & Ly4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof HIR as (R23 & R25 & R20 & R21 & R22 & R24 & R26).
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  assert (HSTK : CNL_STK = 16640) by (vm_compute; reflexivity).
  destruct (gp5_ca_entry W regs mem AF_gn_call R27) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (gp5_EE regs _ 9 9%bv eq_refl)).
  assert (E20 : ew E 20 = getr regs 20) by (subst E; exact (gp5_EE regs _ 20 20%bv eq_refl)).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_call)) with (Z_to_bv 64 (BASE + AF_gn_call)).
  paj_run_to_tok RUNTO HS HJ SHOK gp5_span AF_fr_check_no_loss.
  { gp5_awr. }
  pmkst HS.
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] CA1_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) N1.
  prreg HS (10%bv : bv 5) N10.
  prreg HS (11%bv : bv 5) N11.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof (gp5_jk_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  rewrite U9 in N11. rewrite E20, R20 in N10.
  destruct (gn_afn_pre B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP HG LS RINV cx ly S3 fpos kk W mem mdc (ms_regs ms)
    CNL_STK HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite N1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(rewrite HSTK; lia) ltac:(rewrite HSTK; unfold LLVMF_STK; lia)) as (ch & HPREc).
  pose proof (M2 k Hk) as Hslot. unfold aslot in Hslot. rewrite Hh in Hslot.
  pose proof HSEP as ((rest0 & HPM) & _).
  destruct (gp5_aout_pre cx mc k h ly S3 W mem mdc rest0 HARc HPM Hh M4) as (OB1 & OB2 & OB3).
  pose proof M4 as (_ & _ & M4no & _ & _ & _ & M4out & _).
  pose proof (gp5_lits W mem HRV) as (L1 & L2 & L3).
  pose proof (gp5_SLOT_rng k Hk) as (HSL1 & HSL2).
  pose proof M5 as (M5a & M5b & M5c).
  rewrite Q9 in M5a, M5c.
  assert (HF8 : (lf_F cx + 208) mod 8 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (lf_F cx / 32) + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult. }
  eassert (HCALL : SRr segs W (cfg_at segs (BASE + AF_fr_check_no_loss) (ms_regs ms) mem mdc) _).
  { apply (CNL k Hk W ly S3 (ms_regs ms) mem mdc ch 224 (gp5_SLOT k) k (lf_F cx + 208) h (lm_gn m1) A
      (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)).
    - exact HPREc.
    - lia.
    - reflexivity.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. intros a Ha. apply (gp5_jk_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a).
      unfold LLVMF_STK in *. lia.
    - exact N10.
    - exact N11.
    - unfold gp5_SLOT. rewrite (proj2 (proj2 (proj2 gp5_objs))). reflexivity.
    - exact Hk.
    - exact HF8.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - exact Hslot.
    - intros a Ha. unfold gn_Gs. apply inG_cons. left. unfold in_zr, gp5_SLOT in *. cbn [fst snd]. lia.
    - destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). exists zr. split; [exact Hzin|]. split; [exact Hz8|].
      unfold gp5_SLOT, ASRC in *. lia.
    - exact F1.
    - exact F2.
    - exact F3.
    - exact HAT.
    - exact F4.
    - rewrite (proj1 gp5_objs). exact M5a.
    - destruct M5c as [X|X]; rewrite X; lia.
    - rewrite (proj1 (proj2 gp5_objs)). exact M4no.
    - rewrite (proj1 (proj2 (proj2 gp5_objs))). exact M4out.
    - exact OB1.
    - reflexivity.
    - lia.
    - intros _. exact F5.
    - exact OB2.
    - exact OB3.
    - exact F6.
    - exact HRV.
    - exact L1.
    - exact L2.
    - exact L3.
    - exact F8.
    - exact F9.
    - exact F7.
    - rewrite Hsp1. exact (gp5_stk_rd cx fpos ly S3 W mem mdc kk HB HJ). }
  eapply SRr_bind; [exact HCALL|].
  intros W2 cc Hwle2 (ly' & S' & regs' & mem' & md' & kk1 & E' & H' & -> & HJc & HP & HPK & HERR1 & HSRC & HE1 & HE2 &
    HE3 & HND & HTX & HCAP & HAT1 & HGN1 & HNO1 & HOUT1 & HOB1 & HPERM & HFRS & HMLE & HCAPGE & HCAPEQ).
  rewrite Hsp1 in HJc.
  replace (lf_F cx + 208 + 8) with (lf_F cx + 216) in HJc by lia.
  set (h1 := set_exp_held h E' H') in *.
  set (oldb := alist_blks (hs_expected h) ++ alist_blks (hs_held h)).
  set (newb := alist_blks E' ++ alist_blks H').
  set (R := (hs_partial h, APARTIAL) :: alist_blks (hs_pending h)).
  assert (HA0 : Permutation (asrc_blks h) (oldb ++ R)).
  { unfold oldb, R. rewrite <- app_assoc. exact (gp5_asrc_perm h). }
  assert (HA1 : Permutation (asrc_blks h1) (newb ++ R)).
  { unfold h1, newb, R. rewrite gp5_asrc_exp_held.
    change ((hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks E' ++ alist_blks H')
      with (((hs_partial h, APARTIAL) :: alist_blks (hs_pending h)) ++ (alist_blks E' ++ alist_blks H')).
    apply Permutation_app_comm. }
  assert (HPOSTb : forall rest, Permutation (ablocks B ly S3) (oldb ++ rest) ->
      Permutation (ablocks B ly' S') (newb ++ rest)).
  { intros rest Hr. unfold oldb, newb in *. rewrite <- app_assoc in Hr |- *. exact (HPERM rest Hr). }
  destruct (gp5_split cx mc k h ly S3 oldb R HSEP Hh HA0) as (restX & P1 & _).
  assert (Hsurv : forall b, In b (ablocks B ly S3) -> ~ In b (list_blks (hs_expected h) ++ list_blks (hs_held h)) ->
      In b (ablocks B ly' S')).
  { intros b Hb Hnb. exact (gp5_surv ly S3 ly' S' oldb newb _ b P1 (HPOSTb _ P1) Hb Hnb). }
  assert (HGS' : gst B G_fr fr_FP cx t (gn_kq cx m) mc fake_shadow_open fpos ly S3 W mem mdc kk).
  { split; [|split; [exact HMOD | exact HSEP]]. repeat (split; [assumption|]); assumption. }
  pose proof (gp5_xport cx t m mc fpos ly S3 W mem mdc kk k h (list_blks (hs_expected h) ++ list_blks (hs_held h))
    CNL_STK ly' S' W2 mem' md' kk1 HB HGS' HAW HPF H24 H112 Hk Hh (fun b Hb => Hb) HJc
    ltac:(rewrite HSTK; lia) ltac:(rewrite HSTK; unfold LLVMF_STK; lia) HERR1 Hsurv) as HXP.
  assert (Hkl : (k < length (lm_hs mc))%nat) by (rewrite M1; exact Hk).
  pose proof (gp5_sep_step cx mc k h h1 fpos ly S3 W mem mdc kk ly' S' W2 mem' md' oldb newb R HJ
    (gp5_jk_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) HSEP Hkl Hh HA0 HA1 HPOSTb) as HSEP1.
  pose proof (gp5_tie_step cx m ly0 S0 mc k h h1 ly S3 ly' S' oldb newb R Htie Hkl Hh HA0 HA1 HPOSTb) as Htie1.
  destruct (gp5_rebuild cx t m mc fpos ly' S' W2 mem' md' (kk + kk1) k h1 HXP Hk M1 HSRC HSEP1)
    as (HGS1 & HAW1 & HPF1 & H241 & H1121).
  assert (HCOK : gn_cnl_ok h h1 E' H')
    by exact (conj eq_refl (conj HE1 (conj HE2 (conj HE3 (conj HND (conj HTX (conj HCAP (conj HCAPGE HCAPEQ)))))))).
  destruct (F10 h1 E' H' S' HCOK HMLE) as (G1 & G2 & G3 & G4).
  pose proof (gp5_jk_faddr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos) as EFF.
  destruct (gp5_regs_call cx (frame_addr ly 1 fpos) i k regs (ms_regs ms) regs' CA1_KEPT HR HIR
    ltac:(intros r Hr; unfold CA1_KEPT; cbn [In] in Hr |- *; tauto) KR HP) as (HR' & HIR').
  apply SRr_ret.
  exists regs', mem', md', ly', S', (kk + kk1), fpos, mc, A, h, h1, E', H', ly0, S0,
    (cst + cnl_cost MT (hs_expected h) (hs_held h)), qc.
  split.
  { rewrite N1. unfold cfg_at. change (w64 (fr_B0 + AF_gn_ret1)) with (Z_to_bv 64 (BASE + 10452)). reflexivity. }
  split; [exact HGS1|]. split; [exact HDN|]. split; [exact HLS|].
  split; [exact (mo_le_trans MT ML _ _ _ _ _ Hmle HMLE)|].
  split; [exact Htie1|].
  split; [exact HRUN|]. split; [exact HRUNC|].
  split; [destruct Hcst as (rq & Hrq & Hcle); exists rq; split; [exact Hrq | clear - Hcle; lia]|].
  split; [lia|]. split; [exact Hk|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hfd|].
  split; [exact HCOK|].
  split; [exact F5|]. split; [exact G1|].
  split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [exact HAW1|]. split; [unfold sv8, gn_at1; exact HAT1|]. split; [exact HPF1|].
  split; [exact H241|]. split; [exact H1121|].
  rewrite EFF. split; [exact HR' | exact HIR'].
Qed.

Lemma gp5_c3 : forall cx t m m1 i k W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> P5M cx t m m1 i k W c ->
  SRr segs W c (P5T cx t m m1 i k).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & h & h1 & E' & H' & ly0 & S0 & cst0 & qc &
    -> & HGS & HDN & HLS & Hmle & Htie & HRUN & HRUNC & Hcst & HA0p & Hk & Hi & Hh & Hfd & HCOK & HO32 & G1 & G2 & G3 &
    G4 &
    HAW & HAT & HPF & H24 & H112 & HR & HIR).
  set (mc1 := gn_set mc k h1) in *.
  pose proof HGS as ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR0).
  pose proof (gp5_ly cx fpos ly S3 W mem md kk HB HJ) as (Ly1 & Ly2 & Ly3 & Ly4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof HIR as (R23 & R25 & R20 & R21 & R22 & R24 & R26).
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  assert (HSTK : CSHE_STK = 16560) by (vm_compute; reflexivity).
  assert (Hh1 : nth k (lm_hs mc1) None = Some h1).
  { unfold mc1, gn_set. cbn [lm_hs]. apply gp5_setn_same.
    rewrite <- (gp5_setn_length k (Some h1) (lm_hs mc)).
    change (gn_setn k (Some h1) (lm_hs mc)) with (lm_hs mc1). rewrite M1. exact Hk. }
  assert (Hfin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  pose proof (frame_al64 segs B ly S3 W mem md 1 fpos HAR0 Hfin) as (HFF64 & _).
  set (FF := frame_addr ly 1 fpos) in *.
  assert (HFF8 : FF mod 8 = 0).
  { pose proof (Z.div_mod FF 64 ltac:(lia)) as D. rewrite HFF64, Z.add_0_r in D. rewrite D.
    replace (64 * (FF / 64)) with ((8 * (FF / 64)) * 8) by lia. apply Z_mod_mult. }
  destruct (gp5_ca_entry W regs mem AF_gn_ret1 R27) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (gp5_EE regs _ 9 9%bv eq_refl)).
  assert (E19 : ew E 19 = getr regs 19) by (subst E; exact (gp5_EE regs _ 19 19%bv eq_refl)).
  assert (E20 : ew E 20 = getr regs 20) by (subst E; exact (gp5_EE regs _ 20 20%bv eq_refl)).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_ret1)) with (Z_to_bv 64 (BASE + AF_gn_ret1)).
  paj_run_to_tok RUNTO HS HJ SHOK gp5_span AF_fr_check_shape_ends.
  { gp5_awr. }
  pmkst HS.
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] CA2_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) N1.
  prreg HS (10%bv : bv 5) N10.
  prreg HS (11%bv : bv 5) N11.
  prreg HS (12%bv : bv 5) N12.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof (gp5_jk_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  rewrite U9 in N12. rewrite E20, R20 in N10. rewrite E19, R19 in N11.
  destruct (gn_afn_pre B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP HG LS RINV cx ly S3 fpos kk W mem mdc (ms_regs ms)
    CSHE_STK HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite N1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(rewrite HSTK; lia) ltac:(rewrite HSTK; unfold LLVMF_STK; lia)) as (ch & HPREc).
  pose proof (M2 k Hk) as Hslot. unfold aslot in Hslot. rewrite Hh1 in Hslot.
  pose proof HSEP as ((rest0 & HPM) & _).
  destruct (gp5_aout_pre cx mc1 k h1 ly S3 W mem mdc rest0 HARc HPM Hh1 M4) as (OB1 & OB2 & OB3).
  pose proof M4 as (_ & _ & M4no & _ & _ & _ & M4out & _).
  pose proof M5 as (M5a & M5b & M5c).
  change (lm_gn mc1) with (lm_gn mc) in M5a, M5c. rewrite Q9 in M5a, M5c.
  pose proof (gp5_held_low ly S3 W mem mdc (gp5_SLOT k) h1 HARc Hslot) as (HL1 & HL2).
  pose proof (gp5_SLOT_rng k Hk) as (HSL1 & HSL2).
  pose proof HPF as (PF1 & PF2 & PF3 & PF4 & PF5).
  pose proof HCOK as (EQh1 & HCE1 & HCE2 & HCE3 & HND1 & HTX1 & HCAP1 & _ & _).
  assert (HF8 : (lf_F cx + 208) mod 8 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (lf_F cx / 32) + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult. }
  eassert (HCALL : SRr segs W (cfg_at segs (BASE + AF_fr_check_shape_ends) (ms_regs ms) mem mdc) _).
  { apply (CSHE k Hk W ly S3 (ms_regs ms) mem mdc ch 224 (lf_F cx + 208) (gp5_SLOT k) k (FF + 32) h1 (gn_pre cx m)
      (gn_at1 (lm_gn m1) A h) (lm_gn m1) (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)).
    - exact HPREc.
    - lia.
    - reflexivity.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. intros a Ha. apply (gp5_jk_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a).
      unfold LLVMF_STK in *. lia.
    - exact N10.
    - exact N11.
    - exact N12.
    - exact Hslot.
    - pose proof (Z.div_mod (gp5_SLOT k) 32 ltac:(lia)) as D. rewrite HSL2, Z.add_0_r in D. rewrite D.
      replace (32 * (gp5_SLOT k / 32)) with ((4 * (gp5_SLOT k / 32)) * 8) by lia. apply Z_mod_mult.
    - lia.
    - unfold ASRC, kLowMemEnd. lia.
    - intros a Ha. unfold gn_Gs. apply inG_cons. left. unfold in_zr, gp5_SLOT in *. cbn [fst snd]. lia.
    - destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). exists zr. split; [exact Hzin|]. split; [exact Hz8|].
      unfold gp5_SLOT, ASRC in *. lia.
    - unfold gp5_SLOT. destruct gp5_hi as (_ & _ & _ & _ & H19). rewrite H19. reflexivity.
    - exact Hk.
    - intros a Ha Hw. rewrite Hsp1, HSTK in Hw. unfold ASRC, LLVMF_STK in *. lia.
    - intros a Ha. unfold cshe_home. right. left.
      assert (Hg : inG G_fr a) by (apply HGs; unfold gp5_SLOT, ASRC in *; lia).
      destruct (HG a Hg) as (Him & Hown & _). split; [exact Him|]. split; [exact Hown|].
      apply HCE. apply (gp5_cell (rg_s fr_RG) (4 * ASRC)); [gp5_inl | unfold gp5_SLOT, ASRC in *; lia].
    - rewrite EQh1. exact HND1.
    - exact G1.
    - intros a Ha Hw. pose proof (HL1 a Ha). rewrite Hsp1, HSTK in Hw. unfold LLVMF_STK in *. lia.
    - intros r Hr a Ha Hw. pose proof (HL2 r Hr a Ha). rewrite Hsp1, HSTK in Hw. unfold LLVMF_STK in *. lia.
    - exact HF8.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - apply (gp5_ra_stack ly S3 W mem mdc (lf_F cx + 208) 8 HARc); unfold LLVMF_STK in *; lia.
    - exact HAT.
    - exact PF4.
    - lia.
    - lia.
    - lia.
    - exact PF1.
    - exact PF2.
    - intros a Ha. split; [apply PF3; lia | rewrite Hsp1, HSTK; unfold LLVMF_STK in *; lia].
    - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFFapp; lia | lia].
    - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFFapp; lia | lia].
    - apply (gp5_ra_fake cx FF W mem _ _ HFR HFF8); lia.
    - apply (shadow_hull_vis_of_frame segs B LAWS ly S3 W mem mdc 1 fpos _ _ HARc Hfin);
        [fold FF; lia | change (fs_frame_bytes 1) with 128; fold FF; lia | lia].
    - (* the PF premise (the kit's disjunction): its fake-frame disjunct, PF = s3 = FF + 32 *)
      right. exists 1, fpos. split; [exact Hfin|]. intros a Ha.
      unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold FF. lia.
    - exact (gp5_lit_end5 W mem HRV).
    - exact HRV.
    - rewrite (proj1 gp5_objs). exact M5a.
    - destruct M5c as [X|X]; rewrite X; lia.
    - rewrite (proj1 (proj2 gp5_objs)). exact M4no.
    - rewrite (proj1 (proj2 (proj2 gp5_objs))). exact M4out.
    - exact OB1.
    - reflexivity.
    - lia.
    - intros _. exact HO32.
    - exact OB2.
    - exact OB3.
    - split; [unfold gn_at1; destruct (lm_gn m1 =? 0); lia | exact G2].
    - exact G3.
    - exact G4. }
  eapply SRr_bind; [exact HCALL|].
  intros W2 cc Hwle2 (ly' & S' & regs' & mem' & md' & kk2 & H'' & ds & c3 & -> & HJc & HP & HERR2 & HSRC & HV2 & HC2 &
    HND2 & HCASE & Hc0 & HAT2 & HGN2 & HPERM2 & HFRS2 & HMLE2).
  rewrite Hsp1 in HJc.
  replace (lf_F cx + 208 + 8) with (lf_F cx + 216) in HJc by lia.
  set (h2 := set_held h1 H'') in *.
  pose proof (gp5_held_perm (hs_held h1) H'' ds HV2 HC2 (gp5_cshe_perm _ _ _ _ _ _ _ _ HCASE)) as HHP.
  assert (HA0 : Permutation (asrc_blks h1) (cshe_ds_blks ds ++ asrc_blks h2)).
  { unfold h2. rewrite gp5_asrc_held. unfold asrc_blks. apply gp5_perm_held. exact HHP. }
  assert (HA1 : Permutation (asrc_blks h2) ([] ++ asrc_blks h2)) by reflexivity.
  assert (HPOSTb : forall rest, Permutation (ablocks B ly S3) (cshe_ds_blks ds ++ rest) ->
      Permutation (ablocks B ly' S') ([] ++ rest)) by exact HPERM2.
  destruct (gp5_split cx mc1 k h1 ly S3 (cshe_ds_blks ds) (asrc_blks h2) HSEP Hh1 HA0) as (restX & P1 & _).
  assert (Hds_in : forall b, In b (cshe_ds_blks ds) -> In b (list_blks (hs_held h1))).
  { intros b Hb. apply (Permutation_in b (Permutation_sym HHP)). apply in_or_app. left. exact Hb. }
  assert (Hsurv : forall b, In b (ablocks B ly S3) -> ~ In b (list_blks (hs_held h1)) -> In b (ablocks B ly' S')).
  { intros b Hb Hnb.
    exact (gp5_surv ly S3 ly' S' (cshe_ds_blks ds) [] _ b P1 (HPOSTb _ P1) Hb (fun X => Hnb (Hds_in b X))). }
  assert (HGS' : gst B G_fr fr_FP cx t (gn_kq cx m) mc1 fake_shadow_open fpos ly S3 W mem mdc kk).
  { split; [|split; [exact HMOD | exact HSEP]]. repeat (split; [assumption|]); assumption. }
  pose proof (gp5_xport cx t m mc1 fpos ly S3 W mem mdc kk k h1 (list_blks (hs_held h1))
    CSHE_STK ly' S' W2 mem' md' kk2 HB HGS' HAW HPF H24 H112 Hk Hh1 (fun b Hb => in_or_app _ _ _ (or_intror Hb))
    HJc ltac:(rewrite HSTK; lia) ltac:(rewrite HSTK; unfold LLVMF_STK; lia) HERR2 Hsurv) as HXP.
  assert (Hkl : (k < length (lm_hs mc1))%nat) by (rewrite M1; exact Hk).
  pose proof (gp5_sep_step cx mc1 k h1 h2 fpos ly S3 W mem mdc kk ly' S' W2 mem' md' (cshe_ds_blks ds) []
    (asrc_blks h2) HJ (gp5_jk_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) HSEP Hkl Hh1 HA0 HA1 HPOSTb) as HSEP1.
  pose proof (gp5_tie_step cx m ly0 S0 mc1 k h1 h2 ly S3 ly' S' (cshe_ds_blks ds) [] (asrc_blks h2)
    Htie Hkl Hh1 HA0 HA1 HPOSTb) as Htie1.
  unfold mc1 in Htie1. rewrite gp5_set_set in Htie1.
  destruct (gp5_rebuild cx t m mc1 fpos ly' S' W2 mem' md' (kk + kk2) k h2 HXP Hk M1 HSRC HSEP1)
    as (HGS1 & HAW1 & HPF1 & H241 & H1121).
  unfold mc1 in HGS1. rewrite gp5_set_set in HGS1.
  assert (HCSOK : gn_cshe_ok (gn_pre cx m) (lm_gn m1) (gn_at1 (lm_gn m1) A h) (lm_O mc) h1 h2 ds c3).
  { exists H''. split; [reflexivity|]. split; [exact HV2|]. split; [exact HC2|]. split; [exact HND2|].
    split; [exact Hc0 | exact HCASE]. }
  pose proof (gp5_jk_faddr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos) as EFF.
  destruct (gp5_regs_call cx FF i k regs (ms_regs ms) regs' CA2_KEPT HR HIR
    ltac:(intros r Hr; unfold CA2_KEPT; cbn [In] in Hr |- *; tauto) KR HP) as (HR' & HIR').
  apply SRr_ret.
  exists regs', mem', md', ly', S', (kk + kk2), fpos, (gn_set mc k h2), (gn_at1 (lm_gn m1) A h + c3).
  split.
  { rewrite N1. unfold cfg_at. change (w64 (fr_B0 + AF_gn_skip)) with (Z_to_bv 64 (BASE + 10468)). reflexivity. }
  split.
  { split; [exact HGS1|]. split; [exact HDN|].
    (* KF-COUNT: the meter after check_shape_ends (cshe_post's charge cshe_cost MT (hs_held h1)), and the run's cost
       index after the call (gn_runc_call adds both posts' charges) *)
    split; [exists ly0, S0, (cst0 + hl_n (hs_held h1) * mo_free MT),
              (qc + cnl_cost MT (hs_expected h) (hs_held h) + cshe_cost MT (hs_held h1));
            split; [exact HLS|]; split; [exact (mo_le_trans MT ML _ _ _ _ _ Hmle HMLE2)|];
            split; [exact (gn_runc_call _ _ _ mc A i k qc h h1 h2 E' H' ds c3 HRUNC Hk Hi Hh Hfd HCOK HCSOK)|];
            split; [destruct Hcst as (rq & Hrq & Hcle); exists rq; split; [exact Hrq|];
                    unfold cshe_cost; generalize (hl_n (hs_held h1) * mo_free MT); intros zc; clear - Hcle; lia |
                    exact Htie1]|].
    split; [exact (gn_run_call _ _ mc A i k h h1 h2 E' H' ds c3 HRUN Hk Hi Hh Hfd HCOK HCSOK)|].
    split; [exact HAW1|]. split; [exact HAT2|]. split; [exact HPF1|]. split; [exact H241 | exact H1121]. }
  split; [exact Hk|]. split; [exact Hi|].
  rewrite EFF. split; [exact HR' | exact HIR'].
Qed.

End gp5b.
