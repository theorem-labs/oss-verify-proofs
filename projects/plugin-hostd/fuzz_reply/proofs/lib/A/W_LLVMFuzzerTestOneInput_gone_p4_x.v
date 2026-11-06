(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC conversion of PHASE p4 of ARM_gone of fuzz_reply's LLVMFuzzerTestOneInput
   walk (lib/A/W_LLVMFuzzerTestOneInput_gone_p4.v, a Theorem Labs lane's, Qed: GC1 q -> GT0, 0x84848 -> 0x84864, the
   check_no_loss_read loop of fuzz_reply.c:643-645) to the cut invariants of lib/A/W_LLVMFuzzerTestOneInput_cut_x.v
   (a Theorem Labs lane's route (b), step 7).  _gone_p4.v is not edited.
   - The Section header is cut_x's Section w header (B .. RINV, with PST / ARx / hl / LAWS / HP0 / HG / LSx).  The
     phase's own hypotheses follow in _gone_p4.v's order: HZS, RIR, HGcells, HROMPIN verbatim; CNLR at W_contract_x's
     cnlr_spec_x.  HPST (forced by the generic placement, add_x's text): check_no_loss_read's journal keeps the image
     bytes off PST, so the loop's kept image bytes need the image off PST (trivial at the instance's PST := []).
   - _gone_p4.v's transport kit (Section gp4k_kit) reads no AR: its lemmas are CITED from it.  Of Section gp4, the
     AR-free definitions and lemmas are CITED (with their section arguments, through local abbreviations); each item
     that reads AR (the journal gp4_jr, lf_base, afn_pre, the run lemmas, a converted item) is converted here under its
     name + _x, with _gone_p4.v's proof, at the ghost list [] (cut_x's HP0): gp4_jr_x, gp4_afn_pre_at_x,
     gp4_head_post_x, gp4_head_x, gp4_tail_post_x, gp4_tail_x, gp4_loop_post_x, gp4_loopX_x and the phase lemma
     gp4_c1_t0_x over base_x's GC1_x / GT0_x.  _gone_p4.v's Section-local tactics gp4_in / gp4_mem are restated. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
(* _gone_p4.v's own imports, AFTER the generic kit's: the copied proofs see the names they were written against *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_contract W_sites W_frame W_rebase W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* _gone_p4.v compiles with this flag true (its imports' last setting, YN1e); _gone_tk.v, Required through tk_x, sets it
   false globally.  Restored here, so the copied proofs' lia calls see _gone_p4.v's setting (pro_x does the same). *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ================================================================== phase p4, over ARx *)
Section gp4_x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variables LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
(* ---- the phase's own hypotheses, in _gone_p4.v's order ---- *)
(* g_s lies in the instance's zero-shadow ranges: check_no_loss_read's shadow check of &g_s[k] *)
Hypothesis HZS : GN_HZS B.
(* the slots the loop calls check_no_loss_read on have no pending record (relay_instance_gone drained them) *)
Hypothesis RIR : GN_RI_read RINV.
(* check_no_loss_read (0x85904): W_contract_x.v:434 cnlr_spec_x, the twin of _gone_p4.v's CNLR (W_contract.v:483) *)
Hypothesis CNLR : cnlr_spec_x B PST ARx (BASE + AF_fr_check_no_loss_read).
(* what carries the model and the read-only image across that call (_gone_p4.v's text, verbatim) *)
Hypothesis HGcells : GN_HGcells G_fr.
Hypothesis HROMPIN : GN_ROM_PIN B.
(* the image is off PST (add_x's HPST): check_no_loss_read's journal keeps an image byte only off PST (YCbqG.v:254-256,
   the 11th conjunct of ajournal_x); trivial at PST = [] *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AFN0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
Ltac hp0g HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
(* ---- _gone_p4.v's AR-free items that take section arguments, cited with them ---- *)
Local Notation gp4_keep := (W_LLVMFuzzerTestOneInput_gone_p4.gp4_keep B).
Local Notation gp4_keep_trans := (W_LLVMFuzzerTestOneInput_gone_p4.gp4_keep_trans B).
Local Notation gp4_cls_cell := (W_LLVMFuzzerTestOneInput_gone_p4.gp4_cls_cell B G_fr HG HGcells).
Local Notation gp4_azs_sub := (W_LLVMFuzzerTestOneInput_gone_p4.gp4_azs_sub B).
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
(* _gone_p4.v:489-492, Section-local there *)
Ltac gp4_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* a run over read-only regions leaves the memory as it was *)
Ltac gp4_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

(* _gone_p4.v:407 gp4_jr: the walk's journal, at both ghost lists [] *)
Definition gp4_jr_x (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk.

(* _gone_p4.v:536 gp4_afn_pre_at: check_no_loss_read's afn_pre at sp = F *)
Lemma gp4_afn_pre_at_x : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  gp4_jr_x cx fpos ly3 S3 W mem md k -> gp4_saved cx W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  unfold gp4_jr_x in HJ. unfold gp4_saved in HSV.
  destruct HB as (_ & HPRE).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_x (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* ---- 0x84848 -> 0x84858: reads[q], and check_no_loss_read(&g_s[q]) when it is set ---- *)
(* _gone_p4.v:666 gp4_head_post *)
Definition gp4_head_post_x (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk', c' = cfg_at segs (fr_B0 + AF_gp4_mid) regs' mem' md' /\
    gp4_jr_x cx fpos ly S W' mem' md' kk' /\ (forall r, In r GP4_CS -> getr regs' r = getr regs r) /\
    gp4_keep cx ly S W mem W' mem'.
(* _gone_p4.v:671 gp4_head *)
Lemma gp4_head_x : forall cx fpos ly S kk (W : world segs) regs mem md (q : nat) rd,
  LFB0 cx ->
  gp4_jr_x cx fpos ly S W mem md kk -> gp4_saved cx W mem -> (q < 4)%nat ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) -> getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat q) rd -> (rd = 0 \/ (rd = 1 /\ gp4_vok W mem q)) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_c1) regs mem md) (gp4_head_post_x cx fpos ly S W regs mem).
Proof.
  intros cx fpos ly S kk W regs mem md q rd HB HJ HSV Hq R2 R3 R4 R8 R20 R21 HRD Hrd.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx _ ly S W mem md kk fpos
    HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (Hrd01 : 0 <= rd <= 1) by (destruct Hrd as [-> | (-> & _)]; lia).
  unfold gp4_jr_x in HJ.
  destruct (gp4_entry_c1 W regs mem (lf_F cx + 192 + 4 * Z.of_nat q) rd R20 ltac:(unfold LLVMF_STK in *; lia) ltac:(unfold LLVMF_STK in *; lia)
    Hrd01 HRD) as [HS SHOK].
  remember (Eimg (Ereg regs (gp4_c1_extra rd))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (gp4_c1_extra rd)) E)
    by (rewrite HE; split; [intros x Hx; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 rd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_c1)) with (Z_to_bv 64 (BASE + AF_gn_c1)).
  paj_run_tok_x RUN HS HJ SHOK gp4_Bspan.
  { apply awr_ok_x_cons; [intros x Hx; cbn in Hx; lia | apply awr_ok_x_nil]. }
  gp4_mem HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUN BR HS SHOK gp4_Bspan.
  - (* reads[q] = 0: no call *)
    paj_run_to_tok_x RUNTO HS HJ SHOK gp4_Bspan AF_gp4_mid.
    { apply awr_ok_x_cons; [intros x Hx; cbn in Hx; lia | apply awr_ok_x_nil]. }
    gp4_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_CS HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_head_post_x.
    lazymatch goal with |- exists _ _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
      exists r, mm, d, kk end.
    split; [reflexivity|]. split; [exact HJ|]. split; [exact KR|].
    intros x _. apply gp4_abk_refl.
  - (* reads[q] = 1: check_no_loss_read(&g_s[q]) *)
    assert (Hrd1 : rd = 1 /\ gp4_vok W mem q).
    { destruct Hrd as [-> | H]; [|exact H]. exfalso.
      rewrite branch_eq_U, (U_atom E 32 0 E32), U_lit in Hc by lia. discriminate Hc. }
    destruct Hrd1 as (-> & v & Mv & Rv & Hsign).
    paj_run_to_tok_x RUNTO HS HJ SHOK gp4_Bspan AF_fr_check_no_loss_read.
    { apply awr_ok_x_cons; [intros x Hx; cbn in Hx; lia | apply awr_ok_x_nil]. }
    gp4_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_CS HS HAE ltac:(vm_compute; reflexivity)) as KR.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
      set (rc0 := r) in *; set (mdc := d) in * end.
    assert (Hsp1 : spZ rc0 = lf_F cx).
    { unfold spZ. rewrite (KR 2%bv ltac:(gp4_in)), R2. unfold w64. apply unsigned_lit_small.
      unfold LLVMF_STK in *. lia. }
    destruct (gp4_afn_pre_at_x cx ly S fpos kk W mem mdc rc0 CNLR_STK HB HJ HSV Hsp1) as (ch & HPREc).
    { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
    { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
    { rewrite (KR 3%bv ltac:(gp4_in)). exact R3. }
    { rewrite (KR 4%bv ltac:(gp4_in)). exact R4. }
    { rewrite (KR 8%bv ltac:(gp4_in)). exact R8. }
    { unfold CNLR_STK. lia. }
    { unfold CNLR_STK, LLVMF_STK. lia. }
    (* check_no_loss_read's premises at p = &g_s[q] *)
    assert (Hgs : rg_s fr_RG = 6129888) by (vm_compute; reflexivity).
    assert (Hv0 : VAL (A_OBJ 0) = 645584) by (vm_compute; reflexivity).
    assert (Hv32 : VAL (A_OBJ 32) = 680120) by (vm_compute; reflexivity).
    set (p := rg_s fr_RG + ASRC * Z.of_nat q) in *.
    assert (H10 : getr rc0 10 = w64 p) by (rewrite Q10, (EEo 21%nat 21%bv eq_refl); exact R21).
    assert (Hp16 : p mod 16 = 0).
    { unfold p. rewrite Hgs. unfold ASRC.
      replace (6129888 + 96 * Z.of_nat q) with ((383118 + 6 * Z.of_nat q) * 16) by lia. apply Z_mod_mult. }
    assert (Hp0 : 0x10000 <= p) by (unfold p, ASRC; lia).
    assert (Hp1 : p + 28 <= 0x5fb000) by (unfold p, ASRC; lia).
    assert (Hzs : azs B p 28) by (apply (gp4_azs_sub _ _ _ _ HZS); unfold p, ASRC; lia).
    assert (Hd0 : p + 28 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= p) by (right; rewrite Hv0; unfold p, ASRC; lia).
    assert (Hd32 : p + 28 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= p) by (right; rewrite Hv32; unfold p, ASRC; lia).
    eapply SRr_bind.
    { exact (CNLR W ly S [] rc0 mem mdc ch p v HPREc H10 Hp16 Hp0 Hp1 Hzs Hd0 Hd32 Mv Rv Hsign). }
    intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & HPR2 & HEV).
    rewrite Hsp1 in HJc.
    pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & JH & JB & JI & JF & _).
    (* check_no_loss_read's journal inside this function's: W2's ajournal_gx_sub_x at G_fr, lifted from the donor's
       journal (G = []) *)
    assert (HJc0 : AJ0 [] 0 [] CNLR_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0)
      by (apply ajournal_gx_nil_x; exact HJc).
    assert (HJc' : AJ0 G_fr 0 [] CNLR_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
    { refine (ajournal_gx_G_mono_x segs B PST ARx [] G_fr 0 [] CNLR_STK (lf_F cx) [] ly S [] W mem mdc [] ly S [] W2
        mem2 md2 0 _ HJc0).
      intros a Ha. exfalso. exact (inG_nil a Ha). }
    pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
       (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc kk
       CNLR_STK (lf_F cx) 0 [] [] [] ly S [] W2 mem2 md2 0 HJ HJc'
       ltac:(unfold CNLR_STK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
    cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
    apply SRr_ret. unfold gp4_head_post_x.
    exists regs2, mem2, md2, kk.
    split; [unfold cfg_at; rewrite Q1; reflexivity|].
    split; [exact HJ2|].
    split; [intros r Hr; rewrite (gp4_cs_pres rc0 regs2 HP2 r Hr); exact (KR r Hr)|].
    (* the kept bytes: aleaf_post_x's view clauses and errno's view; writability from presence and wle *)
    intros a Kc. split; [|exact (gp4k_wr_kept W W2 mem mem2 a (HPR2 a) Hwle2)].
    destruct Kc as [(Kh1 & Kh2) | [(pb & nb & Kin & Kr) | [(Ki & Ko) | [Ke | (cid & pos & Kin & Kr)]]]].
    + apply JH; [exact Kh1 | unfold CNLR_STK; lia].
    + replace a with (pb + (a - pb)) by lia.
      apply (JB pb nb (a - pb)); [exact Kin | exact Kin | lia | intros Kf; exact (inFP_nil _ Kf)].
    + destruct (Z_le_dec (as_errno B) a) as [Ke1|Ke1]; [destruct (Z_lt_dec a (as_errno B + 4)) as [Ke2|Ke2]|].
      * replace a with (as_errno B + (a - as_errno B)) by lia. apply HEV. lia.
      * apply JI; [exact Ki | exact Ko | lia | exact (HPST a Ki) | apply fp_spares_closed; exact sink_closed_nil].
      * apply JI; [exact Ki | exact Ko | lia | exact (HPST a Ki) | apply fp_spares_closed; exact sink_closed_nil].
    + replace a with (as_errno B + (a - as_errno B)) by lia. apply HEV. lia.
    + apply (JF cid pos a Kin Kr). intros Kf. exact (inFP_nil _ Kf).
Qed.

(* ---- 0x84858 -> 0x84848 (q + 1 < 4) or 0x84864 (q = 3) ---- *)
(* _gone_p4.v:794 gp4_tail_post *)
Definition gp4_tail_post_x (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (q : nat) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' md' kk', gp4_jr_x cx fpos ly S W mem md' kk' /\
    (forall r, In r GP4_K2 -> getr regs' r = getr regs r) /\
    ((((q + 1) < 4)%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_c1) regs' mem md' /\
      getr regs' 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat (q + 1)) /\
      getr regs' 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat (q + 1))) \/
     ((q + 1)%nat = 4%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_t0) regs' mem md')).
(* _gone_p4.v:802 gp4_tail *)
Lemma gp4_tail_x : forall cx fpos ly S kk (W : world segs) regs mem md (q : nat),
  gp4_jr_x cx fpos ly S W mem md kk -> (q < 4)%nat -> 0 <= lf_F cx -> lf_F cx + 256 <= 2 ^ 64 ->
  getr regs 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) -> getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 22 = w64 (lf_F cx + 208) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gp4_mid) regs mem md) (gp4_tail_post_x cx fpos ly S W regs mem q).
Proof.
  intros cx fpos ly S kk W regs mem md q HJ Hq HF0 HF1 R20 R21 R22.
  unfold gp4_jr_x in HJ.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  assert (Hgs : rg_s fr_RG = 6129888) by (vm_compute; reflexivity).
  destruct (gp4_entry_md W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs gp4_md_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs gp4_md_extra) E)
    by (rewrite HE; split; [intros x Hx; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E20 : ew E 20 = Z_to_bv 64 (lf_F cx + 192 + 4 * Z.of_nat q)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E21 : ew E 21 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (lf_F cx + 208)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gp4_mid)) with (Z_to_bv 64 (BASE + AF_gp4_mid)).
  paj_run_tok_x RUN HS HJ SHOK gp4_Bspan. { apply awr_ok_x_nil. }
  gp4_mem HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUN BR HS SHOK gp4_Bspan.
  - (* s4 <> s6: back to the head *)
    rewrite branch_ne_U, (U_atom_off E 20 _ 4 E20), (U_atom E 22 _ E22) in Hc by lia.
    assert (Hq1 : ((q + 1) < 4)%nat).
    { destruct (Z.eqb_spec (lf_F cx + 192 + 4 * Z.of_nat q + 4) (lf_F cx + 208)) as [He | He];
        [discriminate Hc | lia]. }
    paj_run_to_tok_x RUNTO HS HJ SHOK gp4_Bspan AF_gn_c1. { apply awr_ok_x_nil. }
    gp4_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_K2 HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_tail_post_x. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |}] => exists r, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. left.
    split; [exact Hq1|]. split; [reflexivity|].
    split.
    + rewrite Q20, E20, unsigned_lit_small by lia. unfold w64. f_equal. lia.
    + rewrite Q21, E21, unsigned_lit_small by (unfold ASRC; lia). unfold w64. f_equal. unfold ASRC. lia.
  - (* s4 = s6: the loop is done *)
    rewrite branch_ne_U, (U_atom_off E 20 _ 4 E20), (U_atom E 22 _ E22) in Hc by lia.
    assert (Hq4 : (q + 1)%nat = 4%nat).
    { destruct (Z.eqb_spec (lf_F cx + 192 + 4 * Z.of_nat q + 4) (lf_F cx + 208)) as [He | He];
        [lia | discriminate Hc]. }
    paj_run_to_tok_x RUNTO HS HJ SHOK gp4_Bspan AF_gn_t0. { apply awr_ok_x_nil. }
    gp4_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_K2 HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_tail_post_x. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |}] => exists r, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. right.
    split; [exact Hq4 | reflexivity].
Qed.

(* ---- the loop, by induction on the slots left ---- *)
(* _gone_p4.v:863 gp4_loop_post *)
Definition gp4_loop_post_x (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk', c' = cfg_at segs (fr_B0 + AF_gn_t0) regs' mem' md' /\
    gp4_jr_x cx fpos ly S W' mem' md' kk' /\ (forall r, In r GP4_K2 -> getr regs' r = getr regs r) /\
    gp4_keep cx ly S W mem W' mem'.
(* _gone_p4.v:868 gp4_loopX *)
Lemma gp4_loopX_x : forall (k : nat) cx fpos ly S (q : nat) kk (W : world segs) regs mem md,
  LFB0 cx -> k = (4 - q)%nat -> (q < 4)%nat ->
  gp4_jr_x cx fpos ly S W mem md kk -> gp4_saved cx W mem -> gp4_cells cx W mem q ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) -> getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 22 = w64 (lf_F cx + 208) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_c1) regs mem md) (gp4_loop_post_x cx fpos ly S W regs mem).
Proof.
  induction k as [|k IH]; intros cx fpos ly S q kk W regs mem md HB Hk Hq HJ HSV HCL R2 R3 R4 R8 R20 R21 R22; [lia|].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx _ ly S W mem md kk fpos
    HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (HFlo : alloc_ceiling + 8 <= lf_F cx - 16) by (unfold LLVMF_STK in *; lia).
  destruct (HCL q ltac:(lia)) as (rd & HRD & Hrd).
  eapply SRr_bind; [exact (gp4_head_x cx fpos ly S kk W regs mem md q rd HB HJ HSV Hq R2 R3 R4 R8 R20 R21 HRD Hrd)|].
  intros W1 c1 Hwle1 (regs1 & mem1 & md1 & kk1 & -> & HJ1 & KR1 & KP1).
  eapply SRr_bind.
  { apply (gp4_tail_x cx fpos ly S kk1 W1 regs1 mem1 md1 q HJ1 Hq); [lia | lia | | |].
    - rewrite (KR1 20%bv ltac:(gp4_in)). exact R20.
    - rewrite (KR1 21%bv ltac:(gp4_in)). exact R21.
    - rewrite (KR1 22%bv ltac:(gp4_in)). exact R22. }
  intros W2 c2 Hwle2 (-> & regs2 & md2 & kk2 & HJ2 & KR2 & [(Hq1 & -> & Q20 & Q21) | (Hq4 & ->)]).
  - (* the next slot *)
    assert (KRR : forall r, In r GP4_K2 -> getr regs2 r = getr regs r)
      by (intros r Hr; rewrite (KR2 r Hr); exact (KR1 r (gp4_k2_cs r Hr))).
    eapply SRr_mono.
    { apply (IH cx fpos ly S (q + 1)%nat kk2 W1 regs2 mem1 md2 HB ltac:(lia) Hq1 HJ2).
      - intros o r Hin. apply (gp4k_sv8_kept W W1 mem mem1); [|exact (HSV o r Hin)].
        intros x Hx.
        assert (Ho : 8 <= o <= 104).
        { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
        apply KP1. left. split; lia.
      - intros j Hj. destruct (HCL j ltac:(lia)) as (rj & Hcj & Hrj). exists rj. split.
        + apply (akept_vm W mem); [|exact Hcj]. intros x Hx. apply KP1. left. split; lia.
        + destruct Hrj as [Hr0 | (Hr1 & vj & Mvj & Rvj & Hsj)]; [left; exact Hr0|]. right. split; [exact Hr1|].
          exists vj. split; [|split; [exact Rvj | exact Hsj]].
          apply (akept_vm W mem); [|exact Mvj]. intros x Hx. apply KP1. apply gp4_cls_cell.
          apply (gp4k_cell (rg_s fr_RG) (4 * ASRC)); [gp4k_inl | unfold ASRC in *; lia].
      - rewrite (KRR 2%bv ltac:(gp4_in)). exact R2.
      - rewrite (KRR 3%bv ltac:(gp4_in)). exact R3.
      - rewrite (KRR 4%bv ltac:(gp4_in)). exact R4.
      - rewrite (KRR 8%bv ltac:(gp4_in)). exact R8.
      - exact Q20.
      - exact Q21.
      - rewrite (KRR 22%bv ltac:(gp4_in)). exact R22. }
    intros W' c' Hwle (regs' & mem' & md' & kk' & -> & HJ' & KR' & KP').
    exists regs', mem', md', kk'. split; [reflexivity|]. split; [exact HJ'|].
    split; [intros r Hr; rewrite (KR' r Hr); exact (KRR r Hr)|].
    exact (gp4_keep_trans cx ly S W W1 W' mem mem1 mem' KP1 KP').
  - (* the last slot: 0x84864 *)
    apply SRr_ret. exists regs2, mem1, md2, kk2. split; [reflexivity|]. split; [exact HJ2|].
    split; [intros r Hr; rewrite (KR2 r Hr); exact (KR1 r (gp4_k2_cs r Hr))|]. exact KP1.
Qed.

(* ================================================================== GP4 *)
(* _gone_p4.v:924 gp4_c1_t0 *)
Lemma gp4_c1_t0_x : forall q cx t m m1 W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GC1_x B MT NP G_fr fr_FP PST ARx LSx RINV cx t m m1 q W c ->
  SRr segs W c (GT0_x B MT NP G_fr fr_FP PST ARx LSx RINV cx t m m1).
Proof.
  intros q cx t m m1 W c HB HC.
  destruct HC as (regs & mem & md & ly & S & kk & fpos & -> & HGST & HGD & HLS & HKR & R20 & R21 & R22 & Hq & HCL &
    HAWR & H208 & HPF).
  pose proof HGST as ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP).
  pose proof HKR as (R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27).
  pose proof HGD as (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx _ ly S W mem md kk fpos
    HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (Hq4 : (q < 4)%nat) by exact Hq.
  (* the cells reads[j] and the slots behind them *)
  assert (HCL' : gp4_cells cx W mem q).
  { intros j Hj. exists (gn_reads m j). split; [exact (HCL j ltac:(lia))|].
    destruct (gp4_reads01 m j) as [H0 | H1]; [left; exact H0 | right; split; [exact H1|]].
    exists 0. split; [|split; [lia | left; reflexivity]].
    pose proof HMOD as (_ & HSL & _). specialize (HSL j ltac:(lia)). unfold aslot in HSL.
    destruct (nth j (lm_hs m1) None) as [h|] eqn:Hnth.
    - destruct (RIR cx t m hs qs c2 O2 cap2 out2 m1 j h HRI Hpairs Hafter Hrok ltac:(lia) H1 Hnth) as [Hpe _].
      destruct HSL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hn & _) & _).
      unfold hl_n in Hn. rewrite Hpe in Hn. cbn [length Z.of_nat] in Hn.
      replace (rg_s fr_RG + ASRC * Z.of_nat j + 24) with (rg_s fr_RG + ASRC * Z.of_nat j + 16 + 8) by lia. exact Hn.
    - destruct HSL as [HZ _]. exact (gp4_zero4 _ _ 24 HZ ltac:(lia) ltac:(unfold ASRC; lia)). }
  eapply SRr_mono.
  { exact (gp4_loopX_x (4 - q) cx fpos ly S q kk W regs mem md HB eq_refl Hq4 HJ (proj1 HFR) HCL'
      R2 R3 R4 R8 R20 R21 R22). }
  intros W' c' Hwle (regs' & mem' & md' & kk' & -> & HJ' & KR & KP).
  (* what the loop kept (gp4_kcls): every byte from s1 up, the fake frame and its shadow, the live blocks, the
     model's cells, errno; and the read-only image, the allocator's own bytes pinned in both states *)
  assert (HlenP : Z.of_nat (length (c_pl cx)) = c_n cx).
  { destruct HB as (_ & HPRE0). unfold fr_lib_pre_cf_x in HPRE0. symmetry. tauto. }
  assert (HFlo : alloc_ceiling + 8 <= lf_F cx - 16) by (unfold LLVMF_STK in *; lia).
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply KP; left; split; lia).
  assert (KF : forall a, frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
      SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16 -> abyte_kept W mem W' mem' a).
  { intros a Ha. apply KP. right; right; right; right. exists 1, fpos. split; [rewrite Hfrs; left; reflexivity|].
    unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1) with 128.
    change (128 / 8) with 16. unfold SB in Ha. unfold SHADOW_OFF. lia. }
  assert (KB : forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> abyte_kept W mem W' mem' (p + i))
    by (intros p n i Hin Hi; apply KP; right; left; exists p, n; split; [exact Hin | lia]).
  assert (KC : forall a, inG gn_cells a -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply KP; apply gp4_cls_cell; exact Ha).
  assert (KE : forall i, 0 <= i < 4 -> abyte_kept W mem W' mem' (as_errno B + i))
    by (intros i Hi; apply KP; right; right; right; left; lia).
  assert (HAR' : AR0 ly S W' mem' md') by (eapply ajournal_gx_AR_x; exact HJ').
  assert (ROMK : forall a, in_rom segs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
  { intros a Ha.
    assert (Him : in_img segs a) by (destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
    destruct (Exists_dec (in_zr a) (as_owned_static B)) as [Ho|Ho].
    { intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r));
        [left; lia | right; lia | right; lia | right; lia]. }
    - pose proof (HROMPIN a Ha Ho) as Hp.
      rewrite (rom_pinned_view_x segs B ARx LAWS ly S [] W' mem' md' a HAR' Hp),
        (rom_pinned_view_x segs B ARx LAWS ly S [] W mem md a HAR Hp).
      reflexivity.
    - refine (proj1 (KP a _)). right; right; left. split; [exact Him | exact Ho]. }
  assert (HFR' : gframe cx fake_shadow_open (frame_addr ly 1 fpos) W' mem')
    by (apply (gp4_gframe_kept cx fake_shadow_open (frame_addr ly 1 fpos) W W' mem mem' HFR eq_refl KF KH); lia).
  pose proof (gp4k_amodel_kept B ly S W mem W' mem' m1 HMOD KB KC KE) as HMOD'.
  assert (HIN' : ainput_at B cx ly S W' mem').
  { destruct HIN as (I1 & I2). split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
    intros x Hx. rewrite length_map, HlenP in Hx.
    destruct I1 as [(Hn0 & _) | (Hn & Hin)]; [exfalso; lia|].
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hr].
    replace x with (c_p cx + (x - c_p cx)) by lia. apply (KB _ _ _ Hin). lia. }
  assert (HRV' : rom_view segs W' mem') by (intros a Ha; rewrite (ROMK a Ha); exact (HRV a Ha)).
  assert (HJT' : jt_rom W' mem').
  { intros i Hi. apply (val_mem_kept segs (w_H W) (w_H W') mem mem'); [|exact (HJT i Hi)].
    intros j Hj. apply ROMK. apply gp4k_jt_in_rom. cbn in Hj. lia. }
  (* the fake frame's flag word: FF + 120 lies in the fake frame, kept like gframe's FF words *)
  assert (HFL' : sv8 W' mem' (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos)).
  { apply (gp4k_sv8_kept W W' mem mem'); [|exact HFL]. intros x Hx. apply KF. lia. }
  exists regs', mem', md', ly, S, kk', fpos. split; [reflexivity|].
  split.
  { split; [|split; [exact HMOD' | exact HSEP]].
    split; [exact HJ'|]. split; [exact HFR'|].
    split; [apply (gp4k_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H40]|].
    split; [apply (gp4k_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H144]|].
    split; [exact HIN'|]. split; [exact HRV'|]. split; [exact HJT' | exact HFL']. }
  split; [exact HGD|]. split; [exact HLS|].
  split.
  { unfold gn_kregs. repeat split; rewrite KR; first [assumption | unfold GP4_K2; gp4_in]. }
  split; [apply (akept_awr W mem); [intros x Hx; apply KH; lia | exact HAWR]|].
  split; [apply (gp4k_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H208]|].
  apply (gp4_prefix_kept cx m W W' mem mem' _ HPF). intros a Ha. apply KF. lia.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): GP4 over the cut journal at a world relation R (base_x's GC1_xR / GT0_xR).
   The phase's one call, check_no_loss_read, keeps its STRICT spec CNLR (a leaf: it frees nothing), so the phase stays
   strict SRr over the R journal: the strict SRr_bind at CNLR, the callee's (strict) journal lifted to R by
   ajournal_gx_xR_mono (WLE_R) and composed with the caller's by ajournal_gx_sub_xR (R_trans).  The runs are
   W_journal_x's paj_run_x_xR / paj_run_to_x_xR, the journal reads the _xR twins (ajournal_gx_inner_xR,
   aview_above_of_journal_xR, afn_pre_x_atR, ajournal_gx_AR_xR, gn_nums_xR); every other line is the strict proof
   above.  At R := wle each text is the strict one. *)
Section gp4_xR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Ltac hp0gR HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
Let RUNR := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].

(* gp4_jr_x at R *)
Definition gp4_jr_xR (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk.

(* gp4_afn_pre_at_x over the journal at R *)
Lemma gp4_afn_pre_at_xR : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  gp4_jr_xR cx fpos ly3 S3 W mem md k -> gp4_saved cx W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  unfold gp4_jr_xR in HJ. unfold gp4_saved in HSV.
  destruct HB as (_ & HPRE).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_xR (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* gp4_head_post_x at R *)
Definition gp4_head_post_xR (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk', c' = cfg_at segs (fr_B0 + AF_gp4_mid) regs' mem' md' /\
    gp4_jr_xR cx fpos ly S W' mem' md' kk' /\ (forall r, In r GP4_CS -> getr regs' r = getr regs r) /\
    gp4_keep cx ly S W mem W' mem'.
(* gp4_head_x over the journal at R: CNLR stays strict, its journal is lifted to R (WLE_R) and composed (R_trans) *)
Lemma gp4_head_xR : forall cx fpos ly S kk (W : world segs) regs mem md (q : nat) rd,
  LFB0 cx ->
  gp4_jr_xR cx fpos ly S W mem md kk -> gp4_saved cx W mem -> (q < 4)%nat ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) -> getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat q) rd -> (rd = 0 \/ (rd = 1 /\ gp4_vok W mem q)) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_c1) regs mem md) (gp4_head_post_xR cx fpos ly S W regs mem).
Proof.
  intros cx fpos ly S kk W regs mem md q rd HB HJ HSV Hq R2 R3 R4 R8 R20 R21 HRD Hrd.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx _ ly S W mem md kk fpos
    HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (Hrd01 : 0 <= rd <= 1) by (destruct Hrd as [-> | (-> & _)]; lia).
  unfold gp4_jr_xR in HJ.
  destruct (gp4_entry_c1 W regs mem (lf_F cx + 192 + 4 * Z.of_nat q) rd R20 ltac:(unfold LLVMF_STK in *; lia) ltac:(unfold LLVMF_STK in *; lia)
    Hrd01 HRD) as [HS SHOK].
  remember (Eimg (Ereg regs (gp4_c1_extra rd))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (gp4_c1_extra rd)) E)
    by (rewrite HE; split; [intros x Hx; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 rd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_c1)) with (Z_to_bv 64 (BASE + AF_gn_c1)).
  paj_run_tok_x RUNR HS HJ SHOK gp4_Bspan.
  { apply awr_ok_x_cons; [intros x Hx; cbn in Hx; lia | apply awr_ok_x_nil]. }
  gp4_mem HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUNR BR HS SHOK gp4_Bspan.
  - (* reads[q] = 0: no call *)
    paj_run_to_tok_x RUNTOR HS HJ SHOK gp4_Bspan AF_gp4_mid.
    { apply awr_ok_x_cons; [intros x Hx; cbn in Hx; lia | apply awr_ok_x_nil]. }
    gp4_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_CS HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_head_post_xR.
    lazymatch goal with |- exists _ _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
      exists r, mm, d, kk end.
    split; [reflexivity|]. split; [exact HJ|]. split; [exact KR|].
    intros x _. apply gp4_abk_refl.
  - (* reads[q] = 1: check_no_loss_read(&g_s[q]) *)
    assert (Hrd1 : rd = 1 /\ gp4_vok W mem q).
    { destruct Hrd as [-> | H]; [|exact H]. exfalso.
      rewrite branch_eq_U, (U_atom E 32 0 E32), U_lit in Hc by lia. discriminate Hc. }
    destruct Hrd1 as (-> & v & Mv & Rv & Hsign).
    paj_run_to_tok_x RUNTOR HS HJ SHOK gp4_Bspan AF_fr_check_no_loss_read.
    { apply awr_ok_x_cons; [intros x Hx; cbn in Hx; lia | apply awr_ok_x_nil]. }
    gp4_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_CS HS HAE ltac:(vm_compute; reflexivity)) as KR.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
      set (rc0 := r) in *; set (mdc := d) in * end.
    assert (Hsp1 : spZ rc0 = lf_F cx).
    { unfold spZ. rewrite (KR 2%bv ltac:(gp4_in)), R2. unfold w64. apply unsigned_lit_small.
      unfold LLVMF_STK in *. lia. }
    destruct (gp4_afn_pre_at_xR cx ly S fpos kk W mem mdc rc0 CNLR_STK HB HJ HSV Hsp1) as (ch & HPREc).
    { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
    { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
    { rewrite (KR 3%bv ltac:(gp4_in)). exact R3. }
    { rewrite (KR 4%bv ltac:(gp4_in)). exact R4. }
    { rewrite (KR 8%bv ltac:(gp4_in)). exact R8. }
    { unfold CNLR_STK. lia. }
    { unfold CNLR_STK, LLVMF_STK. lia. }
    (* check_no_loss_read's premises at p = &g_s[q] *)
    assert (Hgs : rg_s fr_RG = 6129888) by (vm_compute; reflexivity).
    assert (Hv0 : VAL (A_OBJ 0) = 645584) by (vm_compute; reflexivity).
    assert (Hv32 : VAL (A_OBJ 32) = 680120) by (vm_compute; reflexivity).
    set (p := rg_s fr_RG + ASRC * Z.of_nat q) in *.
    assert (H10 : getr rc0 10 = w64 p) by (rewrite Q10, (EEo 21%nat 21%bv eq_refl); exact R21).
    assert (Hp16 : p mod 16 = 0).
    { unfold p. rewrite Hgs. unfold ASRC.
      replace (6129888 + 96 * Z.of_nat q) with ((383118 + 6 * Z.of_nat q) * 16) by lia. apply Z_mod_mult. }
    assert (Hp0 : 0x10000 <= p) by (unfold p, ASRC; lia).
    assert (Hp1 : p + 28 <= 0x5fb000) by (unfold p, ASRC; lia).
    assert (Hzs : azs B p 28) by (apply (gp4_azs_sub _ _ _ _ HZS); unfold p, ASRC; lia).
    assert (Hd0 : p + 28 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= p) by (right; rewrite Hv0; unfold p, ASRC; lia).
    assert (Hd32 : p + 28 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= p) by (right; rewrite Hv32; unfold p, ASRC; lia).
    eapply SRr_bind.
    { exact (CNLR W ly S [] rc0 mem mdc ch p v HPREc H10 Hp16 Hp0 Hp1 Hzs Hd0 Hd32 Mv Rv Hsign). }
    intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & HPR2 & HEV).
    rewrite Hsp1 in HJc.
    pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & JH & JB & JI & JF & _).
    (* check_no_loss_read's journal inside this function's: W2's ajournal_gx_sub_xR at G_fr, lifted from the donor's
       strict journal (G = []) to G_fr, then to R *)
    assert (HJc0 : AJ0 [] 0 [] CNLR_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0)
      by (apply ajournal_gx_nil_x; exact HJc).
    assert (HJc' : AJ0 G_fr 0 [] CNLR_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
    { refine (ajournal_gx_G_mono_x segs B PST ARx [] G_fr 0 [] CNLR_STK (lf_F cx) [] ly S [] W mem mdc [] ly S [] W2
        mem2 md2 0 _ HJc0).
      intros a Ha. exfalso. exact (inG_nil a Ha). }
    assert (HJcR : AJ0R G_fr 0 [] CNLR_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
    { rewrite ajournal_gx_x_wle in HJc'.
      exact (ajournal_gx_xR_mono segs B PST ARx (@wle segs) R WLE_R G_fr 0 [] CNLR_STK (lf_F cx) [] ly S [] W mem mdc
        [] ly S [] W2 mem2 md2 0 HJc'). }
    pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 []
       (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc kk
       CNLR_STK (lf_F cx) 0 [] [] [] ly S [] W2 mem2 md2 0 HJ HJcR
       ltac:(unfold CNLR_STK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
    cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
    apply SRr_ret. unfold gp4_head_post_xR.
    exists regs2, mem2, md2, kk.
    split; [unfold cfg_at; rewrite Q1; reflexivity|].
    split; [exact HJ2|].
    split; [intros r Hr; rewrite (gp4_cs_pres rc0 regs2 HP2 r Hr); exact (KR r Hr)|].
    (* the kept bytes: aleaf_post_x's view clauses and errno's view; writability from presence and wle *)
    intros a Kc. split; [|exact (gp4k_wr_kept W W2 mem mem2 a (HPR2 a) Hwle2)].
    destruct Kc as [(Kh1 & Kh2) | [(pb & nb & Kin & Kr) | [(Ki & Ko) | [Ke | (cid & pos & Kin & Kr)]]]].
    + apply JH; [exact Kh1 | unfold CNLR_STK; lia].
    + replace a with (pb + (a - pb)) by lia.
      apply (JB pb nb (a - pb)); [exact Kin | exact Kin | lia | intros Kf; exact (inFP_nil _ Kf)].
    + destruct (Z_le_dec (as_errno B) a) as [Ke1|Ke1]; [destruct (Z_lt_dec a (as_errno B + 4)) as [Ke2|Ke2]|].
      * replace a with (as_errno B + (a - as_errno B)) by lia. apply HEV. lia.
      * apply JI; [exact Ki | exact Ko | lia | exact (HPST a Ki) | apply fp_spares_closed; exact sink_closed_nil].
      * apply JI; [exact Ki | exact Ko | lia | exact (HPST a Ki) | apply fp_spares_closed; exact sink_closed_nil].
    + replace a with (as_errno B + (a - as_errno B)) by lia. apply HEV. lia.
    + apply (JF cid pos a Kin Kr). intros Kf. exact (inFP_nil _ Kf).
Qed.

(* gp4_tail_post_x at R *)
Definition gp4_tail_post_xR (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (q : nat) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' md' kk', gp4_jr_xR cx fpos ly S W mem md' kk' /\
    (forall r, In r GP4_K2 -> getr regs' r = getr regs r) /\
    ((((q + 1) < 4)%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_c1) regs' mem md' /\
      getr regs' 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat (q + 1)) /\
      getr regs' 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat (q + 1))) \/
     ((q + 1)%nat = 4%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_t0) regs' mem md')).
(* gp4_tail_x over the journal at R *)
Lemma gp4_tail_xR : forall cx fpos ly S kk (W : world segs) regs mem md (q : nat),
  gp4_jr_xR cx fpos ly S W mem md kk -> (q < 4)%nat -> 0 <= lf_F cx -> lf_F cx + 256 <= 2 ^ 64 ->
  getr regs 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) -> getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 22 = w64 (lf_F cx + 208) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gp4_mid) regs mem md) (gp4_tail_post_xR cx fpos ly S W regs mem q).
Proof.
  intros cx fpos ly S kk W regs mem md q HJ Hq HF0 HF1 R20 R21 R22.
  unfold gp4_jr_xR in HJ.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  assert (Hgs : rg_s fr_RG = 6129888) by (vm_compute; reflexivity).
  destruct (gp4_entry_md W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs gp4_md_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs gp4_md_extra) E)
    by (rewrite HE; split; [intros x Hx; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E20 : ew E 20 = Z_to_bv 64 (lf_F cx + 192 + 4 * Z.of_nat q)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E21 : ew E 21 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (lf_F cx + 208)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gp4_mid)) with (Z_to_bv 64 (BASE + AF_gp4_mid)).
  paj_run_tok_x RUNR HS HJ SHOK gp4_Bspan. { apply awr_ok_x_nil. }
  gp4_mem HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUNR BR HS SHOK gp4_Bspan.
  - (* s4 <> s6: back to the head *)
    rewrite branch_ne_U, (U_atom_off E 20 _ 4 E20), (U_atom E 22 _ E22) in Hc by lia.
    assert (Hq1 : ((q + 1) < 4)%nat).
    { destruct (Z.eqb_spec (lf_F cx + 192 + 4 * Z.of_nat q + 4) (lf_F cx + 208)) as [He | He];
        [discriminate Hc | lia]. }
    paj_run_to_tok_x RUNTOR HS HJ SHOK gp4_Bspan AF_gn_c1. { apply awr_ok_x_nil. }
    gp4_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_K2 HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_tail_post_xR. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |}] => exists r, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. left.
    split; [exact Hq1|]. split; [reflexivity|].
    split.
    + rewrite Q20, E20, unsigned_lit_small by lia. unfold w64. f_equal. lia.
    + rewrite Q21, E21, unsigned_lit_small by (unfold ASRC; lia). unfold w64. f_equal. unfold ASRC. lia.
  - (* s4 = s6: the loop is done *)
    rewrite branch_ne_U, (U_atom_off E 20 _ 4 E20), (U_atom E 22 _ E22) in Hc by lia.
    assert (Hq4 : (q + 1)%nat = 4%nat).
    { destruct (Z.eqb_spec (lf_F cx + 192 + 4 * Z.of_nat q + 4) (lf_F cx + 208)) as [He | He];
        [lia | discriminate Hc]. }
    paj_run_to_tok_x RUNTOR HS HJ SHOK gp4_Bspan AF_gn_t0. { apply awr_ok_x_nil. }
    gp4_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_K2 HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_tail_post_xR. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |}] => exists r, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. right.
    split; [exact Hq4 | reflexivity].
Qed.

(* gp4_loop_post_x at R *)
Definition gp4_loop_post_xR (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk', c' = cfg_at segs (fr_B0 + AF_gn_t0) regs' mem' md' /\
    gp4_jr_xR cx fpos ly S W' mem' md' kk' /\ (forall r, In r GP4_K2 -> getr regs' r = getr regs r) /\
    gp4_keep cx ly S W mem W' mem'.
(* gp4_loopX_x over the journal at R *)
Lemma gp4_loopX_xR : forall (k : nat) cx fpos ly S (q : nat) kk (W : world segs) regs mem md,
  LFB0 cx -> k = (4 - q)%nat -> (q < 4)%nat ->
  gp4_jr_xR cx fpos ly S W mem md kk -> gp4_saved cx W mem -> gp4_cells cx W mem q ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) -> getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 22 = w64 (lf_F cx + 208) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_c1) regs mem md) (gp4_loop_post_xR cx fpos ly S W regs mem).
Proof.
  induction k as [|k IH]; intros cx fpos ly S q kk W regs mem md HB Hk Hq HJ HSV HCL R2 R3 R4 R8 R20 R21 R22; [lia|].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx _ ly S W mem md kk fpos
    HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (HFlo : alloc_ceiling + 8 <= lf_F cx - 16) by (unfold LLVMF_STK in *; lia).
  destruct (HCL q ltac:(lia)) as (rd & HRD & Hrd).
  eapply SRr_bind; [exact (gp4_head_xR cx fpos ly S kk W regs mem md q rd HB HJ HSV Hq R2 R3 R4 R8 R20 R21 HRD Hrd)|].
  intros W1 c1 Hwle1 (regs1 & mem1 & md1 & kk1 & -> & HJ1 & KR1 & KP1).
  eapply SRr_bind.
  { apply (gp4_tail_xR cx fpos ly S kk1 W1 regs1 mem1 md1 q HJ1 Hq); [lia | lia | | |].
    - rewrite (KR1 20%bv ltac:(gp4_in)). exact R20.
    - rewrite (KR1 21%bv ltac:(gp4_in)). exact R21.
    - rewrite (KR1 22%bv ltac:(gp4_in)). exact R22. }
  intros W2 c2 Hwle2 (-> & regs2 & md2 & kk2 & HJ2 & KR2 & [(Hq1 & -> & Q20 & Q21) | (Hq4 & ->)]).
  - (* the next slot *)
    assert (KRR : forall r, In r GP4_K2 -> getr regs2 r = getr regs r)
      by (intros r Hr; rewrite (KR2 r Hr); exact (KR1 r (gp4_k2_cs r Hr))).
    eapply SRr_mono.
    { apply (IH cx fpos ly S (q + 1)%nat kk2 W1 regs2 mem1 md2 HB ltac:(lia) Hq1 HJ2).
      - intros o r Hin. apply (gp4k_sv8_kept W W1 mem mem1); [|exact (HSV o r Hin)].
        intros x Hx.
        assert (Ho : 8 <= o <= 104).
        { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
        apply KP1. left. split; lia.
      - intros j Hj. destruct (HCL j ltac:(lia)) as (rj & Hcj & Hrj). exists rj. split.
        + apply (akept_vm W mem); [|exact Hcj]. intros x Hx. apply KP1. left. split; lia.
        + destruct Hrj as [Hr0 | (Hr1 & vj & Mvj & Rvj & Hsj)]; [left; exact Hr0|]. right. split; [exact Hr1|].
          exists vj. split; [|split; [exact Rvj | exact Hsj]].
          apply (akept_vm W mem); [|exact Mvj]. intros x Hx. apply KP1. apply gp4_cls_cell.
          apply (gp4k_cell (rg_s fr_RG) (4 * ASRC)); [gp4k_inl | unfold ASRC in *; lia].
      - rewrite (KRR 2%bv ltac:(gp4_in)). exact R2.
      - rewrite (KRR 3%bv ltac:(gp4_in)). exact R3.
      - rewrite (KRR 4%bv ltac:(gp4_in)). exact R4.
      - rewrite (KRR 8%bv ltac:(gp4_in)). exact R8.
      - exact Q20.
      - exact Q21.
      - rewrite (KRR 22%bv ltac:(gp4_in)). exact R22. }
    intros W' c' Hwle (regs' & mem' & md' & kk' & -> & HJ' & KR' & KP').
    exists regs', mem', md', kk'. split; [reflexivity|]. split; [exact HJ'|].
    split; [intros r Hr; rewrite (KR' r Hr); exact (KRR r Hr)|].
    exact (gp4_keep_trans cx ly S W W1 W' mem mem1 mem' KP1 KP').
  - (* the last slot: 0x84864 *)
    apply SRr_ret. exists regs2, mem1, md2, kk2. split; [reflexivity|]. split; [exact HJ2|].
    split; [intros r Hr; rewrite (KR2 r Hr); exact (KR1 r (gp4_k2_cs r Hr))|]. exact KP1.
Qed.

(* GP4 at R: GC1_xR q to GT0_xR, strict SRr over the R journal *)
Lemma gp4_c1_t0_xR : forall q cx t m m1 W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GC1_xR B MT NP G_fr fr_FP PST ARx LSx RINV R cx t m m1 q W c ->
  SRr segs W c (GT0_xR B MT NP G_fr fr_FP PST ARx LSx RINV R cx t m m1).
Proof.
  intros q cx t m m1 W c HB HC.
  destruct HC as (regs & mem & md & ly & S & kk & fpos & -> & HGST & HGD & HLS & HKR & R20 & R21 & R22 & Hq & HCL &
    HAWR & H208 & HPF).
  pose proof HGST as ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP).
  pose proof HKR as (R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27).
  pose proof HGD as (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx _ ly S W mem md kk fpos
    HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (Hq4 : (q < 4)%nat) by exact Hq.
  (* the cells reads[j] and the slots behind them *)
  assert (HCL' : gp4_cells cx W mem q).
  { intros j Hj. exists (gn_reads m j). split; [exact (HCL j ltac:(lia))|].
    destruct (gp4_reads01 m j) as [H0 | H1]; [left; exact H0 | right; split; [exact H1|]].
    exists 0. split; [|split; [lia | left; reflexivity]].
    pose proof HMOD as (_ & HSL & _). specialize (HSL j ltac:(lia)). unfold aslot in HSL.
    destruct (nth j (lm_hs m1) None) as [h|] eqn:Hnth.
    - destruct (RIR cx t m hs qs c2 O2 cap2 out2 m1 j h HRI Hpairs Hafter Hrok ltac:(lia) H1 Hnth) as [Hpe _].
      destruct HSL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hn & _) & _).
      unfold hl_n in Hn. rewrite Hpe in Hn. cbn [length Z.of_nat] in Hn.
      replace (rg_s fr_RG + ASRC * Z.of_nat j + 24) with (rg_s fr_RG + ASRC * Z.of_nat j + 16 + 8) by lia. exact Hn.
    - destruct HSL as [HZ _]. exact (gp4_zero4 _ _ 24 HZ ltac:(lia) ltac:(unfold ASRC; lia)). }
  eapply SRr_mono.
  { exact (gp4_loopX_xR (4 - q) cx fpos ly S q kk W regs mem md HB eq_refl Hq4 HJ (proj1 HFR) HCL'
      R2 R3 R4 R8 R20 R21 R22). }
  intros W' c' Hwle (regs' & mem' & md' & kk' & -> & HJ' & KR & KP).
  (* what the loop kept (gp4_kcls): every byte from s1 up, the fake frame and its shadow, the live blocks, the
     model's cells, errno; and the read-only image, the allocator's own bytes pinned in both states *)
  assert (HlenP : Z.of_nat (length (c_pl cx)) = c_n cx).
  { destruct HB as (_ & HPRE0). unfold fr_lib_pre_cf_x in HPRE0. symmetry. tauto. }
  assert (HFlo : alloc_ceiling + 8 <= lf_F cx - 16) by (unfold LLVMF_STK in *; lia).
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply KP; left; split; lia).
  assert (KF : forall a, frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
      SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16 -> abyte_kept W mem W' mem' a).
  { intros a Ha. apply KP. right; right; right; right. exists 1, fpos. split; [rewrite Hfrs; left; reflexivity|].
    unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1) with 128.
    change (128 / 8) with 16. unfold SB in Ha. unfold SHADOW_OFF. lia. }
  assert (KB : forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> abyte_kept W mem W' mem' (p + i))
    by (intros p n i Hin Hi; apply KP; right; left; exists p, n; split; [exact Hin | lia]).
  assert (KC : forall a, inG gn_cells a -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply KP; apply gp4_cls_cell; exact Ha).
  assert (KE : forall i, 0 <= i < 4 -> abyte_kept W mem W' mem' (as_errno B + i))
    by (intros i Hi; apply KP; right; right; right; left; lia).
  assert (HAR' : AR0 ly S W' mem' md') by (eapply ajournal_gx_AR_xR; exact HJ').
  assert (ROMK : forall a, in_rom segs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
  { intros a Ha.
    assert (Him : in_img segs a) by (destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
    destruct (Exists_dec (in_zr a) (as_owned_static B)) as [Ho|Ho].
    { intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r));
        [left; lia | right; lia | right; lia | right; lia]. }
    - pose proof (HROMPIN a Ha Ho) as Hp.
      rewrite (rom_pinned_view_x segs B ARx LAWS ly S [] W' mem' md' a HAR' Hp),
        (rom_pinned_view_x segs B ARx LAWS ly S [] W mem md a HAR Hp).
      reflexivity.
    - refine (proj1 (KP a _)). right; right; left. split; [exact Him | exact Ho]. }
  assert (HFR' : gframe cx fake_shadow_open (frame_addr ly 1 fpos) W' mem')
    by (apply (gp4_gframe_kept cx fake_shadow_open (frame_addr ly 1 fpos) W W' mem mem' HFR eq_refl KF KH); lia).
  pose proof (gp4k_amodel_kept B ly S W mem W' mem' m1 HMOD KB KC KE) as HMOD'.
  assert (HIN' : ainput_at B cx ly S W' mem').
  { destruct HIN as (I1 & I2). split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
    intros x Hx. rewrite length_map, HlenP in Hx.
    destruct I1 as [(Hn0 & _) | (Hn & Hin)]; [exfalso; lia|].
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hr].
    replace x with (c_p cx + (x - c_p cx)) by lia. apply (KB _ _ _ Hin). lia. }
  assert (HRV' : rom_view segs W' mem') by (intros a Ha; rewrite (ROMK a Ha); exact (HRV a Ha)).
  assert (HJT' : jt_rom W' mem').
  { intros i Hi. apply (val_mem_kept segs (w_H W) (w_H W') mem mem'); [|exact (HJT i Hi)].
    intros j Hj. apply ROMK. apply gp4k_jt_in_rom. cbn in Hj. lia. }
  (* the fake frame's flag word: FF + 120 lies in the fake frame, kept like gframe's FF words *)
  assert (HFL' : sv8 W' mem' (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos)).
  { apply (gp4k_sv8_kept W W' mem mem'); [|exact HFL]. intros x Hx. apply KF. lia. }
  exists regs', mem', md', ly, S, kk', fpos. split; [reflexivity|].
  split.
  { split; [|split; [exact HMOD' | exact HSEP]].
    split; [exact HJ'|]. split; [exact HFR'|].
    split; [apply (gp4k_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H40]|].
    split; [apply (gp4k_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H144]|].
    split; [exact HIN'|]. split; [exact HRV'|]. split; [exact HJT' | exact HFL']. }
  split; [exact HGD|]. split; [exact HLS|].
  split.
  { unfold gn_kregs. repeat split; rewrite KR; first [assumption | unfold GP4_K2; gp4_in]. }
  split; [apply (akept_awr W mem); [intros x Hx; apply KH; lia | exact HAWR]|].
  split; [apply (gp4k_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H208]|].
  apply (gp4_prefix_kept cx m W W' mem mem' _ HPF). intros a Ha. apply KF. lia.
Qed.
End gp4_xR.

End gp4_x.
