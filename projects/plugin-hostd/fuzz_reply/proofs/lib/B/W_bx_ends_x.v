(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: block `ends` of image B's SEG_EXIT over the GENERIC allocator relation ARx
   (fuzz_reply.asan-ubsan 0x84f08-0x84fe8, lib/B/W_bx_defs_x.v lx_ends_S_x): the two nested loops after relay_finish
   that call check_shape_ends(&g_s[k], "", &at) for every open g_s[k] whose fd is order[i].
   SOURCE: lib/B/W_bx_ends.v (this block's AR proof, Qed), converted.  TEMPLATE: image A's ARx conversion of the same
   block, e60b29a425a lib/A/W_LLVMFuzzerTestOneInput_exit_x.v :2130-3572 (its AR original b86949b953d
   lib/A/W_LLVMFuzzerTestOneInput_exit.v :3016-5897), lemma by lemma.
   What changes against lib/B/W_bx_ends.v, and nothing else:
   - `AR segs B ly S W mem md` -> `ARx ly S [] W mem md`, the journal -> ajournal_gx_x segs B PST ARx with [] after
     each state, afn_pre -> afn_pre_x, lf_base -> lf_base_x, AR's al_* laws -> AR_laws_x's alx_* fields and YCbqG's
     _x lemmas; AR's block-size bound (al_blocks' `0 <= n < MALLOC_MAX`) -> the Section's BLKN / BLKM;
   - check_shape_ends is the kit's twin cshe_spec_x (lib/B/W_contract_x.v:1230) through CSHE, in place of the AR
     file's verbatim copy lx_cshe_spec (lib/B/W_bx_defs.v:219).  The two texts differ only by the ARx conversion
     (the ghost lists Hp / Hp', afn_pre_x, ashp_x, ajournal_gx_x) and by the kit's names CSHE_STK / cshe_home /
     cshe_ds_blks / cshe_cost for lx_CSHE_STK / lx_cshe_home / lx_cshe_ds_blks / lx_cshe_cost, which have the same
     bodies (lib/B/W_contract.v:1839-1855); the post's extra existential Hp' is [] by HP0;
   - the two journal lemmas of lib/B/W_bx_defs.v the block reads (lx_fla_kept, lx_afn_pre_at) are restated here
     over ARx (lx_fla_kept_x, lx_afn_pre_at_x), each with the proof of its AR text converted as above.
   Everything AR-free is CITED from lib/B/W_bx_ends.v (Local Notation where it takes Section arguments): the walk
   kit, the three journal-free runs xe_head_run / xe_adv_run (and their XEWalk tools), the transport kit, the model
   lemmas and the meter.  The Ltacs of the AR file are restated (an Ltac does not outlive its Section). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_shadow_pin W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_frame_x W_contract_x W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_bx_defs W_bx_defs_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_bx_ends.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g6.
(* RelocB's sink-instance guard, after every Import of YE2k: no sink class is a hint after it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section lxx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Local Notation A_LLVMF := YCfn.A_LLVMF.
Local Notation RA_LLVMF := YCfn.RA_LLVMF.
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ---- cut_x's Section w header (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v:199-244), verbatim ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
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
Variable MMAX : Z.
(* the AR-free model of lib/B/W_bx_defs.v, cited at this Section's variables *)
Local Notation lx_rf_run := (W_bx_defs.lx_rf_run).
Local Notation lx_rf_cost := (W_bx_defs.lx_rf_cost MT).
Local Notation lx_rf_room := (W_bx_defs.lx_rf_room MMAX).
Local Notation lx_ends_cost := (W_bx_defs.lx_ends_cost MT).
Local Notation lx_sr_total := (W_bx_defs.lx_sr_total MT).
Local Notation lx_exit_cost := (W_bx_defs.lx_exit_cost MT).
Local Notation LS := LSx.
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* ---- the hypotheses this block uses, each verbatim from lib/B/W_LLVMFuzzerTestOneInput_exit_x.v's Section
   (the list of record) ---- *)
Hypothesis MLM : ameter_laws MT.
Hypothesis ERR : errno_law_x B ARx.
Hypothesis HG_SL : forall a, inG (G_SL B fr_RG) a -> inG G_fr a.
Hypothesis AZS_s : azs B (rg_s fr_RG) (4 * ASRC).
(* ---- the room round (image A's exit_x at 5a9b16eac9e): the allocator rules' room record RP, whose room invariant is
   the cut's NP (cand13's kit, W_journal_x.v Record roomp) ---- *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis CSHE : forall G, gx_ok segs B G -> cshe_spec_x B PST ARx MT RP G (BASE + AF_fr_check_shape_ends).
Hypothesis XRF_ROM_OUT : rom_out segs B G_fr.
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis XE_LIT_S : ashp_x ARx (VAL AX_lit_empty) 1.
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  0 <= n.
Hypothesis BLKM : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  n < 2 ^ 30.
(* ---- the derived facts lib/B/W_bx_ends.v takes, each verbatim from that file ---- *)
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HG_RFc : forall a, inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_client fr_RG, 4); (AG_LISTEN, 4)] a ->
  inG G_fr a.
Hypothesis HG_MODEL : forall a,
  inG [(rg_src fr_RG, 8); (rg_capsrc fr_RG, 4); (rg_send_max fr_RG, 8); (rg_send_dead fr_RG, 1);
       (rg_gone fr_RG, 1); (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a ->
  inG G_fr a.
Hypothesis XE_ERR_HI : rg_out fr_RG + 8 <= as_errno B.
Hypothesis XE_ERR_S : as_errno B + 4 <= rg_s fr_RG \/ rg_s fr_RG + 4 * ASRC <= as_errno B.
Hypothesis XRF_JTAB_ROM : forall a, fr_jtab <= a < fr_jtab + 36 -> in_rom segs a.
Hypothesis XRF_END5 : forall (W : world segs) (mem : word -> option byte),
  rom_view segs W mem -> garr8 segs (arm W mem) (VAL A_lit_end5) (bzs END5).

(* ---- the statements' defs and the AR-free names of lib/B/W_bx_ends.v that take Section arguments, cited ---- *)
Local Notation lx_ends_post_x := (W_bx_defs_x.lx_ends_post_x B MT NP G_fr fr_FP PST ARx RP).
#[local] Notation lx_cshe_cost := (W_bx_defs.lx_cshe_cost MT).
Local Notation xe_kept_by := (W_bx_ends.xe_kept_by B).
Local Notation xe_regs_keep := (W_bx_ends.xe_regs_keep B).
Local Notation xe_regs_outer := (W_bx_ends.xe_regs_outer B).
Local Notation xe_regs_slot := (W_bx_ends.xe_regs_slot B).
Local Notation xe_head_run := (W_bx_ends.xe_head_run B XM_LIB XN_LIB RLO LSx RINV XE_ERR_S).
Local Notation xe_adv_run := (W_bx_ends.xe_adv_run B XM_LIB XN_LIB RLO LSx RINV XE_ERR_S).
Local Notation xe_globs_G := (W_bx_ends.xe_globs_G B G_fr HG_SL HG_RFc HG_MODEL).
Local Notation xe_asrc_blks := (W_bx_ends.xe_asrc_blks B).
Local Notation xe_amodel_tr := (W_bx_ends.xe_amodel_tr B).
Local Notation xe_ainput_tr := (W_bx_ends.xe_ainput_tr B).
Local Notation xe_jt_tr := (W_bx_ends.xe_jt_tr XRF_JTAB_ROM).
Local Notation xm_cost_set := (W_bx_ends.xm_cost_set MT).
Local Notation xe_cost_nonneg := (W_bx_ends.xe_cost_nonneg MT MLM).
Local Notation xe_azs_sub := (W_bx_ends.xe_azs_sub B).
Local Notation xc_slot_kept := (W_bx_ends.xc_slot_kept B).
Local Notation xc_cost_nth := (W_bx_ends.xc_cost_nth MT MLM).

(* the ROM bytes lie outside PST (ajournal_gx_rom_view_x's premise): ROM bytes are image bytes *)
Lemma PST_ROM : forall a, in_rom segs a -> ~ Exists (in_zr a) PST.
Proof. intros a (sg & H1 & _ & H3). apply HPST. exists sg. split; assumption. Qed.

(* the symbolic-run scaffolding, over W_journal_x's generic chain (cut_x's Let RUNTO / BR) *)
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* ---- lib/B/W_bx_defs.v's two journal lemmas this block reads (Section kit), over ARx ---- *)
(* a journal keeps the layout's frame base (layout_le), so the flag addresses (the donor's :1080) *)
Lemma lx_fla_kept_x : forall {G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k},
  ajournal_gx_x segs B PST ARx G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 own ly2 S2 [] W2 m2 md2 k ->
  forall cid pos, flag_addr ly2 cid pos = flag_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _) cid pos.
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold flag_addr. rewrite EF. reflexivity.
Qed.

(* The call sites' shared entry fact (the donor's :479): every call this block makes (relay_finish,
   check_shape_ends, check_shape_done, source_reset) needs the callee's `afn_pre` at sp = F, built with `afn_pre_at`
   (Reusable/YCbq.v) over the entry's frame-pointer chain with this frame pushed (`achain_push`): the prologue saved
   ra at sp0-8 and s0 at sp0-16, the first clause of bx_frame (and so of aframe_at, through bx_frame_of_aframe).
   `lf_F cx` is 320 or 336 below the entry sp, so the budget LLVMF_STK - 352 is what a callee may take. *)
Lemma lx_afn_pre_at_x : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  bx_frame cx (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 [] W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & HSG).
  rewrite !Z.add_0_r in HJ0.
  (* the frame base is 320 or 336 below the entry sp, and 32-aligned *)
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { pose proof (Z.mod_divide (sp0 - 320) 16 ltac:(lia)) as _.
      assert (E16 : (sp0 - 320) mod 16 = 0)
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
  (* the chain: the entry's, with this frame pushed *)
  pose proof (aview_above_of_journal_x (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
  pose proof HFR as (HSV & _).
  assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  clear Hpres0.
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hsp8 : sp0 mod 8 = 0).
  { assert (Hq : sp0 = 16 * (sp0 / 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    rewrite Hq. replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  assert (HCH : exists ch, achain ly3 (aview segs (w_H W) mem) (lf_F cx) sp0 ch).
  { destruct (Z_lt_ge_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
    - exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
      apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
      eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
        sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
        [ exact Hch0 | lia
        | intros a Ha; rewrite (HAB a ltac:(lia)); apply HSG; rewrite unsigned_lit_small by lia; intros HGa;
          pose proof (inG_low segs B pa_segs_low G_fr a HG HGa); lia
        | exact Hra8 | exact Hs016
        | unfold raZ in Hra40; lia | lia | exact Hsp8 | exact Hlt | rewrite HF32; lia ].
    - exists []. left. split; [right; left; rewrite HTOPeq; lia | reflexivity]. }
  destruct HCH as (ch & HCH).
  exists ch.
  eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
    [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
    [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
    | exact Hgp | exact Htp | ].
  rewrite Hsp. replace (s0Z regs) with sp0 by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  exact HCH.
Qed.

(* ============================================================ the pieces of the block ============== *)
(* the journal of one check_shape_ends call, read as the six keeps of xe_kept_by *)
Lemma xe_keeps_of_journal_x : forall G FP F AT W mem md ly S ly' S' W' mem' md' kk,
  gx_ok segs B G ->
  ~ YI16.sink_open_fp FP ->
  ajournal_gx_x segs B PST ARx G AX_XO [(AT, AT + 8)] lx_CSHE_STK F FP ly S [] W mem md [] ly' S' [] W' mem' md' kk ->
  xe_kept_by G FP F AT W mem W' mem' ly S ly' S'.
Proof.
  intros G FP F AT W mem md ly S ly' S' W' mem' md' kk HGg Hsk HJX.
  pose proof HJX as (_ & _ & _ & Hout).
  destruct (ajournal_gx_inner_x segs B PST ARx G _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJX) as (memS & HJ & Hmg).
  destruct HJ as (HAR' & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres &
    Hstatic & F5 & HQT).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  assert (HnG : forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
  { intros a Ha Hg. apply Hmg. rewrite unsigned_lit_small by lia. exact Hg. }
  assert (Hlow : forall a, inG G a -> 0 <= a < kLowMemEnd) by (intros a Ha; exact (Hsl a (proj1 (HGg a Ha)))).
  split.
  { intros a Hi HnGa Hno He _. rewrite (F3 a Hi Hno He (HPST a Hi) (fp_spares_closed FP a Hsk)).
    apply HnG; [pose proof (Hsl a Hi); lia | exact HnGa]. }
  split.
  { intros a Ha Hn. rewrite (F1 a Ha ltac:(lia)). apply HnG; [lia|].
    intros Hg. pose proof (Hlow a Hg). lia. }
  split.
  { intros a Ha Hn. apply Hout; [exact Ha|]. intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn in Hra. lia. }
  split.
  { intros p n i H1 H2 Hi Hnf. rewrite (F2 p n i H1 H2 Hi Hnf).
    destruct (alx_blocks _ _ ARx LAWS ly' S' [] W' mem' md' p n HAR' H2) as (_ & H4096 & Hce & _).
    apply HnG; [lia|]. intros Hg. destruct (HGg _ Hg) as [Himg _].
    refine (proj2 (alx_client_img _ _ ARx LAWS ly' S' [] W' mem' md' (p + i) HAR' _) Himg).
    left. exists p, n. split; [exact H2 | lia]. }
  split.
  { intros cid pos a Hin Hr Hnf. rewrite (F4 cid pos a Hin Hr Hnf).
    assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hin).
    assert (Efr : frame_addr ly' cid pos = frame_addr ly cid pos).
    { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    destruct (frames_bounds_x segs B ARx LAWS ly' S' [] W' mem' md' cid pos HAR' Hin') as (Hf0 & Hfc & _).
    rewrite Efr in Hf0, Hfc.
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr].
    - apply HnG; [lia|]. intros Hg. destruct (HGg _ Hg) as [Himg _].
      refine (proj2 (alx_client_img _ _ ARx LAWS ly' S' [] W' mem' md' a HAR' _) Himg).
      right. left. exists cid, pos. rewrite Efr. split; [exact Hin' | lia].
    - pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(lia)) as Hs1.
      pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2.
      pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hfs) as Hs3.
      apply HnG; [lia|]. intros Hg. pose proof (Hlow a Hg). lia. }
  intros a Ha. apply Hpres. lia.
Qed.

(* ---- the state the two loops carry (the cut's facts, the model's evolution and the meter).  B: the frame is
   bx_frame, and the two cells the entry wrote (F+152 norder, F+144 SB + g_s/8) are carried ---- *)
Definition xe_inv_x (cx : lfcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (m0 : lmod) (norder : Z) (ord : Z -> Z)
    (A : Z) (ly : alayout) (S : astate) (m : lmod) (W : world segs) (mem : word -> option byte) (md : Model)
  : Prop :=
  (exists kk, ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md kk) /\
  bx_frame cx (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  frame_addr ly 1 fpos = frame_addr ly3 1 fpos /\
  amodel_at B ly S W mem m /\
  ainput_at B cx ly S W mem /\
  rom_view segs W mem /\ jt_rom W mem /\
  ablocks_sep B fr_FP cx m ly S /\
  (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m0 ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest)) /\
  length (lm_hs m) = 4%nat /\
  (forall j, (j < 4)%nat -> lx_slot_evo (nth j (lm_hs m0) None) (nth j (lm_hs m) None)) /\
  lm_k m = lm_k m0 /\ lm_G m = lm_G m0 /\ lm_es m = lm_es m0 /\
  lm_c m = lx_ctl_ev (lm_c m0) (ct_ev (lm_c m)) /\
  lm_O m = lm_O m0 /\ lm_mx m = lm_mx m0 /\ lm_cap m = lm_cap m0 /\ lm_out m = lm_out m0 /\
  lm_gn m = lm_gn m0 /\ lm_nfd m = lm_nfd m0 /\
  frames S = frames S3 /\
  mo_le MT S3 S (lx_ends_cost (lm_hs m0) - lx_ends_cost (lm_hs m)) /\
  mo_ok MT S (lx_ends_cost (lm_hs m)) /\
  (forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None)) /\
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 A /\ 0 <= A <= Z.of_nat (length (lm_O m0)) /\
  val_mem segs (arm W mem) (lf_F cx + AX_NORDER) 8 norder /\ 1 <= norder <= 4 /\
  val_mem segs (arm W mem) (lf_F cx + AX_GS8) 8 (shadow_addr (rg_s fr_RG)) /\
  (forall i, 0 <= i < norder ->
     val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 (ord i) /\ 0 <= ord i < 2 ^ 31) /\
  (* the room round: the cut's NP and the count (relay_finish's post's, kept by check_shape_ends' frees) *)
  NP S /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly S).
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): xe_inv_x at a world relation R.  The journal conjunct ajournal_gx_x becomes
   ajournal_gx_xR R; every other conjunct is verbatim.  At R := wle it is xe_inv_x (xe_inv_x_wle below). *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
(* :316 xe_inv_x *)
Definition xe_inv_xR (cx : lfcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (m0 : lmod) (norder : Z) (ord : Z -> Z)
    (A : Z) (ly : alayout) (S : astate) (m : lmod) (W : world segs) (mem : word -> option byte) (md : Model)
  : Prop :=
  (exists kk, ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md kk) /\
  bx_frame cx (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  frame_addr ly 1 fpos = frame_addr ly3 1 fpos /\
  amodel_at B ly S W mem m /\
  ainput_at B cx ly S W mem /\
  rom_view segs W mem /\ jt_rom W mem /\
  ablocks_sep B fr_FP cx m ly S /\
  (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m0 ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest)) /\
  length (lm_hs m) = 4%nat /\
  (forall j, (j < 4)%nat -> lx_slot_evo (nth j (lm_hs m0) None) (nth j (lm_hs m) None)) /\
  lm_k m = lm_k m0 /\ lm_G m = lm_G m0 /\ lm_es m = lm_es m0 /\
  lm_c m = lx_ctl_ev (lm_c m0) (ct_ev (lm_c m)) /\
  lm_O m = lm_O m0 /\ lm_mx m = lm_mx m0 /\ lm_cap m = lm_cap m0 /\ lm_out m = lm_out m0 /\
  lm_gn m = lm_gn m0 /\ lm_nfd m = lm_nfd m0 /\
  frames S = frames S3 /\
  mo_le MT S3 S (lx_ends_cost (lm_hs m0) - lx_ends_cost (lm_hs m)) /\
  mo_ok MT S (lx_ends_cost (lm_hs m)) /\
  (forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None)) /\
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 A /\ 0 <= A <= Z.of_nat (length (lm_O m0)) /\
  val_mem segs (arm W mem) (lf_F cx + AX_NORDER) 8 norder /\ 1 <= norder <= 4 /\
  val_mem segs (arm W mem) (lf_F cx + AX_GS8) 8 (shadow_addr (rg_s fr_RG)) /\
  (forall i, 0 <= i < norder ->
     val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 (ord i) /\ 0 <= ord i < 2 ^ 31) /\
  (* the room round: the cut's NP and the count (relay_finish's post's, kept by check_shape_ends' frees) *)
  NP S /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly S).
End wR.
Lemma xe_inv_x_wle : xe_inv_x = xe_inv_xR (@wle segs). Proof. reflexivity. Qed.
(* paj_after_run_tok (W_kit.v:470) without the journal hypothesis *)
Ltac xw_after_run HS SHOK :=
  let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
  let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
  let HEI := fresh "HEI" in
  intros ws ms' mat' Hlen HEI HS SHOK HF HFr HG;
  cbn [sh_j sh_ss] in Hlen, HS, SHOK;
  repeat (let w := fresh "w" in
    destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
  (destruct ws; [clear Hlen | discriminate Hlen]);
  cbn [extK length Nat.add] in HS, SHOK, HEI;
  cbn [ms_mem mkst] in HF, HFr, HG;
  try match type of HS with context [restrict _ ?msn] =>
    repeat match goal with
    | old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
    end
  end;
  srr_norm_model.
(* paj_run_tok / paj_run_to_tok (W_kit.v:491-536) over xw_run_nj / xw_run_to_nj *)
Ltac xw_run HS SHOK Bspan :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
      let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
      let r := eval vm_compute in (sym_runN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH FUEL ss) in
      lazymatch r with
      | (?st', ?rs) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH FUEL ss = (st', rs))
          by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "xw_run: no img_env" end in
        eapply (xw_run_nj W FUEL E K Bx Bspan SH ss st' rs ms _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK
                  ltac:(vm_compute; reflexivity) Hrun);
        [ clear Hrun; cbn [sh_obls]; srr_obls
        | clear Hrun HS SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
          xw_after_run HS SHOK ]
      end
    end
  end.
Ltac xw_run_to HS SHOK Bspan stop :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
      let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
      let r := eval vm_compute in
        (sym_run_toN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH FUEL stop ss) in
      lazymatch r with
      | (?st', ?rs) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_run_toN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH FUEL stop ss = (st', rs))
          by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "xw_run_to: no img_env" end in
        eapply (xw_run_to_nj W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS
                  SHOK ltac:(vm_compute; reflexivity) Hrun);
        [ clear Hrun; cbn [sh_obls]; srr_obls
        | clear Hrun HS SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
          xw_after_run HS SHOK ]
      end
    end
  end.
(* the registers' environment of an entry state: the registers, then the extra atoms 32.. *)
Ltac xw_env regs extra E HE HEI HAE EEo :=
  remember (Eimg (Ereg regs extra)) as E eqn:HE;
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env);
  assert (HAE : env_agree 32 (Ereg regs extra) E)
    by (rewrite HE; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hm).
(* a register of a symbolic state, as the denotation of its symbolic value (prreg without the normalization) *)
Ltac xw_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in Hr; cbn [ms_regs restrict mkst] in Hr
  end.
(* a run over read-only regions leaves the memory as it was (the drain's ds_meq) *)
Ltac xw_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
(* the final registers and materialization of a run's end state, for the post's existentials *)
Ltac xw_ex := lazymatch goal with |- context [mkCfg (mkst ?r _ _ _) (with_vm_backing _ ?X _)] => exists r, X end.
Ltac xw_in_slot KR N25 N27 P25 P27 :=
  unfold W_bx_ends.xe_regs_slot, W_bx_ends.xe_regs_keep;
  rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
    (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)), (KR 19%bv ltac:(cbv; tauto)),
    (KR 22%bv ltac:(cbv; tauto)), (KR 24%bv ltac:(cbv; tauto)), (KR 18%bv ltac:(cbv; tauto)),
    (KR 20%bv ltac:(cbv; tauto)), (KR 21%bv ltac:(cbv; tauto)), (KR 26%bv ltac:(cbv; tauto)),
    (KR 23%bv ltac:(cbv; tauto));
  rewrite N25, N27, <- P25, <- P27;
  repeat split; assumption.
(* ---- the four runs.  Only the first writes memory (the frame cells F+144 and F+152); the others are register
   arithmetic, one read of F+144 or F+152, two shadow-checked reads of the slot and one read of order[i]. ---- *)
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): run (1) at a world relation R.  The segment moves no world: its strict walk,
   over the R journal (paj_run_to_x_xR), lifts to R by SRr_SRrG (WLE_R).  xe_entry_run_x below is it at wle. *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
(* :445 xe_entry_run_x *)
Lemma xe_entry_run_xR : forall cx (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk norder,
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own lyc Sc [] W mem md kk ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 19 = w64 norder -> getr regs 27 = w64 SB ->
  1 <= norder <= 4 -> sp0 - STK <= lf_F cx -> lf_F cx + AX_XO <= sp0 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  awr W mem (lf_F cx) (sp0 - lf_F cx) ->
  SRrG segs R W (cfg_at segs (BASE + AX_after_rf) regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' X,
       c' = cfg_at segs (BASE + AX_outer) regs' mem' (with_vm_backing (m_vm_lazy md) X md) /\
       ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own lyc Sc [] W mem'
         (with_vm_backing (m_vm_lazy md) X md) kk /\
       xe_regs_outer cx 0 norder regs' /\
       val_mem segs (arm W mem') (lf_F cx + AX_NORDER) 8 norder /\
       val_mem segs (arm W mem') (lf_F cx + AX_GS8) 8 (shadow_addr (rg_s fr_RG)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AX_GS8 <= a < lf_F cx + AX_GS8 + 16) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
  intros cx W regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk norder HJ R2 R9 R8 R3 R4 R19 R27 Hn
    HSTK HXO HF0 HF1 HAWR.
  apply (SRr_SRrG segs R WLE_R).
  pose proof asan_consts as (CC1 & _).
  destruct xw_shgs as (SG0 & SG4).
  xw_env regs (@nil word) E HE HEI HAE EEo.
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 norder) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E xw_ss_en
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_after_rf)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold xw_ss_en. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold xw_en_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. unfold AX_XO in HXO. exact (HAWR o ltac:(lia)).
    - cbn [pairwise_disjoint all_disjoint xw_en_regions]. exact (conj I I).
    - split; [|split; [exact I | exact I]].
      cbn [xw_en_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E19, E27, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  clear HE.
  assert (SHOK : sh_ok segs (SOff 27 0) [] E (mrestrict (w_H W) mem)) by constructor.
  unfold cfg_at. change (w64 (BASE + AX_after_rf)) with (Z_to_bv 64 (BASE + AX_after_rf)).
  paj_run_to_tok_x RUNTOR HS HJ SHOK xw_span AX_outer.
  { cbn [ss_mem add_cond xw_ss_en xw_en_regions].
    repeat (apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
        unfold AX_XO in HXO; left; split; [left; lia | lia]
      | ]).
    apply awr_ok_x_nil. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AX_GS8 <= a < lf_F cx + AX_GS8 + 16) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Hna. apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
    intros (r & Hin & Hr). cbn [ss_mem xw_ss_en xw_en_regions In] in Hin.
    destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
    rewrite U9 in Hr. unfold AX_GS8 in Hna. lia. }
  assert (P1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hp; exact (xw_pres_grows W _ _ a HG1 Hp)).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (VG : U E (SOff 260 0) = rg_s fr_RG)
    by (rewrite (U_img_atom E HEI 260) by (unfold A_TEXT, A_LIM; lia); exact xw_val_gs).
  assert (VG4 : U E (SOff 260 4) = rg_s fr_RG + 4)
    by (rewrite (xw_img_off E HEI 260 4) by (unfold A_TEXT, A_LIM in *; rewrite ?xw_val_gs, ?xw_rg_s; lia);
        rewrite xw_val_gs; reflexivity).
  assert (VL : U E (SOff 266 0) = VAL AX_lit_empty)
    by (rewrite (U_img_atom E HEI 266) by (unfold A_TEXT, A_LIM; lia); exact xw_val_lit).
  assert (SVN : val_mem segs (arm W (ms_mem ms)) (lf_F cx + AX_NORDER) 8 norder).
  { unfold arm, AX_NORDER.
    apply (field_of_region E _ 9%nat (lf_F cx) _ _ _ _ _ 152 8%N (SOff 19 0) norder RG0).
    - exact U9.
    - right. left. reflexivity.
    - rewrite xw_den_atom. exact E19.
    - zside.
    - zside. }
  assert (SVG : val_mem segs (arm W (ms_mem ms)) (lf_F cx + AX_GS8) 8 (shadow_addr (rg_s fr_RG))).
  { unfold arm, AX_GS8.
    apply (field_of_region E _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N
      (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 260 0) (SLit 3))) (shadow_addr (rg_s fr_RG)) RG0).
    - exact U9.
    - left. reflexivity.
    - apply xw_den; [apply xw_shU; [exact E27 | exact VG | rewrite xw_rg_s; lia] | rewrite SG0; lia].
    - rewrite SG0. zside.
    - zside. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_EN HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  xw_reg HS (18%bv : bv 5) N18. xw_reg HS (19%bv : bv 5) N19. xw_reg HS (22%bv : bv 5) N22.
  xw_reg HS (24%bv : bv 5) N24.
  pmkst HS.
  apply SRr_ret. split; [reflexivity|].
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) (with_vm_backing _ ?X _)] => exists r, mm, X end.
  split; [reflexivity|]. split; [exact HJ|].
  split.
  { unfold W_bx_ends.xe_regs_outer, W_bx_ends.xe_regs_keep.
    rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
      (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)).
    split; [|rewrite N18; reflexivity].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split.
    { rewrite N19. unfold w64. pose proof (pa_val_range AX_lit_empty) as VR.
      apply xw_den; [exact VL | exact VR]. }
    split.
    { rewrite N22. unfold w64.
      apply xw_den; [apply xw_shU; [exact E27 | exact VG4 | rewrite xw_rg_s; lia] | rewrite SG4; lia]. }
    { rewrite N24. unfold w64. apply xw_den; [exact VG | rewrite xw_rg_s; lia]. } }
  split; [exact SVN|]. split; [exact SVG|]. split; [exact K1 | exact P1].
Qed.
End wR.
(* the strict texts are the R sections' at R := wle (route R's rule: one walk text): each R premise at wle is the
   strict hypothesis of the same name, and the three laws hold for wle *)
Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].
(* (1) 0x84f08 -> 0x84f3c: g_nout = 0 is NOT here (lx_rf_site did it); this run stores norder at F+152 and the
   shadow cursor of g_s at F+144, and sets up the counter, g_s, its second shadow cursor and .str.3. *)
Lemma xe_entry_run_x : forall cx (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk norder,
  ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own lyc Sc [] W mem md kk ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 19 = w64 norder -> getr regs 27 = w64 SB ->
  1 <= norder <= 4 -> sp0 - STK <= lf_F cx -> lf_F cx + AX_XO <= sp0 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  awr W mem (lf_F cx) (sp0 - lf_F cx) ->
  SRr segs W (cfg_at segs (BASE + AX_after_rf) regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' X,
       c' = cfg_at segs (BASE + AX_outer) regs' mem' (with_vm_backing (m_vm_lazy md) X md) /\
       ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own lyc Sc [] W mem'
         (with_vm_backing (m_vm_lazy md) X md) kk /\
       xe_regs_outer cx 0 norder regs' /\
       val_mem segs (arm W mem') (lf_F cx + AX_NORDER) 8 norder /\
       val_mem segs (arm W mem') (lf_F cx + AX_GS8) 8 (shadow_addr (rg_s fr_RG)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AX_GS8 <= a < lf_F cx + AX_GS8 + 16) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof. eapply (xe_entry_run_xR (@wle segs)); wle_inst. Qed.
(* (3) 0x84f5c -> 0x84f8c (the call) or 0x84f90 (the next slot): the two inlined shadow checks of g_s[k].open
   and g_s[k].fd (their shadow byte is 0 - g_s is in the instance's zero-shadow ranges - so the partial-granule
   arms 0x84fac / 0x84fc0 are not taken), then the two tests; the call's arguments a0 = s4, a1 = s3 (.str.3),
   a2 = F + 208. *)
Lemma xe_inner_run_x : forall cx (W : world segs) regs mem md ly S md0 i (k : nat) (n : Z) (op fd oi : Z),
  ARx ly S [] W mem md0 ->
  xe_regs_slot cx i k n regs -> (k < 4)%nat -> 0 <= i < 4 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  val_mem segs (arm W mem) (xe_HA k) 4 fd -> 0 <= fd < 2 ^ 31 ->
  val_mem segs (arm W mem) (xe_HA k + 4) 4 op -> 0 <= op < 2 ^ 31 ->
  val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 oi -> 0 <= oi < 2 ^ 31 ->
  SRr segs W (cfg_at segs (BASE + AX_inner) regs mem md)
    (fun W' c' => W' = W /\ exists regs' X,
       ((op <> 0 /\ oi = fd /\
         c' = cfg_at segs (BASE + AX_call) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
         getr regs' 10 = w64 (xe_HA k) /\ getr regs' 11 = w64 (VAL AX_lit_empty) /\
         getr regs' 12 = w64 (lf_F cx + AX_AT) /\
         xe_regs_slot cx i k n regs') \/
        ((op = 0 \/ oi <> fd) /\
         c' = cfg_at segs (BASE + AX_adv) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
         xe_regs_slot cx i k n regs'))).
Proof.
  intros cx W regs mem md ly S md0 i k n op fd oi HAR HR Hk Hi HF0 HF1 Mfd Hfd Mop Hop Moi Hoi.
  destruct HR as ((R2 & R9 & R8 & R3 & R4 & R19 & R22 & R24) & R18 & R20 & R21 & R25 & R27 & R26 & R23).
  pose proof asan_consts as (CC1 & _).
  pose proof (xw_HA_rng k ltac:(lia)) as (HA1 & HA2).
  assert (HA3 : xe_HA k <= 0x5d8e60 + 288) by (unfold xe_HA, ASRC; rewrite xw_rg_s; lia).
  xw_env regs (xw_in_extra fd op oi) E HE HEI HAE EEo.
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 (VAL AX_lit_empty)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = Z_to_bv 64 (xe_HA k)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E26 : ew E 26 = Z_to_bv 64 (lf_F cx + AX_ORDER + 4 * i))
    by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 fd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 op)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 oi)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (U20 : bv_unsigned (ew E 20) = xe_HA k) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = lf_F cx + AX_ORDER + 4 * i)
    by (rewrite E26; apply unsigned_lit_small; unfold AX_ORDER; lia).
  assert (P25 : getr regs 25 = sv_denot E (SAlu ALU_ADD (SOff 35 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3)))).
  { rewrite R25. symmetry. unfold w64. pose proof (xw_sh_rng (xe_HA k) ltac:(lia)).
    apply xw_den; [|lia]. apply xw_shU; [exact E35 | exact (U_atom E 20 _ E20 ltac:(lia)) | lia]. }
  assert (P27 : getr regs 27 = sv_denot E (SAlu ALU_ADD (SOff 35 0) (SAlu ALU_SRL (SOff 20 4) (SLit 3)))).
  { rewrite R27. symmetry. unfold w64. pose proof (xw_sh_rng (xe_HA k + 4) ltac:(lia)).
    apply xw_den; [|lia]. apply xw_shU; [exact E35 | exact (U_atom_off E 20 _ 4 E20 ltac:(lia) ltac:(lia)) | lia]. }
  assert (HS : st_ok_pi segs VAL E xw_ss_in
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_inner)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold xw_ss_in. apply pa_entry_st_ok_full.
    - unfold xw_in_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
                         | intros X; discriminate X |]; rewrite <- HE; assumption.
    - vm_compute. reflexivity.
    - unfold xw_in_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor]].
        * apply (chunk_ok_val segs E _ (xe_HA k) 0 4 (SOff 32 0) fd);
            [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
          rewrite Z.add_0_r. exact Mfd.
        * apply (chunk_ok_val segs E _ (xe_HA k) 4 4 (SOff 33 0) op);
            [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
          exact Mop.
      + rewrite U26. unfold AX_ORDER in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (lf_F cx + 192 + 4 * i) 0 4 (SOff 34 0) oi);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Moi.
    - unfold xw_in_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, U26. unfold AX_ORDER.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [xw_in_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E20, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  clear HE.
  assert (HBx : U E xw_in_Bx = SHADOW_OFF)
    by (unfold xw_in_Bx; rewrite (U_atom E 35 SB E35) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs xw_in_Bx xw_in_SH E (mrestrict (w_H W) mem)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    - apply (azs_range_addressable_x B ARx LAWS ly S [] W mem md0 (xe_HA k) 96 HAR).
      destruct AZS_s as (zr & Hzin & Hz8 & Hzlo & Hzhi). unfold ASRC in Hzhi. rewrite xw_rg_s in Hzlo, Hzhi.
      exists zr. refine (conj Hzin (conj Hz8 _)). lia.
    - exact HBx.
    - rewrite (U_atom E 20 _ E20) by lia. reflexivity.
    - lia.
    - lia.
    - intros x Hx. unfold SHADOW_OFF in *. lia. }
  unfold cfg_at. change (w64 (BASE + AX_inner)) with (Z_to_bv 64 (BASE + AX_inner)).
  xw_run HS SHOK xw_span.
  xw_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok xw_run_nj BR HS SHOK xw_span.
  - (* 0x84f68 beqz a0 taken: the slot is closed, on to 0x84f90 *)
    rewrite branch_eq_U, (U_atom E 33 op E33), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    xw_run_to HS SHOK xw_span AX_adv.
    xw_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_IN HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    xw_reg HS (25%bv : bv 5) N25. xw_reg HS (27%bv : bv 5) N27.
    pmkst HS. rewrite Em2, Em1.
    apply SRr_ret. split; [reflexivity|]. xw_ex. right.
    split; [left; exact Hc|]. split; [reflexivity|].
    xw_in_slot KR N25 N27 P25 P27.
  - (* 0x84f68 beqz a0 not taken: the slot is open; the shadow check of s->fd, s->fd and order[i] *)
    rewrite branch_eq_U, (U_atom E 33 op E33), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
    xw_run HS SHOK xw_span.
    xw_meq HF Em2. clear HF HFr HG0.
    psrr_branch_tok xw_run_nj BR HS SHOK xw_span.
    + (* 0x84f7c bne taken: another fd, on to 0x84f90 *)
      rewrite branch_ne_U, (U_atom E 32 fd E32), (U_atom E 34 oi E34) in Hc0 by lia.
      apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
      xw_run_to HS SHOK xw_span AX_adv.
      xw_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_IN HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      xw_reg HS (25%bv : bv 5) N25. xw_reg HS (27%bv : bv 5) N27.
      pmkst HS. rewrite Em3, Em2, Em1.
      apply SRr_ret. split; [reflexivity|]. xw_ex. right.
      split; [right; lia|]. split; [reflexivity|].
      xw_in_slot KR N25 N27 P25 P27.
    + (* 0x84f7c bne not taken: the slot's fd is order[i]; the call's arguments, to the jal at 0x84f8c *)
      rewrite branch_ne_U, (U_atom E 32 fd E32), (U_atom E 34 oi E34) in Hc0 by lia.
      apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
      xw_run_to HS SHOK xw_span AX_call.
      xw_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_IN HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      xw_reg HS (25%bv : bv 5) N25. xw_reg HS (27%bv : bv 5) N27.
      xw_reg HS (10%bv : bv 5) N10. xw_reg HS (11%bv : bv 5) N11. xw_reg HS (12%bv : bv 5) N12.
      pmkst HS. rewrite Em3, Em2, Em1.
      apply SRr_ret. split; [reflexivity|]. xw_ex. left.
      split; [exact Hc|]. split; [lia|]. split; [reflexivity|].
      split; [rewrite N10, xw_den_atom, E20; reflexivity|].
      split; [rewrite N11, xw_den_atom, E19; reflexivity|].
      split; [rewrite N12, (xw_atom_off E 9 (lf_F cx) 208 E9) by lia; reflexivity|].
      xw_in_slot KR N25 N27 P25 P27.
Qed.
Ltac xe_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac xe_or n := lazymatch n with
  | O => first [left; lia | lia]
  | S ?m => right; xe_or m
  end.
(* the live blocks: pairwise distinct, and counted *)
Lemma xe_nodup_x : forall ly S (W : world segs) mem md, ARx ly S [] W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin.
    pose proof (BLKN ly S [] W mem md p n HAR Hin) as Hn.
    cbn [snd]. apply req_size_pos. lia. }
  destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
(* the cut's facts across the entry run's two stores (norder into F+152, SB + g_s / 8 into F+144), the shape of
   W_LLVMFuzzerTestOneInput_drain.v de_carry; the entry's aframe_at is weakened to bx_frame first *)
Lemma xe_carry_x : forall cx (W : world segs) mem mem' md ly3 S3 fpos m,
  ARx ly3 S3 [] W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  bx_frame cx (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AX_GS8 <= a < lf_F cx + AX_GS8 + 16) ->
     aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  bx_frame cx (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem' /\
  (forall a n v, lf_F cx + AX_ORDER <= a -> a + Z.of_nat n <= lf_F cx + AX_AT + 8 ->
     val_mem segs (arm W mem) a n v -> val_mem segs (arm W mem') a n v).
Proof.
  intros cx W mem mem' md ly3 S3 fpos m HAR Hin1 Hlen Hsp HFA HMOD HIN HRV HJT HV HPR.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by lia.
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  assert (HWK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a)
    by (intros a Hw; exact (writable_kept (w_H W) mem mem' a (HPR a) Hw)).
  assert (KL : forall a, 0 <= a < alloc_ceiling -> abyte_kept W mem W mem' a).
  { intros a Ha. split; [apply HV; unfold AX_GS8; lia | exact (HWK a)]. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1.
  pose proof (xe_div8 (frame_addr ly3 1 fpos) ltac:(lia)) as HFF8.
  assert (HEL : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd).
  { assert (Hg0 : inG G_fr (as_errno B))
      by (apply HG_SL; unfold G_SL; apply (xe_inG_of _ (as_errno B) 4); [xe_in | lia]).
    assert (Hg3 : inG G_fr (as_errno B + 3))
      by (apply HG_SL; unfold G_SL; apply (xe_inG_of _ (as_errno B) 4); [xe_in | lia]).
    pose proof (Hsl _ (proj1 (HG _ Hg0))). pose proof (Hsl _ (proj1 (HG _ Hg3))). lia. }
  split.
  { pose proof HFA as (_ & A2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A19 & _ & A21).
    apply (xe_bxframe_tr cx _ W mem W mem' HFA HFhi).
    - intros a Ha Hn _. apply HV; [lia | exact Hn].
    - intros i Hi. exact (HWK _ (A2 i Hi)).
    - intros a Ha. unfold SB in Ha. apply HV; [lia | unfold AX_GS8; lia].
    - intros i Hi. exact (HWK _ (A19 i Hi)).
    - intros i Hi. exact (HWK _ (A21 i Hi)). }
  split.
  { destruct m as [mk mhs mG mes [cl br dd ei ev0] mO mmx mcap mout mgn mnfd].
    pose proof HMOD as (M1 & _ & _ & M4 & _).
    pose proof M4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & Hevw & Hevb & _).
    refine (xe_amodel_tr ly3 S3 W mem ly3 S3 W mem' _ 4 mhs ev0 HMOD M1 _ _ _ _ _ _ _ _).
    - intros H4. lia.
    - intros i _ _. reflexivity.
    - intros i Hi _ a Ha. apply KL. unfold xe_HA, ASRC in Ha. cbn [fr_RG fr_globals_b rg_s] in Ha. lia.
    - intros b _ Hb. split; [exact Hb|]. destruct b as [p n]. intros a Ha. cbn [fst snd] in Ha.
      destruct (alx_blocks _ _ ARx LAWS ly3 S3 [] W mem md p n HAR Hb) as (_ & H4096 & Hce & _). apply KL. lia.
    - intros a Ha. apply KL. destruct (xe_globs_rng a Ha) as [H1 _]. cbn [fr_RG fr_globals_b rg_out] in H1. lia.
    - apply (akept_vm W mem); [intros x Hx; apply KL; lia | exact Hev].
    - apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact Hevw].
    - exact Hevb. }
  split.
  { apply (xe_ainput_tr cx ly3 S3 W mem ly3 S3 W mem' HIN Hlen). intros Hn.
    destruct HIN as [[(Hn0 & _) | (Hn0 & Hinb)] _]; [lia|]. split; [exact Hinb|].
    intros a Ha. cbn [fst snd] in Ha.
    destruct (alx_blocks _ _ ARx LAWS ly3 S3 [] W mem md _ _ HAR Hinb) as (_ & H4096 & Hce & _). apply KL. lia. }
  assert (HRV' : rom_view segs W mem').
  { intros a Ha. rewrite <- (HRV a Ha).
    assert (Hin : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
    pose proof (Hsl a Hin). exact (proj1 (KL a ltac:(lia))). }
  split; [exact HRV'|].
  split; [exact (xe_jt_tr W mem W mem' HRV HRV' HJT)|].
  intros a n v H1 H2 Hv. apply (xe_vm_view W W mem mem'); [|exact Hv].
  intros x Hx. apply HV; unfold AX_ORDER, AX_AT, AX_GS8 in *; lia.
Qed.
(* a real-stack range passes every shadow check (W_check_shape_event.v:182 range_addressable_stack) *)
Lemma xe_ra_stack_x : forall ly S (W : world segs) mem md a len,
  ARx ly S [] W mem md -> ly_stk_lo ly <= a -> a + len <= ly_stk_hi ly -> 0 <= len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a len.
Proof.
  (* the AR proof read the stack's page alignment off AR's model (am_layout) and the zero-shadow range law; over ARx
     the laws' field alx_zshadow_byte gives each stack byte's zero shadow directly *)
  intros ly S W mem md a len HAR Hlo Hhi Hlen x Hx.
  exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. exact (alx_zshadow_byte _ _ _ LAWS ly S [] W mem md x HAR ltac:(lia)).
Qed.
(* ---- the model after one call: every clause of xe_inv_x re-established at the slot check_shape_ends trimmed.
   The views come from xe_keeps_of_journal_x, the writability of the model's cells from GWR (they are bytes of
   G_fr), of the frame from the journal's presence clause and of the fake frame from the laws' alx_frames. ---- *)
Lemma xe_model_after_x : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md
    (k : nat) h (H' : hlist) (ds : list (Z * list byte)) (c : Z) ly' St' W' mem' md' kk,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  ajournal_gx_x segs B PST ARx (xe_G k) AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] lx_CSHE_STK (lf_F cx)
    (blk_FP (list_blks (hs_held h))) ly St [] W mem md [] ly' St' [] W' mem' md' kk ->
  asrc_at B ly' St' W' mem' (xe_HA k) (CheckRep.set_held h H') ->
  hl_v H' = hl_v (hs_held h) -> hl_cap H' = hl_cap (hs_held h) ->
  NoDup (CheckRep.texts H') -> hl_recs H' = [] ->
  Permutation (hl_recs (hs_held h)) ds ->
  val_mem segs (mrestrict (w_H W') mem') (lf_F cx + AX_AT) 8 (A + c) ->
  0 <= c -> A + c <= Z.of_nat (length (lm_O m0)) ->
  (forall rest, Permutation (ablocks B ly St) (lx_cshe_ds_blks ds ++ rest) ->
     Permutation (ablocks B ly' St') rest) ->
  frames St' = frames St ->
  mo_le MT St St' (lx_cshe_cost (hs_held h)) ->
  NP St' ->
  exists m', lm_hs m' = xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m) /\
    xe_inv_x cx fpos ly3 S3 m0 norder ord (A + c) ly' St' m' W' mem' md'.
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md k h H' ds c ly' St' W' mem' md' kk
    HB HI Hk Hh HJc HSRC Hv Hcap HND Hrecs HPds HAT Hc HAc HFRM HFR HMLE HNPa.
  destruct HI as ((kk0 & HJ0) & HFA & HFLW & HFAeq & HMOD & HIN & HRV & HJT & HSEP & HBF & Hlen & Hevo & Ek & EG & Ees & Ec &
    EO & Emx & Ecap & Eout & Egn & Enfd & Hfrs & Hmle & Hmok & Hsok & HATv & HA & HNO & Hnord & HGS8 & Hord & HNPi & HCNi).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  pose proof HB as (HAI0 & HPRE0).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  (* the two AR states, slot k and its held blocks *)
  pose proof (ajournal_gx_AR_x segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ0) as HAR.
  pose proof (ajournal_gx_AR_x segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as HAR'.
  pose proof HMOD as (M1 & M2 & _).
  destruct (xe_nth_some k (lm_hs m) h Hh) as [Hhe Hkl].
  pose proof (M2 k Hk) as HSk. unfold aslot in HSk. rewrite Hh in HSk.
  assert (HAH : forall b, In b (alist_blks (hs_held h)) -> In b (ablocks B ly St)).
  { intros b Hb. apply (xe_asrc_blks _ _ _ _ _ _ HSk). unfold asrc_blks. right.
    apply in_or_app. right. apply in_or_app. right. exact Hb. }
  change (list_blks (hs_held h)) with (alist_blks (hs_held h)) in HJc.
  assert (HFPc : ~ YI16.sink_open_fp (blk_FP (alist_blks (hs_held h)))).
  { apply sink_closed_pos. unfold blk_FP. apply Forall_forall. intros r Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    destruct (alx_blocks _ _ ARx LAWS ly St [] W mem md p n HAR (HAH _ Hb)) as (_ & H4096 & _). cbn [fst]. lia. }
  assert (HGk : gx_ok segs B (xe_G k)).
  { apply (gx_ok_sub segs B (xe_G k) G_fr); [|exact HG]. intros a Ha. apply HGs.
    pose proof (xe_inG_xeG k a Ha). unfold xe_HA, ASRC in *. lia. }
  destruct (xe_keeps_of_journal_x (xe_G k) (blk_FP (alist_blks (hs_held h))) (lf_F cx) (lf_F cx + AX_AT)
    W mem md ly St ly' St' W' mem' md' kk HGk HFPc HJc) as (KK1 & KK2 & KK3 & KK4 & KK5 & KK6).
  assert (HnFPi : forall a, in_img segs a -> ~ inFP (blk_FP (alist_blks (hs_held h))) a).
  { intros a Hi (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    cbn [fst snd] in Hra.
    refine (proj2 (alx_client_img _ _ ARx LAWS ly St [] W mem md a HAR _) Hi). left. exists p, n.
    split; [exact (HAH _ Hb) | lia]. }
  (* the blocks: the call frees the held records, keeps every other block of the model *)
  destruct HSEP as ((R0 & HPz0) & HSEP2).
  pose proof (xe_mblks_split cx m k h R0 Hh) as HS1.
  assert (HNDL : List.NoDup (alist_blks (hs_held h) ++ xe_skh h ++ xe_BL cx m k ++ R0)).
  { eapply Permutation_NoDup; [|exact (xe_nodup_x ly St W mem md HAR)]. eapply perm_trans; [exact HPz0 | exact HS1]. }
  destruct (ERR ly' St' [] W' mem' md' HAR') as ((ev & Hev & Hevb) & Hevw).
  set (M' := xe_set_slot m k (Some (CheckRep.set_held h H')) ev).
  assert (Hh' : nth k (lm_hs M') None = Some (CheckRep.set_held h H'))
    by (exact (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl)).
  assert (EBL : xe_BL cx M' k = xe_BL cx m k).
  { unfold xe_BL, M', xe_set_slot. cbn [lm_G lm_es lm_hs lm_cap lm_out]. rewrite xe_set_set. reflexivity. }
  assert (HAHs : Permutation (alist_blks (hs_held h)) (lx_cshe_ds_blks ds ++ alist_blks H')).
  { unfold alist_blks at 2. rewrite Hv, Hcap, Hrecs. cbn [map]. rewrite app_nil_r.
    unfold alist_blks, lx_cshe_ds_blks.
    eapply perm_trans; [apply Permutation_app_head; apply Permutation_map; exact HPds | apply Permutation_app_comm]. }
  assert (HSPL : forall R, Permutation (input_blks cx ++ model_blks m ++ R)
      (lx_cshe_ds_blks ds ++ (input_blks cx ++ model_blks M' ++ R))).
  { intros R. pose proof (xe_mblks_split cx M' k (CheckRep.set_held h H') R Hh') as X. rewrite EBL in X.
    exact (xe_perm_comb _ _ _ _ _ _ _ _ (xe_mblks_split cx m k h R Hh) X HAHs). }
  assert (HP0' : Permutation (ablocks B ly' St') (input_blks cx ++ model_blks M' ++ R0))
    by (apply HFRM; exact (perm_trans HPz0 (HSPL R0))).
  pose proof (xe_mblks_split cx M' k (CheckRep.set_held h H') R0 Hh') as HS1'. rewrite EBL in HS1'.
  assert (HBLold : forall b, In b (xe_BL cx m k) -> In b (ablocks B ly St)).
  { intros b Hb. eapply Permutation_in; [exact (Permutation_sym HPz0)|].
    eapply Permutation_in; [exact (Permutation_sym HS1)|].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (HBLnew : forall b, In b (xe_BL cx m k) -> In b (ablocks B ly' St')).
  { intros b Hb. eapply Permutation_in; [exact (Permutation_sym HP0')|].
    eapply Permutation_in; [exact (Permutation_sym HS1')|].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  (* the bytes the model reads, kept: blocks, globals, the other slots *)
  assert (KB : forall b, In b (xe_BL cx m k) -> xe_bk W mem W' mem' b).
  { intros [p n] Hb. unfold xe_bk. cbn [fst snd]. intros a Ha.
    pose proof (HBLold _ Hb) as Hin. pose proof (HBLnew _ Hb) as Hin'.
    split.
    - replace a with (p + (a - p)) by lia. apply (KK4 p n); [exact Hin | exact Hin' | lia |].
      intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq). cbn [fst snd] in Hra.
      assert (Hne : (q, n2) <> (p, n)).
      { intros E. rewrite E in Hq.
        exact (xe_nodup_app _ _ _ HNDL Hq ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)). }
      pose proof (sep_blocks_x segs B ARx LAWS ly St [] W mem md q n2 p n HAR (HAH _ Hq) Hin Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    - intros _. destruct (alx_blocks _ _ ARx LAWS ly' St' [] W' mem' md' p n HAR' Hin') as (_ & _ & _ & _ & Hpr & _).
      apply xe_wr_of_present. exact (proj1 (Hpr a Ha)). }
  assert (KG : forall a, inG XE_GLOBS a -> abyte_kept W mem W' mem' a).
  { intros a Ha. destruct (xe_globs_rng a Ha) as (Hlo & Hout). pose proof (xe_globs_G a Ha) as HGa.
    destruct (HG a HGa) as (Himg & Hown & _). split.
    - apply KK1; [exact Himg | | exact Hown | | exact (HnFPi a Himg)].
      + intros Hx. pose proof (xe_inG_xeG k a Hx) as Hx'. unfold xe_HA, ASRC in *. lia.
      + pose proof XE_ERR_HI. lia.
    - intros _. apply GWR. exact HGa. }
  assert (KS : forall i, (i < 4)%nat -> i <> k -> forall a, xe_HA i <= a < xe_HA i + ASRC ->
      abyte_kept W mem W' mem' a).
  { intros i Hi Hik a Ha.
    assert (HGa : inG G_fr a) by (apply HGs; unfold xe_HA, ASRC in *; lia).
    destruct (HG a HGa) as (Himg & Hown & _). split.
    - apply KK1; [exact Himg | | exact Hown | | exact (HnFPi a Himg)].
      + intros Hx. pose proof (xe_inG_xeG k a Hx) as Hx'. unfold xe_HA, ASRC in *. lia.
      + pose proof XE_ERR_S as HE. unfold xe_HA, ASRC in *. lia.
    - intros _. apply GWR. exact HGa. }
  assert (HMOD' : amodel_at B ly' St' W' mem' M').
  { refine (xe_amodel_tr ly St W mem ly' St' W' mem' m k (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m))
      ev HMOD _ _ _ _ _ _ Hev Hevw Hevb).
    - rewrite xe_set_nth_length. exact M1.
    - intros _. rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl). exact HSRC.
    - intros i Hi Hik. exact (xe_nth_set_ne k i (Some (CheckRep.set_held h H')) None (lm_hs m) Hik).
    - exact KS.
    - intros b Hb _. pose proof (xe_BL_cover cx m k b M1 Hb) as HbB.
      split; [exact (HBLnew _ HbB) | exact (KB _ HbB)].
    - exact KG. }
  (* the frame and the fake frame *)
  assert (Efr : frame_addr ly' 1 fpos = frame_addr ly 1 fpos).
  { destruct (ajournal_gx_inner_x segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as (memS & HJi & _).
    pose proof HJi as (_ & Hly & _). unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _).
    rewrite EF. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames St)).
  { pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & _ & _ & _ & _ & Hfrs0 & _).
    rewrite Hfrs0. left. reflexivity. }
  assert (Hin1' : In (1, fpos) (frames St')) by (rewrite HFR; exact Hin1).
  destruct (frames_bounds_x segs B ARx LAWS ly St [] W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1.
  pose proof (xe_div8 (frame_addr ly 1 fpos) ltac:(lia)) as HFF8.
  destruct (alx_frames _ _ ARx LAWS ly' St' [] W' mem' md' 1 fpos HAR' Hin1') as (_ & _ & HFP & HSP).
  rewrite Efr in HFP, HSP. change (fs_frame_bytes 1) with 128 in HFP, HSP. change (128 / 8) with 16 in HSP.
  assert (KFF : forall a, (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
      SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16) ->
      aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
  { intros a Ha. apply (KK5 1 fpos a Hin1).
    - unfold frame_rng, in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
      unfold shadow_addr, SHADOW_OFF. unfold SB in Ha. destruct Ha as [Ha | Ha]; [left | right]; lia.
    - intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq).
      cbn [fst snd] in Hra. pose proof (HAH _ Hq) as Hq'.
      pose proof (sep_block_frame_x segs B ARx LAWS ly St [] W mem md q n2 1 fpos HAR Hq' Hin1) as Hd.
      destruct (alx_blocks _ _ ARx LAWS ly St [] W mem md q n2 HAR Hq') as (_ & _ & _ & [Hh1 Hh2] & _).
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      unfold SB in Ha. destruct Ha as [Ha | Ha]; [lia | zlia]. }
  (* this function's journal: the callee's, lifted to G_fr, composed *)
  assert (HJcG : ajournal_gx_x segs B PST ARx G_fr AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] lx_CSHE_STK (lf_F cx)
      (blk_FP (alist_blks (hs_held h))) ly St [] W mem md [] ly' St' [] W' mem' md' kk).
  { apply (ajournal_gx_G_mono_x segs B PST ARx (xe_G k) G_fr); [|exact HJc].
    intros a Ha. apply HGs. pose proof (xe_inG_xeG k a Ha). unfold xe_HA, ASRC in *. lia. }
  assert (HFPprov : forall a, inFP (blk_FP (alist_blks (hs_held h))) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly St) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly St) a).
  { intros a (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq).
    cbn [fst snd] in Hra. pose proof (HAH _ Hq) as Hq'.
    destruct (HSEP2 (q, n2) (xe_held_in_model m k h Hh _ Hq)) as [Hno | Hfp].
    - right. exists q, n2. split; [exact Hq' | split; [exact Hno | exact Hra]].
    - left. split.
      + (* B's ablocks_sep names the block's request-size footprint, as blk_FP does *)
        apply Hfp. cbn [fst snd]. exact Hra.
      + exists q, n2. split; [exact Hq' | exact Hra]. }
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly St [] W mem md kk0
     lx_CSHE_STK (lf_F cx) AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] (blk_FP (alist_blks (hs_held h))) []
     ly' St' [] W' mem' md' kk HJ0 HJcG) as HJ2.
  assert (HJ2' : ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' St' [] W' mem' md' (kk0 + kk)).
  { apply HJ2.
    - unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, LLVMF_STK. lia.
    - lia.
    - unfold AX_XO. lia.
    - intros a (r & [<- | []] & Hra). left. cbn [fst snd] in Hra. unfold AX_AT, LLVMF_STK in *. lia.
    - exact HG.
    - exact HFPprov. }
  pose proof HJ2' as (_ & _ & (memS2 & HJi2 & _) & _).
  pose proof HJi2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  assert (HRO : rom_out segs B (xe_G k)).
  { intros a Ha. destruct (XRF_ROM_OUT a Ha) as (R1 & R2 & R3 & R4). split; [|exact (conj R2 (conj R3 R4))].
    intros Hx. apply R1. apply HGs. pose proof (xe_inG_xeG k a Hx). unfold xe_HA, ASRC in *. lia. }
  pose proof (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low (xe_G k) _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc HRO
    PST_ROM HRV) as HRV'.
  pose proof (xm_cost_set k (lm_hs m) h H' Hkl Hh Hrecs) as Ecost.
  (* the post *)
  exists M'. split; [reflexivity|].
  unfold xe_inv_x.
  split; [exists (kk0 + kk); exact HJ2'|].
  split.
  { rewrite Efr. apply (xe_bxframe_tr cx _ W mem W' mem' HFA HFhi).
    - intros a Ha _ Hat. destruct (Z_lt_le_dec a (lf_F cx + AX_XO)) as [Hl | Hl].
      + apply KK3; [lia | exact Hat].
      + apply KK2; [unfold AX_XO in *; lia | unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *; lia].
    - apply xe_awr_pres. intros x Hx. apply Hpres2. unfold LLVMF_STK. lia.
    - exact KFF.
    - apply xe_awr_pres. intros x Hx. exact (proj1 (HFP x Hx)).
    - apply xe_awr_pres. intros x Hx.
      replace x with (shadow_addr (frame_addr ly 1 fpos) + (x - (SB + frame_addr ly 1 fpos / 8)))
        by (unfold shadow_addr, SHADOW_OFF, SB; lia).
      apply (HSP (x - (SB + frame_addr ly 1 fpos / 8))). lia. }
  split.
  { (* the fake frame's flag word, read by view *)
    rewrite Efr, (lx_fla_kept_x HJc). unfold sv8 in HFLW |- *. apply (xe_vm_view W W' mem mem'); [|exact HFLW].
    intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. apply KFF. left. lia. }
  split; [rewrite Efr; exact HFAeq|].
  split; [exact HMOD'|].
  split.
  { apply (xe_ainput_tr cx ly St W mem ly' St' W' mem' HIN (eq_sym HlenP)).
    intros Hn. assert (Hb : In (c_p cx, c_n cx) (xe_BL cx m k)).
    { unfold xe_BL. apply in_or_app. left. unfold input_blks.
      rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    exact (conj (HBLnew _ Hb) (KB _ Hb)). }
  split; [exact HRV'|].
  split; [exact (xe_jt_tr W mem W' mem' HRV HRV' HJT)|].
  split.
  { split; [exists R0; exact HP0'|]. intros b Hb. apply HSEP2.
    exact (xe_model_sub m k h H' ev Hh Hv Hcap Hrecs b Hb). }
  split; [intros rest Hr; apply HFRM; exact (perm_trans (HBF rest Hr) (HSPL rest))|].
  split; [exact (eq_trans (xe_set_nth_length k _ (lm_hs m)) M1)|].
  split.
  { intros j Hj. specialize (Hevo j Hj).
    change (lm_hs M') with (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
    assert (Hn0 : hl_n H' = 0) by (unfold hl_n; rewrite Hrecs; reflexivity).
    destruct (Nat.eq_dec j k) as [-> | Hjk].
    - rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl). rewrite Hh in Hevo.
      destruct Hevo as [E | (h0 & H0 & E1 & E2 & Hle)].
      + right. exists h, H'. split; [symmetry; exact E|]. split; [reflexivity|]. rewrite Hn0. unfold hl_n. lia.
      + right. exists h0, H'. split; [exact E1|]. injection E2 as E2. split; [rewrite E2; reflexivity|].
        rewrite Hn0. unfold hl_n. lia.
    - rewrite (xe_nth_set_ne k j (Some (CheckRep.set_held h H')) None (lm_hs m) Hjk). exact Hevo. }
  split; [exact Ek|]. split; [exact EG|]. split; [exact Ees|].
  split.
  { change (lx_ctl_ev (lm_c m) ev = lx_ctl_ev (lm_c m0) ev). rewrite Ec. reflexivity. }
  split; [exact EO|]. split; [exact Emx|]. split; [exact Ecap|]. split; [exact Eout|].
  split; [exact Egn|]. split; [exact Enfd|].
  split; [rewrite HFR; exact Hfrs|].
  change (lx_ends_cost (lm_hs M')) with (lx_ends_cost (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m))).
  rewrite Ecost.
  split.
  { pose proof (mo_le_trans MT MLM _ _ _ _ _ Hmle HMLE) as X. unfold W_bx_defs.lx_cshe_cost in X.
    replace (lx_ends_cost (lm_hs m0) - (lx_ends_cost (lm_hs m) - hl_n (hs_held h) * mo_free MT))
      with (lx_ends_cost (lm_hs m0) - lx_ends_cost (lm_hs m) + hl_n (hs_held h) * mo_free MT) by lia.
    exact X. }
  split.
  { apply (mo_ok_step MT MLM St St' (hl_n (hs_held h) * mo_free MT)); [|exact HMLE].
    replace (hl_n (hs_held h) * mo_free MT + (lx_ends_cost (lm_hs m) - hl_n (hs_held h) * mo_free MT))
      with (lx_ends_cost (lm_hs m)) by lia. exact Hmok. }
  split.
  { intros j Hj. change (lm_hs M') with (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
    destruct (Nat.eq_dec j k) as [-> | Hjk].
    - rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl).
      cbn [lx_ends_slot_ok CheckRep.set_held hs_held].
      split; [exact HND | unfold hl_n; rewrite Hrecs; cbn [length Z.of_nat]; lia].
    - rewrite (xe_nth_set_ne k j (Some (CheckRep.set_held h H')) None (lm_hs m) Hjk). exact (Hsok j Hj). }
  split; [exact HAT|]. split; [lia|].
  split.
  { apply (xe_vm_view W W' mem mem'); [|exact HNO]. intros x Hx. apply KK3; unfold AX_NORDER, AX_XO, AX_AT in *; lia. }
  split; [exact Hnord|].
  split.
  { apply (xe_vm_view W W' mem mem'); [|exact HGS8]. intros x Hx. apply KK3; unfold AX_GS8, AX_XO, AX_AT in *; lia. }
  split.
  { intros i Hi. destruct (Hord i Hi) as [Hv1 Hb1]. split; [|exact Hb1].
    apply (xe_vm_view W W' mem mem'); [|exact Hv1]. intros x Hx. apply KK3; unfold AX_ORDER, AX_XO, AX_AT in *; lia. }
  split; [exact HNPa|].
  (* check_shape_ends only freed: the count after it is at most the count before *)
  apply (cnt_ok_pk_mono RP (fun _ => 0%nat) (fun _ => 0%nat) (ablocks B ly St) (ablocks B ly' St')); [|exact HCNi].
  intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP0'), (ReplyCnt.acnt_perm P _ _ (perm_trans HPz0 (HSPL R0))).
  rewrite (ReplyCnt.acnt_app P (lx_cshe_ds_blks ds)). cbv beta. lia.
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the model after a check_shape_ends call, at a world relation R, with the two
   journal lemmas it reads (lx_fla_kept_x, xe_keeps_of_journal_x): ajournal_gx_x -> ajournal_gx_xR R, xe_inv_x ->
   xe_inv_xR R, the kit's journal lemmas -> their _xR twins (ajournal_gx_sub_xR takes R_trans).  The strict texts
   above keep their proofs. ---- *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
(* :169 lx_fla_kept_x *)
Lemma lx_fla_kept_xR : forall {G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k},
  ajournal_gx_xR segs B PST ARx R G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 own ly2 S2 [] W2 m2 md2 k ->
  forall cid pos, flag_addr ly2 cid pos = flag_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _) cid pos.
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold flag_addr. rewrite EF. reflexivity.
Qed.
(* :265 xe_keeps_of_journal_x *)
Lemma xe_keeps_of_journal_xR : forall G FP F AT W mem md ly S ly' S' W' mem' md' kk,
  gx_ok segs B G ->
  ~ YI16.sink_open_fp FP ->
  ajournal_gx_xR segs B PST ARx R G AX_XO [(AT, AT + 8)] lx_CSHE_STK F FP ly S [] W mem md [] ly' S' [] W' mem' md' kk ->
  xe_kept_by G FP F AT W mem W' mem' ly S ly' S'.
Proof.
  intros G FP F AT W mem md ly S ly' S' W' mem' md' kk HGg Hsk HJX.
  pose proof HJX as (_ & _ & _ & Hout).
  destruct (ajournal_gx_inner_xR segs B PST ARx G _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJX) as (memS & HJ & Hmg).
  destruct HJ as (HAR' & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres &
    Hstatic & F5 & HQT).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  assert (HnG : forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
  { intros a Ha Hg. apply Hmg. rewrite unsigned_lit_small by lia. exact Hg. }
  assert (Hlow : forall a, inG G a -> 0 <= a < kLowMemEnd) by (intros a Ha; exact (Hsl a (proj1 (HGg a Ha)))).
  split.
  { intros a Hi HnGa Hno He _. rewrite (F3 a Hi Hno He (HPST a Hi) (fp_spares_closed FP a Hsk)).
    apply HnG; [pose proof (Hsl a Hi); lia | exact HnGa]. }
  split.
  { intros a Ha Hn. rewrite (F1 a Ha ltac:(lia)). apply HnG; [lia|].
    intros Hg. pose proof (Hlow a Hg). lia. }
  split.
  { intros a Ha Hn. apply Hout; [exact Ha|]. intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn in Hra. lia. }
  split.
  { intros p n i H1 H2 Hi Hnf. rewrite (F2 p n i H1 H2 Hi Hnf).
    destruct (alx_blocks _ _ ARx LAWS ly' S' [] W' mem' md' p n HAR' H2) as (_ & H4096 & Hce & _).
    apply HnG; [lia|]. intros Hg. destruct (HGg _ Hg) as [Himg _].
    refine (proj2 (alx_client_img _ _ ARx LAWS ly' S' [] W' mem' md' (p + i) HAR' _) Himg).
    left. exists p, n. split; [exact H2 | lia]. }
  split.
  { intros cid pos a Hin Hr Hnf. rewrite (F4 cid pos a Hin Hr Hnf).
    assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hin).
    assert (Efr : frame_addr ly' cid pos = frame_addr ly cid pos).
    { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    destruct (frames_bounds_x segs B ARx LAWS ly' S' [] W' mem' md' cid pos HAR' Hin') as (Hf0 & Hfc & _).
    rewrite Efr in Hf0, Hfc.
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr].
    - apply HnG; [lia|]. intros Hg. destruct (HGg _ Hg) as [Himg _].
      refine (proj2 (alx_client_img _ _ ARx LAWS ly' S' [] W' mem' md' a HAR' _) Himg).
      right. left. exists cid, pos. rewrite Efr. split; [exact Hin' | lia].
    - pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(lia)) as Hs1.
      pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2.
      pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hfs) as Hs3.
      apply HnG; [lia|]. intros Hg. pose proof (Hlow a Hg). lia. }
  intros a Ha. apply Hpres. lia.
Qed.
(* :884 xe_model_after_x *)
Lemma xe_model_after_xR : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md
    (k : nat) h (H' : hlist) (ds : list (Z * list byte)) (c : Z) ly' St' W' mem' md' kk,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  xe_inv_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  ajournal_gx_xR segs B PST ARx R (xe_G k) AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] lx_CSHE_STK (lf_F cx)
    (blk_FP (list_blks (hs_held h))) ly St [] W mem md [] ly' St' [] W' mem' md' kk ->
  asrc_at B ly' St' W' mem' (xe_HA k) (CheckRep.set_held h H') ->
  hl_v H' = hl_v (hs_held h) -> hl_cap H' = hl_cap (hs_held h) ->
  NoDup (CheckRep.texts H') -> hl_recs H' = [] ->
  Permutation (hl_recs (hs_held h)) ds ->
  val_mem segs (mrestrict (w_H W') mem') (lf_F cx + AX_AT) 8 (A + c) ->
  0 <= c -> A + c <= Z.of_nat (length (lm_O m0)) ->
  (forall rest, Permutation (ablocks B ly St) (lx_cshe_ds_blks ds ++ rest) ->
     Permutation (ablocks B ly' St') rest) ->
  frames St' = frames St ->
  mo_le MT St St' (lx_cshe_cost (hs_held h)) ->
  NP St' ->
  exists m', lm_hs m' = xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m) /\
    xe_inv_xR R cx fpos ly3 S3 m0 norder ord (A + c) ly' St' m' W' mem' md'.
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md k h H' ds c ly' St' W' mem' md' kk
    HB HI Hk Hh HJc HSRC Hv Hcap HND Hrecs HPds HAT Hc HAc HFRM HFR HMLE HNPa.
  destruct HI as ((kk0 & HJ0) & HFA & HFLW & HFAeq & HMOD & HIN & HRV & HJT & HSEP & HBF & Hlen & Hevo & Ek & EG & Ees & Ec &
    EO & Emx & Ecap & Eout & Egn & Enfd & Hfrs & Hmle & Hmok & Hsok & HATv & HA & HNO & Hnord & HGS8 & Hord & HNPi & HCNi).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  pose proof HB as (HAI0 & HPRE0).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  (* the two AR states, slot k and its held blocks *)
  pose proof (ajournal_gx_AR_xR segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ0) as HAR.
  pose proof (ajournal_gx_AR_xR segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as HAR'.
  pose proof HMOD as (M1 & M2 & _).
  destruct (xe_nth_some k (lm_hs m) h Hh) as [Hhe Hkl].
  pose proof (M2 k Hk) as HSk. unfold aslot in HSk. rewrite Hh in HSk.
  assert (HAH : forall b, In b (alist_blks (hs_held h)) -> In b (ablocks B ly St)).
  { intros b Hb. apply (xe_asrc_blks _ _ _ _ _ _ HSk). unfold asrc_blks. right.
    apply in_or_app. right. apply in_or_app. right. exact Hb. }
  change (list_blks (hs_held h)) with (alist_blks (hs_held h)) in HJc.
  assert (HFPc : ~ YI16.sink_open_fp (blk_FP (alist_blks (hs_held h)))).
  { apply sink_closed_pos. unfold blk_FP. apply Forall_forall. intros r Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    destruct (alx_blocks _ _ ARx LAWS ly St [] W mem md p n HAR (HAH _ Hb)) as (_ & H4096 & _). cbn [fst]. lia. }
  assert (HGk : gx_ok segs B (xe_G k)).
  { apply (gx_ok_sub segs B (xe_G k) G_fr); [|exact HG]. intros a Ha. apply HGs.
    pose proof (xe_inG_xeG k a Ha). unfold xe_HA, ASRC in *. lia. }
  destruct (xe_keeps_of_journal_xR (xe_G k) (blk_FP (alist_blks (hs_held h))) (lf_F cx) (lf_F cx + AX_AT)
    W mem md ly St ly' St' W' mem' md' kk HGk HFPc HJc) as (KK1 & KK2 & KK3 & KK4 & KK5 & KK6).
  assert (HnFPi : forall a, in_img segs a -> ~ inFP (blk_FP (alist_blks (hs_held h))) a).
  { intros a Hi (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    cbn [fst snd] in Hra.
    refine (proj2 (alx_client_img _ _ ARx LAWS ly St [] W mem md a HAR _) Hi). left. exists p, n.
    split; [exact (HAH _ Hb) | lia]. }
  (* the blocks: the call frees the held records, keeps every other block of the model *)
  destruct HSEP as ((R0 & HPz0) & HSEP2).
  pose proof (xe_mblks_split cx m k h R0 Hh) as HS1.
  assert (HNDL : List.NoDup (alist_blks (hs_held h) ++ xe_skh h ++ xe_BL cx m k ++ R0)).
  { eapply Permutation_NoDup; [|exact (xe_nodup_x ly St W mem md HAR)]. eapply perm_trans; [exact HPz0 | exact HS1]. }
  destruct (ERR ly' St' [] W' mem' md' HAR') as ((ev & Hev & Hevb) & Hevw).
  set (M' := xe_set_slot m k (Some (CheckRep.set_held h H')) ev).
  assert (Hh' : nth k (lm_hs M') None = Some (CheckRep.set_held h H'))
    by (exact (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl)).
  assert (EBL : xe_BL cx M' k = xe_BL cx m k).
  { unfold xe_BL, M', xe_set_slot. cbn [lm_G lm_es lm_hs lm_cap lm_out]. rewrite xe_set_set. reflexivity. }
  assert (HAHs : Permutation (alist_blks (hs_held h)) (lx_cshe_ds_blks ds ++ alist_blks H')).
  { unfold alist_blks at 2. rewrite Hv, Hcap, Hrecs. cbn [map]. rewrite app_nil_r.
    unfold alist_blks, lx_cshe_ds_blks.
    eapply perm_trans; [apply Permutation_app_head; apply Permutation_map; exact HPds | apply Permutation_app_comm]. }
  assert (HSPL : forall Rl, Permutation (input_blks cx ++ model_blks m ++ Rl)
      (lx_cshe_ds_blks ds ++ (input_blks cx ++ model_blks M' ++ Rl))).
  { intros Rl. pose proof (xe_mblks_split cx M' k (CheckRep.set_held h H') Rl Hh') as X. rewrite EBL in X.
    exact (xe_perm_comb _ _ _ _ _ _ _ _ (xe_mblks_split cx m k h Rl Hh) X HAHs). }
  assert (HP0' : Permutation (ablocks B ly' St') (input_blks cx ++ model_blks M' ++ R0))
    by (apply HFRM; exact (perm_trans HPz0 (HSPL R0))).
  pose proof (xe_mblks_split cx M' k (CheckRep.set_held h H') R0 Hh') as HS1'. rewrite EBL in HS1'.
  assert (HBLold : forall b, In b (xe_BL cx m k) -> In b (ablocks B ly St)).
  { intros b Hb. eapply Permutation_in; [exact (Permutation_sym HPz0)|].
    eapply Permutation_in; [exact (Permutation_sym HS1)|].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (HBLnew : forall b, In b (xe_BL cx m k) -> In b (ablocks B ly' St')).
  { intros b Hb. eapply Permutation_in; [exact (Permutation_sym HP0')|].
    eapply Permutation_in; [exact (Permutation_sym HS1')|].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  (* the bytes the model reads, kept: blocks, globals, the other slots *)
  assert (KB : forall b, In b (xe_BL cx m k) -> xe_bk W mem W' mem' b).
  { intros [p n] Hb. unfold xe_bk. cbn [fst snd]. intros a Ha.
    pose proof (HBLold _ Hb) as Hin. pose proof (HBLnew _ Hb) as Hin'.
    split.
    - replace a with (p + (a - p)) by lia. apply (KK4 p n); [exact Hin | exact Hin' | lia |].
      intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq). cbn [fst snd] in Hra.
      assert (Hne : (q, n2) <> (p, n)).
      { intros E. rewrite E in Hq.
        exact (xe_nodup_app _ _ _ HNDL Hq ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)). }
      pose proof (sep_blocks_x segs B ARx LAWS ly St [] W mem md q n2 p n HAR (HAH _ Hq) Hin Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    - intros _. destruct (alx_blocks _ _ ARx LAWS ly' St' [] W' mem' md' p n HAR' Hin') as (_ & _ & _ & _ & Hpr & _).
      apply xe_wr_of_present. exact (proj1 (Hpr a Ha)). }
  assert (KG : forall a, inG XE_GLOBS a -> abyte_kept W mem W' mem' a).
  { intros a Ha. destruct (xe_globs_rng a Ha) as (Hlo & Hout). pose proof (xe_globs_G a Ha) as HGa.
    destruct (HG a HGa) as (Himg & Hown & _). split.
    - apply KK1; [exact Himg | | exact Hown | | exact (HnFPi a Himg)].
      + intros Hx. pose proof (xe_inG_xeG k a Hx) as Hx'. unfold xe_HA, ASRC in *. lia.
      + pose proof XE_ERR_HI. lia.
    - intros _. apply GWR. exact HGa. }
  assert (KS : forall i, (i < 4)%nat -> i <> k -> forall a, xe_HA i <= a < xe_HA i + ASRC ->
      abyte_kept W mem W' mem' a).
  { intros i Hi Hik a Ha.
    assert (HGa : inG G_fr a) by (apply HGs; unfold xe_HA, ASRC in *; lia).
    destruct (HG a HGa) as (Himg & Hown & _). split.
    - apply KK1; [exact Himg | | exact Hown | | exact (HnFPi a Himg)].
      + intros Hx. pose proof (xe_inG_xeG k a Hx) as Hx'. unfold xe_HA, ASRC in *. lia.
      + pose proof XE_ERR_S as HE. unfold xe_HA, ASRC in *. lia.
    - intros _. apply GWR. exact HGa. }
  assert (HMOD' : amodel_at B ly' St' W' mem' M').
  { refine (xe_amodel_tr ly St W mem ly' St' W' mem' m k (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m))
      ev HMOD _ _ _ _ _ _ Hev Hevw Hevb).
    - rewrite xe_set_nth_length. exact M1.
    - intros _. rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl). exact HSRC.
    - intros i Hi Hik. exact (xe_nth_set_ne k i (Some (CheckRep.set_held h H')) None (lm_hs m) Hik).
    - exact KS.
    - intros b Hb _. pose proof (xe_BL_cover cx m k b M1 Hb) as HbB.
      split; [exact (HBLnew _ HbB) | exact (KB _ HbB)].
    - exact KG. }
  (* the frame and the fake frame *)
  assert (Efr : frame_addr ly' 1 fpos = frame_addr ly 1 fpos).
  { destruct (ajournal_gx_inner_xR segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as (memS & HJi & _).
    pose proof HJi as (_ & Hly & _). unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _).
    rewrite EF. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames St)).
  { pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & _ & _ & _ & _ & Hfrs0 & _).
    rewrite Hfrs0. left. reflexivity. }
  assert (Hin1' : In (1, fpos) (frames St')) by (rewrite HFR; exact Hin1).
  destruct (frames_bounds_x segs B ARx LAWS ly St [] W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1.
  pose proof (xe_div8 (frame_addr ly 1 fpos) ltac:(lia)) as HFF8.
  destruct (alx_frames _ _ ARx LAWS ly' St' [] W' mem' md' 1 fpos HAR' Hin1') as (_ & _ & HFP & HSP).
  rewrite Efr in HFP, HSP. change (fs_frame_bytes 1) with 128 in HFP, HSP. change (128 / 8) with 16 in HSP.
  assert (KFF : forall a, (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
      SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16) ->
      aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
  { intros a Ha. apply (KK5 1 fpos a Hin1).
    - unfold frame_rng, in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
      unfold shadow_addr, SHADOW_OFF. unfold SB in Ha. destruct Ha as [Ha | Ha]; [left | right]; lia.
    - intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq).
      cbn [fst snd] in Hra. pose proof (HAH _ Hq) as Hq'.
      pose proof (sep_block_frame_x segs B ARx LAWS ly St [] W mem md q n2 1 fpos HAR Hq' Hin1) as Hd.
      destruct (alx_blocks _ _ ARx LAWS ly St [] W mem md q n2 HAR Hq') as (_ & _ & _ & [Hh1 Hh2] & _).
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      unfold SB in Ha. destruct Ha as [Ha | Ha]; [lia | zlia]. }
  (* this function's journal: the callee's, lifted to G_fr, composed *)
  assert (HJcG : ajournal_gx_xR segs B PST ARx R G_fr AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] lx_CSHE_STK (lf_F cx)
      (blk_FP (alist_blks (hs_held h))) ly St [] W mem md [] ly' St' [] W' mem' md' kk).
  { apply (ajournal_gx_G_mono_xR segs B PST ARx (xe_G k) G_fr); [|exact HJc].
    intros a Ha. apply HGs. pose proof (xe_inG_xeG k a Ha). unfold xe_HA, ASRC in *. lia. }
  assert (HFPprov : forall a, inFP (blk_FP (alist_blks (hs_held h))) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly St) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly St) a).
  { intros a (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq).
    cbn [fst snd] in Hra. pose proof (HAH _ Hq) as Hq'.
    destruct (HSEP2 (q, n2) (xe_held_in_model m k h Hh _ Hq)) as [Hno | Hfp].
    - right. exists q, n2. split; [exact Hq' | split; [exact Hno | exact Hra]].
    - left. split.
      + (* B's ablocks_sep names the block's request-size footprint, as blk_FP does *)
        apply Hfp. cbn [fst snd]. exact Hra.
      + exists q, n2. split; [exact Hq' | exact Hra]. }
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly St [] W mem md kk0
     lx_CSHE_STK (lf_F cx) AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] (blk_FP (alist_blks (hs_held h))) []
     ly' St' [] W' mem' md' kk HJ0 HJcG) as HJ2.
  assert (HJ2' : ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' St' [] W' mem' md' (kk0 + kk)).
  { apply HJ2.
    - unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, LLVMF_STK. lia.
    - lia.
    - unfold AX_XO. lia.
    - intros a (r & [<- | []] & Hra). left. cbn [fst snd] in Hra. unfold AX_AT, LLVMF_STK in *. lia.
    - exact HG.
    - exact HFPprov. }
  pose proof HJ2' as (_ & _ & (memS2 & HJi2 & _) & _).
  pose proof HJi2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  assert (HRO : rom_out segs B (xe_G k)).
  { intros a Ha. destruct (XRF_ROM_OUT a Ha) as (R1 & R2 & R3 & R4). split; [|exact (conj R2 (conj R3 R4))].
    intros Hx. apply R1. apply HGs. pose proof (xe_inG_xeG k a Hx). unfold xe_HA, ASRC in *. lia. }
  pose proof (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low (xe_G k) _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc HRO
    PST_ROM HRV) as HRV'.
  pose proof (xm_cost_set k (lm_hs m) h H' Hkl Hh Hrecs) as Ecost.
  (* the post *)
  exists M'. split; [reflexivity|].
  unfold xe_inv_xR.
  split; [exists (kk0 + kk); exact HJ2'|].
  split.
  { rewrite Efr. apply (xe_bxframe_tr cx _ W mem W' mem' HFA HFhi).
    - intros a Ha _ Hat. destruct (Z_lt_le_dec a (lf_F cx + AX_XO)) as [Hl | Hl].
      + apply KK3; [lia | exact Hat].
      + apply KK2; [unfold AX_XO in *; lia | unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *; lia].
    - apply xe_awr_pres. intros x Hx. apply Hpres2. unfold LLVMF_STK. lia.
    - exact KFF.
    - apply xe_awr_pres. intros x Hx. exact (proj1 (HFP x Hx)).
    - apply xe_awr_pres. intros x Hx.
      replace x with (shadow_addr (frame_addr ly 1 fpos) + (x - (SB + frame_addr ly 1 fpos / 8)))
        by (unfold shadow_addr, SHADOW_OFF, SB; lia).
      apply (HSP (x - (SB + frame_addr ly 1 fpos / 8))). lia. }
  split.
  { (* the fake frame's flag word, read by view *)
    rewrite Efr, (lx_fla_kept_xR HJc). unfold sv8 in HFLW |- *. apply (xe_vm_view W W' mem mem'); [|exact HFLW].
    intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. apply KFF. left. lia. }
  split; [rewrite Efr; exact HFAeq|].
  split; [exact HMOD'|].
  split.
  { apply (xe_ainput_tr cx ly St W mem ly' St' W' mem' HIN (eq_sym HlenP)).
    intros Hn. assert (Hb : In (c_p cx, c_n cx) (xe_BL cx m k)).
    { unfold xe_BL. apply in_or_app. left. unfold input_blks.
      rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    exact (conj (HBLnew _ Hb) (KB _ Hb)). }
  split; [exact HRV'|].
  split; [exact (xe_jt_tr W mem W' mem' HRV HRV' HJT)|].
  split.
  { split; [exists R0; exact HP0'|]. intros b Hb. apply HSEP2.
    exact (xe_model_sub m k h H' ev Hh Hv Hcap Hrecs b Hb). }
  split; [intros rest Hr; apply HFRM; exact (perm_trans (HBF rest Hr) (HSPL rest))|].
  split; [exact (eq_trans (xe_set_nth_length k _ (lm_hs m)) M1)|].
  split.
  { intros j Hj. specialize (Hevo j Hj).
    change (lm_hs M') with (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
    assert (Hn0 : hl_n H' = 0) by (unfold hl_n; rewrite Hrecs; reflexivity).
    destruct (Nat.eq_dec j k) as [-> | Hjk].
    - rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl). rewrite Hh in Hevo.
      destruct Hevo as [E | (h0 & H0 & E1 & E2 & Hle)].
      + right. exists h, H'. split; [symmetry; exact E|]. split; [reflexivity|]. rewrite Hn0. unfold hl_n. lia.
      + right. exists h0, H'. split; [exact E1|]. injection E2 as E2. split; [rewrite E2; reflexivity|].
        rewrite Hn0. unfold hl_n. lia.
    - rewrite (xe_nth_set_ne k j (Some (CheckRep.set_held h H')) None (lm_hs m) Hjk). exact Hevo. }
  split; [exact Ek|]. split; [exact EG|]. split; [exact Ees|].
  split.
  { change (lx_ctl_ev (lm_c m) ev = lx_ctl_ev (lm_c m0) ev). rewrite Ec. reflexivity. }
  split; [exact EO|]. split; [exact Emx|]. split; [exact Ecap|]. split; [exact Eout|].
  split; [exact Egn|]. split; [exact Enfd|].
  split; [rewrite HFR; exact Hfrs|].
  change (lx_ends_cost (lm_hs M')) with (lx_ends_cost (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m))).
  rewrite Ecost.
  split.
  { pose proof (mo_le_trans MT MLM _ _ _ _ _ Hmle HMLE) as X. unfold W_bx_defs.lx_cshe_cost in X.
    replace (lx_ends_cost (lm_hs m0) - (lx_ends_cost (lm_hs m) - hl_n (hs_held h) * mo_free MT))
      with (lx_ends_cost (lm_hs m0) - lx_ends_cost (lm_hs m) + hl_n (hs_held h) * mo_free MT) by lia.
    exact X. }
  split.
  { apply (mo_ok_step MT MLM St St' (hl_n (hs_held h) * mo_free MT)); [|exact HMLE].
    replace (hl_n (hs_held h) * mo_free MT + (lx_ends_cost (lm_hs m) - hl_n (hs_held h) * mo_free MT))
      with (lx_ends_cost (lm_hs m)) by lia. exact Hmok. }
  split.
  { intros j Hj. change (lm_hs M') with (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
    destruct (Nat.eq_dec j k) as [-> | Hjk].
    - rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl).
      cbn [lx_ends_slot_ok CheckRep.set_held hs_held].
      split; [exact HND | unfold hl_n; rewrite Hrecs; cbn [length Z.of_nat]; lia].
    - rewrite (xe_nth_set_ne k j (Some (CheckRep.set_held h H')) None (lm_hs m) Hjk). exact (Hsok j Hj). }
  split; [exact HAT|]. split; [lia|].
  split.
  { apply (xe_vm_view W W' mem mem'); [|exact HNO]. intros x Hx. apply KK3; unfold AX_NORDER, AX_XO, AX_AT in *; lia. }
  split; [exact Hnord|].
  split.
  { apply (xe_vm_view W W' mem mem'); [|exact HGS8]. intros x Hx. apply KK3; unfold AX_GS8, AX_XO, AX_AT in *; lia. }
  split.
  { intros i Hi. destruct (Hord i Hi) as [Hv1 Hb1]. split; [|exact Hb1].
    apply (xe_vm_view W W' mem mem'); [|exact Hv1]. intros x Hx. apply KK3; unfold AX_ORDER, AX_XO, AX_AT in *; lia. }
  split; [exact HNPa|].
  (* check_shape_ends only freed: the count after it is at most the count before *)
  apply (cnt_ok_pk_mono RP (fun _ => 0%nat) (fun _ => 0%nat) (ablocks B ly St) (ablocks B ly' St')); [|exact HCNi].
  intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP0'), (ReplyCnt.acnt_perm P _ _ (perm_trans HPz0 (HSPL R0))).
  rewrite (ReplyCnt.acnt_app P (lx_cshe_ds_blks ds)). cbv beta. lia.
Qed.
End wR.
(* the value of a register index, as a numeral (W_img.v's zlit idiom) *)
Ltac xc_bvz :=
  lazymatch goal with
  | |- acallee_saved ?x => let v := eval vm_compute in x in (change x with v; unfold acallee_saved; lia)
  | |- ?x <> 1 => let v := eval vm_compute in x in (change x with v; lia)
  end.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): xc_inv_mat_x at a world relation R (xe_inv_xR, ajournal_gx_materialize_xR);
   xc_inv_mat_x below is it at wle *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
(* :1092 xc_inv_mat_x *)
Lemma xc_inv_mat_xR : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md X,
  xe_inv_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_inv_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md X ((kk & HJ) & REST).
  split; [|exact REST]. exists kk.
  eapply (ajournal_gx_materialize_xR segs B PST ARx LAWS pa_segs_low). exact HJ.
Qed.
End wR.
(* the invariant across the step's materialization of the model *)
Lemma xc_inv_mat_x : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md X,
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem (with_vm_backing (m_vm_lazy md) X md).
Proof. eapply (xc_inv_mat_xR (@wle segs)); wle_inst. Qed.
(* the live blocks are distinct (they are pairwise disjoint and each covers a byte) *)
Lemma xc_blocks_nodup_x : forall ly S (W : world segs) mem md, ARx ly S [] W mem md ->
  List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _].
  apply pairwise_app_l in Hp as [Hp _].
  apply (xc_nodup_of_pairwise _ Hp).
  apply Forall_forall. intros [p nn] Hin.
  pose proof (BLKN ly S [] W mem md p nn HAR Hin) as Hn.
  cbn [snd]. lia.
Qed.
(* the stream's buffer is none of the source's blocks *)
Lemma xc_out_apart_x : forall cx m ly S (W : world segs) mem md (k : nat) h,
  ARx ly S [] W mem md -> ablocks_sep B fr_FP cx m ly S ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h -> lm_cap m <> 0 ->
  ~ In (lm_out m) (hs_blocks h).
Proof.
  intros cx m ly S W mem md k h HAR (HPm & _) Hk4 Hh Hcap Hin.
  destruct (xc_hsb_in h (lm_out m) Hin) as (nn & Hnn).
  destruct HPm as (rest & HP).
  assert (Hlen : (k < length (lm_hs m))%nat).
  { destruct (Nat.lt_ge_cases k (length (lm_hs m))) as [Hlt | Hge]; [exact Hlt|].
    rewrite (nth_overflow _ _ Hge) in Hh. discriminate Hh. }
  assert (Hslot : In (lm_out m, nn) (concat (map slot_blks (lm_hs m)))).
  { apply in_concat. exists (slot_blks (Some h)). split.
    - rewrite <- Hh. exact (in_map slot_blks (lm_hs m) (nth k (lm_hs m) None) (nth_In _ None Hlen)).
    - cbn [slot_blks]. exact Hnn. }
  assert (Hout : In (lm_out m, lm_cap m) (aout_blks (lm_cap m) (lm_out m))).
  { unfold aout_blks. destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; [exfalso; exact (Hcap E)|].
    left. reflexivity. }
  assert (I1 : In (lm_out m, nn) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. left.
    unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hslot. }
  assert (I2 : In (lm_out m, lm_cap m) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. left.
    unfold model_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hout. }
  pose proof (BLKN ly S [] W mem md _ _ HAR I1) as Hn1.
  pose proof (BLKN ly S [] W mem md _ _ HAR I2) as Hn2.
  destruct (Z.eq_dec nn (lm_cap m)) as [Ene | Ene].
  - (* the same pair twice: the model's block list holds it once *)
    subst nn. exfalso.
    assert (HND : List.NoDup (ablocks B ly S)) by exact (xc_blocks_nodup_x ly S W mem md HAR).
    assert (HNDm : List.NoDup (input_blks cx ++ model_blks m ++ rest))
      by exact (Permutation_NoDup HP HND).
    apply List.NoDup_app_remove_l in HNDm. apply List.NoDup_app_remove_r in HNDm.
    unfold model_blks in HNDm. apply List.NoDup_cons_iff in HNDm as (_ & HNDm).
    apply List.NoDup_app_remove_l in HNDm.
    destruct (in_split _ _ Hslot) as (l1 & l2 & Esplit).
    rewrite Esplit, <- app_assoc in HNDm. cbn [app] in HNDm.
    apply NoDup_remove_2 in HNDm.
    apply HNDm. apply in_or_app. right. apply in_or_app. right. exact Hout.
  - pose proof (sep_blocks_x segs B ARx LAWS ly S [] W mem md _ _ _ _ HAR I1 I2
      ltac:(intros E; injection E as E1; exact (Ene E1))) as Hd.
    pose proof (req_size_pos nn ltac:(lia)) as [Hq1 _].
    pose proof (req_size_pos (lm_cap m) ltac:(lia)) as [Hq2 _].
    unfold YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* ---------------- (3) the call site ---------------- *)
(* ---- one call of check_shape_ends at the slot the inner loop stands on: the contract at the slot's own G,
   its journal composed into this function's, and the model's slot replaced ---- *)
Lemma xe_call_x : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) n h,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k n regs ->
  getr regs 10 = w64 (xe_HA k) -> getr regs 11 = w64 (VAL AX_lit_empty) ->
  getr regs 12 = w64 (lf_F cx + AX_AT) ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A <> None ->
  SRr segs W (cfg_at segs (BASE + AX_call) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (m' : lmod) (H' : hlist) (A1 : Z),
       c' = cfg_at segs (BASE + AX_adv) regs' mem' md' /\
       xe_inv_x cx fpos ly3 S3 m0 norder ord A1 ly' S' m' W' mem' md' /\
       xe_regs_slot cx i k n regs' /\
       hl_recs H' = [] /\
       lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A = Some (hl_recs H', A1) /\
       lm_hs m' = xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k n h HB HI HR R10 R11 R12 Hk4 Hh Hnone.
  (* ---- the frame's geometry, from the contract's entry ---- *)
  pose proof HB as HBc. destruct HBc as (HAI & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo0 & Hshi0 & H47 & _ & Htop0 & Htop1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  assert (HFmod : lf_F cx mod 32 = 0).
  { pose proof (Z.div_mod (spZ (c_regs cx) - 320) 32 ltac:(lia)) as D32.
    replace (lf_F cx) with (((spZ (c_regs cx) - 320) / 32) * 32) by lia. apply Z_mod_mult. }
  assert (HF64 : 0 <= lf_F cx < 2 ^ 64) by lia.
  destruct xe_vals as (Egone & Enout & Eoutv & Egs & Hlit).
  assert (Egsv : rg_s fr_RG = 6131296) by (vm_compute; reflexivity).
  (* ---- the jal at 0x84cf0 ---- *)
  unfold cfg_at.
  eapply (SRr_step segs pa_wx W); [reflexivity | |].
  - rewrite restrict_mkst_fx. apply xc_step_jal.
  - intros md1 Hsame.
    cbn [ms_regs ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
    assert (HI1 : xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md1).
    { rewrite (same_but_materialized_wvb md md1 Hsame). apply xc_inv_mat_x. exact HI. }
    (* the registers after the link *)
    assert (Q1 : getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) 1 = Z_to_bv 64 (BASE + AX_adv))
      by apply xc_getr_upd1_same.
    assert (Kr : forall r : bv 5, bv_unsigned r <> 1 ->
      getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) r = getr regs r)
      by (intros r Hr; apply xc_getr_upd1; exact Hr).
    pose proof HR as HRc.
    destruct HRc as ((R2 & R9 & R8 & R3 & R4 & R19 & R22 & R24) & R18 & R20 & R21 & R25 & R27 & R26 & R23).
    assert (S2 : getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) 2 = w64 (lf_F cx))
      by (rewrite Kr; [exact R2 | xc_bvz]).
    assert (Hsp1 : spZ (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) = lf_F cx).
    { unfold spZ. rewrite S2. unfold w64. apply unsigned_lit_small. exact HF64. }
    (* the cut's facts at the materialized model *)
    pose proof HI1 as HI1c.
    destruct HI1c as ((kk & HJ1) & HFR1 & HFLW1 & HFA1 & HMOD1 & HIN1 & HRV1 & HJT1 & HSEP1 & HPERM1 & HLEN1 & HEVO1 &
      EK1 & EG1 & EES1 & EC1 & EO1 & EMX1 & ECAP1 & EOUT1 & EGN1 & ENFD1 & HFRS1 & HMLE1 & HMOK1 & HSLOK1 &
      HAT1 & HA01 & HNORD1 & HGS81 & HORD1 & HORDf1 & HNPi1 & HCNi1).
    pose proof HJ1 as HJ1c.
    destruct HJ1c as (HSTKj & HXOj & (memS & HJi & Hagj) & Houtj).
    pose proof HJi as (HARly1 & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & _ & _ & _).
    destruct Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _ & _ & _ & _ & _ & _).
    destruct HMOD1 as (HLm & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFDv & HNFDw & HNFDr & HTU & HLST & HLSTw).
    pose proof (HSL k Hk4) as HSLk. rewrite Hh in HSLk. cbn [aslot] in HSLk.
    pose proof (HSLOK1 k Hk4) as HSOK. rewrite Hh in HSOK. cbn [lx_ends_slot_ok] in HSOK.
    destruct HSOK as (HNDt & HNb).
    destruct HOUT as (HOmx & _ & HOno & _ & HOcap & _ & HOout & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & HOlen & HOcase).
    (* the callee's entry state *)
    assert (HPRE1 : exists ch, afn_pre_x segs B ARx lx_CSHE_STK ly St [] W
      (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) mem md1 ch).
    { apply (lx_afn_pre_at_x cx ly St fpos kk W mem md1
        (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) lx_CSHE_STK HB HJ1 HFR1 Hsp1).
      - rewrite Q1. apply ret_ok_codeptr_v;
          [unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput; lia | vm_compute; reflexivity].
      - unfold raZ. rewrite Q1.
        pose proof pa_B_ok as (HB0 & HB1 & _). pose proof (pa_base_lo (L := fr_prog_listing)) as HBlo.
        rewrite unsigned_lit_small by (unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput in *; lia).
        unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput. lia.
      - rewrite Kr; [exact R3 | xc_bvz].
      - rewrite Kr; [exact R4 | xc_bvz].
      - rewrite Kr; [exact R8 | xc_bvz].
      - unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK. lia.
      - unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, LLVMF_STK. lia. }
    destruct HPRE1 as (ch & HPREc).
    (* the slot's G *)
    assert (HGk : gx_ok segs B (xe_G k)).
    { apply (gx_ok_sub segs B (xe_G k) G_fr); [|exact HG].
      intros a Ha. apply HGs. unfold xe_G in Ha. apply inG_cons in Ha as [Ha | Ha];
        [|exfalso; exact (inG_nil a Ha)].
      unfold in_zr, xe_HA, ASRC in *. cbn [fst snd] in Ha. lia. }
    (* the held list of the slot *)
    pose proof HSLk as HSLkc.
    destruct HSLkc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      HHELD & _).
    pose proof HHELD as HHELDc.
    destruct HHELDc as (_ & _ & _ & _ & _ & HVEC & _ & _ & HRECS).
    (* the stream, as check_shape_ends reads it *)
    assert (HSTR : ob_at W mem (lm_out m) (lm_O m) /\
      Z.of_nat (length (lm_O m)) <= 2 ^ 40 /\
      (0 < Z.of_nat (length (lm_O m)) -> Z.of_nat (length (lm_O m)) < 2 ^ 32) /\
      amem_range (lm_out m) (Z.of_nat (length (lm_O m)) + 8) /\
      (lm_O m = [] \/ exists CO, Z.of_nat (length (lm_O m)) <= CO /\
         In (lm_out m, CO) (ablocks B ly St) /\ ~ In (lm_out m) (hs_blocks h))).
    { destruct HOcase as [(Ecap & Eout0 & Elen0) | (Hcap0 & Hnocap & Hinb & junk & Hjl & Hg8)].
      - assert (HO0 : lm_O m = []) by (apply length_zero_iff_nil; lia).
        split; [intros j Hj; rewrite Elen0 in Hj; lia|].
        split; [rewrite Elen0; lia|].
        split; [rewrite Elen0; lia|].
        split; [unfold amem_range; left; rewrite Elen0, Eout0; unfold kLowMemEnd; lia|].
        left. exact HO0.
      - pose proof (alx_blocks _ _ ARx LAWS ly St [] W mem md1 _ _ HARly1 Hinb)
          as (Hal & H4096 & Hceilb & Happ & _).
        pose proof (BLKN ly St [] W mem md1 _ _ HARly1 Hinb) as Hmm0.
        pose proof (BLKM ly St [] W mem md1 _ _ HARly1 Hinb) as Hmm.
        pose proof (req_size_pos (lm_cap m) ltac:(lia)) as [Hq1 Hq2].
        split; [exact (xe_ob_of_garr8 W mem (lm_out m) (lm_O m) junk Hg8)|].
        split; [lia|].
        split; [intros _; lia|].
        split.
        { unfold amem_range. unfold in_app in Happ. destruct Happ as (_ & [Hlow | (Hhi1 & Hhi2)]).
          - left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
          - right. split; [lia|]. unfold ASAN_CEIL in Hhi2. unfold kHighMemEnd. lia. }
        right. exists (lm_cap m). split; [lia|]. split; [exact Hinb|].
        apply (xc_out_apart_x cx m ly St W mem md1 k h HARly1 HSEP1 Hk4 Hh). lia. }
    destruct HSTR as (HOB & HObound & HObound2 & HOmr & HOdis).
    (* ---- check_shape_ends at the slot's own G ---- *)
    pose proof (CSHE (xe_G k) HGk W ly St [] (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) mem md1 ch AX_XO
      (lf_F cx + AX_AT) (xe_HA k) k (VAL AX_lit_empty) h [] A (lm_gn m)
      (Z.of_nat (length (lm_O m))) (lm_out m) (lm_O m)) as HC.
    cbv zeta in HC.
    eapply SRr_mono.
    { apply HC with (kr := 0%nat).
      + exact HPREc.
      + unfold AX_XO. lia.
      + vm_compute. reflexivity.
      + rewrite Hsp1, Etop. unfold AX_XO. lia.
      + rewrite Hsp1. intros a Ha. apply Hpresj. unfold AX_XO in Ha. unfold LLVMF_STK in *. lia.
      + rewrite Kr; [exact R10 | xc_bvz].
      + rewrite Kr; [exact R11 | xc_bvz].
      + rewrite Kr; [exact R12 | xc_bvz].
      + exact HSLk.
      + unfold xe_HA. rewrite Egsv.
        replace (6131296 + ASRC * Z.of_nat k) with ((766412 + 12 * Z.of_nat k) * 8) by (unfold ASRC; lia).
        apply Z_mod_mult.
      + unfold xe_HA, ASRC. rewrite Egsv. lia.
      + unfold xe_HA, ASRC, kLowMemEnd. rewrite Egsv. lia.
      + intros a Ha. unfold xe_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
      + apply (xe_azs_sub (rg_s fr_RG) (4 * ASRC)); [exact AZS_s | unfold xe_HA, ASRC; lia |
          unfold xe_HA, ASRC; lia].
      + unfold xe_HA. destruct xe_vals as (_ & _ & _ & Exgs & _). rewrite <- Exgs. reflexivity.
      + lia.
      + rewrite Hsp1. intros a Ha.
        unfold xe_HA, ASRC, CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *. rewrite Egsv in Ha. lia.
      + intros a Ha.
        assert (HGa : inG G_fr a) by (apply HGs; unfold xe_HA, ASRC in *; lia).
        destruct (HG a HGa) as (Himg & Hown & _).
        unfold cshe_home. right. left. split; [exact Himg|]. split; [exact Hown|].
        unfold xe_HA, ASRC in *. lia.
      + exact HNDt.
      + exact HNb.
      + rewrite Hsp1. intros a Ha.
        destruct HVEC as [(Ec & Ev) | (Hc0 & Hinv & _)].
        * rewrite Ec in Ha. unfold AREC in Ha. lia.
        * pose proof (alx_blocks _ _ ARx LAWS ly St [] W mem md1 _ _ HARly1 Hinv) as (_ & _ & Hceilv & _).
          pose proof (req_size_pos (AREC * hl_cap (hs_held h)) ltac:(unfold AREC; lia)) as [_ Hgev].
          unfold CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *. lia.
      + rewrite Hsp1. intros r Hr a Ha.
        pose proof (proj1 (Forall_forall _ _) HRECS r Hr) as (Hinr & _).
        pose proof (alx_blocks _ _ ARx LAWS ly St [] W mem md1 _ _ HARly1 Hinr) as (_ & _ & Hceilr & _).
        pose proof (req_size_pos (Z.of_nat (length (snd r)) + 1) ltac:(lia)) as [_ Hger].
        unfold CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *. lia.
      + pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D32. rewrite HFmod, Z.add_0_r in D32.
        unfold AX_AT. replace (lf_F cx + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult.
      + rewrite Hsp1. unfold AX_AT. lia.
      + rewrite Hsp1. unfold AX_AT, AX_XO. lia.
      + apply (xe_ra_stack_x ly St W mem md1); [exact HARly1 | rewrite Eslo; unfold AX_AT, LLVMF_STK in *; lia |
          rewrite Eshi; unfold AX_AT in *; lia | lia].
      + exact HAT1.
      + intros Hc. destruct Hc.
      + cbn [length]. lia.
      + rewrite Hlit. lia.
      + rewrite Hlit. cbn [length]. lia.
      + cbn [length]. intros j Hj. lia.
      + cbn [length]. rewrite Z.add_0_r. exact (proj1 (xe_lit_bytes W mem HRV1)).
      + cbn [length]. intros a Ha.
        split; [apply (proj2 (xe_lit_bytes W mem HRV1)); rewrite Hlit in *; lia|].
        rewrite Hsp1; rewrite Hlit in *.
        unfold CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *; lia.
      + unfold amem_range. left. rewrite Hlit. cbn [length]. unfold kLowMemEnd. lia.
      + unfold amem_range. left. rewrite Hlit. unfold kLowMemEnd. lia.
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia).
        exact (proj1 (XE_LIT_S ly St [] W mem md1 HARly1)).
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia).
        exact (proj2 (XE_LIT_S ly St [] W mem md1 HARly1) ltac:(lia)).
      + (* the prefix's home: B's spec takes it as one disjunction; .str.3 is a read-only literal *)
        left. split; [cbn [length]; intros a Ha; apply xe_lit_rom; lia|].
        replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia). exact XE_LIT_S.
      + exact (XRF_END5 W mem HRV1).
      + exact HRV1.
      + rewrite Egone. exact (proj1 HGONE).
      + destruct HGONE as (_ & _ & [E0 | E1]); lia.
      + rewrite Enout. exact HOno.
      + rewrite Eoutv. exact HOout.
      + exact HOB.
      + reflexivity.
      + exact HObound.
      + exact HObound2.
      + exact HOmr.
      + exact HOdis.
      + rewrite EO1. lia.
      + intros Hg0 E'. apply Hnone. unfold lx_ends_c1.
        rewrite <- EGN1, Hg0, <- EO1. cbn [Z.eqb]. rewrite E'. reflexivity.
      + apply (mo_ok_le MT MLM St (cshe_cost MT (hs_held h)) (lx_ends_cost (lm_hs m)) HMOK1).
        unfold cshe_cost. exact (xc_cost_nth (lm_hs m) k h Hh).
      + apply RP_NP. exact HNPi1.
      + exact HCNi1. }
    (* ---- the post ---- *)
    intros W2 c2 Hwle2 (ly' & S' & Hp' & regs2 & mem2 & md2 & kk2 & H' & ds & c & -> & HJc & HP2 & _ & HSRC2 & Hv' &
      Hcap' & HND2 & Harms & Hc0 & HAT2 & HGONE2 & HPERM2 & HFRS2 & HMLE2 & HRM').
    (* cshe_post_x's ghost list is [] (HP0 at the post's journal) *)
    assert (Ehp : Hp' = []) by (eapply HP0; eapply ajournal_gx_AR_x; exact HJc). subst Hp'.
    rewrite Hsp1 in HJc.
    assert (HE : hl_recs H' = [] /\ Permutation (hl_recs (hs_held h)) ds /\
      A + c <= Z.of_nat (length (lm_O m0)) /\
      lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A = Some (hl_recs H', A + c)).
    { destruct Harms as [(Hg & Hrecs & Hds & Hc) | (Hg & Hrun)].
      - assert (Hr0 : hl_recs H' = []) by (rewrite Hrecs; apply xm_filter_nil_f).
        assert (Hds0 : ds = hl_recs (hs_held h)) by (rewrite Hds; apply xm_filter_nil_t).
        split; [exact Hr0|].
        split; [rewrite Hds0; apply Permutation_refl|].
        split; [subst c; rewrite Z.add_0_r; lia|].
        unfold lx_ends_c1. rewrite <- EGN1.
        destruct (Z.eqb_spec (lm_gn m) 0) as [E0 | E0]; [exfalso; exact (Hg E0)|].
        rewrite Hr0, xm_filter_nil_f. subst c. rewrite Z.add_0_r. reflexivity.
      - assert (Hc1e : lx_ends_c1 (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A = Some (hl_recs H', A + c)).
        { unfold lx_ends_c1. rewrite Hg. cbn [Z.eqb]. rewrite Hrun. reflexivity. }
        destruct (xm_c1 (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A (hl_recs H') (A + c) Hc1e) as (Hr0 & Hb).
        destruct (xm_c1_ds (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A (hl_recs H') (A + c) Hc1e) as (_ & Hds2).
        split; [exact Hr0|].
        split; [exact (Hds2 Hg ds c Hrun)|].
        rewrite length_skipn in Hb. rewrite EO1 in Hb.
        split; [lia|].
        rewrite <- EGN1, <- EO1. exact Hc1e. }
    destruct HE as (Hr0 & Hperm_ds & Hbound & Hends).
    destruct (xe_model_after_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md1 k h H' ds c ly' S' W2 mem2 md2 kk2
      HB HI1 Hk4 Hh HJc HSRC2 Hv' Hcap' HND2 Hr0 Hperm_ds HAT2 Hc0 Hbound HPERM2 HFRS2 HMLE2
      (proj1 (RP_NP S' 0%nat) HRM')) as (m' & Hm'hs & HI').
    exists ly', S', regs2, mem2, md2, m', H', (A + c).
    split; [rewrite Q1; reflexivity|].
    split; [exact HI'|].
    split; [exact (xc_slot_kept cx i k n regs regs2 (Z_to_bv 64 (BASE + AX_adv)) HR HP2)|].
    split; [exact Hr0|].
    split; [exact Hends | exact Hm'hs].
Qed.
(* a run leaves the model materialized; the loop's state does not read it but through the journal *)
Lemma xe_inv_materialize_x : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md X,
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV.
  destruct HINV as ((kk & HJ) & REST).
  split; [exists kk; eapply (ajournal_gx_materialize_x segs B PST ARx LAWS pa_segs_low); exact HJ | exact REST].
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): xe_inv_materialize_x at a world relation R; the strict text above keeps its
   proof. ---- *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
(* :1509 xe_inv_materialize_x *)
Lemma xe_inv_materialize_xR : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md X,
  xe_inv_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_inv_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV.
  destruct HINV as ((kk & HJ) & REST).
  split; [exists kk; eapply (ajournal_gx_materialize_xR segs B PST ARx LAWS pa_segs_low); exact HJ | exact REST].
Qed.
End wR.
(* the frame base is 320 to 351 bytes below the entry sp, above the allocation ceiling *)
Lemma xe_geom_x : forall cx, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320 /\
  alloc_ceiling < lf_F cx /\ lf_F cx + 320 <= 2 ^ 47.
Proof.
  intros cx (HAI & HPRE).
  pose proof HPRE as (HFNP & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  assert (HLS : LLVMF_STK = 32768) by reflexivity. rewrite HLS in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320)
    by (unfold lf_F; pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)); lia).
  split; [lia|]. split; [lia|]. split; lia.
Qed.
(* ---- one trip of the inner loop: the two tests and, when they pass, the call ---- *)
Lemma xe_step_inner_x : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) afin,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k (4 - Z.of_nat k) regs -> (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  xe_fin (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m)) = Some afin ->
  SRr segs W (cfg_at segs (BASE + AX_inner) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (m' : lmod) (A1 : Z),
       c' = cfg_at segs (BASE + AX_adv) regs' mem' md' /\
       xe_inv_x cx fpos ly3 S3 m0 norder ord A1 ly' S' m' W' mem' md' /\
       xe_regs_slot cx i k (4 - Z.of_nat k) regs' /\
       xe_fin (lm_gn m0) (lm_O m0) ord norder i (S k) A1 (map lx_ends_slot0 (lm_hs m')) = Some afin).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k afin HB HINV HR Hk4 Hi Hnord HFIN.
  pose proof HINV as (HJx & HFR & HFLW & HFA & HMOD & HINP & HRV & HJT & HSEP & HBF & HLEN & HEVO & HKk & HGG & HES &
    HCC & HOO & HMX & HCAP & HOUTm & HGN & HNFD & HFRS & HMLE & HMOK & HSLOK & HATv & HAb & HNOv & Hn4 & HGS8 & HORDv &
    HNPv & HCNv).
  destruct HJx as (kk & HJ).
  assert (HAR : ARx ly St [] W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  pose proof HMOD as (HL4 & HSLOT & _).
  destruct (HORDv i ltac:(lia)) as (HOI & HOIr).
  destruct (xe_geom_x cx HB) as (Hsp & HFb & HFlo & HFhi).
  (* the slot's two fields, and the model's reduced slot *)
  pose proof (HSLOT k Hk4) as HSL. unfold aslot in HSL.
  assert (Hknth : nth_error (lm_hs m) k = Some (nth k (lm_hs m) None))
    by (apply nth_error_nth'; lia).
  assert (HNE : nth_error (map lx_ends_slot0 (lm_hs m)) k =
                Some (lx_ends_slot0 (nth k (lm_hs m) None))).
  { rewrite nth_error_map, Hknth. reflexivity. }
  destruct (nth k (lm_hs m) None) as [h|] eqn:Ehk.
  - (* an open source *)
    pose proof HSL as (Mfd & Mop & _ & _ & _ & _ & _ & Hopen & Hfdr & _).
    eapply SRr_bind.
    { eapply (xe_inner_run_x cx W regs mem md ly St md i k (4 - Z.of_nat k) (hs_open h) (hs_fd h) (ord i));
        first [exact HAR | exact HR | exact Mfd | exact Mop | exact HOI | lia]. }
    cbv beta. intros W' c' _ (-> & regs' & X & [(Hop & Hoi & -> & Ha0 & Ha1 & Ha2 & HR') | (Hsk & -> & HR')]).
    + (* the fd matches: the call *)
      assert (HNE2 : nth_error (map lx_ends_slot0 (lm_hs m)) k = Some (Some (hs_fd h, hl_recs (hs_held h))))
        by (rewrite HNE; try rewrite Ehk; reflexivity).
      eapply SRr_mono.
      { eapply (xe_call_x cx fpos ly3 S3 m0 norder ord A ly St m W mem
                  (with_vm_backing (m_vm_lazy md) X md) regs' i k (4 - Z.of_nat k) h HB
                  (xe_inv_materialize_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)
                  HR' Ha0 Ha1 Ha2 Hk4 Ehk).
        exact (xm_fin_c1_ne (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                 (hs_fd h) (hl_recs (hs_held h)) afin HNE2 (eq_sym Hoi) HFIN). }
      cbv beta. intros W2 c2 _ (ly' & S' & regs2 & mem2 & md2 & m' & H' & A1 & -> & HINV2 & HR2 & HH' & HC1 & HHS).
      exists ly', S', regs2, mem2, md2, m', A1.
      split; [reflexivity|]. split; [exact HINV2|]. split; [exact HR2|].
      assert (ESL : map lx_ends_slot0 (lm_hs m') =
                    xe_set_nth k (Some (hs_fd h, hl_recs H')) (map lx_ends_slot0 (lm_hs m))).
      { rewrite HHS, xm_slot0_set. cbn [lx_ends_slot0 CheckRep.set_held hs_fd hs_held]. reflexivity. }
      rewrite ESL.
      rewrite <- (xm_fin_call (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                    (hs_fd h) (hl_recs (hs_held h)) (hl_recs H') A1 HNE2 (eq_sym Hoi) HC1).
      exact HFIN.
    + (* the slot is skipped *)
      apply SRr_ret.
      exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), m, A.
      split; [reflexivity|].
      split; [exact (xe_inv_materialize_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)|].
      split; [exact HR'|].
      rewrite <- (xm_fin_skip (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                    (lx_ends_slot0 (Some h)) HNE).
      * exact HFIN.
      * right. exists (hs_fd h), (hl_recs (hs_held h)).
        split; [try rewrite Ehk; reflexivity|].
        destruct Hsk as [Hz | Hne]; [rewrite Hopen in Hz; discriminate | intros Heq; apply Hne; symmetry; exact Heq].
  - (* a closed slot: its fd and open fields read 0, so the loop skips it *)
    destruct (xe_closed_vals W mem (rg_s fr_RG + ASRC * Z.of_nat k) HSL) as (Mfd & Mop).
    assert (EHA : rg_s fr_RG + ASRC * Z.of_nat k = xe_HA k) by reflexivity.
    rewrite EHA in Mfd, Mop.
    eapply SRr_bind.
    { eapply (xe_inner_run_x cx W regs mem md ly St md i k (4 - Z.of_nat k) 0 0 (ord i));
        first [exact HAR | exact HR | exact Mfd | exact Mop | exact HOI | lia]. }
    cbv beta. intros W' c' _ (-> & regs' & X & [(Hop & _ & _ & _ & _ & _ & _) | (Hsk & -> & HR')]);
      [exfalso; exact (Hop eq_refl)|].
    apply SRr_ret.
    exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), m, A.
    split; [reflexivity|].
    split; [exact (xe_inv_materialize_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)|].
    split; [exact HR'|].
    rewrite <- (xm_fin_skip (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                  (lx_ends_slot0 None) HNE).
    * exact HFIN.
    * left. try rewrite Ehk. reflexivity.
Qed.
(* ---- the two loops, from the advance point after the slot k of trip i ---- *)
Lemma xe_loop_x : forall (fuel : nat) cx t fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) afin,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  (Z.to_nat (4 * (norder - i)) - S k < fuel)%nat ->
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k (4 - Z.of_nat k) regs ->
  lx_ends_run (lm_gn m0) (lm_O m0) norder ord (lm_hs m0) 0 = Some afin ->
  xe_fin (lm_gn m0) (lm_O m0) ord norder i (S k) A (map lx_ends_slot0 (lm_hs m)) = Some afin ->
  SRr segs W (cfg_at segs (BASE + AX_adv) regs mem md) (lx_ends_post_x cx t fpos ly3 S3 m0 norder ord).
Proof.
  induction fuel as [|fuel IH];
    intros cx t fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k afin HB Hk4 Hi Hnord Hfuel HINV HR
      HRUN HFIN; [exfalso; lia|].
  pose proof HINV as (HJx & HFR & HFLW & HFA & HMOD & HINP & HRV & HJT & HSEP & HBF & HLEN & HEVO & HKk & HGG & HES &
    HCC & HOO & HMX & HCAP & HOUTm & HGN & HNFD & HFRS & HMLE & HMOK & HSLOK & HATv & HAb & HNOv & Hn4 & HGS8 & HORDv &
    HNPv & HCNv).
  destruct HJx as (kk & HJ).
  destruct (xe_geom_x cx HB) as (Hsp & HFb & HFlo & HFhi).
  assert (HSL4 : length (map lx_ends_slot0 (lm_hs m)) = 4%nat) by (rewrite length_map; exact HLEN).
  eapply SRr_bind.
  { eapply (xe_adv_run cx W regs mem md i k norder HR Hk4 Hi Hnord HFlo HFhi HNOv). }
  cbv beta. intros W' c' _ (-> & regs' & X & [(Hk' & -> & HR') | [(Hk4' & Hin & -> & HR') | (Hk4' & Hie & -> & HRK)]]).
  - (* the next slot of this trip *)
    eapply SRr_bind.
    { eapply (xe_step_inner_x cx fpos ly3 S3 m0 norder ord A ly St m W mem
                (with_vm_backing (m_vm_lazy md) X md) regs' i (S k) afin HB
                (xe_inv_materialize_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)
                HR' Hk' Hi Hnord HFIN). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & m2 & A2 & -> & HINV2 & HR2 & HFIN2).
    exact (IH cx t fpos ly3 S3 m0 norder ord A2 ly2 S2 m2 W2 mem2 md2 regs2 i (S k) afin HB Hk' Hi Hnord
             ltac:(lia) HINV2 HR2 HRUN HFIN2).
  - (* the next trip *)
    assert (HFIN' : xe_fin (lm_gn m0) (lm_O m0) ord norder (i + 1) 0 A (map lx_ends_slot0 (lm_hs m)) = Some afin).
    { rewrite <- (xm_fin_next (lm_gn m0) (lm_O m0) ord norder i A (map lx_ends_slot0 (lm_hs m)) HSL4
                    ltac:(lia) ltac:(lia)).
      rewrite <- Hk4'. exact HFIN. }
    eapply SRr_bind.
    { eapply (xe_head_run cx W regs' mem (with_vm_backing (m_vm_lazy md) X md) (i + 1) norder HR'
                ltac:(lia) HFlo HFhi HGS8). }
    cbv beta. intros W2 c2 _ (-> & regs2 & X2 & -> & HR2).
    eapply SRr_bind.
    { eapply (xe_step_inner_x cx fpos ly3 S3 m0 norder ord A ly St m W mem
                (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X md)) X2
                   (with_vm_backing (m_vm_lazy md) X md)) regs2 (i + 1) 0%nat afin HB
                (xe_inv_materialize_x cx fpos ly3 S3 m0 norder ord A ly St m W mem
                   (with_vm_backing (m_vm_lazy md) X md) X2
                   (xe_inv_materialize_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV))
                HR2 ltac:(lia) ltac:(lia) Hnord HFIN'). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2' & mem2 & md2 & m2 & A2 & -> & HINV2 & HR2' & HFIN2).
    exact (IH cx t fpos ly3 S3 m0 norder ord A2 ly2 S2 m2 W2 mem2 md2 regs2' (i + 1) 0%nat afin HB
             ltac:(lia) ltac:(lia) Hnord ltac:(lia) HINV2 HR2' HRUN HFIN2).
  - (* the last trip is done: 0x84d4c, with the `at` cell at its final value *)
    apply SRr_ret.
    assert (EA : afin = A).
    { pose proof (xm_fin_done (lm_gn m0) (lm_O m0) ord norder i A (map lx_ends_slot0 (lm_hs m)) HSL4
        ltac:(lia)) as HD.
      rewrite <- Hk4' in HD. rewrite HD in HFIN. injection HFIN as <-. reflexivity. }
    pose proof HRK as (R2 & R9 & R8 & R3 & R4 & _).
    exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), kk, m, A.
    split; [reflexivity|].
    split; [eapply (ajournal_gx_materialize_x segs B PST ARx LAWS pa_segs_low); exact HJ|].
    split; [exact HFR|]. split; [exact HFLW|]. split; [exact HFA|]. split; [exact HMOD|]. split; [exact HINP|].
    split; [exact HRV|]. split; [exact HJT|]. split; [exact HSEP|]. split; [exact HBF|].
    split; [exact R2|]. split; [exact R8|]. split; [exact R9|]. split; [exact R3|]. split; [exact R4|].
    split; [exact HATv|]. split; [lia|].
    split; [congruence|].
    split; [exact HKk|]. split; [exact HGG|]. split; [exact HES|]. split; [exact HCC|].
    split; [exact HOO|]. split; [exact HMX|]. split; [exact HCAP|]. split; [exact HOUTm|].
    split; [exact HGN|]. split; [exact HNFD|]. split; [exact HLEN|]. split; [exact HEVO|].
    split; [exact HFRS|].
    split; [eapply (mo_le_mono MT MLM); [exact HMLE|]; pose proof (xe_cost_nonneg (lm_hs m)); lia|].
    split; [exact HNPv | exact HCNv].
Qed.

Lemma lx_ends_x : lx_ends_S_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx RP.
Proof.
(* The block, assembled: the entry run stores norder at F+152 and the shadow cursor at F+144 and sets the cursors
   (xe_entry_run_x), the outer head sets the slot cursors of trip 0 (xe_head_run), the first inner trip runs
   (xe_step_inner_x) and the two loops then run to 0x84fe8 (xe_loop_x).  The model side is xe_fin, which at (0, 0) is
   lx_ends_run.  The entry's aframe_at is weakened to bx_frame: its F+152 cell is the one the entry overwrites. *)
  unfold lx_ends_S_x.
  intros cx t fpos ly3 S3 m norder ord regs mem md W kk HJ HFR0 HFL HMOD HINP HRV HJT HSEP HMOK HSLOK HRUN
    R2 R8 R9 R27 R19 R3 R4 Hnord HAT HORD HB HNP3 HCN3.
  pose proof (bx_frame_of_aframe _ _ _ _ HFR0) as HFR. clear HFR0.
  destruct (xe_geom_x cx HB) as (Hsp & HFb & HFlo & HFhi).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFR as (_ & HAWR & _).
  assert (HAR : ARx ly3 S3 [] W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _).
    pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (lx_ends_run (lm_gn m) (lm_O m) norder ord (lm_hs m) 0) as [afin|] eqn:ERUN;
    [|exfalso; exact (HRUN eq_refl)].
  (* (1) 0x84c74 -> 0x84c9c *)
  eapply SRr_bind.
  { eapply (xe_entry_run_x cx W regs mem md LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 kk norder HJ
      R2 R9 R8 R3 R4 R19 R27 Hnord ltac:(unfold LLVMF_STK; lia) ltac:(unfold AX_XO; lia) HFlo HFhi HAWR). }
  cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & X & -> & HJ1 & HRO1 & HNO1 & HGS1 & HKEEP & HPRES).
  destruct (xe_carry_x cx W mem mem1 md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
              HFR HMOD HINP HRV HJT HKEEP HPRES) as (HFR1 & HMOD1 & HINP1 & HRV1 & HJT1 & HVAL1).
  assert (HFL1 : sv8 W mem1 (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)).
  { destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem md 1 fpos HAR Hfin) as (HFF0 & HFF1 & _).
    change (fs_frame_bytes 1) with 128 in HFF1. unfold sv8 in HFL |- *.
    apply (xe_vm_view W W mem mem1); [|exact HFL]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
    apply HKEEP; unfold AX_GS8; lia. }
  assert (HINV : xe_inv_x cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1 (with_vm_backing (m_vm_lazy md) X md)).
  { split; [exists kk; exact HJ1|].
    split; [exact HFR1|]. split; [exact HFL1|]. split; [reflexivity|]. split; [exact HMOD1|]. split; [exact HINP1|].
    split; [exact HRV1|]. split; [exact HJT1|]. split; [exact HSEP|].
    split; [intros rest HP; exact HP|].
    split; [exact (proj1 HMOD1)|].
    split; [intros j Hj; left; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [destruct (lm_c m); reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [replace (lx_ends_cost (lm_hs m) - lx_ends_cost (lm_hs m)) with 0 by ring;
            exact (mo_le_refl MT MLM S3)|].
    split; [exact HMOK|].
    split; [exact HSLOK|].
    split; [exact (HVAL1 (lf_F cx + AX_AT) 8%nat 0 ltac:(unfold AX_ORDER, AX_AT; lia)
                     ltac:(unfold AX_AT; lia) HAT)|].
    split; [lia|].
    split; [exact HNO1|].
    split; [exact Hnord|].
    split; [exact HGS1|].
    split.
    { intros i Hi. destruct (HORD i Hi) as (HV & HR0). split; [|exact HR0].
      exact (HVAL1 (lf_F cx + AX_ORDER + 4 * i) 4%nat (ord i) ltac:(unfold AX_ORDER; lia)
               ltac:(unfold AX_ORDER, AX_AT; lia) HV). }
    split; [exact HNP3 | exact HCN3]. }
  (* (2) 0x84c9c -> 0x84cbc, then the first inner trip *)
  eapply SRr_bind.
  { eapply (xe_head_run cx W regs1 mem1 (with_vm_backing (m_vm_lazy md) X md) 0 norder HRO1
              ltac:(lia) HFlo HFhi HGS1). }
  cbv beta. intros W2 c2 _ (-> & regs2 & X2 & -> & HR2).
  assert (HFIN0 : xe_fin (lm_gn m) (lm_O m) ord norder 0 0%nat 0 (map lx_ends_slot0 (lm_hs m)) = Some afin).
  { rewrite (xm_fin_start (lm_gn m) (lm_O m) ord norder 0 (map lx_ends_slot0 (lm_hs m)) ltac:(lia)).
    unfold lx_ends_run in ERUN. exact ERUN. }
  eapply SRr_bind.
  { eapply (xe_step_inner_x cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1
              (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X md)) X2
                 (with_vm_backing (m_vm_lazy md) X md)) regs2 0 0%nat afin HB
              (xe_inv_materialize_x cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1
                 (with_vm_backing (m_vm_lazy md) X md) X2 HINV)
              HR2 ltac:(lia) ltac:(lia) Hnord HFIN0). }
  cbv beta. intros W3 c3 _ (ly' & S' & regs3 & mem3 & md3 & m' & A1 & -> & HINV3 & HR3 & HFIN3).
  (* (3) the two loops *)
  exact (xe_loop_x (S (Z.to_nat (4 * norder))) cx t fpos ly3 S3 m norder ord A1 ly' S' m' W3 mem3 md3 regs3
           0 0%nat afin HB ltac:(lia) ltac:(lia) Hnord ltac:(lia) HINV3 HR3 ERUN HFIN3).
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the block lx_ends at a world relation R, lx_ends_xR : W_contract_xR_g3.v
   lx_ends_S_xR.  ajournal_gx_x -> ajournal_gx_xR R, xe_inv_x -> xe_inv_xR R, SRr segs -> SRrG segs R, the kit's
   journal lemmas -> their _xR twins; the journal-free runs of W_bx_ends.v (xe_inner_run_x, xe_adv_run, xe_head_run)
   are lifted by SRr_SRrG (WLE_R) where they are used; check_shape_ends is CSHE_R below, at W_contract_xR_g6.cshe_spec_xR
   (a Theorem Labs lane's).  The strict texts above keep their proofs. ---- *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
(* check_shape_ends at R: W_contract_xR_g6.cshe_spec_xR (a Theorem Labs lane's), at check_shape_ends' address, as the strict
   CSHE above takes it *)
Hypothesis CSHE_R : forall G, gx_ok segs B G -> cshe_spec_xR B PST ARx R MT RP G (BASE + AF_fr_check_shape_ends).
(* YA0n.v:135 SRr_step at SRrG segs R (its proof never reads the relation; the kit has no SRrG single-step lemma) *)
Lemma xe_SRrG_step : forall W ms msr' model Q,
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict (w_H W) ms) = MachineOk msr' ->
  (forall model', same_but_materialized model model' ->
     SRrG segs R W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
  SRrG segs R W (mkCfg ms model) Q.
Proof.
  intros W ms msr' model Q Hsvc Hs Hk HI T HK.
  destruct HI as (HH & Hwf & Hcov & Hinv & Hh).
  destruct (node_instr_restricted segs (w_H W) HH pa_wx (w_A W) ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
    as (model' & Hinv' & Hsame & _ & _ & Hnode).
  apply (srz_silent1 segs _ _ T Hnode).
  apply (Hk model' Hsame).
  - apply (AI_same segs (w_H W) (w_A W) model model'); [split; auto | exact Hsame | exact Hinv'].
  - exact HK.
Qed.
(* :183 lx_afn_pre_at_x *)
Lemma lx_afn_pre_at_xR : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  bx_frame cx (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 [] W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & HSG).
  rewrite !Z.add_0_r in HJ0.
  (* the frame base is 320 or 336 below the entry sp, and 32-aligned *)
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { pose proof (Z.mod_divide (sp0 - 320) 16 ltac:(lia)) as _.
      assert (E16 : (sp0 - 320) mod 16 = 0)
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
  (* the chain: the entry's, with this frame pushed *)
  pose proof (aview_above_of_journal_xR (PI := PB_fr) (R := R) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
  pose proof HFR as (HSV & _).
  assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  clear Hpres0.
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hsp8 : sp0 mod 8 = 0).
  { assert (Hq : sp0 = 16 * (sp0 / 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    rewrite Hq. replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  assert (HCH : exists ch, achain ly3 (aview segs (w_H W) mem) (lf_F cx) sp0 ch).
  { destruct (Z_lt_ge_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
    - exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
      apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
      eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
        sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
        [ exact Hch0 | lia
        | intros a Ha; rewrite (HAB a ltac:(lia)); apply HSG; rewrite unsigned_lit_small by lia; intros HGa;
          pose proof (inG_low segs B pa_segs_low G_fr a HG HGa); lia
        | exact Hra8 | exact Hs016
        | unfold raZ in Hra40; lia | lia | exact Hsp8 | exact Hlt | rewrite HF32; lia ].
    - exists []. left. split; [right; left; rewrite HTOPeq; lia | reflexivity]. }
  destruct HCH as (ch & HCH).
  exists ch.
  eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
    [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
    [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
    | exact Hgp | exact Htp | ].
  rewrite Hsp. replace (s0Z regs) with sp0 by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  exact HCH.
Qed.
(* :1599 xe_call_x *)
Lemma xe_call_xR : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) n h,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  xe_inv_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k n regs ->
  getr regs 10 = w64 (xe_HA k) -> getr regs 11 = w64 (VAL AX_lit_empty) ->
  getr regs 12 = w64 (lf_F cx + AX_AT) ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A <> None ->
  SRrG segs R W (cfg_at segs (BASE + AX_call) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (m' : lmod) (H' : hlist) (A1 : Z),
       c' = cfg_at segs (BASE + AX_adv) regs' mem' md' /\
       xe_inv_xR R cx fpos ly3 S3 m0 norder ord A1 ly' S' m' W' mem' md' /\
       xe_regs_slot cx i k n regs' /\
       hl_recs H' = [] /\
       lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A = Some (hl_recs H', A1) /\
       lm_hs m' = xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k n h HB HI HR R10 R11 R12 Hk4 Hh Hnone.
  (* ---- the frame's geometry, from the contract's entry ---- *)
  pose proof HB as HBc. destruct HBc as (HAI & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo0 & Hshi0 & H47 & _ & Htop0 & Htop1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  assert (HFmod : lf_F cx mod 32 = 0).
  { pose proof (Z.div_mod (spZ (c_regs cx) - 320) 32 ltac:(lia)) as D32.
    replace (lf_F cx) with (((spZ (c_regs cx) - 320) / 32) * 32) by lia. apply Z_mod_mult. }
  assert (HF64 : 0 <= lf_F cx < 2 ^ 64) by lia.
  destruct xe_vals as (Egone & Enout & Eoutv & Egs & Hlit).
  assert (Egsv : rg_s fr_RG = 6131296) by (vm_compute; reflexivity).
  (* ---- the jal at 0x84cf0 ---- *)
  unfold cfg_at.
  eapply (xe_SRrG_step W); [reflexivity | |].
  - rewrite restrict_mkst_fx. apply xc_step_jal.
  - intros md1 Hsame.
    cbn [ms_regs ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
    assert (HI1 : xe_inv_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem md1).
    { rewrite (same_but_materialized_wvb md md1 Hsame). apply (xc_inv_mat_xR R). exact HI. }
    (* the registers after the link *)
    assert (Q1 : getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) 1 = Z_to_bv 64 (BASE + AX_adv))
      by apply xc_getr_upd1_same.
    assert (Kr : forall r : bv 5, bv_unsigned r <> 1 ->
      getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) r = getr regs r)
      by (intros r Hr; apply xc_getr_upd1; exact Hr).
    pose proof HR as HRc.
    destruct HRc as ((R2 & R9 & R8 & R3 & R4 & R19 & R22 & R24) & R18 & R20 & R21 & R25 & R27 & R26 & R23).
    assert (S2 : getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) 2 = w64 (lf_F cx))
      by (rewrite Kr; [exact R2 | xc_bvz]).
    assert (Hsp1 : spZ (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) = lf_F cx).
    { unfold spZ. rewrite S2. unfold w64. apply unsigned_lit_small. exact HF64. }
    (* the cut's facts at the materialized model *)
    pose proof HI1 as HI1c.
    destruct HI1c as ((kk & HJ1) & HFR1 & HFLW1 & HFA1 & HMOD1 & HIN1 & HRV1 & HJT1 & HSEP1 & HPERM1 & HLEN1 & HEVO1 &
      EK1 & EG1 & EES1 & EC1 & EO1 & EMX1 & ECAP1 & EOUT1 & EGN1 & ENFD1 & HFRS1 & HMLE1 & HMOK1 & HSLOK1 &
      HAT1 & HA01 & HNORD1 & HGS81 & HORD1 & HORDf1 & HNPi1 & HCNi1).
    pose proof HJ1 as HJ1c.
    destruct HJ1c as (HSTKj & HXOj & (memS & HJi & Hagj) & Houtj).
    pose proof HJi as (HARly1 & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & _ & _ & _).
    destruct Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _ & _ & _ & _ & _ & _).
    destruct HMOD1 as (HLm & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFDv & HNFDw & HNFDr & HTU & HLST & HLSTw).
    pose proof (HSL k Hk4) as HSLk. rewrite Hh in HSLk. cbn [aslot] in HSLk.
    pose proof (HSLOK1 k Hk4) as HSOK. rewrite Hh in HSOK. cbn [lx_ends_slot_ok] in HSOK.
    destruct HSOK as (HNDt & HNb).
    destruct HOUT as (HOmx & _ & HOno & _ & HOcap & _ & HOout & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & HOlen & HOcase).
    (* the callee's entry state *)
    assert (HPRE1 : exists ch, afn_pre_x segs B ARx lx_CSHE_STK ly St [] W
      (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) mem md1 ch).
    { apply (lx_afn_pre_at_xR cx ly St fpos kk W mem md1
        (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) lx_CSHE_STK HB HJ1 HFR1 Hsp1).
      - rewrite Q1. apply ret_ok_codeptr_v;
          [unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput; lia | vm_compute; reflexivity].
      - unfold raZ. rewrite Q1.
        pose proof pa_B_ok as (HB0 & HB1 & _). pose proof (pa_base_lo (L := fr_prog_listing)) as HBlo.
        rewrite unsigned_lit_small by (unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput in *; lia).
        unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput. lia.
      - rewrite Kr; [exact R3 | xc_bvz].
      - rewrite Kr; [exact R4 | xc_bvz].
      - rewrite Kr; [exact R8 | xc_bvz].
      - unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK. lia.
      - unfold lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, LLVMF_STK. lia. }
    destruct HPRE1 as (ch & HPREc).
    (* the slot's G *)
    assert (HGk : gx_ok segs B (xe_G k)).
    { apply (gx_ok_sub segs B (xe_G k) G_fr); [|exact HG].
      intros a Ha. apply HGs. unfold xe_G in Ha. apply inG_cons in Ha as [Ha | Ha];
        [|exfalso; exact (inG_nil a Ha)].
      unfold in_zr, xe_HA, ASRC in *. cbn [fst snd] in Ha. lia. }
    (* the held list of the slot *)
    pose proof HSLk as HSLkc.
    destruct HSLkc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      HHELD & _).
    pose proof HHELD as HHELDc.
    destruct HHELDc as (_ & _ & _ & _ & _ & HVEC & _ & _ & HRECS).
    (* the stream, as check_shape_ends reads it *)
    assert (HSTR : ob_at W mem (lm_out m) (lm_O m) /\
      Z.of_nat (length (lm_O m)) <= 2 ^ 40 /\
      (0 < Z.of_nat (length (lm_O m)) -> Z.of_nat (length (lm_O m)) < 2 ^ 32) /\
      amem_range (lm_out m) (Z.of_nat (length (lm_O m)) + 8) /\
      (lm_O m = [] \/ exists CO, Z.of_nat (length (lm_O m)) <= CO /\
         In (lm_out m, CO) (ablocks B ly St) /\ ~ In (lm_out m) (hs_blocks h))).
    { destruct HOcase as [(Ecap & Eout0 & Elen0) | (Hcap0 & Hnocap & Hinb & junk & Hjl & Hg8)].
      - assert (HO0 : lm_O m = []) by (apply length_zero_iff_nil; lia).
        split; [intros j Hj; rewrite Elen0 in Hj; lia|].
        split; [rewrite Elen0; lia|].
        split; [rewrite Elen0; lia|].
        split; [unfold amem_range; left; rewrite Elen0, Eout0; unfold kLowMemEnd; lia|].
        left. exact HO0.
      - pose proof (alx_blocks _ _ ARx LAWS ly St [] W mem md1 _ _ HARly1 Hinb)
          as (Hal & H4096 & Hceilb & Happ & _).
        pose proof (BLKN ly St [] W mem md1 _ _ HARly1 Hinb) as Hmm0.
        pose proof (BLKM ly St [] W mem md1 _ _ HARly1 Hinb) as Hmm.
        pose proof (req_size_pos (lm_cap m) ltac:(lia)) as [Hq1 Hq2].
        split; [exact (xe_ob_of_garr8 W mem (lm_out m) (lm_O m) junk Hg8)|].
        split; [lia|].
        split; [intros _; lia|].
        split.
        { unfold amem_range. unfold in_app in Happ. destruct Happ as (_ & [Hlow | (Hhi1 & Hhi2)]).
          - left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
          - right. split; [lia|]. unfold ASAN_CEIL in Hhi2. unfold kHighMemEnd. lia. }
        right. exists (lm_cap m). split; [lia|]. split; [exact Hinb|].
        apply (xc_out_apart_x cx m ly St W mem md1 k h HARly1 HSEP1 Hk4 Hh). lia. }
    destruct HSTR as (HOB & HObound & HObound2 & HOmr & HOdis).
    (* ---- check_shape_ends at the slot's own G ---- *)
    pose proof (CSHE_R (xe_G k) HGk W ly St [] (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) mem md1 ch AX_XO
      (lf_F cx + AX_AT) (xe_HA k) k (VAL AX_lit_empty) h [] A (lm_gn m)
      (Z.of_nat (length (lm_O m))) (lm_out m) (lm_O m)) as HC.
    cbv zeta in HC.
    eapply SRrG_mono.
    { apply HC with (kr := 0%nat).
      + exact HPREc.
      + unfold AX_XO. lia.
      + vm_compute. reflexivity.
      + rewrite Hsp1, Etop. unfold AX_XO. lia.
      + rewrite Hsp1. intros a Ha. apply Hpresj. unfold AX_XO in Ha. unfold LLVMF_STK in *. lia.
      + rewrite Kr; [exact R10 | xc_bvz].
      + rewrite Kr; [exact R11 | xc_bvz].
      + rewrite Kr; [exact R12 | xc_bvz].
      + exact HSLk.
      + unfold xe_HA. rewrite Egsv.
        replace (6131296 + ASRC * Z.of_nat k) with ((766412 + 12 * Z.of_nat k) * 8) by (unfold ASRC; lia).
        apply Z_mod_mult.
      + unfold xe_HA, ASRC. rewrite Egsv. lia.
      + unfold xe_HA, ASRC, kLowMemEnd. rewrite Egsv. lia.
      + intros a Ha. unfold xe_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
      + apply (xe_azs_sub (rg_s fr_RG) (4 * ASRC)); [exact AZS_s | unfold xe_HA, ASRC; lia |
          unfold xe_HA, ASRC; lia].
      + unfold xe_HA. destruct xe_vals as (_ & _ & _ & Exgs & _). rewrite <- Exgs. reflexivity.
      + lia.
      + rewrite Hsp1. intros a Ha.
        unfold xe_HA, ASRC, CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *. rewrite Egsv in Ha. lia.
      + intros a Ha.
        assert (HGa : inG G_fr a) by (apply HGs; unfold xe_HA, ASRC in *; lia).
        destruct (HG a HGa) as (Himg & Hown & _).
        unfold cshe_home. right. left. split; [exact Himg|]. split; [exact Hown|].
        unfold xe_HA, ASRC in *. lia.
      + exact HNDt.
      + exact HNb.
      + rewrite Hsp1. intros a Ha.
        destruct HVEC as [(Ec & Ev) | (Hc0 & Hinv & _)].
        * rewrite Ec in Ha. unfold AREC in Ha. lia.
        * pose proof (alx_blocks _ _ ARx LAWS ly St [] W mem md1 _ _ HARly1 Hinv) as (_ & _ & Hceilv & _).
          pose proof (req_size_pos (AREC * hl_cap (hs_held h)) ltac:(unfold AREC; lia)) as [_ Hgev].
          unfold CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *. lia.
      + rewrite Hsp1. intros r Hr a Ha.
        pose proof (proj1 (Forall_forall _ _) HRECS r Hr) as (Hinr & _).
        pose proof (alx_blocks _ _ ARx LAWS ly St [] W mem md1 _ _ HARly1 Hinr) as (_ & _ & Hceilr & _).
        pose proof (req_size_pos (Z.of_nat (length (snd r)) + 1) ltac:(lia)) as [_ Hger].
        unfold CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *. lia.
      + pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D32. rewrite HFmod, Z.add_0_r in D32.
        unfold AX_AT. replace (lf_F cx + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult.
      + rewrite Hsp1. unfold AX_AT. lia.
      + rewrite Hsp1. unfold AX_AT, AX_XO. lia.
      + apply (xe_ra_stack_x ly St W mem md1); [exact HARly1 | rewrite Eslo; unfold AX_AT, LLVMF_STK in *; lia |
          rewrite Eshi; unfold AX_AT in *; lia | lia].
      + exact HAT1.
      + intros Hc. destruct Hc.
      + cbn [length]. lia.
      + rewrite Hlit. lia.
      + rewrite Hlit. cbn [length]. lia.
      + cbn [length]. intros j Hj. lia.
      + cbn [length]. rewrite Z.add_0_r. exact (proj1 (xe_lit_bytes W mem HRV1)).
      + cbn [length]. intros a Ha.
        split; [apply (proj2 (xe_lit_bytes W mem HRV1)); rewrite Hlit in *; lia|].
        rewrite Hsp1; rewrite Hlit in *.
        unfold CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, LDROP_STK, LDROP_FRAME, ASTACK, AX_XO in *; lia.
      + unfold amem_range. left. rewrite Hlit. cbn [length]. unfold kLowMemEnd. lia.
      + unfold amem_range. left. rewrite Hlit. unfold kLowMemEnd. lia.
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia).
        exact (proj1 (XE_LIT_S ly St [] W mem md1 HARly1)).
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia).
        exact (proj2 (XE_LIT_S ly St [] W mem md1 HARly1) ltac:(lia)).
      + (* the prefix's home: B's spec takes it as one disjunction; .str.3 is a read-only literal *)
        left. split; [cbn [length]; intros a Ha; apply xe_lit_rom; lia|].
        replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia). exact XE_LIT_S.
      + exact (XRF_END5 W mem HRV1).
      + exact HRV1.
      + rewrite Egone. exact (proj1 HGONE).
      + destruct HGONE as (_ & _ & [E0 | E1]); lia.
      + rewrite Enout. exact HOno.
      + rewrite Eoutv. exact HOout.
      + exact HOB.
      + reflexivity.
      + exact HObound.
      + exact HObound2.
      + exact HOmr.
      + exact HOdis.
      + rewrite EO1. lia.
      + intros Hg0 E'. apply Hnone. unfold lx_ends_c1.
        rewrite <- EGN1, Hg0, <- EO1. cbn [Z.eqb]. rewrite E'. reflexivity.
      + apply (mo_ok_le MT MLM St (cshe_cost MT (hs_held h)) (lx_ends_cost (lm_hs m)) HMOK1).
        unfold cshe_cost. exact (xc_cost_nth (lm_hs m) k h Hh).
      + apply RP_NP. exact HNPi1.
      + exact HCNi1. }
    (* ---- the post ---- *)
    intros W2 c2 Hwle2 (ly' & S' & Hp' & regs2 & mem2 & md2 & kk2 & H' & ds & c & -> & HJc & HP2 & _ & HSRC2 & Hv' &
      Hcap' & HND2 & Harms & Hc0 & HAT2 & HGONE2 & HPERM2 & HFRS2 & HMLE2 & HRM').
    (* cshe_post_x's ghost list is [] (HP0 at the post's journal) *)
    assert (Ehp : Hp' = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJc). subst Hp'.
    rewrite Hsp1 in HJc.
    assert (HE : hl_recs H' = [] /\ Permutation (hl_recs (hs_held h)) ds /\
      A + c <= Z.of_nat (length (lm_O m0)) /\
      lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A = Some (hl_recs H', A + c)).
    { destruct Harms as [(Hg & Hrecs & Hds & Hc) | (Hg & Hrun)].
      - assert (Hr0 : hl_recs H' = []) by (rewrite Hrecs; apply xm_filter_nil_f).
        assert (Hds0 : ds = hl_recs (hs_held h)) by (rewrite Hds; apply xm_filter_nil_t).
        split; [exact Hr0|].
        split; [rewrite Hds0; apply Permutation_refl|].
        split; [subst c; rewrite Z.add_0_r; lia|].
        unfold lx_ends_c1. rewrite <- EGN1.
        destruct (Z.eqb_spec (lm_gn m) 0) as [E0 | E0]; [exfalso; exact (Hg E0)|].
        rewrite Hr0, xm_filter_nil_f. subst c. rewrite Z.add_0_r. reflexivity.
      - assert (Hc1e : lx_ends_c1 (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A = Some (hl_recs H', A + c)).
        { unfold lx_ends_c1. rewrite Hg. cbn [Z.eqb]. rewrite Hrun. reflexivity. }
        destruct (xm_c1 (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A (hl_recs H') (A + c) Hc1e) as (Hr0 & Hb).
        destruct (xm_c1_ds (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A (hl_recs H') (A + c) Hc1e) as (_ & Hds2).
        split; [exact Hr0|].
        split; [exact (Hds2 Hg ds c Hrun)|].
        rewrite length_skipn in Hb. rewrite EO1 in Hb.
        split; [lia|].
        rewrite <- EGN1, <- EO1. exact Hc1e. }
    destruct HE as (Hr0 & Hperm_ds & Hbound & Hends).
    destruct (xe_model_after_xR R R_trans cx fpos ly3 S3 m0 norder ord A ly St m W mem md1 k h H' ds c ly' S' W2 mem2 md2 kk2
      HB HI1 Hk4 Hh HJc HSRC2 Hv' Hcap' HND2 Hr0 Hperm_ds HAT2 Hc0 Hbound HPERM2 HFRS2 HMLE2
      (proj1 (RP_NP S' 0%nat) HRM')) as (m' & Hm'hs & HI').
    exists ly', S', regs2, mem2, md2, m', H', (A + c).
    split; [rewrite Q1; reflexivity|].
    split; [exact HI'|].
    split; [exact (xc_slot_kept cx i k n regs regs2 (Z_to_bv 64 (BASE + AX_adv)) HR HP2)|].
    split; [exact Hr0|].
    split; [exact Hends | exact Hm'hs].
Qed.
(* :1898 xe_step_inner_x *)
Lemma xe_step_inner_xR : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) afin,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  xe_inv_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k (4 - Z.of_nat k) regs -> (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  xe_fin (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m)) = Some afin ->
  SRrG segs R W (cfg_at segs (BASE + AX_inner) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (m' : lmod) (A1 : Z),
       c' = cfg_at segs (BASE + AX_adv) regs' mem' md' /\
       xe_inv_xR R cx fpos ly3 S3 m0 norder ord A1 ly' S' m' W' mem' md' /\
       xe_regs_slot cx i k (4 - Z.of_nat k) regs' /\
       xe_fin (lm_gn m0) (lm_O m0) ord norder i (S k) A1 (map lx_ends_slot0 (lm_hs m')) = Some afin).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k afin HB HINV HR Hk4 Hi Hnord HFIN.
  pose proof HINV as (HJx & HFR & HFLW & HFA & HMOD & HINP & HRV & HJT & HSEP & HBF & HLEN & HEVO & HKk & HGG & HES &
    HCC & HOO & HMX & HCAP & HOUTm & HGN & HNFD & HFRS & HMLE & HMOK & HSLOK & HATv & HAb & HNOv & Hn4 & HGS8 & HORDv &
    HNPv & HCNv).
  destruct HJx as (kk & HJ).
  assert (HAR : ARx ly St [] W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  pose proof HMOD as (HL4 & HSLOT & _).
  destruct (HORDv i ltac:(lia)) as (HOI & HOIr).
  destruct (xe_geom_x cx HB) as (Hsp & HFb & HFlo & HFhi).
  (* the slot's two fields, and the model's reduced slot *)
  pose proof (HSLOT k Hk4) as HSL. unfold aslot in HSL.
  assert (Hknth : nth_error (lm_hs m) k = Some (nth k (lm_hs m) None))
    by (apply nth_error_nth'; lia).
  assert (HNE : nth_error (map lx_ends_slot0 (lm_hs m)) k =
                Some (lx_ends_slot0 (nth k (lm_hs m) None))).
  { rewrite nth_error_map, Hknth. reflexivity. }
  destruct (nth k (lm_hs m) None) as [h|] eqn:Ehk.
  - (* an open source *)
    pose proof HSL as (Mfd & Mop & _ & _ & _ & _ & _ & Hopen & Hfdr & _).
    eapply (SRrG_bind segs R R_trans).
    { apply (SRr_SRrG segs R WLE_R). eapply (xe_inner_run_x cx W regs mem md ly St md i k (4 - Z.of_nat k) (hs_open h) (hs_fd h) (ord i));
        first [exact HAR | exact HR | exact Mfd | exact Mop | exact HOI | lia]. }
    cbv beta. intros W' c' _ (-> & regs' & X & [(Hop & Hoi & -> & Ha0 & Ha1 & Ha2 & HR') | (Hsk & -> & HR')]).
    + (* the fd matches: the call *)
      assert (HNE2 : nth_error (map lx_ends_slot0 (lm_hs m)) k = Some (Some (hs_fd h, hl_recs (hs_held h))))
        by (rewrite HNE; try rewrite Ehk; reflexivity).
      eapply SRrG_mono.
      { eapply (xe_call_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem
                  (with_vm_backing (m_vm_lazy md) X md) regs' i k (4 - Z.of_nat k) h HB
                  (xe_inv_materialize_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)
                  HR' Ha0 Ha1 Ha2 Hk4 Ehk).
        exact (xm_fin_c1_ne (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                 (hs_fd h) (hl_recs (hs_held h)) afin HNE2 (eq_sym Hoi) HFIN). }
      cbv beta. intros W2 c2 _ (ly' & S' & regs2 & mem2 & md2 & m' & H' & A1 & -> & HINV2 & HR2 & HH' & HC1 & HHS).
      exists ly', S', regs2, mem2, md2, m', A1.
      split; [reflexivity|]. split; [exact HINV2|]. split; [exact HR2|].
      assert (ESL : map lx_ends_slot0 (lm_hs m') =
                    xe_set_nth k (Some (hs_fd h, hl_recs H')) (map lx_ends_slot0 (lm_hs m))).
      { rewrite HHS, xm_slot0_set. cbn [lx_ends_slot0 CheckRep.set_held hs_fd hs_held]. reflexivity. }
      rewrite ESL.
      rewrite <- (xm_fin_call (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                    (hs_fd h) (hl_recs (hs_held h)) (hl_recs H') A1 HNE2 (eq_sym Hoi) HC1).
      exact HFIN.
    + (* the slot is skipped *)
      apply (SRrG_ret segs R R_refl).
      exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), m, A.
      split; [reflexivity|].
      split; [exact (xe_inv_materialize_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)|].
      split; [exact HR'|].
      rewrite <- (xm_fin_skip (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                    (lx_ends_slot0 (Some h)) HNE).
      * exact HFIN.
      * right. exists (hs_fd h), (hl_recs (hs_held h)).
        split; [try rewrite Ehk; reflexivity|].
        destruct Hsk as [Hz | Hne]; [rewrite Hopen in Hz; discriminate | intros Heq; apply Hne; symmetry; exact Heq].
  - (* a closed slot: its fd and open fields read 0, so the loop skips it *)
    destruct (xe_closed_vals W mem (rg_s fr_RG + ASRC * Z.of_nat k) HSL) as (Mfd & Mop).
    assert (EHA : rg_s fr_RG + ASRC * Z.of_nat k = xe_HA k) by reflexivity.
    rewrite EHA in Mfd, Mop.
    eapply (SRrG_bind segs R R_trans).
    { apply (SRr_SRrG segs R WLE_R). eapply (xe_inner_run_x cx W regs mem md ly St md i k (4 - Z.of_nat k) 0 0 (ord i));
        first [exact HAR | exact HR | exact Mfd | exact Mop | exact HOI | lia]. }
    cbv beta. intros W' c' _ (-> & regs' & X & [(Hop & _ & _ & _ & _ & _ & _) | (Hsk & -> & HR')]);
      [exfalso; exact (Hop eq_refl)|].
    apply (SRrG_ret segs R R_refl).
    exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), m, A.
    split; [reflexivity|].
    split; [exact (xe_inv_materialize_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)|].
    split; [exact HR'|].
    rewrite <- (xm_fin_skip (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                  (lx_ends_slot0 None) HNE).
    * exact HFIN.
    * left. try rewrite Ehk. reflexivity.
Qed.
(* :1985 xe_loop_x *)
Lemma xe_loop_xR : forall (fuel : nat) cx t fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) afin,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  (Z.to_nat (4 * (norder - i)) - S k < fuel)%nat ->
  xe_inv_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k (4 - Z.of_nat k) regs ->
  lx_ends_run (lm_gn m0) (lm_O m0) norder ord (lm_hs m0) 0 = Some afin ->
  xe_fin (lm_gn m0) (lm_O m0) ord norder i (S k) A (map lx_ends_slot0 (lm_hs m)) = Some afin ->
  SRrG segs R W (cfg_at segs (BASE + AX_adv) regs mem md) ((lx_ends_post_xR B MT NP G_fr fr_FP PST ARx R RP) cx t fpos ly3 S3 m0 norder ord).
Proof.
  induction fuel as [|fuel IH];
    intros cx t fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k afin HB Hk4 Hi Hnord Hfuel HINV HR
      HRUN HFIN; [exfalso; lia|].
  pose proof HINV as (HJx & HFR & HFLW & HFA & HMOD & HINP & HRV & HJT & HSEP & HBF & HLEN & HEVO & HKk & HGG & HES &
    HCC & HOO & HMX & HCAP & HOUTm & HGN & HNFD & HFRS & HMLE & HMOK & HSLOK & HATv & HAb & HNOv & Hn4 & HGS8 & HORDv &
    HNPv & HCNv).
  destruct HJx as (kk & HJ).
  destruct (xe_geom_x cx HB) as (Hsp & HFb & HFlo & HFhi).
  assert (HSL4 : length (map lx_ends_slot0 (lm_hs m)) = 4%nat) by (rewrite length_map; exact HLEN).
  eapply (SRrG_bind segs R R_trans).
  { apply (SRr_SRrG segs R WLE_R). eapply (xe_adv_run cx W regs mem md i k norder HR Hk4 Hi Hnord HFlo HFhi HNOv). }
  cbv beta. intros W' c' _ (-> & regs' & X & [(Hk' & -> & HR') | [(Hk4' & Hin & -> & HR') | (Hk4' & Hie & -> & HRK)]]).
  - (* the next slot of this trip *)
    eapply (SRrG_bind segs R R_trans).
    { eapply (xe_step_inner_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem
                (with_vm_backing (m_vm_lazy md) X md) regs' i (S k) afin HB
                (xe_inv_materialize_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)
                HR' Hk' Hi Hnord HFIN). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & m2 & A2 & -> & HINV2 & HR2 & HFIN2).
    exact (IH cx t fpos ly3 S3 m0 norder ord A2 ly2 S2 m2 W2 mem2 md2 regs2 i (S k) afin HB Hk' Hi Hnord
             ltac:(lia) HINV2 HR2 HRUN HFIN2).
  - (* the next trip *)
    assert (HFIN' : xe_fin (lm_gn m0) (lm_O m0) ord norder (i + 1) 0 A (map lx_ends_slot0 (lm_hs m)) = Some afin).
    { rewrite <- (xm_fin_next (lm_gn m0) (lm_O m0) ord norder i A (map lx_ends_slot0 (lm_hs m)) HSL4
                    ltac:(lia) ltac:(lia)).
      rewrite <- Hk4'. exact HFIN. }
    eapply (SRrG_bind segs R R_trans).
    { apply (SRr_SRrG segs R WLE_R). eapply (xe_head_run cx W regs' mem (with_vm_backing (m_vm_lazy md) X md) (i + 1) norder HR'
                ltac:(lia) HFlo HFhi HGS8). }
    cbv beta. intros W2 c2 _ (-> & regs2 & X2 & -> & HR2).
    eapply (SRrG_bind segs R R_trans).
    { eapply (xe_step_inner_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem
                (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X md)) X2
                   (with_vm_backing (m_vm_lazy md) X md)) regs2 (i + 1) 0%nat afin HB
                (xe_inv_materialize_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem
                   (with_vm_backing (m_vm_lazy md) X md) X2
                   (xe_inv_materialize_xR R cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV))
                HR2 ltac:(lia) ltac:(lia) Hnord HFIN'). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2' & mem2 & md2 & m2 & A2 & -> & HINV2 & HR2' & HFIN2).
    exact (IH cx t fpos ly3 S3 m0 norder ord A2 ly2 S2 m2 W2 mem2 md2 regs2' (i + 1) 0%nat afin HB
             ltac:(lia) ltac:(lia) Hnord ltac:(lia) HINV2 HR2' HRUN HFIN2).
  - (* the last trip is done: 0x84d4c, with the `at` cell at its final value *)
    apply (SRrG_ret segs R R_refl).
    assert (EA : afin = A).
    { pose proof (xm_fin_done (lm_gn m0) (lm_O m0) ord norder i A (map lx_ends_slot0 (lm_hs m)) HSL4
        ltac:(lia)) as HD.
      rewrite <- Hk4' in HD. rewrite HD in HFIN. injection HFIN as <-. reflexivity. }
    pose proof HRK as (R2 & R9 & R8 & R3 & R4 & _).
    exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), kk, m, A.
    split; [reflexivity|].
    split; [eapply (ajournal_gx_materialize_xR segs B PST ARx LAWS pa_segs_low); exact HJ|].
    split; [exact HFR|]. split; [exact HFLW|]. split; [exact HFA|]. split; [exact HMOD|]. split; [exact HINP|].
    split; [exact HRV|]. split; [exact HJT|]. split; [exact HSEP|]. split; [exact HBF|].
    split; [exact R2|]. split; [exact R8|]. split; [exact R9|]. split; [exact R3|]. split; [exact R4|].
    split; [exact HATv|]. split; [lia|].
    split; [congruence|].
    split; [exact HKk|]. split; [exact HGG|]. split; [exact HES|]. split; [exact HCC|].
    split; [exact HOO|]. split; [exact HMX|]. split; [exact HCAP|]. split; [exact HOUTm|].
    split; [exact HGN|]. split; [exact HNFD|]. split; [exact HLEN|]. split; [exact HEVO|].
    split; [exact HFRS|].
    split; [eapply (mo_le_mono MT MLM); [exact HMLE|]; pose proof (xe_cost_nonneg (lm_hs m)); lia|].
    split; [exact HNPv | exact HCNv].
Qed.
(* :2059 lx_ends_x *)
Lemma lx_ends_xR : lx_ends_S_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx R RP.
Proof.
(* The block, assembled: the entry run stores norder at F+152 and the shadow cursor at F+144 and sets the cursors
   (xe_entry_run_xR R WLE_R), the outer head sets the slot cursors of trip 0 (xe_head_run), the first inner trip runs
   (xe_step_inner_xR) and the two loops then run to 0x84fe8 (xe_loop_xR).  The model side is xe_fin, which at (0, 0) is
   lx_ends_run.  The entry's aframe_at is weakened to bx_frame: its F+152 cell is the one the entry overwrites. *)
  unfold lx_ends_S_xR.
  intros cx t fpos ly3 S3 m norder ord regs mem md W kk HJ HFR0 HFL HMOD HINP HRV HJT HSEP HMOK HSLOK HRUN
    R2 R8 R9 R27 R19 R3 R4 Hnord HAT HORD HB HNP3 HCN3.
  pose proof (bx_frame_of_aframe _ _ _ _ HFR0) as HFR. clear HFR0.
  destruct (xe_geom_x cx HB) as (Hsp & HFb & HFlo & HFhi).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFR as (_ & HAWR & _).
  assert (HAR : ARx ly3 S3 [] W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _).
    pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (lx_ends_run (lm_gn m) (lm_O m) norder ord (lm_hs m) 0) as [afin|] eqn:ERUN;
    [|exfalso; exact (HRUN eq_refl)].
  (* (1) 0x84c74 -> 0x84c9c *)
  eapply (SRrG_bind segs R R_trans).
  { eapply (xe_entry_run_xR R WLE_R cx W regs mem md LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 kk norder HJ
      R2 R9 R8 R3 R4 R19 R27 Hnord ltac:(unfold LLVMF_STK; lia) ltac:(unfold AX_XO; lia) HFlo HFhi HAWR). }
  cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & X & -> & HJ1 & HRO1 & HNO1 & HGS1 & HKEEP & HPRES).
  destruct (xe_carry_x cx W mem mem1 md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
              HFR HMOD HINP HRV HJT HKEEP HPRES) as (HFR1 & HMOD1 & HINP1 & HRV1 & HJT1 & HVAL1).
  assert (HFL1 : sv8 W mem1 (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)).
  { destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem md 1 fpos HAR Hfin) as (HFF0 & HFF1 & _).
    change (fs_frame_bytes 1) with 128 in HFF1. unfold sv8 in HFL |- *.
    apply (xe_vm_view W W mem mem1); [|exact HFL]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
    apply HKEEP; unfold AX_GS8; lia. }
  assert (HINV : xe_inv_xR R cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1 (with_vm_backing (m_vm_lazy md) X md)).
  { split; [exists kk; exact HJ1|].
    split; [exact HFR1|]. split; [exact HFL1|]. split; [reflexivity|]. split; [exact HMOD1|]. split; [exact HINP1|].
    split; [exact HRV1|]. split; [exact HJT1|]. split; [exact HSEP|].
    split; [intros rest HP; exact HP|].
    split; [exact (proj1 HMOD1)|].
    split; [intros j Hj; left; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [destruct (lm_c m); reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [replace (lx_ends_cost (lm_hs m) - lx_ends_cost (lm_hs m)) with 0 by ring;
            exact (mo_le_refl MT MLM S3)|].
    split; [exact HMOK|].
    split; [exact HSLOK|].
    split; [exact (HVAL1 (lf_F cx + AX_AT) 8%nat 0 ltac:(unfold AX_ORDER, AX_AT; lia)
                     ltac:(unfold AX_AT; lia) HAT)|].
    split; [lia|].
    split; [exact HNO1|].
    split; [exact Hnord|].
    split; [exact HGS1|].
    split.
    { intros i Hi. destruct (HORD i Hi) as (HV & HR0). split; [|exact HR0].
      exact (HVAL1 (lf_F cx + AX_ORDER + 4 * i) 4%nat (ord i) ltac:(unfold AX_ORDER; lia)
               ltac:(unfold AX_ORDER, AX_AT; lia) HV). }
    split; [exact HNP3 | exact HCN3]. }
  (* (2) 0x84c9c -> 0x84cbc, then the first inner trip *)
  eapply (SRrG_bind segs R R_trans).
  { apply (SRr_SRrG segs R WLE_R). eapply (xe_head_run cx W regs1 mem1 (with_vm_backing (m_vm_lazy md) X md) 0 norder HRO1
              ltac:(lia) HFlo HFhi HGS1). }
  cbv beta. intros W2 c2 _ (-> & regs2 & X2 & -> & HR2).
  assert (HFIN0 : xe_fin (lm_gn m) (lm_O m) ord norder 0 0%nat 0 (map lx_ends_slot0 (lm_hs m)) = Some afin).
  { rewrite (xm_fin_start (lm_gn m) (lm_O m) ord norder 0 (map lx_ends_slot0 (lm_hs m)) ltac:(lia)).
    unfold lx_ends_run in ERUN. exact ERUN. }
  eapply (SRrG_bind segs R R_trans).
  { eapply (xe_step_inner_xR cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1
              (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X md)) X2
                 (with_vm_backing (m_vm_lazy md) X md)) regs2 0 0%nat afin HB
              (xe_inv_materialize_xR R cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1
                 (with_vm_backing (m_vm_lazy md) X md) X2 HINV)
              HR2 ltac:(lia) ltac:(lia) Hnord HFIN0). }
  cbv beta. intros W3 c3 _ (ly' & S' & regs3 & mem3 & md3 & m' & A1 & -> & HINV3 & HR3 & HFIN3).
  (* (3) the two loops *)
  exact (xe_loop_xR (S (Z.to_nat (4 * norder))) cx t fpos ly3 S3 m norder ord A1 ly' S' m' W3 mem3 md3 regs3
           0 0%nat afin HB ltac:(lia) ltac:(lia) Hnord ltac:(lia) HINV3 HR3 ERUN HFIN3).
Qed.
End wR.
End lxx.
