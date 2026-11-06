(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx (generic allocator relation) conversion of image B's block `reset` of SEG_EXIT
   (fuzz_reply.asan-ubsan 0x84fe8 `ld a0,208(s1); jal check_shape_done`, the loop set-up 0x84ff0..0x85000 and the four
   trips of `mv a0,s3; jal source_reset; addi s3,s3,96; bne s3,s2` to 0x85014): it proves lib/B/W_bx_defs_x.v's
   lx_reset_S_x.  The AR file is NOT edited.
   SOURCE: lib/B/W_bx_reset.v (lx_reset, Qed), converted lemma by lemma.  TEMPLATE: image A's conversion of the same
   block, e60b29a425a lib/A/W_LLVMFuzzerTestOneInput_exit_x.v :3573-4389
   (lx_reset_post_x .. lx_reset_x; its lx_afn_pre_at_x :246-342), against its AR original
   b86949b953d lib/A/W_LLVMFuzzerTestOneInput_exit.v :5898-7421.
   What changes against the AR proof, and nothing else:
   - the journal is ajournal_gx_x over ARx with the ghost head list [] (HP0 makes it [] in every ARx state; the
     source_reset post's Hp' is read [] through HP0 at its journal); AR's laws are AR_laws_x (alx_blocks, alx_sep,
     alx_layout, alx_client_img, frames_bounds_x), with BLKN for a live block's size and HPST for the image clause;
   - the callees are the kit's csd_spec_x and sr_spec_g_x (lib/B/W_contract_x.v :119, :395); csd_spec_x's post is
     aleaf_post_x, whose presence and errno-view clauses are two conjuncts;
   - W_bx_defs.v's lx_afn_pre_at (Section kit, over AR) is converted here as lx_afn_pre_at_x (A's :328 form over
     bx_frame);
   - xr_jkeep_blk_x reads "a live block's byte is off the image" from alx_client_img's block clause, not from the
     kit's blk_off_imgP_x: that lemma states off_img at image A's top 0x5fb000, and image B's segments reach 0x5fc000.
   Everything AR-free is CITED from lib/B/W_bx_reset.v (Imported): the byte, list, footprint, model, cost and symbolic-
   entry lemmas, through the local abbreviations below where they take Section arguments.  bx_frame is on both sides;
   the loop invariant and the post carry x20 and x24 (B loads no s7). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_bx_reset.
(* route R: SRrG (YA0nH) and the callees' contracts at R (W_contract_srlf_xR: csd_spec_xR, sr_spec_g_xR) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_srlf_xR.
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

(* ---- the hypotheses this block takes, verbatim from lib/B/W_LLVMFuzzerTestOneInput_exit_x.v's Section ---- *)
Hypothesis MLM : ameter_laws MT.
Hypothesis ERR : errno_law_x B ARx.
Hypothesis AZS_s : azs B (rg_s fr_RG) (4 * ASRC).
Hypothesis CSD : csd_spec_x B PST ARx (BASE + AF_fr_check_shape_done).
(* ---- the room round (image A's exit_x at 5a9b16eac9e): the allocator rules' room record RP, whose room invariant is
   the cut's NP (cand13's kit, W_journal_x.v Record roomp) ---- *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis SR : sr_spec_g_x B PST ARx MT RP (BASE + AF_fr_source_reset).
Hypothesis XRF_ROM_OUT : rom_out segs B G_fr.
Hypothesis XR_HGM : forall a, inG xr_GM a -> inG G_fr a.
Hypothesis XR_GSHV : forall ly S Hp (W : world segs) mem md a n, ARx ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> rg_s fr_RG <= x < rg_s fr_RG + 4 * ASRC) ->
  shadow_hull_vis (aview segs (w_H W) mem) a n.
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  0 <= n.
(* ... and the derived fact the AR file takes, verbatim from lib/B/W_bx_reset.v (the spine proves it from XR_HGM and
   XRF_ERRNO) *)
Hypothesis XR_ERRNO : forall a, inG xr_GM a -> ~ (as_errno B <= a < as_errno B + 4).

(* ---- the AR file's AR-free definitions and lemmas with Section arguments, cited ---- *)
Local Notation xr_kb := (W_bx_reset.xr_kb B).
Local Notation xr_akept_cov := (W_bx_reset.xr_akept_cov B).
Local Notation xr_asrc_cov := (W_bx_reset.xr_asrc_cov B).
Local Notation xr_asrc_live := (W_bx_reset.xr_asrc_live B).
Local Notation xr_asrc_pos := (W_bx_reset.xr_asrc_pos B).
Local Notation xr_rest_kept := (W_bx_reset.xr_rest_kept B).
Local Notation xr_ainput_kept := (W_bx_reset.xr_ainput_kept B).
Local Notation xr_bxframe_kept := (W_bx_reset.xr_bxframe_kept B).
Local Notation xr_azs_sub := (W_bx_reset.xr_azs_sub B).
Local Notation xr_mid0 := (W_bx_reset.xr_mid0 B).
Local Notation xr_rom_out_sub := (W_bx_reset.xr_rom_out_sub B G_fr XRF_ROM_OUT).
Local Notation xr_cost := (W_bx_reset.xr_cost MT).
Local Notation xr_cost_skip := (W_bx_reset.xr_cost_skip MT).
Local Notation xr_cost_first := (W_bx_reset.xr_cost_first MT).
Local Notation xr_cost_all := (W_bx_reset.xr_cost_all MT).
Local Notation xr_cost_nonneg := (W_bx_reset.xr_cost_nonneg MT MLM).

(* the ROM bytes lie outside PST (ajournal_gx_rom_view_x's premise): ROM bytes are image bytes *)
Lemma PST_ROM : forall a, in_rom segs a -> ~ Exists (in_zr a) PST.
Proof. intros a (sg & H1 & _ & H3). apply HPST. exists sg. split; assumption. Qed.

(* the symbolic-run scaffolding (cut_x's) *)
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).


Lemma xr_blk_present_x : forall ly S (W : world segs) mem md p n a, ARx ly S [] W mem md ->
  In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> apresent (w_H W) mem a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha.
  destruct (alx_blocks _ _ ARx LAWS ly S [] W mem md p n HAR Hin) as (_ & _ & _ & _ & Hp & _). exact (proj1 (Hp a Ha)).
Qed.

(* ---- lists of blocks ---- *)
(* two different live blocks are apart *)
Lemma xr_blk_apart_x : forall ly S (W : world segs) mem md b1 b2, ARx ly S [] W mem md ->
  In b1 (ablocks B ly S) -> In b2 (ablocks B ly S) -> b1 <> b2 ->
  fst b1 + req_size (snd b1) <= fst b2 \/ fst b2 + req_size (snd b2) <= fst b1.
Proof.
  intros ly S W mem md b1 b2 HAR H1 H2 Hne.
  destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  exact (xr_pw_map (fun b => (fst b, req_size (snd b))) zdisjoint xr_zd_sym _ b1 b2 Hp H1 H2 Hne).
Qed.
(* a live block and a fake frame are apart *)
Lemma xr_blk_frame_apart_x : forall ly S (W : world segs) mem md b cid pos, ARx ly S [] W mem md ->
  In b (ablocks B ly S) -> In (cid, pos) (frames S) ->
  fst b + req_size (snd b) <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= fst b.
Proof.
  intros ly S W mem md b cid pos HAR H1 H2.
  destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _].
  exact (xr_pw_app zdisjoint _ _ _ _ Hp (in_map (fun b => (fst b, req_size (snd b))) _ _ H1)
    (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ _ H2)).
Qed.
(* W_gestures_end.v gse_nodup; a block's size is non-negative by BLKN (alx_blocks carries no size bound) *)
Lemma xr_nodup_x : forall ly S (W : world segs) mem md, ARx ly S [] W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR. destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _].
  apply pairwise_app_l in Hp as [Hp _].
  assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S [] W mem md p n HAR Hin) as Hn.
    cbn [snd]. pose proof (req_size_pos n ltac:(lia)). lia. }
  induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. inversion Hpos as [|? ? Hb Hl]; subst.
  apply List.NoDup_cons; [|exact (IH Hp Hl)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.

(* concrete addresses of fuzz_reply.asan-ubsan's globals (lib/B/W_rep.v fr_globals_b, the cut's AG_NFD etc.); the AR
   file's Ltacs, restated (they are Section-local there) *)
Ltac xr_num := unfold AG_NFD, AG_THREAD_UP, AG_LISTEN, ASRC, fr_RG in *;
  cbn [fr_globals_b rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *.
Ltac xr_inGM := unfold xr_GM;
  repeat (apply (proj2 (inG_cons _ _ _)); first [left; unfold in_zr; cbn [fst snd]; xr_num; lia | right]).



(* ------------------------------------------------------------------ source_reset's globals: a slot of g_s
   source_reset's own G: W_contract_x.v gx_prog_x at the slot, its image facts by vm_compute at PB_fr; B's gx_rt names
   the GOT slot A_OBJ 0 and the shadow cell A_OBJ 30 (lib/B/W_contract.v A_got_shadow / A_shadow_cell) *)
Lemma xr_gxp_x : forall i, (i < 4)%nat -> gx_prog_x B ARx [(xr_HA i, ASRC)].
Proof.
  intros i Hi.
  assert (Hsub : forall a, inG [(xr_HA i, ASRC)] a -> inG G_fr a)
    by (intros a Ha; apply XR_HGM; apply xr_gs_GM; exact (xr_slot_gs i a Hi Ha)).
  assert (H0 : ((rg_s fr_RG + 4 * ASRC <=? VAL (A_OBJ 0)) || (VAL (A_OBJ 0) + 8 <=? rg_s fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  assert (H1 : ((rg_s fr_RG + 4 * ASRC <=? VAL (A_OBJ 30)) || (VAL (A_OBJ 30) + 8 <=? rg_s fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  apply orb_prop in H0, H1.
  split; [exact (gx_ok_sub segs B _ G_fr Hsub HG)|].
  split.
  { intros a Ha. pose proof (xr_slot_gs i a Hi Ha) as Hg.
    split; [exact (XR_ERRNO a (xr_gs_GM a Hg))|].
    destruct H0 as [H0|H0]; destruct H1 as [H1|H1]; apply Z.leb_le in H0; apply Z.leb_le in H1; split; lia. }
  split.
  { intros a Ha. destruct (XRF_ROM_OUT a Ha) as (Hn & Ho & He & Hk).
    split; [intros Hin; exact (Hn (Hsub a Hin)) | exact (conj Ho (conj He Hk))]. }
  split; [intros a Ha; exact (xr_gs_rom a (xr_slot_gs i a Hi Ha))|].
  split; [intros a Ha; exact (xr_gs_wr a (xr_slot_gs i a Hi Ha))|].
  intros ly S Hp W mem md a n HAR Hn Hx. apply (XR_GSHV ly S Hp W mem md a n HAR Hn).
  intros x Hx'. exact (xr_slot_gs i x Hi (Hx x Hx')).
Qed.

(* ---- one call keeps the model: everything but the slots it is handed, and errno, by the keep bundle ---- *)
Lemma xr_slot_kept_x : forall Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j o,
  ARx ly1 S1 [] W1 m1 md1 -> (j < 4)%nat ->
  aslot B ly1 S1 W1 m1 j o ->
  (forall a, inG Gc a -> ~ (xr_HA j <= a < xr_HA j + ASRC)) ->
  (forall b, In b (slot_blks o) -> ~ In b BLx) ->
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  aslot B ly2 S2 W2 m2 j o.
Proof.
  intros Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j o HAR Hj Hs HGc HBL HK. pose proof HK as (K1 & K2 & _ & _).
  assert (Hgs : forall a, xr_HA j <= a < xr_HA j + ASRC -> inG xr_GM a)
    by (intros a Ha; apply xr_gs_GM; unfold xr_HA, ASRC in *; lia).
  assert (KS : forall a, xr_HA j <= a < xr_HA j + ASRC -> abyte_kept W1 m1 W2 m2 a)
    by (intros a Ha; apply K1; [exact (Hgs a Ha) | intros Hc; exact (HGc a Hc Ha)]).
  destruct o as [h|]; unfold aslot in *.
  - apply (asrc_at_kept B ly1 S1 W1 m1); [exact Hs | |].
    + apply (xr_akept_cov Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 (asrc_blks h) _
        (fun a => xr_HA j <= a < xr_HA j + ASRC) HK).
      * intros b Hb. split; [exact (xr_asrc_live _ _ _ _ _ _ Hs b Hb) | exact (HBL b Hb)].
      * intros a Ha. split; [exact (Hgs a Ha) | intros Hc; exact (HGc a Hc Ha)].
      * intros r Hr. destruct (xr_asrc_cov _ _ _ _ _ _ Hs r Hr) as [Hin | Hbl];
          [left; intros a Ha; unfold xr_HA in *; lia | right; right; exact Hbl].
    + intros b Hb. exact (proj1 (K2 b (xr_asrc_live _ _ _ _ _ _ Hs b Hb) (HBL b Hb))).
  - destruct Hs as [Hg Hw]. split.
    + apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx. rewrite repeat_length in Hx.
      apply KS. unfold xr_HA, ASRC in *. lia.
    + apply (akept_awr W1 m1); [|exact Hw]. intros x Hx. apply KS. unfold xr_HA in *. lia.
Qed.
Lemma xr_model_step_x : forall cx (m : lmod) i ev ev2 Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 rest0,
  (i < 4)%nat -> length (lm_hs m) = 4%nat ->
  ARx ly1 S1 [] W1 m1 md1 ->
  amodel_at B ly1 S1 W1 m1 (xr_mid m i ev) ->
  Permutation (ablocks B ly1 S1) (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest0) ->
  (forall a, inG Gc a -> xr_HA i <= a < xr_HA i + ASRC) ->
  (forall b, In b BLx -> In b (slot_blks (nth i (lm_hs m) None))) ->
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  asrc_closed W2 m2 (xr_HA i) ->
  val_mem segs (arm W2 m2) (as_errno B) 4 ev2 -> awr W2 m2 (as_errno B) 4 -> 0 <= ev2 < 2 ^ 32 ->
  amodel_at B ly2 S2 W2 m2 (xr_mid m (S i) ev2).
Proof.
  intros cx m i ev ev2 Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 rest0 Hi Hlen HAR1 HMOD HP HGc HBLx HK Hcl
    Hev Hevw Hevr.
  pose proof (Permutation_NoDup HP (xr_nodup_x ly1 S1 W1 m1 md1 HAR1)) as HND.
  pose proof (Permutation_NoDup (xr_mb_perm cx m i ev ev2 rest0 Hi Hlen) HND) as HND2.
  assert (HY : forall b, In b (input_blks cx ++ model_blks (xr_mid m (S i) ev2) ++ rest0) -> ~ In b BLx)
    by (intros b Hb Hx; exact (xr_nodup_app _ _ b HND2 (HBLx b Hx) Hb)).
  assert (HYm : forall b, In b (model_blks (xr_mid m (S i) ev2)) -> ~ In b BLx)
    by (intros b Hb; apply HY; apply in_or_app; right; apply in_or_app; left; exact Hb).
  pose proof HMOD as (_ & Hsl & _).
  apply (xr_rest_kept (xr_mid m i ev) (xr_hs (S i) (lm_hs m)) ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 HMOD).
  - intros a Ha. pose proof (HGc a Ha). unfold xr_HA, ASRC in *. lia.
  - intros b Hb. apply HYm. unfold model_blks, xr_mid. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    apply in_app_or in Hb as [Hb | Hb].
    + unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [left; reflexivity|].
      right. apply in_or_app. left. exact Hb.
    + right. apply in_or_app. right. apply in_or_app. right. exact Hb.
  - exact HK.
  - exact Hev.
  - exact Hevw.
  - exact Hevr.
  - apply xr_hs_len; lia.
  - intros j Hj. rewrite xr_nth_hs by lia.
    pose proof (Hsl j Hj) as Hs. cbn [lm_hs xr_mid] in Hs. rewrite xr_nth_hs in Hs by lia.
    destruct (Nat.ltb_spec j (S i)).
    + destruct (Nat.eq_dec j i) as [-> | Hne]; [exact Hcl|].
      destruct (Nat.ltb_spec j i); [|lia].
      apply (xr_slot_kept_x Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j None HAR1 Hj Hs); [| intros b [] | exact HK].
      intros a Ha Hr. pose proof (HGc a Ha). unfold xr_HA, ASRC in *. lia.
    + destruct (Nat.ltb_spec j i); [lia|].
      apply (xr_slot_kept_x Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j (nth j (lm_hs m) None) HAR1 Hj Hs);
        [| | exact HK].
      * intros a Ha Hr. pose proof (HGc a Ha). unfold xr_HA, ASRC in *. lia.
      * intros b Hb. apply HYm. unfold model_blks, xr_mid. cbn [lm_G lm_es lm_hs lm_cap lm_out].
        right. apply in_or_app. right. apply in_or_app. left.
        apply (xr_slot_in (S i) (lm_hs m) j b); [lia | exact Hlen | exact Hj | lia | exact Hb].
Qed.
Lemma xr_model_keep_x : forall (m : lmod) i ev ev2 FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2,
  (i <= 4)%nat -> length (lm_hs m) = 4%nat -> ARx ly1 S1 [] W1 m1 md1 ->
  amodel_at B ly1 S1 W1 m1 (xr_mid m i ev) ->
  xr_kb [] [] FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  val_mem segs (arm W2 m2) (as_errno B) 4 ev2 -> awr W2 m2 (as_errno B) 4 -> 0 <= ev2 < 2 ^ 32 ->
  amodel_at B ly2 S2 W2 m2 (xr_mid m i ev2).
Proof.
  intros m i ev ev2 FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 Hi Hlen HAR1 HMOD HK Hev Hevw Hevr.
  pose proof HMOD as (_ & Hsl & _).
  apply (xr_rest_kept (xr_mid m i ev) (xr_hs i (lm_hs m)) ev2 [] [] FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 HMOD);
    [intros a Ha; exfalso; exact (inG_nil a Ha) | intros b _ [] | exact HK | exact Hev | exact Hevw | exact Hevr
    | apply xr_hs_len; lia |].
  intros j Hj. apply (xr_slot_kept_x [] [] FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j _ HAR1 Hj (Hsl j Hj));
    [intros a Ha; exfalso; exact (inG_nil a Ha) | intros b _ [] | exact HK].
Qed.
Lemma xr_frames_kept_x : forall G XO OUT STK sp FP ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k,
  ajournal_gx_x segs B PST ARx G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 [] ly2 S2 [] W2 m2 md2 k -> frames S2 = frames S1.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & Hfr & _). exact Hfr.
Qed.
(* ------------------------------------------------------------------ the frame's numbers *)
Lemma xr_F_bounds_x : forall cx, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  alloc_ceiling + LLVMF_STK - 352 <= lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  lf_F cx mod 32 = 0 /\ 2 ^ 46 <= lf_F cx /\ spZ (c_regs cx) <= lf_F cx + 352.
Proof.
  intros cx (_ & HPRE). pose proof (proj1 HPRE) as HAFN.
  pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold lf_F. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  split; [unfold LLVMF_STK in *; lia|]. split; [lia|]. split; [lia|]. split.
  - rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity.
  - split; [unfold LLVMF_STK in *; lia | lia].
Qed.

(* ------------------------------------------------------------------ the reset loop (0x85004, four trips) *)
Ltac xr_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Ltac xr_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* the loop head 0x85004 of trip i (i = 4: the fall-through 0x85014) *)
Definition xr_inv_x (cx : lfcx) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate) (i : nat)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S k ev,
    c = cfg_at segs (BASE + (if (i <? 4)%nat then AX_reset_loop else AX_ffexit)) regs mem md /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md k /\
    frame_addr ly 1 fpos = frame_addr ly3 1 fpos /\
    bx_frame cx (frame_addr ly3 1 fpos) W mem /\
    sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    getr regs 2 = w64 (lf_F cx) /\ getr regs 9 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\
    getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
    getr regs 19 = w64 (xr_HA i) /\ getr regs 18 = w64 (xr_HA 4) /\
    getr regs 20 = w64 (frame_addr ly3 1 fpos) /\
    getr regs 24 = w64 (SB + frame_addr ly3 1 fpos / 8) /\
    amodel_at B ly S W mem (xr_mid m i ev) /\
    (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly S) (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest)) /\
    ainput_at B cx ly S W mem /\
    rom_view segs W mem /\
    mo_le MT S3 S (xr_cost (firstn i (lm_hs m))) /\
    mo_ok MT S (xr_cost (skipn i (lm_hs m))) /\
    NP S /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly S).

(* ================================================================== route R: the block at a world relation R (the
   reply's shape, a working branch 7d2979ecc661 cut_x).  Each <name>R is <name> with the journal
   ajournal_gx_x segs B PST ARx -> ajournal_gx_xR segs B PST ARx R, SRr segs -> SRrG segs R, the post / statement
   lx_reset_post_x / lx_reset_S_x -> lib/B/W_bx_defs_x.v's _xR twins, the callees' contracts CSD / SR -> CSD_R / SR_R,
   the runs / branch -> their SRrG forms, the journal lemmas -> their _xR twins (W_journal_x.v, YCbqG.v, W_frame_x.v)
   and this file's journal helpers -> the _xR twins below; every other token, and each proof, is the strict text's.
   At R := wle each is its strict text by conversion: the strict lemmas after the Section are these at wle (moved
   below the Section; their statements are unchanged). *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
(* the callees at R (lib/B/W_contract_srlf_xR.v, a working branch bcac56210a75): SR_R is the G4 row
   W_bx_reset_x.v:114 SR (source_reset's contract) at R; CSD_R is CSD (:109, check_shape_done's contract) at R *)
Hypothesis CSD_R : csd_spec_xR B PST ARx R (BASE + AF_fr_check_shape_done).
Hypothesis SR_R : sr_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_source_reset).
(* the runs and the branch at R (W_journal_x.v paj_run_x_xG / paj_run_to_x_xG, W_kit.v paj_branch_xR): the walks
   below cross source_reset's / check_shape_done's frees, so they are SRrG walks, not strict walks lifted *)
Let RUNG := paj_run_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let BRR := paj_branch_xR (PI := PB_fr) (R := R).
(* :156 lx_afn_pre_at_x *)
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
  (* fr_lib_pre_cf_x's first clause (a projection: tauto would touch the Section's hypotheses) *)
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by exact (proj1 HPRE).
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
  pose proof (aview_above_of_journal_xR (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
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
(* :238 xr_jkeep_img_x *)
Lemma xr_jkeep_img_xR : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_xR segs B PST ARx R Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  fp_spares FP a -> ~ inG Gc a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He (HPST a Hi) Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false.
  rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
(* :249 xr_jkeep_high_x *)
Lemma xr_jkeep_high_xR : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok segs B Gc -> ajournal_gx_xR segs B PST ARx R Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low Gc a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* :261 xr_jkeep_blk_x *)
Lemma xr_jkeep_blk_xR : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok segs B Gc -> ajournal_gx_xR segs B PST ARx R Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs Gc _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (alx_blocks _ _ ARx LAWS ly' S' [] W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  (* a live block's bytes lie off the image: alx_client_img's block clause (the kit's blk_off_imgP_x states off_img at
     image A's top 0x5fb000, below image B's 0x5fc000, so it does not decide this here) *)
  destruct (alx_client_img _ _ ARx LAWS ly' S' [] W' mem' md' (p + i) HAR0) as [_ Hn]; [|exact (Hn Hi')].
  left. exists p, n. split; [exact H2 | lia].
Qed.
(* :278 xr_jkeep_frame_x *)
Lemma xr_jkeep_frame_xR : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok segs B Gc -> ajournal_gx_xR segs B PST ARx R Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k cid pos a HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
    Hin Hr Hf Ha Hni.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Hr Hf).
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia.
  intros HGa. exact (Hni (proj1 (HGx a HGa))).
Qed.
(* :343 xr_kb_of_j_x *)
Lemma xr_kb_of_j_xR : forall Gc BLx STK F hi FF fpos ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 kk restB,
  gx_ok segs B Gc ->
  ajournal_gx_xR segs B PST ARx R Gc 0 [] STK F (ablocks_fp BLx) ly1 S1 [] W1 m1 md1 [] ly2 S2 [] W2 m2 md2 kk ->
  ARx ly1 S1 [] W1 m1 md1 ->
  Permutation (ablocks B ly1 S1) (BLx ++ restB) -> Permutation (ablocks B ly2 S2) restB ->
  apres_kept B W1 m1 W2 m2 ->
  0 <= STK -> alloc_ceiling <= F - STK -> F <= hi <= 2 ^ 64 ->
  In (1, fpos) (frames S1) -> FF = frame_addr ly1 1 fpos ->
  xr_kb Gc BLx FF F hi ly1 S1 W1 m1 ly2 S2 W2 m2.
Proof.
  intros Gc BLx STK F hi FF fpos ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 kk restB HGc HJ HAR1 HP1 HP2 HPRES HSTK HFlo HFhi
    Hfr HFF.
  pose proof (ajournal_gx_AR_xR segs B PST ARx Gc 0 [] STK F (ablocks_fp BLx) ly1 S1 [] W1 m1 md1 [] ly2 S2 [] W2 m2 md2 kk HJ)
    as HAR2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HBL1 : forall b, In b BLx -> In b (ablocks B ly1 S1))
    by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HP1 | apply in_or_app; left; exact Hb]).
  assert (HFP : forall a, inFP (ablocks_fp BLx) a -> exists b, In b BLx /\ fst b <= a < fst b + req_size (snd b)).
  { intros a (r & Hr & Ha). unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hb).
    exists b. split; [exact Hb|]. cbn [fst snd] in Ha. exact Ha. }
  split; [|split; [|split]].
  - intros a Hg Hn. pose proof (XR_HGM a Hg) as HgF. destruct (HG a HgF) as (Hi & Ho & _).
    pose proof (XR_ERRNO a Hg) as He.
    apply xr_abyte_img.
    + apply (xr_jkeep_img_xR Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk HJ a Hi Ho He); [|exact Hn].
      apply xr_fp_spares. intros [p n] Hb.
      destruct (alx_blocks _ _ ARx LAWS ly1 S1 [] W1 m1 md1 p n HAR1 (HBL1 _ Hb)) as (_ & H4 & _). exact H4.
    + intros Hp. exact (HPRES a Hi Ho He Hp).
  - intros b Hb Hnb.
    assert (Hb2 : In b (ablocks B ly2 S2)).
    { eapply Permutation_in; [apply Permutation_sym; exact HP2|].
      pose proof (Permutation_in _ HP1 Hb) as H. apply in_app_or in H as [H|H]; [contradiction | exact H]. }
    split; [exact Hb2|]. intros a Ha. destruct b as [p n]. cbn [fst snd] in Ha.
    split.
    + replace a with (p + (a - p)) by lia.
      apply (xr_jkeep_blk_xR Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk p n (a - p) HGc HJ Hb Hb2);
        [lia|].
      replace (p + (a - p)) with a by lia. intros HF. destruct (HFP a HF) as (b' & Hb' & Ha').
      assert (Hne : (p, n) <> b') by (intros <-; exact (Hnb Hb')).
      destruct (xr_blk_apart_x ly1 S1 W1 m1 md1 (p, n) b' HAR1 Hb (HBL1 b' Hb') Hne) as [H|H]; cbn [fst snd] in H; lia.
    + intros _. unfold arm. apply xr_pres_wr. exact (xr_blk_present_x ly2 S2 W2 m2 md2 p n a HAR2 Hb2 Ha).
  - intros a Ha. apply xr_abyte_off; [lia | intros Hi; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia |].
    apply (xr_jkeep_high_xR Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk HGc HJ a); lia.
  - destruct (frames_bounds_x segs B ARx LAWS ly1 S1 [] W1 m1 md1 1 fpos HAR1 Hfr) as (HF0 & HF1 & HFapp).
    replace (fs_frame_bytes 1) with 128 in HF1, HFapp by reflexivity. rewrite <- HFF in HF0, HF1, HFapp.
    pose proof (Z.div_mod FF 8 ltac:(lia)) as HD8. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as HM8.
    intros a Ha.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold SB in Ha; lia).
    assert (Hni : ~ in_img segs a).
    { intros Hi. destruct Ha as [Ha | Ha].
      - destruct (alx_client_img _ _ ARx LAWS ly1 S1 [] W1 m1 md1 a HAR1) as [_ Hn]; [|exact (Hn Hi)].
        right; left. exists 1, fpos. split; [exact Hfr|]. rewrite <- HFF. replace (fs_frame_bytes 1) with 128 by reflexivity.
        lia.
      - pose proof (pa_segs_low a Hi). unfold SB, kLowMemEnd in *. lia. }
    apply xr_abyte_off; [exact Ha64 | exact Hni |].
    apply (xr_jkeep_frame_xR Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk 1 fpos a HGc HJ Hfr);
      [| | exact Ha64 | exact Hni].
    + destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite <- HFF.
      * replace (fs_frame_bytes 1) with 128 by reflexivity. lia.
      * replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr, SHADOW_OFF. unfold SB in Ha. lia.
    + intros HF. destruct (HFP a HF) as (b' & Hb' & Ha'). destruct Ha as [Ha | Ha].
      * destruct (xr_blk_frame_apart_x ly1 S1 W1 m1 md1 b' 1 fpos HAR1 (HBL1 b' Hb') Hfr) as [H|H];
          rewrite <- HFF in H; replace (fs_frame_bytes 1) with 128 in H by reflexivity; lia.
      * destruct b' as [p' n']. cbn [fst snd] in Ha'.
        destruct (alx_blocks _ _ ARx LAWS ly1 S1 [] W1 m1 md1 p' n' HAR1 (HBL1 _ Hb')) as (_ & _ & _ & Happ & _).
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia.
Qed.
(* :530 xr_fa_kept_x *)
Lemma xr_fa_kept_xR : forall G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k W0 m0 md0,
  ajournal_gx_xR segs B PST ARx R G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 own ly2 S2 [] W2 m2 md2 k ->
  ARx ly1 S1 [] W0 m0 md0 -> forall cid pos, frame_addr ly2 cid pos = frame_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k W0 m0 md0 (_ & _ & (memS & HJi & _) & _) HAR.
  pose proof HJi as (_ & Hly & _).
  exact (proj1 (proj2 (alx_layout _ _ ARx LAWS ly1 S1 [] W0 m0 md0 ly2 HAR Hly))).
Qed.
(* :567 xr_inv_x *)
Definition xr_inv_xR (cx : lfcx) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate) (i : nat)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S k ev,
    c = cfg_at segs (BASE + (if (i <? 4)%nat then AX_reset_loop else AX_ffexit)) regs mem md /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md k /\
    frame_addr ly 1 fpos = frame_addr ly3 1 fpos /\
    bx_frame cx (frame_addr ly3 1 fpos) W mem /\
    sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    getr regs 2 = w64 (lf_F cx) /\ getr regs 9 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\
    getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
    getr regs 19 = w64 (xr_HA i) /\ getr regs 18 = w64 (xr_HA 4) /\
    getr regs 20 = w64 (frame_addr ly3 1 fpos) /\
    getr regs 24 = w64 (SB + frame_addr ly3 1 fpos / 8) /\
    amodel_at B ly S W mem (xr_mid m i ev) /\
    (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly S) (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest)) /\
    ainput_at B cx ly S W mem /\
    rom_view segs W mem /\
    mo_le MT S3 S (xr_cost (firstn i (lm_hs m))) /\
    mo_ok MT S (xr_cost (skipn i (lm_hs m))) /\
    NP S /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly S).
(* :590 xr_iter_x *)
Lemma xr_iter_xR : forall cx m fpos ly3 S3 i (W : world segs) c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> (i < 4)%nat -> length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
     (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  xr_inv_xR cx m fpos ly3 S3 i W c ->
  SRrG segs R W c (xr_inv_xR cx m fpos ly3 S3 (S i)).
Proof.
  intros cx m fpos ly3 S3 i W c HB Hi Hlen (rest0 & HPz0) HSEP2
    (regs & mem & md & ly & S & k & ev & -> & HJ & HFA & HFR & HFL & R2 & R9 & R8 & R3 & R4 & R19 & R18 & R20 & R24 &
     HMOD & HPRM & HIN & HROM & HMLE & HMOK & HNPr & HCNr).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (xr_F_bounds_x cx HB) as (HFlo & HFsp & Hsp47 & HF32 & HF46 & HFsp2).
  set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  set (hs := lm_hs m) in *.
  replace (if (i <? 4)%nat then AX_reset_loop else AX_ffexit) with AX_reset_loop
    by (destruct (Nat.ltb_spec i 4); [reflexivity | lia]).
  destruct (xr_entry0 AX_reset_loop W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs xr_extra0)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs xr_extra0) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E19 : ew E 19 = getr regs 19)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
  clear HE.
  unfold cfg_at. change (w64 (BASE + AX_reset_loop)) with (Z_to_bv 64 (BASE + AX_reset_loop)).
  paj_run_to_tok_x RUNTOG HS HJ SHOK XRspan AF_fr_source_reset.
  { apply awr_ok_x_nil. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Emeq end.
  pmkst HS.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs xr_extra0 xr_kept0 HS HAE ltac:(vm_compute; reflexivity))
    as KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  cbn [ms_regs restrict] in KR.
  rewrite Emeq in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  (* the input's length: fr_lib_pre_cf_x's sixth clause (a positional destruct: tauto would touch every arrow-typed
     Section variable and make the lemma take them) *)
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (destruct HB as (_ & (_ & _ & _ & _ & _ & HN & _)); exact HN).
  assert (Hsp1 : spZ (ms_regs ms) = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(unfold xr_kept0; xr_in)), R2; apply unsigned_lit_small; unfold LLVMF_STK in *;
        lia).
  assert (HFR' : bx_frame cx (frame_addr ly 1 fpos) W mem) by (rewrite HFA; exact HFR).
  destruct (lx_afn_pre_at_xR cx ly S fpos k W mem mdc (ms_regs ms) SR_STK HB HJ HFR' Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(unfold xr_kept0; xr_in)). exact R3. }
  { rewrite (KR 4%bv ltac:(unfold xr_kept0; xr_in)). exact R4. }
  { rewrite (KR 8%bv ltac:(unfold xr_kept0; xr_in)). exact R8. }
  { unfold SR_STK, LF_STK, ASTACK. lia. }
  { unfold SR_STK, LF_STK, ASTACK, LLVMF_STK. lia. }
  (* source_reset's premises: the slot, its zero shadow, the meter *)
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof (proj1 HJi) as HAR.
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hin1 : In (1, fpos) (frames S)) by (rewrite Hfrs; left; reflexivity).
  pose proof HMOD as (_ & Hsl & _).
  set (o := nth i hs None) in *.
  assert (Hslot : match o with Some h => asrc_at B ly S W mem (xr_HA i) h | None => asrc_closed W mem (xr_HA i) end).
  { pose proof (Hsl i Hi) as Hs. cbn [lm_hs xr_mid] in Hs. fold hs in Hs.
    rewrite xr_nth_hs in Hs by lia. destruct (Nat.ltb_spec i i); [lia|]. exact Hs. }
  assert (Hazs : azs B (xr_HA i) ASRC) by (apply (xr_azs_sub _ _ _ _ AZS_s); unfold xr_HA, ASRC; lia).
  (* B's sr_spec takes the slot's alignment: g_s = 0x5d8e60 = 8 * 766412, ASRC = 96 *)
  assert (HHA8 : xr_HA i mod 8 = 0).
  { unfold xr_HA, ASRC, fr_RG. cbn [fr_globals_b rg_s]. apply (proj2 (Z.mod_divide _ 8 ltac:(lia))).
    exists (766412 + 12 * Z.of_nat i). lia. }
  assert (HMOKs : mo_ok MT S (sr_cost MT o)).
  { apply (mo_ok_le MT MLM S _ (xr_cost (skipn i hs))); [exact HMOK|].
    rewrite (xr_cost_skip i hs Hi Hlen). pose proof (xr_cost_nonneg (skipn (Datatypes.S i) hs)). fold o. lia. }
  eapply (SRrG_bind segs R R_trans).
  { exact (SR_R [(xr_HA i, ASRC)] (xr_gxp_x i Hi) W ly S [] (ms_regs ms) mem mdc ch (xr_HA i) o HPREc
      ltac:(rewrite Q10, E19; exact R19) HHA8 Hslot
      ltac:(intros a Ha; apply (proj2 (inG_cons _ _ _)); left; unfold in_zr; cbn [fst snd]; exact Ha) Hazs HROM HMOKs
      0%nat (proj2 (RP_NP S _) HNPr) HCNr). }
  intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & -> & HJc & HP2 & Hcl & HBP & HPRES & HFRM & HFRS2 & HMLE2m
    & HRM').
  pose proof (conj HFRS2 HMLE2m) as HMLE2.
  (* sr_post_x's ghost list is [] (HP0 at the post's journal) *)
  assert (Ehp : Hp2 = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJc). subst Hp2.
  rewrite Hsp1 in HJc.
  (* the slot's blocks: live, in the model, not empty *)
  assert (HoS : forall b, In b (sr_blks o) -> In b (slot_blks o))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym (xr_sr_slot o)) Hb)).
  assert (HoL : forall b, In b (slot_blks o) -> In b (ablocks B ly S) /\ 0 < snd b).
  { intros b Hb. destruct o as [h|]; [|destruct Hb]. cbn [slot_blks] in Hb.
    exact (conj (xr_asrc_live _ _ _ _ _ _ Hslot b Hb) (xr_asrc_pos _ _ _ _ _ _ Hslot b Hb)). }
  assert (HoM : forall b, In b (slot_blks o) -> In b (model_blks m)).
  { intros b Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left.
    pose proof (xr_slot_in 0 hs i b ltac:(lia) Hlen Hi ltac:(lia) Hb) as H. exact H. }
  (* source_reset's journal inside this function's *)
  assert (HGsub : forall a, inG [(xr_HA i, ASRC)] a -> inG G_fr a)
    by (intros a Ha; apply XR_HGM; apply xr_gs_GM; exact (xr_slot_gs i a Hi Ha)).
  pose proof (ajournal_gx_G_mono_xR segs B PST ARx _ G_fr 0 [] SR_STK F _ ly S [] W mem mdc [] ly2 S2 [] W2 mem2 md2 kk
    HGsub HJc) as HJc'.
  assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc k
     SR_STK F 0 [] _ [] ly2 S2 [] W2 mem2 md2 kk HJ HJc'
     ltac:(unfold SR_STK, LF_STK, ASTACK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG) as HJ2.
  assert (HJ2' : ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx)
      (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 [] W2 mem2 md2 (k + kk)).
  { apply HJ2. intros a (r & Hr & Ha). unfold blk_FP in Hr. apply in_map_iff in Hr as (b & <- & Hb). cbn [fst snd] in Ha.
    destruct (HoL b (HoS b Hb)) as [HbL Hb0].
    destruct (in_dec DEC b (ablocks B (c_ly cx) (c_S cx))) as [Hent | Hnew].
    - destruct (HSEP2 b (HoM b (HoS b Hb))) as [Hn | Hcov]; [contradiction|].
      left. split; [apply Hcov; lia|]. exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact HbL | exact Ha].
    - right. exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact HbL|]. split; [exact Hnew | exact Ha]. }
  clear HJ2. cbn [app] in HJ2'.
  clear HS SHOK HF HFr HG0.
  (* what the call kept *)
  set (restB := input_blks cx ++ model_blks (xr_mid m (Datatypes.S i) ev) ++ rest0).
  assert (HPa : Permutation (ablocks B ly S) (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest0))
    by exact (HPRM rest0 HPz0).
  assert (HPb : Permutation (ablocks B ly S) (sr_blks o ++ restB)).
  { eapply Permutation_trans; [exact HPa|]. eapply Permutation_trans; [exact (xr_mb_perm cx m i ev ev rest0 Hi Hlen)|].
    apply Permutation_app_tail. exact (xr_sr_slot o). }
  assert (HK : xr_kb [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem ly2 S2 W2 mem2).
  { apply (xr_kb_of_j_xR [(xr_HA i, ASRC)] (sr_blks o) SR_STK F sp0 FF fpos ly S W mem mdc ly2 S2 W2 mem2 md2 kk restB
      (gx_ok_sub segs B _ G_fr HGsub HG) HJc HAR HPb (HBP restB HPb) HPRES);
      [unfold SR_STK, LF_STK, ASTACK; lia | unfold SR_STK, LF_STK, ASTACK, LLVMF_STK in *; lia | lia | exact Hin1
      | symmetry; exact HFA]. }
  pose proof (ajournal_gx_AR_xR segs B PST ARx _ 0 [] SR_STK F _ ly S [] W mem mdc [] ly2 S2 [] W2 mem2 md2 kk HJc) as HAR2.
  destruct (ERR ly2 S2 [] W2 mem2 md2 HAR2) as ((ev2 & Hev & Hevr) & Hevw).
  assert (HMOD2 : amodel_at B ly2 S2 W2 mem2 (xr_mid m (Datatypes.S i) ev2)).
  { apply (xr_model_step_x cx m i ev ev2 [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem mdc ly2 S2 W2 mem2 rest0
      Hi Hlen HAR HMOD HPa); [| exact HoS | exact HK | exact Hcl | exact Hev | exact Hevw | exact Hevr].
    intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; exact Ha|].
    exfalso. exact (inG_nil a Ha). }
  assert (HPRM2 : forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly2 S2) (input_blks cx ++ model_blks (xr_mid m (Datatypes.S i) ev2) ++ rest)).
  { intros rest Hr. apply HBP. eapply Permutation_trans; [exact (HPRM rest Hr)|].
    eapply Permutation_trans; [exact (xr_mb_perm cx m i ev ev2 rest Hi Hlen)|].
    apply Permutation_app_tail. exact (xr_sr_slot o). }
  assert (HND : List.NoDup (sr_blks o ++ restB)) by exact (Permutation_NoDup HPb (xr_nodup_x ly S W mem mdc HAR)).
  assert (HIN2 : ainput_at B cx ly2 S2 W2 mem2).
  { apply (xr_ainput_kept cx [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem ly2 S2 W2 mem2 HIN (eq_sym HlenP));
      [|exact HK].
    intros b Hb Hx. exact (xr_nodup_app _ _ b HND Hx ltac:(unfold restB; apply in_or_app; left; exact Hb)). }
  assert (HFR2 : bx_frame cx FF W2 mem2)
    by exact (xr_bxframe_kept cx FF [(xr_HA i, ASRC)] (sr_blks o) ly S W mem ly2 S2 W2 mem2 HFR HK HFsp).
  assert (HFL2 : sv8 W2 mem2 (FF + 120) (flag_addr ly3 1 fpos)).
  { pose proof HK as (_ & _ & _ & KF). apply (xr_sv8_kept W W2 mem mem2); [|exact HFL].
    intros x Hx. apply KF. left. lia. }
  assert (HROM2 : rom_view segs W2 mem2).
  { eapply ajournal_gx_rom_view_xR;
      first [exact HJc | exact (xr_rom_out_sub _ HGsub) | exact HROM | exact LAWS | exact pa_segs_low | exact PST_ROM]. }
  assert (HFA2 : frame_addr ly2 1 fpos = FF).
  { rewrite (xr_fa_kept_xR _ _ _ _ _ _ ly S W mem mdc _ ly2 S2 W2 mem2 md2 kk W mem mdc HJc HAR). exact HFA. }
  assert (HMLE3 : mo_le MT S3 S2 (xr_cost (firstn (Datatypes.S i) hs))).
  { rewrite (xr_cost_first i hs Hi Hlen). exact (mo_le_trans MT MLM _ _ _ _ _ HMLE (proj2 HMLE2)). }
  assert (HMOK3 : mo_ok MT S2 (xr_cost (skipn (Datatypes.S i) hs))).
  { rewrite (xr_cost_skip i hs Hi Hlen) in HMOK. exact (mo_ok_step MT MLM _ _ _ _ HMOK (proj2 HMLE2)). }
  (* the room round: NP from source_reset's rp_RM; the count drops by its frees (HPb, HBP) *)
  assert (HNP2 : NP S2) by exact (proj1 (RP_NP S2 0%nat) HRM').
  assert (HCN2 : cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly2 S2)).
  { apply (cnt_ok_pk_mono RP (fun _ => 0%nat) (fun _ => 0%nat) (ablocks B ly S) (ablocks B ly2 S2)); [|exact HCNr].
    intros P. rewrite (ReplyCnt.acnt_perm P _ _ (HBP restB HPb)), (ReplyCnt.acnt_perm P _ _ HPb).
    rewrite (ReplyCnt.acnt_app P (sr_blks o) restB).
    cbv beta. lia. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xr_kept0 -> getr regs2 r = getr regs r)
    by (intros r H1 H2; rewrite (xr_pres (ms_regs ms) regs2 r HP2 H1); exact (KR r H2)).
  (* back at 0x8500c (AX_reset_loop + 8 = 0x2cc8 = 11464 from BASE): addi s3,s3,96; bne s3,s2 *)
  rewrite Q1. change (Z_to_bv 64 (BASE + 11464)) with (Z_to_bv 64 (BASE + (AX_reset_loop + 8))).
  destruct (xr_entry0 (AX_reset_loop + 8) W2 regs2 mem2) as [HSb SHOKb].
  remember (Eimg (Ereg regs2 xr_extra0)) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs2 xr_extra0) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb19 : ew Eb 19 = w64 (xr_HA i)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl).
    rewrite (RR 19%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)). exact R19. }
  assert (Eb18 : ew Eb 18 = w64 (xr_HA 4)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl).
    rewrite (RR 18%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)). exact R18. }
  clear HEb.
  paj_run_tok_x RUNG HSb HJ2' SHOKb XRspan.
  { apply awr_ok_x_nil. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em2 end.
  clear HF HFr.
  assert (FIN : forall rf mdf, (forall r, In r xr_kept19 -> getr rf r = getr regs2 r) ->
      getr rf 19 = w64 (xr_HA (Datatypes.S i)) ->
      ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 [] W2 mem2 mdf (k + kk) ->
      forall c, c = cfg_at segs (BASE + (if (Datatypes.S i <? 4)%nat then AX_reset_loop else AX_ffexit)) rf mem2 mdf ->
      xr_inv_xR cx m fpos ly3 S3 (Datatypes.S i) W2 c).
  { intros rf mdf KX R19' HJf c ->. exists rf, mem2, mdf, ly2, S2, (k + kk), ev2.
    split; [reflexivity|]. split; [exact HJf|]. split; [exact HFA2|]. split; [exact HFR2|]. split; [exact HFL2|].
    assert (KY : forall r : bv 5, In r xr_kept19 -> acallee_saved (bv_unsigned r) -> In r xr_kept0 ->
        getr rf r = getr regs r) by (intros r H1 H2 H3; rewrite (KX r H1); exact (RR r H2 H3)).
    split; [rewrite (KY 2%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R2|].
    split; [rewrite (KY 9%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R9|].
    split; [rewrite (KY 8%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R8|].
    split; [rewrite (KY 3%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R3|].
    split; [rewrite (KY 4%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R4|].
    split; [exact R19'|].
    split; [rewrite (KY 18%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R18|].
    split; [rewrite (KY 20%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R20|].
    split; [rewrite (KY 24%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R24|].
    split; [exact HMOD2|]. split; [exact HPRM2|]. split; [exact HIN2|]. split; [exact HROM2|].
    split; [exact HMLE3|]. split; [exact HMOK3|]. split; [exact HNP2 | exact HCN2]. }
  assert (HU19 : U Eb (SOff 19 96) = xr_HA i + 96)
    by (apply (U_atom_off Eb 19 (xr_HA i) 96 Eb19); unfold xr_HA; xr_num; lia).
  assert (HU18 : U Eb (SOff 18 0) = xr_HA 4) by (apply (U_atom Eb 18 (xr_HA 4) Eb18); unfold xr_HA; xr_num; lia).
  psrr_branch_tok RUNG BRR HSb SHOKb XRspan.
  - assert (Hi3 : (i < 3)%nat).
    { rewrite branch_ne_U, HU19, HU18 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. unfold xr_HA, ASRC in Hc.
      lia. }
    paj_run_to_tok_x RUNTOG HSb HJ2' SHOKb XRspan AX_reset_loop.
    { apply awr_ok_x_nil. }
    lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
      pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em3 end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 xr_extra0 xr_kept19 HSb HAEb
      ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    prreg HSb (19%bv : bv 5) Q19.
    pmkst HSb.
    rewrite Em3 in *. rewrite Em2 in *.
    apply (SRrG_ret segs R R_refl).
    lazymatch goal with |- xr_inv_xR _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      apply (FIN r d KR2) end.
    + rewrite Q19, Eb19. unfold w64. rewrite unsigned_lit_small by (unfold xr_HA; xr_num; lia). f_equal.
      unfold xr_HA, ASRC. lia.
    + exact HJ2'.
    + rewrite (proj2 (Nat.ltb_lt (Datatypes.S i) 4) ltac:(lia)). reflexivity.
  - assert (Hi3 : i = 3%nat).
    { rewrite branch_ne_U, HU19, HU18 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold xr_HA, ASRC in Hc. lia. }
    paj_run_to_tok_x RUNTOG HSb HJ2' SHOKb XRspan AX_ffexit.
    { apply awr_ok_x_nil. }
    lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
      pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em3 end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 xr_extra0 xr_kept19 HSb HAEb
      ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    prreg HSb (19%bv : bv 5) Q19.
    pmkst HSb.
    rewrite Em3 in *. rewrite Em2 in *.
    apply (SRrG_ret segs R R_refl).
    lazymatch goal with |- xr_inv_xR _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      apply (FIN r d KR2) end.
    + rewrite Q19, Eb19. unfold w64. rewrite unsigned_lit_small by (unfold xr_HA; xr_num; lia). f_equal.
      unfold xr_HA, ASRC. lia.
    + exact HJ2'.
    + subst i. reflexivity.
Qed.
(* :840 xr_loop_x *)
Lemma xr_loop_xR : forall cx m fpos ly3 S3,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
     (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  forall n i (W : world segs) c, (i + n = 4)%nat -> xr_inv_xR cx m fpos ly3 S3 i W c ->
  SRrG segs R W c (xr_inv_xR cx m fpos ly3 S3 4).
Proof.
  intros cx m fpos ly3 S3 HB Hlen Hrest HSEP2 n. induction n as [|n IH]; intros i W c Hn Hinv.
  - replace i with 4%nat in Hinv by lia. apply (SRrG_ret segs R R_refl). exact Hinv.
  - eapply (SRrG_bind segs R R_trans); [exact (xr_iter_xR cx m fpos ly3 S3 i W c HB ltac:(lia) Hlen Hrest HSEP2 Hinv)|].
    intros W' c' _ Hinv'. exact (IH (Datatypes.S i) W' c' ltac:(lia) Hinv').
Qed.
(* :855 xr_post_x *)
Lemma xr_post_xR : forall cx m fpos ly3 S3 (W : world segs) c,
  length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
     (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  xr_inv_xR cx m fpos ly3 S3 4 W c -> lx_reset_post_xR B MT NP G_fr fr_FP PST ARx RP R cx m fpos ly3 S3 W c.
Proof.
  intros cx m fpos ly3 S3 W c Hlen (rest0 & HPz0) HSEP2
    (regs & mem & md & ly & S & k & ev & -> & HJ & HFA & HFR & HFL & R2 & R9 & R8 & R3 & R4 & R19 & R18 & R20 & R24 &
     HMOD & HPRM & HIN & HROM & HMLE & HMOK & HNPr & HCNr).
  rewrite (xr_mid4 m ev Hlen) in HMOD, HPRM.
  destruct (xr_cost_all (lm_hs m) Hlen) as [_ Hc4]. rewrite Hc4 in HMLE.
  exists ly, S, regs, mem, md, k, ev.
  split; [reflexivity|]. split; [exact HJ|].
  split; [exact R2|]. split; [exact R9|]. split; [exact R8|]. split; [exact R20|].
  split; [exact R24|]. split; [exact R3|]. split; [exact R4|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split.
  { split; [exists rest0; exact (HPRM rest0 HPz0)|].
    intros b Hb. apply HSEP2. unfold model_blks, lx_reset_model in *. cbn [lm_G lm_es lm_hs lm_cap lm_out] in Hb.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right.
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|].
    apply in_or_app; right. apply in_or_app; right. exact Hb. }
  split; [exact HIN|]. split; [exact HPRM|]. split; [exact HROM|]. split; [exact HFA|]. split; [exact HMLE|].
  split; [exact HNPr | exact HCNr].
Qed.
(* :933 lx_reset_x *)
Lemma lx_reset_xR : lx_reset_S_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx RP R.
Proof.
  unfold lx_reset_S_xR.
  intros cx m A fpos ly3 S3 W regs mem md k HB R2 R9 R8 R3 R4 HJ HFR HFL HMOD HSEP HIN HMOK Mat HA Mgnout HROM HNP3 HCN3.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (F := lf_F cx) in *.
  assert (HFb : 2 ^ 46 <= F /\ F + 320 <= 2 ^ 47 /\ F mod 32 = 0).
  { destruct HB as (_ & HPRE). pose proof (proj1 HPRE) as HAFN.
    pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
    pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
    unfold F, lf_F. set (sp0 := spZ (c_regs cx)) in *.
    pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
    split; [| split].
    - revert Hceil Hslo Hshi H47 Hmb C1 C2 C3 C4 C5. unfold LLVMF_STK. clear. intros. lia.
    - revert Hslo Hshi H47 Hmb. unfold LLVMF_STK. clear. intros. lia.
    - rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  destruct HFb as (HFlo & HFhi & HF32).
  destruct (xr_at_entry W regs mem F A HFlo HFhi HF32 R2 R9 Mat HA) as [HS SHOK].
  remember (Eimg (Ereg regs (xr_at_extra A))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 A) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HAE : env_agree 32 (Ereg regs (xr_at_extra A)) E)
    by (rewrite HE; split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Usp : bv_unsigned (ew E 2) = F) by (rewrite E2, R2; apply unsigned_lit_small; lia).
  clear HE.
  unfold cfg_at. change (w64 (BASE + AX_done)) with (Z_to_bv 64 (BASE + AX_done)).
  paj_run_to_tok_x RUNTOG HS HJ SHOK XRspan AF_fr_check_shape_done.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Emeq end.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  pmkst HS.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (xr_at_extra A) xr_kept0 HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  rewrite Emeq in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  destruct (xr_F_bounds_x cx HB) as (HFlo' & HFsp & Hsp47 & _ & _ & HFsp2).
  change (lf_F cx) with F in HFlo', HFsp, HFsp2.
  set (sp0 := spZ (c_regs cx)) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (Hlen : length (lm_hs m) = 4%nat) by (destruct HMOD as (Hl & _); exact Hl).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (destruct HB as (_ & (_ & _ & _ & _ & _ & HN & _)); exact HN).
  assert (Hsp1 : spZ (ms_regs ms) = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(unfold xr_kept0; xr_in)), R2; apply unsigned_lit_small; lia).
  destruct (lx_afn_pre_at_xR cx ly3 S3 fpos k W mem mdc (ms_regs ms) CSD_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(unfold xr_kept0; xr_in)). exact R3. }
  { rewrite (KR 4%bv ltac:(unfold xr_kept0; xr_in)). exact R4. }
  { rewrite (KR 8%bv ltac:(unfold xr_kept0; xr_in)). exact R8. }
  { unfold CSD_STK. lia. }
  { unfold CSD_STK, LLVMF_STK. lia. }
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof (proj1 HJi) as HAR.
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  (* check_shape_done(at) *)
  eapply (SRrG_bind segs R R_trans).
  { exact (CSD_R W ly3 S3 [] (ms_regs ms) mem mdc ch A HPREc ltac:(rewrite Q10, E32; reflexivity) HA Mgnout). }
  (* aleaf_post_x's last conjunct (errno's view kept) is not read here *)
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HA0 & HPRES2 & _).
  rewrite Hsp1 in HJc.
  clear HS SHOK HF HFr HG0.
  assert (HJc0 : ajournal_gx_xR segs B PST ARx R [] 0 [] CSD_STK F [] ly3 S3 [] W mem mdc [] ly3 S3 [] W2 mem2 md2 0)
    by (apply ajournal_gx_nil_xR; exact HJc).
  pose proof (ajournal_gx_G_mono_xR segs B PST ARx [] G_fr 0 [] CSD_STK F [] ly3 S3 [] W mem mdc [] ly3 S3 [] W2 mem2 md2 0
    (fun a Ha => False_ind _ (inG_nil a Ha)) HJc0) as HJc'.
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem mdc k
     CSD_STK F 0 [] [] [] ly3 S3 [] W2 mem2 md2 0 HJ HJc'
     ltac:(unfold CSD_STK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  assert (HK : xr_kb [] [] FF F sp0 ly3 S3 W mem ly3 S3 W2 mem2).
  { apply (xr_kb_of_j_xR [] [] CSD_STK F sp0 FF fpos ly3 S3 W mem mdc ly3 S3 W2 mem2 md2 0 (ablocks B ly3 S3)
      (gx_ok_nil segs B) HJc0 HAR (Permutation_refl _) (Permutation_refl _)
      (fun a _ _ _ Hp => HPRES2 a Hp));
      [unfold CSD_STK; lia | unfold CSD_STK, LLVMF_STK in *; lia | lia | exact Hin1 | reflexivity]. }
  pose proof (ajournal_gx_AR_xR segs B PST ARx [] 0 [] CSD_STK F [] ly3 S3 [] W mem mdc [] ly3 S3 [] W2 mem2 md2 0 HJc0) as HAR2.
  destruct (ERR ly3 S3 [] W2 mem2 md2 HAR2) as ((ev0 & Hev & Hevr) & Hevw).
  assert (HMOD1 : amodel_at B ly3 S3 W2 mem2 (xr_mid m 0 ev0))
    by exact (xr_model_keep_x m 0 (ct_ev (lm_c m)) ev0 FF F sp0 ly3 S3 W mem mdc ly3 S3 W2 mem2 ltac:(lia) Hlen HAR
                (xr_mid0 _ _ _ _ _ HMOD) HK Hev Hevw Hevr).
  assert (HIN1 : ainput_at B cx ly3 S3 W2 mem2)
    by exact (xr_ainput_kept cx [] [] FF F sp0 ly3 S3 W mem ly3 S3 W2 mem2 HIN (eq_sym HlenP) (fun b _ H => H) HK).
  assert (HFR1 : bx_frame cx FF W2 mem2)
    by exact (xr_bxframe_kept cx FF [] [] ly3 S3 W mem ly3 S3 W2 mem2 HFR HK HFsp).
  assert (HFL1 : sv8 W2 mem2 (FF + 120) (flag_addr ly3 1 fpos)).
  { pose proof HK as (_ & _ & _ & KF). apply (xr_sv8_kept W W2 mem mem2); [|exact HFL].
    intros x Hx. apply KF. left. lia. }
  assert (HROM1 : rom_view segs W2 mem2).
  { eapply ajournal_gx_rom_view_xR;
      first [exact HJc0 | exact (xr_rom_out_sub [] (fun a Ha => False_ind _ (inG_nil a Ha))) | exact HROM | exact LAWS
            | exact pa_segs_low | exact PST_ROM]. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xr_kept0 -> getr regs2 r = getr regs r)
    by (intros r H1 H2; rewrite (xr_pres (ms_regs ms) regs2 r HP2 H1); exact (KR r H2)).
  (* 0x84ff0: the loop's set-up (g_s, g_s + 384, the fake frame's two slots) *)
  pose proof HFR1 as (_ & _ & _ & _ & _ & _ & _ & _ & M80 & M96 & _).
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem mdc 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  replace (fs_frame_bytes 1) with 128 in HFF1 by reflexivity. fold FF in HFF0, HFF1.
  pose proof (Z.div_mod FF 8 ltac:(lia)) as HD8. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as HM8.
  (* the return from check_shape_done: AX_resets = 0x2cac = 11436 from BASE (0x84ff0) *)
  rewrite Q1. change (Z_to_bv 64 (BASE + 11436)) with (Z_to_bv 64 (BASE + AX_resets)).
  assert (R2' : getr regs2 2 = w64 F) by (rewrite (RR 2%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R2).
  assert (R9' : getr regs2 9 = w64 F) by (rewrite (RR 9%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R9).
  destruct (xr_set_entry W2 regs2 mem2 F FF HFlo HFhi HF32 R2' R9' M80 M96 ltac:(lia) ltac:(unfold SB; lia))
    as [HSb SHOKb].
  remember (Eimg (Ereg regs2 (xr_set_extra FF))) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs2 (xr_set_extra FF)) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb32 : ew Eb 32 = Z_to_bv 64 FF)
    by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (Eb33 : ew Eb 33 = Z_to_bv 64 (SB + FF / 8))
    by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  clear HEb.
  paj_run_to_tok_x RUNTOG HSb HJ2 SHOKb XRspan AX_reset_loop.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em2 end.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (xr_set_extra FF) xr_kept_set HSb HAEb
    ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  prreg HSb (18%bv : bv 5) Q18. prreg HSb (19%bv : bv 5) Q19. prreg HSb (20%bv : bv 5) Q20.
  prreg HSb (24%bv : bv 5) Q24.
  pmkst HSb.
  rewrite Em2 in *.
  (* the loop head of the first trip; g_s is image atom 260 = A_OBJ 19 (lib/B/W_bx_defs.v AX_g_s, 0x5d8e60) *)
  assert (U260 : bv_unsigned (ew Eb 260) = rg_s fr_RG).
  { rewrite (HEIb 260%nat ltac:(split; [apply Nat.leb_le | apply Nat.ltb_lt]; vm_compute; reflexivity)).
    vm_compute. reflexivity. }
  assert (KS : forall r : bv 5, In r xr_kept_set -> acallee_saved (bv_unsigned r) -> In r xr_kept0 ->
      getr (ms_regs ms0) r = getr regs r) by (intros r H1 H2 H3; rewrite (KR2 r H1); exact (RR r H2 H3)).
  destruct HSEP as [(rest0 & HPz0) HSEP2].
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
    assert (Hinv0 : xr_inv_xR cx m fpos ly3 S3 0 W2 (cfg_at segs (BASE + AX_reset_loop) r mem2 d)) end.
  { do 3 eexists. exists ly3, S3, k, ev0.
    split; [reflexivity|]. split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR1|]. split; [exact HFL1|].
    split; [rewrite (KR2 2%bv ltac:(unfold xr_kept_set; xr_in)); exact R2'|].
    split; [rewrite (KR2 9%bv ltac:(unfold xr_kept_set; xr_in)); exact R9'|].
    split; [rewrite (KS 8%bv ltac:(unfold xr_kept_set; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R8|].
    split; [rewrite (KS 3%bv ltac:(unfold xr_kept_set; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R3|].
    split; [rewrite (KS 4%bv ltac:(unfold xr_kept_set; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R4|].
    split.
    { rewrite Q19, <- (Z_to_bv_bv_unsigned _ (ew Eb 260)), U260. unfold w64, xr_HA. f_equal. all: lia. }
    split.
    { rewrite Q18, U260. unfold w64, xr_HA, ASRC. f_equal. all: lia. }
    split; [rewrite Q20, Eb32; reflexivity|].
    split; [rewrite Q24, Eb33; reflexivity|].
    split; [exact HMOD1|]. split; [intros rest Hr; exact Hr|]. split; [exact HIN1|]. split; [exact HROM1|].
    split; [exact (mo_le_refl MT MLM S3)|].
    split; [destruct (xr_cost_all (lm_hs m) Hlen) as [Hc0 _]; rewrite Hc0; exact HMOK|].
    split; [exact HNP3 | exact HCN3]. }
  (* the four trips, and the block's post at 0x85014 *)
  eapply (SRrG_bind segs R R_trans); [exact (xr_loop_xR cx m fpos ly3 S3 HB Hlen (ex_intro _ rest0 HPz0) HSEP2 4 0 W2 _ eq_refl Hinv0)|].
  intros W' c' _ Hinv4. apply (SRrG_ret segs R R_refl). exact (xr_post_xR cx m fpos ly3 S3 W' c' Hlen (ex_intro _ rest0 HPz0) HSEP2 Hinv4).
Qed.
End wR.
Lemma xr_inv_x_wle : xr_inv_x = xr_inv_xR (@wle segs). Proof. reflexivity. Qed.
(* the strict texts below are the R section's at R := wle (route R's rule: one walk text): each R premise at wle is
   the strict hypothesis of the same name, and the three laws hold for wle *)
Ltac wle_inst := first [ eassumption | exact SR | exact CSD | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].
(* ------------------------------------------------------------------ W_bx_defs.v:586 lx_afn_pre_at, over ARx
   (A's lx_afn_pre_at_x, :246-342, without the spine, over bx_frame) *)
Lemma lx_afn_pre_at_x : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  bx_frame cx (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 [] W regs mem md ch.
Proof. eapply (lx_afn_pre_at_xR (@wle segs)); wle_inst. Qed.
(* ------------------------------------------------------------------ what a callee's journal keeps, byte by byte *)
Lemma xr_jkeep_img_x : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_x segs B PST ARx Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  fp_spares FP a -> ~ inG Gc a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. eapply (xr_jkeep_img_xR (@wle segs)); wle_inst. Qed.
Lemma xr_jkeep_high_x : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok segs B Gc -> ajournal_gx_x segs B PST ARx Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. eapply (xr_jkeep_high_xR (@wle segs)); wle_inst. Qed.
Lemma xr_jkeep_blk_x : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok segs B Gc -> ajournal_gx_x segs B PST ARx Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof. eapply (xr_jkeep_blk_xR (@wle segs)); wle_inst. Qed.
Lemma xr_jkeep_frame_x : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok segs B Gc -> ajournal_gx_x segs B PST ARx Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. eapply (xr_jkeep_frame_xR (@wle segs)); wle_inst. Qed.
(* a callee at sp = F with globals Gc that frees the blocks BLx keeps the bundle: its journal (the image, block, high
   and frame clauses), the blocks it leaves, and the image bytes it leaves present *)
Lemma xr_kb_of_j_x : forall Gc BLx STK F hi FF fpos ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 kk restB,
  gx_ok segs B Gc ->
  ajournal_gx_x segs B PST ARx Gc 0 [] STK F (ablocks_fp BLx) ly1 S1 [] W1 m1 md1 [] ly2 S2 [] W2 m2 md2 kk ->
  ARx ly1 S1 [] W1 m1 md1 ->
  Permutation (ablocks B ly1 S1) (BLx ++ restB) -> Permutation (ablocks B ly2 S2) restB ->
  apres_kept B W1 m1 W2 m2 ->
  0 <= STK -> alloc_ceiling <= F - STK -> F <= hi <= 2 ^ 64 ->
  In (1, fpos) (frames S1) -> FF = frame_addr ly1 1 fpos ->
  xr_kb Gc BLx FF F hi ly1 S1 W1 m1 ly2 S2 W2 m2.
Proof. eapply (xr_kb_of_j_xR (@wle segs)); wle_inst. Qed.
(* a callee's journal keeps the layout's frame addresses and, owning nothing, the frames *)
Lemma xr_fa_kept_x : forall G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k W0 m0 md0,
  ajournal_gx_x segs B PST ARx G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 own ly2 S2 [] W2 m2 md2 k ->
  ARx ly1 S1 [] W0 m0 md0 -> forall cid pos, frame_addr ly2 cid pos = frame_addr ly1 cid pos.
Proof. eapply (xr_fa_kept_xR (@wle segs)); wle_inst. Qed.
Lemma xr_iter_x : forall cx m fpos ly3 S3 i (W : world segs) c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> (i < 4)%nat -> length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
     (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  xr_inv_x cx m fpos ly3 S3 i W c ->
  SRr segs W c (xr_inv_x cx m fpos ly3 S3 (S i)).
Proof. eapply (xr_iter_xR (@wle segs)); wle_inst. Qed.
(* the four trips *)
Lemma xr_loop_x : forall cx m fpos ly3 S3,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
     (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  forall n i (W : world segs) c, (i + n = 4)%nat -> xr_inv_x cx m fpos ly3 S3 i W c ->
  SRr segs W c (xr_inv_x cx m fpos ly3 S3 4).
Proof. eapply (xr_loop_xR (@wle segs)); wle_inst. Qed.
(* the loop's exit is the block's post (lib/B/W_bx_defs_x.v lx_reset_post_x) *)
Lemma xr_post_x : forall cx m fpos ly3 S3 (W : world segs) c,
  length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
     (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  xr_inv_x cx m fpos ly3 S3 4 W c -> lx_reset_post_x B MT NP G_fr fr_FP PST ARx RP cx m fpos ly3 S3 W c.
Proof. eapply (xr_post_xR (@wle segs)); wle_inst. Qed.

(* ------------------------------------------------------------------ 0x84fe8 check_shape_done(at); 0x84ff0, back from it,
   the loop's set-up (`auipc a0,0x554; addi s3,a0,-400; addi s2,s3,384; ld s4,80(s1); ld s8,96(s1)`) reads the two
   frame slots F+80 (FF) and F+96 (shadow of FF); B has no `ld s7,88(s1)` *)
Lemma lx_reset_x : lx_reset_S_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx RP.
Proof. eapply (lx_reset_xR (@wle segs)); wle_inst.
Qed.
End lxx.
