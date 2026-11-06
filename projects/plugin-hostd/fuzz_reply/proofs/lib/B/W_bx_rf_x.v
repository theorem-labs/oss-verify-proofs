(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: block `rf` of image B's SEG_EXIT (fuzz_reply.asan-ubsan) over the GENERIC allocator relation
   ARx: proves lib/B/W_bx_defs_x.v's lx_rf_site_S_x, the two relay_finish call sites `sd zero,-1892(s10); jal
   relay_finish` at 0x84f00 (AX_join, back at 0x84f08) and 0x84fe0 (AX_noord, back at 0x84fe8), relay_finish at
   0x82344.  The ARx conversion of lib/B/W_bx_rf.v (lx_rf_site, Qed; that file is NOT edited), following image A's
   finished conversion of the same block, e60b29a425a
   lib/A/W_LLVMFuzzerTestOneInput_exit_x.v lines 1282-2129 (lx_rf_post_site_x ..
   lx_rf_site_x), with A's AR original b86949b953d lib/A/W_LLVMFuzzerTestOneInput_exit.v :1817-3015 as the diff that
   shows each step.
   - Cited from lib/B/W_bx_rf.v (their statements and Section arguments do not mention AR, the AR journal or an AR callee
     spec): the byte, footprint, block-list, register and model lemmas, through the abbreviations below where they take
     Section arguments.
   - Converted here with an _x suffix: every lemma whose statement names AR, al_blocks, the AR journal or AR's laws, over
     ARx with HP0's [] ghost list, AR_laws_x (alx_blocks / alx_sep / alx_img / alx_client_img), YCbqG / W_journal_x's
     generic journal and the kit's _x lemmas; relay_finish's contract is the kit's rf_spec_x at K0's CTX_AFREE.
   - From lib/B/W_bx_defs.v's Section kit (AR-stated there): lx_fla_kept and lx_afn_pre_at, converted the same way
     (A's lx_fla_kept_x / lx_afn_pre_at_sp_x text without the chain's spine, which B's rf_spec_x does not read).
   - Two lemmas state image B's top 0x5fc000 directly (xrf_blk_img_x, xrf_frm_off_img_x): the kit's blk_off_imgP_x /
     frm_off_imgP_x state the shared core's off_img (Reusable/YCbq.v, image A's top 0x5fb000), while the AR file read
     lib/B/YCbq.v's off_img (top 0x5fc000) and B's pa_img_range [0x10000, 0x5fc000).  Their proofs are the kit's, at
     W_img_x.fr_img_cover_x's B cover. *)
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
(* the AR file of this block, whose AR-free lemmas are cited *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps W_bx_rf.
(* B's K0 tables (5128b798413, by path): rf_spec_x's caller-context table is K0's free table *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCk0.
(* route R (Section wR at the end): SRrG (YA0nH), and relay_finish's contract at R (lib/B/W_contract_xR.v
   rf_spec_xR; W_contract_xR is Required without Import and cited qualified) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_xR.
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

(* ---- the hypotheses this block uses: (a) lib/B/W_LLVMFuzzerTestOneInput_exit_x.v's Section lxx, verbatim (LS_rf_room
   names W_bx_defs.lx_rf_room in full: the header's lx_rf_room abbreviation already carries MMAX) ---- *)
Hypothesis HG_SL : forall a, inG (G_SL B fr_RG) a -> inG G_fr a.
(* ---- the room round (image A's exit_x at 5a9b16eac9e): the allocator rules' room record RP, whose room invariant is
   the cut's NP (cand13's kit, W_journal_x.v Record roomp) ---- *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
(* relay_finish: the kit's rf_spec_x at its own G = RF_G ++ G_SL, over K0's free table (lib/B/YCk0.v CTX_AFREE
   at 5128b798413); the site discharges In [BASE + AF_fr_relay_finish + 200] = [0x8240c] *)
Hypothesis RFg : rf_spec_x B PST ARx MT RP MMAX (RF_G fr_RG AG_LISTEN ++ G_SL B fr_RG) fr_RG AG_THREAD_UP AG_LISTEN
  YCk0.CTX_AFREE (BASE + AF_fr_relay_finish).
Hypothesis XRF_ERRNO : rg_out fr_RG + 8 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.
Hypothesis XRF_ROM_OUT : rom_out segs B G_fr.
(* TX_LS_rf_room (image A's exit_x at 5a9b16eac9e): lregs_X's t bound after LSx *)
Hypothesis LS_rf_room : forall cx t m ly S,
  LSx cx t m ly S -> 0 <= t <= OPS_MAX ->
  W_bx_defs.lx_rf_room MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).
(* the image's bytes lie outside PST: the generic journal keeps only bytes outside PST.  At the instance's PST := []
   it holds trivially. *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* a live block's size: AR's al_blocks carries `0 <= n < MALLOC_MAX`, the generic alx_blocks carries neither *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  0 <= n.
(* ---- (b) the derived facts the spine proves, verbatim from lib/B/W_bx_rf.v (LS is the header's LSx; LS_rf_mok names
   W_bx_defs.lx_rf_cost in full: the header's lx_rf_cost abbreviation already carries MT) ---- *)
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HG_RFc : forall a, inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_client fr_RG, 4); (AG_LISTEN, 4)] a ->
  inG G_fr a.
Hypothesis XRF_Gcells : forall a,
  rg_gone fr_RG <= a < rg_gone fr_RG + 1 \/ rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 \/
  AG_NFD <= a < AG_NFD + 4 \/ AG_THREAD_UP <= a < AG_THREAD_UP + 1 -> inG G_fr a.
Hypothesis XRF_JTAB_ROM : forall a, fr_jtab <= a < fr_jtab + 36 -> in_rom segs a.
Hypothesis XRF_END5 : forall (W : world segs) (mem : word -> option byte),
  rom_view segs W mem -> garr8 segs (arm W mem) (VAL A_lit_end5) (bzs END5).
(* KF-COUNT F8 (A aacecd50fed's exit_keys_nonempty, the same proof): every relay entry's key texts are non-empty -
   amodel_at's arelay_at gives aentry_ok for each entry (W_rep.v), whose last conjunct puts every key text at 14 bytes
   or more *)
Lemma exit_keys_nonempty : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m).
Proof.
  intros ly S W mem m HM. pose proof HM as (_ & _ & HREL & _).
  destruct HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  rewrite Forall_forall in HF |- *. intros e He.
  pose proof (HF e He) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K15).
  unfold gse_keys. rewrite Forall_forall in K15 |- *. intros x Hx.
  apply in_map_iff in Hx as (k & <- & Hk). destruct (K15 k Hk) as (_ & _ & _ & L & _).
  intros E. rewrite E in L. cbn [length] in L. lia.
Qed.
(* KF-COUNT F8: the exit block's LS_exit_budget takes lregs_X's t bound and the non-empty key texts, so the derived
   budget does too *)
Hypothesis LS_rf_mok : forall cx t m ly S,
  LS cx t m ly S -> 0 <= t <= OPS_MAX ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  mo_ok MT S (W_bx_defs.lx_rf_cost MT (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)).

(* ---- lib/B/W_bx_rf.v's AR-free lemmas with Section arguments, cited ---- *)
Local Notation xrf_errno_lo := (W_bx_rf.xrf_errno_lo B XRF_ERRNO).
Local Notation xrf_asrc_blks_in := (W_bx_rf.xrf_asrc_blks_in B).
Local Notation xrf_arelay_blks_in := (W_bx_rf.xrf_arelay_blks_in B).
Local Notation xrf_cost_eq := (W_bx_rf.xrf_cost_eq MT).
Local Notation xrf_room_eq := (W_bx_rf.xrf_room_eq MMAX).
Local Notation xrf_G := (W_bx_rf.xrf_G B).
Local Notation xrf_inG_RF := (W_bx_rf.xrf_inG_RF B).
Local Notation xrf_G_sub := (W_bx_rf.xrf_G_sub B G_fr HG_SL HG_RFc).
Local Notation xrf_G_ok := (W_bx_rf.xrf_G_ok B G_fr HG HG_SL HG_RFc).
Local Notation xrf_L_pos := (W_bx_rf.xrf_L_pos B).
Local Notation xrf_asrc_fp_in := (W_bx_rf.xrf_asrc_fp_in B).
Local Notation xrf_Gnout := (W_bx_rf.xrf_Gnout B G_fr HG_SL).

(* the image cover at image B's top, from the laws' image field (lib/B/W_img_x.v:30) *)
Lemma IMGC : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Proof. exact (W_img_x.fr_img_cover_x B ARx LAWS). Qed.
(* the ROM bytes lie outside PST (ajournal_gx_rom_view_x's premise): ROM bytes are image bytes *)
Lemma PST_ROM : forall a, in_rom segs a -> ~ Exists (in_zr a) PST.
Proof. intros a (sg & H1 & _ & H3). apply HPST. exists sg. split; assumption. Qed.
(* the symbolic-run scaffolding (cut_x's) *)
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].

(* a live block is off image B (top 0x5fc000): lib/B/W_kit_x.v blk_off_imgP_x's proof at IMGC's B cover (its
   statement's off_img is the shared core's, with image A's top 0x5fb000) *)
Lemma xrf_blk_img_x : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  p + req_size n <= 0x10000 \/ 0x5fc000 <= p.
Proof.
  intros ly S Hp W mem md p n HAR Hin.
  destruct (IMGC ly S Hp W mem md HAR) as [C1 C2].
  pose proof (req_size_pos n (BLKN ly S Hp W mem md p n HAR Hin)) as [Q _].
  destruct (Z.le_gt_cases (p + req_size n) 0x10000) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases 0x5fc000 p) as [|H2]; [right; lia|]. exfalso.
  assert (Hc : ~ in_zr (Z.max p 0x10000) (ly_img ly)).
  { refine (proj1 (alx_client_img _ _ _ LAWS ly S Hp W mem md (Z.max p 0x10000) HAR _)).
    left. exists p, n. split; [exact Hin | lia]. }
  apply Hc. unfold in_zr. lia.
Qed.
(* a fake frame is off image B (top 0x5fc000): lib/B/W_frame_x.v frm_off_imgP_x's proof at IMGC's B cover *)
Lemma xrf_frm_off_img_x : forall ly S (W : world segs) mem md cid pos,
  ARx ly S [] W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos + fs_frame_bytes cid <= 0x10000 \/ 0x5fc000 <= frame_addr ly cid pos.
Proof.
  intros ly S W mem md cid pos HAR Hin.
  destruct (IMGC ly S [] W mem md HAR) as [_ C2].
  pose proof (proj2 (alx_img _ _ _ LAWS ly S [] W mem md HAR) cid pos Hin) as Hf.
  right. lia.
Qed.

(* ------------------------------------------------------------------ the g_nout store's kit *)
Section fo.
Variables lo hi : Z.
Hypothesis Hlo : 0x10008 <= lo.
Hypothesis Hhi : hi <= 0x5fc000.
(* a byte of a live block, or within 8 bytes after it *)
Lemma xrf_blk_off_x : forall ly S W mem md p n a, ARx ly S [] W mem md -> In (p, n) (ablocks B ly S) ->
  p <= a < p + req_size n + 8 -> xrf_offw lo hi a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha.
  destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _).
  pose proof (xrf_blk_img_x _ _ [] _ _ _ _ _ HAR Hin) as Himg.
  pose proof asan_consts as (C1 & _). split; lia.
Qed.
Lemma xrf_alist_fp_off_x : forall ly S W mem md LA l lines, ARx ly S [] W mem md ->
  alist_at B ly S W mem LA l lines -> xrf_rng_off lo hi (LA, LA + 16) ->
  forall r, In r (alist_fp LA l) -> xrf_rng_off lo hi r.
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA r Hr.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [exact HLA|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
    apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app, xrf_len_text in Ha.
    unfold hl_n in Hj, H5.
    apply (xrf_blk_off_x ly S W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin).
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hq]. unfold AREC in *. lia.
  - apply in_map_iff in Hr as (rr & <- & Hrr). rewrite Forall_forall in H9. destruct (H9 rr Hrr) as (Hb & _).
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (xrf_blk_off_x ly S W mem md (fst rr) (Z.of_nat (length (snd rr)) + 1) a HAR Hb).
    pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xrf_asrc_fp_off_x : forall ly S W mem md HA h, ARx ly S [] W mem md -> asrc_at B ly S W mem HA h ->
  xrf_rng_off lo hi (HA, HA + ASRC) -> forall r, In r (asrc_fp HA h) -> xrf_rng_off lo hi r.
Proof.
  intros ly S W mem md HA h HAR Hs HHA r Hr.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]]; [exact HHA | |].
  - intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, H19 in Ha.
    apply (xrf_blk_off_x ly S W mem md (hs_partial h) APARTIAL a HAR H18).
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + apply (xrf_alist_fp_off_x ly S W mem md (HA + 16) (hs_pending h) false HAR H10); [|exact Hr].
      apply (xrf_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (xrf_alist_fp_off_x ly S W mem md (HA + 64) (hs_expected h) true HAR H22); [|exact Hr].
      apply (xrf_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (xrf_alist_fp_off_x ly S W mem md (HA + 80) (hs_held h) true HAR H23); [|exact Hr].
      apply (xrf_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
Qed.
Lemma xrf_aentry_fp_off_x : forall ly S W mem md e, ARx ly S [] W mem md -> aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> xrf_rng_off lo hi r.
Proof.
  intros ly S W mem md e HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha.
    apply (xrf_blk_off_x ly S W mem md (re_buf e) (re_cap e) a HAR Hin).
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hq]. lia.
  - destruct Hr as [<- | Hr].
    + intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, xrf_len_kptrs in Ha.
      destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)]; [rewrite Hk in Ha; cbn in Ha; lia|].
      apply (xrf_blk_off_x ly S W mem md (re_hp e) (re_kh e) a HAR Hin).
      pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hq]. unfold re_nheld in Hk1. lia.
    + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & K2 & K3 & K4 & K5).
      intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
      apply (xrf_blk_off_x ly S W mem md (gestures_end_b_c.key_addr k) (Z.of_nat (length (gestures_end_b_c.key_text k)) + 1) a HAR K1).
      pose proof (req_size_pos (Z.of_nat (length (gestures_end_b_c.key_text k)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xrf_arelay_fp_off_x : forall RG ly S W mem md G es, ARx ly S [] W mem md -> arelay_at B RG ly S W mem G es ->
  xrf_rng_off lo hi (rg_src RG, rg_src RG + 8) -> xrf_rng_off lo hi (rg_nsrc RG, rg_nsrc RG + 4) ->
  xrf_rng_off lo hi (rg_capsrc RG, rg_capsrc RG + 4) ->
  forall r, In r (arelay_fp RG G es) -> xrf_rng_off lo hi r.
Proof.
  intros RG ly S W mem md G es HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) R1 R2 R3 r Hr.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; [exact R1 | exact R2 | exact R3 | |].
  - intros a Ha. cbn [fst snd] in Ha. apply (xrf_blk_off_x ly S W mem md G ATABLE a HAR H8).
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [_ Hq]. lia.
  - apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in H10. exact (xrf_aentry_fp_off_x ly S W mem md e HAR (H10 e He) r Hr).
Qed.
End fo.

Lemma xrf_aout_clear_x : forall ly S W mem md mem' c O mx no cap out,
  ARx ly S [] W mem md ->
  (forall a, xrf_offw 6131264 6131272 a -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 -> xrf_rng_off 6131264 6131272 (as_errno B, as_errno B + 4) ->
  aout_at B fr_RG ly S W mem c O mx no cap out -> aout_at B fr_RG ly S W mem' c [] mx 0 cap out.
Proof.
  intros ly S W mem md mem' c O mx no cap out HAR KB KW HN0 HER
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26).
  assert (KK : forall x, 0 <= x < 6131264 \/ 6131272 <= x < 2 ^ 64 -> abyte_kept W mem W mem' x)
    by (intros x Hx; apply KB; split; lia).
  unfold aout_at. cbn [rg_send_max rg_nout rg_capout rg_out rg_client rg_client_broken rg_send_dead rg_send_eintr fr_RG fr_globals_b]
    in *.
  pose proof HER as HER'. unfold xrf_rng_off, xrf_offw in HER'. cbn [fst snd] in HER'.
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H1]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H2]|].
  split; [exact HN0|].
  split; [intros i Hi; apply KW; exact (H4 i Hi)|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H5]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H7]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H9]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H11]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H13]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H15]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H16]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KB; apply HER'; cbn in Hx; lia | exact H17]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KB; apply HER'; lia | exact H18]|].
  do 6 (split; [assumption|]).
  split; [reflexivity|].
  destruct H26 as [(Hc & Ho & Hn) | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; lia|right].
  split; [exact Hc|]. split; [lia|]. split; [exact Hin|].
  exists (O ++ junk). split; [rewrite length_app, Nat2Z.inj_add; lia|].
  cbn [app]. apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx. apply KB.
  apply (xrf_blk_off_x 6131264 6131272 ltac:(lia) ltac:(lia) ly S W mem md out cap x HAR Hin).
  pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.

Lemma xrf_store_kept_x : forall cx ly3 S3 W mem md mem' fpos m,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ARx ly3 S3 [] W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> jt_rom W mem ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' (xrf_clear_O m) /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx ly3 S3 W mem md mem' fpos m HB HAR Hfp HKX HGR HN0 HFR HMOD HIN HRV HJT.
  change (rg_nout fr_RG) with 6131264 in HKX, HN0.
  pose proof (xrf_kept_off W mem mem' 6131264 (6131264 + 8) HKX HGR) as KB. change (6131264 + 8) with 6131272 in KB.
  pose proof (xrf_writable_kept W mem mem' HGR) as KW.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  unfold LLVMF_STK in *.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HF : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  destruct (frames_bounds_x _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (xrf_frm_off_img_x _ _ _ _ _ _ _ HAR Hfp) as HFFi.
  change (fs_frame_bytes 1) with 128 in HFF1, HFFi.
  assert (KX : forall a n, 0 <= a -> a + n <= 6131264 \/ 6131272 <= a -> a + n <= 2 ^ 64 ->
    forall x, a <= x < a + n -> abyte_kept W mem W mem' x)
    by (intros a n Ha Hn Hb x Hx; apply KB; split; lia).
  split; [|split; [|split; [|split]]].
  - (* the frame and the fake frame *)
    unfold aframe_at in *. cbv zeta in *.
    destruct HFR as (FS & FW & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F96 & F104 & F120 & F128 & F136 & F152 &
      F184 & FF0 & FF8 & FF16 & FFw & FFsh & FFshw).
    unfold sv8 in *.
    assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) ->
      val_mem segs (arm W mem) a 8 v -> val_mem segs (arm W mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem); [intros x Hx; apply (KX a 8); lia | exact Hv]).
    assert (KF : forall a v, frame_addr ly3 1 fpos <= a -> a + 8 <= frame_addr ly3 1 fpos + 128 ->
      val_mem segs (arm W mem) a 8 v -> val_mem segs (arm W mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem); [intros x Hx; apply (KX a 8); lia | exact Hv]).
    split.
    { intros o r Hor. assert (Ho : 8 <= o <= 104).
      { unfold saved_regs in Hor. cbn [In] in Hor.
        repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- _; lia |]). destruct Hor. }
      apply KV; [lia | lia | exact (FS o r Hor)]. }
    split; [apply (akept_awr W mem); [intros x Hx; apply (KX (lf_F cx) (spZ (c_regs cx) - lf_F cx)); lia | exact FW]|].
    split; [apply KV; [lia | lia | exact F32]|]. split; [apply KV; [lia | lia | exact F40]|].
    split; [apply KV; [lia | lia | exact F48]|]. split; [apply KV; [lia | lia | exact F56]|].
    split; [apply KV; [lia | lia | exact F64]|]. split; [apply KV; [lia | lia | exact F72]|].
    split; [apply KV; [lia | lia | exact F80]|]. split; [apply KV; [lia | lia | exact F96]|].
    split; [apply KV; [lia | lia | exact F104]|]. split; [apply KV; [lia | lia | exact F120]|].
    split; [apply KV; [lia | lia | exact F128]|]. split; [apply KV; [lia | lia | exact F136]|].
    split; [apply KV; [lia | lia | exact F152]|]. split; [apply KV; [lia | lia | exact F184]|].
    split; [apply KF; [lia | lia | exact FF0]|]. split; [apply KF; [lia | lia | exact FF8]|].
    split; [apply KF; [lia | lia | exact FF16]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply (KX (frame_addr ly3 1 fpos) 128); lia | exact FFw]|].
    assert (HSB : 0 <= SB + frame_addr ly3 1 fpos / 8 /\ SB + frame_addr ly3 1 fpos / 8 + 16 <= 2 ^ 64 /\
      6131272 <= SB + frame_addr ly3 1 fpos / 8).
    { unfold SB. pose proof (Z.div_pos (frame_addr ly3 1 fpos) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (frame_addr ly3 1 fpos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
    split.
    { apply (akept_garr8 W mem); [|exact FFsh]. intros x Hx. change (length fake_shadow) with 16%nat in Hx.
      apply (KX (SB + frame_addr ly3 1 fpos / 8) 16); lia. }
    apply (akept_awr W mem); [intros x Hx; apply (KX (SB + frame_addr ly3 1 fpos / 8) 16); lia | exact FFshw].
  - (* the model, with what the controller read in this operation forgotten *)
    destruct HMOD as (Hhs4 & Hslots & Hrel & Hout & Hgone & Hlock & Hwake & Hnfd & Hnfdw & Hnfdr & Htu & Hlst & Hlstw).
    unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd xrf_clear_O].
    split; [exact Hhs4|].
    split.
    { intros i Hi. specialize (Hslots i Hi). unfold aslot in *.
      assert (HHA : xrf_rng_off 6131264 6131272 (rg_s fr_RG + ASRC * Z.of_nat i, rg_s fr_RG + ASRC * Z.of_nat i + ASRC)).
      { intros x Hx. cbn [fst snd rg_s fr_RG fr_globals_b] in Hx. unfold ASRC in Hx. split; lia. }
      destruct (nth i (lm_hs m) None) as [h|].
      - apply (asrc_at_kept B ly3 S3 W mem ly3 S3 W mem' _ h Hslots).
        + apply (xrf_akept W mem mem' 6131264 6131272); [exact KB|].
          exact (xrf_asrc_fp_off_x 6131264 6131272 ltac:(lia) ltac:(lia) ly3 S3 W mem md _ h HAR Hslots HHA).
        + exact (xrf_asrc_blks_in ly3 S3 W mem _ h Hslots).
      - destruct Hslots as [Hz Hw]. split.
        + apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx. apply KB. apply HHA.
          cbn [fst snd]. unfold ASRC in *. lia.
        + apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply KB. apply HHA. cbn [fst snd]. lia. }
    split.
    { apply (arelay_at_kept B fr_RG ly3 S3 W mem ly3 S3 W mem' _ _ Hrel).
      + apply (xrf_akept W mem mem' 6131264 6131272); [exact KB|].
        apply (xrf_arelay_fp_off_x 6131264 6131272 ltac:(lia) ltac:(lia) fr_RG ly3 S3 W mem md _ _ HAR Hrel);
          intros x Hx; cbn [fst snd rg_src rg_nsrc rg_capsrc fr_RG fr_globals_b] in Hx; split; lia.
      + exact (xrf_arelay_blks_in fr_RG ly3 S3 W mem _ _ Hrel). }
    split.
    { eapply (xrf_aout_clear_x ly3 S3 W mem md mem' _ _ _ _ _ _ HAR KB KW HN0); [|exact Hout].
      intros x Hx. cbn [fst snd] in Hx. pose proof xrf_errno_lo as He0. pose proof (proj2 XRF_ERRNO) as He1.
      split; lia. }
    split.
    { apply (agone_at_kept fr_RG W mem W mem' _ Hgone). intros r Hr a Ha. destruct Hr as [<- | []].
      apply KB. cbn in Ha |- *. split; lia. }
    split.
    { apply (alock_at_kept fr_RG W mem W mem' _ Hlock). intros r Hr a Ha. destruct Hr as [<- | []].
      apply KB. cbn in Ha |- *. split; lia. }
    split.
    { apply (awake_at_kept fr_RG W mem W mem' Hwake). intros r Hr a Ha. destruct Hr as [<- | []].
      apply KB. cbn in Ha |- *. split; lia. }
    split; [apply (akept_vm W mem); [intros x Hx; apply KB; unfold AG_NFD in *; cbn in Hx; split; lia | exact Hnfd]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KB; unfold AG_NFD in *; split; lia | exact Hnfdw]|].
    split; [exact Hnfdr|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KB; unfold AG_THREAD_UP in *; cbn in Hx; split; lia | exact Htu]|].
    split; [destruct Hlst as [lst Hlst]; exists lst;
      apply (akept_vm W mem); [intros x Hx; apply KB; unfold AG_LISTEN in *; cbn in Hx; split; lia | exact Hlst]|].
    apply (akept_awr W mem); [intros x Hx; apply KB; unfold AG_LISTEN in *; split; lia | exact Hlstw].
  - (* the input block *)
    destruct HIN as [Hblk Hg]. split; [exact Hblk|]. apply (akept_garr8 W mem); [|exact Hg].
    intros x Hx. rewrite length_map, <- Hlen in Hx. apply KB.
    destruct Hblk as [(Hn0 & _) | (Hn & Hin)]; [lia|].
    apply (xrf_blk_off_x 6131264 6131272 ltac:(lia) ltac:(lia) ly3 S3 W mem md (c_p cx) (c_n cx) x HAR Hin).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia.
  - (* .rodata *)
    intros a Ha. pose proof (xrf_rom_low a Ha) as Hrl.
    destruct (Z_lt_le_dec a 6131264) as [Hlt | Hge].
    + rewrite (proj1 (KB a ltac:(split; lia))). apply HRV. exact Ha.
    + destruct (Z_lt_le_dec a 6131272) as [Hlt2 | Hge2].
      * exfalso. exact (xrf_not_rom 6131264 6131272 a xrf_nout_not_rom ltac:(lia) Ha).
      * rewrite (proj1 (KB a ltac:(split; lia))). apply HRV. exact Ha.
  - (* the jump table *)
    intros i Hi. apply (akept_vm W mem); [|exact (HJT i Hi)].
    intros x Hx. apply KB. unfold fr_jtab in Hx. cbn in Hx. split; lia.
Qed.
(* the fake frame's flag word across the same store: the fake frame is off the image, so off g_nout *)
Lemma xrf_store_flag_x : forall ly3 S3 W mem md mem' fpos,
  ARx ly3 S3 [] W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros ly3 S3 W mem md mem' fpos HAR Hfp HKX HGR HFL.
  change (rg_nout fr_RG) with 6131264 in HKX.
  pose proof (xrf_kept_off W mem mem' 6131264 (6131264 + 8) HKX HGR) as KB. change (6131264 + 8) with 6131272 in KB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds_x _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (xrf_frm_off_img_x _ _ _ _ _ _ _ HAR Hfp) as HFFi.
  change (fs_frame_bytes 1) with 128 in HFF1, HFFi.
  apply (lxk_sv8_kept W W mem mem'); [|exact HFL]. intros x Hx. apply KB. split; lia.
Qed.

(* ------------------------------------------------------------------ lib/B/W_bx_defs.v's Section kit, over ARx *)
(* a journal keeps the layout's frame base (layout_le), so the flag addresses (W_bx_defs.v lx_fla_kept) *)
Lemma lx_fla_kept_x : forall {G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k},
  ajournal_gx_x segs B PST ARx G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 own ly2 S2 [] W2 m2 md2 k ->
  forall cid pos, flag_addr ly2 cid pos = flag_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _) cid pos.
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold flag_addr. rewrite EF. reflexivity.
Qed.
(* The call site's entry fact (W_bx_defs.v lx_afn_pre_at): relay_finish's `afn_pre_x` at sp = F, built with
   `afn_pre_x_at` (Reusable/YCbqG.v) over the entry's frame-pointer chain with this frame pushed (`achain_push`): the
   prologue saved ra at sp0-8 and s0 at sp0-16, the first clause of bx_frame. *)
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

(* ------------------------------------------------------------------ the call's kit *)
(* What a callee's journal keeps (W_gestures_end.v gse_keep_img / gse_keep_high / gse_keep_blk / gse_fp_spares /
   gse_nodup), and its frames clause *)
Lemma xrf_keep_img_x : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  fp_spares FP a -> ~ inG G a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He (HPST a Hi) Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
Lemma xrf_keep_high_x : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok segs B G -> ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma xrf_keep_blk_x : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok segs B G -> ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (alx_blocks _ _ ARx LAWS ly' S' [] W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  (* B: lib/B/W_kit.v pa_img_range, [0x10000, 0x5fc000) *)
  pose proof (xrf_blk_img_x ly' S' [] W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. lia.
Qed.
Lemma xrf_keep_frm_x : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok segs B G -> ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  ARx ly S [] W mem md -> In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
    HAR Hin Ha Hf.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Ha Hf).
  destruct (frames_bounds_x segs B ARx LAWS ly S [] W mem md cid pos HAR Hin) as (Hf0 & Hf1 & _).
  pose proof (xrf_frm_off_img_x ly S W mem md cid pos HAR Hin) as Hoff.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)) as Hd0.
  pose proof (Z.div_le_upper_bound (frame_addr ly cid pos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)) as Hd1.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as Hd2.
  pose proof (Z.div_le_upper_bound (fs_frame_bytes cid) 8 (fs_frame_bytes cid) ltac:(lia) ltac:(lia)) as Hd3.
  unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Ha. cbn [fst snd] in Ha.
  assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  destruct (HGx _ HGa) as [Hi _]. pose proof (pa_img_range _ Hi) as HR. pose proof (pa_segs_low a Hi) as HL.
  unfold kLowMemEnd in HL. lia.
Qed.
Lemma xrf_nodup_x : forall ly S W mem md, ARx ly S [] W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR. destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S [] W mem md p n HAR Hin) as Hn.
    cbn [snd]. pose proof (req_size_pos n ltac:(lia)). lia. }
  induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. inversion Hpos as [|? ? Hb Hl]; subst.
  apply List.NoDup_cons; [|exact (IH Hp Hl)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.

(* ------------------------------------------------------------------ the two instructions, to relay_finish's entry *)
(* writes of the run: g_nout's 8 bytes only *)
Ltac xrf_wr E26 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr;
    first [ lia
          | rewrite ?ew_ewset_other in Hr by lia; rewrite E26, unsigned_lit_small in Hr by (unfold HI_G_NOUT; lia);
            cbn; unfold HI_G_NOUT in Hr; lia ] |]);
  destruct Hin.
Ltac xrf_awr E26 :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha;
       first [ lia
             | right; left; apply xrf_Gnout; rewrite ?ew_ewset_other in Ha by lia;
               rewrite E26, unsigned_lit_small in Ha by (unfold HI_G_NOUT; lia); cbn; unfold HI_G_NOUT in Ha; lia ] |] ].
Ltac xrf_run_body_x E26 HS HJ SHOK HAE :=
  paj_run_to_tok_x RUNTO HS HJ SHOK xrf_Bspan AF_fr_relay_finish;
  [ xrf_awr E26 |];
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ ?mem0) (mrestrict _ (ms_mem ?ms1)) |- _ =>
    let MEQ := fresh "MEQ" in
    assert (MEQ : forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
        mrestrict (w_H _) (ms_mem ms1) x = mrestrict (w_H _) mem0 x)
      by (apply (xrf_frame_nout _ _ _ _ HFx); xrf_wr E26) end;
  lazymatch goal with H : mem_grows (mrestrict _ ?mem0) (mrestrict _ (ms_mem _)) |- _ =>
    let MG := fresh "MG" in rename H into MG end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  let KR := fresh "KR" in
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ xrf_kept HS HAE ltac:(vm_compute; reflexivity)) as KR;
  cbn [ms_regs restrict] in KR;
  let Q1 := fresh "Q1" in prreg HS (1%bv : bv 5) Q1;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) =>
    let r := eval vm_compute in (nth 0 (ss_mem ss) xrf_rnout) in
    let HRN := fresh "HRN" in let HN0 := fresh "HN0" in
    pose proof (st_ok_pi_region_nth Ev ss (restrict H ms) 0 r HS ltac:(vm_compute; reflexivity)) as HRN;
    cbn [ms_mem restrict] in HRN;
    pose proof (field_of_region Ev _ 26 HI_G_NOUT _ _ _ _ _ (-1892) 8 (SLit 0) 0 HRN
      ltac:(rewrite ?ew_ewset_other by lia; rewrite E26; apply unsigned_lit_small; unfold HI_G_NOUT; lia)
      ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as HN0;
    change (HI_G_NOUT + -1892) with (rg_nout fr_RG) in HN0; change (N.to_nat 8) with 8%nat in HN0; clear HRN
  end;
  pmkst HS;
  apply SRr_ret; split; [reflexivity|];
  lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
    exists r, mm, d end;
  split; [reflexivity|];
  split; [rewrite Q1; f_equal; unfold AX_join, AX_noord, AF_fr_LLVMFuzzerTestOneInput; lia|];
  split; [exact KR|];
  split; [rewrite ?wvb_collapse in HJ; exact HJ|];
  split; [assumption|]; split; [assumption | assumption].
Lemma xrf_to_rf_x : forall pcj (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k,
  pcj = AX_join \/ pcj = AX_noord ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own ly3 S3 [] W mem md k ->
  getr regs 26 = w64 HI_G_NOUT -> awr W mem (rg_nout fr_RG) 8 ->
  SRr segs W (cfg_at segs (fr_B0 + pcj) regs mem md) (fun W' c' => W' = W /\ exists regs1 mem1 md1,
    c' = cfg_at segs (BASE + AF_fr_relay_finish) regs1 mem1 md1 /\
    getr regs1 1 = Z_to_bv 64 (BASE + (pcj + 8)) /\
    (forall r, In r xrf_kept -> getr regs1 r = getr regs r) /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own ly3 S3 [] W mem1 md1 k /\
    (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
       mrestrict (w_H W) mem1 x = mrestrict (w_H W) mem x) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem1) /\
    val_mem segs (arm W mem1) (rg_nout fr_RG) 8 0).
Proof.
  intros pcj W regs mem md STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k Hpcj HJ R26 AWN.
  destruct (xrf_entry W regs mem pcj R26 AWN) as [HS SHOK].
  remember (Eimg (Ereg regs xrf_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs xrf_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E26 : ew E 26 = Z_to_bv 64 HI_G_NOUT)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. rewrite <- BASE_B0. change (w64 (BASE + pcj)) with (Z_to_bv 64 (BASE + pcj)).
  destruct Hpcj as [-> | ->]; unfold xrf_ss in HS; xrf_run_body_x E26 HS HJ SHOK HAE.
Qed.

(* a callee-saved register across the call *)
Ltac xrf_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

(* g_out's blocks count at most one of any class (image A's exit_x lx_acnt_aout) *)
Lemma lx_acnt_aout : forall P cap out, (ReplyCnt.acnt P (aout_blks cap out) <= 1)%nat.
Proof.
  intros P cap out. unfold aout_blks, ReplyCnt.acnt. destruct (cap =? 0); [cbn; lia|].
  cbn [map List.filter snd]. destruct (P cap); cbn; lia.
Qed.

(* ------------------------------------------------------------------ the site, both call sites in one lemma
   (lib/B/W_bx_defs_x.v lx_rf_site_S_x; relay_finish's spec RFg is applied once, below, for both sites) *)
Lemma lx_rf_site_x : lx_rf_site_S_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LSx RP.
Proof.
  unfold lx_rf_site_S_x.
  intros cx pcj t W regs mem md ly3 S3 fpos k m HB Hpcj HJ HFR HFL HMOD HIN HRV HJT HSEP HLS HR HAT HNP HCNT.
  pose proof HR as (R2 & R8 & R9 & R18 & R26 & R27 & R3 & R4 & Rk).
  pose proof HMOD as (_ & _ & _ & Hout & _).
  pose proof Hout as (O1 & O2 & O3 & O4 & _).
  pose proof xrf_errno_lo as HE0. pose proof (proj2 XRF_ERRNO) as HE1.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  (* the two instructions *)
  eapply SRr_bind; [exact (xrf_to_rf_x pcj W regs mem md _ _ _ _ _ _ _ _ _ _ _ _ Hpcj HJ R26 O4)|].
  intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & Q1 & KR & HJ1 & MEQ & MG & HN0).
  (* the cut facts across the store *)
  pose proof (ajournal_gx_AR_x _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ) as HAR.
  pose proof (ajournal_gx_AR_x _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ1) as HAR1.
  destruct (ajournal_gx_inner_x _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ) as (memS0 & HJi0 & _).
  pose proof HJi0 as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & Hfreed & _).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & Hgarr & Hfr0 & _).
  assert (Hfp : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (HFRS3 : frames S3 = [(1, fpos)]) by (rewrite Hfrs, Hfr0; reflexivity).
  destruct (xrf_store_kept_x cx ly3 S3 W mem md mem1 fpos m HB HAR Hfp MEQ MG HN0 HFR HMOD HIN HRV HJT)
    as (HFR1 & HMOD1 & HIN1 & HRV1 & HJT1).
  pose proof (xrf_store_flag_x ly3 S3 W mem md mem1 fpos HAR Hfp MEQ MG HFL) as HFL1.
  pose proof HMOD1 as (Hhs1 & Hslots1 & Hrel1 & Hout1 & Hgone1 & Hlock1 & Hwake1 & Hnfd1 & Hnfdw1 & Hnfdr1 & Htu1 &
    Hlst1 & Hlstw1).
  cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd xrf_clear_O] in Hhs1, Hslots1, Hrel1, Hout1,
    Hgone1, Hnfd1, Hnfdr1.
  (* the frame's numbers *)
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. set (x := spZ (c_regs cx) - 320).
    assert (Hq : x - x mod 32 = 32 * (x / 32)) by (pose proof (Z.div_mod x 32 ltac:(lia)); lia).
    rewrite Hq, Z.mul_comm. apply Z_mod_mult. }
  assert (Hsp1 : spZ regs1 = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  assert (Hpc8 : 0 <= pcj + 8 < 2 ^ 40 /\ (pcj + 8) mod 2 = 0)
    by (destruct Hpcj as [-> | ->]; (unfold AX_join, AX_noord, AF_fr_LLVMFuzzerTestOneInput; split; [lia | reflexivity])).
  assert (HSTKv : RF_STK = 16672) by reflexivity.
  (* relay_finish's afn_pre_x at sp = F *)
  destruct (lx_afn_pre_at_x cx ly3 S3 fpos k W mem1 md1 regs1 RF_STK HB HJ1 (bx_frame_of_aframe _ _ _ _ HFR1) Hsp1)
    as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; lia. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { lia. }
  { unfold LLVMF_STK. lia. }
  (* the blocks: relay_finish's three kinds first, then the rest Rr *)
  destruct HSEP as ((rest0 & HPz0) & HSEP2).
  pose proof Hrel1 as (Rr1 & Rr2 & Rr3 & Rr4 & Rr5 & Rr6 & Rr7 & Rr8 & Rr9 & Rr10 & Rr11).
  destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 Rr8) as (_ & HT4096 & _).
  assert (HTB : rf_tblk (lm_G m) = [(lm_G m, ATABLE)])
    by (unfold rf_tblk; destruct (Z.eqb_spec (lm_G m) 0); [lia | reflexivity]).
  set (Rr := input_blks cx ++ concat (map slot_blks (lm_hs m)) ++ rest0).
  set (L := rf_tblk (lm_G m) ++ rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m)).
  assert (HPRF : Permutation (ablocks B ly3 S3) (L ++ Rr)).
  { eapply Permutation_trans; [exact HPz0|]. unfold L, Rr. rewrite HTB. unfold model_blks, rf_eblks.
    rewrite <- !app_assoc. apply xrf_perm. }
  assert (HND3 : List.NoDup (L ++ Rr)) by exact (Permutation_NoDup HPRF (xrf_nodup_x _ _ _ _ _ HAR1)).
  assert (HL3 : forall b, In b L -> In b (ablocks B ly3 S3))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPRF)); apply in_or_app; left; exact Hb).
  assert (HR3 : forall b, In b Rr -> In b (ablocks B ly3 S3))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPRF)); apply in_or_app; right; exact Hb).
  assert (HLM : forall b, In b L -> In b (model_blks m)).
  { intros b Hb. unfold L in Hb. rewrite HTB in Hb. unfold model_blks, rf_eblks.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right. cbn [app] in Hb.
    apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left; exact Hb|]. right. apply in_or_app. right. exact Hb. }
  (* relay_finish *)
  eapply SRr_bind.
  { apply (RFg W ly3 S3 [] regs1 mem1 md1 ch (lm_G m) (lm_es m) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_out m) Rr HPREc)
      with (kr := 0%nat).
    - rewrite Hsp1. exact HF32.
    - rewrite HFRS3. reflexivity.
    - exact Htu1.
    - exact Hlock1.
    - right. exact Hrel1.
    - exact Hlst1.
    - exact Hlstw1.
    - exact Hout1.
    - unfold L in HPRF. rewrite <- !app_assoc in HPRF. exact HPRF.
    - exact (XRF_END5 W mem1 HRV1).
    - exact HRV1.
    - intros a Ha. apply inG_app. left. exact Ha.
    - intros a Ha. apply inG_app. right. exact Ha.
    - intros a Ha He. unfold RF_G in Ha.
      repeat (apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr, AG_LISTEN in Ha; cbn in Ha; lia |]).
      exact (inG_nil a Ha).
    - apply xrf_room_eq. exact (LS_rf_room cx t m ly3 S3 HLS (proj2 Rk)).
    - (* relay_finish's own free returns at entry + 200 = 0x8240c, the one-entry trace K0's free table holds
         (lib/B/YCk0.v CTX_AFREE row [0x8240c]; the edge (CTX_relay_finish, 0x8240c, CTX_AFREE, K0Lit)) *)
      assert (E200 : BASE + AF_fr_relay_finish + 200 = 0x8240c) by (vm_compute; reflexivity).
      rewrite E200. unfold YCk0.CTX_AFREE. cbn [In]. repeat first [left; reflexivity | right].
    - rewrite <- xrf_cost_eq.
      exact (LS_rf_mok cx t m ly3 S3 HLS (proj2 Rk) (exit_keys_nonempty ly3 S3 W mem m HMOD)).
    - apply RP_NP. exact HNP.
    - exact HCNT. }
  intros W2 c2 _ (ly' & S' & Hp' & regs' & mem' & md' & k' & out' & -> & HJc & HPR & HPK & HFRM & HMO & HRM' & HPERM &
    HOUT & HLOCK & HRA & HGL & HGLw).
  (* rf_post_x's ghost list is [] (HP0 at the post's journal) *)
  assert (Ehp : Hp' = []) by (eapply HP0; eapply ajournal_gx_AR_x; exact HJc). subst Hp'.
  rewrite Hsp1 in HJc.
  fold xrf_G in HJc.
  unfold rf_FP in HJc. fold L in HJc.
  rewrite HTB in HPERM.
  set (R := rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) in *.
  pose proof (ajournal_gx_AR_x _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as HAR2.
  assert (HR2 : forall b, In b Rr -> In b (ablocks B ly' S'))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; cbn [app]; apply in_or_app; right; exact Hb).
  assert (HND2 : List.NoDup ([(lm_G m, ATABLE)] ++ aout_blks (gse_cap R) out' ++ Rr))
    by exact (Permutation_NoDup HPERM (xrf_nodup_x _ _ _ _ _ HAR2)).
  (* what the call keeps *)
  assert (HL4096 : forall b, In b L -> 4096 <= fst b).
  { intros [p n] Hb. destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 (HL3 _ Hb)) as (_ & H4 & _). exact H4. }
  assert (KIMG : forall a, inG G_fr a -> ~ inG xrf_G a -> a < 0x5d90c8 -> abyte_kept W mem1 W2 mem' a).
  { intros a HGa HnR Hlt. destruct (HG a HGa) as (Hi & Ho & _). pose proof (pa_segs_low a Hi) as HL.
    apply xrf_abyte_kept.
    - unfold kLowMemEnd in HL. lia.
    - apply (xrf_keep_img_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Hi Ho); [lia | apply xrf_fp_spares; exact HL4096 | exact HnR].
    - intros Hro. exact (proj1 (XRF_ROM_OUT a Hro) HGa). }
  assert (KHIGH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem1 W2 mem' a).
  { intros a Ha. apply xrf_abyte_kept; [lia | |].
    - apply (xrf_keep_high_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xrf_G_ok HJc a); lia.
    - intros (sg & Hsg & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as HL.
      unfold kLowMemEnd in HL. lia. }
  assert (HnFP : forall p n i, In (p, n) Rr -> 0 <= i < req_size n -> ~ inFP (ablocks_fp L) (p + i)).
  { intros p n i Hb Hi Hf. destruct (xrf_inFP_blk L (p + i) Hf) as (p' & n' & Hb' & Ha').
    assert (Hne : (p', n') <> (p, n)) by (intros E; rewrite E in Hb'; exact (xrf_nodup_app L Rr (p, n) HND3 Hb' Hb)).
    pose proof (sep_blocks_x segs B ARx LAWS ly3 S3 [] W mem1 md1 p' n' p n HAR1 (HL3 _ Hb') (HR3 _ Hb) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KB : forall b, In b Rr -> forall a, fst b <= a < fst b + snd b -> abyte_kept W mem1 W2 mem' a).
  { intros [p n] Hb a Ha. cbn [fst snd] in Ha.
    destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 (HR3 _ Hb)) as (_ & Hp4 & Hpc & _).
    pose proof (BLKN _ _ [] _ _ _ _ _ HAR1 (HR3 _ Hb)) as Hn.
    pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
    pose proof (xrf_blk_img_x _ _ [] _ _ _ _ _ HAR1 (HR3 _ Hb)) as Hoff.
    replace a with (p + (a - p)) by lia.
    apply xrf_abyte_kept; [lia | |].
    - apply (xrf_keep_blk_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n (a - p) xrf_G_ok HJc (HR3 _ Hb) (HR2 _ Hb));
        [lia | apply (HnFP p n); [exact Hb | lia]].
    - intros (sg & Hsg & _ & Hr). pose proof (pa_img_range _ (ex_intro _ sg (conj Hsg Hr))) as HIR. lia. }
  assert (HFF := frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem1 md1 1 fpos HAR1 Hfp).
  destruct HFF as (HFF0 & HFF1 & HFFa).
  change (fs_frame_bytes 1) with 128 in HFF1, HFFa.
  assert (KFRM : forall a, (frame_addr ly3 1 fpos <= a < frame_addr ly3 1 fpos + 128 \/
      SB + frame_addr ly3 1 fpos / 8 <= a < SB + frame_addr ly3 1 fpos / 8 + 16) -> abyte_kept W mem1 W2 mem' a).
  { intros a Ha.
    pose proof (Z.div_pos (frame_addr ly3 1 fpos) 8 ltac:(lia) ltac:(lia)) as Hd0.
    pose proof (Z.div_le_upper_bound (frame_addr ly3 1 fpos) 8 0xfffffff0000 ltac:(lia) ltac:(lia)) as Hd1.
    assert (Hd2 : 512 <= frame_addr ly3 1 fpos / 8) by (apply Z.div_le_lower_bound; lia).
    pose proof (xrf_frm_off_img_x _ _ _ _ _ _ _ HAR1 Hfp) as Hoff. change (fs_frame_bytes 1) with 128 in Hoff.
    apply xrf_abyte_kept; [unfold SB in Ha; lia | |].
    - apply (xrf_keep_frm_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos a xrf_G_ok HJc HAR1 Hfp).
      + unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
        change (fs_frame_bytes 1) with 128. unfold SB in Ha.
        destruct Ha as [Ha | Ha]; [left | right]; lia.
      + intros Hf. destruct (xrf_inFP_blk L a Hf) as (p' & n' & Hb' & Ha').
        destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 (HL3 _ Hb')) as (_ & Hp4 & Hpc & Happ & _).
        pose proof (sep_block_frame_x segs B ARx LAWS ly3 S3 [] W mem1 md1 p' n' 1 fpos HAR1 (HL3 _ Hb') Hfp) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SB in Ha.
        destruct Ha as [Ha | Ha]; lia.
    - intros (sg & Hsg & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as HL.
      pose proof (pa_img_range _ (ex_intro _ sg (conj Hsg Hr))) as HIR.
      unfold kLowMemEnd in HL. unfold SB in Ha. destruct Ha as [Ha | Ha]; lia. }
  (* the journal from the entry *)
  assert (HJc' : ajournal_gx_x segs B PST ARx G_fr 0 [] RF_STK (lf_F cx) (ablocks_fp L) ly3 S3 [] W mem1 md1 [] ly' S' [] W2 mem' md' k')
    by exact (ajournal_gx_G_mono_x segs B PST ARx xrf_G G_fr 0 [] RF_STK (lf_F cx) (ablocks_fp L) ly3 S3 [] W mem1 md1 [] ly' S' [] W2 mem' md'
      k' xrf_G_sub HJc).
  assert (HJ2 : ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) ([] ++ [(1, fpos)]) ly' S' [] W2 mem' md' (k + k')).
  { apply (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem1 md1 k
      RF_STK (lf_F cx) 0 [] (ablocks_fp L) [] ly' S' [] W2 mem' md' k' HJ1 HJc');
      [unfold LLVMF_STK; lia | lia | lia | intros a Ha; exfalso; exact (inFP_nil a Ha) | exact HG |].
    intros a Hf. destruct (xrf_inFP_blk L a Hf) as (p & n & Hb & Ha).
    pose proof (xrf_L_pos _ _ _ _ _ _ _ _ _ _ _ _ (p, n) Hrel1 Hout1 Hb) as Hpos. cbn [snd] in Hpos.
    unfold req_size in Ha. destruct (Z.eqb_spec n 0) as [Hn0 | _]; [lia|].
    destruct (HSEP2 (p, n) (HLM _ Hb)) as [Hne | Hin].
    - right. exists p, n. split; [exact (HL3 _ Hb)|]. split; [exact Hne|]. unfold req_size.
      destruct (Z.eqb_spec n 0); [lia | exact Ha].
    - left. split; [apply Hin; cbn [fst snd]; unfold req_size; destruct (Z.eqb_spec n 0); [lia | exact Ha]|].
      exists p, n. split; [exact (HL3 _ Hb)|].
      unfold req_size. destruct (Z.eqb_spec n 0); [lia | exact Ha]. }
  cbn [app] in HJ2.
  (* the frame address *)
  assert (HFA : frame_addr ly' 1 fpos = frame_addr ly3 1 fpos).
  { destruct (ajournal_gx_inner_x _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as (memSc & HJic & _).
    pose proof HJic as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF.
    reflexivity. }
  (* the stream after: g_nout = |O| *)
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HOno & _).
  (* the post *)
  apply SRr_ret.
  exists ly', S', regs', mem', md', (k + k'),
    (LM (lm_k m) (lm_hs m) (lm_G m) [] (lx_rf_ctl (gse_c R)) (gse_O R) (lm_mx m) (gse_cap R) out' (lm_gn m) (lm_nfd m)).
  cbn [lm_k lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  assert (HPM : Permutation (ablocks B ly' S') (input_blks cx ++
      model_blks (LM (lm_k m) (lm_hs m) (lm_G m) [] (lx_rf_ctl (gse_c R)) (gse_O R) (lm_mx m) (gse_cap R) out'
        (lm_gn m) (lm_nfd m)) ++ rest0)).
  { eapply Permutation_trans; [exact HPERM|]. apply Permutation_sym. unfold model_blks. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    exact (xrf_perm (lm_G m, ATABLE) [] (concat (map slot_blks (lm_hs m))) (aout_blks (gse_cap R) out') (input_blks cx) rest0). }
  split.
  { (* the configuration *)
    unfold cfg_at, w64. rewrite Q1, BASE_B0, Z.add_assoc. reflexivity. }
  split; [exact HJ2|].
  split.
  { (* the frame and the fake frame *)
    rewrite HFA.
    unfold aframe_at in HFR1 |- *. cbv zeta in HFR1 |- *.
    destruct HFR1 as (FS & FW & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F96 & F104 & F120 & F128 & F136 & F152 &
      F184 & FF0 & FF8 & FF16 & FFw & FFsh & FFshw).
    unfold sv8 in *.
    assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) ->
      val_mem segs (arm W mem1) a 8 v -> val_mem segs (arm W2 mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem1); [intros x Hx; apply KHIGH; lia | exact Hv]).
    assert (KF : forall a v, frame_addr ly3 1 fpos <= a -> a + 8 <= frame_addr ly3 1 fpos + 128 ->
      val_mem segs (arm W mem1) a 8 v -> val_mem segs (arm W2 mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem1); [intros x Hx; apply KFRM; left; lia | exact Hv]).
    split.
    { intros o r Hor. assert (Ho : 8 <= o <= 104).
      { unfold saved_regs in Hor. cbn [In] in Hor.
        repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- _; lia |]). destruct Hor. }
      apply KV; [lia | lia | exact (FS o r Hor)]. }
    split; [apply (akept_awr W mem1); [intros x Hx; apply KHIGH; lia | exact FW]|].
    split; [apply KV; [lia | lia | exact F32]|]. split; [apply KV; [lia | lia | exact F40]|].
    split; [apply KV; [lia | lia | exact F48]|]. split; [apply KV; [lia | lia | exact F56]|].
    split; [apply KV; [lia | lia | exact F64]|]. split; [apply KV; [lia | lia | exact F72]|].
    split; [apply KV; [lia | lia | exact F80]|]. split; [apply KV; [lia | lia | exact F96]|].
    split; [apply KV; [lia | lia | exact F104]|]. split; [apply KV; [lia | lia | exact F120]|].
    split; [apply KV; [lia | lia | exact F128]|]. split; [apply KV; [lia | lia | exact F136]|].
    split; [apply KV; [lia | lia | exact F152]|]. split; [apply KV; [lia | lia | exact F184]|].
    split; [apply KF; [lia | lia | exact FF0]|]. split; [apply KF; [lia | lia | exact FF8]|].
    split; [apply KF; [lia | lia | exact FF16]|].
    split; [apply (akept_awr W mem1); [intros x Hx; apply KFRM; left; lia | exact FFw]|].
    split.
    { apply (akept_garr8 W mem1); [|exact FFsh]. intros x Hx. change (length fake_shadow) with 16%nat in Hx.
      apply KFRM. right. lia. }
    apply (akept_awr W mem1); [intros x Hx; apply KFRM; right; lia | exact FFshw]. }
  split.
  { (* the fake frame's flag word: kept by the store (above) and by the call (it lies in the fake frame) *)
    rewrite HFA, (lx_fla_kept_x HJc). apply (lxk_sv8_kept W W2 mem1 mem'); [|exact HFL1].
    intros x Hx. apply KFRM. left. lia. }
  split; [exact HFA|].
  split.
  { (* the model *)
    unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [exact Hhs1|].
    split.
    { intros i Hi. specialize (Hslots1 i Hi). unfold aslot in *.
      assert (HHA : forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
        abyte_kept W mem1 W2 mem' a).
      { intros a Ha. cbn [rg_s fr_RG fr_globals_b] in Ha. unfold ASRC in Ha. apply KIMG.
        - apply HGs. cbn [rg_s fr_RG fr_globals_b]. unfold ASRC. lia.
        - intros HR'. apply xrf_inG_RF in HR'. lia.
        - lia. }
      destruct (nth i (lm_hs m) None) as [h|] eqn:Eh.
      - apply (asrc_at_kept B ly3 S3 W mem1 ly' S' W2 mem' _ h Hslots1).
        + intros r Hr a Ha. refine (xrf_asrc_fp_in (abyte_kept W mem1 W2 mem') ly3 S3 W mem1 _ h Hslots1 HHA _ r Hr a Ha).
          intros b Hb x Hx. apply (KB b); [|exact Hx].
          unfold Rr. apply in_or_app. right. apply in_or_app. left.
          exact (xrf_slot_in (lm_hs m) i h ltac:(rewrite Hhs1; exact Hi) Eh b Hb).
        + intros b Hb. apply HR2. unfold Rr. apply in_or_app. right. apply in_or_app. left.
          exact (xrf_slot_in (lm_hs m) i h ltac:(rewrite Hhs1; exact Hi) Eh b Hb).
      - destruct Hslots1 as [Hz Hw]. split.
        + apply (akept_garr8 W mem1); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx. apply HHA.
          unfold ASRC in *. lia.
        + apply (akept_awr W mem1); [|exact Hw]. intros x Hx. apply HHA. lia. }
    split.
    { destruct HRA as [(HT0 & _) | HRA]; [lia | exact HRA]. }
    split.
    { rewrite <- HOno in HOUT. exact HOUT. }
    split.
    { apply (agone_at_kept fr_RG W mem1 W2 mem' _ Hgone1). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd rg_gone fr_RG fr_globals_b] in Ha. apply KIMG; [apply XRF_Gcells; left; cbn; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [exact HLOCK|].
    split.
    { apply (awake_at_kept fr_RG W mem1 W2 mem' Hwake1). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd rg_wake fr_RG fr_globals_b] in Ha. apply KIMG; [apply XRF_Gcells; right; left; cbn; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    assert (KN : forall a, AG_NFD <= a < AG_NFD + 4 -> abyte_kept W mem1 W2 mem' a).
    { intros a Ha. unfold AG_NFD in Ha. apply KIMG; [apply XRF_Gcells; right; right; left; unfold AG_NFD; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [apply (akept_vm W mem1); [intros x Hx; apply KN; cbn in Hx; lia | exact Hnfd1]|].
    split; [apply (akept_awr W mem1); [intros x Hx; apply KN; lia | exact Hnfdw1]|].
    split; [exact Hnfdr1|].
    split.
    { apply (akept_vm W mem1); [|exact Htu1]. intros x Hx. cbn in Hx. unfold AG_THREAD_UP in Hx.
      apply KIMG; [apply XRF_Gcells; right; right; right; unfold AG_THREAD_UP; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [exists (2 ^ 32 - 1); exact HGL | exact HGLw]. }
  split.
  { (* the input block *)
    destruct HIN1 as [Hblk Hg]. split.
    - destruct Hblk as [Hb0 | (Hn & Hin)]; [left; exact Hb0|]. right. split; [exact Hn|].
      apply HR2. unfold Rr, input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. left. reflexivity.
    - apply (akept_garr8 W mem1); [|exact Hg]. intros x Hx. rewrite length_map, <- Hlen in Hx.
      destruct Hblk as [(Hn0 & _) | (Hn & Hin)]; [lia|].
      apply (KB (c_p cx, c_n cx)); [|cbn [fst snd]; exact Hx].
      unfold Rr, input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. left. reflexivity. }
  assert (HROM2 : rom_view segs W2 mem').
  { eapply (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low); [exact HJc | | exact PST_ROM | exact HRV1].
    intros a Ha. destruct (XRF_ROM_OUT a Ha) as (H1 & H2 & H3 & H4). split; [|split; [exact H2 | split; assumption]].
    intros HGa. exact (H1 (xrf_G_sub a HGa)). }
  split; [exact HROM2|].
  split.
  { (* the jump table *)
    intros i Hi. apply (xrf_vm_aview W W2 mem1 mem'); [|exact (HJT1 i Hi)].
    intros x Hx. cbn in Hx. assert (Hro : in_rom segs x) by (apply XRF_JTAB_ROM; lia).
    rewrite (HROM2 x Hro), (HRV1 x Hro). reflexivity. }
  split.
  { (* the blocks *)
    split; [exists rest0; exact HPM|].
    intros b Hb. unfold model_blks in Hb. cbn [lm_G lm_es lm_hs lm_cap lm_out map concat app] in Hb.
    destruct Hb as [<- | Hb]; [apply HSEP2; left; reflexivity|].
    apply in_app_or in Hb as [Hb | Hb].
    { apply HSEP2. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    destruct (in_dec xrf_peq b (ablocks B (c_ly cx) (c_S cx))) as [Hbe | Hbe]; [|left; exact Hbe].
    destruct (in_dec xrf_peq b (ablocks B ly3 S3)) as [Hb3 | Hb3].
    - pose proof (Permutation_in _ HPRF Hb3) as HbLR. apply in_app_or in HbLR as [HbL | HbR].
      + apply HSEP2. exact (HLM _ HbL).
      + exfalso. cbn [app] in HND2. apply List.NoDup_cons_iff in HND2 as [_ Hn2].
        exact (xrf_nodup_app (aout_blks (gse_cap R) out') Rr b Hn2 Hb HbR).
    - right. destruct b as [p n]. intros a Ha. cbn [fst snd] in Ha.
      assert (Hb' : In (p, n) (ablocks B ly' S'))
        by (apply (Permutation_in _ (Permutation_sym HPERM)); right; cbn [app]; apply in_or_app; left; exact Hb).
      pose proof (BLKN _ _ [] _ _ _ _ _ HAR2 Hb') as Hn.
      pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
      replace a with (p + (a - p)) by lia. apply (Hfreed p n (a - p) Hbe Hb3). lia. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xrf_kept -> getr regs' r = getr regs r)
    by (intros r H1 H2; rewrite (xrf_pres regs1 regs' r HPR H1); exact (KR r H2)).
  split; [rewrite (RR 2%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R2|].
  split; [rewrite (RR 8%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (RR 9%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (RR 3%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (RR 4%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (RR 27%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R27|].
  split; [exact (RR 19%bv ltac:(xrf_cs) ltac:(cbv; tauto))|].
  (* the caller's frame: kept by the store (off g_nout) and by the call (above its frame) *)
  assert (KC : forall a, lf_F cx <= a < spZ (c_regs cx) -> aview segs (w_H W2) mem' a = aview segs (w_H W) mem a).
  { intros a Ha. rewrite (proj1 (KHIGH a ltac:(lia))). apply aview_eq_of. apply MEQ.
    rewrite unsigned_lit_small by lia. cbn [rg_nout fr_RG fr_globals_b]. lia. }
  split.
  { apply (xrf_vm_aview W W2 mem mem'); [|exact HAT]. intros x Hx. apply KC. unfold AX_AT in Hx. cbn in Hx. lia. }
  split; [exact KC|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [intros Hes; unfold R; rewrite Hes; reflexivity|].
  split; [rewrite xrf_run_eq; reflexivity|].
  split.
  { intros rest Hrest.
    assert (Hrr : Permutation rest rest0).
    { apply (Permutation_app_inv_l (input_blks cx ++ model_blks m)). rewrite <- !app_assoc.
      eapply Permutation_trans; [apply Permutation_sym; exact Hrest | exact HPz0]. }
    eapply Permutation_trans; [exact HPM|]. apply Permutation_app_head. apply Permutation_app_head.
    apply Permutation_sym. exact Hrr. }
  split; [rewrite HFRM; reflexivity|].
  split; [rewrite xrf_cost_eq; exact HMO|].
  split; [rewrite xrf_run_eq; reflexivity|].
  (* the room round: NP from relay_finish's rp_RM; the count after it is X's plus relay_finish's net growth, which
     its peak rf_pk covers (the entries' blocks are freed, the table kept, g_out replaced by one block) *)
  split; [exact (proj1 (RP_NP S' 0%nat) HRM')|].
  apply (cnt_ok_pk_mono RP rf_pk _ (ablocks B ly3 S3) _); [|exact HCNT].
  intros P. rewrite (ReplyCnt.acnt_perm P _ _ HPERM), (ReplyCnt.acnt_perm P _ _ HPRF). unfold L. rewrite HTB.
  rewrite (ReplyCnt.acnt_app P [(lm_G m, ATABLE)] (aout_blks (gse_cap R) out' ++ Rr)),
    (ReplyCnt.acnt_app P (aout_blks (gse_cap R) out') Rr),
    (ReplyCnt.acnt_app P ([(lm_G m, ATABLE)] ++ rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m)) Rr),
    (ReplyCnt.acnt_app P [(lm_G m, ATABLE)] (rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m))).
  pose proof (lx_acnt_aout P (gse_cap R) out'). unfold rf_pk. cbv beta. lia.
Qed.

(* ==================================================================================================================
   ROUTE R: the relay_finish site at a world relation R (image A's twin: lib/A/W_LLVMFuzzerTestOneInput_exit_x.v Section
   exitR, lx_rf_site_xR).  A free inside relay_finish re-hides the dead shadow, so at R := wle' segs RZ_cf the call step
   gives only `R W W'`.  lx_rf_site_xR below proves lib/B/W_bx_defs_x.v lx_rf_site_S_xR (R last).
   - relay_finish at R: RF_R is RFg (above) at relay_finish's R contract lib/B/W_contract_xR.v rf_spec_xR (R right after
     ARx); its post rf_post_xR is the strict one with the journal at R, so the strict proof reads it with the same
     destructs.
   - Every lemma below is a lemma above whose statement names the journal, with its name R appended ((* :N name *) cites
     the strict text): ajournal_gx_x segs B PST ARx -> ajournal_gx_xR segs B PST ARx R, the kit's journal lemmas -> their
     _xR twins (W_journal_x.v, YCbqG.v, W_frame_x.v), RUNTO -> RUNTOR (W_journal_x.v paj_run_to_x_xR).  The two
     instructions to relay_finish's entry (xrf_to_rf_xR) keep the world (W' = W): they stay SRr over the R journal and are
     lifted by SRr_SRrG (WLE_R).  The call is bound by SRrG_bind (R_trans), the post is returned by SRrG_ret (R_refl), and
     the two journals are joined by ajournal_gx_sub_xR (R_trans).
   - The journal-free lemmas above (xrf_store_kept_x, xrf_store_flag_x, xrf_nodup_x, lx_acnt_aout and the cited
     lib/B/W_bx_rf.v lemmas) are used as they are; the strict lemmas above keep their text and proofs. *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
(* relay_finish at R: RFg (above) at lib/B/W_contract_xR.v rf_spec_xR, R inserted right after ARx *)
Hypothesis RF_R : W_contract_xR.rf_spec_xR B PST ARx R MT RP MMAX (RF_G fr_RG AG_LISTEN ++ G_SL B fr_RG) fr_RG
  AG_THREAD_UP AG_LISTEN YCk0.CTX_AFREE (BASE + AF_fr_relay_finish).
(* the run to relay_finish's entry over the R journal (concludes SRr) *)
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].

(* :467 lx_fla_kept_x *)
Lemma lx_fla_kept_xR : forall {G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k},
  ajournal_gx_xR segs B PST ARx R G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 own ly2 S2 [] W2 m2 md2 k ->
  forall cid pos, flag_addr ly2 cid pos = flag_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _) cid pos.
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold flag_addr. rewrite EF. reflexivity.
Qed.
(* :478 lx_afn_pre_at_x; the text and proof of lib/B/W_bx_reset_x.v:403 lx_afn_pre_at_xR (Section wR there) *)
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
(* :561 xrf_keep_img_x *)
Lemma xrf_keep_img_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  fp_spares FP a -> ~ inG G a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He (HPST a Hi) Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
(* :571 xrf_keep_high_x *)
Lemma xrf_keep_high_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok segs B G -> ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* :582 xrf_keep_blk_x *)
Lemma xrf_keep_blk_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok segs B G -> ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (alx_blocks _ _ ARx LAWS ly' S' [] W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  (* B: lib/B/W_kit.v pa_img_range, [0x10000, 0x5fc000) *)
  pose proof (xrf_blk_img_x ly' S' [] W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. lia.
Qed.
(* :598 xrf_keep_frm_x *)
Lemma xrf_keep_frm_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok segs B G -> ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  ARx ly S [] W mem md -> In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
    HAR Hin Ha Hf.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Ha Hf).
  destruct (frames_bounds_x segs B ARx LAWS ly S [] W mem md cid pos HAR Hin) as (Hf0 & Hf1 & _).
  pose proof (xrf_frm_off_img_x ly S W mem md cid pos HAR Hin) as Hoff.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)) as Hd0.
  pose proof (Z.div_le_upper_bound (frame_addr ly cid pos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)) as Hd1.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as Hd2.
  pose proof (Z.div_le_upper_bound (fs_frame_bytes cid) 8 (fs_frame_bytes cid) ltac:(lia) ltac:(lia)) as Hd3.
  unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Ha. cbn [fst snd] in Ha.
  assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  destruct (HGx _ HGa) as [Hi _]. pose proof (pa_img_range _ Hi) as HR. pose proof (pa_segs_low a Hi) as HL.
  unfold kLowMemEnd in HL. lia.
Qed.
(* :654 xrf_run_body_x *)
Ltac xrf_run_body_xR E26 HS HJ SHOK HAE :=
  paj_run_to_tok_x RUNTOR HS HJ SHOK xrf_Bspan AF_fr_relay_finish;
  [ xrf_awr E26 |];
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ ?mem0) (mrestrict _ (ms_mem ?ms1)) |- _ =>
    let MEQ := fresh "MEQ" in
    assert (MEQ : forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
        mrestrict (w_H _) (ms_mem ms1) x = mrestrict (w_H _) mem0 x)
      by (apply (xrf_frame_nout _ _ _ _ HFx); xrf_wr E26) end;
  lazymatch goal with H : mem_grows (mrestrict _ ?mem0) (mrestrict _ (ms_mem _)) |- _ =>
    let MG := fresh "MG" in rename H into MG end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  let KR := fresh "KR" in
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ xrf_kept HS HAE ltac:(vm_compute; reflexivity)) as KR;
  cbn [ms_regs restrict] in KR;
  let Q1 := fresh "Q1" in prreg HS (1%bv : bv 5) Q1;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) =>
    let r := eval vm_compute in (nth 0 (ss_mem ss) xrf_rnout) in
    let HRN := fresh "HRN" in let HN0 := fresh "HN0" in
    pose proof (st_ok_pi_region_nth Ev ss (restrict H ms) 0 r HS ltac:(vm_compute; reflexivity)) as HRN;
    cbn [ms_mem restrict] in HRN;
    pose proof (field_of_region Ev _ 26 HI_G_NOUT _ _ _ _ _ (-1892) 8 (SLit 0) 0 HRN
      ltac:(rewrite ?ew_ewset_other by lia; rewrite E26; apply unsigned_lit_small; unfold HI_G_NOUT; lia)
      ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as HN0;
    change (HI_G_NOUT + -1892) with (rg_nout fr_RG) in HN0; change (N.to_nat 8) with 8%nat in HN0; clear HRN
  end;
  pmkst HS;
  apply SRr_ret; split; [reflexivity|];
  lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
    exists r, mm, d end;
  split; [reflexivity|];
  split; [rewrite Q1; f_equal; unfold AX_join, AX_noord, AF_fr_LLVMFuzzerTestOneInput; lia|];
  split; [exact KR|];
  split; [rewrite ?wvb_collapse in HJ; exact HJ|];
  split; [assumption|]; split; [assumption | assumption].
(* :688 xrf_to_rf_x *)
Lemma xrf_to_rf_xR : forall pcj (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k,
  pcj = AX_join \/ pcj = AX_noord ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own ly3 S3 [] W mem md k ->
  getr regs 26 = w64 HI_G_NOUT -> awr W mem (rg_nout fr_RG) 8 ->
  SRr segs W (cfg_at segs (fr_B0 + pcj) regs mem md) (fun W' c' => W' = W /\ exists regs1 mem1 md1,
    c' = cfg_at segs (BASE + AF_fr_relay_finish) regs1 mem1 md1 /\
    getr regs1 1 = Z_to_bv 64 (BASE + (pcj + 8)) /\
    (forall r, In r xrf_kept -> getr regs1 r = getr regs r) /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own ly3 S3 [] W mem1 md1 k /\
    (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
       mrestrict (w_H W) mem1 x = mrestrict (w_H W) mem x) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem1) /\
    val_mem segs (arm W mem1) (rg_nout fr_RG) 8 0).
Proof.
  intros pcj W regs mem md STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k Hpcj HJ R26 AWN.
  destruct (xrf_entry W regs mem pcj R26 AWN) as [HS SHOK].
  remember (Eimg (Ereg regs xrf_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs xrf_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E26 : ew E 26 = Z_to_bv 64 HI_G_NOUT)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. rewrite <- BASE_B0. change (w64 (BASE + pcj)) with (Z_to_bv 64 (BASE + pcj)).
  destruct Hpcj as [-> | ->]; unfold xrf_ss in HS; xrf_run_body_xR E26 HS HJ SHOK HAE.
Qed.
(* :730 lx_rf_site_x *)
Lemma lx_rf_site_xR : lx_rf_site_S_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LSx RP R.
Proof.
  unfold lx_rf_site_S_xR.
  intros cx pcj t W regs mem md ly3 S3 fpos k m HB Hpcj HJ HFR HFL HMOD HIN HRV HJT HSEP HLS HR HAT HNP HCNT.
  pose proof HR as (R2 & R8 & R9 & R18 & R26 & R27 & R3 & R4 & Rk).
  pose proof HMOD as (_ & _ & _ & Hout & _).
  pose proof Hout as (O1 & O2 & O3 & O4 & _).
  pose proof xrf_errno_lo as HE0. pose proof (proj2 XRF_ERRNO) as HE1.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  (* the two instructions *)
  eapply (SRrG_bind segs R R_trans); [apply (SRr_SRrG segs R WLE_R); exact (xrf_to_rf_xR pcj W regs mem md _ _ _ _ _ _ _ _ _ _ _ _ Hpcj HJ R26 O4)|].
  intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & Q1 & KR & HJ1 & MEQ & MG & HN0).
  (* the cut facts across the store *)
  pose proof (ajournal_gx_AR_xR _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ) as HAR.
  pose proof (ajournal_gx_AR_xR _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ1) as HAR1.
  destruct (ajournal_gx_inner_xR _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ) as (memS0 & HJi0 & _).
  pose proof HJi0 as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & Hfreed & _).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & Hgarr & Hfr0 & _).
  assert (Hfp : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (HFRS3 : frames S3 = [(1, fpos)]) by (rewrite Hfrs, Hfr0; reflexivity).
  destruct (xrf_store_kept_x cx ly3 S3 W mem md mem1 fpos m HB HAR Hfp MEQ MG HN0 HFR HMOD HIN HRV HJT)
    as (HFR1 & HMOD1 & HIN1 & HRV1 & HJT1).
  pose proof (xrf_store_flag_x ly3 S3 W mem md mem1 fpos HAR Hfp MEQ MG HFL) as HFL1.
  pose proof HMOD1 as (Hhs1 & Hslots1 & Hrel1 & Hout1 & Hgone1 & Hlock1 & Hwake1 & Hnfd1 & Hnfdw1 & Hnfdr1 & Htu1 &
    Hlst1 & Hlstw1).
  cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd xrf_clear_O] in Hhs1, Hslots1, Hrel1, Hout1,
    Hgone1, Hnfd1, Hnfdr1.
  (* the frame's numbers *)
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. set (x := spZ (c_regs cx) - 320).
    assert (Hq : x - x mod 32 = 32 * (x / 32)) by (pose proof (Z.div_mod x 32 ltac:(lia)); lia).
    rewrite Hq, Z.mul_comm. apply Z_mod_mult. }
  assert (Hsp1 : spZ regs1 = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  assert (Hpc8 : 0 <= pcj + 8 < 2 ^ 40 /\ (pcj + 8) mod 2 = 0)
    by (destruct Hpcj as [-> | ->]; (unfold AX_join, AX_noord, AF_fr_LLVMFuzzerTestOneInput; split; [lia | reflexivity])).
  assert (HSTKv : RF_STK = 16672) by reflexivity.
  (* relay_finish's afn_pre_x at sp = F *)
  destruct (lx_afn_pre_at_xR cx ly3 S3 fpos k W mem1 md1 regs1 RF_STK HB HJ1 (bx_frame_of_aframe _ _ _ _ HFR1) Hsp1)
    as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; lia. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { lia. }
  { unfold LLVMF_STK. lia. }
  (* the blocks: relay_finish's three kinds first, then the rest Rr *)
  destruct HSEP as ((rest0 & HPz0) & HSEP2).
  pose proof Hrel1 as (Rr1 & Rr2 & Rr3 & Rr4 & Rr5 & Rr6 & Rr7 & Rr8 & Rr9 & Rr10 & Rr11).
  destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 Rr8) as (_ & HT4096 & _).
  assert (HTB : rf_tblk (lm_G m) = [(lm_G m, ATABLE)])
    by (unfold rf_tblk; destruct (Z.eqb_spec (lm_G m) 0); [lia | reflexivity]).
  set (Rr := input_blks cx ++ concat (map slot_blks (lm_hs m)) ++ rest0).
  set (L := rf_tblk (lm_G m) ++ rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m)).
  assert (HPRF : Permutation (ablocks B ly3 S3) (L ++ Rr)).
  { eapply Permutation_trans; [exact HPz0|]. unfold L, Rr. rewrite HTB. unfold model_blks, rf_eblks.
    rewrite <- !app_assoc. apply xrf_perm. }
  assert (HND3 : List.NoDup (L ++ Rr)) by exact (Permutation_NoDup HPRF (xrf_nodup_x _ _ _ _ _ HAR1)).
  assert (HL3 : forall b, In b L -> In b (ablocks B ly3 S3))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPRF)); apply in_or_app; left; exact Hb).
  assert (HR3 : forall b, In b Rr -> In b (ablocks B ly3 S3))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPRF)); apply in_or_app; right; exact Hb).
  assert (HLM : forall b, In b L -> In b (model_blks m)).
  { intros b Hb. unfold L in Hb. rewrite HTB in Hb. unfold model_blks, rf_eblks.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right. cbn [app] in Hb.
    apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left; exact Hb|]. right. apply in_or_app. right. exact Hb. }
  (* relay_finish *)
  eapply (SRrG_bind segs R R_trans).
  { apply (RF_R W ly3 S3 [] regs1 mem1 md1 ch (lm_G m) (lm_es m) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_out m) Rr HPREc)
      with (kr := 0%nat).
    - rewrite Hsp1. exact HF32.
    - rewrite HFRS3. reflexivity.
    - exact Htu1.
    - exact Hlock1.
    - right. exact Hrel1.
    - exact Hlst1.
    - exact Hlstw1.
    - exact Hout1.
    - unfold L in HPRF. rewrite <- !app_assoc in HPRF. exact HPRF.
    - exact (XRF_END5 W mem1 HRV1).
    - exact HRV1.
    - intros a Ha. apply inG_app. left. exact Ha.
    - intros a Ha. apply inG_app. right. exact Ha.
    - intros a Ha He. unfold RF_G in Ha.
      repeat (apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr, AG_LISTEN in Ha; cbn in Ha; lia |]).
      exact (inG_nil a Ha).
    - apply xrf_room_eq. exact (LS_rf_room cx t m ly3 S3 HLS (proj2 Rk)).
    - (* relay_finish's own free returns at entry + 200 = 0x8240c, the one-entry trace K0's free table holds
         (lib/B/YCk0.v CTX_AFREE row [0x8240c]; the edge (CTX_relay_finish, 0x8240c, CTX_AFREE, K0Lit)) *)
      assert (E200 : BASE + AF_fr_relay_finish + 200 = 0x8240c) by (vm_compute; reflexivity).
      rewrite E200. unfold YCk0.CTX_AFREE. cbn [In]. repeat first [left; reflexivity | right].
    - rewrite <- xrf_cost_eq.
      exact (LS_rf_mok cx t m ly3 S3 HLS (proj2 Rk) (exit_keys_nonempty ly3 S3 W mem m HMOD)).
    - apply RP_NP. exact HNP.
    - exact HCNT. }
  intros W2 c2 _ (ly' & S' & Hp' & regs' & mem' & md' & k' & out' & -> & HJc & HPR & HPK & HFRM & HMO & HRM' & HPERM &
    HOUT & HLOCK & HRA & HGL & HGLw).
  (* rf_post_x's ghost list is [] (HP0 at the post's journal) *)
  assert (Ehp : Hp' = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJc). subst Hp'.
  rewrite Hsp1 in HJc.
  fold xrf_G in HJc.
  unfold rf_FP in HJc. fold L in HJc.
  rewrite HTB in HPERM.
  set (Rrun := rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) in *.
  pose proof (ajournal_gx_AR_xR _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as HAR2.
  assert (HR2 : forall b, In b Rr -> In b (ablocks B ly' S'))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; cbn [app]; apply in_or_app; right; exact Hb).
  assert (HND2 : List.NoDup ([(lm_G m, ATABLE)] ++ aout_blks (gse_cap Rrun) out' ++ Rr))
    by exact (Permutation_NoDup HPERM (xrf_nodup_x _ _ _ _ _ HAR2)).
  (* what the call keeps *)
  assert (HL4096 : forall b, In b L -> 4096 <= fst b).
  { intros [p n] Hb. destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 (HL3 _ Hb)) as (_ & H4 & _). exact H4. }
  assert (KIMG : forall a, inG G_fr a -> ~ inG xrf_G a -> a < 0x5d90c8 -> abyte_kept W mem1 W2 mem' a).
  { intros a HGa HnR Hlt. destruct (HG a HGa) as (Hi & Ho & _). pose proof (pa_segs_low a Hi) as HL.
    apply xrf_abyte_kept.
    - unfold kLowMemEnd in HL. lia.
    - apply (xrf_keep_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Hi Ho); [lia | apply xrf_fp_spares; exact HL4096 | exact HnR].
    - intros Hro. exact (proj1 (XRF_ROM_OUT a Hro) HGa). }
  assert (KHIGH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem1 W2 mem' a).
  { intros a Ha. apply xrf_abyte_kept; [lia | |].
    - apply (xrf_keep_high_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xrf_G_ok HJc a); lia.
    - intros (sg & Hsg & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as HL.
      unfold kLowMemEnd in HL. lia. }
  assert (HnFP : forall p n i, In (p, n) Rr -> 0 <= i < req_size n -> ~ inFP (ablocks_fp L) (p + i)).
  { intros p n i Hb Hi Hf. destruct (xrf_inFP_blk L (p + i) Hf) as (p' & n' & Hb' & Ha').
    assert (Hne : (p', n') <> (p, n)) by (intros E; rewrite E in Hb'; exact (xrf_nodup_app L Rr (p, n) HND3 Hb' Hb)).
    pose proof (sep_blocks_x segs B ARx LAWS ly3 S3 [] W mem1 md1 p' n' p n HAR1 (HL3 _ Hb') (HR3 _ Hb) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KB : forall b, In b Rr -> forall a, fst b <= a < fst b + snd b -> abyte_kept W mem1 W2 mem' a).
  { intros [p n] Hb a Ha. cbn [fst snd] in Ha.
    destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 (HR3 _ Hb)) as (_ & Hp4 & Hpc & _).
    pose proof (BLKN _ _ [] _ _ _ _ _ HAR1 (HR3 _ Hb)) as Hn.
    pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
    pose proof (xrf_blk_img_x _ _ [] _ _ _ _ _ HAR1 (HR3 _ Hb)) as Hoff.
    replace a with (p + (a - p)) by lia.
    apply xrf_abyte_kept; [lia | |].
    - apply (xrf_keep_blk_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n (a - p) xrf_G_ok HJc (HR3 _ Hb) (HR2 _ Hb));
        [lia | apply (HnFP p n); [exact Hb | lia]].
    - intros (sg & Hsg & _ & Hr). pose proof (pa_img_range _ (ex_intro _ sg (conj Hsg Hr))) as HIR. lia. }
  assert (HFF := frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem1 md1 1 fpos HAR1 Hfp).
  destruct HFF as (HFF0 & HFF1 & HFFa).
  change (fs_frame_bytes 1) with 128 in HFF1, HFFa.
  assert (KFRM : forall a, (frame_addr ly3 1 fpos <= a < frame_addr ly3 1 fpos + 128 \/
      SB + frame_addr ly3 1 fpos / 8 <= a < SB + frame_addr ly3 1 fpos / 8 + 16) -> abyte_kept W mem1 W2 mem' a).
  { intros a Ha.
    pose proof (Z.div_pos (frame_addr ly3 1 fpos) 8 ltac:(lia) ltac:(lia)) as Hd0.
    pose proof (Z.div_le_upper_bound (frame_addr ly3 1 fpos) 8 0xfffffff0000 ltac:(lia) ltac:(lia)) as Hd1.
    assert (Hd2 : 512 <= frame_addr ly3 1 fpos / 8) by (apply Z.div_le_lower_bound; lia).
    pose proof (xrf_frm_off_img_x _ _ _ _ _ _ _ HAR1 Hfp) as Hoff. change (fs_frame_bytes 1) with 128 in Hoff.
    apply xrf_abyte_kept; [unfold SB in Ha; lia | |].
    - apply (xrf_keep_frm_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos a xrf_G_ok HJc HAR1 Hfp).
      + unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
        change (fs_frame_bytes 1) with 128. unfold SB in Ha.
        destruct Ha as [Ha | Ha]; [left | right]; lia.
      + intros Hf. destruct (xrf_inFP_blk L a Hf) as (p' & n' & Hb' & Ha').
        destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 (HL3 _ Hb')) as (_ & Hp4 & Hpc & Happ & _).
        pose proof (sep_block_frame_x segs B ARx LAWS ly3 S3 [] W mem1 md1 p' n' 1 fpos HAR1 (HL3 _ Hb') Hfp) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SB in Ha.
        destruct Ha as [Ha | Ha]; lia.
    - intros (sg & Hsg & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as HL.
      pose proof (pa_img_range _ (ex_intro _ sg (conj Hsg Hr))) as HIR.
      unfold kLowMemEnd in HL. unfold SB in Ha. destruct Ha as [Ha | Ha]; lia. }
  (* the journal from the entry *)
  assert (HJc' : ajournal_gx_xR segs B PST ARx R G_fr 0 [] RF_STK (lf_F cx) (ablocks_fp L) ly3 S3 [] W mem1 md1 [] ly' S' [] W2 mem' md' k')
    by exact (ajournal_gx_G_mono_xR segs B PST ARx xrf_G G_fr 0 [] RF_STK (lf_F cx) (ablocks_fp L) ly3 S3 [] W mem1 md1 [] ly' S' [] W2 mem' md'
      k' xrf_G_sub HJc).
  assert (HJ2 : ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) ([] ++ [(1, fpos)]) ly' S' [] W2 mem' md' (k + k')).
  { apply (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem1 md1 k
      RF_STK (lf_F cx) 0 [] (ablocks_fp L) [] ly' S' [] W2 mem' md' k' HJ1 HJc');
      [unfold LLVMF_STK; lia | lia | lia | intros a Ha; exfalso; exact (inFP_nil a Ha) | exact HG |].
    intros a Hf. destruct (xrf_inFP_blk L a Hf) as (p & n & Hb & Ha).
    pose proof (xrf_L_pos _ _ _ _ _ _ _ _ _ _ _ _ (p, n) Hrel1 Hout1 Hb) as Hpos. cbn [snd] in Hpos.
    unfold req_size in Ha. destruct (Z.eqb_spec n 0) as [Hn0 | _]; [lia|].
    destruct (HSEP2 (p, n) (HLM _ Hb)) as [Hne | Hin].
    - right. exists p, n. split; [exact (HL3 _ Hb)|]. split; [exact Hne|]. unfold req_size.
      destruct (Z.eqb_spec n 0); [lia | exact Ha].
    - left. split; [apply Hin; cbn [fst snd]; unfold req_size; destruct (Z.eqb_spec n 0); [lia | exact Ha]|].
      exists p, n. split; [exact (HL3 _ Hb)|].
      unfold req_size. destruct (Z.eqb_spec n 0); [lia | exact Ha]. }
  cbn [app] in HJ2.
  (* the frame address *)
  assert (HFA : frame_addr ly' 1 fpos = frame_addr ly3 1 fpos).
  { destruct (ajournal_gx_inner_xR _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as (memSc & HJic & _).
    pose proof HJic as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF.
    reflexivity. }
  (* the stream after: g_nout = |O| *)
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HOno & _).
  (* the post *)
  apply (SRrG_ret segs R R_refl).
  exists ly', S', regs', mem', md', (k + k'),
    (LM (lm_k m) (lm_hs m) (lm_G m) [] (lx_rf_ctl (gse_c Rrun)) (gse_O Rrun) (lm_mx m) (gse_cap Rrun) out' (lm_gn m) (lm_nfd m)).
  cbn [lm_k lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  assert (HPM : Permutation (ablocks B ly' S') (input_blks cx ++
      model_blks (LM (lm_k m) (lm_hs m) (lm_G m) [] (lx_rf_ctl (gse_c Rrun)) (gse_O Rrun) (lm_mx m) (gse_cap Rrun) out'
        (lm_gn m) (lm_nfd m)) ++ rest0)).
  { eapply Permutation_trans; [exact HPERM|]. apply Permutation_sym. unfold model_blks. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    exact (xrf_perm (lm_G m, ATABLE) [] (concat (map slot_blks (lm_hs m))) (aout_blks (gse_cap Rrun) out') (input_blks cx) rest0). }
  split.
  { (* the configuration *)
    unfold cfg_at, w64. rewrite Q1, BASE_B0, Z.add_assoc. reflexivity. }
  split; [exact HJ2|].
  split.
  { (* the frame and the fake frame *)
    rewrite HFA.
    unfold aframe_at in HFR1 |- *. cbv zeta in HFR1 |- *.
    destruct HFR1 as (FS & FW & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F96 & F104 & F120 & F128 & F136 & F152 &
      F184 & FF0 & FF8 & FF16 & FFw & FFsh & FFshw).
    unfold sv8 in *.
    assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) ->
      val_mem segs (arm W mem1) a 8 v -> val_mem segs (arm W2 mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem1); [intros x Hx; apply KHIGH; lia | exact Hv]).
    assert (KF : forall a v, frame_addr ly3 1 fpos <= a -> a + 8 <= frame_addr ly3 1 fpos + 128 ->
      val_mem segs (arm W mem1) a 8 v -> val_mem segs (arm W2 mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem1); [intros x Hx; apply KFRM; left; lia | exact Hv]).
    split.
    { intros o r Hor. assert (Ho : 8 <= o <= 104).
      { unfold saved_regs in Hor. cbn [In] in Hor.
        repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- _; lia |]). destruct Hor. }
      apply KV; [lia | lia | exact (FS o r Hor)]. }
    split; [apply (akept_awr W mem1); [intros x Hx; apply KHIGH; lia | exact FW]|].
    split; [apply KV; [lia | lia | exact F32]|]. split; [apply KV; [lia | lia | exact F40]|].
    split; [apply KV; [lia | lia | exact F48]|]. split; [apply KV; [lia | lia | exact F56]|].
    split; [apply KV; [lia | lia | exact F64]|]. split; [apply KV; [lia | lia | exact F72]|].
    split; [apply KV; [lia | lia | exact F80]|]. split; [apply KV; [lia | lia | exact F96]|].
    split; [apply KV; [lia | lia | exact F104]|]. split; [apply KV; [lia | lia | exact F120]|].
    split; [apply KV; [lia | lia | exact F128]|]. split; [apply KV; [lia | lia | exact F136]|].
    split; [apply KV; [lia | lia | exact F152]|]. split; [apply KV; [lia | lia | exact F184]|].
    split; [apply KF; [lia | lia | exact FF0]|]. split; [apply KF; [lia | lia | exact FF8]|].
    split; [apply KF; [lia | lia | exact FF16]|].
    split; [apply (akept_awr W mem1); [intros x Hx; apply KFRM; left; lia | exact FFw]|].
    split.
    { apply (akept_garr8 W mem1); [|exact FFsh]. intros x Hx. change (length fake_shadow) with 16%nat in Hx.
      apply KFRM. right. lia. }
    apply (akept_awr W mem1); [intros x Hx; apply KFRM; right; lia | exact FFshw]. }
  split.
  { (* the fake frame's flag word: kept by the store (above) and by the call (it lies in the fake frame) *)
    rewrite HFA, (lx_fla_kept_xR HJc). apply (lxk_sv8_kept W W2 mem1 mem'); [|exact HFL1].
    intros x Hx. apply KFRM. left. lia. }
  split; [exact HFA|].
  split.
  { (* the model *)
    unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [exact Hhs1|].
    split.
    { intros i Hi. specialize (Hslots1 i Hi). unfold aslot in *.
      assert (HHA : forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
        abyte_kept W mem1 W2 mem' a).
      { intros a Ha. cbn [rg_s fr_RG fr_globals_b] in Ha. unfold ASRC in Ha. apply KIMG.
        - apply HGs. cbn [rg_s fr_RG fr_globals_b]. unfold ASRC. lia.
        - intros HR'. apply xrf_inG_RF in HR'. lia.
        - lia. }
      destruct (nth i (lm_hs m) None) as [h|] eqn:Eh.
      - apply (asrc_at_kept B ly3 S3 W mem1 ly' S' W2 mem' _ h Hslots1).
        + intros r Hr a Ha. refine (xrf_asrc_fp_in (abyte_kept W mem1 W2 mem') ly3 S3 W mem1 _ h Hslots1 HHA _ r Hr a Ha).
          intros b Hb x Hx. apply (KB b); [|exact Hx].
          unfold Rr. apply in_or_app. right. apply in_or_app. left.
          exact (xrf_slot_in (lm_hs m) i h ltac:(rewrite Hhs1; exact Hi) Eh b Hb).
        + intros b Hb. apply HR2. unfold Rr. apply in_or_app. right. apply in_or_app. left.
          exact (xrf_slot_in (lm_hs m) i h ltac:(rewrite Hhs1; exact Hi) Eh b Hb).
      - destruct Hslots1 as [Hz Hw]. split.
        + apply (akept_garr8 W mem1); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx. apply HHA.
          unfold ASRC in *. lia.
        + apply (akept_awr W mem1); [|exact Hw]. intros x Hx. apply HHA. lia. }
    split.
    { destruct HRA as [(HT0 & _) | HRA]; [lia | exact HRA]. }
    split.
    { rewrite <- HOno in HOUT. exact HOUT. }
    split.
    { apply (agone_at_kept fr_RG W mem1 W2 mem' _ Hgone1). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd rg_gone fr_RG fr_globals_b] in Ha. apply KIMG; [apply XRF_Gcells; left; cbn; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [exact HLOCK|].
    split.
    { apply (awake_at_kept fr_RG W mem1 W2 mem' Hwake1). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd rg_wake fr_RG fr_globals_b] in Ha. apply KIMG; [apply XRF_Gcells; right; left; cbn; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    assert (KN : forall a, AG_NFD <= a < AG_NFD + 4 -> abyte_kept W mem1 W2 mem' a).
    { intros a Ha. unfold AG_NFD in Ha. apply KIMG; [apply XRF_Gcells; right; right; left; unfold AG_NFD; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [apply (akept_vm W mem1); [intros x Hx; apply KN; cbn in Hx; lia | exact Hnfd1]|].
    split; [apply (akept_awr W mem1); [intros x Hx; apply KN; lia | exact Hnfdw1]|].
    split; [exact Hnfdr1|].
    split.
    { apply (akept_vm W mem1); [|exact Htu1]. intros x Hx. cbn in Hx. unfold AG_THREAD_UP in Hx.
      apply KIMG; [apply XRF_Gcells; right; right; right; unfold AG_THREAD_UP; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [exists (2 ^ 32 - 1); exact HGL | exact HGLw]. }
  split.
  { (* the input block *)
    destruct HIN1 as [Hblk Hg]. split.
    - destruct Hblk as [Hb0 | (Hn & Hin)]; [left; exact Hb0|]. right. split; [exact Hn|].
      apply HR2. unfold Rr, input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. left. reflexivity.
    - apply (akept_garr8 W mem1); [|exact Hg]. intros x Hx. rewrite length_map, <- Hlen in Hx.
      destruct Hblk as [(Hn0 & _) | (Hn & Hin)]; [lia|].
      apply (KB (c_p cx, c_n cx)); [|cbn [fst snd]; exact Hx].
      unfold Rr, input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. left. reflexivity. }
  assert (HROM2 : rom_view segs W2 mem').
  { eapply (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low); [exact HJc | | exact PST_ROM | exact HRV1].
    intros a Ha. destruct (XRF_ROM_OUT a Ha) as (H1 & H2 & H3 & H4). split; [|split; [exact H2 | split; assumption]].
    intros HGa. exact (H1 (xrf_G_sub a HGa)). }
  split; [exact HROM2|].
  split.
  { (* the jump table *)
    intros i Hi. apply (xrf_vm_aview W W2 mem1 mem'); [|exact (HJT1 i Hi)].
    intros x Hx. cbn in Hx. assert (Hro : in_rom segs x) by (apply XRF_JTAB_ROM; lia).
    rewrite (HROM2 x Hro), (HRV1 x Hro). reflexivity. }
  split.
  { (* the blocks *)
    split; [exists rest0; exact HPM|].
    intros b Hb. unfold model_blks in Hb. cbn [lm_G lm_es lm_hs lm_cap lm_out map concat app] in Hb.
    destruct Hb as [<- | Hb]; [apply HSEP2; left; reflexivity|].
    apply in_app_or in Hb as [Hb | Hb].
    { apply HSEP2. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    destruct (in_dec xrf_peq b (ablocks B (c_ly cx) (c_S cx))) as [Hbe | Hbe]; [|left; exact Hbe].
    destruct (in_dec xrf_peq b (ablocks B ly3 S3)) as [Hb3 | Hb3].
    - pose proof (Permutation_in _ HPRF Hb3) as HbLR. apply in_app_or in HbLR as [HbL | HbR].
      + apply HSEP2. exact (HLM _ HbL).
      + exfalso. cbn [app] in HND2. apply List.NoDup_cons_iff in HND2 as [_ Hn2].
        exact (xrf_nodup_app (aout_blks (gse_cap Rrun) out') Rr b Hn2 Hb HbR).
    - right. destruct b as [p n]. intros a Ha. cbn [fst snd] in Ha.
      assert (Hb' : In (p, n) (ablocks B ly' S'))
        by (apply (Permutation_in _ (Permutation_sym HPERM)); right; cbn [app]; apply in_or_app; left; exact Hb).
      pose proof (BLKN _ _ [] _ _ _ _ _ HAR2 Hb') as Hn.
      pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
      replace a with (p + (a - p)) by lia. apply (Hfreed p n (a - p) Hbe Hb3). lia. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xrf_kept -> getr regs' r = getr regs r)
    by (intros r H1 H2; rewrite (xrf_pres regs1 regs' r HPR H1); exact (KR r H2)).
  split; [rewrite (RR 2%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R2|].
  split; [rewrite (RR 8%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (RR 9%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (RR 3%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (RR 4%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (RR 27%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R27|].
  split; [exact (RR 19%bv ltac:(xrf_cs) ltac:(cbv; tauto))|].
  (* the caller's frame: kept by the store (off g_nout) and by the call (above its frame) *)
  assert (KC : forall a, lf_F cx <= a < spZ (c_regs cx) -> aview segs (w_H W2) mem' a = aview segs (w_H W) mem a).
  { intros a Ha. rewrite (proj1 (KHIGH a ltac:(lia))). apply aview_eq_of. apply MEQ.
    rewrite unsigned_lit_small by lia. cbn [rg_nout fr_RG fr_globals_b]. lia. }
  split.
  { apply (xrf_vm_aview W W2 mem mem'); [|exact HAT]. intros x Hx. apply KC. unfold AX_AT in Hx. cbn in Hx. lia. }
  split; [exact KC|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [intros Hes; unfold Rrun; rewrite Hes; reflexivity|].
  split; [rewrite xrf_run_eq; reflexivity|].
  split.
  { intros rest Hrest.
    assert (Hrr : Permutation rest rest0).
    { apply (Permutation_app_inv_l (input_blks cx ++ model_blks m)). rewrite <- !app_assoc.
      eapply Permutation_trans; [apply Permutation_sym; exact Hrest | exact HPz0]. }
    eapply Permutation_trans; [exact HPM|]. apply Permutation_app_head. apply Permutation_app_head.
    apply Permutation_sym. exact Hrr. }
  split; [rewrite HFRM; reflexivity|].
  split; [rewrite xrf_cost_eq; exact HMO|].
  split; [rewrite xrf_run_eq; reflexivity|].
  (* the room round: NP from relay_finish's rp_RM; the count after it is X's plus relay_finish's net growth, which
     its peak rf_pk covers (the entries' blocks are freed, the table kept, g_out replaced by one block) *)
  split; [exact (proj1 (RP_NP S' 0%nat) HRM')|].
  apply (cnt_ok_pk_mono RP rf_pk _ (ablocks B ly3 S3) _); [|exact HCNT].
  intros P. rewrite (ReplyCnt.acnt_perm P _ _ HPERM), (ReplyCnt.acnt_perm P _ _ HPRF). unfold L. rewrite HTB.
  rewrite (ReplyCnt.acnt_app P [(lm_G m, ATABLE)] (aout_blks (gse_cap Rrun) out' ++ Rr)),
    (ReplyCnt.acnt_app P (aout_blks (gse_cap Rrun) out') Rr),
    (ReplyCnt.acnt_app P ([(lm_G m, ATABLE)] ++ rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m)) Rr),
    (ReplyCnt.acnt_app P [(lm_G m, ATABLE)] (rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m))).
  pose proof (lx_acnt_aout P (gse_cap Rrun) out'). unfold rf_pk. cbv beta. lia.
Qed.

End wR.

End lxx.
