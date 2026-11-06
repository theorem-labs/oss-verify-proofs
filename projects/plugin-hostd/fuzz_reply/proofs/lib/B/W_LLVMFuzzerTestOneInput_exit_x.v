(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: SEG_EXIT of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput (image B,
   fuzz_reply.asan-ubsan 0x84e64-0x850f8) over a GENERIC allocator relation ARx: the ARx conversion of
   lib/B/W_LLVMFuzzerTestOneInput_exit.v's lf_seg_exit, stated as the Section hypothesis SEG_EXIT of
   lib/B/W_LLVMFuzzerTestOneInput_cut_x.v:639 (the form lib/B/W_LLVMFuzzerTestOneInput_top_x.v consumes).  The AR
   files are NOT edited.
   SOURCE: this lane's AR proof at ae51b062ed4 (lf_seg_exit Qed on the kit fb28b53a2b8; cbrec v17 VERDICT ok) plus
   the post clause of 38eb27d6984.  TEMPLATE: image A's conversion of the same segment, e60b29a425a
   lib/A/W_LLVMFuzzerTestOneInput_exit_x.v.
   Base: the B cut e879350a388 (the cut tip a38906f5dd8 + the kit
   cand12 3fb3a60177f + the harness-block clause HB; cut_x Requires lib.Reusable YCbqG and the kit's generated lib/B
   W_kit_x / W_journal_x / W_img_x); 1481d9da2b2 is not in this history.
   THE ONE PREMISE THAT GOES AWAY.  The AR file's LS_exit_end carries `0 <= k'` (I added it on 2026-10-29: with k'
   universal the text was unsatisfiable at image B's fr_live_post_b, which bounds k by `0 <= k`).  In the ARx shape
   that premise is REDUNDANT and is dropped: LS_exit_end here takes the journal itself,
   `ajournal_gx_x ... k'`, whose 8th conjunct (YCbqG.v ajournal_x) is `0 <= k'`.  This is A's ARx text
   (lib/A/W_LLVMFuzzerTestOneInput_exit_x.v:158-167) with B's names.
   THE HARNESS-BLOCK POST CONJUNCT (HB).  e879350a388 adds `List.NoDup (fr_hblks W' mem') /\ incl (fr_hblks W' mem')
   (ablocks B ly' S')` LAST in fr_lib_post_cf_x, fr_hblks being the cut's one definition (_cut.v).  lx_end_state_x
   carries the stronger `List.NoDup (input_blks cx ++ fr_hblks W' mem') /\ incl ...` LAST (bx_post_hblks_x, from the
   model's blocks), and lx_post_of_end_x drops the input block with NoDup_app_remove_l.  Any FURTHER post conjunct
   goes after it. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_exit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g6 W_contract_xR_g3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_srlf_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YE01_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCk0.
(* the ARx twins of YE01's two journal lemmas (new file of this lane, A's lib/A/YE01_x.v text) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YE01_x.
(* the five ARx blocks, each proved in its own file against W_bx_defs_x.v's statement *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
  W_bx_order_x W_bx_rf_x W_bx_ends_x W_bx_reset_x W_bx_ffexit_x.
(* RelocB's sink-instance guard, after every Import of YE2k: no sink class is a hint after it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.

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

(* ---- the AR file's Section hypotheses (lib/B/W_LLVMFuzzerTestOneInput_exit.v Section lx), over ARx where they
   name AR; the AR-free ones keep their text ---- *)
Hypothesis TL : PALib B.
Hypothesis MLM : ameter_laws MT.
Hypothesis ASF : astack_free_law_x segs B ARx.
Hypothesis FFL : frame_flag_lawP_x segs B ARx.
Hypothesis ERR : errno_law_x B ARx.
(* the AR file's ML (model_laws) is read only by W_frame.v's aj_flag_store_pi, in the release's flag run; its twin
   W_frame_x.aj_flag_store_pi_x takes instead the state invariant WFx, its law and the frame split SFREE
   (lib/B/W_frame_x.v Section a0's hypotheses, verbatim; A's conversion does the same) *)
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law segs ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
  exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Variable MMAX : Z.
Hypothesis HG_SL : forall a, inG (G_SL B fr_RG) a -> inG G_fr a.
Hypothesis AZS_s : azs B (rg_s fr_RG) (4 * ASRC).
(* ---- the room round (image A's exit_x at 5a9b16eac9e; ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.2): the allocator rules' room
   record RP, whose room invariant is the cut's NP (the walk's RM := fun S _ => NP S; at top_x rp_RM RP := fun S _ =>
   room_live_cf S = NP) ---- *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
(* ---- the callees, in the kit's _x forms (lib/B/W_contract_x.v) ---- *)
Hypothesis CSD : csd_spec_x B PST ARx (BASE + AF_fr_check_shape_done).
Hypothesis SR : sr_spec_g_x B PST ARx MT RP (BASE + AF_fr_source_reset).
(* check_shape_ends: the kit's own twin of B's contract (W_contract_x.v:1230), at every G with gx_ok.  The AR file's
   lx_cshe_spec was the verbatim copy of that contract; here the kit's twin is taken instead. *)
Hypothesis CSHE : forall G, gx_ok segs B G -> cshe_spec_x B PST ARx MT RP G (BASE + AF_fr_check_shape_ends).
(* relay_finish: the kit's rf_spec_x at its own G = RF_G ++ G_SL, over K0's free table (lib/B/YCk0.v CTX_AFREE
   at 5128b798413); the site discharges In [BASE + AF_fr_relay_finish + 200] = [0x8240c] *)
Hypothesis RFg : rf_spec_x B PST ARx MT RP MMAX (RF_G fr_RG AG_LISTEN ++ G_SL B fr_RG) fr_RG AG_THREAD_UP AG_LISTEN
  YCk0.CTX_AFREE (BASE + AF_fr_relay_finish).
Hypothesis XRF_ERRNO : rg_out fr_RG + 8 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.
Hypothesis XRF_ROM_OUT : rom_out segs B G_fr.
(* ---- the model rules at X (LS is cut_x's LSx) ---- *)
(* TX_LS_rf_room (image A's exit_x at 5a9b16eac9e): lregs_X's t bound after LSx *)
Hypothesis LS_rf_room : forall cx t m ly S,
  LSx cx t m ly S -> 0 <= t <= OPS_MAX ->
  lx_rf_room MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).
(* KF-COUNT F8 (A aacecd50fed): the block's meter at X takes lregs_X's t bound and the relay entries' non-empty key
   texts (W_bx_rf_x's exit_keys_nonempty, from amodel_at's aentry_ok) *)
Hypothesis LS_exit_budget : forall cx t m ly S, LSx cx t m ly S ->
  0 <= t <= OPS_MAX ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  mo_ok MT S (lx_exit_cost MT m).
Hypothesis XR_HGM : forall a, inG xr_GM a -> inG G_fr a.
Hypothesis XR_GSHV : forall ly S Hp (W : world segs) mem md a n, ARx ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> rg_s fr_RG <= x < rg_s fr_RG + 4 * ASRC) ->
  shadow_hull_vis (aview segs (w_H W) mem) a n.
Hypothesis GWR : glob_wr_law G_fr.
(* the "" literal .str.3's shadow facts in every ARx state: the kit's ashp_x (the AR file's XE_LIT_S is W_shadow_pin's
   ashp, of which ashp_x is the twin) *)
Hypothesis XE_LIT_S : ashp_x ARx (VAL AX_lit_empty) 1.
Hypothesis RI_exit_slots : forall cx t m, RINV cx t m ->
  forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None).
(* the shutdown check's run (image A's restated text, 3f40808c334): its last two premises are amodel_at's
   (W_LLVMFuzzerTestOneInput_cut.v:466), which the arm holds at X: g_gone is 0 or 1 (agone_at, W_rep.v:195) and no held
   text has a NUL byte (asrc_at's held list, alist_at at lines = true, W_rep.v:92) *)
Hypothesis RI_exit_ends : forall cx t m, RINV cx t m -> (0 < length (lm_es m))%nat ->
  0 <= lm_gn m <= 1 ->
  (forall i h, nth i (lm_hs m) None = Some h -> Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))) ->
  lx_ends_run (lm_gn m) (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).
(* the live-state clauses at the return, in cut_x's post shape: fr_surv names the memories.  k' is the journal's
   counter, and the journal premise carries `0 <= k'`, so the AR file's explicit `0 <= k'` premise is dropped here.
   The post's NP is NOT concluded here (the room round): the walk threads it through the cuts (lcut_x's NP) and every
   allocator call's post to the return.  Its last four premises, after the journal, are the text of record
   TX_LS_exit_end_e's (A ReplyLSI.v:206; B ReplyLS3B_inst.v:204 at 89889da5299; a Theorem Labs lane's LS_exit_end3e):
   relay_finish's final capacity (lx_rf_post_site_x's cap conjunct), lregs_X's t bound, the return's held blocks
   (HFH) and their NoDup (HND), all held at lx_end_of_ffexit_x *)
Hypothesis LS_exit_end : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= lx_exit_cost MT m ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks B ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
(* the room round's two exit rules for the post's XCNT and CAPOUT conjuncts (fr_lib_post_cf_x's last two; image A's
   exit_x text at 5a9b16eac9e): LS facts at X, so LS rules.  LS_exit_cnt: the return's blocks other than the input,
   the kept table and g_out are the LS state's rest, whose counts the LS state bounds: the cut's own count
   (ReplyCnt.xcnt_ok, _cut.v's XCNT text).  LS_exit_cap: relay_finish's final capacity, which is g_capout at the return
   (lx_rf_post_site_x's cap conjunct), stays under CAPOUT_MAX. *)
Hypothesis LS_exit_cnt : forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks B ly' S') -> 4096 <= p) ->
  ReplyCnt.xcnt_ok B S' ly' (input_blks cx) (lm_G m) cap out.
Hypothesis LS_exit_cap : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> 0 <= t <= OPS_MAX ->
  gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) <= CAPOUT_MAX.
(* the room round's count row at X (image A's exit_x LS_cnt; pk_exit = 5 = relay_finish's rf_pk): the live counts at
   X plus relay_finish's peak stay under RP's bounds; check_shape_ends and source_reset later only free.  The guards
   are the walk's facts at X (the model's sizes come from amodel_at; lregs_X's t bound) *)
Hypothesis LS_cnt : forall cx t m ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> amodel_at B ly S W mem m -> 0 <= t <= OPS_MAX ->
  cnt_ok_pk RP rf_pk (ablocks B ly S).
(* the journal's footprint names no sink, over cut_x's lf_base_x *)
Hypothesis FP_SINK : forall cx Hp, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ~ YI16.sink_open_fp (lf_FP fr_FP cx).
Hypothesis AIL : asink_img_laws segs B tfib_K.
Hypothesis HG_K : forall a, aenv_addr tfib_K a \/ ak_meta_ptr tfib_K <= a < ak_meta_ptr tfib_K + 8 \/
  ak_meta_mem tfib_K <= a < ak_meta_mem tfib_K + 8 -> 0 <= a < 2 ^ 64 /\ ~ inG G_fr a.
(* ---- forced by the generic relation and the placement PST (A's conversion takes the same two, plus HPST) ---- *)
(* the image's bytes lie outside PST: the generic journal keeps only bytes outside PST.  At the instance's PST := []
   it holds trivially. *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* a live block's size: AR's al_blocks carries `0 <= n < MALLOC_MAX`, the generic alx_blocks carries neither *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  0 <= n.
Hypothesis BLKM : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  n < 2 ^ 30.

(* ------------------------------------------------------------------ THE STATEMENT
   cut_x's SEG_EXIT (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v:639), over the Section above *)
Definition lf_seg_exit_x_stmt : Prop :=
  forall cx Hp W c,
    lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
    INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp W c ->
    SRr segs W c (lf_post_x B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx cx Hp).


(* the journal keeps the layout's frame bases, so the flag addresses (the AR file's lx_fla_kept, over ajournal_gx_x) *)
Lemma lx_fla_kept_x : forall {G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k},
  ajournal_gx_x segs B PST ARx G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 own ly2 S2 [] W2 m2 md2 k ->
  forall cid pos, flag_addr ly2 cid pos = flag_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _) cid pos.
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold flag_addr. rewrite EF. reflexivity.
Qed.

(* the image cover, from the laws' image field (lib/B/W_img_x.v:30 fr_img_cover_x; W_kit_x / W_frame_x name it
   IMGC), in place of AR's ledger field fr_img_cover *)
Lemma IMGC : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Proof. exact (W_img_x.fr_img_cover_x B ARx LAWS). Qed.

(* ------------------------------------------------------------------ what the hypotheses give
   The AR file's derived facts (lib/B/W_LLVMFuzzerTestOneInput_exit.v, the A donor's :343-470).  Their statements and
   proofs are AR-FREE - they read only MT / MLM / B / G_fr / HG / HG_SL / XR_HGM / XRF_ERRNO - so they are the AR
   file's text, restated here (not re-derived) because this Section's variables differ: LS is cut_x's LSx. *)
Lemma lx_ends_cost_nonneg : forall hs, 0 <= lx_ends_cost MT hs.
Proof.
  pose proof (mo_free_nonneg MT MLM) as Hf.
  induction hs as [|[h|] hs IH]; cbn [lx_ends_cost]; [lia| |exact IH].
  assert (0 <= hl_n (hs_held h)) by (unfold hl_n; lia). nia.
Qed.
Lemma lx_sr_cost_nonneg : forall o, 0 <= sr_cost MT o.
Proof.
  pose proof (mo_free_nonneg MT MLM) as Hf.
  intros [h|]; cbn [sr_cost]; [|lia]. unfold lf_cost.
  assert (0 <= hl_n (hs_pending h)) by (unfold hl_n; lia). assert (0 <= hl_n (hs_expected h)) by (unfold hl_n; lia).
  assert (0 <= hl_n (hs_held h)) by (unfold hl_n; lia). nia.
Qed.
Lemma lx_sr_total_nonneg : forall hs, 0 <= lx_sr_total MT hs.
Proof.
  intros hs. unfold lx_sr_total.
  pose proof (lx_sr_cost_nonneg (nth 0 hs None)). pose proof (lx_sr_cost_nonneg (nth 1 hs None)).
  pose proof (lx_sr_cost_nonneg (nth 2 hs None)). pose proof (lx_sr_cost_nonneg (nth 3 hs None)). lia.
Qed.
(* the AR file's LS_rf_mok, converted (KF-COUNT F8): LS_exit_budget here takes lregs_X's t bound and the non-empty key
   texts *)
Lemma LS_rf_mok_x : forall cx t m ly S,
  LSx cx t m ly S -> 0 <= t <= OPS_MAX ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  mo_ok MT S (lx_rf_cost MT (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)).
Proof.
  intros cx t m ly S HLS Ht HK. apply (mo_ok_le MT MLM S _ (lx_exit_cost MT m) (LS_exit_budget cx t m ly S HLS Ht HK)).
  unfold lx_exit_cost. pose proof (lx_ends_cost_nonneg (lm_hs m)). pose proof (lx_sr_total_nonneg (lm_hs m)). lia.
Qed.
Lemma xi_GM_cover : forall l,
  forallb (fun r => existsb (fun g => (fst g <=? fst r) && (fst r + snd r <=? fst g + snd g)) xr_GM) l = true ->
  forall a, inG l a -> inG G_fr a.
Proof.
  intros l Hl a Ha. apply XR_HGM. unfold inG in *. apply Exists_exists in Ha as (r & Hr & Hz).
  rewrite forallb_forall in Hl. pose proof (Hl r Hr) as Hc. apply existsb_exists in Hc as (g & Hg & Hc).
  apply andb_prop in Hc as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply Exists_exists. exists g. split; [exact Hg|]. unfold in_zr in *. lia.
Qed.
(* every global amodel_at reads ends at or below g_out + 8 (B: 0x5d90c8) *)
Lemma xi_GM_below : forall a, inG xr_GM a -> a < rg_out fr_RG + 8.
Proof.
  intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  assert (Hb : forallb (fun r => fst r + snd r <=? rg_out fr_RG + 8) xr_GM = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. specialize (Hb r Hr). apply Z.leb_le in Hb. unfold in_zr in Hz. lia.
Qed.
Lemma HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Proof.
  intros a Ha. apply (xi_GM_cover [(rg_s fr_RG, 4 * ASRC)]); [vm_compute; reflexivity|].
  apply (proj2 (inG_cons _ _ _)). left. unfold in_zr. cbn [fst snd]. exact Ha.
Qed.
Lemma HG_RFc : forall a, inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_client fr_RG, 4); (AG_LISTEN, 4)] a ->
  inG G_fr a.
Proof. apply xi_GM_cover. vm_compute. reflexivity. Qed.
Lemma HG_MODEL : forall a,
  inG [(rg_src fr_RG, 8); (rg_capsrc fr_RG, 4); (rg_send_max fr_RG, 8); (rg_send_dead fr_RG, 1);
       (rg_gone fr_RG, 1); (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a ->
  inG G_fr a.
Proof. apply xi_GM_cover. vm_compute. reflexivity. Qed.
Lemma XRF_Gcells : forall a,
  rg_gone fr_RG <= a < rg_gone fr_RG + 1 \/ rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 \/
  AG_NFD <= a < AG_NFD + 4 \/ AG_THREAD_UP <= a < AG_THREAD_UP + 1 -> inG G_fr a.
Proof.
  intros a Ha. apply (xi_GM_cover [(rg_gone fr_RG, 1); (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1)]);
    [vm_compute; reflexivity|].
  destruct Ha as [Ha | [Ha | [Ha | Ha]]];
    repeat (apply (proj2 (inG_cons _ _ _)); first [left; unfold in_zr; cbn [fst snd]; lia | right]).
Qed.
Lemma XE_ERR_HI : rg_out fr_RG + 8 <= as_errno B.
Proof. exact (proj1 XRF_ERRNO). Qed.
Lemma XE_ERR_S : as_errno B + 4 <= rg_s fr_RG \/ rg_s fr_RG + 4 * ASRC <= as_errno B.
Proof.
  right. assert (E : (rg_s fr_RG + 4 * ASRC <=? rg_out fr_RG + 8) = true) by (vm_compute; reflexivity).
  apply Z.leb_le in E. pose proof (proj1 XRF_ERRNO). lia.
Qed.
Lemma XR_ERRNO : forall a, inG xr_GM a -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros a Ha. pose proof (xi_GM_below a Ha). pose proof (proj1 XRF_ERRNO). lia. Qed.
(* read-only image ranges: one segment check by vm_compute *)
Definition xe_romseg (lo hi : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? lo) &&
    (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Lemma xe_romseg_ok : forall lo hi a, xe_romseg lo hi = true -> lo <= a < hi -> in_rom segs a.
Proof.
  intros lo hi a H Ha. unfold xe_romseg in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hs|]. split; [exact H0 | lia].
Qed.
Lemma XRF_JTAB_ROM : forall a, fr_jtab <= a < fr_jtab + 36 -> in_rom segs a.
Proof. intros a Ha. apply (xe_romseg_ok fr_jtab (fr_jtab + 36)); [vm_compute; reflexivity | exact Ha]. Qed.
Lemma xe_vm1_of_aview : forall (W : world segs) mem a v,
  aview segs (w_H W) mem a = Some v -> val_mem segs (arm W mem) a 1 v /\ 0 <= v < 256.
Proof.
  intros W mem a v E. destruct (aview_byte segs (w_H W) mem a v E) as (b & Hb & Hv & Hr).
  split; [|exact Hr]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold arm. rewrite Hb. f_equal. unfold YO0f.le_byte.
  replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia.
  rewrite Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma XRF_END5 : forall (W : world segs) (mem : word -> option byte),
  rom_view segs W mem -> garr8 segs (arm W mem) (VAL A_lit_end5) (bzs END5).
Proof.
  intros W mem HRV j Hj. change (length (bzs END5)) with 5%nat in Hj.
  assert (Hr : in_rom segs (VAL A_lit_end5 + Z.of_nat j)).
  { apply (xe_romseg_ok (VAL A_lit_end5) (VAL A_lit_end5 + 5)); [vm_compute; reflexivity | lia]. }
  apply xe_vm1_of_aview. rewrite (HRV _ Hr).
  destruct j as [|[|[|[|[|j]]]]]; [..|lia]; vm_compute; reflexivity.
Qed.


(* ================================================================== the cut's harness-block post clause (HB)
   e879350a388 adds, LAST in fr_lib_pre_cf_x and LAST in fr_lib_post_cf_x (W_LLVMFuzzerTestOneInput_cut_x.v:111 / :128),
     pre:  NoDup ((if n =? 0 then [] else [(p, n)]) ++ fr_hblks W mem) /\ incl (fr_hblks W mem) (ablocks B ly S)
     post: NoDup (fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')
   where fr_hblks (W_LLVMFuzzerTestOneInput_cut.v, the one definition on image B) reads g_src's table and g_out's
   buffer out of memory.  SEG_EXIT owes the POST half.  It needs NO new premise: the table and the buffer are the
   model's blocks (amodel_at's arelay_at / aout_at carry both their addresses and `In ... (ablocks ...)`), and
   ablocks_sep's Permutation together with ablocks' NoDup gives the distinctness.  bx_post_hblks_x proves the clause
   with the input block kept in the NoDup; lx_post_of_end_x drops it. *)
Lemma bx_nodup_ablocks_x : forall ly S (W : world segs) mem md, ARx ly S [] W mem md -> List.NoDup (ablocks B ly S).
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
Lemma bx_nodup_mid_x : forall {X : Type} (A : list X) t b, List.NoDup (A ++ t :: b) -> List.NoDup (A ++ b).
Proof.
  intros X A t b H.
  assert (HP : Permutation (t :: A ++ b) (A ++ t :: b)) by apply Permutation_middle.
  pose proof (Permutation_NoDup (Permutation_sym HP) H) as H2.
  inversion H2 as [|x l Hnin Hnd]; exact Hnd.
Qed.
Lemma bx_nodup_cut_x : forall {X : Type} (A : list X) t b rest,
  List.NoDup (A ++ t :: b ++ rest) -> List.NoDup (A ++ t :: b).
Proof.
  intros X A t b rest H.
  assert (E : A ++ t :: b ++ rest = (A ++ t :: b) ++ rest)
    by (rewrite <- app_assoc; cbn [app]; reflexivity).
  rewrite E in H. exact (NoDup_app_remove_r _ _ H).
Qed.
(* a live block's address and size are 64-bit, for rdword's range side condition *)
Lemma bx_blk_rng_x : forall ly S (W : world segs) mem md p n, ARx ly S [] W mem md -> In (p, n) (ablocks B ly S) ->
  0 <= p < 2 ^ 64 /\ 0 <= n < 2 ^ 64.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (alx_blocks _ _ ARx LAWS ly S [] W mem md p n HAR Hin) as (_ & H4 & Hceil & _).
  pose proof (BLKN ly S [] W mem md p n HAR Hin) as Hn0. pose proof (BLKM ly S [] W mem md p n HAR Hin) as Hn1.
  pose proof ASAN_CEIL_range as (CR & _). pose proof (req_size_pos n ltac:(lia)) as (_ & Hrq).
  unfold ASAN_CEIL in *. lia.
Qed.
Lemma bx_post_hblks_x : forall cx ly' S' (W' : world segs) mem' md' T c O mx no cap out rest,
  ARx ly' S' [] W' mem' md' ->
  ra_rel B fr_RG ly' S' W' mem' T [] ->
  aout_at B fr_RG ly' S' W' mem' c O mx no cap out ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (T, ATABLE) :: aout_blks cap out ++ rest) ->
  List.NoDup (input_blks cx ++ fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S').
Proof.
  intros cx ly' S' W' mem' md' T c O mx no cap out rest HAR HRA HOUT HP.
  pose proof (Permutation_NoDup HP (bx_nodup_ablocks_x ly' S' W' mem' md' HAR)) as HND.
  assert (HSRC : rdword (aview segs (w_H W') mem') (rg_src fr_RG) = Some T /\
                 (T <> 0 -> In (T, ATABLE) (ablocks B ly' S'))).
  { destruct HRA as [(HT0 & _ & (Hv & _)) | HRL].
    - rewrite HT0 in *. split; [apply (rdword_of_val_mem segs (w_H W') mem'); [exact Hv | lia]
                               | intros H0; exfalso; exact (H0 eq_refl)].
    - pose proof HRL as (Hv & _ & _ & _ & _ & _ & _ & Hin & _).
      destruct (bx_blk_rng_x ly' S' W' mem' md' T ATABLE HAR Hin) as (HT & _).
      split; [apply (rdword_of_val_mem segs (w_H W') mem'); [exact Hv | lia] | intros _; exact Hin]. }
  destruct HSRC as (HSRCr & HSRCin).
  pose proof HOUT as (_ & _ & _ & _ & Hcapv & _ & Houtv & _).
  assert (HCASE : (cap = 0 /\ out = 0) \/ (0 < cap /\ In (out, cap) (ablocks B ly' S'))).
  { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & Hc).
    destruct Hc as [(H1 & H2 & _) | (H1 & _ & H2 & _)]; [left; split; assumption | right; split; assumption]. }
  assert (HOUTr : rdword (aview segs (w_H W') mem') (rg_out fr_RG) = Some out /\
                  rdword (aview segs (w_H W') mem') (rg_capout fr_RG) = Some cap).
  { destruct HCASE as [(Hc0 & Ho0) | (Hc & Hin)].
    - rewrite Hc0, Ho0 in *.
      split; apply (rdword_of_val_mem segs (w_H W') mem'); solve [exact Houtv | exact Hcapv | lia].
    - destruct (bx_blk_rng_x ly' S' W' mem' md' out cap HAR Hin) as (Ho & Hcp).
      split; apply (rdword_of_val_mem segs (w_H W') mem'); solve [exact Houtv | exact Hcapv | lia]. }
  destruct HOUTr as (HOr & HCr).
  assert (EH : fr_hblks W' mem' = (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out).
  (* fr_hblks reads through _cut.v's segs (tfibsegs); this file's segs is the kit's name for the same segments *)
  { unfold fr_hblks, aout_blks. cbv zeta. change tfibsegs with segs. rewrite HSRCr, HOr, HCr. reflexivity. }
  rewrite EH. split.
  - destruct (Z.eqb_spec T 0) as [HT0 | HT0]; cbn [app].
    + rewrite HT0 in HND.
      exact (bx_nodup_mid_x (input_blks cx) (0, ATABLE) _
               (bx_nodup_cut_x (input_blks cx) (0, ATABLE) (aout_blks cap out) rest HND)).
    + exact (bx_nodup_cut_x (input_blks cx) (T, ATABLE) (aout_blks cap out) rest HND).
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [destruct Hb|].
      destruct Hb as [<- | []]. exact (HSRCin HT0).
    + unfold aout_blks in Hb. destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; cbn [In] in Hb; [destruct Hb|].
      destruct Hb as [<- | []]. destruct HCASE as [(H1 & _) | (_ & Hin)]; [lia | exact Hin].
Qed.

(* ------------------------------------------------------------------ the block's end state, and the contract's post
   (the donor's :7647-7686) *)
Definition lx_end_state_x (cx : lfcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k',
    c' = cfg_at segs RA_LLVMF regs' mem' md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' S' [] W' mem' md' k' /\
    fr_live_post (c_S cx) S' k' /\ NP S' /\
    aregs_preserved (c_regs cx) regs' /\ getr regs' 10 = w64 0 /\
    fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' S' W' mem' /\
    fr_gi B G_fr ly' S' W' mem' /\
    rom_view segs W' mem' /\
    (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds (c_md cx)) fd) /\
    m_fs md' = m_fs (c_md cx) /\
    asink_none segs tfib_K (mrestrict (w_H W') mem') md' /\
    ameta_inv segs tfib_K ly' (mrestrict (w_H W') mem') (c_M cx) /\
    mo_le MT (c_S cx) S' (XN_LIB (c_n cx)) /\
    (forall i, 0 <= i < c_n cx ->
       aview segs (w_H W') mem' (c_p cx + i) = aview segs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) /\
    (* the cut's HB post clause (fr_lib_post_cf_x's HB conjunct), with the input block kept in the NoDup *)
    (List.NoDup (input_blks cx ++ fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')) /\
    (* the post's XCNT and CAPOUT clauses (_cut_x.v fr_lib_post_cf_x's last two), from LS_exit_cnt / LS_exit_cap *)
    (exists T0 c O mx cap out, ra_rel B fr_RG ly' S' W' mem' T0 [] /\
      aout_at B fr_RG ly' S' W' mem' c O mx (Z.of_nat (length O)) cap out /\
      ReplyCnt.xcnt_ok B S' ly' (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)]) T0 cap out) /\
    (exists c, val_mem segs (arm W' mem') (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
Lemma lx_post_of_end_x : forall cx W' c',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> lx_end_state_x cx W' c' ->
  lf_post_x B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx cx [] W' c'.
Proof.
  intros cx W' c' HB (ly' & S' & regs' & mem' & md' & k' & -> & HJ & HLV & HNP & HPRES & HA0 & HSV & HGI & HROM & HFD &
    HFS & HSK & HMI & HMO & HIN & HBL & HXC & HCO).
  (* HBL is the cut's HB post clause with the input block kept; the post's last conjunct drops it *)
  destruct HB as (_ & HPRE).
  unfold lf_post_x. exists ly', S', [], regs', mem', md', k'.
  split; [reflexivity|].
  unfold fr_lib_post_cf_x.
  split; [exact HJ|]. split; [exact HLV|]. split; [exact HNP|]. split; [exact HPRES|]. split; [exact HA0|].
  split; [exact HSV|]. split; [exact HGI|]. split; [exact HROM|]. split; [exact HFD|].
  split; [exact HFS|]. split; [reflexivity|]. split; [reflexivity|].
  assert (HFSS : Fs.fs_sorted (m_fs (c_md cx)) = true) by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  split; [cbn [ll_fs]; exact HFSS|].
  split; [exact HSK|]. split; [exact HMI|]. split; [exact HMO|]. split; [exact HIN|].
  split; [split; [exact (List.NoDup_app_remove_l _ _ (proj1 HBL)) | exact (proj2 HBL)]|].
  split; [exact HXC | exact HCO].
Qed.

(* ================================================================== the spine (the donor's :7688-8157) *)
Lemma lx_base_facts_x : forall cx, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  frames (c_S cx) = [] /\ raZ (c_regs cx) = RA_LLVMF /\
  getr (c_regs cx) 3 = w64 (as_gp B) /\ getr (c_regs cx) 4 = w64 (as_tp B) /\
  c_n cx = Z.of_nat (length (c_pl cx)) /\
  garr8 segs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  asink_none segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_md cx) /\
  ameta_inv segs tfib_K (c_ly cx) (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_M cx).
Proof.
  intros cx (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE.
  destruct HPRE as (HPz0 & Hra & _ & _ & _ & Hlen & Hpl & Hfr & _ & _ & _ & _ & _ & _ & Hsink & _ & _ & Hmeta & _).
  pose proof HPz0 as (_ & _ & _ & Hgp & Htp & _).
  split; [exact Hfr|]. split; [exact Hra|]. split; [exact Hgp|]. split; [exact Htp|].
  split; [exact Hlen|]. split; [exact Hpl|]. split; [exact Hsink | exact Hmeta].
Qed.

(* check_shape_ends only drops held records, so the source_resets after it cost no more than at X *)
Lemma lx_sr_total_evo_x : forall hs hs', (forall j, (j < 4)%nat -> lx_slot_evo (nth j hs None) (nth j hs' None)) ->
  lx_sr_total MT hs' <= lx_sr_total MT hs.
Proof.
  intros hs hs' HE. pose proof (mo_free_nonneg MT MLM) as Hf.
  assert (K : forall j, (j < 4)%nat -> sr_cost MT (nth j hs' None) <= sr_cost MT (nth j hs None)).
  { intros j Hj. destruct (HE j Hj) as [-> | (h & H' & -> & -> & Hn)]; [lia|].
    unfold CheckRep.set_held. cbn [sr_cost hs_pending hs_expected hs_held]. unfold lf_cost. nia. }
  unfold lx_sr_total.
  pose proof (K 0%nat ltac:(lia)). pose proof (K 1%nat ltac:(lia)). pose proof (K 2%nat ltac:(lia)).
  pose proof (K 3%nat ltac:(lia)). lia.
Qed.

Lemma lx_pairwise_cross_x : forall {X : Type} (R : X -> X -> Prop) l1 l2 x y,
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y HP Hx Hy; [destruct Hx|].
  cbn in HP. destruct HP as [HF HP]. destruct Hx as [<- | Hx].
  - rewrite Forall_forall in HF. apply HF. apply in_or_app. right. exact Hy.
  - exact (IH l2 x y HP Hx Hy).
Qed.
(* the addresses of the globals the end state reads (lib/B/W_rep.v fr_globals_b; the cut's AG_THREAD_UP /
   AG_LISTEN); all lie in B's image range [0x10000, 0x5fc000) (lib/B/W_img.v fr_img_range).  Stated as equations so
   each use is one small lia. *)
Lemma lx_glob_lits_x :
  rg_src fr_RG = 0x5d8d40 /\ rg_nsrc fr_RG = 0x5d8d20 /\ rg_capsrc fr_RG = 0x5d8d80 /\
  rg_send_max fr_RG = 0x5d8dc0 /\ rg_nout fr_RG = 0x5d8e40 /\ rg_capout fr_RG = 0x5d90a0 /\ rg_out fr_RG = 0x5d90c0 /\
  rg_client fr_RG = 0xa2560 /\ rg_client_broken fr_RG = 0x5d8d60 /\ rg_send_dead fr_RG = 0x5d8e00 /\
  rg_send_eintr fr_RG = 0x5d8e20 /\ rg_gone fr_RG = 0x5d8de0 /\ rg_lock fr_RG = 0x5d9040 /\ rg_wake fr_RG = 0xa2520 /\
  rg_s fr_RG = 0x5d8e60 /\ AG_THREAD_UP = 0x5d8ce0 /\ AG_LISTEN = 0xa2540 /\ ASRC = 96.
Proof. vm_compute. repeat split. Qed.
Lemma lx_errno_rng_x : forall a, as_errno B <= a < as_errno B + 4 -> 0x10000 <= a < 0x5fc000.
Proof.
  intros a Ha. apply fr_img_range.
  assert (Hs : inG (G_SL B fr_RG) a).
  { unfold G_SL, inG. apply Exists_exists. exists (as_errno B, 4).
    split; [right; right; right; right; right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia]. }
  exact (proj1 (HG a (HG_SL a Hs))).
Qed.
Lemma lx_rom_rng_x : forall a, in_rom segs a -> 0x10000 <= a < 0x5fc000.
Proof.
  intros a (sg & Hsg & _ & Hr). apply fr_img_range. exists sg. split; [exact Hsg | exact Hr].
Qed.
Lemma lx_garr8_view_x : forall (W W' : world segs) mem mem' p l i,
  garr8 segs (mrestrict (w_H W) mem) p l -> garr8 segs (mrestrict (w_H W') mem') p l ->
  0 <= i < Z.of_nat (length l) -> aview segs (w_H W) mem (p + i) = aview segs (w_H W') mem' (p + i).
Proof.
  intros W W' mem mem' p l i H1 H2 Hi.
  destruct (H1 (Z.to_nat i) ltac:(lia)) as (V1 & _). destruct (H2 (Z.to_nat i) ltac:(lia)) as (V2 & _).
  pose proof (V1 0%nat ltac:(lia)) as E1. pose proof (V2 0%nat ltac:(lia)) as E2.
  rewrite Z2Nat.id in E1, E2 by lia. cbn [Z.of_nat] in E1, E2. rewrite Z.add_0_r in E1, E2.
  unfold aview. rewrite E1, E2. reflexivity.
Qed.

(* ------------------------------------------------------------------ across the fake frame's release
   lx_ffexit keeps every byte outside the fake frame, its 16 shadow bytes and the flag byte, and the readable memory
   only grows; the image's globals and the live heap blocks are outside all three (AR: frames and flags are not
   image bytes, blocks and frames are disjoint, a block is application memory and not owned, the flag is owned). *)
Lemma lx_ff_kept_x : forall cx ly S (W : world segs) mem md k fpos (W' : world segs) mem',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128) ->
     ~ (SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16) ->
     ~ (flag_addr ly 1 fpos <= a < flag_addr ly 1 fpos + 1) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') ->
  forall a, (0x10000 <= a < 0x5fc000 \/ exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros cx ly S W mem md k fpos W' mem' HB HJ HKV HGR a Hwh.
  assert (HAR : ARx ly S [] W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (HFS : frames S = [(1, fpos)]).
  { pose proof HJ as (_ & _ & (memS & HJa & _) & _). pose proof HJa as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. destruct (lx_base_facts_x cx HB) as (Hf0 & _). rewrite Hf0. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames S)) by (rewrite HFS; left; reflexivity).
  assert (H128 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
  destruct (IMGC ly S [] W mem md HAR) as [C1 C2].
  destruct (alx_frames _ _ ARx LAWS ly S [] W mem md 1 fpos HAR Hin1) as (HF32 & HFapp & _ & _).
  rewrite H128 in HFapp.
  destruct (FFL ly S [] W mem md 1 fpos HAR Hin1) as (_ & HFLo & _ & _).
  pose proof (Z.div_mod (frame_addr ly 1 fpos) 8 ltac:(lia)) as HD8.
  pose proof (Z.mod_pos_bound (frame_addr ly 1 fpos) 8 ltac:(lia)) as HM8.
  pose proof ASAN_CEIL_range as (CR & _).
  unfold in_app in HFapp. change kLowShadowBeg with 2147446784 in HFapp. change kHighMemBeg with 17594333495296 in HFapp.
  assert (HBK : forall p n, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
    4096 <= p /\ (p + req_size n <= 2147446784 \/ (17594333495296 <= p /\ p + req_size n <= ASAN_CEIL)) /\
    ~ aowned B ly S a /\ zdisjoint (p, req_size n) (frame_addr ly 1 fpos, 128)).
  { intros p n Hin Hr.
    destruct (alx_blocks _ _ ARx LAWS ly S [] W mem md p n HAR Hin) as (_ & _ & _ & Happ & Hown & _).
    unfold in_app in Happ. change kLowShadowBeg with 2147446784 in Happ. change kHighMemBeg with 17594333495296 in Happ.
    split; [lia|]. split; [lia|]. split; [exact (proj2 (Hown a Hr))|].
    destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _].
    rewrite <- H128. apply (lx_pairwise_cross zdisjoint _ _ _ _ Hp).
    - apply in_map_iff. exists (p, n). split; [reflexivity | exact Hin].
    - apply in_map_iff. exists (1, fpos). split; [reflexivity | exact Hin1]. }
  assert (Ha64 : 0 <= a < 2 ^ 64).
  { destruct Hwh as [Hw | (p & n & Hin & Hr)]; [lia|]. destruct (HBK p n Hin Hr) as (H4 & Hap & _). lia. }
  split.
  - apply HKV; [exact Ha64| | |].
    + intros HinF. destruct Hwh as [Hw | (p & n & Hin & Hr)].
      * assert (HinF' : frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + fs_frame_bytes 1) by (rewrite H128; exact HinF).
        destruct (alx_client_img _ _ ARx LAWS ly S [] W mem md a HAR
          (or_intror (or_introl (ex_intro _ 1 (ex_intro _ fpos (conj Hin1 HinF')))))) as [Hnz _].
        apply Hnz. unfold in_zr. lia.
      * destruct (HBK p n Hin Hr) as (_ & _ & _ & Hz). unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
    + intros HinS. unfold SB in HinS. destruct Hwh as [Hw | (p & n & Hin & Hr)]; [lia|].
      destruct (HBK p n Hin Hr) as (H4 & Hap & _). lia.
    + intros HinFl. assert (Ea : a = flag_addr ly 1 fpos) by lia. destruct Hwh as [Hw | (p & n & Hin & Hr)].
      * destruct (alx_client_img _ _ ARx LAWS ly S [] W mem md a HAR
          (or_intror (or_intror (ex_intro _ 1 (ex_intro _ fpos (conj Hin1 Ea)))))) as [Hnz _].
        apply Hnz. unfold in_zr. lia.
      * destruct (HBK p n Hin Hr) as (_ & _ & Hno & _). apply Hno. rewrite Ea. exact HFLo.
  - intros Hw. unfold arm in *. exact (writable_at_grows segs _ _ a HGR Hw).
Qed.

(* the four md-level clauses of the post, off the journal from the entry (FP_SINK: no sink in its footprint) *)
Lemma lx_end_md_x : forall cx ly' S' (W' : world segs) mem' md' k',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' S' [] W' mem' md' k' ->
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds (c_md cx)) fd) /\
  m_fs md' = m_fs (c_md cx) /\
  asink_none segs tfib_K (mrestrict (w_H W') mem') md' /\
  ameta_inv segs tfib_K ly' (mrestrict (w_H W') mem') (c_M cx).
Proof.
  intros cx ly' S' W' mem' md' k' HB HJ.
  pose proof (FP_SINK cx [] HB) as HFP.
  destruct (lx_base_facts_x cx HB) as (_ & _ & _ & _ & _ & _ & HSK0 & HMI0).
  destruct (ajournal_gx_inner_x segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ) as (memS & HJa & HmS).
  pose proof HJa as (_ & _ & _ & _ & Hio & _).
  destruct Hio as (_ & _ & _ & _ & _ & _ & Hcl).
  destruct (Hcl HFP) as (Efd & Efs & _).
  assert (MS : forall a, 0 <= a < 2 ^ 64 -> ~ inG G_fr a ->
    mbyte segs (mrestrict (w_H (c_W cx)) memS) a = mbyte segs (mrestrict (w_H (c_W cx)) (c_mem cx)) a).
  { intros a Ha Hg. apply mbyte_of_aview. apply HmS. rewrite unsigned_lit_small by lia. exact Hg. }
  split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
  split; [unfold m_fs; rewrite Efs; reflexivity|].
  split.
  - eapply (YE01_x.asink_none_kept_x segs B PST ARx tfib_K AIL);
      [exact HJa | intros a Ha; apply HPST; exact (proj1 (ail_env _ _ _ AIL a Ha)) | exact HFP |].
    apply (asink_none_frame segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx))); [|exact HSK0].
    intros a Ha. destruct (HG_K a (or_introl Ha)) as (Hr & Hg). exact (MS a Hr Hg).
  - eapply (YE01_x.ameta_inv_kept_x segs B PST ARx LAWS tfib_K AIL);
      [exact HJa | intros a Ha; apply HPST; exact (proj1 (ail_meta _ _ _ AIL a Ha)) |].
    destruct HMI0 as (HX & HIM & HOK). split; [exact HX|]. split; [exact HIM|].
    apply (ameta_ok_frame segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx))); [|exact HOK].
    intros a [Ha | [Ha | Ha]].
    + destruct (HG_K a (or_intror (or_introl Ha))) as (Hr & Hg). exact (MS a Hr Hg).
    + destruct (HG_K a (or_intror (or_intror Ha))) as (Hr & Hg). exact (MS a Hr Hg).
    + pose proof HOK as (_ & _ & HM0 & HM47 & _). apply MS; [lia|]. intros Hg.
      pose proof (HIM a (proj1 (HG a Hg))). lia.
Qed.

(* the end state from the reset's post and the release's post *)
Lemma lx_end_of_ffexit_x : forall cx t m0 ly0 S0 rest C m ev ly2 S2 (W2 : world segs) mem2 md2 k2 fpos
    (W3 : world segs) regs3 mem3 md3,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  LSx cx t m0 ly0 S0 ->
  Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m0 ++ rest) ->
  mo_le MT S0 S2 C -> C <= lx_exit_cost MT m0 ->
  lm_G m = lm_G m0 -> lm_es m = [] ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 [] W2 mem2 md2 k2 ->
  amodel_at B ly2 S2 W2 mem2 (lx_reset_model m ev) ->
  ainput_at B cx ly2 S2 W2 mem2 ->
  Permutation (ablocks B ly2 S2) (input_blks cx ++ model_blks (lx_reset_model m ev) ++ rest) ->
  rom_view segs W2 mem2 ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly2 (stack_free_state 1 fpos S2) [] W3 mem3 md3 k2 ->
  aregs_preserved (c_regs cx) regs3 -> getr regs3 10 = w64 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr ly2 1 fpos <= a < frame_addr ly2 1 fpos + 128) ->
     ~ (SB + frame_addr ly2 1 fpos / 8 <= a < SB + frame_addr ly2 1 fpos / 8 + 16) ->
     ~ (flag_addr ly2 1 fpos <= a < flag_addr ly2 1 fpos + 1) ->
     aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a) ->
  mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W3) mem3) ->
  (* relay_finish's final capacity, from lx_rf_post_site_x through lx_ends_post_x: the cap LS_exit_end is taken at *)
  lm_cap m = gse_cap (lx_rf_run (lm_c m0) [] (lm_mx m0) 0 (lm_cap m0) (lm_es m0)) ->
  (* LS_exit_cap's RINV and lregs_X's t bound at X; the room thread's NP at the reset's state; LS_exit_end's last
     premise, X's non-empty key texts (KF-COUNT F8) *)
  RINV cx t m0 -> 0 <= t <= OPS_MAX -> NP S2 ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m0) ->
  lx_end_state_x cx W3 (cfg_at segs RA_LLVMF regs3 mem3 md3).
Proof.
  intros cx t m0 ly0 S0 rest C m ev ly2 S2 W2 mem2 md2 k2 fpos W3 regs3 mem3 md3
    HB HLS HPm0 HMO HC EG Ees HJ2 HM2 HIN2 HP2 HROM2 HJ3 HPRES HA0 HKV HGR Hcap HRI Ht HNP2 HK0.
  assert (HFS2 : frames S2 = [(1, fpos)]).
  { pose proof HJ2 as (_ & _ & (memS & HJa & _) & _). pose proof HJa as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. destruct (lx_base_facts_x cx HB) as (Hf0 & _). rewrite Hf0. reflexivity. }
  pose proof (lx_ff_kept_x cx ly2 S2 W2 mem2 md2 k2 fpos W3 mem3 HB HJ2 HKV HGR) as KEEP.
  assert (EB : ablocks B ly2 (stack_free_state 1 fpos S2) = ablocks B ly2 S2) by reflexivity.
  assert (EM : model_blks (lx_reset_model m ev) = (lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)).
  { unfold model_blks, lx_reset_model. cbn [lm_G lm_es lm_hs lm_cap lm_out]. rewrite Ees, EG. reflexivity. }
  (* HFH at the reset's state: fr_hb_of_model at the reset's model (image A's lx_end_of_ffexit_x) *)
  assert (HAR2 : ARx ly2 S2 [] W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJ2).
  assert (HFH2 : fr_hblks W2 mem2 = (lm_G (lx_reset_model m ev), ATABLE) ::
      aout_blks (lm_cap (lx_reset_model m ev)) (lm_out (lx_reset_model m ev))).
  { refine (proj1 (fr_hb_of_model B cx (lx_reset_model m ev) ly2 S2 W2 mem2 rest _
      (bx_nodup_ablocks_x ly2 S2 W2 mem2 md2 HAR2) HM2 HP2)).
    intros p n Hin. destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR2 Hin) as (_ & H1 & H2 & _). lia. }
  cbn [lx_reset_model lm_G lm_cap lm_out] in HFH2. rewrite EG in HFH2.
  rewrite EM in HP2.
  assert (INB : forall b, In b ((lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)) -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
  assert (KI : forall x, 0x10000 <= x < 0x5fc000 -> abyte_kept W2 mem2 W3 mem3 x)
    by (intros x Hx; exact (KEEP x (or_introl Hx))).
  pose proof lx_glob_lits_x as LITS.
  assert (HFH : fr_hblks W3 mem3 = (lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)).
  { rewrite (fr_hblks_kept W2 W3 mem2 mem3); [exact HFH2|].
    intros a Ha. pose proof LITS as (L1 & _ & _ & _ & _ & L6 & L7 & _). rewrite L1, L6, L7 in Ha.
    exact (proj1 (KI a ltac:(lia))). }
  destruct (LS_exit_end cx t m0 ly0 S0 rest ly2 S2 W3 mem3 md3 fpos k2 C (lm_cap m) (lm_out m) HLS HPm0 HP2 HFS2 HMO HC
    HJ3 Hcap Ht HFH (bx_nodup_ablocks_x ly2 S2 W2 mem2 md2 HAR2) HK0) as (HLV & HSV & HMOE).
  (* NP at the return: the room thread's NP through the release (rp_RM survives stack_free_state) *)
  assert (HNP : NP (stack_free_state 1 fpos S2))
    by exact (proj1 (RP_NP _ 0%nat) (RPF_stack_free RP S2 1 fpos 0%nat (proj2 (RP_NP S2 0%nat) HNP2))).
  destruct (lx_end_md_x cx ly2 (stack_free_state 1 fpos S2) W3 mem3 md3 k2 HB HJ3) as (HFD & HFSY & HSK & HMI).
  pose proof HM2 as (_ & HSL & HRL & HOUT & HGN & HLK & HWK & _ & _ & _ & HTU & HLST & HLW).
  cbn [lx_reset_model lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn] in HSL, HRL, HOUT, HGN.
  assert (HAR3 : ARx ly2 (stack_free_state 1 fpos S2) [] W3 mem3 md3)
    by (eapply ajournal_gx_AR_x; exact HJ3).
  (* the relay's table and the controller's buffer at the END state, named once: fr_gi uses them, and so does the
     cut's coming last conjunct *)
  assert (HRL3 : arelay_at B fr_RG ly2 (stack_free_state 1 fpos S2) W3 mem3 (lm_G m) []).
  { rewrite Ees in HRL.
    apply (arelay_at_kept B fr_RG ly2 S2 W2 mem2 ly2 _ W3 mem3 (lm_G m) [] HRL).
    - intros r Hr x Hx. unfold arelay_fp in Hr. cbn [map concat app] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hx; [apply KI; lia | apply KI; lia | apply KI; lia|].
      apply KEEP. right. exists (lm_G m), ATABLE. split; [apply INB; left; rewrite EG; reflexivity|].
      change (req_size ATABLE) with 896. change ATABLE with 896 in Hx. lia.
    - intros b Hb. rewrite EB. cbn in Hb. destruct Hb as [<- | []]. apply INB. left. rewrite EG. reflexivity. }
  eassert (HOUT3 : aout_at B fr_RG ly2 (stack_free_state 1 fpos S2) W3 mem3 _ _ _ _ (lm_cap m) (lm_out m)).
  { apply (aout_at_kept B fr_RG ly2 S2 W2 mem2 ly2 _ W3 mem3 _ _ _ _ _ _ HOUT).
    - intros r Hr x Hx. unfold aout_fp in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Hx.
      1-8: (apply KI; lia).
      + apply KI. apply lx_errno_rng_x. lia.
      + revert Hr. destruct (Z.eqb_spec (lm_cap m) 0) as [Hc0 | Hc0]; intros Hr; [destruct Hr|].
        destruct Hr as [<- | []]. cbn [fst snd] in Hx. apply KEEP. right. exists (lm_out m), (lm_cap m).
        split; [apply INB; right; unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ 0) Hc0); left; reflexivity|].
        unfold req_size. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). lia.
    - intros b Hb. rewrite EB. apply INB. right. exact Hb. }
  (* XCNT at the return: LS_exit_cnt at the reset's blocks (stack_free_state keeps ablocks) *)
  assert (H4096 : forall p n, In (p, n) (ablocks B ly2 S2) -> 4096 <= p).
  { intros p n Hin. destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR2 Hin) as (_ & H4 & _). exact H4. }
  pose proof (LS_exit_cnt cx t m0 ly0 S0 rest ly2 S2 (lm_cap m) (lm_out m) HLS HPm0 HP2 H4096) as HXP.
  assert (HXC : ReplyCnt.xcnt_ok B (stack_free_state 1 fpos S2) ly2 (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)])
    (lm_G m) (lm_cap m) (lm_out m)).
  { rewrite EG. unfold ReplyCnt.xcnt_ok in HXP |- *. rewrite EB. exact HXP. }
  (* CAPOUT at the return: g_capout is relay_finish's final capacity, under CAPOUT_MAX by LS_exit_cap *)
  pose proof (LS_exit_cap cx t m0 ly0 S0 HLS HRI Ht) as HCAP.
  exists ly2, (stack_free_state 1 fpos S2), regs3, mem3, md3, k2.
  split; [reflexivity|]. split; [exact HJ3|]. split; [exact HLV|]. split; [exact HNP|]. split; [exact HPRES|].
  split; [exact HA0|]. split; [exact HSV|].
  split.
  { unfold fr_gi.
    split; [intros a Ha; exact (GWR (w_H W3) mem3 a Ha)|].
    split.
    { intros i Hi. specialize (HSL i Hi).
      assert (Enth : nth i [None; None; None; None] (@None hsrc) = None)
        by (do 4 (destruct i as [|i]; [reflexivity|]); lia).
      rewrite Enth in HSL. destruct HSL as (HZ & HWr).
      assert (KS : forall x, rg_s fr_RG + ASRC * Z.of_nat i <= x < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
        abyte_kept W2 mem2 W3 mem3 x) by (intros x Hx; apply KI; lia).
      split.
      - apply (akept_garr8 W2 mem2); [|exact HZ]. intros x Hx. apply KS.
        rewrite repeat_length, Z2Nat.id in Hx by lia. lia.
      - apply (akept_awr W2 mem2); [|exact HWr]. exact KS. }
    split.
    { exists (lm_G m). right. exact HRL3. }
    split.
    { eexists _, _, _, _, _. exact HOUT3. }
    split.
    { eexists. apply (agone_at_kept fr_RG W2 mem2 W3 mem3 _ HGN).
      intros r [<- | []] x Hx. apply KI. cbn [fst snd] in Hx. lia. }
    split.
    { apply (alock_at_kept fr_RG W2 mem2 W3 mem3 _ HLK). intros r [<- | []] x Hx. apply KI. cbn [fst snd] in Hx. lia. }
    split.
    { apply (awake_at_kept fr_RG W2 mem2 W3 mem3 HWK). intros r [<- | []] x Hx. apply KI. cbn [fst snd] in Hx. lia. }
    split.
    { apply (akept_vm W2 mem2 W3 mem3 AG_THREAD_UP 1%nat 0); [intros x Hx; apply KI; lia | exact HTU]. }
    split.
    { destruct HLST as (lst & Hl). exists lst.
      apply (akept_vm W2 mem2 W3 mem3 AG_LISTEN 4%nat lst); [intros x Hx; apply KI; lia | exact Hl]. }
    pose proof (akept_awr W2 mem2 W3 mem3 AG_LISTEN 4 ltac:(intros x Hx; apply KI; lia) HLW) as HLW3.
    intros i Hi. exact (HLW3 i Hi). }
  split.
  { intros a Ha. rewrite (proj1 (KEEP a (or_introl (lx_rom_rng_x a Ha)))). exact (HROM2 a Ha). }
  split; [exact HFD|]. split; [exact HFSY|]. split; [exact HSK|]. split; [exact HMI|]. split; [exact HMOE|].
  split.
  { intros i Hi.
    destruct (lx_base_facts_x cx HB) as (_ & _ & _ & _ & Hlen & Hpl0 & _).
    destruct HIN2 as ([[Hn0 _] | [Hnr HinB]] & Hg2); [lia|].
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
    assert (Hri : c_p cx <= c_p cx + i < c_p cx + req_size (c_n cx)) by lia.
    rewrite (proj1 (KEEP (c_p cx + i) (or_intror (ex_intro _ (c_p cx) (ex_intro _ (c_n cx) (conj HinB Hri)))))).
    apply (lx_garr8_view_x W2 (c_W cx) mem2 (c_mem cx) (c_p cx) _ i Hg2 Hpl0).
    rewrite length_map. lia. }
  (* the cut's HB post clause, from the model's blocks and ablocks_sep's Permutation *)
  split.
  { refine (bx_post_hblks_x cx ly2 (stack_free_state 1 fpos S2) W3 mem3 md3 (lm_G m) _ _ _ _ (lm_cap m) (lm_out m) rest
      HAR3 (or_intror HRL3) HOUT3 _).
    rewrite EB, EG. exact HP2. }
  (* the post's XCNT and CAPOUT clauses (image A's lx_end_of_ffexit_x): the table and g_out at the return with
     LS_exit_cnt's count, and g_capout's bound *)
  split.
  - exists (lm_G m). eexists _, _, _. exists (lm_cap m), (lm_out m).
    split; [right; exact HRL3|]. split; [exact HOUT3 | exact HXC].
  - exists (lm_cap m).
    pose proof HOUT3 as (_ & _ & _ & _ & Hcv & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & Hcd).
    split; [exact Hcv|]. split; [destruct Hcd as [(Hc0 & _) | (Hp & _)]; lia|]. rewrite Hcap. exact HCAP.
Qed.

(* ---- the spine over the five block statements (lib/B/W_bx_defs.v), each proved in its own file ---- *)
Section spine.
Hypothesis LXO : lx_order_S_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx.
Hypothesis LXRF : lx_rf_site_S_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LSx RP.
Hypothesis LXE : lx_ends_S_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx RP.
Hypothesis LXR : lx_reset_S_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx RP.
Hypothesis LXF : lx_ffexit_S_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx.

(* from 0x84fe8 (check_shape_done(at)) to the return: lx_reset, lx_ffexit, the end state *)
Lemma lx_tail_x : forall cx t m0 ly0 S0 rest C m A ly S (W : world segs) regs mem md k fpos,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  LSx cx t m0 ly0 S0 ->
  Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m0 ++ rest) ->
  mo_le MT S0 S C -> C + lx_sr_total MT (lm_hs m) <= lx_exit_cost MT m0 ->
  mo_ok MT S (lx_sr_total MT (lm_hs m)) ->
  lm_G m = lm_G m0 -> lm_es m = [] ->
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md k ->
  bx_frame cx (frame_addr ly 1 fpos) W mem ->
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) ->
  amodel_at B ly S W mem m ->
  ablocks_sep B fr_FP cx m ly S ->
  ainput_at B cx ly S W mem ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 A -> 0 <= A < 2 ^ 64 ->
  val_mem segs (arm W mem) (VAL A_g_nout) 8 A ->
  rom_view segs W mem ->
  (* relay_finish's final capacity (lx_end_of_ffexit_x's last premise) *)
  lm_cap m = gse_cap (lx_rf_run (lm_c m0) [] (lm_mx m0) 0 (lm_cap m0) (lm_es m0)) ->
  (* LS_exit_cap's RINV and t bound at X; the room thread's NP and count at the reset's start *)
  RINV cx t m0 -> 0 <= t <= OPS_MAX -> NP S -> cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly S) ->
  (* X's non-empty key texts (lx_end_of_ffexit_x's last premise, KF-COUNT F8) *)
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m0) ->
  SRr segs W (cfg_at segs (BASE + AX_done) regs mem md)
    (lf_post_x B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx cx []).
Proof.
  intros cx t m0 ly0 S0 rest C m A ly S W regs mem md k fpos HB HLS HPm0 HMO HC HOK EG Ees HPm r2 r9 r8 r3 r4
    HJ HFR HFL HM HSEP HIN HAT HA HNO HROM Hcap HRI Ht HNPs HCNs HK0.
  eapply SRr_bind; [exact (LXR cx m A fpos ly S W regs mem md k HB r2 r9 r8 r3 r4 HJ HFR HFL HM HSEP HIN HOK HAT HA HNO HROM
    HNPs HCNs)|].
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k2 & ev & -> & HJ2 & q2 & q9 & q8 & q20 & q24 & q3 & q4 &
    HFR2 & HFL2 & HM2 & HSEP2 & HIN2 & HR2 & HROM2 & Hfa2 & HMO2 & HNP2 & HCN2).
  assert (HFR2' : bx_frame cx (frame_addr ly2 1 fpos) W2 mem2) by (rewrite Hfa2; exact HFR2).
  assert (HFL2' : sv8 W2 mem2 (frame_addr ly2 1 fpos + 120) (flag_addr ly2 1 fpos)).
  { rewrite Hfa2, (lx_fla_kept_x HJ2). rewrite (lx_fla_kept_x HJ) in HFL2. exact HFL2. }
  destruct (lx_base_facts_x cx HB) as (_ & Hra & Hgp & Htp & _).
  eapply SRr_mono.
  { apply (LXF cx W2 regs2 mem2 md2 ly2 S2 k2 fpos (frame_addr ly2 1 fpos) HB eq_refl HJ2 HFR2' HFL2').
    - rewrite q8. unfold spZ. symmetry. apply lit_of_word.
    - exact q9.
    - rewrite Hfa2. exact q20.
    - rewrite Hfa2. exact q24.
    - rewrite q3, Hgp. reflexivity.
    - rewrite q4, Htp. reflexivity.
    - unfold raZ in Hra. rewrite <- Hra. symmetry. apply lit_of_word. }
  intros W3 c3 _ (regs3 & mem3 & md3 & -> & HJ3 & HPRES & HA0 & HKV & HGR).
  apply (lx_post_of_end_x cx W3 _ HB).
  apply (lx_end_of_ffexit_x cx t m0 ly0 S0 rest (C + lx_sr_total MT (lm_hs m)) m ev ly2 S2 W2 mem2 md2 k2 fpos
    W3 regs3 mem3 md3 HB HLS HPm0); try assumption.
  - exact (mo_le_trans MT MLM _ _ _ _ _ HMO HMO2).
  - exact (HR2 rest HPm).
Qed.

(* the walk at the instance's ghost list [] *)
Lemma lx_seg_exit_nil_x : forall cx W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx [] W c ->
  SRr segs W c (lf_post_x B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx cx []).
Proof.
  intros cx W c HB (regs & mem & md & t & -> & HJT & HL).
  destruct HL as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HM & HIN & HROM & HSEP & HLS & HNP3 & HRI & HX).
  (* lregs_X's t bound (its last conjunct; B's lregs_X has nine conjuncts before it, A's ten) and LS_cnt's count at X *)
  assert (Ht : 0 <= t <= OPS_MAX) by (pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ht); exact Ht).
  pose proof (LS_cnt cx t m ly3 S3 W mem HLS HRI HM Ht) as HCNT.
  (* the cut's ghost list is [] (HP0 at its journal's end state) *)
  assert (Ehp3 : Hp3 = []) by (eapply HP0; eapply ajournal_gx_AR_x; exact HJ). subst Hp3.
  pose proof HSEP as ((rest & HPm0) & _).
  (* LS_exit_budget's two F8 premises: lregs_X's t bound and X's non-empty key texts, read off X's amodel_at (HM) *)
  pose proof (W_bx_rf_x.exit_keys_nonempty B ly3 S3 W mem m HM) as HK.
  pose proof (LS_exit_budget cx t m ly3 S3 HLS Ht HK) as HMOK.
  pose proof (lx_ends_cost_nonneg (lm_hs m)) as Hec. pose proof (lx_sr_total_nonneg (lm_hs m)) as Hsc.
  assert (HNOUT : VAL A_g_nout = rg_nout fr_RG) by (vm_compute; reflexivity).
  eapply SRr_bind; [exact (LXO cx W _ regs mem md own ly3 S3 k m fpos t HB eq_refl HJ Hown HFR HFL HM HIN HROM HX HJT)|].
  intros W1 c1 _ (-> & regs1 & mem1 & md1 & Hcase & HJ1 & HFR1 & HFL1 & HM1 & HIN1 & HROM1 & HJT1 & HAT1 & HX1).
  subst own.
  assert (Hrf : forall pcj, pcj = AX_join \/ pcj = AX_noord ->
    SRr segs W (cfg_at segs (fr_B0 + pcj) regs1 mem1 md1)
      (lx_rf_post_site_x B MT NP G_fr fr_FP PST ARx RP cx pcj m fpos ly3 S3 (getr regs1 19) W mem1))
    by (intros pcj Hp; exact (LXRF cx pcj t W regs1 mem1 md1 ly3 S3 fpos k m HB Hp HJ1 HFR1 HFL1 HM1 HIN1 HROM1 HJT1
          HSEP HLS HX1 HAT1 HNP3 HCNT)).
  destruct Hcase as [(-> & Hes0) | (-> & Hes & Hr19 & Hord)].
  - (* no relay entry: 0x84fe0 *)
    apply length_zero_iff_nil in Hes0.
    eapply SRr_bind; [exact (Hrf AX_noord (or_intror eq_refl))|].
    intros W2 c2 _ (ly4 & S4 & regs4 & mem4 & md4 & k4 & m4 & -> & HJ4 & HFR4 & HFL4 & Hfa4 & HM4 & HIN4 & HROM4 & HJT4 &
      HSEP4 & q2 & q8 & q9 & q3 & q4 & q27 & q19 & HAT4 & Hkeep4 & Ek & Ehs & EG & Ees4 & Egn & Enfd & HO0 & HOe &
      HR4 & Hfrm4 & HMO4 & Ecap4 & HNP4 & HCN4).
    replace (fr_B0 + AX_noord + 8) with (BASE + AX_done) by (rewrite BASE_B0; unfold AX_noord, AX_done; lia).
    pose proof (HO0 Hes0) as HO4.
    pose proof HM4 as (_ & _ & _ & HOUT4 & _). pose proof HOUT4 as (_ & _ & HNO4 & _).
    rewrite HO4 in HNO4. cbn [length Z.of_nat] in HNO4. rewrite <- HNOUT in HNO4.
    apply (lx_tail_x cx t m ly3 S3 rest (lx_rf_cost MT (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) m4 0 ly4 S4 W2
      regs4 mem4 md4 k4 fpos HB HLS HPm0 HMO4); try assumption.
    + unfold lx_exit_cost. rewrite Ehs. lia.
    + rewrite Ehs. apply (mo_ok_le MT MLM S4 _ (lx_ends_cost MT (lm_hs m) + lx_sr_total MT (lm_hs m))); [|lia].
      exact (mo_ok_step MT MLM S3 S4 _ _ HMOK HMO4).
    + exact (HR4 rest HPm0).
    + exact (bx_frame_of_aframe _ _ _ _ HFR4).
    + lia.
  - (* the relay's table is not empty: 0x84f00 *)
    eapply SRr_bind; [exact (Hrf AX_join (or_introl eq_refl))|].
    intros W2 c2 _ (ly4 & S4 & regs4 & mem4 & md4 & k4 & m4 & -> & HJ4 & HFR4 & HFL4 & Hfa4 & HM4 & HIN4 & HROM4 & HJT4 &
      HSEP4 & q2 & q8 & q9 & q3 & q4 & q27 & q19 & HAT4 & Hkeep4 & Ek & Ehs & EG & Ees4 & Egn & Enfd & HO0 & HOe &
      HR4 & Hfrm4 & HMO4 & Ecap4 & HNP4 & HCN4).
    replace (fr_B0 + AX_join + 8) with (BASE + AX_after_rf) by (rewrite BASE_B0; unfold AX_join, AX_after_rf; lia).
    (* RI_exit_ends' last two premises, read off X's amodel_at (HM): agone_at's 0 / 1, the held lists' NUL-free texts *)
    assert (Hgn01 : 0 <= lm_gn m <= 1)
      by (pose proof HM as (_ & _ & _ & _ & (_ & _ & Hg) & _); clear - Hg; destruct Hg as [Hg|Hg]; lia).
    assert (Hnul : forall i h, nth i (lm_hs m) None = Some h ->
      Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))).
    { intros i h Eh. pose proof HM as (Hl4 & HSL & _).
      destruct (Nat.lt_ge_cases i 4) as [Hi | Hi]; [|rewrite nth_overflow in Eh by (clear - Hl4 Hi; lia); discriminate Eh].
      pose proof (HSL i Hi) as X. rewrite Eh in X. cbn [aslot] in X.
      destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        (_ & _ & _ & _ & _ & _ & _ & _ & Hrecs) & _).
      eapply Forall_impl; [|exact Hrecs]. intros r (_ & _ & Hl & _). exact (proj1 (Hl eq_refl)). }
    pose proof (RI_exit_ends cx t m HRI Hes Hgn01 Hnul) as Hrun. unfold lx_rf_O in Hrun.
    pose proof (mo_ok_step MT MLM S3 S4 _ _ HMOK HMO4) as HMOK4.
    eapply SRr_bind.
    { apply (LXE cx t fpos ly4 S4 m4 (lx_norder m) (lx_ord m) regs4 mem4 md4 W2 k4 HJ4 HFR4 HFL4 HM4 HIN4 HROM4 HJT4 HSEP4).
      - rewrite Ehs. apply (mo_ok_le MT MLM S4 _ _ HMOK4). lia.
      - intros j Hj. rewrite Ehs. exact (RI_exit_slots cx t m HRI j Hj).
      - rewrite Egn, HOe, Ehs, Hrun. discriminate.
      - exact q2.
      - exact q8.
      - exact q9.
      - exact q27.
      - rewrite q19, Hr19. reflexivity.
      - exact q3.
      - exact q4.
      - unfold lx_norder. lia.
      - exact HAT4.
      - intros i Hi. unfold lx_norder in Hi. split.
        + intros kk Hk. unfold arm. rewrite (mbyte_of_aview segs (w_H W) (w_H W2) mem1 mem4); [exact (Hord i Hi kk Hk)|].
          apply Hkeep4. unfold lf_F, AX_ORDER.
          pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia.
        + pose proof HM as (_ & _ & HRL & _). pose proof HRL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HEOK & _).
          rewrite Forall_forall in HEOK.
          assert (Hn : In (nth (Z.to_nat i) (lm_es m) lxo_e0) (lm_es m)) by (apply nth_In; lia).
          destruct (HEOK _ Hn) as (_ & _ & _ & _ & Hfd & _). unfold lx_ord. exact Hfd.
      - exact HB.
      - exact HNP4.
      - exact HCN4. }
    intros W3 c3 _ (ly5 & S5 & regs5 & mem5 & md5 & k5 & m5 & afin & -> & HJ5 & HFR5 & HFL5 & Hfa5 & HM5 & HIN5 & HROM5 &
      HJT5 & HSEP5 & HR5 & s2 & s8 & s9 & s3 & s4 & HAT5 & Haf0 & Hrun5 & Ek5 & EG5 & Ees5 & Ec5 & EO5 & Emx5 & Ecap5 &
      Eout5 & Egn5 & Enfd5 & Hlen5 & Hevo5 & Hfrm5 & HMO5 & HNP5 & HCN5).
    rewrite Egn, HOe, Ehs, Hrun in Hrun5. injection Hrun5 as Eaf.
    rewrite Ehs in HMO5, Hevo5.
    pose proof (lx_sr_total_evo_x (lm_hs m) (lm_hs m5) Hevo5) as Hsr5.
    pose proof HM5 as (_ & _ & _ & HOUT5 & _).
    pose proof HOUT5 as (_ & _ & HNO5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & HCAP5).
    rewrite EO5, HOe, Eaf in HNO5. rewrite <- HNOUT in HNO5.
    assert (HA5 : 0 <= afin < 2 ^ 64).
    { split; [exact Haf0|]. rewrite EO5, HOe, Eaf in HCAP5.
      destruct HCAP5 as [(_ & _ & ->) | (_ & Hle & Hin & _)]; [lia|].
      assert (HAR5 : ARx ly5 S5 [] W3 mem5 md5) by (eapply ajournal_gx_AR_x; exact HJ5).
      pose proof (BLKM ly5 S5 [] W3 mem5 md5 _ _ HAR5 Hin) as Hmx. lia. }
    assert (Ecapf : lm_cap m5 = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)))
      by (rewrite Ecap5; exact Ecap4).
    apply (lx_tail_x cx t m ly3 S3 rest (lx_rf_cost MT (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) + lx_ends_cost MT (lm_hs m))
      m5 afin ly5 S5 W3 regs5 mem5 md5 k5 fpos HB HLS HPm0); try assumption.
    + exact (mo_le_trans MT MLM _ _ _ _ _ HMO4 HMO5).
    + unfold lx_exit_cost. lia.
    + apply (mo_ok_le MT MLM S5 _ (lx_sr_total MT (lm_hs m))); [|lia].
      exact (mo_ok_step MT MLM S4 S5 _ _ HMOK4 HMO5).
    + rewrite EG5, EG. reflexivity.
    + rewrite Ees5, Ees4. reflexivity.
    + exact (HR5 rest (HR4 rest HPm0)).
Qed.

(* ---- cut_x Section w's SEG_EXIT (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v:639): the entry's ghost list is [] by HP0
   at lf_base_x's afn_pre_x, and the walk is lx_seg_exit_nil_x ---- *)
Theorem lf_seg_exit_x : lf_seg_exit_x_stmt.
Proof.
  unfold lf_seg_exit_x_stmt. intros cx Hp W c HB HX.
  assert (Ehp : Hp = []).
  { destruct HB as (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE. destruct HPRE as ((HAR & _) & _).
    exact (HP0 _ _ _ _ _ _ HAR). }
  subst Hp. exact (lx_seg_exit_nil_x cx W c HB HX).
Qed.
(* THE CHECK: cut_x's SEG_EXIT hypothesis in its own text, closed by `exact` *)
Local Notation BASEx cx Hp := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp).
Local Notation IX := (INV_X_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation POSTx := (lf_post_x B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx).
Lemma lf_seg_exit_x_check : forall cx Hp W c, BASEx cx Hp -> IX cx Hp W c -> SRr segs W c (POSTx cx Hp).
Proof. exact lf_seg_exit_x. Qed.
End spine.

(* ================================================================== SEG_EXIT over ARx
   the spine over the five ARx blocks: lx_order_x (W_bx_order_x.v), lx_rf_site_x (W_bx_rf_x.v), lx_ends_x
   (W_bx_ends_x.v), lx_reset_x (W_bx_reset_x.v), lx_ffexit_x (W_bx_ffexit_x.v); each takes Section hypotheses of this
   file or the facts proved from them above (HGs, HG_RFc, HG_MODEL, XRF_Gcells, XE_ERR_HI, XE_ERR_S,
   XR_ERRNO, XRF_JTAB_ROM, XRF_END5, LS_rf_mok_x). *)
Ltac bx_hyp_x := first [ eassumption | exact HGs | exact HG_RFc | exact HG_MODEL | exact XRF_Gcells
  | exact XE_ERR_HI | exact XE_ERR_S | exact XR_ERRNO | exact XRF_JTAB_ROM | exact XRF_END5
  | exact LS_rf_mok_x ].
Theorem lf_seg_exit_x_all : lf_seg_exit_x_stmt.
Proof.
  apply lf_seg_exit_x.
  - eapply W_bx_order_x.lx_order_x; bx_hyp_x.
  - eapply W_bx_rf_x.lx_rf_site_x; bx_hyp_x.
  - eapply W_bx_ends_x.lx_ends_x; bx_hyp_x.
  - eapply W_bx_reset_x.lx_reset_x; bx_hyp_x.
  - eapply W_bx_ffexit_x.lx_ffexit_x; bx_hyp_x.
  Unshelve. all: eassumption.
Qed.


(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): lf_seg_exit_x_all_xR, the R twin of lf_seg_exit_x_all, concluding cut_x's
   SEG_EXIT_R (lf_seg_exit_x_stmt_xR), from the spine's R twin lf_seg_exit_xR over the five R block statements:
   lx_order_xR, lx_ends_xR, lx_reset_xR and lx_ffexit_xR (lib/B/W_bx_order_x.v, W_bx_ends_x.v, W_bx_reset_x.v,
   W_bx_ffexit_x.v) and the premise LXRF_R : W_bx_defs_x.v lx_rf_site_S_xR for the relay_finish site.  The journal lemmas the spine reads are
   twinned at R.  Strict text above unchanged. ---- *)
Section lxxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
(* the freeing callees at R, in the strict order: source_reset (lib/B/W_contract_srlf_xR.v), check_shape_ends
   (lib/B/W_contract_xR_g6.v); check_shape_done frees nothing and keeps its strict CSD.  relay_finish (RFg) is
   called only inside the lx_rf_site block, which is the stand-in LXRF_R below. *)
Hypothesis SR_R : W_contract_srlf_xR.sr_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_source_reset).
Hypothesis CSHE_R : forall G, gx_ok segs B G -> cshe_spec_xR B PST ARx R MT RP G (BASE + AF_fr_check_shape_ends).

(* the model rule LS_exit_end (above) at the R journal: its journal premise ajournal_gx_x -> ajournal_gx_xR .. R,
   every other token the strict text's *)
Hypothesis LS_exit_end_R : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= lx_exit_cost MT m ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks B ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).

(* the relay_finish site block at R: lib/B/W_bx_defs_x.v lx_rf_site_S_xR (its R block lemma is not in lib/B yet,
   so it is the Section premise LXRF_R) *)
Hypothesis LXRF_R : W_bx_defs_x.lx_rf_site_S_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LSx RP R.

Definition lf_seg_exit_x_stmt_xR : Prop :=
  forall cx Hp W c,
    lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
    INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp W c ->
    YA0nH.SRrG segs R W c (lf_post_xR B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx R cx Hp).

Lemma lx_fla_kept_xR : forall {G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k},
  ajournal_gx_xR segs B PST ARx R G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 own ly2 S2 [] W2 m2 md2 k ->
  forall cid pos, flag_addr ly2 cid pos = flag_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _) cid pos.
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold flag_addr. rewrite EF. reflexivity.
Qed.

Definition lx_end_state_xR (cx : lfcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k',
    c' = cfg_at segs RA_LLVMF regs' mem' md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' S' [] W' mem' md' k' /\
    fr_live_post (c_S cx) S' k' /\ NP S' /\
    aregs_preserved (c_regs cx) regs' /\ getr regs' 10 = w64 0 /\
    fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' S' W' mem' /\
    fr_gi B G_fr ly' S' W' mem' /\
    rom_view segs W' mem' /\
    (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds (c_md cx)) fd) /\
    m_fs md' = m_fs (c_md cx) /\
    asink_none segs tfib_K (mrestrict (w_H W') mem') md' /\
    ameta_inv segs tfib_K ly' (mrestrict (w_H W') mem') (c_M cx) /\
    mo_le MT (c_S cx) S' (XN_LIB (c_n cx)) /\
    (forall i, 0 <= i < c_n cx ->
       aview segs (w_H W') mem' (c_p cx + i) = aview segs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) /\
    (* the cut's HB post clause (fr_lib_post_cf_x's HB conjunct), with the input block kept in the NoDup *)
    (List.NoDup (input_blks cx ++ fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')) /\
    (* the post's XCNT and CAPOUT clauses (_cut_x.v fr_lib_post_cf_x's last two), from LS_exit_cnt / LS_exit_cap *)
    (exists T0 c O mx cap out, ra_rel B fr_RG ly' S' W' mem' T0 [] /\
      aout_at B fr_RG ly' S' W' mem' c O mx (Z.of_nat (length O)) cap out /\
      ReplyCnt.xcnt_ok B S' ly' (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)]) T0 cap out) /\
    (exists c, val_mem segs (arm W' mem') (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).

Lemma lx_post_of_end_xR : forall cx W' c',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> lx_end_state_xR cx W' c' ->
  lf_post_xR B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx R cx [] W' c'.
Proof.
  intros cx W' c' HB (ly' & S' & regs' & mem' & md' & k' & -> & HJ & HLV & HNP & HPRES & HA0 & HSV & HGI & HROM & HFD &
    HFS & HSK & HMI & HMO & HIN & HBL & HXC & HCO).
  (* HBL is the cut's HB post clause with the input block kept; the post's last conjunct drops it *)
  destruct HB as (_ & HPRE).
  unfold lf_post_xR. exists ly', S', [], regs', mem', md', k'.
  split; [reflexivity|].
  unfold fr_lib_post_cf_x.
  split; [exact HJ|]. split; [exact HLV|]. split; [exact HNP|]. split; [exact HPRES|]. split; [exact HA0|].
  split; [exact HSV|]. split; [exact HGI|]. split; [exact HROM|]. split; [exact HFD|].
  split; [exact HFS|]. split; [reflexivity|]. split; [reflexivity|].
  assert (HFSS : Fs.fs_sorted (m_fs (c_md cx)) = true) by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  split; [cbn [ll_fs]; exact HFSS|].
  split; [exact HSK|]. split; [exact HMI|]. split; [exact HMO|]. split; [exact HIN|].
  split; [split; [exact (List.NoDup_app_remove_l _ _ (proj1 HBL)) | exact (proj2 HBL)]|].
  split; [exact HXC | exact HCO].
Qed.

Lemma lx_ff_kept_xR : forall cx ly S (W : world segs) mem md k fpos (W' : world segs) mem',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128) ->
     ~ (SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16) ->
     ~ (flag_addr ly 1 fpos <= a < flag_addr ly 1 fpos + 1) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') ->
  forall a, (0x10000 <= a < 0x5fc000 \/ exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros cx ly S W mem md k fpos W' mem' HB HJ HKV HGR a Hwh.
  assert (HAR : ARx ly S [] W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (HFS : frames S = [(1, fpos)]).
  { pose proof HJ as (_ & _ & (memS & HJa & _) & _). pose proof HJa as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. destruct (lx_base_facts_x cx HB) as (Hf0 & _). rewrite Hf0. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames S)) by (rewrite HFS; left; reflexivity).
  assert (H128 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
  destruct (IMGC ly S [] W mem md HAR) as [C1 C2].
  destruct (alx_frames _ _ ARx LAWS ly S [] W mem md 1 fpos HAR Hin1) as (HF32 & HFapp & _ & _).
  rewrite H128 in HFapp.
  destruct (FFL ly S [] W mem md 1 fpos HAR Hin1) as (_ & HFLo & _ & _).
  pose proof (Z.div_mod (frame_addr ly 1 fpos) 8 ltac:(lia)) as HD8.
  pose proof (Z.mod_pos_bound (frame_addr ly 1 fpos) 8 ltac:(lia)) as HM8.
  pose proof ASAN_CEIL_range as (CR & _).
  unfold in_app in HFapp. change kLowShadowBeg with 2147446784 in HFapp. change kHighMemBeg with 17594333495296 in HFapp.
  assert (HBK : forall p n, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
    4096 <= p /\ (p + req_size n <= 2147446784 \/ (17594333495296 <= p /\ p + req_size n <= ASAN_CEIL)) /\
    ~ aowned B ly S a /\ zdisjoint (p, req_size n) (frame_addr ly 1 fpos, 128)).
  { intros p n Hin Hr.
    destruct (alx_blocks _ _ ARx LAWS ly S [] W mem md p n HAR Hin) as (_ & _ & _ & Happ & Hown & _).
    unfold in_app in Happ. change kLowShadowBeg with 2147446784 in Happ. change kHighMemBeg with 17594333495296 in Happ.
    split; [lia|]. split; [lia|]. split; [exact (proj2 (Hown a Hr))|].
    destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _].
    rewrite <- H128. apply (lx_pairwise_cross zdisjoint _ _ _ _ Hp).
    - apply in_map_iff. exists (p, n). split; [reflexivity | exact Hin].
    - apply in_map_iff. exists (1, fpos). split; [reflexivity | exact Hin1]. }
  assert (Ha64 : 0 <= a < 2 ^ 64).
  { destruct Hwh as [Hw | (p & n & Hin & Hr)]; [lia|]. destruct (HBK p n Hin Hr) as (H4 & Hap & _). lia. }
  split.
  - apply HKV; [exact Ha64| | |].
    + intros HinF. destruct Hwh as [Hw | (p & n & Hin & Hr)].
      * assert (HinF' : frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + fs_frame_bytes 1) by (rewrite H128; exact HinF).
        destruct (alx_client_img _ _ ARx LAWS ly S [] W mem md a HAR
          (or_intror (or_introl (ex_intro _ 1 (ex_intro _ fpos (conj Hin1 HinF')))))) as [Hnz _].
        apply Hnz. unfold in_zr. lia.
      * destruct (HBK p n Hin Hr) as (_ & _ & _ & Hz). unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
    + intros HinS. unfold SB in HinS. destruct Hwh as [Hw | (p & n & Hin & Hr)]; [lia|].
      destruct (HBK p n Hin Hr) as (H4 & Hap & _). lia.
    + intros HinFl. assert (Ea : a = flag_addr ly 1 fpos) by lia. destruct Hwh as [Hw | (p & n & Hin & Hr)].
      * destruct (alx_client_img _ _ ARx LAWS ly S [] W mem md a HAR
          (or_intror (or_intror (ex_intro _ 1 (ex_intro _ fpos (conj Hin1 Ea)))))) as [Hnz _].
        apply Hnz. unfold in_zr. lia.
      * destruct (HBK p n Hin Hr) as (_ & _ & Hno & _). apply Hno. rewrite Ea. exact HFLo.
  - intros Hw. unfold arm in *. exact (writable_at_grows segs _ _ a HGR Hw).
Qed.

Lemma lx_end_md_xR : forall cx ly' S' (W' : world segs) mem' md' k',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' S' [] W' mem' md' k' ->
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds (c_md cx)) fd) /\
  m_fs md' = m_fs (c_md cx) /\
  asink_none segs tfib_K (mrestrict (w_H W') mem') md' /\
  ameta_inv segs tfib_K ly' (mrestrict (w_H W') mem') (c_M cx).
Proof.
  intros cx ly' S' W' mem' md' k' HB HJ.
  pose proof (FP_SINK cx [] HB) as HFP.
  destruct (lx_base_facts_x cx HB) as (_ & _ & _ & _ & _ & _ & HSK0 & HMI0).
  destruct (ajournal_gx_inner_xR segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ) as (memS & HJa & HmS).
  pose proof HJa as (_ & _ & _ & _ & Hio & _).
  destruct Hio as (_ & _ & _ & _ & _ & _ & Hcl).
  destruct (Hcl HFP) as (Efd & Efs & _).
  assert (MS : forall a, 0 <= a < 2 ^ 64 -> ~ inG G_fr a ->
    mbyte segs (mrestrict (w_H (c_W cx)) memS) a = mbyte segs (mrestrict (w_H (c_W cx)) (c_mem cx)) a).
  { intros a Ha Hg. apply mbyte_of_aview. apply HmS. rewrite unsigned_lit_small by lia. exact Hg. }
  split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
  split; [unfold m_fs; rewrite Efs; reflexivity|].
  split.
  - eapply (YE01_xR.asink_none_kept_xR segs B PST ARx tfib_K AIL R);
      [exact HJa | intros a Ha; apply HPST; exact (proj1 (ail_env _ _ _ AIL a Ha)) | exact HFP |].
    apply (asink_none_frame segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx))); [|exact HSK0].
    intros a Ha. destruct (HG_K a (or_introl Ha)) as (Hr & Hg). exact (MS a Hr Hg).
  - eapply (YE01_xR.ameta_inv_kept_xR segs B PST ARx LAWS tfib_K AIL R);
      [exact HJa | intros a Ha; apply HPST; exact (proj1 (ail_meta _ _ _ AIL a Ha)) |].
    destruct HMI0 as (HX & HIM & HOK). split; [exact HX|]. split; [exact HIM|].
    apply (ameta_ok_frame segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx))); [|exact HOK].
    intros a [Ha | [Ha | Ha]].
    + destruct (HG_K a (or_intror (or_introl Ha))) as (Hr & Hg). exact (MS a Hr Hg).
    + destruct (HG_K a (or_intror (or_intror Ha))) as (Hr & Hg). exact (MS a Hr Hg).
    + pose proof HOK as (_ & _ & HM0 & HM47 & _). apply MS; [lia|]. intros Hg.
      pose proof (HIM a (proj1 (HG a Hg))). lia.
Qed.

Lemma lx_end_of_ffexit_xR : forall cx t m0 ly0 S0 rest C m ev ly2 S2 (W2 : world segs) mem2 md2 k2 fpos
    (W3 : world segs) regs3 mem3 md3,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  LSx cx t m0 ly0 S0 ->
  Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m0 ++ rest) ->
  mo_le MT S0 S2 C -> C <= lx_exit_cost MT m0 ->
  lm_G m = lm_G m0 -> lm_es m = [] ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 [] W2 mem2 md2 k2 ->
  amodel_at B ly2 S2 W2 mem2 (lx_reset_model m ev) ->
  ainput_at B cx ly2 S2 W2 mem2 ->
  Permutation (ablocks B ly2 S2) (input_blks cx ++ model_blks (lx_reset_model m ev) ++ rest) ->
  rom_view segs W2 mem2 ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly2 (stack_free_state 1 fpos S2) [] W3 mem3 md3 k2 ->
  aregs_preserved (c_regs cx) regs3 -> getr regs3 10 = w64 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr ly2 1 fpos <= a < frame_addr ly2 1 fpos + 128) ->
     ~ (SB + frame_addr ly2 1 fpos / 8 <= a < SB + frame_addr ly2 1 fpos / 8 + 16) ->
     ~ (flag_addr ly2 1 fpos <= a < flag_addr ly2 1 fpos + 1) ->
     aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a) ->
  mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W3) mem3) ->
  (* relay_finish's final capacity, from lx_rf_post_site_x through lx_ends_post_x: the cap LS_exit_end is taken at *)
  lm_cap m = gse_cap (lx_rf_run (lm_c m0) [] (lm_mx m0) 0 (lm_cap m0) (lm_es m0)) ->
  (* LS_exit_cap's RINV and lregs_X's t bound at X; the room thread's NP at the reset's state; LS_exit_end's last
     premise, X's non-empty key texts (KF-COUNT F8) *)
  RINV cx t m0 -> 0 <= t <= OPS_MAX -> NP S2 ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m0) ->
  lx_end_state_xR cx W3 (cfg_at segs RA_LLVMF regs3 mem3 md3).
Proof.
  intros cx t m0 ly0 S0 rest C m ev ly2 S2 W2 mem2 md2 k2 fpos W3 regs3 mem3 md3
    HB HLS HPm0 HMO HC EG Ees HJ2 HM2 HIN2 HP2 HROM2 HJ3 HPRES HA0 HKV HGR Hcap HRI Ht HNP2 HK0.
  assert (HFS2 : frames S2 = [(1, fpos)]).
  { pose proof HJ2 as (_ & _ & (memS & HJa & _) & _). pose proof HJa as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. destruct (lx_base_facts_x cx HB) as (Hf0 & _). rewrite Hf0. reflexivity. }
  pose proof (lx_ff_kept_xR cx ly2 S2 W2 mem2 md2 k2 fpos W3 mem3 HB HJ2 HKV HGR) as KEEP.
  assert (EB : ablocks B ly2 (stack_free_state 1 fpos S2) = ablocks B ly2 S2) by reflexivity.
  assert (EM : model_blks (lx_reset_model m ev) = (lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)).
  { unfold model_blks, lx_reset_model. cbn [lm_G lm_es lm_hs lm_cap lm_out]. rewrite Ees, EG. reflexivity. }
  (* HFH at the reset's state: fr_hb_of_model at the reset's model (image A's lx_end_of_ffexit_x) *)
  assert (HAR2 : ARx ly2 S2 [] W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
  assert (HFH2 : fr_hblks W2 mem2 = (lm_G (lx_reset_model m ev), ATABLE) ::
      aout_blks (lm_cap (lx_reset_model m ev)) (lm_out (lx_reset_model m ev))).
  { refine (proj1 (fr_hb_of_model B cx (lx_reset_model m ev) ly2 S2 W2 mem2 rest _
      (bx_nodup_ablocks_x ly2 S2 W2 mem2 md2 HAR2) HM2 HP2)).
    intros p n Hin. destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR2 Hin) as (_ & H1 & H2 & _). lia. }
  cbn [lx_reset_model lm_G lm_cap lm_out] in HFH2. rewrite EG in HFH2.
  rewrite EM in HP2.
  assert (INB : forall b, In b ((lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)) -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
  assert (KI : forall x, 0x10000 <= x < 0x5fc000 -> abyte_kept W2 mem2 W3 mem3 x)
    by (intros x Hx; exact (KEEP x (or_introl Hx))).
  pose proof lx_glob_lits_x as LITS.
  assert (HFH : fr_hblks W3 mem3 = (lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)).
  { rewrite (fr_hblks_kept W2 W3 mem2 mem3); [exact HFH2|].
    intros a Ha. pose proof LITS as (L1 & _ & _ & _ & _ & L6 & L7 & _). rewrite L1, L6, L7 in Ha.
    exact (proj1 (KI a ltac:(lia))). }
  destruct (LS_exit_end_R cx t m0 ly0 S0 rest ly2 S2 W3 mem3 md3 fpos k2 C (lm_cap m) (lm_out m) HLS HPm0 HP2 HFS2 HMO HC
    HJ3 Hcap Ht HFH (bx_nodup_ablocks_x ly2 S2 W2 mem2 md2 HAR2) HK0) as (HLV & HSV & HMOE).
  (* NP at the return: the room thread's NP through the release (rp_RM survives stack_free_state) *)
  assert (HNP : NP (stack_free_state 1 fpos S2))
    by exact (proj1 (RP_NP _ 0%nat) (RPF_stack_free RP S2 1 fpos 0%nat (proj2 (RP_NP S2 0%nat) HNP2))).
  destruct (lx_end_md_xR cx ly2 (stack_free_state 1 fpos S2) W3 mem3 md3 k2 HB HJ3) as (HFD & HFSY & HSK & HMI).
  pose proof HM2 as (_ & HSL & HRL & HOUT & HGN & HLK & HWK & _ & _ & _ & HTU & HLST & HLW).
  cbn [lx_reset_model lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn] in HSL, HRL, HOUT, HGN.
  assert (HAR3 : ARx ly2 (stack_free_state 1 fpos S2) [] W3 mem3 md3)
    by (eapply ajournal_gx_AR_xR; exact HJ3).
  (* the relay's table and the controller's buffer at the END state, named once: fr_gi uses them, and so does the
     cut's coming last conjunct *)
  assert (HRL3 : arelay_at B fr_RG ly2 (stack_free_state 1 fpos S2) W3 mem3 (lm_G m) []).
  { rewrite Ees in HRL.
    apply (arelay_at_kept B fr_RG ly2 S2 W2 mem2 ly2 _ W3 mem3 (lm_G m) [] HRL).
    - intros r Hr x Hx. unfold arelay_fp in Hr. cbn [map concat app] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hx; [apply KI; lia | apply KI; lia | apply KI; lia|].
      apply KEEP. right. exists (lm_G m), ATABLE. split; [apply INB; left; rewrite EG; reflexivity|].
      change (req_size ATABLE) with 896. change ATABLE with 896 in Hx. lia.
    - intros b Hb. rewrite EB. cbn in Hb. destruct Hb as [<- | []]. apply INB. left. rewrite EG. reflexivity. }
  eassert (HOUT3 : aout_at B fr_RG ly2 (stack_free_state 1 fpos S2) W3 mem3 _ _ _ _ (lm_cap m) (lm_out m)).
  { apply (aout_at_kept B fr_RG ly2 S2 W2 mem2 ly2 _ W3 mem3 _ _ _ _ _ _ HOUT).
    - intros r Hr x Hx. unfold aout_fp in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Hx.
      1-8: (apply KI; lia).
      + apply KI. apply lx_errno_rng_x. lia.
      + revert Hr. destruct (Z.eqb_spec (lm_cap m) 0) as [Hc0 | Hc0]; intros Hr; [destruct Hr|].
        destruct Hr as [<- | []]. cbn [fst snd] in Hx. apply KEEP. right. exists (lm_out m), (lm_cap m).
        split; [apply INB; right; unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ 0) Hc0); left; reflexivity|].
        unfold req_size. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). lia.
    - intros b Hb. rewrite EB. apply INB. right. exact Hb. }
  (* XCNT at the return: LS_exit_cnt at the reset's blocks (stack_free_state keeps ablocks) *)
  assert (H4096 : forall p n, In (p, n) (ablocks B ly2 S2) -> 4096 <= p).
  { intros p n Hin. destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR2 Hin) as (_ & H4 & _). exact H4. }
  pose proof (LS_exit_cnt cx t m0 ly0 S0 rest ly2 S2 (lm_cap m) (lm_out m) HLS HPm0 HP2 H4096) as HXP.
  assert (HXC : ReplyCnt.xcnt_ok B (stack_free_state 1 fpos S2) ly2 (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)])
    (lm_G m) (lm_cap m) (lm_out m)).
  { rewrite EG. unfold ReplyCnt.xcnt_ok in HXP |- *. rewrite EB. exact HXP. }
  (* CAPOUT at the return: g_capout is relay_finish's final capacity, under CAPOUT_MAX by LS_exit_cap *)
  pose proof (LS_exit_cap cx t m0 ly0 S0 HLS HRI Ht) as HCAP.
  exists ly2, (stack_free_state 1 fpos S2), regs3, mem3, md3, k2.
  split; [reflexivity|]. split; [exact HJ3|]. split; [exact HLV|]. split; [exact HNP|]. split; [exact HPRES|].
  split; [exact HA0|]. split; [exact HSV|].
  split.
  { unfold fr_gi.
    split; [intros a Ha; exact (GWR (w_H W3) mem3 a Ha)|].
    split.
    { intros i Hi. specialize (HSL i Hi).
      assert (Enth : nth i [None; None; None; None] (@None hsrc) = None)
        by (do 4 (destruct i as [|i]; [reflexivity|]); lia).
      rewrite Enth in HSL. destruct HSL as (HZ & HWr).
      assert (KS : forall x, rg_s fr_RG + ASRC * Z.of_nat i <= x < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
        abyte_kept W2 mem2 W3 mem3 x) by (intros x Hx; apply KI; lia).
      split.
      - apply (akept_garr8 W2 mem2); [|exact HZ]. intros x Hx. apply KS.
        rewrite repeat_length, Z2Nat.id in Hx by lia. lia.
      - apply (akept_awr W2 mem2); [|exact HWr]. exact KS. }
    split.
    { exists (lm_G m). right. exact HRL3. }
    split.
    { eexists _, _, _, _, _. exact HOUT3. }
    split.
    { eexists. apply (agone_at_kept fr_RG W2 mem2 W3 mem3 _ HGN).
      intros r [<- | []] x Hx. apply KI. cbn [fst snd] in Hx. lia. }
    split.
    { apply (alock_at_kept fr_RG W2 mem2 W3 mem3 _ HLK). intros r [<- | []] x Hx. apply KI. cbn [fst snd] in Hx. lia. }
    split.
    { apply (awake_at_kept fr_RG W2 mem2 W3 mem3 HWK). intros r [<- | []] x Hx. apply KI. cbn [fst snd] in Hx. lia. }
    split.
    { apply (akept_vm W2 mem2 W3 mem3 AG_THREAD_UP 1%nat 0); [intros x Hx; apply KI; lia | exact HTU]. }
    split.
    { destruct HLST as (lst & Hl). exists lst.
      apply (akept_vm W2 mem2 W3 mem3 AG_LISTEN 4%nat lst); [intros x Hx; apply KI; lia | exact Hl]. }
    pose proof (akept_awr W2 mem2 W3 mem3 AG_LISTEN 4 ltac:(intros x Hx; apply KI; lia) HLW) as HLW3.
    intros i Hi. exact (HLW3 i Hi). }
  split.
  { intros a Ha. rewrite (proj1 (KEEP a (or_introl (lx_rom_rng_x a Ha)))). exact (HROM2 a Ha). }
  split; [exact HFD|]. split; [exact HFSY|]. split; [exact HSK|]. split; [exact HMI|]. split; [exact HMOE|].
  split.
  { intros i Hi.
    destruct (lx_base_facts_x cx HB) as (_ & _ & _ & _ & Hlen & Hpl0 & _).
    destruct HIN2 as ([[Hn0 _] | [Hnr HinB]] & Hg2); [lia|].
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
    assert (Hri : c_p cx <= c_p cx + i < c_p cx + req_size (c_n cx)) by lia.
    rewrite (proj1 (KEEP (c_p cx + i) (or_intror (ex_intro _ (c_p cx) (ex_intro _ (c_n cx) (conj HinB Hri)))))).
    apply (lx_garr8_view_x W2 (c_W cx) mem2 (c_mem cx) (c_p cx) _ i Hg2 Hpl0).
    rewrite length_map. lia. }
  (* the cut's HB post clause, from the model's blocks and ablocks_sep's Permutation *)
  split.
  { refine (bx_post_hblks_x cx ly2 (stack_free_state 1 fpos S2) W3 mem3 md3 (lm_G m) _ _ _ _ (lm_cap m) (lm_out m) rest
      HAR3 (or_intror HRL3) HOUT3 _).
    rewrite EB, EG. exact HP2. }
  (* the post's XCNT and CAPOUT clauses (image A's lx_end_of_ffexit_x): the table and g_out at the return with
     LS_exit_cnt's count, and g_capout's bound *)
  split.
  - exists (lm_G m). eexists _, _, _. exists (lm_cap m), (lm_out m).
    split; [right; exact HRL3|]. split; [exact HOUT3 | exact HXC].
  - exists (lm_cap m).
    pose proof HOUT3 as (_ & _ & _ & _ & Hcv & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & Hcd).
    split; [exact Hcv|]. split; [destruct Hcd as [(Hc0 & _) | (Hp & _)]; lia|]. rewrite Hcap. exact HCAP.
Qed.

Section spineR.
Hypothesis LXO_R : lx_order_S_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx R.
Hypothesis LXE_R : lx_ends_S_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx R RP.
Hypothesis LXR_R : lx_reset_S_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx RP R.
Hypothesis LXF_R : lx_ffexit_S_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx R.

Lemma lx_tail_xR : forall cx t m0 ly0 S0 rest C m A ly S (W : world segs) regs mem md k fpos,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  LSx cx t m0 ly0 S0 ->
  Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m0 ++ rest) ->
  mo_le MT S0 S C -> C + lx_sr_total MT (lm_hs m) <= lx_exit_cost MT m0 ->
  mo_ok MT S (lx_sr_total MT (lm_hs m)) ->
  lm_G m = lm_G m0 -> lm_es m = [] ->
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md k ->
  bx_frame cx (frame_addr ly 1 fpos) W mem ->
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) ->
  amodel_at B ly S W mem m ->
  ablocks_sep B fr_FP cx m ly S ->
  ainput_at B cx ly S W mem ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 A -> 0 <= A < 2 ^ 64 ->
  val_mem segs (arm W mem) (VAL A_g_nout) 8 A ->
  rom_view segs W mem ->
  (* relay_finish's final capacity (lx_end_of_ffexit_x's last premise) *)
  lm_cap m = gse_cap (lx_rf_run (lm_c m0) [] (lm_mx m0) 0 (lm_cap m0) (lm_es m0)) ->
  (* LS_exit_cap's RINV and t bound at X; the room thread's NP and count at the reset's start *)
  RINV cx t m0 -> 0 <= t <= OPS_MAX -> NP S -> cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly S) ->
  (* X's non-empty key texts (lx_end_of_ffexit_x's last premise, KF-COUNT F8) *)
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m0) ->
  YA0nH.SRrG segs R W (cfg_at segs (BASE + AX_done) regs mem md)
    (lf_post_xR B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx R cx []).
Proof.
  intros cx t m0 ly0 S0 rest C m A ly S W regs mem md k fpos HB HLS HPm0 HMO HC HOK EG Ees HPm r2 r9 r8 r3 r4
    HJ HFR HFL HM HSEP HIN HAT HA HNO HROM Hcap HRI Ht HNPs HCNs HK0.
  eapply (YA0nH.SRrG_bind segs R R_trans); [exact (LXR_R cx m A fpos ly S W regs mem md k HB r2 r9 r8 r3 r4 HJ HFR HFL HM HSEP HIN HOK HAT HA HNO HROM
    HNPs HCNs)|].
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k2 & ev & -> & HJ2 & q2 & q9 & q8 & q20 & q24 & q3 & q4 &
    HFR2 & HFL2 & HM2 & HSEP2 & HIN2 & HR2 & HROM2 & Hfa2 & HMO2 & HNP2 & HCN2).
  assert (HFR2' : bx_frame cx (frame_addr ly2 1 fpos) W2 mem2) by (rewrite Hfa2; exact HFR2).
  assert (HFL2' : sv8 W2 mem2 (frame_addr ly2 1 fpos + 120) (flag_addr ly2 1 fpos)).
  { rewrite Hfa2, (lx_fla_kept_xR HJ2). rewrite (lx_fla_kept_xR HJ) in HFL2. exact HFL2. }
  destruct (lx_base_facts_x cx HB) as (_ & Hra & Hgp & Htp & _).
  eapply YA0nH.SRrG_mono.
  { apply (LXF_R cx W2 regs2 mem2 md2 ly2 S2 k2 fpos (frame_addr ly2 1 fpos) HB eq_refl HJ2 HFR2' HFL2').
    - rewrite q8. unfold spZ. symmetry. apply lit_of_word.
    - exact q9.
    - rewrite Hfa2. exact q20.
    - rewrite Hfa2. exact q24.
    - rewrite q3, Hgp. reflexivity.
    - rewrite q4, Htp. reflexivity.
    - unfold raZ in Hra. rewrite <- Hra. symmetry. apply lit_of_word. }
  intros W3 c3 _ (regs3 & mem3 & md3 & -> & HJ3 & HPRES & HA0 & HKV & HGR).
  apply (lx_post_of_end_xR cx W3 _ HB).
  apply (lx_end_of_ffexit_xR cx t m0 ly0 S0 rest (C + lx_sr_total MT (lm_hs m)) m ev ly2 S2 W2 mem2 md2 k2 fpos
    W3 regs3 mem3 md3 HB HLS HPm0); try assumption.
  - exact (mo_le_trans MT MLM _ _ _ _ _ HMO HMO2).
  - exact (HR2 rest HPm).
Qed.

Lemma lx_seg_exit_nil_xR : forall cx W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] W c ->
  YA0nH.SRrG segs R W c (lf_post_xR B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx R cx []).
Proof.
  intros cx W c HB (regs & mem & md & t & -> & HJT & HL).
  destruct HL as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HM & HIN & HROM & HSEP & HLS & HNP3 & HRI & HX).
  (* lregs_X's t bound (its last conjunct; B's lregs_X has nine conjuncts before it, A's ten) and LS_cnt's count at X *)
  assert (Ht : 0 <= t <= OPS_MAX) by (pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ht); exact Ht).
  pose proof (LS_cnt cx t m ly3 S3 W mem HLS HRI HM Ht) as HCNT.
  (* the cut's ghost list is [] (HP0 at its journal's end state) *)
  assert (Ehp3 : Hp3 = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJ). subst Hp3.
  pose proof HSEP as ((rest & HPm0) & _).
  (* LS_exit_budget's two F8 premises: lregs_X's t bound and X's non-empty key texts, read off X's amodel_at (HM) *)
  pose proof (W_bx_rf_x.exit_keys_nonempty B ly3 S3 W mem m HM) as HK.
  pose proof (LS_exit_budget cx t m ly3 S3 HLS Ht HK) as HMOK.
  pose proof (lx_ends_cost_nonneg (lm_hs m)) as Hec. pose proof (lx_sr_total_nonneg (lm_hs m)) as Hsc.
  assert (HNOUT : VAL A_g_nout = rg_nout fr_RG) by (vm_compute; reflexivity).
  eapply (YA0nH.SRrG_bind segs R R_trans); [exact (LXO_R cx W _ regs mem md own ly3 S3 k m fpos t HB eq_refl HJ Hown HFR HFL HM HIN HROM HX HJT)|].
  intros W1 c1 _ (-> & regs1 & mem1 & md1 & Hcase & HJ1 & HFR1 & HFL1 & HM1 & HIN1 & HROM1 & HJT1 & HAT1 & HX1).
  subst own.
  assert (Hrf : forall pcj, pcj = AX_join \/ pcj = AX_noord ->
    YA0nH.SRrG segs R W (cfg_at segs (fr_B0 + pcj) regs1 mem1 md1)
      (W_bx_defs_x.lx_rf_post_site_xR B MT NP G_fr fr_FP PST ARx RP R cx pcj m fpos ly3 S3 (getr regs1 19) W mem1))
    by (intros pcj Hp; exact (LXRF_R cx pcj t W regs1 mem1 md1 ly3 S3 fpos k m HB Hp HJ1 HFR1 HFL1 HM1 HIN1 HROM1 HJT1
          HSEP HLS HX1 HAT1 HNP3 HCNT)).
  destruct Hcase as [(-> & Hes0) | (-> & Hes & Hr19 & Hord)].
  - (* no relay entry: 0x84fe0 *)
    apply length_zero_iff_nil in Hes0.
    eapply (YA0nH.SRrG_bind segs R R_trans); [exact (Hrf AX_noord (or_intror eq_refl))|].
    intros W2 c2 _ (ly4 & S4 & regs4 & mem4 & md4 & k4 & m4 & -> & HJ4 & HFR4 & HFL4 & Hfa4 & HM4 & HIN4 & HROM4 & HJT4 &
      HSEP4 & q2 & q8 & q9 & q3 & q4 & q27 & q19 & HAT4 & Hkeep4 & Ek & Ehs & EG & Ees4 & Egn & Enfd & HO0 & HOe &
      HR4 & Hfrm4 & HMO4 & Ecap4 & HNP4 & HCN4).
    replace (fr_B0 + AX_noord + 8) with (BASE + AX_done) by (rewrite BASE_B0; unfold AX_noord, AX_done; lia).
    pose proof (HO0 Hes0) as HO4.
    pose proof HM4 as (_ & _ & _ & HOUT4 & _). pose proof HOUT4 as (_ & _ & HNO4 & _).
    rewrite HO4 in HNO4. cbn [length Z.of_nat] in HNO4. rewrite <- HNOUT in HNO4.
    apply (lx_tail_xR cx t m ly3 S3 rest (lx_rf_cost MT (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) m4 0 ly4 S4 W2
      regs4 mem4 md4 k4 fpos HB HLS HPm0 HMO4); try assumption.
    + unfold lx_exit_cost. rewrite Ehs. lia.
    + rewrite Ehs. apply (mo_ok_le MT MLM S4 _ (lx_ends_cost MT (lm_hs m) + lx_sr_total MT (lm_hs m))); [|lia].
      exact (mo_ok_step MT MLM S3 S4 _ _ HMOK HMO4).
    + exact (HR4 rest HPm0).
    + exact (bx_frame_of_aframe _ _ _ _ HFR4).
    + lia.
  - (* the relay's table is not empty: 0x84f00 *)
    eapply (YA0nH.SRrG_bind segs R R_trans); [exact (Hrf AX_join (or_introl eq_refl))|].
    intros W2 c2 _ (ly4 & S4 & regs4 & mem4 & md4 & k4 & m4 & -> & HJ4 & HFR4 & HFL4 & Hfa4 & HM4 & HIN4 & HROM4 & HJT4 &
      HSEP4 & q2 & q8 & q9 & q3 & q4 & q27 & q19 & HAT4 & Hkeep4 & Ek & Ehs & EG & Ees4 & Egn & Enfd & HO0 & HOe &
      HR4 & Hfrm4 & HMO4 & Ecap4 & HNP4 & HCN4).
    replace (fr_B0 + AX_join + 8) with (BASE + AX_after_rf) by (rewrite BASE_B0; unfold AX_join, AX_after_rf; lia).
    (* RI_exit_ends' last two premises, read off X's amodel_at (HM): agone_at's 0 / 1, the held lists' NUL-free texts *)
    assert (Hgn01 : 0 <= lm_gn m <= 1)
      by (pose proof HM as (_ & _ & _ & _ & (_ & _ & Hg) & _); clear - Hg; destruct Hg as [Hg|Hg]; lia).
    assert (Hnul : forall i h, nth i (lm_hs m) None = Some h ->
      Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))).
    { intros i h Eh. pose proof HM as (Hl4 & HSL & _).
      destruct (Nat.lt_ge_cases i 4) as [Hi | Hi]; [|rewrite nth_overflow in Eh by (clear - Hl4 Hi; lia); discriminate Eh].
      pose proof (HSL i Hi) as X. rewrite Eh in X. cbn [aslot] in X.
      destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        (_ & _ & _ & _ & _ & _ & _ & _ & Hrecs) & _).
      eapply Forall_impl; [|exact Hrecs]. intros r (_ & _ & Hl & _). exact (proj1 (Hl eq_refl)). }
    pose proof (RI_exit_ends cx t m HRI Hes Hgn01 Hnul) as Hrun. unfold lx_rf_O in Hrun.
    pose proof (mo_ok_step MT MLM S3 S4 _ _ HMOK HMO4) as HMOK4.
    eapply (YA0nH.SRrG_bind segs R R_trans).
    { apply (LXE_R cx t fpos ly4 S4 m4 (lx_norder m) (lx_ord m) regs4 mem4 md4 W2 k4 HJ4 HFR4 HFL4 HM4 HIN4 HROM4 HJT4 HSEP4).
      - rewrite Ehs. apply (mo_ok_le MT MLM S4 _ _ HMOK4). lia.
      - intros j Hj. rewrite Ehs. exact (RI_exit_slots cx t m HRI j Hj).
      - rewrite Egn, HOe, Ehs, Hrun. discriminate.
      - exact q2.
      - exact q8.
      - exact q9.
      - exact q27.
      - rewrite q19, Hr19. reflexivity.
      - exact q3.
      - exact q4.
      - unfold lx_norder. lia.
      - exact HAT4.
      - intros i Hi. unfold lx_norder in Hi. split.
        + intros kk Hk. unfold arm. rewrite (mbyte_of_aview segs (w_H W) (w_H W2) mem1 mem4); [exact (Hord i Hi kk Hk)|].
          apply Hkeep4. unfold lf_F, AX_ORDER.
          pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia.
        + pose proof HM as (_ & _ & HRL & _). pose proof HRL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HEOK & _).
          rewrite Forall_forall in HEOK.
          assert (Hn : In (nth (Z.to_nat i) (lm_es m) lxo_e0) (lm_es m)) by (apply nth_In; lia).
          destruct (HEOK _ Hn) as (_ & _ & _ & _ & Hfd & _). unfold lx_ord. exact Hfd.
      - exact HB.
      - exact HNP4.
      - exact HCN4. }
    intros W3 c3 _ (ly5 & S5 & regs5 & mem5 & md5 & k5 & m5 & afin & -> & HJ5 & HFR5 & HFL5 & Hfa5 & HM5 & HIN5 & HROM5 &
      HJT5 & HSEP5 & HR5 & s2 & s8 & s9 & s3 & s4 & HAT5 & Haf0 & Hrun5 & Ek5 & EG5 & Ees5 & Ec5 & EO5 & Emx5 & Ecap5 &
      Eout5 & Egn5 & Enfd5 & Hlen5 & Hevo5 & Hfrm5 & HMO5 & HNP5 & HCN5).
    rewrite Egn, HOe, Ehs, Hrun in Hrun5. injection Hrun5 as Eaf.
    rewrite Ehs in HMO5, Hevo5.
    pose proof (lx_sr_total_evo_x (lm_hs m) (lm_hs m5) Hevo5) as Hsr5.
    pose proof HM5 as (_ & _ & _ & HOUT5 & _).
    pose proof HOUT5 as (_ & _ & HNO5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & HCAP5).
    rewrite EO5, HOe, Eaf in HNO5. rewrite <- HNOUT in HNO5.
    assert (HA5 : 0 <= afin < 2 ^ 64).
    { split; [exact Haf0|]. rewrite EO5, HOe, Eaf in HCAP5.
      destruct HCAP5 as [(_ & _ & ->) | (_ & Hle & Hin & _)]; [lia|].
      assert (HAR5 : ARx ly5 S5 [] W3 mem5 md5) by (eapply ajournal_gx_AR_xR; exact HJ5).
      pose proof (BLKM ly5 S5 [] W3 mem5 md5 _ _ HAR5 Hin) as Hmx. lia. }
    assert (Ecapf : lm_cap m5 = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)))
      by (rewrite Ecap5; exact Ecap4).
    apply (lx_tail_xR cx t m ly3 S3 rest (lx_rf_cost MT (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) + lx_ends_cost MT (lm_hs m))
      m5 afin ly5 S5 W3 regs5 mem5 md5 k5 fpos HB HLS HPm0); try assumption.
    + exact (mo_le_trans MT MLM _ _ _ _ _ HMO4 HMO5).
    + unfold lx_exit_cost. lia.
    + apply (mo_ok_le MT MLM S5 _ (lx_sr_total MT (lm_hs m))); [|lia].
      exact (mo_ok_step MT MLM S4 S5 _ _ HMOK4 HMO5).
    + rewrite EG5, EG. reflexivity.
    + rewrite Ees5, Ees4. reflexivity.
    + exact (HR5 rest (HR4 rest HPm0)).
Qed.

Theorem lf_seg_exit_xR : lf_seg_exit_x_stmt_xR.
Proof.
  unfold lf_seg_exit_x_stmt_xR. intros cx Hp W c HB HX.
  assert (Ehp : Hp = []).
  { destruct HB as (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE. destruct HPRE as ((HAR & _) & _).
    exact (HP0 _ _ _ _ _ _ HAR). }
  subst Hp. exact (lx_seg_exit_nil_xR cx W c HB HX).
Qed.
End spineR.

Theorem lf_seg_exit_x_all_xR : lf_seg_exit_x_stmt_xR.
Proof.
  (* check_shape_done frees nothing: its R text from the strict CSD (W_contract_srlf_xR.v csd_spec_xR_of_x, WLE_R) *)
  assert (CSD_R : W_contract_srlf_xR.csd_spec_xR B PST ARx R (BASE + AF_fr_check_shape_done))
    by (eapply W_contract_srlf_xR.csd_spec_xR_of_x; eassumption).
  apply lf_seg_exit_xR.
  - eapply W_bx_order_x.lx_order_xR; bx_hyp_x.
  - eapply W_bx_ends_x.lx_ends_xR; bx_hyp_x.
  - eapply W_bx_reset_x.lx_reset_xR; bx_hyp_x.
  - eapply W_bx_ffexit_x.lx_ffexit_xR; bx_hyp_x.
  Unshelve. all: eassumption.
Qed.

End lxxR.

End lxx.
