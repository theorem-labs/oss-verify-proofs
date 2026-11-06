(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC conversion of SEG_PRO, the prologue of fuzz_reply's LLVMFuzzerTestOneInput
   (lib/A/W_LLVMFuzzerTestOneInput_pro.v, a Theorem Labs lane's lf_seg_pro, Qed at a working branch 5c8023c8afd) to
   the cut invariants of lib/A/W_LLVMFuzzerTestOneInput_cut_x.v (a Theorem Labs lane's route (b), step 7). lf_seg_pro_x is
   exactly cut_x's Section w hypothesis SEG_PRO. Neither _pro.v nor cut_x is edited.
   - The Section header is cut_x's Section w header (B .. RINV, with PST / ARx / hl / LAWS / HP0 / HG / LSx).
   - _pro.v's own hypotheses, in its order: the AR-free ones verbatim (TL, TLF, GWL, HEV, HZS, HG_obj, HROM_G,
     ROM_PIN); W2_op_add at the kit's form W_op_add.oa_spec_g_x (lib/A/W_op_add.v:2936); ERRL at cut_x's
     errno_law_x; ASM1 / FFL at W_frame_x's astack_malloc_pres_x / frame_flag_lawP_x; SHV_oa over ARx; HFP_pro,
     LS_pro_oa, RI_pro, LS_pro with lf_base -> lf_base_x at the entry's ghost list Hp (bound after cx) and LS -> LSx,
     the rest of their text verbatim.
   - ML and SMP (cgif's model_laws / stack_malloc_progressP) are not hypotheses here: the generic stack_malloc seat
     W_frame_x.aj_stack_malloc_pres_at_x takes in their place its Section fsp hypotheses OWNLOW, WFx / WFL and
     SMALLOC, stated here in W_frame_x.v:747-759's text (W_frame_x's header: forced by the second instance).
   - OWED (kit has no twin): BLKN, add_x's text (AR's al_blocks has 0 <= n, AR_laws_x's alx_blocks does not).
     Forced by the generic placement, add_x's text: HPST (the image is off PST; at the instance's PST := [] it holds
     trivially), which the ROM-view lemma W_journal_x.ajournal_gx_rom_view_x asks.
   - MO_FR (top_x's text, W_LLVMFuzzerTestOneInput_top_x.v:343): the seat's set_fs costs nothing at the meter MT; it
     gives LS_pro_oa's / LS_pro's premise mo_le MT (c_S cx) S2 0 (KF-COUNT F2, f937a8adaa8) at the seat.
   - HP0 makes every ghost list of the walk empty, so the converted helpers are stated at Hp = []: AR0 is _pro.v's AR at
     [], AJ0 its journal at G, AFN0 its afn_pre, LFB0 its lf_base. The AR-free lemmas and definitions of _pro.v are
     CITED from it (with their section arguments, through local abbreviations); each one that reads AR is converted
     here under its name + _x with _pro.v's proof: AR's laws -> AR_laws_x's fields, the journal lemmas ->
     W_journal_x's, the runs -> W_journal_x's paj_run_x_x / paj_run_to_x_x (the first run at G = [], W1Verify's
     template) and W_frame_x's SRr_run_pi_AJ_x, lib/A/W_LLVMFuzzerTestOneInput_latch.v's keep lemmas -> latch_x's.
   - Re-derived locally rather than taken as hypotheses: YCbq.v:2602 region_kept_stack_aj over ajournal_x
     (region_kept_stack_aj_x, its proof), W_frame_x's IMGC by small_x's sm_imgc_x (the image law), and
     W_journal.v:399 ajournal_gx_rom_view at AJ0 (ajournal_gx_rom_view0, from HPST).
   - ROUTE R (a Theorem Labs lane, 2026-10-31): Section prxR at the end of Section prx states lf_seg_pro_xR, cut_x's Section wR
     hypothesis SEG_PRO_R, over R R_refl R_trans WLE_R and op_add's R contract W2_op_add_R (in place of W2_op_add);
     the strict lemmas are unchanged, and Section chkR at the end checks the twin's type and its slot in cut_x's
     lf_contract_of_segments_xR. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
(* route R: SRrG and its lemmas (Section prxR), imported before _pro.v's imports so that they shadow nothing there *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_op_add W_LLVMFuzzerTestOneInput_small_x W_LLVMFuzzerTestOneInput_latch_x.
(* _pro.v's own imports, AFTER the generic kit's: the copied proofs see the names they were written against *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a YP07.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_G W_LLVMFuzzerTestOneInput_latch.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_pro.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag _pro.v's proofs (copied here) expect *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section prx.
(* cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:191-235) *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
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
(* the instance's ghost poisoned-head set stays empty (a Theorem Labs lane's HP0 ruling, W_journal_x at 0c4d57d9bf1;
   fuzz_reply calls no poison routine): the driver reads the post's Hp' = [] from the journal's ARx through it *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* ---- the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.2 / 0.4): the allocator rules' room record RP, whose room invariant
   is the cut's NP (the walk's RM := fun S _ => NP S; at top_x rp_RM RP := fun S _ => room_live_cf S = NP), and NPF:
   the fake frame's seat (a set_fs) keeps NP (top_x: room_live_set_fs) ---- *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis NPF : forall S f, NP S -> NP (set_fs f S).
(* ---- KF-COUNT F2: the meter law of the same seat, a set_fs costs nothing at MT (top_x's MO_FR verbatim,
   lib/A/W_LLVMFuzzerTestOneInput_top_x.v:343): it gives LS_pro_oa's / LS_pro's premise mo_le MT (c_S cx) S2 0 ---- *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
(* ---- _pro.v's AR-free items that take section arguments, cited with them ---- *)
Local Notation oa_cost := (W_LLVMFuzzerTestOneInput_pro.oa_cost MT).

(* ---------------------------------------------------------------- op_add
   _pro.v:119-160's copy of W2's oa_post / oa_spec / oa_spec_g over ARx (Hp after S, Hp' after S'): the text of
   lib/A/W_op_add.v:264-309 oa_post_x / oa_spec_x and :1942 oa_spec_g_x (at the room record RP), written with _pro.v's names (oa_first, oa_kept,
   oa_FP, oa_cost, ...), which are W_op_add.v's texts. The Section hypothesis W2_op_add is W_op_add.v's oa_spec_g_x
   itself; oa_spec_g_x_of_kit reads it at these local names (the two are convertible). *)
Definition oa_post_x (G : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
(os : list Z) (n0 T : Z) (es : list rentry) (kr : nat) : world segs -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' kk,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal_gx_x segs B PST ARx G 0 [] OA_STK (spZ regs) (oa_FP os T es) ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\ oa_kept G os W mem W' mem' /\ frames S' = frames S /\ rp_RM RP S' kr /\
match oa_first os with
| None => ly' = ly /\ S' = S /\ W' = W /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - OA_STK <= a < spZ regs) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a)
| Some i => exists (q T' : Z) (pj : list byte),
    asrc_at B ly' S' W' mem' (oa_HA i) (oa_new_src (100 + n0) q pj) /\
    val_mem segs (arm W' mem') A_NFD 4 (n0 + 1) /\
    arelay_at B fr_globals ly' S' W' mem' T' (es ++ [ra_new (100 + n0)]) /\
    alock_at fr_globals W' mem' false /\
    ((T = 0 /\ Permutation (ablocks B ly' S') ((T', ATABLE) :: (q, APARTIAL) :: ablocks B ly S)) \/
     (T <> 0 /\ T' = T /\ Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S))) /\
    mo_le MT S S' oa_cost
end /\
(forall i, 0 <= i < 4 -> aview segs (w_H W') mem' (as_errno B + i) = aview segs (w_H W) mem (as_errno B + i)).
Definition oa_spec_x (G : list (Z * Z)) (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch (os : list Z) (n0 T : Z) (es : list rentry),
afn_pre_x segs B ARx OA_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
count_cid 0 (frames S) < fs_frames 0 ->
length os = 4%nat ->
(forall i, (i < 4)%nat -> 0 <= nth i os 0 < 2 ^ 31) ->
(forall i, (i < 4)%nat -> val_mem segs (arm W mem) (oa_HA i + 4) 4 (nth i os 0)) ->
(forall i, (i < 4)%nat -> nth i os 0 = 0 -> asrc_closed W mem (oa_HA i)) ->
val_mem segs (arm W mem) A_NFD 4 n0 -> 0 <= n0 <= 512 ->
azs B (rg_s fr_globals) (4 * ASRC) ->
(forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G a) ->
(forall a, A_NFD <= a < A_NFD + 4 -> inG G a) ->
(forall a, inG (RA_G fr_globals) a -> inG G a) ->
ra_rel B fr_globals ly S W mem T es ->
alock_at fr_globals W mem false -> awake_at fr_globals W mem ->
rom_view segs W mem ->
(oa_first os <> None -> (length es < 4)%nat /\ ~ In (100 + n0) (map re_fd es)) ->
blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX ->
mo_ok MT S oa_cost ->
forall kr : nat,
rp_RM RP S (W_op_add.oa_rk + kr) ->
cnt_ok_pk RP W_op_add.oa_peak (ablocks B ly S) ->
SRr segs W (cfg_at segs pc regs mem md) (oa_post_x G regs ly S Hp W mem md os n0 T es kr).
Definition oa_spec_g_x (pc : Z) : Prop := forall G, gx_prog_x B ARx G -> oa_spec_x G pc.
Lemma oa_spec_g_x_of_kit : forall pc, W_op_add.oa_spec_g_x (PI := PB_fr) B PST ARx MT RP pc -> oa_spec_g_x pc.
Proof. intros pc H G HGP. exact (H G HGP). Qed.

(* ---------------------------------------------------------------- SEG_PRO's own hypotheses, in _pro.v's order *)
(* op_add: W2's contract at the kit's form (lib/A/W_op_add.v:2936 oa_spec_g_x; _pro.v:161's W2_op_add over ARx) *)
Hypothesis W2_op_add : W_op_add.oa_spec_g_x (PI := PB_fr) B PST ARx MT RP (BASE + AF_fr_op_add).
Hypothesis TL : PALib B.                            (* the allocator instance (W_kit.v) *)
Hypothesis TLF : PALibF B.                          (* its fake-stack fields (W_frame.v) *)
(* the stack_malloc seat's Section fsp hypotheses (W_frame_x.v:747-759, verbatim), in place of _pro.v's ML / SMP *)
Hypothesis OWNLOW : ARx_owned_low_law segs B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law segs ARx WFx.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
(* _pro.v:168-169 over ARx: W_frame_x.v:763 astack_malloc_pres_x at class 1 and :69 frame_flag_lawP_x *)
Hypothesis ASM1 : astack_malloc_pres_x segs B ARx 1.
Hypothesis FFL : frame_flag_lawP_x segs B ARx.
(* _cut's two shared facts: glob_wr_law verbatim, errno_law at cut_x's errno_law_x *)
Hypothesis GWL : glob_wr_law G_fr.
Hypothesis ERRL : errno_law_x B ARx.
(* ---- instance facts, in _top.v's text (HEV, HZS: AF0m's ts_errno / ts_zsh, measured in _G.v's header) ---- *)
Hypothesis HEV : as_errno B = TFIB_ERRNO_A.
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
(* ---- G_fr: it holds the program's 20 objects (_G.v obj_c proves it of G_fr_c), and no read-only byte (_G.v
   c_rom_apart) ---- *)
Hypothesis HG_obj : forall a, inG G_fr_obj a -> inG G_fr a.
Hypothesis HROM_G : forall a, in_rom segs a -> ~ inG G_fr a.
(* ---- the instance obligation of W_journal.v's rom_out (a working branch 45a3cc9bdd0): an owned read-only byte
   is one of AR's pinned const cells (AF0m pins all 408) ---- *)
Hypothesis ROM_PIN : forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a.
(* _pro.v:194 SHV_oa over ARx (gx_prog_x's last conjunct at G_oa; add_x's GSHV at ad_G = G_oa) *)
Hypothesis SHV_oa : forall ly S Hp (W : world segs) mem md a n, ARx ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG G_oa x) -> shadow_hull_vis (aview segs (w_H W) mem) a n.
(* ---- the entry's surviving blocks (the relay's table g_src and the controller's buffer g_out): apart from the input
   block and inside the entry's footprint fr_FP (_cut.v:124-128) over their REQUEST size, as the cut's ablocks_sep
   (req_size, a Theorem Labs lane's ruling 12:2xZ) and op_add's journal take them; an obligation of the instance's
   fr_live_pre / fr_FP (ablocks_fp-shaped, i.e. (fst b, fst b + req_size (snd b))) ---- *)
Hypothesis HFP_pro : forall cx Hp T c O mx cap out,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ra_rel B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) T [] ->
  aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c O mx (Z.of_nat (length O)) cap out ->
  (exists rest, Permutation (ablocks B (c_ly cx) (c_S cx))
     (input_blks cx ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out ++ rest)) /\
  (T <> 0 -> forall a, T <= a < T + req_size ATABLE -> inFP (lf_FP fr_FP cx) a) /\
  (forall b, In b (aout_blks cap out) -> forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a).
(* ---- the allocator-state invariant's facts op_add takes, at the state after the fake frame (LS_pro_oa), and the
   cut's two Variables at the first cut point (LS_pro, RI_pro): the model after op_add, k = 0 ---- *)
Hypothesis LS_pro_oa : forall cx Hp (S2 : astate) pos,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  mo_le MT (c_S cx) S2 0 ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S2 oa_cost.
Hypothesis RI_pro : forall cx Hp q T' pj c O cap out,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  RINV cx 0 (pro_m q T' pj c O cap out).
(* LS_pro at the PROPOSED text (a Theorem Labs lane 20:4xZ; W8Add's fr_LS_pro, a working branch f57b3e2d0ca
   lib/A/ReplyLS.v:571): the blocks after op_add are given with the entry's split at its table T0 (HFP_pro's first
   conjunct) and relay_add's two cases (T0 = 0: a new table T'; T0 <> 0: T' = T0), so LS's own rest can be built.
   The published premise (a bare disjunction of the two Permutations) gives no such split.  The room round (ruling
   (a)): the entry's xcnt_ok and HFH0 (fr_hblks is the entry's table and g_out buffer, the three harness reads SEG_PRO
   makes) sit inside the existential, the text of s5-r1d's TX_LS_pro_xok (commit 66e5beebeaa,
   lib/A/ReplyLS3cTopxPro.v:148) with LS -> LSx *)
Hypothesis LS_pro : forall cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 ->
  mo_le MT S2 S oa_cost ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  LSx cx 0 (pro_m q T' pj c O cap out) ly S.
(* the room round's count row for SEG_PRO (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c); lib/A/ReplyLScnt.v fr_cnt_pro at
   commit ba8e99b5bd2): op_add's count premise at the seat's state S2, whose blocks are the entry's.  The counts come
   from the entry's xcnt_ok (fr_lib_pre_cf_x's XCNT, at the entry's table T0 and g_out), not from LS *)
Hypothesis LS_cnt : forall cx T0 cap out (S2 : astate),
  ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) ->
  cnt_ok_pk RP W_op_add.oa_peak (ablocks B (c_ly cx) S2).
(* ---- forced by the generic relation and the placement PST (add_x's texts) ---- *)
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct). The text is W_kit_x.v's BLKN (add_x's). *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): the ROM-view lemma's premise; trivial at PST = [] *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
Local Notation pro_cov := (W_LLVMFuzzerTestOneInput_pro.pro_cov G_fr HG_obj).
Local Notation pro_rom_out := (W_LLVMFuzzerTestOneInput_pro.pro_rom_out B HEV ROM_PIN).
Local Notation pro_rom_out_fr := (W_LLVMFuzzerTestOneInput_pro.pro_rom_out_fr B G_fr HEV HROM_G ROM_PIN).
Local Notation G_oa_fr := (W_LLVMFuzzerTestOneInput_pro.G_oa_fr G_fr HG_obj).
Local Notation G_oa_rt := (W_LLVMFuzzerTestOneInput_pro.G_oa_rt B HEV).
Local Notation pro_extra := (W_LLVMFuzzerTestOneInput_pro.pro_extra B).
Local Notation pro_regs := (W_LLVMFuzzerTestOneInput_pro.pro_regs B).
Local Notation G_obj_err := (W_LLVMFuzzerTestOneInput_pro.G_obj_err B HEV).
Local Notation pro_ks := (W_LLVMFuzzerTestOneInput_pro.pro_ks B).

(* ---------------------------------------------------------------- the walk at the empty ghost list
   HP0: every ARx state's ghost list is [], so the walk runs at Hp = []: AR0 is _pro.v's AR, AJ0 its journal at G,
   AJi0 the plain journal, AFN0 its afn_pre, LFB0 its lf_base *)
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
(* the AR laws _pro.v cites, at AR0 (cgif's al_* -> AR_laws_x's alx_*, YCbq.v's lemmas -> their _x twins) *)
Local Notation al0_const ly S W mem md := (alx_const _ _ _ LAWS ly S [] W mem md).
Local Notation al0_frames ly S W mem md := (alx_frames _ _ _ LAWS ly S [] W mem md).
Local Notation al0_sep ly S W mem md := (alx_sep _ _ _ LAWS ly S [] W mem md).
Local Notation frames_bounds0 ly S W mem md := (frames_bounds_x _ _ _ LAWS ly S [] W mem md).
Local Notation blk_img0 ly S W mem md := (blk_img_x _ _ _ LAWS ly S [] W mem md).
(* cgif's al_blocks at AR0: ARx_blocks_law's six conjuncts and BLKN's size *)
Lemma al0_blocks : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
  (forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.
(* W_frame_x's IMGC (W_kit.v:52 pa_img_cover over ARx): small_x's sm_imgc_x, from the image law alx_img *)
Let IMGCx := W_LLVMFuzzerTestOneInput_small_x.sm_imgc_x B XM_LIB XN_LIB RLO ARx LAWS.
(* W_journal.v:399 ajournal_gx_rom_view at AJ0: W_journal_x's, whose ROM-off-PST premise HPST gives *)
Lemma ajournal_gx_rom_view0 : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs)
    mem' md' k,
  AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  rom_out segs B G -> rom_view segs W mem -> rom_view segs W' mem'.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR Hrv.
  apply (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low G XO OUT STK sp0 FP ly S [] W mem md own ly' S' []
    W' mem' md' k HJ HR); [|exact Hrv].
  intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr].
Qed.
(* YCbq.v:2602 region_kept_stack_aj over ajournal_x (its proof: the journal's presence and stack clauses) *)
Lemma region_kept_stack_aj_x : forall E lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (Er : Z -> Prop)
    n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
  acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er ->
  ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
  bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
  region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
  intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k
    (K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & HQT).
  pose proof asan_consts as (C1 & _).
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
  - apply (mbyte_of_aview segs). apply K1; lia.
  - intros _. apply (apresent_writable segs). apply Hpres. lia.
Qed.
(* _pro.v:238-244 and :355-360, restated (the runs over the generic chain: the first one at G = [], W1Verify's
   template; the plain one W_frame_x's SRr_run_pi_AJ_x) *)
Let HG_client := pro_cov (rg_client fr_RG) 4 ltac:(vm_compute; reflexivity).
Let HG_cbroken := pro_cov (rg_client_broken fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HG_nfd := pro_cov A_NFD 4 ltac:(vm_compute; reflexivity).
Let HG_smax := pro_cov (rg_send_max fr_RG) 8 ltac:(vm_compute; reflexivity).
Let HG_gone := pro_cov (rg_gone fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HG_sdead := pro_cov (rg_send_dead fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HG_seintr := pro_cov (rg_send_eintr fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let HG0 : gx_ok segs B [] := gx_ok_nil segs B.
Let RUN0 := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS [] HG0 0 [].
Let RUNP := SRr_run_pi_AJ_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS.
Let RUNX := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTOX := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
(* _pro.v's section-local tactics, restated *)
Ltac pro_keep HS idxs :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (YP03.pick (ss_mem ssx) idxs) in
  let HSk := fresh "HSk" in
  pose proof (st_ok_pi_submem (PI := PB_fr) Ex ssx msx rs HS ltac:(submem_tac) ltac:(vm_compute; reflexivity)) as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.
Ltac pro_ro HS i :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let r := eval vm_compute in (nth i (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  let HSk := fresh "HSk" in
  pose proof (ast_ok_pi_set_region (PI := PB_fr) Ex ssx msx i r (set_window r 0 0) HS eq_refl eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow sg Ex _ r 0 0 (st_ok_pi_region_nth (PI := PB_fr) Ex ssx msx i r HS eq_refl) ltac:(intros o Ho; lia)))
    as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.
Ltac pro_val :=
  repeat match goal with |- context [VAL ?a] =>
    let a' := eval vm_compute in a in
    let v := eval vm_compute in (VAL a') in
    let Hv := fresh "Hval" in
    assert (Hv : VAL a = v) by (vm_compute; reflexivity); rewrite Hv; clear Hv end.
Ltac pro_img HEI :=
  repeat match goal with |- context [bv_unsigned (ew ?E ?a)] =>
    let a' := eval vm_compute in a in
    lazymatch eval vm_compute in ((A_TEXT <=? a') && (a' <? A_LIM))%nat with
    | true => rewrite (HEI a ltac:(unfold A_HI, A_OBJ, A_TEXT, A_LIM; lia))
    end end;
  pro_val.
Ltac pro_imgh HEI H :=
  repeat match type of H with context [bv_unsigned (ew ?E ?a)] =>
    let a' := eval vm_compute in a in
    lazymatch eval vm_compute in ((A_TEXT <=? a') && (a' <? A_LIM))%nat with
    | true => rewrite (HEI a ltac:(unfold A_HI, A_OBJ, A_TEXT, A_LIM; lia)) in H
    end end;
  repeat match type of H with context [VAL ?a] =>
    let a' := eval vm_compute in a in
    let v := eval vm_compute in (VAL a') in
    let Hv := fresh "Hval" in
    assert (Hv : VAL a = v) by (vm_compute; reflexivity); rewrite Hv in H; clear Hv end.
Ltac pro_addg HS HEI j off w HGx :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let HSk := fresh "HSk" in
  pose proof (st_ok_pi_add_region Ex ssx msx (pr_g j off w) HS eq_refl
    ltac:(unfold region_ok, pr_g; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
          pro_img HEI; split; [lia|]; split; [lia|]; split; [|constructor];
          intros o Ho; cbn [ms_mem restrict mkst]; apply GWL; apply HGx; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, pr_g; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          repeat match goal with H : bv_unsigned (ew ?E ?a) = _ |- context [bv_unsigned (ew ?E ?a)] => rewrite H end;
          pro_img HEI;
          unfold SB, off_img in *; repeat split; lia)) as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.
Ltac pro_addf HS HEI n :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let v := eval vm_compute in (VAL n) in
  let HSk := fresh "HSk" in
  pose proof (st_ok_pi_add_fact Ex ssx msx n (mkAF v v 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
          rewrite (HEI n ltac:(unfold A_TEXT, A_LIM; lia)); pro_val;
          rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.
Ltac pro_rgn HS i HR :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth i (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (st_ok_pi_region_nth (PI := PB_fr) Ex ssx msx i r HS eq_refl) as HR end.
Ltac pro_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Ltac pro_rwimg HEI n :=
  let v := eval vm_compute in (VAL n) in
  rewrite (HEI n ltac:(unfold A_TEXT, A_LIM; lia));
  replace (VAL n) with v by (vm_compute; reflexivity).
Ltac pro_nwr_k HEIx Ha HFlo HFsp :=
  let r := fresh "r" in let Hin' := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin' & Hr);
  lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end;
  cbn [In] in Hin';
  repeat (destruct Hin' as [<- | Hin'];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      repeat match goal with Hu : bv_unsigned (ew ?E ?x) = _ |- _ =>
        match type of Hr with context [bv_unsigned (ew E x)] => rewrite Hu in Hr end end;
      pro_imgh HEIx Hr; unfold SB in Hr;
      first [ clear - Hr; lia
            | clear - Hr Ha HFlo HFsp; lia
            | match goal with Hk : ~ (_ <= _ < _) |- _ => clear - Hr Hk; lia end
            | match goal with Hk : (_ \/ _) |- _ => clear - Hr Hk; lia end ] | ]);
  destruct Hin'.

Lemma G_oa_prog_x : gx_prog_x B ARx G_oa.
Proof.
  split; [exact (gx_ok_sub segs B G_oa G_fr G_oa_fr HG)|].
  split; [exact G_oa_rt|].
  split; [apply pro_rom_out; intros a Ha; exact (rom_apart_ok segs G_oa a ltac:(vm_compute; reflexivity) Ha)|].
  split.
  { intros a Ha.
    pose proof (rng_all_in (fun x => match seg_rom segs (Z_to_bv 64 x) with Some _ => true | None => false end)
      G_oa a ltac:(vm_compute; reflexivity) Ha) as H.
    cbv beta in H. destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | discriminate H]. }
  split; [intros a Ha m; apply pro_wr_any; apply (segwb_ok segs);
          exact (rng_all_in (segwb segs) G_oa a ltac:(vm_compute; reflexivity) Ha)|].
  exact SHV_oa.
Qed.

Lemma pro_entry_x : forall W ly S regs mem md ch n,
  AFN0 LLVMF_STK ly S W regs mem md ch -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 26 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (pro_extra regs))) ss_pro0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_pro)) mem (seg_rom segs)))
  /\ sh_ok segs Bx [] (Eimg (Ereg regs (pro_extra regs))) (mrestrict (w_H W) mem).
Proof.
  intros W ly S regs mem md ch n HPRE H11 Rn.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity.
  destruct (al0_const ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
  pose proof (palf_uar_img B TLF) as HuR. pose proof (palf_uar_al B TLF) as HuA. pose proof (palf_sep B TLF) as HSEP.
  cbn [zseps zseps_from fst snd] in HSEP.
  set (F := pro_F regs).
  assert (HFv : F = spZ regs - 320 \/ F = spZ regs - 336) by exact (pro_F_facts (spZ regs) Hal16).
  assert (HFal : F mod 32 = 0) by exact (pro_F_al (spZ regs - 320)).
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (pro_extra regs))). pose proof pa_B_ok as HBASE.
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E11 : ew E 11 = getr regs 11) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (E273 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (HspR : 2 ^ 46 <= F /\ spZ regs <= 2 ^ 47).
  { revert HFv Hslo Hshi H47 Hceil C1 C3 WS Hstk0. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
  assert (UF : bv_unsigned (ew E 34) = F) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
  { intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
  split.
  - unfold ss_pro0, A_pro. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold pro_regions0, pr_zero, pr_save, pr_F, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * cbn [base_val]. rewrite UF. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
          [cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (VAL (A_OBJ 32)) 0 8 (SOff 33 0) SB);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
      * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff 32 0) (as_uar_cell B));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
      * rewrite (VB 32%nat (as_uar_cell B) E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
    + apply pairwise_disjoint_of_extents.
      unfold pro_regions0, pr_zero, pr_save, pr_F, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia).
      rewrite (VB 32%nat (as_uar_cell B) E32) by lia. cbn [base_val]. rewrite Usp, UF.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert HFv HspR Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR HguR HuR HSEP. clear.
      unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [pro_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite Usp, UF, E11, H11, E32, E33, !unsigned_lit_small by (unfold SB; lia).
        change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
        revert HFv HFal HspR Hal16 Rn HuR HuA. clear. unfold SB. intros.
        repeat match goal with |- _ /\ _ => split end; lia.
      * cbn [pro_facts0 f_alias alias_ok pro_alias]. split; [|exact I].
        assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
        apply U_inj. rewrite U_SAlu, (U_atom_off E 2 (spZ regs) (-320) E2'), (U_atom E 34 F E34) by lia.
        rewrite U_SLit. cbn [zalu_raw].
        assert (Hlo : 0 <= spZ regs + -320 < 2 ^ 64) by (destruct HspR as [HspR1 HspR2]; destruct HFv as [HFv | HFv]; rewrite HFv in HspR1; lia).
        change (zcanon (-32)) with (2 ^ 64 - 2 ^ 5). rewrite (land_neg_pow2_u64 (spZ regs + -320) 5 Hlo ltac:(lia)).
        assert (EF : spZ regs + -320 - (spZ regs + -320) mod 2 ^ 5 = F) by reflexivity.
        rewrite EF. apply zcanon_id. unfold M64. destruct HspR as [HspR1 HspR2]. destruct HFv as [HFv | HFv]; lia.
  - unfold sh_ok. constructor.
Qed.

(* ------------------------------------------------------------------ the frame's numbers *)
Lemma pro_Fb_x : forall cx, LFB0 cx ->
  CEIL8 + 32000 <= lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) /\ spZ (c_regs cx) - 352 <= lf_F cx /\
  spZ (c_regs cx) <= 2 ^ 47 /\ lf_F cx mod 32 = 0 /\ spZ (c_regs cx) mod 16 = 0.
Proof.
  intros cx (_ & HPRE0).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  pose proof (pro_F_al (spZ (c_regs cx) - 320)) as Hal32. rewrite <- HF32 in Hal32.
  assert (HFlo : CEIL8 + 32000 <= lf_F cx) by (unfold CEIL8, LLVMF_STK in *; lia).
  split; [exact HFlo|]. split; [lia|]. split; [lia|]. split; [unfold LLVMF_STK in *; lia|].
  split; [exact Hal32 | exact Hal16].
Qed.

Lemma pro_frame_wr_x : forall cx own ly3 S3 k (W : world segs) mem md,
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k ->
  forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a.
Proof.
  intros cx own ly3 S3 k W mem md (_ & _ & (memS & HJi & _) & _) a Ha. rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  apply (apresent_writable segs). apply Hpres. lia.
Qed.

(* ------------------------------------------------------------------ 0x84234-0x842a0: the loop's set-up *)
Lemma pro_fin_x : forall cx (W : world segs) regs mem md ly3 S3 k m fpos,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  pro_fr cx (frame_addr ly3 1 fpos) W mem -> pro_regs cx (frame_addr ly3 1 fpos) regs ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m -> lm_k m = 0 -> ainput_at B cx ly3 S3 W mem -> rom_view segs W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx 0 m ly3 S3 -> NP S3 -> RINV cx 0 m ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_pro_ret)) mem (seg_rom segs)) md)
    (fun W' c' => INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx [] 0 W' c' \/ INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx [] W' c').
Proof.
  intros cx W regs mem md ly3 S3 k m fpos HB HJ HFR HRG HFLG HMOD Hk0 HIN HRV HSEP HLS HNP HRI.
  pose proof (pro_Fb_x cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity.
  pose proof HB as (HAI0 & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (Hn26 : 0 <= c_n cx < 2 ^ 26)
    by (unfold fr_lib_pre_cf_x in HPRE0; destruct HPRE0 as (_ & _ & _ & _ & [(H0 & _) | (H0 & _)] & _); lia).
  set (FF := frame_addr ly3 1 fpos) in *. set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin1 : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct (frames_bounds0 ly3 S3 W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  destruct (al0_frames ly3 S3 W mem md 1 fpos HAR Hin1) as (HFFal & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1, HFFal.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  pose proof HFR as (HSV & H24 & H48 & H56 & H64 & H72 & H80 & H88 & H184 & HH0 & HH8 & HH16 & HFW & HSH & HSW).
  pose proof HRG as (R2 & R8 & R9 & R21 & R22 & R24 & R26 & R3 & R4).
  assert (HDIV : val_mem segs (arm W mem) 0x10320 8 DIV10)
    by (apply (rom_vmb_ok W mem _ _ _ HRV); vm_compute; reflexivity).
  assert (HWR : forall a, F + 32 <= a < F + 160 -> writable_at segs (arm W mem) a)
    by (intros a Ha; apply (pro_frame_wr_x cx _ _ _ _ W mem md HJ); unfold sp0 in *; lia).
  destruct (pro_entry2 W regs mem F FF R9 ltac:(lia) ltac:(lia) HFal ltac:(lia) HFFal H88 HDIV HWR) as [HS SHOK].
  remember (Eimg (Ereg regs (pro2_extra FF))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (pro2_extra FF)) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  assert (E21 : ew E 21 = Z_to_bv 64 (c_n cx))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
  assert (E24 : ew E 24 = Z_to_bv 64 (SB + FF / 8))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E33 : ew E 33 = Z_to_bv 64 FF)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  clear HE.
  pose proof pro_vals as (PV67 & PV68 & PV69 & PV70 & PV71 & PV72 & PV73 & PV74 & PV75 & PV76 & PV77 & PV78 &
    PVO22 & PVO25 & PVO26 & PVO0 & PVO32).
  assert (VI : forall j v, VAL (A_HI j) = v -> (A_HI j < A_LIM)%nat -> 0 <= v < 2 ^ 64 -> ew E (A_HI j) = Z_to_bv 64 v).
  { intros j v Hv Hj Hr. apply bv_eq. rewrite (HEI (A_HI j) ltac:(unfold A_HI, A_TEXT in *; lia)).
    rewrite unsigned_lit_small by exact Hr. exact Hv. }
  (* every fact of the cut but the slots the set-up stores, for any memory that keeps the bytes outside them *)
  assert (Herr : 0 <= as_errno B /\ as_errno B + 4 <= CEIL8) by (rewrite HEV; unfold TFIB_ERRNO_A, CEIL8; lia).
  assert (KEEPF : forall mf, (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (F + 96 <= a < F + 160) ->
      abyte_kept W mem W mf a) ->
    amodel_at B ly3 S3 W mf m /\ ainput_at B cx ly3 S3 W mf /\ rom_view segs W mf /\ jt_rom W mf /\
    pro_fr cx FF W mf /\ sv8 W mf (FF + 120) (flag_addr ly3 1 fpos)).
  { intros mf KO.
    assert (KL : forall a, 0 <= a < CEIL8 -> abyte_kept W mem W mf a)
      by (intros a Ha; apply KO; unfold CEIL8 in *; lia).
    assert (HRVf : rom_view segs W mf) by exact (lt_rom_kept W W mem mf HRV KL).
    split; [exact (W_LLVMFuzzerTestOneInput_latch_x.lt_amodel_kept_x B ARx LAWS ly3 S3 [] W mem md W mf m HAR HMOD (proj1 Herr) (proj2 Herr) KL)|].
    split; [exact (W_LLVMFuzzerTestOneInput_latch_x.lt_ainput_kept_x B ARx LAWS cx ly3 S3 [] W mem md W mf HAR HIN (eq_sym HlenP) KL)|].
    split; [exact HRVf|]. split; [exact (pro_jt W mf HRVf)|].
    assert (KH : forall a v, (forall x, a <= x < a + 8 -> abyte_kept W mem W mf x) -> sv8 W mem a v -> sv8 W mf a v)
      by (intros a v Hk Hv; exact (lt_sv8_kept W W mem mf a v Hk Hv)).
    split; [|apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HFLG]].
    split; [intros o r Hor; apply KH; [|exact (HSV o r Hor)]; intros x Hx;
            unfold saved_regs in Hor; cbn [In] in Hor;
            repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; apply KO; unfold sp0 in *; lia|]);
            destruct Hor|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H24]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H48]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H56]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H64]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H72]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H80]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H88]|].
    split; [apply KH; [intros x Hx; apply KO; unfold sp0 in *; lia | exact H184]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH0]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH8]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH16]|].
    split; [apply (akept_awr W mem W mf); [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HFW]|].
    split; [apply (akept_garr8 W mem W mf); [intros x Hx; apply KL; cbn [length fake_shadow] in Hx;
            pose proof (Z.div_le_upper_bound FF 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SB, CEIL8 in *; lia
            | exact HSH]|].
    apply (akept_awr W mem W mf); [intros x Hx; apply KL;
      pose proof (Z.div_le_upper_bound FF 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SB, CEIL8 in *; lia | exact HSW]. }
  paj_run_tok_x RUNX HS HJ SHOK Bspan.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr;
        first [ lia | left; split; [left; unfold sp0 in *; lia | lia] ] | ]).
    destruct Hin'. }
  clear HF.
  lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) =>
    assert (KO1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (F + 96 <= a < F + 160) ->
      abyte_kept W m1 W m2 a) end.
  { intros a Ha H1 H2. apply (pro_kept_frame E _ W _ _ a HFr Ha). intros (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]).
    destruct Hin'. }
  clear HFr.
  psrr_branch_tok RUNX BR HS SHOK Bspan.
  - (* beqz s5: an empty input goes to the shutdown block *)
    assert (Hn0 : c_n cx = 0).
    { rewrite branch_eq_U, (U_atom E 21 (c_n cx) E21), U_lit in Hc by lia. apply Z.eqb_eq in Hc. exact Hc. }
    paj_run_to_tok_x RUNTOX HS HJ SHOK Bspan AF_LLVM_exit.
    { intros a (r & Hin' & Hr).
      lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
      cbn [In] in Hin'.
      repeat (destruct Hin' as [<- | Hin'];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr;
          first [ lia | left; split; [left; unfold sp0 in *; lia | lia] ] | ]).
      destruct Hin'. }
    clear HF.
    lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) =>
      assert (KO2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (F + 96 <= a < F + 160) ->
        abyte_kept W m1 W m2 a) end.
    { intros a Ha H1 H2. apply (pro_kept_frame E _ W _ _ a HFr Ha). intros (r & Hin' & Hr).
      lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
      cbn [In] in Hin'.
      repeat (destruct Hin' as [<- | Hin'];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]).
      destruct Hin'. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (pro2_extra FF) pro_kept HS HAE
      ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
    pro_rgn HS 2%nat HR96.
    pmkst HS.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rf _ ?mf _; cfg_model := ?df |} _ =>
      apply SRr_ret; right; exists rf, mf, df, 0 end.
    split; [reflexivity|].
    lazymatch type of KO2 with forall a, _ -> _ -> _ -> abyte_kept _ _ _ ?m2 _ =>
      destruct (KEEPF m2 (fun a H0 H1 H2 => abyte_kept_trans W W W _ _ _ a (KO1 a H0 H1 H2) (KO2 a H0 H1 H2)))
        as (HMODf & HINf & HRVf & HJTf & HFRf & HFLf) end.
    split; [exact HJTf|].
    exists [(1, fpos)], ly3, S3, [], k, m, fpos.
    split; [exact HJ|]. split; [reflexivity|].
    split.
    { apply (pro_aframe cx false FF W _ HFRf).
      - pose proof (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 96 8 (SOff 24 0) (SB + FF / 8) HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E24, unsigned_lit_small, Z.add_0_r by (unfold SB; lia);
                 reflexivity) ltac:(unfold SB in *; zside) ltac:(zside)) as V96.
        exact V96.
      - intros Hf. discriminate Hf.
      - exact (pro_frame_wr_x cx _ _ _ _ W _ _ HJ).
      - lia.
      - lia. }
    split; [exact HFLf|].
    split; [exact HMODf|]. split; [exact HINf|]. split; [exact HRVf|].
    split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
    unfold lregs_X.
    split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite Q18; change 355%nat with (A_HI 75); apply VI; [exact PV75 | cbv; lia | unfold HI_G_SRC; lia]|].
    split; [rewrite Q23; change 354%nat with (A_HI 74); apply VI; [exact PV74 | cbv; lia | unfold HI_G_NSRC; lia]|].
    split; [rewrite Q25; change 356%nat with (A_HI 76); apply VI; [exact PV76 | cbv; lia | unfold HI_G_NOUT; lia]|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    split; [rewrite Hk0; lia | unfold OPS_MAX; lia].
  - (* the loop head *)
    assert (Hn0 : c_n cx <> 0).
    { rewrite branch_eq_U, (U_atom E 21 (c_n cx) E21), U_lit in Hc by lia. apply Z.eqb_neq in Hc. exact Hc. }
    paj_run_to_tok_x RUNTOX HS HJ SHOK Bspan AF_LLVM_head.
    { intros a (r & Hin' & Hr).
      lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
      cbn [In] in Hin'.
      repeat (destruct Hin' as [<- | Hin'];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr;
          first [ lia | left; split; [left; unfold sp0 in *; lia | lia] ] | ]).
      destruct Hin'. }
    clear HF.
    lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) =>
      assert (KO2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (F + 96 <= a < F + 160) ->
        abyte_kept W m1 W m2 a) end.
    { intros a Ha H1 H2. apply (pro_kept_frame E _ W _ _ a HFr Ha). intros (r & Hin' & Hr).
      lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
      cbn [In] in Hin'.
      repeat (destruct Hin' as [<- | Hin'];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]).
      destruct Hin'. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (pro2_extra FF) pro_kept HS HAE
      ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
    prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7. prreg HS (19%bv : bv 5) Q19.
    prreg HS (20%bv : bv 5) Q20. prreg HS (27%bv : bv 5) Q27.
    pro_rgn HS 0%nat HR32. pro_rgn HS 2%nat HR96.
    assert (Hgs : rg_s fr_RG = 0x5d88e0) by (vm_compute; reflexivity).
    assert (E263 : ew E (A_OBJ 22) = Z_to_bv 64 (rg_s fr_RG))
      by (apply bv_eq; rewrite (HEI (A_OBJ 22) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
          rewrite unsigned_lit_small by (rewrite Hgs; lia); rewrite PVO22, Hgs; reflexivity).
    change (A_OBJ 22) with 263%nat in E263.
    pose proof (pro_sh_den E 26 263 SB (rg_s fr_RG) 0 E26 E263 ltac:(unfold SB; lia) ltac:(lia) ltac:(lia)) as D112.
    pose proof (pro_sh_den E 26 263 SB (rg_s fr_RG) 4 E26 E263 ltac:(unfold SB; lia) ltac:(lia) ltac:(lia)) as D152.
    rewrite Z.add_0_r in D112.
    pmkst HS.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rf _ ?mf _; cfg_model := ?df |} _ =>
      apply SRr_ret; left; exists rf, mf, df end.
    split; [reflexivity|].
    lazymatch type of KO2 with forall a, _ -> _ -> _ -> abyte_kept _ _ _ ?m2 _ =>
      destruct (KEEPF m2 (fun a H0 H1 H2 => abyte_kept_trans W W W _ _ _ a (KO1 a H0 H1 H2) (KO2 a H0 H1 H2)))
        as (HMODf & HINf & HRVf & HJTf & HFRf & HFLf) end.
    split; [exact HJTf|].
    exists [(1, fpos)], ly3, S3, [], k, m, fpos.
    split; [exact HJ|]. split; [reflexivity|].
    split.
    { apply (pro_aframe cx true FF W _ HFRf).
      - exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 96 8 (SOff 24 0) (SB + FF / 8) HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E24, unsigned_lit_small, Z.add_0_r by (unfold SB; lia);
                 reflexivity) ltac:(unfold SB in *; zside) ltac:(zside)).
      - intros _.
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 32 40 32 40 32 8 (SOff 263 0) (rg_s fr_RG) HR32 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E263, unsigned_lit_small, Z.add_0_r by lia;
                 reflexivity) ltac:(zside) ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 104 8 (SOff 356 0) HI_G_NOUT HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
                 change 356%nat with (A_HI 76); apply VI; [exact PV76 | cbv; lia | unfold HI_G_NOUT; lia])
          ltac:(unfold HI_G_NOUT; zside) ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 112 8
          (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 263 0) (SLit 3))) (SB + rg_s fr_RG / 8) HR96 U9
          ltac:(cbn [In]; tauto) D112 ltac:(rewrite Hgs; unfold SB; change (6129888 / 8) with 766236; zside)
          ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 120 8 (SOff 354 0) HI_G_NSRC HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
                 change 354%nat with (A_HI 74); apply VI; [exact PV74 | cbv; lia | unfold HI_G_NSRC; lia])
          ltac:(unfold HI_G_NSRC; zside) ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 128 8 (SOff 263 4) (rg_s fr_RG + 4) HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E263, unsigned_lit_small by lia; reflexivity)
          ltac:(zside) ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 136 8 (SLit DIV10) DIV10 HR96 U9
          ltac:(cbn [In]; tauto) eq_refl ltac:(unfold DIV10; zside) ltac:(zside))|].
        exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 152 8
          (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 263 4) (SLit 3))) (SB + (rg_s fr_RG + 4) / 8) HR96 U9
          ltac:(cbn [In]; tauto) D152 ltac:(rewrite Hgs; unfold SB; change ((6129888 + 4) / 8) with 766236; zside)
          ltac:(zside)).
      - exact (pro_frame_wr_x cx _ _ _ _ W _ _ HJ).
      - lia.
      - lia. }
    split; [exact HFLf|].
    split; [exact HMODf|]. split; [exact HINf|]. split; [exact HRVf|].
    split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
    unfold lregs_H, lregs_common.
    split.
    { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
      split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
      split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
      split; [rewrite Q18; change 355%nat with (A_HI 75); apply VI; [exact PV75 | cbv; lia | unfold HI_G_SRC; lia]|].
      split; [rewrite Q19, E33, unsigned_lit_small by lia; reflexivity|].
      split; [rewrite Q20; reflexivity|].
      split; [rewrite Q23; change 354%nat with (A_HI 74); apply VI; [exact PV74 | cbv; lia | unfold HI_G_NSRC; lia]|].
      split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
      split; [rewrite Q25; change 356%nat with (A_HI 76); apply VI; [exact PV76 | cbv; lia | unfold HI_G_NOUT; lia]|].
      split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
      split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
      rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4. }
    split; [rewrite Q6; reflexivity|]. split; [rewrite Q7; reflexivity|].
    split; [rewrite (KR 21%bv ltac:(cbv; tauto)), Hk0, Z.sub_0_r; exact R21|].
    split; [rewrite (KR 22%bv ltac:(cbv; tauto)), Hk0, Z.add_0_r; exact R22|].
    split; [rewrite Q27; reflexivity|].
    split; [unfold OPS_MAX; lia|].
    rewrite Hk0. lia.
Qed.

(* ------------------------------------------------------------------ op_add's call: what the callee keeps *)
(* the live blocks are pairwise distinct (W_gesture_end.v ablocks_nodup), and two distinct ones are apart *)
Lemma pro_nodup_x : forall ly S (W : world segs) mem md, AR0 ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin.
    destruct (al0_blocks ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. apply req_size_pos. lia. }
  destruct (al0_sep ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.

Lemma pro_blk_disj_x : forall ly S (W : world segs) mem md x y, AR0 ly S W mem md ->
  In x (ablocks B ly S) -> In y (ablocks B ly S) -> x <> y ->
  fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x.
Proof.
  intros ly S W mem md x y HAR Hx Hy Hne.
  destruct (al0_sep ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hp Hx Hy. induction (ablocks B ly S) as [|b l IH]; intros Hp Hx Hy; [destruct Hx|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. rewrite Forall_forall in Hf.
  destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
  - exfalso. exact (Hne eq_refl).
  - pose proof (Hf _ (in_map (fun b => (fst b, req_size (snd b))) _ _ Hy)) as H.
    unfold zdisjoint in H. cbn [fst snd] in H. exact H.
  - pose proof (Hf _ (in_map (fun b => (fst b, req_size (snd b))) _ _ Hx)) as H.
    unfold zdisjoint in H. cbn [fst snd] in H. lia.
  - exact (IH Hp Hx Hy).
Qed.

(* what a callee taken at its own G keeps (W2's oa_call_keep / _blk / _hi, W_op_add.v:335-403), and the caller's
   fake frames (the journal's frame clause) *)
Lemma pro_call_img_x : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  AJ0 G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k -> ~ YI16.sink_open_fp FP ->
  forall a, in_img segs a -> ~ inG G' a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HJx Hsk a Him HnG Hno He.
  pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Him Hno He (HPST a Him) ltac:(apply fp_spares_closed; exact Hsk)).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.

Lemma pro_call_blk_x : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G' ->
  AJ0 G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall p n j, In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly1 S1) -> 0 <= j < req_size n ->
  ~ inFP FP (p + j) -> aview segs (w_H W1) m1 (p + j) = aview segs (w_H W0) m0 (p + j).
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx p n j H0 H1 Hj Hfp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 p n j H0 H1 Hj Hfp).
  destruct (al0_blocks ly1 S1 W1 m1 md1 p n HAR1 H1) as (_ & H4096 & Hbc & _).
  apply (aview_gagree segs G' (w_H W0) m0 memS (p + j) HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  exact (blk_img0 ly1 S1 W1 m1 md1 p n (p + j) HAR1 H1 ltac:(lia) (proj1 (HGok _ Hin))).
Qed.

Lemma pro_call_hi_x : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G' ->
  AJ0 G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx a Ha Hno.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  rewrite (F1 a Ha Hno).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.

Lemma pro_call_frm_x : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  AJ0 G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall cid pos a, In (cid, pos) (frames S0) ->
  (in_zr a (frame_rng ly0 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly0 cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ inG G' a -> aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HJx cid pos a Hin Hr Hfp Ha HnG.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cid pos a Hin Hr Hfp).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma pro_afn_pre_at_x : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
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
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* the fake frame keeps its place across a journal (frame_addr reads only ly_F, which layout_le keeps) *)
Lemma pro_ff_eq_x : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' W' mem' md' k cid pos,
  AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF.
  reflexivity.
Qed.

(* a live block and a fake frame are apart (AR_sep_law) *)
Lemma pro_blk_frm_x : forall ly S (W : world segs) mem md p n cid pos, AR0 ly S W mem md ->
  In (p, n) (ablocks B ly S) -> In (cid, pos) (frames S) ->
  p + req_size n <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= p.
Proof.
  intros ly S W mem md p n cid pos HAR Hb Hf.
  destruct (al0_sep ly S W mem md HAR) as [Hp _].
  pose proof (pro_pw_app zdisjoint _ _ _ _ Hp (in_map (fun b => (fst b, req_size (snd b))) _ _ Hb)
    (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hf)) as H.
  unfold zdisjoint in H. cbn [fst snd] in H. exact H.
Qed.

Lemma pro_blk_gst_x : forall ly S (W : world segs) mem md p n a, AR0 ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> pro_gst_out a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha. pose proof (blk_img0 ly S W mem md p n a HAR Hin Ha) as Hni.
  assert (HI : forall lo w, rng_inb lo w G_fr_obj = true -> ~ (lo <= a < lo + w))
    by (intros lo w Hr Hx; apply Hni; exact (proj1 (HG a (HG_obj a (rng_cover lo w G_fr_obj Hr a Hx))))).
  split; [intros Hx; refine (HI 0xa1fe0 4 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d87e0 1 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8820 4 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8840 8 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8860 1 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8880 1 _ _); [vm_compute; reflexivity | lia]|].
  intros Hx; refine (HI 0x5d88a0 1 _ _); [vm_compute; reflexivity | lia].
Qed.

(* ---- the room round: the entry's three harness cells (g_src, g_capout, g_out) read back as the relay's table and
   the stream's buffer; SEG_PRO's HFH0 and the identification of the pre's XCNT witnesses with fr_gi's ---- *)
Lemma prx_cells : forall ly S Hp (W : world segs) mem md T c O mx cap out,
  ARx ly S Hp W mem md ->
  ra_rel B fr_RG ly S W mem T [] ->
  aout_at B fr_RG ly S W mem c O mx (Z.of_nat (length O)) cap out ->
  rdword (aview segs (w_H W) mem) (rg_src fr_RG) = Some T /\
  rdword (aview segs (w_H W) mem) (rg_capout fr_RG) = Some cap /\
  rdword (aview segs (w_H W) mem) (rg_out fr_RG) = Some out.
Proof.
  intros ly S Hp W mem md T c O mx cap out HAR HRA HAO.
  pose proof asan_consts as (C1 & _).
  assert (BLK : forall p n, In (p, n) (ablocks B ly S) -> 0 <= p /\ 0 <= n /\ p + n < 2 ^ 64).
  { intros p0 n0 Hin.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p0 n0 HAR Hin) as (_ & H4096 & Hce & _).
    pose proof (BLKN ly S Hp W mem md p0 n0 HAR Hin) as Hn0.
    assert (Hrq : n0 <= req_size n0) by (unfold req_size; destruct (Z.eqb_spec n0 0); lia).
    lia. }
  assert (HT : rdword (aview segs (w_H W) mem) (rg_src fr_RG) = Some T).
  { destruct HRA as [(-> & _ & Hv & _) | (Hv & _ & _ & _ & _ & _ & _ & Hin & _)].
    - apply (W_frame.rdword_of_val_mem segs (w_H W) mem); [exact Hv | lia].
    - destruct (BLK T ATABLE Hin) as (H0 & H1 & H2).
      apply (W_frame.rdword_of_val_mem segs (w_H W) mem); [exact Hv | unfold ATABLE in *; lia]. }
  destruct HAO as (_ & _ & _ & _ & Hcap & _ & Hout & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & Hco).
  split; [exact HT|].
  destruct Hco as [(-> & -> & _) | (Hc & _ & Hin & _)].
  - split; (apply (W_frame.rdword_of_val_mem segs (w_H W) mem); [assumption | lia]).
  - destruct (BLK out cap Hin) as (H0 & H1 & H2).
    split; (apply (W_frame.rdword_of_val_mem segs (w_H W) mem); [assumption | lia]).
Qed.

(* ------------------------------------------------------------------ 0x84230 `jal op_add` *)
Lemma pro_mid_x : forall cx regs mem md S2 k fpos,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 (c_W cx) mem md k ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, fpos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 -> NP S2 ->
  pro_fr cx (frame_addr (c_ly cx) 1 fpos) (c_W cx) mem ->
  sv8 (c_W cx) mem (frame_addr (c_ly cx) 1 fpos + 120) (flag_addr (c_ly cx) 1 fpos) ->
  getr regs 1 = w64 (BASE + A_pro_ret) -> pro_regs cx (frame_addr (c_ly cx) 1 fpos) regs ->
  pro_glob (c_W cx) mem ->
  (forall a, pro_ks cx a -> aview segs (w_H (c_W cx)) mem a = aview segs (w_H (c_W cx)) (c_mem cx) a) ->
  SRr segs (c_W cx) (cfg_at segs (BASE + AF_fr_op_add) regs mem md)
    (fun W' c' => INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx [] 0 W' c' \/ INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx [] W' c').
Proof.
  intros cx regs mem md S2 k fpos HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HNP2 HFR HFLG Hra HRG HGL KEEP.
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & Hra0 & H10 & H11 & Hin & Hnl & Hgarr & Hfrs & Hlive & _ & _ & Hgi & Hrom & _).
  destruct Hgi as (HGP0 & HCL & (T & HRR) & (c0 & O & mx0 & cap & out & HAO) & (gn0 & HGN) & HLK & HWK & HTU &
    (lst & HLS0) & HLW).
  (* the room round: the pre's XCNT (its 22nd conjunct) at fr_gi's table T and g_out (cap, out), read off the same three
     cells (prx_cells), and HFH0 *)
  pose proof HPRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HXC0 & _).
  destruct HXC0 as (Tx & cx0 & Ox & mxx & capx & outx & HRRx & HAOx & HXC).
  pose proof (proj1 HPREE) as HARe.
  destruct (prx_cells _ _ _ _ _ _ T c0 O mx0 cap out HARe HRR HAO) as (CT & CC & CO).
  destruct (prx_cells _ _ _ _ _ _ Tx cx0 Ox mxx capx outx HARe HRRx HAOx) as (CTx & CCx & COx).
  rewrite CT in CTx. rewrite CC in CCx. rewrite CO in COx.
  injection CTx as <-. injection CCx as <-. injection COx as <-. clear HRRx HAOx.
  change (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)]) with (input_blks cx) in HXC.
  assert (HFH0 : fr_hblks (c_W cx) (c_mem cx) = (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out).
  { unfold fr_hblks. cbv zeta. change tfibsegs with segs. rewrite CT, CO, CC. unfold aout_blks. reflexivity. }
  pose proof (pro_Fb_x cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof (HFP_pro cx [] T c0 O mx0 cap out HB HRR HAO) as ((rest0 & HPERM0) & HFPT & HFPO).
  set (W := c_W cx) in *. set (FF := frame_addr (c_ly cx) 1 fpos) in *. set (F := lf_F cx) in *.
  set (sp0 := spZ (c_regs cx)) in *.
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
  assert (Hgs : rg_s fr_RG = 0x5d88e0) by (vm_compute; reflexivity).
  (* ---- kept from the entry to the call ---- *)
  assert (KG : forall a, inG G_keep a -> aview segs (w_H W) mem a = aview segs (w_H W) (c_mem cx) a)
    by (intros a Ha; apply KEEP; left; exact Ha).
  assert (KBk : forall p n a, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> p <= a < p + req_size n ->
      aview segs (w_H W) mem a = aview segs (w_H W) (c_mem cx) a)
    by (intros p0 n0 a Hp Ha; apply KEEP; right; exists p0, n0; split; [exact Hp | exact Ha]).
  assert (KGv : forall a n v, rng_inb a (Z.of_nat n) G_keep = true ->
      val_mem segs (arm W (c_mem cx)) a n v -> val_mem segs (arm W mem) a n v).
  { intros a n0 v Hr Hv. apply (pro_vm_view W W (c_mem cx) mem); [|exact Hv].
    intros x Hx. exact (KG x (rng_cover a (Z.of_nat n0) G_keep Hr x Hx)). }
  assert (AW : forall a n, rng_inb a n G_fr_obj = true -> forall (W' : world segs) m', awr W' m' a n).
  { intros a n0 Hr W' m' i Hi. apply (G_obj_wr (a + i) (rng_cover a n0 G_fr_obj Hr (a + i) ltac:(lia))). }
  (* ---- the call's facts ---- *)
  assert (HCLc : forall i, (i < 4)%nat -> asrc_closed W mem (oa_HA i)).
  { intros i Hi. destruct (HCL i Hi) as [HZ _]. split.
    - apply (pro_garr8_view W W (c_mem cx) mem); [|exact HZ].
      intros x Hx. apply KG. rewrite repeat_length in Hx. change (Z.of_nat (Z.to_nat ASRC)) with 96 in Hx.
      apply (rng_cover (rg_s fr_RG) 384 G_keep ltac:(vm_compute; reflexivity)).
      unfold oa_HA, fr_RG in *. unfold ASRC in Hx. rewrite Hgs in *. lia.
    - apply (AW (oa_HA i) ASRC). unfold oa_HA, ASRC.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%nat as Hc by lia.
      destruct Hc as [->|[->|[->| ->]]]; vm_compute; reflexivity. }
  assert (Hos : forall i, nth i [0; 0; 0; 0] 0 = 0) by (intros i; destruct i as [|[|[|[|[|i]]]]]; reflexivity).
  assert (HRRc : ra_rel B fr_RG (c_ly cx) S2 W mem T []).
  { destruct HRR as [(HT0 & _ & (E1 & E2 & E3 & E4 & E5 & E6)) | HAT].
    - left. split; [exact HT0|]. split; [reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E1]|]. split; [apply AW; vm_compute; reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E3]|]. split; [apply AW; vm_compute; reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E5] | apply AW; vm_compute; reflexivity].
    - right. pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & HTin & _).
      apply (arelay_at_kept B fr_RG (c_ly cx) (c_S cx) W (c_mem cx) (c_ly cx) S2 W mem T [] HAT).
      + intros r Hr a Ha. split.
        * unfold arelay_fp in Hr. cbn [map concat app] in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
          -- apply KG. refine (rng_cover (rg_src fr_RG) 8 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply KG. refine (rng_cover (rg_nsrc fr_RG) 4 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply KG. refine (rng_cover (rg_capsrc fr_RG) 4 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply (KBk T ATABLE a HTin). change (req_size ATABLE) with 896. unfold ATABLE in Ha. lia.
        * intros _. unfold arelay_fp in Hr. cbn [map concat app] in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
          -- refine (G_obj_wr a (rng_cover (rg_src fr_RG) 8 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- refine (G_obj_wr a (rng_cover (rg_nsrc fr_RG) 4 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- refine (G_obj_wr a (rng_cover (rg_capsrc fr_RG) 4 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- rewrite <- Eab2 in HTin.
             destruct (al0_blocks _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & _ & _ & _ & Hpr & _).
             apply (apresent_writable segs). apply (proj1 (Hpr a ltac:(change (req_size ATABLE) with 896;
               unfold ATABLE in Ha; lia))).
      + intros b Hb. rewrite Eab2. cbn [arelay_blks map concat app] in Hb. destruct Hb as [<- | []]. exact HTin. }
  assert (HLKc : alock_at fr_RG W mem false).
  { destruct HLK as (L1 & L2 & L3 & L4).
    split; [apply KGv; [vm_compute; reflexivity | exact L1]|].
    split; [apply KGv; [vm_compute; reflexivity | exact L2]|].
    split; [apply KGv; [vm_compute; reflexivity | exact L3] | apply AW; vm_compute; reflexivity]. }
  assert (HWKc : awake_at fr_RG W mem) by (apply KGv; [vm_compute; reflexivity | exact HWK]).
  assert (HRVc : rom_view segs W mem)
    by (eapply ajournal_gx_rom_view0; first [exact Hsegs | exact LAWS | exact HJ | exact pro_rom_out_fr | exact Hrom]).
  (* ---- op_add's afn_pre, its room and its meter ---- *)
  pose proof HFR as (HSV & H24 & H48 & H56 & H64 & H72 & H80 & H88 & H184 & HH0 & HH8 & HH16 & HFW & HSH & HSW).
  pose proof HRG as (R2 & R8 & R9 & R21 & R22 & R24 & R26 & R3 & R4).
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  destruct (pro_afn_pre_at_x cx (c_ly cx) S2 fpos k W mem md regs OA_STK HB HJ HSV Hsp) as (ch & HPREc).
  { rewrite Hra. apply ret_ok_codeptr_v; [unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput; lia | reflexivity]. }
  { unfold raZ. rewrite Hra, unsigned_lit_small by (unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput; lia).
    unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput. lia. }
  { exact R3. } { exact R4. } { exact R8. }
  { unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK. lia. }
  { unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK, LLVMF_STK. lia. }
  destruct (LS_pro_oa cx [] S2 fpos HB Eab2 Hfrs2 Hnev2 Hbb2 HMO2) as (Hroom & Hmok).
  (* the entry's T: when the table exists it is a live block of the entry, above 4096 *)
  assert (HT4096 : T <> 0 -> 4096 <= T /\ In (T, ATABLE) (ablocks B (c_ly cx) (c_S cx))).
  { intros HT0. destruct HRR as [(HT0' & _) | HAT]; [contradiction|].
    pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & HTin & _). split; [|exact HTin]. rewrite <- Eab2 in HTin.
    destruct (al0_blocks _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & H4096 & _). exact H4096. }
  (* ---- op_add, at its own G ---- *)
  assert (HGcov1 : forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G_oa a).
  { intros a Ha. change (inG ((rg_s fr_globals, 384) :: (A_NFD, 4) :: RA_G fr_globals) a).
    apply inG_cons. left. unfold in_zr, ASRC in *. cbn [fst snd]. lia. }
  assert (HGcov2 : forall a, A_NFD <= a < A_NFD + 4 -> inG G_oa a).
  { intros a Ha. change (inG ((rg_s fr_globals, 384) :: (A_NFD, 4) :: RA_G fr_globals) a).
    apply inG_cons. right. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
  assert (HGcov3 : forall a, inG (RA_G fr_globals) a -> inG G_oa a)
    by (intros a Ha; unfold G_oa; apply inG_app; right; exact Ha).
  destruct HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  eapply SRr_bind.
  { exact (oa_spec_g_x_of_kit _ W2_op_add G_oa G_oa_prog_x W (c_ly cx) S2 [] regs mem md ch [0; 0; 0; 0] 0 T [] HPREc
      ltac:(rewrite Hsp; exact HFal) ltac:(rewrite Hfrs2; vm_compute; reflexivity) eq_refl
      ltac:(intros i _; rewrite Hos; lia)
      ltac:(intros i Hi; rewrite Hos; exact (pro_closed_vm W mem _ (HCLc i Hi)))
      ltac:(intros i Hi _; exact (HCLc i Hi))
      G3 ltac:(lia) HZS HGcov1 HGcov2 HGcov3 HRRc HLKc HWKc HRVc
      ltac:(intros _; split; [cbn; lia | intros []]) Hroom Hmok
      (* the room round: the room from the seat's NP (kr := 0), the counts from the entry's xcnt_ok (LS_cnt) *)
      0%nat (proj2 (RP_NP S2 _) HNP2) (LS_cnt cx T cap out S2 HXC Eab2)). }
  cbv beta. intros W3 c3 Hwle3
    (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & kk & -> & HJo & HP4 & HAPK & HOK & Hfrs4 & HRM4 & HSome & HERR4).
  (* the room after op_add: its post's rp_RM at kr = 0 is the cut's NP *)
  pose proof (proj1 (RP_NP S4 0%nat) HRM4) as HNP4.
  hp0g HJo.
  assert (Hof : oa_first [0; 0; 0; 0] = Some 0%nat) by reflexivity.
  rewrite Hof in HSome. cbv beta iota in HSome.
  destruct HSome as (q & T' & pj & HSRC & HNFD & HREL & HLK4 & HPERM & HMLE).
  cbn [app] in HREL. change (100 + 0) with 100 in HSRC, HREL. change (0 + 1) with 1 in HNFD.
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJo) as HAR4.
  assert (Hsk : ~ YI16.sink_open_fp (oa_FP [0; 0; 0; 0] T [])).
  { unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
    intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
    destruct (HT4096 HT0) as (H4096 & _). lia. }
  (* the journal from the entry, through op_add (lifted from G_oa to G_fr) *)
  pose proof (ajournal_gx_G_mono_x segs B PST ARx G_oa G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G_oa_fr HJo) as HJo'.
  assert (HFP1 : forall a, inFP (oa_FP [0; 0; 0; 0] T []) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B (c_ly cx) S2) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B (c_ly cx) S2) a).
  { intros a Ha. left. unfold oa_FP in Ha. rewrite Hof in Ha. unfold ra_FP in Ha.
    destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [destruct Ha as (r & [] & _)|].
    destruct Ha as (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
    destruct (HT4096 HT0) as (H4096 & HTin).
    split; [apply (HFPT HT0); change (req_size ATABLE) with 896; unfold ATABLE in *; lia|].
    exists T, ATABLE. split; [rewrite Eab2; exact HTin | change (req_size ATABLE) with 896; lia]. }
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 [] W mem md k
     OA_STK (spZ regs) 0 [] (oa_FP [0; 0; 0; 0] T []) [] ly4 S4 [] W3 mem4 md4 kk HJ HJo'
     ltac:(rewrite Hsp; unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK, LLVMF_STK; lia)
     ltac:(lia) ltac:(lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFP1) as HJ4.
  cbn [app] in HJ4.
  assert (EFF : frame_addr ly4 1 fpos = FF) by exact (pro_ff_eq_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos HJo).
  assert (EFL : flag_addr ly4 1 fpos = flag_addr (c_ly cx) 1 fpos)
    by (pose proof EFF as E'; unfold FF, frame_addr in E'; unfold flag_addr; lia).
  (* ---- what op_add keeps ---- *)
  assert (KP : forall a, inG G_pst a -> aview segs (w_H W3) mem4 a = aview segs (w_H W) mem a).
  { intros a Ha. pose proof (G_pst_obj a Ha) as Ho. destruct (HG a (HG_obj a Ho)) as (Him & Hno & _).
    exact (pro_call_img_x G_oa OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HJo Hsk a Him (G_pst_oa a Ha) Hno
      (G_obj_err a Ho)). }
  assert (KPv : forall a n v, rng_inb a (Z.of_nat n) G_pst = true ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W3 mem4) a n v).
  { intros a n0 v Hr Hv. apply (pro_vm_view W W3 mem mem4); [|exact Hv].
    intros x Hx. exact (KP x (rng_cover a (Z.of_nat n0) G_pst Hr x Hx)). }
  assert (KGPv : forall a n v, rng_inb a (Z.of_nat n) G_keep = true -> rng_inb a (Z.of_nat n) G_pst = true ->
      val_mem segs (arm W (c_mem cx)) a n v -> val_mem segs (arm W3 mem4) a n v)
    by (intros a n0 v H1 H2 Hv; exact (KPv a n0 v H2 (KGv a n0 v H1 Hv))).
  assert (Hgs' : rg_s fr_globals = 0x5d88e0) by (vm_compute; reflexivity).
  assert (KS3 : forall i, (1 <= i < 4)%nat -> asrc_closed W3 mem4 (oa_HA i)).
  { intros i Hi. destruct (HCLc i ltac:(lia)) as [HZ _]. split.
    - apply (pro_garr8_view W W3 mem mem4); [|exact HZ]. intros x Hx.
      rewrite repeat_length in Hx. change (Z.of_nat (Z.to_nat ASRC)) with 96 in Hx.
      apply HOK.
      + apply HGcov1. unfold oa_HA, ASRC in *. rewrite Hgs' in *. lia.
      + unfold oa_wr. rewrite Hof. intros [Hx1 | [Hx2 | Hx3]].
        * unfold oa_HA, ASRC in *. cbn [Z.of_nat] in Hx1. rewrite Hgs' in *. lia.
        * unfold oa_HA, ASRC, A_NFD in *. rewrite Hgs' in *. lia.
        * pose proof (pro_ra_g x Hx3). unfold oa_HA, ASRC in *. rewrite Hgs' in *. lia.
    - apply (AW (oa_HA i) ASRC). unfold oa_HA, ASRC.
      assert (i = 1 \/ i = 2 \/ i = 3)%nat as Hc by lia.
      destruct Hc as [->|[->| ->]]; vm_compute; reflexivity. }
  (* the entry's blocks the call keeps: all but the relay's table, whose new entry relay_add writes *)
  assert (KBo : forall p n j, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> (T <> 0 -> (p, n) <> (T, ATABLE)) ->
      0 <= j < req_size n -> aview segs (w_H W3) mem4 (p + j) = aview segs (w_H W) mem (p + j)).
  { intros p n j Hp Hne Hj. assert (Hp2 : In (p, n) (ablocks B (c_ly cx) S2)) by (rewrite Eab2; exact Hp).
    apply (pro_call_blk_x G_oa OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk (proj1 G_oa_prog_x) HJo p n j Hp2).
    - destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)).
      + right. right. exact Hp2.
      + right. exact Hp2.
    - exact Hj.
    - unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
      intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
      destruct (HT4096 HT0) as (H4096 & HTin). rewrite <- Eab2 in HTin.
      destruct (pro_blk_disj_x _ _ _ _ _ (p, n) (T, ATABLE) HAR2 Hp2 HTin (Hne HT0)) as [Hd | Hd]; cbn [fst snd] in Hd;
        change (req_size ATABLE) with 896 in Hd; lia. }
  (* the input block and the controller's buffer are not the relay's table (the entry's blocks are distinct) *)
  assert (ND0 : List.NoDup (input_blks cx ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out ++ rest0)).
  { pose proof HPREE as (HAR0 & _). exact (Permutation_NoDup HPERM0 (pro_nodup_x _ _ _ _ _ HAR0)). }
  assert (HinpT : forall p n, In (p, n) (input_blks cx) -> T <> 0 -> (p, n) <> (T, ATABLE)).
  { intros p n Hp HT0 Heq. rewrite Heq in Hp. apply (pro_nodup_app _ _ (T, ATABLE) ND0 Hp).
    rewrite (proj2 (Z.eqb_neq T 0) HT0). apply in_or_app. left. left. reflexivity. }
  assert (HoutT : forall b, In b (aout_blks cap out) -> T <> 0 -> b <> (T, ATABLE)).
  { intros b Hb HT0 Heq. rewrite Heq in Hb. pose proof (pro_nodup_app_r _ _ ND0) as ND1.
    rewrite (proj2 (Z.eqb_neq T 0) HT0) in ND1. cbn [app] in ND1. inversion ND1 as [|x l Hx _]; subst.
    apply Hx. apply in_or_app. left. exact Hb. }
  assert (KBt : forall p n j, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> (T <> 0 -> (p, n) <> (T, ATABLE)) ->
      0 <= j < req_size n -> aview segs (w_H W3) mem4 (p + j) = aview segs (w_H W) (c_mem cx) (p + j))
    by (intros p n j Hp Hne Hj; rewrite (KBo p n j Hp Hne Hj); exact (KBk p n (p + j) Hp ltac:(lia))).
  (* ---- the cut after op_add: the controller's stream ---- *)
  destruct (ERRL ly4 S4 [] W3 mem4 md4 HAR4) as ((v & Hv & Hvr) & Hvw).
  pose proof HAO as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 &
    A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26).
  assert (HAOp : aout_at B fr_RG ly4 S4 W3 mem4 (W_rep.CTL 3 0 0 0 v) O 0 (Z.of_nat (length O)) cap out).
  { split; [apply KPv; [vm_compute; reflexivity | exact G4]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A3]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A5]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A7]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G1]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G2]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G6]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G7]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [exact Hv|]. split; [exact Hvw|]. split; [exact Hvr|].
    split; [left; reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity|].
    split; [left; reflexivity|]. split; [lia|]. split; [reflexivity|].
    destruct A26 as [A26 | (Hc & Hnc & Hio & junk & Hjl & Hjg)]; [left; exact A26|].
    right. split; [exact Hc|]. split; [exact Hnc|].
    assert (Hio2 : In (out, cap) (ablocks B ly4 S4)).
    { destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)); rewrite Eab2;
        [right; right | right]; exact Hio. }
    split; [exact Hio2|]. exists junk. split; [exact Hjl|].
    apply (pro_garr8_view W W3 (c_mem cx) mem4); [|exact Hjg].
    intros x Hx. unfold bzs in Hx. rewrite length_map, length_app in Hx.
    replace x with (out + (x - out)) by lia.
    apply (KBt out cap (x - out)); [exact Hio | intros HT0; apply (HoutT (out, cap));
      [unfold aout_blks; rewrite (proj2 (Z.eqb_neq cap 0) ltac:(lia)); left; reflexivity | exact HT0] |].
    pose proof (req_size_pos cap ltac:(lia)) as [_ Hrc]. lia. }
  (* the input *)
  assert (HINp : ainput_at B cx ly4 S4 W3 mem4).
  { split.
    - destruct Hin as [Hin | (Hn & Hpin)]; [left; exact Hin|]. right. split; [exact Hn|].
      destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)); rewrite Eab2;
        [right; right | right]; exact Hpin.
    - destruct Hin as [(Hn0 & _) | (Hn & Hpin)].
      + rewrite Hnl in Hn0. assert (Hpl : c_pl cx = []) by (apply length_zero_iff_nil; lia).
        rewrite Hpl. intros j Hj. cbn in Hj. lia.
      + apply (pro_garr8_view W W3 (c_mem cx) mem4); [|exact Hgarr].
        intros x Hx. rewrite length_map in Hx. rewrite <- Hnl in Hx. replace x with (c_p cx + (x - c_p cx)) by lia.
        apply (KBt (c_p cx) (c_n cx) (x - c_p cx)); [exact Hpin | intros HT0; apply (HinpT (c_p cx) (c_n cx));
          [unfold input_blks; rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)); left; reflexivity | exact HT0] |].
        pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrc]. lia. }
  (* the model *)
  assert (HMOD4 : amodel_at B ly4 S4 W3 mem4 (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out)).
  { unfold amodel_at, pro_m. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [reflexivity|].
    split.
    { intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth aslot].
      - exact HSRC.
      - exact (KS3 1%nat ltac:(lia)).
      - exact (KS3 2%nat ltac:(lia)).
      - exact (KS3 3%nat ltac:(lia)).
      - lia. }
    split; [exact HREL|]. split; [exact HAOp|].
    split; [split; [apply KPv; [vm_compute; reflexivity | exact G5]
                  | split; [apply AW; vm_compute; reflexivity | left; reflexivity]]|].
    split; [exact HLK4|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HWK]|].
    split; [exact HNFD|]. split; [apply AW; vm_compute; reflexivity|]. split; [unfold OPS_MAX; lia|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HTU]|].
    split; [exists lst; apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HLS0]|].
    apply AW; vm_compute; reflexivity. }
  (* the frame and the fake frame *)
  assert (HIV : forall x, F <= x < 2 ^ 47 -> aview segs (w_H W3) mem4 x = aview segs (w_H W) mem x).
  { intros x Hx. apply (pro_call_hi_x G_oa OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk (proj1 G_oa_prog_x) HJo x).
    - unfold CEIL8 in *. lia.
    - rewrite Hsp. lia. }
  assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  pose proof (frm_off_imgP_x B ARx LAWS IMGCx _ _ [] _ _ _ 1 fpos HAR2 Hin1) as HFimg.
  change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg. unfold off_img in HFimg.
  destruct (frames_bounds0 _ _ _ _ _ 1 fpos HAR2 Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (FRV : forall x, (FF <= x < FF + 128) \/ (SB + FF / 8 <= x < SB + FF / 8 + 16) ->
      aview segs (w_H W3) mem4 x = aview segs (w_H W) mem x).
  { intros x Hx. apply (pro_call_frm_x G_oa OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HJo 1 fpos x Hin1).
    - unfold frame_rng, in_zr, shadow_addr. rewrite <- SB_SHADOW_OFF. cbn [fst snd].
      change (fs_frame_bytes 1) with 128. change (128 / 8) with 16. fold FF. lia.
    - unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
      intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
      destruct (HT4096 HT0) as (H4096 & HTin). rewrite <- Eab2 in HTin.
      destruct (al0_blocks _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & _ & _ & Happ & _).
      change (req_size ATABLE) with 896 in Happ.
      destruct Hx as [Hx | Hx].
      + destruct (pro_blk_frm_x _ _ _ _ _ T ATABLE 1 fpos HAR2 HTin Hin1) as [Hd | Hd];
          change (req_size ATABLE) with 896 in Hd; change (fs_frame_bytes 1) with 128 in Hd; fold FF in Hd; lia.
      + apply (fshadow_not_app FF 16 T 896 x ltac:(lia) ltac:(lia) Happ); [unfold SB in Hx; lia | lia].
    - unfold SB in *. lia.
    - intros HO. pose proof (G_obj_rng x (G_oa_obj x HO)). unfold SB in *. lia. }
  assert (Hin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4, Hfrs2; left; reflexivity).
  destruct (al0_frames ly4 S4 W3 mem4 md4 1 fpos HAR4 Hin4) as (_ & _ & HFp & HFs).
  rewrite EFF in HFp, HFs. change (fs_frame_bytes 1) with 128 in HFp. change (fs_frame_bytes 1 / 8) with 16 in HFs.
  assert (HFR4 : pro_fr cx FF W3 mem4).
  { split.
    { intros o r Hor. apply (pro_vm_view W W3 mem mem4); [|exact (HSV o r Hor)].
      intros x Hx. apply HIV. unfold saved_regs in Hor. cbn [In] in Hor.
      repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; unfold sp0 in *; lia|]). destruct Hor. }
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H24]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H48]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H56]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H64]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H72]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H80]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H88]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H184]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH0]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH8]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH16]|].
    split; [intros i Hi; apply (apresent_writable segs); exact (proj1 (HFp (FF + i) ltac:(lia)))|].
    split; [apply (pro_garr8_view W W3 mem mem4); [intros x Hx; apply FRV; right; cbn [length fake_shadow] in Hx; lia
            | exact HSH]|].
    intros i Hi. apply (apresent_writable segs). pose proof (proj1 (HFs i Hi)) as H.
    unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. exact H. }
  (* the fake frame's last word, its flag pointer (op_add keeps the fake frame) *)
  assert (HFL4 : sv8 W3 mem4 (FF + 120) (flag_addr (c_ly cx) 1 fpos))
    by (apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HFLG]).
  (* the registers op_add keeps *)
  assert (HRG4 : pro_regs cx FF regs4).
  { split; [rewrite (lt_pres regs regs4 2%bv HP4 ltac:(pro_cs)); exact R2|].
    split; [rewrite (lt_pres regs regs4 8%bv HP4 ltac:(pro_cs)); exact R8|].
    split; [rewrite (lt_pres regs regs4 9%bv HP4 ltac:(pro_cs)); exact R9|].
    split; [rewrite (lt_pres regs regs4 21%bv HP4 ltac:(pro_cs)); exact R21|].
    split; [rewrite (lt_pres regs regs4 22%bv HP4 ltac:(pro_cs)); exact R22|].
    split; [rewrite (lt_pres regs regs4 24%bv HP4 ltac:(pro_cs)); exact R24|].
    split; [rewrite (lt_pres regs regs4 26%bv HP4 ltac:(pro_cs)); exact R26|].
    split; [rewrite (lt_pres regs regs4 3%bv HP4 ltac:(pro_cs)); exact R3|].
    rewrite (lt_pres regs regs4 4%bv HP4 ltac:(pro_cs)); exact R4. }
  (* the blocks, as ablocks_sep lists them *)
  assert (Em : model_blks (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out) =
    (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out) by reflexivity.
  assert (ND4 : List.NoDup (ablocks B ly4 S4)) by exact (pro_nodup_x _ _ _ _ _ HAR4).
  assert (HSEP4 : ablocks_sep B fr_FP cx (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out) ly4 S4).
  { split.
    - exists rest0. rewrite Em. rewrite Eab2 in HPERM. exact (pro_sep_perm _ _ _ _ _ T T' q HPERM0 HPERM).
    - intros b Hb. rewrite Em in Hb. destruct Hb as [<- | [<- | Hb]].
      + destruct HPERM as [(HT0 & HP) | (HT0 & -> & HP)].
        * left. intros Hb'. pose proof (Permutation_NoDup HP ND4) as ND. inversion ND as [|x l Hx ND']; subst.
          apply Hx. right. rewrite Eab2. exact Hb'.
        * right. intros a Ha. cbn [fst snd] in Ha. exact (HFPT HT0 a Ha).
      + left. intros Hb'. destruct HPERM as [(_ & HP) | (_ & _ & HP)]; pose proof (Permutation_NoDup HP ND4) as ND.
        * inversion ND as [|x l _ ND']; subst. inversion ND' as [|x l Hx _]; subst. apply Hx. rewrite Eab2. exact Hb'.
        * inversion ND as [|x l Hx _]; subst. apply Hx. rewrite Eab2. exact Hb'.
      + right. exact (HFPO b Hb). }
  (* the cut's two Variables, and the ROM view after op_add *)
  assert (Hc0ex : exists c1 mx1, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c1 O mx1
    (Z.of_nat (length O)) cap out) by (exists c0, mx0; exact HAO).
  assert (HPERM' : exists T0 rest, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest) /\
     ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks B ly4 S4) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly4 S4) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx)))))
    by (exists T, rest0; split; [exact HPERM0|]; split; [exact HXC|]; split; [exact HFH0|];
        rewrite <- Eab2; exact HPERM).
  pose proof (LS_pro cx [] q T' pj (W_rep.CTL 3 0 0 0 v) O cap out S2 fpos ly4 S4 HB Hc0ex eq_refl eq_refl eq_refl
    eq_refl Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HMLE HPERM') as HLS4.
  pose proof (RI_pro cx [] q T' pj (W_rep.CTL 3 0 0 0 v) O cap out HB Hc0ex eq_refl eq_refl eq_refl eq_refl) as HRI4.
  assert (HRV4 : rom_view segs W3 mem4)
    by (eapply ajournal_gx_rom_view0;
        first [exact Hsegs | exact LAWS | exact HJo | exact (proj1 (proj2 (proj2 G_oa_prog_x))) | exact HRVc]).
  (* the loop's set-up *)
  rewrite Hra. rewrite <- EFF in HFR4, HRG4, HFL4. rewrite <- EFL in HFL4.
  exact (pro_fin_x cx W3 regs4 mem4 md4 ly4 S4 (k + kk) _ fpos HB HJ4 HFR4 HRG4 HFL4 HMOD4 eq_refl HINp HRV4 HSEP4 HLS4 HNP4 HRI4).
Qed.

Lemma pro_at_call_x : forall cx S2 k fpos E regs4 m4 md4,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 (c_W cx) m4 md4 k ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, fpos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 -> NP S2 ->
  img_env VAL A_LIM E ->
  bv_unsigned (ew E 2) = spZ (c_regs cx) -> bv_unsigned (ew E 34) = lf_F cx ->
  bv_unsigned (ew E 39) = frame_addr (c_ly cx) 1 fpos ->
  bv_unsigned (ew E 513) = SB + frame_addr (c_ly cx) 1 fpos / 8 -> ew E 33 = Z_to_bv 64 SB ->
  bv_unsigned (ew E 512) = flag_addr (c_ly cx) 1 fpos ->
  (forall r, (r < 32)%nat -> ew E r = getr (c_regs cx) (Z_to_bv 5 (Z.of_nat r))) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 353 1684 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 352 1660 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 351 1636 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 350 1616 8 8 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 349 1588 4 4 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 348 1528 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 347 (-512) 4 4 3) ->
  region_ok segs E (arm (c_W cx) m4) pc_sh -> region_ok segs E (arm (c_W cx) m4) pc_ff ->
  region_ok segs E (arm (c_W cx) m4) pc_save -> region_ok segs E (arm (c_W cx) m4) pc_F ->
  getr regs4 1 = Z_to_bv 64 (BASE + 8008) -> getr regs4 2 = ew E 34 -> getr regs4 3 = ew E 3 ->
  getr regs4 4 = ew E 4 -> getr regs4 8 = ew E 2 -> getr regs4 9 = ew E 34 -> getr regs4 21 = ew E 11 ->
  getr regs4 22 = ew E 10 -> getr regs4 24 = ew E 513 -> getr regs4 26 = ew E 33 ->
  (forall a, pro_ks cx a -> aview segs (w_H (c_W cx)) m4 a = aview segs (w_H (c_W cx)) (c_mem cx) a) ->
  SRr segs (c_W cx) (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + 11300)) m4 (seg_rom segs)) md4)
    (fun W' c' => INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx [] 0 W' c' \/ INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx [] W' c').
Proof.
  intros cx S2 k fpos E regs4 m4 md4 HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HNP2 HEI U2 U34 U39 U513 E33 U512 EA
    RG7 RG6 RG5 RG4 RG3 RG2 RG1 RSH RFF RSV RF Q1 Q2 Q3 Q4 Q8 Q9 Q21 Q22 Q24 Q26 KEEP.
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & Hra0 & H10 & H11 & _).
  pose proof HPREE as (_ & _ & _ & Hgp & Htp & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pro_Fb_x cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  set (FF := frame_addr (c_ly cx) 1 fpos) in *. set (F := lf_F cx) in *.
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds0 _ _ _ _ _ 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1.
  destruct (al0_frames _ _ _ _ _ 1 fpos HAR Hin1) as (_ & _ & HFp & HFs).
  fold FF in HFp, HFs. change (fs_frame_bytes 1) with 128 in HFp. change (fs_frame_bytes 1 / 8) with 16 in HFs.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (ER : forall (r : nat) (b : bv 5), (r < 32)%nat -> Z.of_nat r = bv_unsigned b -> ew E r = getr (c_regs cx) b).
  { intros r b Hr Hb. rewrite (EA r Hr). f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hb.
    apply bv_wrap_small. change (bv_modulus 5) with 32. lia. }
  (* the frame and the fake frame *)
  assert (HFR : pro_fr cx FF (c_W cx) m4).
  { unfold pro_fr. cbv zeta. fold F.
    split.
    { apply (pro_saved_of_region E _ _ _ _ _ _ _ (c_regs cx) RSV U2 EA).
      unfold saved_regs.
      repeat (apply Forall_cons; [cbn [fst snd In]; repeat (first [left; reflexivity | right]) |]).
      apply Forall_nil. }
    assert (FS : forall off (nv : nat) v, In (YP09.mkChunk off (CVal 8 (SOff nv 0))) (YP09.r_chunks pc_F) ->
        bv_unsigned (ew E nv) = v -> 0 <= v < 2 ^ 64 -> sv8 (c_W cx) m4 (F + off) v).
    { intros off nv v Hc Hv Hr. unfold sv8.
      refine (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 34 F _ 24 208 24 208 off 8 (SOff nv 0) v RF U34 Hc _ Hr
        ltac:(cbn; lia)) eq_refl eq_refl).
      cbn [sv_denot]. rewrite Hv, Z.add_0_r. reflexivity. }
    split; [apply (FS 24 347%nat); [cbn; tauto | pro_rwimg HEI 347%nat; reflexivity | lia]|].
    split; [apply (FS 48 352%nat); [cbn; tauto | pro_rwimg HEI 352%nat; reflexivity | lia]|].
    split; [apply (FS 56 353%nat); [cbn; tauto | pro_rwimg HEI 353%nat; reflexivity | lia]|].
    split; [apply (FS 64 351%nat); [cbn; tauto | pro_rwimg HEI 351%nat; reflexivity | lia]|].
    split; [apply (FS 72 350%nat); [cbn; tauto | pro_rwimg HEI 350%nat; reflexivity | lia]|].
    split; [apply (FS 80 39%nat); [cbn; tauto | exact U39 | lia]|].
    split; [apply (FS 88 39%nat); [cbn; tauto | exact U39 | lia]|].
    split; [apply (FS 184 39%nat); [cbn; tauto | exact U39 | lia]|].
    assert (FH : forall off e v, In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks pc_ff) ->
        sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv8 (c_W cx) m4 (FF + off) v).
    { intros off e v Hc Hv Hr. unfold sv8.
      exact (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 39 FF _ 0 128 0 0 off 8 e v RFF U39 Hc Hv Hr
        ltac:(cbn; lia)) eq_refl eq_refl). }
    split; [rewrite <- (Z.add_0_r FF); apply (FH 0 (SLit 1102416563)); [cbn; tauto | reflexivity | lia]|].
    split; [apply (FH 8 (SOff 266 0)); [cbn; tauto | | lia];
            cbn [sv_denot]; pro_rwimg HEI 266%nat; reflexivity|].
    split; [apply (FH 16 (SOff 240 7620)); [cbn; tauto | | lia];
            cbn [sv_denot]; pro_rwimg HEI 240%nat; reflexivity|].
    split; [intros i Hi; apply (apresent_writable segs); exact (proj1 (HFp (FF + i) ltac:(lia)))|].
    split.
    { apply (pro_shadow_garr8 E _ 513 _ _ 0 16 0 0 RSH U513).
      intros j Hj. do 16 (destruct j as [|j]; [cbn; repeat (first [left; reflexivity | right]) |]). lia. }
    intros i Hi. apply (apresent_writable segs). pose proof (proj1 (HFs i Hi)) as H.
    unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. exact H. }
  (* the registers *)
  assert (HRG : pro_regs cx FF regs4).
  { unfold pro_regs, w64. fold F.
    split; [rewrite Q2, <- U34, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q8, (ER 2%nat 2%bv ltac:(lia) eq_refl); reflexivity|].
    split; [rewrite Q9, <- U34, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q21, (ER 11%nat 11%bv ltac:(lia) eq_refl), H11; reflexivity|].
    split; [rewrite Q22, (ER 10%nat 10%bv ltac:(lia) eq_refl), H10; reflexivity|].
    split; [rewrite Q24, <- U513, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q26; exact E33|].
    split; [rewrite Q3, (ER 3%nat 3%bv ltac:(lia) eq_refl), Hgp; reflexivity|].
    rewrite Q4, (ER 4%nat 4%bv ltac:(lia) eq_refl), Htp; reflexivity. }
  (* the globals *)
  assert (GV : forall n off w (sz : N) v a, region_ok segs E (arm (c_W cx) m4) (pc_g n off w sz v) ->
      (A_TEXT <= n < A_LIM)%nat -> VAL n + off = a -> N.to_nat sz = Z.to_nat w -> 0 <= v < 2 ^ (8 * Z.of_N sz) ->
      (Z.of_N sz <= 8) -> val_mem segs (arm (c_W cx) m4) a (Z.to_nat w) v).
  { intros n0 off w sz v a HR Hn Ha Hw Hv Hs.
    refine (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ n0 (VAL n0) _ off (off + w) off (off + w) off sz
      (SLit v) v HR (HEI n0 Hn) ltac:(cbn; tauto) _ Hv Hs) Ha Hw).
    reflexivity. }
  assert (HGL : pro_glob (c_W cx) m4).
  { unfold pro_glob.
    split; [exact (GV 347%nat (-512) 4 4%N 3 (rg_client fr_RG) RG1 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 348%nat 1528 1 1%N 0 (rg_client_broken fr_RG) RG2 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 349%nat 1588 4 4%N 0 A_NFD RG3 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 350%nat 1616 8 8%N 0 (rg_send_max fr_RG) RG4 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 351%nat 1636 1 1%N 0 (rg_gone fr_RG) RG5 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 352%nat 1660 1 1%N 0 (rg_send_dead fr_RG) RG6 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    exact (GV 353%nat 1684 1 1%N 0 (rg_send_eintr fr_RG) RG7 ltac:(unfold A_TEXT, A_LIM; lia)
      ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
  (* the return address *)
  assert (Hra : getr regs4 1 = w64 (BASE + A_pro_ret)).
  { rewrite Q1. reflexivity. }
  assert (HFLG : sv8 (c_W cx) m4 (FF + 120) (flag_addr (c_ly cx) 1 fpos)).
  { pose proof (bv_unsigned_in_range 64 (ew E 512)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    unfold sv8.
    exact (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 39 FF _ 0 128 0 0 120 8 (SOff 512 0)
      (flag_addr (c_ly cx) 1 fpos) RFF U39 ltac:(cbn; tauto)
      ltac:(cbn [sv_denot]; rewrite U512, Z.add_0_r; reflexivity) ltac:(rewrite <- U512; lia)
      ltac:(cbn; lia)) eq_refl eq_refl). }
  exact (pro_mid_x cx regs4 m4 md4 S2 k fpos HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HNP2 HFR HFLG Hra HRG HGL KEEP).
Qed.

Theorem lf_seg_pro_x : forall cx Hp, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  SRr segs (c_W cx) (lf_entry cx)
    (fun W' c' => INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp 0 W' c' \/ INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp W' c').
Proof.
  intros [ly S W regs mem md p n pl M] Hp HB.
  (* the entry's ghost list is empty (HP0 on the pre's ARx): the walk runs at [] *)
  pose proof HB as (_ & HPRE_). hp0a (proj1 (proj1 HPRE_)). clear HPRE_.
  pose proof HB as (HAI & HPRE & Hra0 & H10 & H11 & Hin & Hnl & Hgarr & Hfrs & Hlive & Hroom & Hnp & Hgi & Hrom & Hrod & Hsink & Hfd & Hsrt & Hmeta & Hmo & Hstkr & Hhb).
  cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_M lf_entry] in *.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (Rn : 0 <= n < 2 ^ 26) by (destruct Hin as [(-> & _) | (Hn & _)]; lia).
  destruct (pro_entry_x W ly S regs mem md [] n HPRE H11 Rn) as [HS SHOK].
  (* the journal at G = [] (W1Verify's template: ajournal_gx_nil_x of ajournal_x_init) *)
  pose proof (proj2 (ajournal_gx_nil_x segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (ajournal_x_init segs B PST ARx LLVMF_STK (lf_FP fr_FP (LFCX ly S W regs mem md p n pl M)) ly S [] W regs mem md [] HPRE)) as HJ.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  remember (Eimg (Ereg regs (pro_extra regs))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n0 r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  set (F := pro_F regs) in *.
  assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  assert (HAE : env_agree 32 (Ereg regs (pro_extra regs)) E)
    by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HFv : F = spZ regs - 320 \/ F = spZ regs - 336) by exact (pro_F_facts (spZ regs) Hal16).
  assert (HFal : F mod 32 = 0) by exact (pro_F_al (spZ regs - 320)).
  assert (HspR : 2 ^ 46 <= F /\ spZ regs <= 2 ^ 47).
  { revert HFv Hslo Hshi H47 Hceil C1 C3 WS Hstk0. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
  assert (UF : bv_unsigned (ew E 34) = F) by (rewrite E34; apply unsigned_lit_small; lia).
  unfold cfg_at. change (w64 A_LLVMF) with (Z_to_bv 64 (BASE + A_pro)).
  (* run 1: the frame, the saved registers, the fake-stack test; stops at __asan_stack_malloc_1 *)
  paj_run_tok_x RUN0 HS HJ SHOK Bspan.
  { apply awr_ok_x_of0. intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?UF in Hr;
        first [ lia | left; lia ] | ]).
    destruct Hin'. }
  (* the call to __asan_stack_malloc_1 (128): the fake frame FF; the journal at G = [] is the plain ajournal_x *)
  apply ajournal_gx_nil_x in HJ.
  pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  rewrite (palf_sm1 B TLF).
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
      eapply (aj_stack_malloc_pres_at_x segs B PST ARx LAWS Hsegs (pal_env B TL) OWNLOW WFx WFL SMALLOC 1 ASM1 ltac:(lia)
        W rg mm LLVMF_STK (spZ regs) _ ly S [] W mem md [] ly S [] _ 0 (F - spZ regs) _ HJ) end.
    - unfold spZ at 1. rewrite R2, UF. lia.
    - destruct HFv as [HFe | HFe]; rewrite HFe;
        [replace (spZ regs - 320 - spZ regs) with ((-20) * 16) by lia | replace (spZ regs - 336 - spZ regs) with ((-21) * 16) by lia];
        apply Z_mod_mult.
    - lia.
    - rewrite WS, Hes. lia.
    - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Hfrs. vm_compute. reflexivity. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HPg & Hsf).
  (* the room round: the seat is a set_fs of the entry's state, so NP holds there (NPF) *)
  assert (HNP2 : NP S2) by (destruct Hsf as (fs & ->); exact (NPF _ fs Hnp)).
  (* KF-COUNT F2: and it costs nothing at the meter (MO_FR), LS_pro_oa's / LS_pro's premise *)
  assert (HMO2 : mo_le MT S S2 0) by (destruct Hsf as (fs & ->); exact (MO_FR S fs)).
  set (FF := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
  pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb.
  destruct (al0_const _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
  destruct (al0_const _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
  rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
  pose proof (palf_uar_img B TLF) as HuR.
  jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | apply Forall_nil].
    - eapply region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
    - eapply region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
    - eapply region_kept_stack_aj_x; [exact HK | exact HJ2 | exact UF | lia | lia | lia | cbn; lia | cbn; lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
        [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kg1) | exact (val_mem_of_rdword segs _ _ _ _ Kg2) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
        [exact (HEI (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kc1) | exact (val_mem_of_rdword segs _ _ _ _ Kc2) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
        [exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kgu1) | exact (val_mem_of_rdword segs _ _ _ _ Kgu2) | lia].
    - apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
        [rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 segs _ _ _ _ Ku1) | exact (val_mem_of_rd32 segs _ _ _ _ Ku2) | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  assert (HAEa : env_agree 32 (Ereg regs (pro_extra regs)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
  clear HEa.
  prreg HS (10%bv : bv 5) RF.
  (* seat the fake frame: FF in atom 39 (a0), its flag FL in 512, the frame's shadow SB + FF / 8 in 513 *)
  assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds0 _ _ _ _ _ 1 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
  destruct (al0_frames _ _ _ _ _ 1 fpos HARb Hfin2) as (HFal2 & HFapp & HFpres & HFSpres).
  destruct (FFL _ _ [] _ _ _ 1 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
  change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  fold FF FL in HFal2, HFapp, HFpres, HFSpres, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
  assert (RF' : ew Ea 39 = Z_to_bv 64 FF) by (rewrite <- RF, Ha0; reflexivity).
  assert (E33a : ew Ea 33 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E33).
  assert (U2a : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
  assert (U34a : bv_unsigned (ew Ea 34) = F) by (rewrite OLDa by lia; exact UF).
  assert (U32a : bv_unsigned (ew Ea 32) = as_uar_cell B) by (rewrite OLDa, E32 by lia; apply unsigned_lit_small; lia).
  assert (U241 : bv_unsigned (ew Ea 241) = VAL (A_OBJ 0)) by exact (HEIa (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (U242 : bv_unsigned (ew Ea 242) = VAL (A_OBJ 1)) by exact (HEIa (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (U273 : bv_unsigned (ew Ea 273) = VAL (A_OBJ 32)) by exact (HEIa (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (HFF8 : FF / 8 = 4 * (FF / 32)).
  { pose proof (Z.div_mod FF 32 ltac:(lia)) as D. rewrite HFal2, Z.add_0_r in D. rewrite D at 1.
    replace (32 * (FF / 32)) with (4 * (FF / 32) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
  assert (HFF8lo : 512 <= FF / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HFF8hi : FF / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
  pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
  pose proof (palf_sep B TLF) as HSEP. cbn [zseps zseps_from fst snd] in HSEP.
  pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 1)). pose proof (pa_val_range (A_OBJ 32)).
  pose proof (ff_seat_ok Ea _ _ (w_H W) mem2 39 33 512 1 FF FL HS eq_refl ltac:(vm_compute; reflexivity)
    RF' E33a ltac:(lia) ltac:(lia) ltac:(right; reflexivity) HFal2 ltac:(lia) ltac:(change (fs_frame_bytes 1) with 128; lia)
    ltac:(lia)
    ltac:(change (fs_frame_bytes 1) with 128; intros a Ha; exact (proj1 (HFpres a Ha)))
    ltac:(change (fs_frame_bytes 1 / 8) with 16; intros i Hi; exact (proj1 (HFSpres i Hi)))
    ltac:(change (fs_frame_bytes 1) with 128; exact Hflag) ltac:(change (fs_frame_bytes 1) with 128; exact Hz)) as HS3.
  pose proof (frm_off_imgP_x B ARx LAWS IMGCx _ _ [] _ _ _ 1 fpos HARb Hfin2) as HFimg. change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg.
  set (Eb := havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)]) in HS3.
  assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; subst Eb; apply YN3v.ew_havoc_old; exact Hm).
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
  assert (U512 : bv_unsigned (ew Eb 512) = FL).
  { subst Eb. rewrite (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
    apply unsigned_lit_small. lia. }
  assert (U513 : bv_unsigned (ew Eb 513) = SB + FF / 8).
  { subst Eb. rewrite (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)).
    apply unsigned_lit_small. unfold SB. lia. }
  assert (U39b : bv_unsigned (ew Eb 39) = FF) by (rewrite OLDb, RF' by lia; apply unsigned_lit_small; lia).
  assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact U2a).
  assert (U34b : bv_unsigned (ew Eb 34) = F) by (rewrite OLDb by lia; exact U34a).
  assert (U32b : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb by lia; exact U32a).
  assert (U241b : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U241).
  assert (U242b : bv_unsigned (ew Eb 242) = VAL (A_OBJ 1)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U242).
  assert (U273b : bv_unsigned (ew Eb 273) = VAL (A_OBJ 32)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U273).
  match type of HS3 with ?A1 -> ?A2 -> _ => assert (HD1 : A1); [|assert (HD2 : A2); [|specialize (HS3 HD1 HD2)]] end.
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, ff_fregion, fframe_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1) with 128. rewrite U39b, U2b, U34b, U241b, U242b, U273b, U32b.
    unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia. }
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, ff_sregion, ff_fregion, fshadow_region, fframe_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1 / 8) with 16. change (fs_frame_bytes 1) with 128.
    rewrite U513, U39b, U2b, U34b, U241b, U242b, U273b, U32b.
    pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hd8a. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as Hd8b.
    pose proof (Z.div_mod FF 8 ltac:(lia)) as Hd8c.
    unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia. }
  clear HS. rename HS3 into HS. norm_ss HS.
  (* run 2 (plain): the frame's slot F+184, the fake frame's header and its shadow's poison *)
  paj_run_sh_x RUNP HS HJ2.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U34b, ?U39b, ?U512, ?U513, ?U241b, ?U242b, ?U273b, ?U32b in Hr;
        first [ lia
        | left; lia
        | right; right; right; exists 1, fpos; split; [left; reflexivity|];
          change (frame_addr ly 1 fpos) with FF; change (fs_frame_bytes 1) with 128;
          first [ left; unfold in_zr; cbn [fst snd]; lia
          | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (128 / 8) with 16; lia ] ]
      | ]).
    destruct Hin'. }
  (* the size refusal: n >> 26 <> 0 goes to 0x84d7c; refuted by the contract's n < 2^26 *)
  assert (E11b : ew Eb 11 = Z_to_bv 64 n) by (rewrite OLDb, OLDa, (EE 11%nat 11%bv eq_refl), H11 by lia; reflexivity).
  psrr_branch_pi_x RUNP BR HS.
  { exfalso. rewrite branch_ne_U, U_SAlu, (U_atom Eb 11 n E11b), !U_SLit in Hc by lia. cbn [zalu_raw] in Hc.
    change (Z.land (zcanon 26) 63) with 26 in Hc. rewrite Z.shiftr_div_pow2, Z.div_small in Hc by lia.
    vm_compute in Hc. discriminate Hc. }
  (* the fake frame and its shadow become read-only (the token run keeps its windows off the shadow span);
     the runtime's GOT and uar regions are dropped *)
  pro_keep HS [0; 1; 2; 3; 4]%nat.
  pro_ro HS 0%nat. pro_ro HS 1%nat.
  pose proof pro_vals as (PV67 & PV68 & PV69 & PV70 & PV71 & PV72 & PV73 & PV74 & PV75 & PV76 & PV77 & PV78 &
    PVO22 & PVO25 & PVO26 & PVO0 & PVO32).
  assert (RGv : rg_client fr_RG = 0xa1fe0 /\ rg_client_broken fr_RG = 0x5d87e0 /\ rg_send_max fr_RG = 0x5d8840 /\
    rg_gone fr_RG = 0x5d8860 /\ rg_send_dead fr_RG = 0x5d8880 /\ rg_send_eintr fr_RG = 0x5d88a0 /\
    rg_s fr_RG = 0x5d88e0 /\ rg_nout fr_RG = 0x5d88c0 /\ rg_nsrc fr_RG = 0x5d87a0 /\ rg_src fr_RG = 0x5d87c0)
    by (vm_compute; repeat split; reflexivity).
  destruct RGv as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & RG7 & RG8 & RG9 & RG10).
  assert (HNFDv : A_NFD = 0x5d8820) by reflexivity.
  (* the seven global stores' regions (pr_g 67 .. 73), all in G_fr *)
  pro_addg HS HEIb 67%nat (-512) 4 HG_client.
  pro_addg HS HEIb 68%nat 1528 1 HG_cbroken.
  pro_addg HS HEIb 69%nat 1588 4 HG_nfd.
  pro_addg HS HEIb 70%nat 1616 8 HG_smax.
  pro_addg HS HEIb 71%nat 1636 1 HG_gone.
  pro_addg HS HEIb 72%nat 1660 1 HG_sdead.
  pro_addg HS HEIb 73%nat 1684 1 HG_seintr.
  pro_addf HS HEIb 347%nat. pro_addf HS HEIb 348%nat. pro_addf HS HEIb 349%nat. pro_addf HS HEIb 350%nat.
  pro_addf HS HEIb 351%nat. pro_addf HS HEIb 352%nat. pro_addf HS HEIb 353%nat.
  (* the journal, from here at G_fr (the donor's journal is ajournal_gx at G = [], lifted) *)
  pose proof (ajournal_gx_G_mono_x segs B PST ARx [] G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a Ha => False_ind _ (inG_nil a Ha)) (proj2 (ajournal_gx_nil_x segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) HJ2)) as HJ3.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (SHOKb : sh_ok segs Bx [] Eb (mrestrict (w_H W) (ms_mem msx))) by (unfold sh_ok; constructor) end.
  pose proof (pro_Fb_x (LFCX ly S W regs mem md p n pl M) HB) as (HFlo & HFsp & HFsp2 & _ & _ & _).
  change (lf_F (LFCX ly S W regs mem md p n pl M)) with F in HFlo, HFsp, HFsp2. unfold CEIL8 in HFlo.
  cbn [c_regs] in HFsp, HFsp2.
  (* run 3: the frame's slots and the seven globals, to `jal op_add` *)
  paj_run_to_tok_x RUNTOX HS HJ3 SHOKb Bspan AF_fr_op_add.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U34b, ?U39b, ?U512, ?U513, ?U241b, ?U242b, ?U273b, ?U32b in Hr;
        pro_imgh HEIb Hr;
        first [ clear - Hr; lia
        | left; split; [left; clear - Hr WS HFsp HFsp2; lia | clear - Hr; lia]
        | right; left; first [ apply HG_client; clear - Hr RG1; lia | apply HG_cbroken; clear - Hr RG2; lia
                             | apply HG_nfd; clear - Hr HNFDv; lia | apply HG_smax; clear - Hr RG3; lia
                             | apply HG_gone; clear - Hr RG4; lia | apply HG_sdead; clear - Hr RG5; lia
                             | apply HG_seintr; clear - Hr RG6; lia ]
        ]
      | ]).
    destruct Hin'. }
  (* ---- the bytes the prologue keeps from the entry to the call (pro_mid_x's KEEP) ---- *)
  pose proof HK as (HK1 & HK2 & HK3 & _ & _ & _).
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) ?m4) |- _ =>
    rename Hx into HFr3;
    assert (K3 : forall a, 0 <= a < alloc_ceiling -> (a + 1 <= FF \/ FF + 128 <= a) ->
        (a < 2147450880 + FF / 8 \/ 2147450880 + FF / 8 + 16 <= a) -> pro_gst_out a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) mem2 a) end.
  { clear - HFr3 HFr0 HEIb U2b U34b U39b U512 U513 U241b U242b U273b U32b HFlo HFsp.
    intros a Ha Hff Hsh Hgst. pose proof Hgst as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6 & Hg7). clear Hgst.
    pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    rewrite (proj1 (pro_kept_frame _ _ W _ _ a HFr3 ltac:(clear - Ha D1; lia) ltac:(pro_nwr_k HEIb Ha HFlo HFsp))).
    pose proof (proj1 (pro_kept_frame _ _ W _ _ a HFr0 ltac:(clear - Ha D1; lia)
      ltac:(pro_nwr_k HEIb Ha HFlo HFsp))) as K2.
    cbn [ms_mem mkst] in K2. exact K2. }
  assert (K1 : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { clear - HFr HEI Usp UF HFlo HFsp.
    intros a Ha. pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    exact (proj1 (pro_kept_frame _ _ W _ _ a HFr ltac:(clear - Ha D1; lia) ltac:(pro_nwr_k HEI Ha HFlo HFsp))). }
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) ?m4) |- _ =>
    assert (KEEP : forall a, pro_ks (LFCX ly S W regs mem md p n pl M) a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) mem a) end.
  { pose proof asan_consts as (D1 & D2 & D3 & D4 & D5). unfold off_img in HFimg.
    intros a [Ha | (p0 & n0 & Hp & Hpa)]; [|cbn [c_ly c_S] in Hp].
    - pose proof (G_obj_rng a (G_keep_obj a Ha)) as Hr. pose proof (G_keep_gst a Ha) as Hg.
      destruct (HG a (HG_obj a (G_keep_obj a Ha))) as (Him & Hno & _).
      rewrite (K3 a ltac:(clear - Hr D1; lia) ltac:(clear - Hr HFimg; lia) ltac:(clear - Hr HF4096; lia) Hg),
        (HK3 a Him Hno (G_obj_err a (G_keep_obj a Ha))).
      exact (K1 a ltac:(clear - Hr D1; lia)).
    - destruct (al0_blocks _ _ _ _ _ p0 n0 HARa Hp) as (_ & H4096 & Hbc & Happ & _).
      assert (Hp2 : In (p0, n0) (ablocks B ly S2)) by (rewrite Eab; exact Hp).
      pose proof (pro_blk_frm_x _ _ _ _ _ p0 n0 1 fpos HARb Hp2 Hfin2) as Hd.
      change (frame_addr ly 1 fpos) with FF in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      assert (Hsh : a < 2147450880 + FF / 8 \/ 2147450880 + FF / 8 + 16 <= a).
      { destruct (Z_lt_le_dec a (2147450880 + FF / 8)) as [Hl | Hl]; [left; exact Hl | right].
        destruct (Z_lt_le_dec a (2147450880 + FF / 8 + 16)) as [Hl2 | Hl2]; [|exact Hl2].
        exfalso. exact (fshadow_not_app FF 16 p0 (req_size n0) a ltac:(clear - HF4096; lia)
          ltac:(clear - HFceil D1; lia) Happ ltac:(clear - Hl Hl2; lia) Hpa). }
      rewrite (K3 a ltac:(clear - H4096 Hbc Hpa; lia) ltac:(clear - Hd Hpa; lia) Hsh
        (pro_blk_gst_x _ _ _ _ _ p0 n0 a HARa Hp Hpa)).
      replace a with (p0 + (a - p0)) by ring.
      rewrite (HK2 p0 n0 (a - p0) Hp ltac:(clear - Hpa; lia) (fun Hf => Hf)).
      exact (K1 (p0 + (a - p0)) ltac:(clear - H4096 Hbc Hpa D1; lia)). }
  (* ---- op_add's entry ---- *)
  pmkst HS.
  pro_rgn HS 0%nat RQ7. pro_rgn HS 1%nat RQ6. pro_rgn HS 2%nat RQ5. pro_rgn HS 3%nat RQ4.
  pro_rgn HS 4%nat RQ3. pro_rgn HS 5%nat RQ2. pro_rgn HS 6%nat RQ1. pro_rgn HS 7%nat RQS.
  pro_rgn HS 8%nat RQF. pro_rgn HS 10%nat RQV. pro_rgn HS 11%nat RQP.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26.
  assert (EAb : forall r, (r < 32)%nat -> ew Eb r = getr regs (Z_to_bv 5 (Z.of_nat r))).
  { intros r Hr. rewrite OLDb, OLDa by (clear - Hr; lia). apply EE. rewrite Z_to_bv_unsigned. symmetry.
    apply bv_wrap_small. change (bv_modulus 5) with 32. clear - Hr; lia. }
  assert (Hfrs2' : frames S2 = [(1, fpos)]) by (rewrite Hfrs2, Hfrs; reflexivity).
  exact (pro_at_call_x (LFCX ly S W regs mem md p n pl M) S2 0 fpos Eb _ _ _ HB HJ3 Eab Hfrs2' Hnev2 Hbb2 HMO2 HNP2 HEIb
    U2b U34b U39b U513 (eq_trans (OLDb 33%nat ltac:(apply Nat.ltb_lt; reflexivity)) E33a) U512 EAb
    RQ7 RQ6 RQ5 RQ4 RQ3 RQ2 RQ1 RQS RQF RQV RQP Q1 Q2 Q3 Q4 Q8 Q9 Q21 Q22 Q24 Q26 KEEP).
Qed.

(* ================================================================ route R
   SEG_PRO at a world relation R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0; a Theorem Labs lane's argument layout for the fourteen twins: a nested
   Section at the end of the strict one, R and its three laws in this order, then the R callee specs).  lf_seg_pro_xR's
   conclusion is cut_x's Section wR hypothesis SEG_PRO_R.  op_add is the one program callee whose contract is stated
   with a journal, so the twin takes op_add's R contract W2_op_add_R (W_op_add.v:2941 oa_spec_g_xR) in place of
   W2_op_add; every other premise is the strict lemma's (the stack_malloc seat neither frees nor reallocs: its strict
   rule stands).  The walk to op_add's call is the strict one, lifted by SRr_SRrG (pro_srr_srrG); op_add's step is its
   R contract, composed by SRrG_bind (R_trans); the cut journal after it is at R (ajournal_gx_sub_xR, with the strict
   journal to the call lifted by ajournal_gx_xR_mono, WLE_R), and the loop's set-up is a strict run over the R journal
   (W_journal_x's paj_run_x_xR / paj_run_to_x_xR), lifted by SRr_SRrG.  The strict lemmas above are unchanged; each
   twin <name>R below is <name>'s text with these replacements. ---- *)
Section prxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
(* op_add at R: the kit's R contract (W_op_add.v:2941 oa_spec_g_xR; a Theorem Labs lane's pb_op_add_g_xR proves it) *)
Hypothesis W2_op_add_R : W_op_add.oa_spec_g_xR (PI := PB_fr) B PST ARx R MT RP (BASE + AF_fr_op_add).
(* oa_post_x / oa_spec_x / oa_spec_g_x above at R (W_op_add.v:206 oa_post_xR, :228 oa_spec_xR, :2944 oa_spec_g_xR),
   written with _pro.v's names as the strict copies are; oa_spec_g_xR_of_kit reads the kit text at them *)
Definition oa_post_xR (G : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
(os : list Z) (n0 T : Z) (es : list rentry) (kr : nat) : world segs -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' kk,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal_gx_xR segs B PST ARx R G 0 [] OA_STK (spZ regs) (oa_FP os T es) ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\ oa_kept G os W mem W' mem' /\ frames S' = frames S /\ rp_RM RP S' kr /\
match oa_first os with
| None => ly' = ly /\ S' = S /\ W' = W /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - OA_STK <= a < spZ regs) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a)
| Some i => exists (q T' : Z) (pj : list byte),
    asrc_at B ly' S' W' mem' (oa_HA i) (oa_new_src (100 + n0) q pj) /\
    val_mem segs (arm W' mem') A_NFD 4 (n0 + 1) /\
    arelay_at B fr_globals ly' S' W' mem' T' (es ++ [ra_new (100 + n0)]) /\
    alock_at fr_globals W' mem' false /\
    ((T = 0 /\ Permutation (ablocks B ly' S') ((T', ATABLE) :: (q, APARTIAL) :: ablocks B ly S)) \/
     (T <> 0 /\ T' = T /\ Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S))) /\
    mo_le MT S S' oa_cost
end /\
(forall i, 0 <= i < 4 -> aview segs (w_H W') mem' (as_errno B + i) = aview segs (w_H W) mem (as_errno B + i)).
Definition oa_spec_xR (G : list (Z * Z)) (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch (os : list Z) (n0 T : Z) (es : list rentry),
afn_pre_x segs B ARx OA_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
count_cid 0 (frames S) < fs_frames 0 ->
length os = 4%nat ->
(forall i, (i < 4)%nat -> 0 <= nth i os 0 < 2 ^ 31) ->
(forall i, (i < 4)%nat -> val_mem segs (arm W mem) (oa_HA i + 4) 4 (nth i os 0)) ->
(forall i, (i < 4)%nat -> nth i os 0 = 0 -> asrc_closed W mem (oa_HA i)) ->
val_mem segs (arm W mem) A_NFD 4 n0 -> 0 <= n0 <= 512 ->
azs B (rg_s fr_globals) (4 * ASRC) ->
(forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G a) ->
(forall a, A_NFD <= a < A_NFD + 4 -> inG G a) ->
(forall a, inG (RA_G fr_globals) a -> inG G a) ->
ra_rel B fr_globals ly S W mem T es ->
alock_at fr_globals W mem false -> awake_at fr_globals W mem ->
rom_view segs W mem ->
(oa_first os <> None -> (length es < 4)%nat /\ ~ In (100 + n0) (map re_fd es)) ->
blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX ->
mo_ok MT S oa_cost ->
forall kr : nat,
rp_RM RP S (W_op_add.oa_rk + kr) ->
cnt_ok_pk RP W_op_add.oa_peak (ablocks B ly S) ->
SRrG segs R W (cfg_at segs pc regs mem md) (oa_post_xR G regs ly S Hp W mem md os n0 T es kr).
Definition oa_spec_g_xR (pc : Z) : Prop := forall G, gx_prog_x B ARx G -> oa_spec_xR G pc.
Lemma oa_spec_g_xR_of_kit : forall pc, W_op_add.oa_spec_g_xR (PI := PB_fr) B PST ARx R MT RP pc -> oa_spec_g_xR pc.
Proof. intros pc H G HGP. exact (H G HGP). Qed.

(* the walk's journal at R, at the empty ghost list (AJ0 at R), and the runs over it *)
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Let RUNXR := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOXR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Ltac hp0gR HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
(* a strict journal is one at R (ajournal_gx_xR_mono, WLE_R) *)
Lemma pro_aj_lift_xR : forall G XO OUT STK sp0 FP ly S Hp (W : world segs) mem md own ly' S' Hp' (W' : world segs)
    mem' md' k,
  ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
  eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ]. Qed.
(* a strict walk whose every end goes on at R is a walk at R (SRr_SRrG, WLE_R; SRrG_bind, R_trans) *)
Lemma pro_srr_srrG : forall (W : world segs) c (Q : world segs -> config -> Prop),
  SRr segs W c (fun W' c' => SRrG segs R W' c' Q) -> SRrG segs R W c Q.
Proof.
  intros W c Q H. eapply (SRrG_bind segs R R_trans); [exact (SRr_SRrG segs R WLE_R _ _ _ H) |].
  intros W' c' _ HQ. exact HQ.
Qed.
(* :566 pro_frame_wr_x at R *)
Lemma pro_frame_wr_xR : forall cx own ly3 S3 k (W : world segs) mem md,
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k ->
  forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a.
Proof.
  intros cx own ly3 S3 k W mem md (_ & _ & (memS & HJi & _) & _) a Ha. rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  apply (apresent_writable segs). apply Hpres. lia.
Qed.
(* :890-949 pro_call_img_x / _blk_x / _hi_x / _frm_x at R (a callee's post journal at R) *)
Lemma pro_call_img_xR : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  AJ0R G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k -> ~ YI16.sink_open_fp FP ->
  forall a, in_img segs a -> ~ inG G' a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HJx Hsk a Him HnG Hno He.
  pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Him Hno He (HPST a Him) ltac:(apply fp_spares_closed; exact Hsk)).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.

Lemma pro_call_blk_xR : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G' ->
  AJ0R G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall p n j, In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly1 S1) -> 0 <= j < req_size n ->
  ~ inFP FP (p + j) -> aview segs (w_H W1) m1 (p + j) = aview segs (w_H W0) m0 (p + j).
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx p n j H0 H1 Hj Hfp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 p n j H0 H1 Hj Hfp).
  destruct (al0_blocks ly1 S1 W1 m1 md1 p n HAR1 H1) as (_ & H4096 & Hbc & _).
  apply (aview_gagree segs G' (w_H W0) m0 memS (p + j) HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  exact (blk_img0 ly1 S1 W1 m1 md1 p n (p + j) HAR1 H1 ltac:(lia) (proj1 (HGok _ Hin))).
Qed.

Lemma pro_call_hi_xR : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G' ->
  AJ0R G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx a Ha Hno.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  rewrite (F1 a Ha Hno).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.

Lemma pro_call_frm_xR : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  AJ0R G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall cid pos a, In (cid, pos) (frames S0) ->
  (in_zr a (frame_rng ly0 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly0 cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ inG G' a -> aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HJx cid pos a Hin Hr Hfp Ha HnG.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cid pos a Hin Hr Hfp).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
(* :1028 pro_ff_eq_x at R *)
Lemma pro_ff_eq_xR : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' W' mem' md' k cid pos,
  AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF.
  reflexivity.
Qed.
(* :303 ajournal_gx_rom_view0 at R (W_journal_x's ajournal_gx_rom_view_xR, from HPST) *)
Lemma ajournal_gx_rom_view0R : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs)
    mem' md' k,
  AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  rom_out segs B G -> rom_view segs W mem -> rom_view segs W' mem'.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR Hrv.
  apply (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low G XO OUT STK sp0 FP ly S [] W mem md own ly' S' []
    W' mem' md' k HJ HR); [|exact Hrv].
  intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr].
Qed.

(* :577 pro_fin_x at R: the cut journal from the entry is at R (op_add's step re-hides at most R); the set-up is a strict
   run over it (RUNXR / RUNTOXR), ending at cut_x's INV_H_xR / INV_X_xR *)
Lemma pro_fin_xR : forall cx (W : world segs) regs mem md ly3 S3 k m fpos,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  pro_fr cx (frame_addr ly3 1 fpos) W mem -> pro_regs cx (frame_addr ly3 1 fpos) regs ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m -> lm_k m = 0 -> ainput_at B cx ly3 S3 W mem -> rom_view segs W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx 0 m ly3 S3 -> NP S3 -> RINV cx 0 m ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_pro_ret)) mem (seg_rom segs)) md)
    (fun W' c' => INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] 0 W' c' \/
      INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] W' c').
Proof.
  intros cx W regs mem md ly3 S3 k m fpos HB HJ HFR HRG HFLG HMOD Hk0 HIN HRV HSEP HLS HNP HRI.
  pose proof (pro_Fb_x cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity.
  pose proof HB as (HAI0 & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (Hn26 : 0 <= c_n cx < 2 ^ 26)
    by (unfold fr_lib_pre_cf_x in HPRE0; destruct HPRE0 as (_ & _ & _ & _ & [(H0 & _) | (H0 & _)] & _); lia).
  set (FF := frame_addr ly3 1 fpos) in *. set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin1 : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct (frames_bounds0 ly3 S3 W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  destruct (al0_frames ly3 S3 W mem md 1 fpos HAR Hin1) as (HFFal & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1, HFFal.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  pose proof HFR as (HSV & H24 & H48 & H56 & H64 & H72 & H80 & H88 & H184 & HH0 & HH8 & HH16 & HFW & HSH & HSW).
  pose proof HRG as (R2 & R8 & R9 & R21 & R22 & R24 & R26 & R3 & R4).
  assert (HDIV : val_mem segs (arm W mem) 0x10320 8 DIV10)
    by (apply (rom_vmb_ok W mem _ _ _ HRV); vm_compute; reflexivity).
  assert (HWR : forall a, F + 32 <= a < F + 160 -> writable_at segs (arm W mem) a)
    by (intros a Ha; apply (pro_frame_wr_xR cx _ _ _ _ W mem md HJ); unfold sp0 in *; lia).
  destruct (pro_entry2 W regs mem F FF R9 ltac:(lia) ltac:(lia) HFal ltac:(lia) HFFal H88 HDIV HWR) as [HS SHOK].
  remember (Eimg (Ereg regs (pro2_extra FF))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (pro2_extra FF)) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  assert (E21 : ew E 21 = Z_to_bv 64 (c_n cx))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
  assert (E24 : ew E 24 = Z_to_bv 64 (SB + FF / 8))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E33 : ew E 33 = Z_to_bv 64 FF)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  clear HE.
  pose proof pro_vals as (PV67 & PV68 & PV69 & PV70 & PV71 & PV72 & PV73 & PV74 & PV75 & PV76 & PV77 & PV78 &
    PVO22 & PVO25 & PVO26 & PVO0 & PVO32).
  assert (VI : forall j v, VAL (A_HI j) = v -> (A_HI j < A_LIM)%nat -> 0 <= v < 2 ^ 64 -> ew E (A_HI j) = Z_to_bv 64 v).
  { intros j v Hv Hj Hr. apply bv_eq. rewrite (HEI (A_HI j) ltac:(unfold A_HI, A_TEXT in *; lia)).
    rewrite unsigned_lit_small by exact Hr. exact Hv. }
  (* every fact of the cut but the slots the set-up stores, for any memory that keeps the bytes outside them *)
  assert (Herr : 0 <= as_errno B /\ as_errno B + 4 <= CEIL8) by (rewrite HEV; unfold TFIB_ERRNO_A, CEIL8; lia).
  assert (KEEPF : forall mf, (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (F + 96 <= a < F + 160) ->
      abyte_kept W mem W mf a) ->
    amodel_at B ly3 S3 W mf m /\ ainput_at B cx ly3 S3 W mf /\ rom_view segs W mf /\ jt_rom W mf /\
    pro_fr cx FF W mf /\ sv8 W mf (FF + 120) (flag_addr ly3 1 fpos)).
  { intros mf KO.
    assert (KL : forall a, 0 <= a < CEIL8 -> abyte_kept W mem W mf a)
      by (intros a Ha; apply KO; unfold CEIL8 in *; lia).
    assert (HRVf : rom_view segs W mf) by exact (lt_rom_kept W W mem mf HRV KL).
    split; [exact (W_LLVMFuzzerTestOneInput_latch_x.lt_amodel_kept_x B ARx LAWS ly3 S3 [] W mem md W mf m HAR HMOD (proj1 Herr) (proj2 Herr) KL)|].
    split; [exact (W_LLVMFuzzerTestOneInput_latch_x.lt_ainput_kept_x B ARx LAWS cx ly3 S3 [] W mem md W mf HAR HIN (eq_sym HlenP) KL)|].
    split; [exact HRVf|]. split; [exact (pro_jt W mf HRVf)|].
    assert (KH : forall a v, (forall x, a <= x < a + 8 -> abyte_kept W mem W mf x) -> sv8 W mem a v -> sv8 W mf a v)
      by (intros a v Hk Hv; exact (lt_sv8_kept W W mem mf a v Hk Hv)).
    split; [|apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HFLG]].
    split; [intros o r Hor; apply KH; [|exact (HSV o r Hor)]; intros x Hx;
            unfold saved_regs in Hor; cbn [In] in Hor;
            repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; apply KO; unfold sp0 in *; lia|]);
            destruct Hor|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H24]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H48]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H56]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H64]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H72]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H80]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H88]|].
    split; [apply KH; [intros x Hx; apply KO; unfold sp0 in *; lia | exact H184]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH0]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH8]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH16]|].
    split; [apply (akept_awr W mem W mf); [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HFW]|].
    split; [apply (akept_garr8 W mem W mf); [intros x Hx; apply KL; cbn [length fake_shadow] in Hx;
            pose proof (Z.div_le_upper_bound FF 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SB, CEIL8 in *; lia
            | exact HSH]|].
    apply (akept_awr W mem W mf); [intros x Hx; apply KL;
      pose proof (Z.div_le_upper_bound FF 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SB, CEIL8 in *; lia | exact HSW]. }
  paj_run_tok_x RUNXR HS HJ SHOK Bspan.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr;
        first [ lia | left; split; [left; unfold sp0 in *; lia | lia] ] | ]).
    destruct Hin'. }
  clear HF.
  lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) =>
    assert (KO1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (F + 96 <= a < F + 160) ->
      abyte_kept W m1 W m2 a) end.
  { intros a Ha H1 H2. apply (pro_kept_frame E _ W _ _ a HFr Ha). intros (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]).
    destruct Hin'. }
  clear HFr.
  psrr_branch_tok RUNXR BR HS SHOK Bspan.
  - (* beqz s5: an empty input goes to the shutdown block *)
    assert (Hn0 : c_n cx = 0).
    { rewrite branch_eq_U, (U_atom E 21 (c_n cx) E21), U_lit in Hc by lia. apply Z.eqb_eq in Hc. exact Hc. }
    paj_run_to_tok_x RUNTOXR HS HJ SHOK Bspan AF_LLVM_exit.
    { intros a (r & Hin' & Hr).
      lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
      cbn [In] in Hin'.
      repeat (destruct Hin' as [<- | Hin'];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr;
          first [ lia | left; split; [left; unfold sp0 in *; lia | lia] ] | ]).
      destruct Hin'. }
    clear HF.
    lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) =>
      assert (KO2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (F + 96 <= a < F + 160) ->
        abyte_kept W m1 W m2 a) end.
    { intros a Ha H1 H2. apply (pro_kept_frame E _ W _ _ a HFr Ha). intros (r & Hin' & Hr).
      lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
      cbn [In] in Hin'.
      repeat (destruct Hin' as [<- | Hin'];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]).
      destruct Hin'. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (pro2_extra FF) pro_kept HS HAE
      ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
    pro_rgn HS 2%nat HR96.
    pmkst HS.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rf _ ?mf _; cfg_model := ?df |} _ =>
      apply SRr_ret; right; exists rf, mf, df, 0 end.
    split; [reflexivity|].
    lazymatch type of KO2 with forall a, _ -> _ -> _ -> abyte_kept _ _ _ ?m2 _ =>
      destruct (KEEPF m2 (fun a H0 H1 H2 => abyte_kept_trans W W W _ _ _ a (KO1 a H0 H1 H2) (KO2 a H0 H1 H2)))
        as (HMODf & HINf & HRVf & HJTf & HFRf & HFLf) end.
    split; [exact HJTf|].
    exists [(1, fpos)], ly3, S3, [], k, m, fpos.
    split; [exact HJ|]. split; [reflexivity|].
    split.
    { apply (pro_aframe cx false FF W _ HFRf).
      - pose proof (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 96 8 (SOff 24 0) (SB + FF / 8) HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E24, unsigned_lit_small, Z.add_0_r by (unfold SB; lia);
                 reflexivity) ltac:(unfold SB in *; zside) ltac:(zside)) as V96.
        exact V96.
      - intros Hf. discriminate Hf.
      - exact (pro_frame_wr_xR cx _ _ _ _ W _ _ HJ).
      - lia.
      - lia. }
    split; [exact HFLf|].
    split; [exact HMODf|]. split; [exact HINf|]. split; [exact HRVf|].
    split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
    unfold lregs_X.
    split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite Q18; change 355%nat with (A_HI 75); apply VI; [exact PV75 | cbv; lia | unfold HI_G_SRC; lia]|].
    split; [rewrite Q23; change 354%nat with (A_HI 74); apply VI; [exact PV74 | cbv; lia | unfold HI_G_NSRC; lia]|].
    split; [rewrite Q25; change 356%nat with (A_HI 76); apply VI; [exact PV76 | cbv; lia | unfold HI_G_NOUT; lia]|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    split; [rewrite Hk0; lia | unfold OPS_MAX; lia].
  - (* the loop head *)
    assert (Hn0 : c_n cx <> 0).
    { rewrite branch_eq_U, (U_atom E 21 (c_n cx) E21), U_lit in Hc by lia. apply Z.eqb_neq in Hc. exact Hc. }
    paj_run_to_tok_x RUNTOXR HS HJ SHOK Bspan AF_LLVM_head.
    { intros a (r & Hin' & Hr).
      lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
      cbn [In] in Hin'.
      repeat (destruct Hin' as [<- | Hin'];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr;
          first [ lia | left; split; [left; unfold sp0 in *; lia | lia] ] | ]).
      destruct Hin'. }
    clear HF.
    lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) =>
      assert (KO2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (F + 96 <= a < F + 160) ->
        abyte_kept W m1 W m2 a) end.
    { intros a Ha H1 H2. apply (pro_kept_frame E _ W _ _ a HFr Ha). intros (r & Hin' & Hr).
      lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
      cbn [In] in Hin'.
      repeat (destruct Hin' as [<- | Hin'];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]).
      destruct Hin'. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (pro2_extra FF) pro_kept HS HAE
      ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
    prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7. prreg HS (19%bv : bv 5) Q19.
    prreg HS (20%bv : bv 5) Q20. prreg HS (27%bv : bv 5) Q27.
    pro_rgn HS 0%nat HR32. pro_rgn HS 2%nat HR96.
    assert (Hgs : rg_s fr_RG = 0x5d88e0) by (vm_compute; reflexivity).
    assert (E263 : ew E (A_OBJ 22) = Z_to_bv 64 (rg_s fr_RG))
      by (apply bv_eq; rewrite (HEI (A_OBJ 22) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
          rewrite unsigned_lit_small by (rewrite Hgs; lia); rewrite PVO22, Hgs; reflexivity).
    change (A_OBJ 22) with 263%nat in E263.
    pose proof (pro_sh_den E 26 263 SB (rg_s fr_RG) 0 E26 E263 ltac:(unfold SB; lia) ltac:(lia) ltac:(lia)) as D112.
    pose proof (pro_sh_den E 26 263 SB (rg_s fr_RG) 4 E26 E263 ltac:(unfold SB; lia) ltac:(lia) ltac:(lia)) as D152.
    rewrite Z.add_0_r in D112.
    pmkst HS.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rf _ ?mf _; cfg_model := ?df |} _ =>
      apply SRr_ret; left; exists rf, mf, df end.
    split; [reflexivity|].
    lazymatch type of KO2 with forall a, _ -> _ -> _ -> abyte_kept _ _ _ ?m2 _ =>
      destruct (KEEPF m2 (fun a H0 H1 H2 => abyte_kept_trans W W W _ _ _ a (KO1 a H0 H1 H2) (KO2 a H0 H1 H2)))
        as (HMODf & HINf & HRVf & HJTf & HFRf & HFLf) end.
    split; [exact HJTf|].
    exists [(1, fpos)], ly3, S3, [], k, m, fpos.
    split; [exact HJ|]. split; [reflexivity|].
    split.
    { apply (pro_aframe cx true FF W _ HFRf).
      - exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 96 8 (SOff 24 0) (SB + FF / 8) HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E24, unsigned_lit_small, Z.add_0_r by (unfold SB; lia);
                 reflexivity) ltac:(unfold SB in *; zside) ltac:(zside)).
      - intros _.
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 32 40 32 40 32 8 (SOff 263 0) (rg_s fr_RG) HR32 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E263, unsigned_lit_small, Z.add_0_r by lia;
                 reflexivity) ltac:(zside) ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 104 8 (SOff 356 0) HI_G_NOUT HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
                 change 356%nat with (A_HI 76); apply VI; [exact PV76 | cbv; lia | unfold HI_G_NOUT; lia])
          ltac:(unfold HI_G_NOUT; zside) ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 112 8
          (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 263 0) (SLit 3))) (SB + rg_s fr_RG / 8) HR96 U9
          ltac:(cbn [In]; tauto) D112 ltac:(rewrite Hgs; unfold SB; change (6129888 / 8) with 766236; zside)
          ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 120 8 (SOff 354 0) HI_G_NSRC HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
                 change 354%nat with (A_HI 74); apply VI; [exact PV74 | cbv; lia | unfold HI_G_NSRC; lia])
          ltac:(unfold HI_G_NSRC; zside) ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 128 8 (SOff 263 4) (rg_s fr_RG + 4) HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E263, unsigned_lit_small by lia; reflexivity)
          ltac:(zside) ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 136 8 (SLit DIV10) DIV10 HR96 U9
          ltac:(cbn [In]; tauto) eq_refl ltac:(unfold DIV10; zside) ltac:(zside))|].
        exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 152 8
          (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 263 4) (SLit 3))) (SB + (rg_s fr_RG + 4) / 8) HR96 U9
          ltac:(cbn [In]; tauto) D152 ltac:(rewrite Hgs; unfold SB; change ((6129888 + 4) / 8) with 766236; zside)
          ltac:(zside)).
      - exact (pro_frame_wr_xR cx _ _ _ _ W _ _ HJ).
      - lia.
      - lia. }
    split; [exact HFLf|].
    split; [exact HMODf|]. split; [exact HINf|]. split; [exact HRVf|].
    split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
    unfold lregs_H, lregs_common.
    split.
    { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
      split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
      split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
      split; [rewrite Q18; change 355%nat with (A_HI 75); apply VI; [exact PV75 | cbv; lia | unfold HI_G_SRC; lia]|].
      split; [rewrite Q19, E33, unsigned_lit_small by lia; reflexivity|].
      split; [rewrite Q20; reflexivity|].
      split; [rewrite Q23; change 354%nat with (A_HI 74); apply VI; [exact PV74 | cbv; lia | unfold HI_G_NSRC; lia]|].
      split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
      split; [rewrite Q25; change 356%nat with (A_HI 76); apply VI; [exact PV76 | cbv; lia | unfold HI_G_NOUT; lia]|].
      split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
      split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
      rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4. }
    split; [rewrite Q6; reflexivity|]. split; [rewrite Q7; reflexivity|].
    split; [rewrite (KR 21%bv ltac:(cbv; tauto)), Hk0, Z.sub_0_r; exact R21|].
    split; [rewrite (KR 22%bv ltac:(cbv; tauto)), Hk0, Z.add_0_r; exact R22|].
    split; [rewrite Q27; reflexivity|].
    split; [unfold OPS_MAX; lia|].
    rewrite Hk0. lia.
Qed.

(* :1097 pro_mid_x at R: the journal to the call is the strict one; op_add's step is its R contract (W2_op_add_R),
   composed by SRrG_bind; its post journal is at R, so the cut journal after it is ajournal_gx_sub_xR's, and the
   facts the strict text reads off op_add's journal are their _xR twins; the set-up is pro_fin_xR, lifted *)
Lemma pro_mid_xR : forall cx regs mem md S2 k fpos,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 (c_W cx) mem md k ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, fpos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 -> NP S2 ->
  pro_fr cx (frame_addr (c_ly cx) 1 fpos) (c_W cx) mem ->
  sv8 (c_W cx) mem (frame_addr (c_ly cx) 1 fpos + 120) (flag_addr (c_ly cx) 1 fpos) ->
  getr regs 1 = w64 (BASE + A_pro_ret) -> pro_regs cx (frame_addr (c_ly cx) 1 fpos) regs ->
  pro_glob (c_W cx) mem ->
  (forall a, pro_ks cx a -> aview segs (w_H (c_W cx)) mem a = aview segs (w_H (c_W cx)) (c_mem cx) a) ->
  SRrG segs R (c_W cx) (cfg_at segs (BASE + AF_fr_op_add) regs mem md)
    (fun W' c' => INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] 0 W' c' \/
      INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] W' c').
Proof.
  intros cx regs mem md S2 k fpos HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HNP2 HFR HFLG Hra HRG HGL KEEP.
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & Hra0 & H10 & H11 & Hin & Hnl & Hgarr & Hfrs & Hlive & _ & _ & Hgi & Hrom & _).
  destruct Hgi as (HGP0 & HCL & (T & HRR) & (c0 & O & mx0 & cap & out & HAO) & (gn0 & HGN) & HLK & HWK & HTU &
    (lst & HLS0) & HLW).
  (* the room round: the pre's XCNT (its 22nd conjunct) at fr_gi's table T and g_out (cap, out), read off the same three
     cells (prx_cells), and HFH0 *)
  pose proof HPRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HXC0 & _).
  destruct HXC0 as (Tx & cx0 & Ox & mxx & capx & outx & HRRx & HAOx & HXC).
  pose proof (proj1 HPREE) as HARe.
  destruct (prx_cells _ _ _ _ _ _ T c0 O mx0 cap out HARe HRR HAO) as (CT & CC & CO).
  destruct (prx_cells _ _ _ _ _ _ Tx cx0 Ox mxx capx outx HARe HRRx HAOx) as (CTx & CCx & COx).
  rewrite CT in CTx. rewrite CC in CCx. rewrite CO in COx.
  injection CTx as <-. injection CCx as <-. injection COx as <-. clear HRRx HAOx.
  change (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)]) with (input_blks cx) in HXC.
  assert (HFH0 : fr_hblks (c_W cx) (c_mem cx) = (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out).
  { unfold fr_hblks. cbv zeta. change tfibsegs with segs. rewrite CT, CO, CC. unfold aout_blks. reflexivity. }
  pose proof (pro_Fb_x cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof (HFP_pro cx [] T c0 O mx0 cap out HB HRR HAO) as ((rest0 & HPERM0) & HFPT & HFPO).
  set (W := c_W cx) in *. set (FF := frame_addr (c_ly cx) 1 fpos) in *. set (F := lf_F cx) in *.
  set (sp0 := spZ (c_regs cx)) in *.
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
  assert (Hgs : rg_s fr_RG = 0x5d88e0) by (vm_compute; reflexivity).
  (* ---- kept from the entry to the call ---- *)
  assert (KG : forall a, inG G_keep a -> aview segs (w_H W) mem a = aview segs (w_H W) (c_mem cx) a)
    by (intros a Ha; apply KEEP; left; exact Ha).
  assert (KBk : forall p n a, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> p <= a < p + req_size n ->
      aview segs (w_H W) mem a = aview segs (w_H W) (c_mem cx) a)
    by (intros p0 n0 a Hp Ha; apply KEEP; right; exists p0, n0; split; [exact Hp | exact Ha]).
  assert (KGv : forall a n v, rng_inb a (Z.of_nat n) G_keep = true ->
      val_mem segs (arm W (c_mem cx)) a n v -> val_mem segs (arm W mem) a n v).
  { intros a n0 v Hr Hv. apply (pro_vm_view W W (c_mem cx) mem); [|exact Hv].
    intros x Hx. exact (KG x (rng_cover a (Z.of_nat n0) G_keep Hr x Hx)). }
  assert (AW : forall a n, rng_inb a n G_fr_obj = true -> forall (W' : world segs) m', awr W' m' a n).
  { intros a n0 Hr W' m' i Hi. apply (G_obj_wr (a + i) (rng_cover a n0 G_fr_obj Hr (a + i) ltac:(lia))). }
  (* ---- the call's facts ---- *)
  assert (HCLc : forall i, (i < 4)%nat -> asrc_closed W mem (oa_HA i)).
  { intros i Hi. destruct (HCL i Hi) as [HZ _]. split.
    - apply (pro_garr8_view W W (c_mem cx) mem); [|exact HZ].
      intros x Hx. apply KG. rewrite repeat_length in Hx. change (Z.of_nat (Z.to_nat ASRC)) with 96 in Hx.
      apply (rng_cover (rg_s fr_RG) 384 G_keep ltac:(vm_compute; reflexivity)).
      unfold oa_HA, fr_RG in *. unfold ASRC in Hx. rewrite Hgs in *. lia.
    - apply (AW (oa_HA i) ASRC). unfold oa_HA, ASRC.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%nat as Hc by lia.
      destruct Hc as [->|[->|[->| ->]]]; vm_compute; reflexivity. }
  assert (Hos : forall i, nth i [0; 0; 0; 0] 0 = 0) by (intros i; destruct i as [|[|[|[|[|i]]]]]; reflexivity).
  assert (HRRc : ra_rel B fr_RG (c_ly cx) S2 W mem T []).
  { destruct HRR as [(HT0 & _ & (E1 & E2 & E3 & E4 & E5 & E6)) | HAT].
    - left. split; [exact HT0|]. split; [reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E1]|]. split; [apply AW; vm_compute; reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E3]|]. split; [apply AW; vm_compute; reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E5] | apply AW; vm_compute; reflexivity].
    - right. pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & HTin & _).
      apply (arelay_at_kept B fr_RG (c_ly cx) (c_S cx) W (c_mem cx) (c_ly cx) S2 W mem T [] HAT).
      + intros r Hr a Ha. split.
        * unfold arelay_fp in Hr. cbn [map concat app] in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
          -- apply KG. refine (rng_cover (rg_src fr_RG) 8 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply KG. refine (rng_cover (rg_nsrc fr_RG) 4 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply KG. refine (rng_cover (rg_capsrc fr_RG) 4 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply (KBk T ATABLE a HTin). change (req_size ATABLE) with 896. unfold ATABLE in Ha. lia.
        * intros _. unfold arelay_fp in Hr. cbn [map concat app] in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
          -- refine (G_obj_wr a (rng_cover (rg_src fr_RG) 8 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- refine (G_obj_wr a (rng_cover (rg_nsrc fr_RG) 4 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- refine (G_obj_wr a (rng_cover (rg_capsrc fr_RG) 4 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- rewrite <- Eab2 in HTin.
             destruct (al0_blocks _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & _ & _ & _ & Hpr & _).
             apply (apresent_writable segs). apply (proj1 (Hpr a ltac:(change (req_size ATABLE) with 896;
               unfold ATABLE in Ha; lia))).
      + intros b Hb. rewrite Eab2. cbn [arelay_blks map concat app] in Hb. destruct Hb as [<- | []]. exact HTin. }
  assert (HLKc : alock_at fr_RG W mem false).
  { destruct HLK as (L1 & L2 & L3 & L4).
    split; [apply KGv; [vm_compute; reflexivity | exact L1]|].
    split; [apply KGv; [vm_compute; reflexivity | exact L2]|].
    split; [apply KGv; [vm_compute; reflexivity | exact L3] | apply AW; vm_compute; reflexivity]. }
  assert (HWKc : awake_at fr_RG W mem) by (apply KGv; [vm_compute; reflexivity | exact HWK]).
  assert (HRVc : rom_view segs W mem)
    by (eapply ajournal_gx_rom_view0; first [exact Hsegs | exact LAWS | exact HJ | exact pro_rom_out_fr | exact Hrom]).
  (* ---- op_add's afn_pre, its room and its meter ---- *)
  pose proof HFR as (HSV & H24 & H48 & H56 & H64 & H72 & H80 & H88 & H184 & HH0 & HH8 & HH16 & HFW & HSH & HSW).
  pose proof HRG as (R2 & R8 & R9 & R21 & R22 & R24 & R26 & R3 & R4).
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  destruct (pro_afn_pre_at_x cx (c_ly cx) S2 fpos k W mem md regs OA_STK HB HJ HSV Hsp) as (ch & HPREc).
  { rewrite Hra. apply ret_ok_codeptr_v; [unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput; lia | reflexivity]. }
  { unfold raZ. rewrite Hra, unsigned_lit_small by (unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput; lia).
    unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput. lia. }
  { exact R3. } { exact R4. } { exact R8. }
  { unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK. lia. }
  { unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK, LLVMF_STK. lia. }
  destruct (LS_pro_oa cx [] S2 fpos HB Eab2 Hfrs2 Hnev2 Hbb2 HMO2) as (Hroom & Hmok).
  (* the entry's T: when the table exists it is a live block of the entry, above 4096 *)
  assert (HT4096 : T <> 0 -> 4096 <= T /\ In (T, ATABLE) (ablocks B (c_ly cx) (c_S cx))).
  { intros HT0. destruct HRR as [(HT0' & _) | HAT]; [contradiction|].
    pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & HTin & _). split; [|exact HTin]. rewrite <- Eab2 in HTin.
    destruct (al0_blocks _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & H4096 & _). exact H4096. }
  (* ---- op_add, at its own G ---- *)
  assert (HGcov1 : forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G_oa a).
  { intros a Ha. change (inG ((rg_s fr_globals, 384) :: (A_NFD, 4) :: RA_G fr_globals) a).
    apply inG_cons. left. unfold in_zr, ASRC in *. cbn [fst snd]. lia. }
  assert (HGcov2 : forall a, A_NFD <= a < A_NFD + 4 -> inG G_oa a).
  { intros a Ha. change (inG ((rg_s fr_globals, 384) :: (A_NFD, 4) :: RA_G fr_globals) a).
    apply inG_cons. right. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
  assert (HGcov3 : forall a, inG (RA_G fr_globals) a -> inG G_oa a)
    by (intros a Ha; unfold G_oa; apply inG_app; right; exact Ha).
  destruct HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  eapply (SRrG_bind segs R R_trans).
  { exact (oa_spec_g_xR_of_kit _ W2_op_add_R G_oa G_oa_prog_x W (c_ly cx) S2 [] regs mem md ch [0; 0; 0; 0] 0 T [] HPREc
      ltac:(rewrite Hsp; exact HFal) ltac:(rewrite Hfrs2; vm_compute; reflexivity) eq_refl
      ltac:(intros i _; rewrite Hos; lia)
      ltac:(intros i Hi; rewrite Hos; exact (pro_closed_vm W mem _ (HCLc i Hi)))
      ltac:(intros i Hi _; exact (HCLc i Hi))
      G3 ltac:(lia) HZS HGcov1 HGcov2 HGcov3 HRRc HLKc HWKc HRVc
      ltac:(intros _; split; [cbn; lia | intros []]) Hroom Hmok
      (* the room round: the room from the seat's NP (kr := 0), the counts from the entry's xcnt_ok (LS_cnt) *)
      0%nat (proj2 (RP_NP S2 _) HNP2) (LS_cnt cx T cap out S2 HXC Eab2)). }
  cbv beta. intros W3 c3 HR3
    (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & kk & -> & HJo & HP4 & HAPK & HOK & Hfrs4 & HRM4 & HSome & HERR4).
  (* the room after op_add: its post's rp_RM at kr = 0 is the cut's NP *)
  pose proof (proj1 (RP_NP S4 0%nat) HRM4) as HNP4.
  hp0gR HJo.
  assert (Hof : oa_first [0; 0; 0; 0] = Some 0%nat) by reflexivity.
  rewrite Hof in HSome. cbv beta iota in HSome.
  destruct HSome as (q & T' & pj & HSRC & HNFD & HREL & HLK4 & HPERM & HMLE).
  cbn [app] in HREL. change (100 + 0) with 100 in HSRC, HREL. change (0 + 1) with 1 in HNFD.
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJo) as HAR4.
  assert (Hsk : ~ YI16.sink_open_fp (oa_FP [0; 0; 0; 0] T [])).
  { unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
    intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
    destruct (HT4096 HT0) as (H4096 & _). lia. }
  (* the journal from the entry, through op_add (lifted from G_oa to G_fr) *)
  pose proof (ajournal_gx_G_mono_xR segs B PST ARx G_oa G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G_oa_fr HJo) as HJo'.
  assert (HFP1 : forall a, inFP (oa_FP [0; 0; 0; 0] T []) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B (c_ly cx) S2) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B (c_ly cx) S2) a).
  { intros a Ha. left. unfold oa_FP in Ha. rewrite Hof in Ha. unfold ra_FP in Ha.
    destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [destruct Ha as (r & [] & _)|].
    destruct Ha as (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
    destruct (HT4096 HT0) as (H4096 & HTin).
    split; [apply (HFPT HT0); change (req_size ATABLE) with 896; unfold ATABLE in *; lia|].
    exists T, ATABLE. split; [rewrite Eab2; exact HTin | change (req_size ATABLE) with 896; lia]. }
  (* the cut journal through op_add, at R: the strict journal to the call (lifted) under op_add's R post journal *)
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 [] W mem md k
     OA_STK (spZ regs) 0 [] (oa_FP [0; 0; 0; 0] T []) [] ly4 S4 [] W3 mem4 md4 kk
     (pro_aj_lift_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) HJo'
     ltac:(rewrite Hsp; unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK, LLVMF_STK; lia)
     ltac:(lia) ltac:(lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFP1) as HJ4.
  cbn [app] in HJ4.
  assert (EFF : frame_addr ly4 1 fpos = FF) by exact (pro_ff_eq_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos HJo).
  assert (EFL : flag_addr ly4 1 fpos = flag_addr (c_ly cx) 1 fpos)
    by (pose proof EFF as E'; unfold FF, frame_addr in E'; unfold flag_addr; lia).
  (* ---- what op_add keeps ---- *)
  assert (KP : forall a, inG G_pst a -> aview segs (w_H W3) mem4 a = aview segs (w_H W) mem a).
  { intros a Ha. pose proof (G_pst_obj a Ha) as Ho. destruct (HG a (HG_obj a Ho)) as (Him & Hno & _).
    exact (pro_call_img_xR G_oa OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HJo Hsk a Him (G_pst_oa a Ha) Hno
      (G_obj_err a Ho)). }
  assert (KPv : forall a n v, rng_inb a (Z.of_nat n) G_pst = true ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W3 mem4) a n v).
  { intros a n0 v Hr Hv. apply (pro_vm_view W W3 mem mem4); [|exact Hv].
    intros x Hx. exact (KP x (rng_cover a (Z.of_nat n0) G_pst Hr x Hx)). }
  assert (KGPv : forall a n v, rng_inb a (Z.of_nat n) G_keep = true -> rng_inb a (Z.of_nat n) G_pst = true ->
      val_mem segs (arm W (c_mem cx)) a n v -> val_mem segs (arm W3 mem4) a n v)
    by (intros a n0 v H1 H2 Hv; exact (KPv a n0 v H2 (KGv a n0 v H1 Hv))).
  assert (Hgs' : rg_s fr_globals = 0x5d88e0) by (vm_compute; reflexivity).
  assert (KS3 : forall i, (1 <= i < 4)%nat -> asrc_closed W3 mem4 (oa_HA i)).
  { intros i Hi. destruct (HCLc i ltac:(lia)) as [HZ _]. split.
    - apply (pro_garr8_view W W3 mem mem4); [|exact HZ]. intros x Hx.
      rewrite repeat_length in Hx. change (Z.of_nat (Z.to_nat ASRC)) with 96 in Hx.
      apply HOK.
      + apply HGcov1. unfold oa_HA, ASRC in *. rewrite Hgs' in *. lia.
      + unfold oa_wr. rewrite Hof. intros [Hx1 | [Hx2 | Hx3]].
        * unfold oa_HA, ASRC in *. cbn [Z.of_nat] in Hx1. rewrite Hgs' in *. lia.
        * unfold oa_HA, ASRC, A_NFD in *. rewrite Hgs' in *. lia.
        * pose proof (pro_ra_g x Hx3). unfold oa_HA, ASRC in *. rewrite Hgs' in *. lia.
    - apply (AW (oa_HA i) ASRC). unfold oa_HA, ASRC.
      assert (i = 1 \/ i = 2 \/ i = 3)%nat as Hc by lia.
      destruct Hc as [->|[->| ->]]; vm_compute; reflexivity. }
  (* the entry's blocks the call keeps: all but the relay's table, whose new entry relay_add writes *)
  assert (KBo : forall p n j, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> (T <> 0 -> (p, n) <> (T, ATABLE)) ->
      0 <= j < req_size n -> aview segs (w_H W3) mem4 (p + j) = aview segs (w_H W) mem (p + j)).
  { intros p n j Hp Hne Hj. assert (Hp2 : In (p, n) (ablocks B (c_ly cx) S2)) by (rewrite Eab2; exact Hp).
    apply (pro_call_blk_xR G_oa OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk (proj1 G_oa_prog_x) HJo p n j Hp2).
    - destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)).
      + right. right. exact Hp2.
      + right. exact Hp2.
    - exact Hj.
    - unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
      intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
      destruct (HT4096 HT0) as (H4096 & HTin). rewrite <- Eab2 in HTin.
      destruct (pro_blk_disj_x _ _ _ _ _ (p, n) (T, ATABLE) HAR2 Hp2 HTin (Hne HT0)) as [Hd | Hd]; cbn [fst snd] in Hd;
        change (req_size ATABLE) with 896 in Hd; lia. }
  (* the input block and the controller's buffer are not the relay's table (the entry's blocks are distinct) *)
  assert (ND0 : List.NoDup (input_blks cx ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out ++ rest0)).
  { pose proof HPREE as (HAR0 & _). exact (Permutation_NoDup HPERM0 (pro_nodup_x _ _ _ _ _ HAR0)). }
  assert (HinpT : forall p n, In (p, n) (input_blks cx) -> T <> 0 -> (p, n) <> (T, ATABLE)).
  { intros p n Hp HT0 Heq. rewrite Heq in Hp. apply (pro_nodup_app _ _ (T, ATABLE) ND0 Hp).
    rewrite (proj2 (Z.eqb_neq T 0) HT0). apply in_or_app. left. left. reflexivity. }
  assert (HoutT : forall b, In b (aout_blks cap out) -> T <> 0 -> b <> (T, ATABLE)).
  { intros b Hb HT0 Heq. rewrite Heq in Hb. pose proof (pro_nodup_app_r _ _ ND0) as ND1.
    rewrite (proj2 (Z.eqb_neq T 0) HT0) in ND1. cbn [app] in ND1. inversion ND1 as [|x l Hx _]; subst.
    apply Hx. apply in_or_app. left. exact Hb. }
  assert (KBt : forall p n j, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> (T <> 0 -> (p, n) <> (T, ATABLE)) ->
      0 <= j < req_size n -> aview segs (w_H W3) mem4 (p + j) = aview segs (w_H W) (c_mem cx) (p + j))
    by (intros p n j Hp Hne Hj; rewrite (KBo p n j Hp Hne Hj); exact (KBk p n (p + j) Hp ltac:(lia))).
  (* ---- the cut after op_add: the controller's stream ---- *)
  destruct (ERRL ly4 S4 [] W3 mem4 md4 HAR4) as ((v & Hv & Hvr) & Hvw).
  pose proof HAO as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 &
    A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26).
  assert (HAOp : aout_at B fr_RG ly4 S4 W3 mem4 (W_rep.CTL 3 0 0 0 v) O 0 (Z.of_nat (length O)) cap out).
  { split; [apply KPv; [vm_compute; reflexivity | exact G4]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A3]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A5]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A7]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G1]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G2]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G6]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G7]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [exact Hv|]. split; [exact Hvw|]. split; [exact Hvr|].
    split; [left; reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity|].
    split; [left; reflexivity|]. split; [lia|]. split; [reflexivity|].
    destruct A26 as [A26 | (Hc & Hnc & Hio & junk & Hjl & Hjg)]; [left; exact A26|].
    right. split; [exact Hc|]. split; [exact Hnc|].
    assert (Hio2 : In (out, cap) (ablocks B ly4 S4)).
    { destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)); rewrite Eab2;
        [right; right | right]; exact Hio. }
    split; [exact Hio2|]. exists junk. split; [exact Hjl|].
    apply (pro_garr8_view W W3 (c_mem cx) mem4); [|exact Hjg].
    intros x Hx. unfold bzs in Hx. rewrite length_map, length_app in Hx.
    replace x with (out + (x - out)) by lia.
    apply (KBt out cap (x - out)); [exact Hio | intros HT0; apply (HoutT (out, cap));
      [unfold aout_blks; rewrite (proj2 (Z.eqb_neq cap 0) ltac:(lia)); left; reflexivity | exact HT0] |].
    pose proof (req_size_pos cap ltac:(lia)) as [_ Hrc]. lia. }
  (* the input *)
  assert (HINp : ainput_at B cx ly4 S4 W3 mem4).
  { split.
    - destruct Hin as [Hin | (Hn & Hpin)]; [left; exact Hin|]. right. split; [exact Hn|].
      destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)); rewrite Eab2;
        [right; right | right]; exact Hpin.
    - destruct Hin as [(Hn0 & _) | (Hn & Hpin)].
      + rewrite Hnl in Hn0. assert (Hpl : c_pl cx = []) by (apply length_zero_iff_nil; lia).
        rewrite Hpl. intros j Hj. cbn in Hj. lia.
      + apply (pro_garr8_view W W3 (c_mem cx) mem4); [|exact Hgarr].
        intros x Hx. rewrite length_map in Hx. rewrite <- Hnl in Hx. replace x with (c_p cx + (x - c_p cx)) by lia.
        apply (KBt (c_p cx) (c_n cx) (x - c_p cx)); [exact Hpin | intros HT0; apply (HinpT (c_p cx) (c_n cx));
          [unfold input_blks; rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)); left; reflexivity | exact HT0] |].
        pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrc]. lia. }
  (* the model *)
  assert (HMOD4 : amodel_at B ly4 S4 W3 mem4 (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out)).
  { unfold amodel_at, pro_m. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [reflexivity|].
    split.
    { intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth aslot].
      - exact HSRC.
      - exact (KS3 1%nat ltac:(lia)).
      - exact (KS3 2%nat ltac:(lia)).
      - exact (KS3 3%nat ltac:(lia)).
      - lia. }
    split; [exact HREL|]. split; [exact HAOp|].
    split; [split; [apply KPv; [vm_compute; reflexivity | exact G5]
                  | split; [apply AW; vm_compute; reflexivity | left; reflexivity]]|].
    split; [exact HLK4|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HWK]|].
    split; [exact HNFD|]. split; [apply AW; vm_compute; reflexivity|]. split; [unfold OPS_MAX; lia|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HTU]|].
    split; [exists lst; apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HLS0]|].
    apply AW; vm_compute; reflexivity. }
  (* the frame and the fake frame *)
  assert (HIV : forall x, F <= x < 2 ^ 47 -> aview segs (w_H W3) mem4 x = aview segs (w_H W) mem x).
  { intros x Hx. apply (pro_call_hi_xR G_oa OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk (proj1 G_oa_prog_x) HJo x).
    - unfold CEIL8 in *. lia.
    - rewrite Hsp. lia. }
  assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  pose proof (frm_off_imgP_x B ARx LAWS IMGCx _ _ [] _ _ _ 1 fpos HAR2 Hin1) as HFimg.
  change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg. unfold off_img in HFimg.
  destruct (frames_bounds0 _ _ _ _ _ 1 fpos HAR2 Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (FRV : forall x, (FF <= x < FF + 128) \/ (SB + FF / 8 <= x < SB + FF / 8 + 16) ->
      aview segs (w_H W3) mem4 x = aview segs (w_H W) mem x).
  { intros x Hx. apply (pro_call_frm_xR G_oa OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HJo 1 fpos x Hin1).
    - unfold frame_rng, in_zr, shadow_addr. rewrite <- SB_SHADOW_OFF. cbn [fst snd].
      change (fs_frame_bytes 1) with 128. change (128 / 8) with 16. fold FF. lia.
    - unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
      intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
      destruct (HT4096 HT0) as (H4096 & HTin). rewrite <- Eab2 in HTin.
      destruct (al0_blocks _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & _ & _ & Happ & _).
      change (req_size ATABLE) with 896 in Happ.
      destruct Hx as [Hx | Hx].
      + destruct (pro_blk_frm_x _ _ _ _ _ T ATABLE 1 fpos HAR2 HTin Hin1) as [Hd | Hd];
          change (req_size ATABLE) with 896 in Hd; change (fs_frame_bytes 1) with 128 in Hd; fold FF in Hd; lia.
      + apply (fshadow_not_app FF 16 T 896 x ltac:(lia) ltac:(lia) Happ); [unfold SB in Hx; lia | lia].
    - unfold SB in *. lia.
    - intros HO. pose proof (G_obj_rng x (G_oa_obj x HO)). unfold SB in *. lia. }
  assert (Hin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4, Hfrs2; left; reflexivity).
  destruct (al0_frames ly4 S4 W3 mem4 md4 1 fpos HAR4 Hin4) as (_ & _ & HFp & HFs).
  rewrite EFF in HFp, HFs. change (fs_frame_bytes 1) with 128 in HFp. change (fs_frame_bytes 1 / 8) with 16 in HFs.
  assert (HFR4 : pro_fr cx FF W3 mem4).
  { split.
    { intros o r Hor. apply (pro_vm_view W W3 mem mem4); [|exact (HSV o r Hor)].
      intros x Hx. apply HIV. unfold saved_regs in Hor. cbn [In] in Hor.
      repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; unfold sp0 in *; lia|]). destruct Hor. }
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H24]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H48]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H56]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H64]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H72]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H80]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H88]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H184]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH0]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH8]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH16]|].
    split; [intros i Hi; apply (apresent_writable segs); exact (proj1 (HFp (FF + i) ltac:(lia)))|].
    split; [apply (pro_garr8_view W W3 mem mem4); [intros x Hx; apply FRV; right; cbn [length fake_shadow] in Hx; lia
            | exact HSH]|].
    intros i Hi. apply (apresent_writable segs). pose proof (proj1 (HFs i Hi)) as H.
    unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. exact H. }
  (* the fake frame's last word, its flag pointer (op_add keeps the fake frame) *)
  assert (HFL4 : sv8 W3 mem4 (FF + 120) (flag_addr (c_ly cx) 1 fpos))
    by (apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HFLG]).
  (* the registers op_add keeps *)
  assert (HRG4 : pro_regs cx FF regs4).
  { split; [rewrite (lt_pres regs regs4 2%bv HP4 ltac:(pro_cs)); exact R2|].
    split; [rewrite (lt_pres regs regs4 8%bv HP4 ltac:(pro_cs)); exact R8|].
    split; [rewrite (lt_pres regs regs4 9%bv HP4 ltac:(pro_cs)); exact R9|].
    split; [rewrite (lt_pres regs regs4 21%bv HP4 ltac:(pro_cs)); exact R21|].
    split; [rewrite (lt_pres regs regs4 22%bv HP4 ltac:(pro_cs)); exact R22|].
    split; [rewrite (lt_pres regs regs4 24%bv HP4 ltac:(pro_cs)); exact R24|].
    split; [rewrite (lt_pres regs regs4 26%bv HP4 ltac:(pro_cs)); exact R26|].
    split; [rewrite (lt_pres regs regs4 3%bv HP4 ltac:(pro_cs)); exact R3|].
    rewrite (lt_pres regs regs4 4%bv HP4 ltac:(pro_cs)); exact R4. }
  (* the blocks, as ablocks_sep lists them *)
  assert (Em : model_blks (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out) =
    (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out) by reflexivity.
  assert (ND4 : List.NoDup (ablocks B ly4 S4)) by exact (pro_nodup_x _ _ _ _ _ HAR4).
  assert (HSEP4 : ablocks_sep B fr_FP cx (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out) ly4 S4).
  { split.
    - exists rest0. rewrite Em. rewrite Eab2 in HPERM. exact (pro_sep_perm _ _ _ _ _ T T' q HPERM0 HPERM).
    - intros b Hb. rewrite Em in Hb. destruct Hb as [<- | [<- | Hb]].
      + destruct HPERM as [(HT0 & HP) | (HT0 & -> & HP)].
        * left. intros Hb'. pose proof (Permutation_NoDup HP ND4) as ND. inversion ND as [|x l Hx ND']; subst.
          apply Hx. right. rewrite Eab2. exact Hb'.
        * right. intros a Ha. cbn [fst snd] in Ha. exact (HFPT HT0 a Ha).
      + left. intros Hb'. destruct HPERM as [(_ & HP) | (_ & _ & HP)]; pose proof (Permutation_NoDup HP ND4) as ND.
        * inversion ND as [|x l _ ND']; subst. inversion ND' as [|x l Hx _]; subst. apply Hx. rewrite Eab2. exact Hb'.
        * inversion ND as [|x l Hx _]; subst. apply Hx. rewrite Eab2. exact Hb'.
      + right. exact (HFPO b Hb). }
  (* the cut's two Variables, and the ROM view after op_add *)
  assert (Hc0ex : exists c1 mx1, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c1 O mx1
    (Z.of_nat (length O)) cap out) by (exists c0, mx0; exact HAO).
  assert (HPERM' : exists T0 rest, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest) /\
     ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks B ly4 S4) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly4 S4) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx)))))
    by (exists T, rest0; split; [exact HPERM0|]; split; [exact HXC|]; split; [exact HFH0|];
        rewrite <- Eab2; exact HPERM).
  pose proof (LS_pro cx [] q T' pj (W_rep.CTL 3 0 0 0 v) O cap out S2 fpos ly4 S4 HB Hc0ex eq_refl eq_refl eq_refl
    eq_refl Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HMLE HPERM') as HLS4.
  pose proof (RI_pro cx [] q T' pj (W_rep.CTL 3 0 0 0 v) O cap out HB Hc0ex eq_refl eq_refl eq_refl eq_refl) as HRI4.
  assert (HRV4 : rom_view segs W3 mem4)
    by (eapply ajournal_gx_rom_view0R;
        first [exact Hsegs | exact LAWS | exact HJo | exact (proj1 (proj2 (proj2 G_oa_prog_x))) | exact HRVc]).
  (* the loop's set-up: a strict run over the R journal, lifted *)
  rewrite Hra. rewrite <- EFF in HFR4, HRG4, HFL4. rewrite <- EFL in HFL4.
  apply (SRr_SRrG segs R WLE_R).
  exact (pro_fin_xR cx W3 regs4 mem4 md4 ly4 S4 (k + kk) _ fpos HB HJ4 HFR4 HRG4 HFL4 HMOD4 eq_refl HINp HRV4 HSEP4 HLS4 HNP4 HRI4).
Qed.

(* :1484 pro_at_call_x at R: its facts at op_add's call, then pro_mid_xR *)
Lemma pro_at_call_xR : forall cx S2 k fpos E regs4 m4 md4,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 (c_W cx) m4 md4 k ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, fpos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 -> NP S2 ->
  img_env VAL A_LIM E ->
  bv_unsigned (ew E 2) = spZ (c_regs cx) -> bv_unsigned (ew E 34) = lf_F cx ->
  bv_unsigned (ew E 39) = frame_addr (c_ly cx) 1 fpos ->
  bv_unsigned (ew E 513) = SB + frame_addr (c_ly cx) 1 fpos / 8 -> ew E 33 = Z_to_bv 64 SB ->
  bv_unsigned (ew E 512) = flag_addr (c_ly cx) 1 fpos ->
  (forall r, (r < 32)%nat -> ew E r = getr (c_regs cx) (Z_to_bv 5 (Z.of_nat r))) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 353 1684 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 352 1660 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 351 1636 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 350 1616 8 8 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 349 1588 4 4 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 348 1528 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 347 (-512) 4 4 3) ->
  region_ok segs E (arm (c_W cx) m4) pc_sh -> region_ok segs E (arm (c_W cx) m4) pc_ff ->
  region_ok segs E (arm (c_W cx) m4) pc_save -> region_ok segs E (arm (c_W cx) m4) pc_F ->
  getr regs4 1 = Z_to_bv 64 (BASE + 8008) -> getr regs4 2 = ew E 34 -> getr regs4 3 = ew E 3 ->
  getr regs4 4 = ew E 4 -> getr regs4 8 = ew E 2 -> getr regs4 9 = ew E 34 -> getr regs4 21 = ew E 11 ->
  getr regs4 22 = ew E 10 -> getr regs4 24 = ew E 513 -> getr regs4 26 = ew E 33 ->
  (forall a, pro_ks cx a -> aview segs (w_H (c_W cx)) m4 a = aview segs (w_H (c_W cx)) (c_mem cx) a) ->
  SRrG segs R (c_W cx) (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + 11300)) m4 (seg_rom segs)) md4)
    (fun W' c' => INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] 0 W' c' \/
      INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] W' c').
Proof.
  intros cx S2 k fpos E regs4 m4 md4 HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HNP2 HEI U2 U34 U39 U513 E33 U512 EA
    RG7 RG6 RG5 RG4 RG3 RG2 RG1 RSH RFF RSV RF Q1 Q2 Q3 Q4 Q8 Q9 Q21 Q22 Q24 Q26 KEEP.
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & Hra0 & H10 & H11 & _).
  pose proof HPREE as (_ & _ & _ & Hgp & Htp & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pro_Fb_x cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  set (FF := frame_addr (c_ly cx) 1 fpos) in *. set (F := lf_F cx) in *.
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds0 _ _ _ _ _ 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1.
  destruct (al0_frames _ _ _ _ _ 1 fpos HAR Hin1) as (_ & _ & HFp & HFs).
  fold FF in HFp, HFs. change (fs_frame_bytes 1) with 128 in HFp. change (fs_frame_bytes 1 / 8) with 16 in HFs.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (ER : forall (r : nat) (b : bv 5), (r < 32)%nat -> Z.of_nat r = bv_unsigned b -> ew E r = getr (c_regs cx) b).
  { intros r b Hr Hb. rewrite (EA r Hr). f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hb.
    apply bv_wrap_small. change (bv_modulus 5) with 32. lia. }
  (* the frame and the fake frame *)
  assert (HFR : pro_fr cx FF (c_W cx) m4).
  { unfold pro_fr. cbv zeta. fold F.
    split.
    { apply (pro_saved_of_region E _ _ _ _ _ _ _ (c_regs cx) RSV U2 EA).
      unfold saved_regs.
      repeat (apply Forall_cons; [cbn [fst snd In]; repeat (first [left; reflexivity | right]) |]).
      apply Forall_nil. }
    assert (FS : forall off (nv : nat) v, In (YP09.mkChunk off (CVal 8 (SOff nv 0))) (YP09.r_chunks pc_F) ->
        bv_unsigned (ew E nv) = v -> 0 <= v < 2 ^ 64 -> sv8 (c_W cx) m4 (F + off) v).
    { intros off nv v Hc Hv Hr. unfold sv8.
      refine (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 34 F _ 24 208 24 208 off 8 (SOff nv 0) v RF U34 Hc _ Hr
        ltac:(cbn; lia)) eq_refl eq_refl).
      cbn [sv_denot]. rewrite Hv, Z.add_0_r. reflexivity. }
    split; [apply (FS 24 347%nat); [cbn; tauto | pro_rwimg HEI 347%nat; reflexivity | lia]|].
    split; [apply (FS 48 352%nat); [cbn; tauto | pro_rwimg HEI 352%nat; reflexivity | lia]|].
    split; [apply (FS 56 353%nat); [cbn; tauto | pro_rwimg HEI 353%nat; reflexivity | lia]|].
    split; [apply (FS 64 351%nat); [cbn; tauto | pro_rwimg HEI 351%nat; reflexivity | lia]|].
    split; [apply (FS 72 350%nat); [cbn; tauto | pro_rwimg HEI 350%nat; reflexivity | lia]|].
    split; [apply (FS 80 39%nat); [cbn; tauto | exact U39 | lia]|].
    split; [apply (FS 88 39%nat); [cbn; tauto | exact U39 | lia]|].
    split; [apply (FS 184 39%nat); [cbn; tauto | exact U39 | lia]|].
    assert (FH : forall off e v, In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks pc_ff) ->
        sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv8 (c_W cx) m4 (FF + off) v).
    { intros off e v Hc Hv Hr. unfold sv8.
      exact (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 39 FF _ 0 128 0 0 off 8 e v RFF U39 Hc Hv Hr
        ltac:(cbn; lia)) eq_refl eq_refl). }
    split; [rewrite <- (Z.add_0_r FF); apply (FH 0 (SLit 1102416563)); [cbn; tauto | reflexivity | lia]|].
    split; [apply (FH 8 (SOff 266 0)); [cbn; tauto | | lia];
            cbn [sv_denot]; pro_rwimg HEI 266%nat; reflexivity|].
    split; [apply (FH 16 (SOff 240 7620)); [cbn; tauto | | lia];
            cbn [sv_denot]; pro_rwimg HEI 240%nat; reflexivity|].
    split; [intros i Hi; apply (apresent_writable segs); exact (proj1 (HFp (FF + i) ltac:(lia)))|].
    split.
    { apply (pro_shadow_garr8 E _ 513 _ _ 0 16 0 0 RSH U513).
      intros j Hj. do 16 (destruct j as [|j]; [cbn; repeat (first [left; reflexivity | right]) |]). lia. }
    intros i Hi. apply (apresent_writable segs). pose proof (proj1 (HFs i Hi)) as H.
    unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. exact H. }
  (* the registers *)
  assert (HRG : pro_regs cx FF regs4).
  { unfold pro_regs, w64. fold F.
    split; [rewrite Q2, <- U34, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q8, (ER 2%nat 2%bv ltac:(lia) eq_refl); reflexivity|].
    split; [rewrite Q9, <- U34, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q21, (ER 11%nat 11%bv ltac:(lia) eq_refl), H11; reflexivity|].
    split; [rewrite Q22, (ER 10%nat 10%bv ltac:(lia) eq_refl), H10; reflexivity|].
    split; [rewrite Q24, <- U513, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q26; exact E33|].
    split; [rewrite Q3, (ER 3%nat 3%bv ltac:(lia) eq_refl), Hgp; reflexivity|].
    rewrite Q4, (ER 4%nat 4%bv ltac:(lia) eq_refl), Htp; reflexivity. }
  (* the globals *)
  assert (GV : forall n off w (sz : N) v a, region_ok segs E (arm (c_W cx) m4) (pc_g n off w sz v) ->
      (A_TEXT <= n < A_LIM)%nat -> VAL n + off = a -> N.to_nat sz = Z.to_nat w -> 0 <= v < 2 ^ (8 * Z.of_N sz) ->
      (Z.of_N sz <= 8) -> val_mem segs (arm (c_W cx) m4) a (Z.to_nat w) v).
  { intros n0 off w sz v a HR Hn Ha Hw Hv Hs.
    refine (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ n0 (VAL n0) _ off (off + w) off (off + w) off sz
      (SLit v) v HR (HEI n0 Hn) ltac:(cbn; tauto) _ Hv Hs) Ha Hw).
    reflexivity. }
  assert (HGL : pro_glob (c_W cx) m4).
  { unfold pro_glob.
    split; [exact (GV 347%nat (-512) 4 4%N 3 (rg_client fr_RG) RG1 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 348%nat 1528 1 1%N 0 (rg_client_broken fr_RG) RG2 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 349%nat 1588 4 4%N 0 A_NFD RG3 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 350%nat 1616 8 8%N 0 (rg_send_max fr_RG) RG4 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 351%nat 1636 1 1%N 0 (rg_gone fr_RG) RG5 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 352%nat 1660 1 1%N 0 (rg_send_dead fr_RG) RG6 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    exact (GV 353%nat 1684 1 1%N 0 (rg_send_eintr fr_RG) RG7 ltac:(unfold A_TEXT, A_LIM; lia)
      ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
  (* the return address *)
  assert (Hra : getr regs4 1 = w64 (BASE + A_pro_ret)).
  { rewrite Q1. reflexivity. }
  assert (HFLG : sv8 (c_W cx) m4 (FF + 120) (flag_addr (c_ly cx) 1 fpos)).
  { pose proof (bv_unsigned_in_range 64 (ew E 512)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    unfold sv8.
    exact (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 39 FF _ 0 128 0 0 120 8 (SOff 512 0)
      (flag_addr (c_ly cx) 1 fpos) RFF U39 ltac:(cbn; tauto)
      ltac:(cbn [sv_denot]; rewrite U512, Z.add_0_r; reflexivity) ltac:(rewrite <- U512; lia)
      ltac:(cbn; lia)) eq_refl eq_refl). }
  exact (pro_mid_xR cx regs4 m4 md4 S2 k fpos HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HNP2 HFR HFLG Hra HRG HGL KEEP).
Qed.

(* :1617 lf_seg_pro_x at R: cut_x's Section wR hypothesis SEG_PRO_R.  The walk to op_add's call is the strict text,
   over the post `the rest is a walk at R` (pro_srr_srrG); at the call, pro_at_call_xR *)
Theorem lf_seg_pro_xR : forall cx Hp, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  SRrG segs R (c_W cx) (lf_entry cx)
    (fun W' c' => INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp 0 W' c' \/
      INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp W' c').
Proof.
  intros [ly S W regs mem md p n pl M] Hp HB.
  (* the entry's ghost list is empty (HP0 on the pre's ARx): the walk runs at [] *)
  pose proof HB as (_ & HPRE_). hp0a (proj1 (proj1 HPRE_)). clear HPRE_.
  (* R_refl is not needed by this walk; it stays in the twin's arguments (a Theorem Labs lane's one layout R R_refl R_trans
     WLE_R for the fourteen twins) *)
  pose proof R_refl as HRrefl. clear HRrefl.
  apply pro_srr_srrG.
  pose proof HB as (HAI & HPRE & Hra0 & H10 & H11 & Hin & Hnl & Hgarr & Hfrs & Hlive & Hroom & Hnp & Hgi & Hrom & Hrod & Hsink & Hfd & Hsrt & Hmeta & Hmo & Hstkr & Hhb).
  cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_M lf_entry] in *.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (Rn : 0 <= n < 2 ^ 26) by (destruct Hin as [(-> & _) | (Hn & _)]; lia).
  destruct (pro_entry_x W ly S regs mem md [] n HPRE H11 Rn) as [HS SHOK].
  (* the journal at G = [] (W1Verify's template: ajournal_gx_nil_x of ajournal_x_init) *)
  pose proof (proj2 (ajournal_gx_nil_x segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (ajournal_x_init segs B PST ARx LLVMF_STK (lf_FP fr_FP (LFCX ly S W regs mem md p n pl M)) ly S [] W regs mem md [] HPRE)) as HJ.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  remember (Eimg (Ereg regs (pro_extra regs))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n0 r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  set (F := pro_F regs) in *.
  assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  assert (HAE : env_agree 32 (Ereg regs (pro_extra regs)) E)
    by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HFv : F = spZ regs - 320 \/ F = spZ regs - 336) by exact (pro_F_facts (spZ regs) Hal16).
  assert (HFal : F mod 32 = 0) by exact (pro_F_al (spZ regs - 320)).
  assert (HspR : 2 ^ 46 <= F /\ spZ regs <= 2 ^ 47).
  { revert HFv Hslo Hshi H47 Hceil C1 C3 WS Hstk0. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
  assert (UF : bv_unsigned (ew E 34) = F) by (rewrite E34; apply unsigned_lit_small; lia).
  unfold cfg_at. change (w64 A_LLVMF) with (Z_to_bv 64 (BASE + A_pro)).
  (* run 1: the frame, the saved registers, the fake-stack test; stops at __asan_stack_malloc_1 *)
  paj_run_tok_x RUN0 HS HJ SHOK Bspan.
  { apply awr_ok_x_of0. intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?UF in Hr;
        first [ lia | left; lia ] | ]).
    destruct Hin'. }
  (* the call to __asan_stack_malloc_1 (128): the fake frame FF; the journal at G = [] is the plain ajournal_x *)
  apply ajournal_gx_nil_x in HJ.
  pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  rewrite (palf_sm1 B TLF).
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
      eapply (aj_stack_malloc_pres_at_x segs B PST ARx LAWS Hsegs (pal_env B TL) OWNLOW WFx WFL SMALLOC 1 ASM1 ltac:(lia)
        W rg mm LLVMF_STK (spZ regs) _ ly S [] W mem md [] ly S [] _ 0 (F - spZ regs) _ HJ) end.
    - unfold spZ at 1. rewrite R2, UF. lia.
    - destruct HFv as [HFe | HFe]; rewrite HFe;
        [replace (spZ regs - 320 - spZ regs) with ((-20) * 16) by lia | replace (spZ regs - 336 - spZ regs) with ((-21) * 16) by lia];
        apply Z_mod_mult.
    - lia.
    - rewrite WS, Hes. lia.
    - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Hfrs. vm_compute. reflexivity. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HPg & Hsf).
  (* the room round: the seat is a set_fs of the entry's state, so NP holds there (NPF) *)
  assert (HNP2 : NP S2) by (destruct Hsf as (fs & ->); exact (NPF _ fs Hnp)).
  (* KF-COUNT F2: and it costs nothing at the meter (MO_FR), LS_pro_oa's / LS_pro's premise *)
  assert (HMO2 : mo_le MT S S2 0) by (destruct Hsf as (fs & ->); exact (MO_FR S fs)).
  set (FF := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
  pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb.
  destruct (al0_const _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
  destruct (al0_const _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
  rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
  pose proof (palf_uar_img B TLF) as HuR.
  jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | apply Forall_nil].
    - eapply region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
    - eapply region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
    - eapply region_kept_stack_aj_x; [exact HK | exact HJ2 | exact UF | lia | lia | lia | cbn; lia | cbn; lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
        [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kg1) | exact (val_mem_of_rdword segs _ _ _ _ Kg2) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
        [exact (HEI (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kc1) | exact (val_mem_of_rdword segs _ _ _ _ Kc2) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
        [exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kgu1) | exact (val_mem_of_rdword segs _ _ _ _ Kgu2) | lia].
    - apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
        [rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 segs _ _ _ _ Ku1) | exact (val_mem_of_rd32 segs _ _ _ _ Ku2) | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  assert (HAEa : env_agree 32 (Ereg regs (pro_extra regs)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
  clear HEa.
  prreg HS (10%bv : bv 5) RF.
  (* seat the fake frame: FF in atom 39 (a0), its flag FL in 512, the frame's shadow SB + FF / 8 in 513 *)
  assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds0 _ _ _ _ _ 1 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
  destruct (al0_frames _ _ _ _ _ 1 fpos HARb Hfin2) as (HFal2 & HFapp & HFpres & HFSpres).
  destruct (FFL _ _ [] _ _ _ 1 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
  change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  fold FF FL in HFal2, HFapp, HFpres, HFSpres, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
  assert (RF' : ew Ea 39 = Z_to_bv 64 FF) by (rewrite <- RF, Ha0; reflexivity).
  assert (E33a : ew Ea 33 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E33).
  assert (U2a : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
  assert (U34a : bv_unsigned (ew Ea 34) = F) by (rewrite OLDa by lia; exact UF).
  assert (U32a : bv_unsigned (ew Ea 32) = as_uar_cell B) by (rewrite OLDa, E32 by lia; apply unsigned_lit_small; lia).
  assert (U241 : bv_unsigned (ew Ea 241) = VAL (A_OBJ 0)) by exact (HEIa (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (U242 : bv_unsigned (ew Ea 242) = VAL (A_OBJ 1)) by exact (HEIa (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (U273 : bv_unsigned (ew Ea 273) = VAL (A_OBJ 32)) by exact (HEIa (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (HFF8 : FF / 8 = 4 * (FF / 32)).
  { pose proof (Z.div_mod FF 32 ltac:(lia)) as D. rewrite HFal2, Z.add_0_r in D. rewrite D at 1.
    replace (32 * (FF / 32)) with (4 * (FF / 32) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
  assert (HFF8lo : 512 <= FF / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HFF8hi : FF / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
  pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
  pose proof (palf_sep B TLF) as HSEP. cbn [zseps zseps_from fst snd] in HSEP.
  pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 1)). pose proof (pa_val_range (A_OBJ 32)).
  pose proof (ff_seat_ok Ea _ _ (w_H W) mem2 39 33 512 1 FF FL HS eq_refl ltac:(vm_compute; reflexivity)
    RF' E33a ltac:(lia) ltac:(lia) ltac:(right; reflexivity) HFal2 ltac:(lia) ltac:(change (fs_frame_bytes 1) with 128; lia)
    ltac:(lia)
    ltac:(change (fs_frame_bytes 1) with 128; intros a Ha; exact (proj1 (HFpres a Ha)))
    ltac:(change (fs_frame_bytes 1 / 8) with 16; intros i Hi; exact (proj1 (HFSpres i Hi)))
    ltac:(change (fs_frame_bytes 1) with 128; exact Hflag) ltac:(change (fs_frame_bytes 1) with 128; exact Hz)) as HS3.
  pose proof (frm_off_imgP_x B ARx LAWS IMGCx _ _ [] _ _ _ 1 fpos HARb Hfin2) as HFimg. change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg.
  set (Eb := havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)]) in HS3.
  assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; subst Eb; apply YN3v.ew_havoc_old; exact Hm).
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
  assert (U512 : bv_unsigned (ew Eb 512) = FL).
  { subst Eb. rewrite (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
    apply unsigned_lit_small. lia. }
  assert (U513 : bv_unsigned (ew Eb 513) = SB + FF / 8).
  { subst Eb. rewrite (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)).
    apply unsigned_lit_small. unfold SB. lia. }
  assert (U39b : bv_unsigned (ew Eb 39) = FF) by (rewrite OLDb, RF' by lia; apply unsigned_lit_small; lia).
  assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact U2a).
  assert (U34b : bv_unsigned (ew Eb 34) = F) by (rewrite OLDb by lia; exact U34a).
  assert (U32b : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb by lia; exact U32a).
  assert (U241b : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U241).
  assert (U242b : bv_unsigned (ew Eb 242) = VAL (A_OBJ 1)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U242).
  assert (U273b : bv_unsigned (ew Eb 273) = VAL (A_OBJ 32)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U273).
  match type of HS3 with ?A1 -> ?A2 -> _ => assert (HD1 : A1); [|assert (HD2 : A2); [|specialize (HS3 HD1 HD2)]] end.
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, ff_fregion, fframe_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1) with 128. rewrite U39b, U2b, U34b, U241b, U242b, U273b, U32b.
    unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia. }
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, ff_sregion, ff_fregion, fshadow_region, fframe_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1 / 8) with 16. change (fs_frame_bytes 1) with 128.
    rewrite U513, U39b, U2b, U34b, U241b, U242b, U273b, U32b.
    pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hd8a. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as Hd8b.
    pose proof (Z.div_mod FF 8 ltac:(lia)) as Hd8c.
    unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia. }
  clear HS. rename HS3 into HS. norm_ss HS.
  (* run 2 (plain): the frame's slot F+184, the fake frame's header and its shadow's poison *)
  paj_run_sh_x RUNP HS HJ2.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U34b, ?U39b, ?U512, ?U513, ?U241b, ?U242b, ?U273b, ?U32b in Hr;
        first [ lia
        | left; lia
        | right; right; right; exists 1, fpos; split; [left; reflexivity|];
          change (frame_addr ly 1 fpos) with FF; change (fs_frame_bytes 1) with 128;
          first [ left; unfold in_zr; cbn [fst snd]; lia
          | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (128 / 8) with 16; lia ] ]
      | ]).
    destruct Hin'. }
  (* the size refusal: n >> 26 <> 0 goes to 0x84d7c; refuted by the contract's n < 2^26 *)
  assert (E11b : ew Eb 11 = Z_to_bv 64 n) by (rewrite OLDb, OLDa, (EE 11%nat 11%bv eq_refl), H11 by lia; reflexivity).
  psrr_branch_pi_x RUNP BR HS.
  { exfalso. rewrite branch_ne_U, U_SAlu, (U_atom Eb 11 n E11b), !U_SLit in Hc by lia. cbn [zalu_raw] in Hc.
    change (Z.land (zcanon 26) 63) with 26 in Hc. rewrite Z.shiftr_div_pow2, Z.div_small in Hc by lia.
    vm_compute in Hc. discriminate Hc. }
  (* the fake frame and its shadow become read-only (the token run keeps its windows off the shadow span);
     the runtime's GOT and uar regions are dropped *)
  pro_keep HS [0; 1; 2; 3; 4]%nat.
  pro_ro HS 0%nat. pro_ro HS 1%nat.
  pose proof pro_vals as (PV67 & PV68 & PV69 & PV70 & PV71 & PV72 & PV73 & PV74 & PV75 & PV76 & PV77 & PV78 &
    PVO22 & PVO25 & PVO26 & PVO0 & PVO32).
  assert (RGv : rg_client fr_RG = 0xa1fe0 /\ rg_client_broken fr_RG = 0x5d87e0 /\ rg_send_max fr_RG = 0x5d8840 /\
    rg_gone fr_RG = 0x5d8860 /\ rg_send_dead fr_RG = 0x5d8880 /\ rg_send_eintr fr_RG = 0x5d88a0 /\
    rg_s fr_RG = 0x5d88e0 /\ rg_nout fr_RG = 0x5d88c0 /\ rg_nsrc fr_RG = 0x5d87a0 /\ rg_src fr_RG = 0x5d87c0)
    by (vm_compute; repeat split; reflexivity).
  destruct RGv as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & RG7 & RG8 & RG9 & RG10).
  assert (HNFDv : A_NFD = 0x5d8820) by reflexivity.
  (* the seven global stores' regions (pr_g 67 .. 73), all in G_fr *)
  pro_addg HS HEIb 67%nat (-512) 4 HG_client.
  pro_addg HS HEIb 68%nat 1528 1 HG_cbroken.
  pro_addg HS HEIb 69%nat 1588 4 HG_nfd.
  pro_addg HS HEIb 70%nat 1616 8 HG_smax.
  pro_addg HS HEIb 71%nat 1636 1 HG_gone.
  pro_addg HS HEIb 72%nat 1660 1 HG_sdead.
  pro_addg HS HEIb 73%nat 1684 1 HG_seintr.
  pro_addf HS HEIb 347%nat. pro_addf HS HEIb 348%nat. pro_addf HS HEIb 349%nat. pro_addf HS HEIb 350%nat.
  pro_addf HS HEIb 351%nat. pro_addf HS HEIb 352%nat. pro_addf HS HEIb 353%nat.
  (* the journal, from here at G_fr (the donor's journal is ajournal_gx at G = [], lifted) *)
  pose proof (ajournal_gx_G_mono_x segs B PST ARx [] G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a Ha => False_ind _ (inG_nil a Ha)) (proj2 (ajournal_gx_nil_x segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) HJ2)) as HJ3.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (SHOKb : sh_ok segs Bx [] Eb (mrestrict (w_H W) (ms_mem msx))) by (unfold sh_ok; constructor) end.
  pose proof (pro_Fb_x (LFCX ly S W regs mem md p n pl M) HB) as (HFlo & HFsp & HFsp2 & _ & _ & _).
  change (lf_F (LFCX ly S W regs mem md p n pl M)) with F in HFlo, HFsp, HFsp2. unfold CEIL8 in HFlo.
  cbn [c_regs] in HFsp, HFsp2.
  (* run 3: the frame's slots and the seven globals, to `jal op_add` *)
  paj_run_to_tok_x RUNTOX HS HJ3 SHOKb Bspan AF_fr_op_add.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U34b, ?U39b, ?U512, ?U513, ?U241b, ?U242b, ?U273b, ?U32b in Hr;
        pro_imgh HEIb Hr;
        first [ clear - Hr; lia
        | left; split; [left; clear - Hr WS HFsp HFsp2; lia | clear - Hr; lia]
        | right; left; first [ apply HG_client; clear - Hr RG1; lia | apply HG_cbroken; clear - Hr RG2; lia
                             | apply HG_nfd; clear - Hr HNFDv; lia | apply HG_smax; clear - Hr RG3; lia
                             | apply HG_gone; clear - Hr RG4; lia | apply HG_sdead; clear - Hr RG5; lia
                             | apply HG_seintr; clear - Hr RG6; lia ]
        ]
      | ]).
    destruct Hin'. }
  (* ---- the bytes the prologue keeps from the entry to the call (pro_mid_x's KEEP) ---- *)
  pose proof HK as (HK1 & HK2 & HK3 & _ & _ & _).
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) ?m4) |- _ =>
    rename Hx into HFr3;
    assert (K3 : forall a, 0 <= a < alloc_ceiling -> (a + 1 <= FF \/ FF + 128 <= a) ->
        (a < 2147450880 + FF / 8 \/ 2147450880 + FF / 8 + 16 <= a) -> pro_gst_out a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) mem2 a) end.
  { clear - HFr3 HFr0 HEIb U2b U34b U39b U512 U513 U241b U242b U273b U32b HFlo HFsp.
    intros a Ha Hff Hsh Hgst. pose proof Hgst as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6 & Hg7). clear Hgst.
    pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    rewrite (proj1 (pro_kept_frame _ _ W _ _ a HFr3 ltac:(clear - Ha D1; lia) ltac:(pro_nwr_k HEIb Ha HFlo HFsp))).
    pose proof (proj1 (pro_kept_frame _ _ W _ _ a HFr0 ltac:(clear - Ha D1; lia)
      ltac:(pro_nwr_k HEIb Ha HFlo HFsp))) as K2.
    cbn [ms_mem mkst] in K2. exact K2. }
  assert (K1 : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { clear - HFr HEI Usp UF HFlo HFsp.
    intros a Ha. pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    exact (proj1 (pro_kept_frame _ _ W _ _ a HFr ltac:(clear - Ha D1; lia) ltac:(pro_nwr_k HEI Ha HFlo HFsp))). }
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) ?m4) |- _ =>
    assert (KEEP : forall a, pro_ks (LFCX ly S W regs mem md p n pl M) a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) mem a) end.
  { pose proof asan_consts as (D1 & D2 & D3 & D4 & D5). unfold off_img in HFimg.
    intros a [Ha | (p0 & n0 & Hp & Hpa)]; [|cbn [c_ly c_S] in Hp].
    - pose proof (G_obj_rng a (G_keep_obj a Ha)) as Hr. pose proof (G_keep_gst a Ha) as Hg.
      destruct (HG a (HG_obj a (G_keep_obj a Ha))) as (Him & Hno & _).
      rewrite (K3 a ltac:(clear - Hr D1; lia) ltac:(clear - Hr HFimg; lia) ltac:(clear - Hr HF4096; lia) Hg),
        (HK3 a Him Hno (G_obj_err a (G_keep_obj a Ha))).
      exact (K1 a ltac:(clear - Hr D1; lia)).
    - destruct (al0_blocks _ _ _ _ _ p0 n0 HARa Hp) as (_ & H4096 & Hbc & Happ & _).
      assert (Hp2 : In (p0, n0) (ablocks B ly S2)) by (rewrite Eab; exact Hp).
      pose proof (pro_blk_frm_x _ _ _ _ _ p0 n0 1 fpos HARb Hp2 Hfin2) as Hd.
      change (frame_addr ly 1 fpos) with FF in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      assert (Hsh : a < 2147450880 + FF / 8 \/ 2147450880 + FF / 8 + 16 <= a).
      { destruct (Z_lt_le_dec a (2147450880 + FF / 8)) as [Hl | Hl]; [left; exact Hl | right].
        destruct (Z_lt_le_dec a (2147450880 + FF / 8 + 16)) as [Hl2 | Hl2]; [|exact Hl2].
        exfalso. exact (fshadow_not_app FF 16 p0 (req_size n0) a ltac:(clear - HF4096; lia)
          ltac:(clear - HFceil D1; lia) Happ ltac:(clear - Hl Hl2; lia) Hpa). }
      rewrite (K3 a ltac:(clear - H4096 Hbc Hpa; lia) ltac:(clear - Hd Hpa; lia) Hsh
        (pro_blk_gst_x _ _ _ _ _ p0 n0 a HARa Hp Hpa)).
      replace a with (p0 + (a - p0)) by ring.
      rewrite (HK2 p0 n0 (a - p0) Hp ltac:(clear - Hpa; lia) (fun Hf => Hf)).
      exact (K1 (p0 + (a - p0)) ltac:(clear - H4096 Hbc Hpa D1; lia)). }
  (* ---- op_add's entry ---- *)
  pmkst HS.
  pro_rgn HS 0%nat RQ7. pro_rgn HS 1%nat RQ6. pro_rgn HS 2%nat RQ5. pro_rgn HS 3%nat RQ4.
  pro_rgn HS 4%nat RQ3. pro_rgn HS 5%nat RQ2. pro_rgn HS 6%nat RQ1. pro_rgn HS 7%nat RQS.
  pro_rgn HS 8%nat RQF. pro_rgn HS 10%nat RQV. pro_rgn HS 11%nat RQP.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26.
  assert (EAb : forall r, (r < 32)%nat -> ew Eb r = getr regs (Z_to_bv 5 (Z.of_nat r))).
  { intros r Hr. rewrite OLDb, OLDa by (clear - Hr; lia). apply EE. rewrite Z_to_bv_unsigned. symmetry.
    apply bv_wrap_small. change (bv_modulus 5) with 32. clear - Hr; lia. }
  assert (Hfrs2' : frames S2 = [(1, fpos)]) by (rewrite Hfrs2, Hfrs; reflexivity).
  apply SRr_ret.
  exact (pro_at_call_xR (LFCX ly S W regs mem md p n pl M) S2 0 fpos Eb _ _ _ HB HJ3 Eab Hfrs2' Hnev2 Hbb2 HMO2 HNP2 HEIb
    U2b U34b U39b U513 (eq_trans (OLDb 33%nat ltac:(apply Nat.ltb_lt; reflexivity)) E33a) U512 EAb
    RQ7 RQ6 RQ5 RQ4 RQ3 RQ2 RQ1 RQS RQF RQV RQP Q1 Q2 Q3 Q4 Q8 Q9 Q21 Q22 Q24 Q26 KEEP).
Qed.

End prxR.

End prx.

(* ---------------------------------------------------------------- THE CHECK
   In cut_x's scope (its Section w header and this piece's hypotheses): lf_seg_pro_x's type is cut_x's Section w
   hypothesis SEG_PRO (W_LLVMFuzzerTestOneInput_cut_x.v:547), restated and closed by `exact`, and it fills that slot of
   cut_x's composition lf_contract_of_segments_x. *)
Section chk.
(* cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:191-235) *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
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
(* the instance's ghost poisoned-head set stays empty (a Theorem Labs lane's HP0 ruling, W_journal_x at 0c4d57d9bf1;
   fuzz_reply calls no poison routine): the driver reads the post's Hp' = [] from the journal's ARx through it *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* ---- the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.2 / 0.4): the allocator rules' room record RP, whose room invariant
   is the cut's NP (the walk's RM := fun S _ => NP S; at top_x rp_RM RP := fun S _ => room_live_cf S = NP), and NPF:
   the fake frame's seat (a set_fs) keeps NP (top_x: room_live_set_fs) ---- *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis NPF : forall S f, NP S -> NP (set_fs f S).
(* KF-COUNT F2: top_x's MO_FR verbatim (lib/A/W_LLVMFuzzerTestOneInput_top_x.v:343), as in Section prx *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- _pro.v's AR-free items that take section arguments, cited with them ---- *)
Local Notation oa_cost := (W_LLVMFuzzerTestOneInput_pro.oa_cost MT).

(* ---------------------------------------------------------------- SEG_PRO's own hypotheses, in _pro.v's order *)
(* op_add: W2's contract at the kit's form (lib/A/W_op_add.v:2936 oa_spec_g_x; _pro.v:161's W2_op_add over ARx) *)
Hypothesis W2_op_add : W_op_add.oa_spec_g_x (PI := PB_fr) B PST ARx MT RP (BASE + AF_fr_op_add).
Hypothesis TL : PALib B.                            (* the allocator instance (W_kit.v) *)
Hypothesis TLF : PALibF B.                          (* its fake-stack fields (W_frame.v) *)
(* the stack_malloc seat's Section fsp hypotheses (W_frame_x.v:747-759, verbatim), in place of _pro.v's ML / SMP *)
Hypothesis OWNLOW : ARx_owned_low_law segs B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law segs ARx WFx.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
(* _pro.v:168-169 over ARx: W_frame_x.v:763 astack_malloc_pres_x at class 1 and :69 frame_flag_lawP_x *)
Hypothesis ASM1 : astack_malloc_pres_x segs B ARx 1.
Hypothesis FFL : frame_flag_lawP_x segs B ARx.
(* _cut's two shared facts: glob_wr_law verbatim, errno_law at cut_x's errno_law_x *)
Hypothesis GWL : glob_wr_law G_fr.
Hypothesis ERRL : errno_law_x B ARx.
(* ---- instance facts, in _top.v's text (HEV, HZS: AF0m's ts_errno / ts_zsh, measured in _G.v's header) ---- *)
Hypothesis HEV : as_errno B = TFIB_ERRNO_A.
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
(* ---- G_fr: it holds the program's 20 objects (_G.v obj_c proves it of G_fr_c), and no read-only byte (_G.v
   c_rom_apart) ---- *)
Hypothesis HG_obj : forall a, inG G_fr_obj a -> inG G_fr a.
Hypothesis HROM_G : forall a, in_rom segs a -> ~ inG G_fr a.
(* ---- the instance obligation of W_journal.v's rom_out (a working branch 45a3cc9bdd0): an owned read-only byte
   is one of AR's pinned const cells (AF0m pins all 408) ---- *)
Hypothesis ROM_PIN : forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a.
(* _pro.v:194 SHV_oa over ARx (gx_prog_x's last conjunct at G_oa; add_x's GSHV at ad_G = G_oa) *)
Hypothesis SHV_oa : forall ly S Hp (W : world segs) mem md a n, ARx ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG G_oa x) -> shadow_hull_vis (aview segs (w_H W) mem) a n.
(* ---- the entry's surviving blocks (the relay's table g_src and the controller's buffer g_out): apart from the input
   block and inside the entry's footprint fr_FP (_cut.v:124-128) over their REQUEST size, as the cut's ablocks_sep
   (req_size, a Theorem Labs lane's ruling 12:2xZ) and op_add's journal take them; an obligation of the instance's
   fr_live_pre / fr_FP (ablocks_fp-shaped, i.e. (fst b, fst b + req_size (snd b))) ---- *)
Hypothesis HFP_pro : forall cx Hp T c O mx cap out,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ra_rel B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) T [] ->
  aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c O mx (Z.of_nat (length O)) cap out ->
  (exists rest, Permutation (ablocks B (c_ly cx) (c_S cx))
     (input_blks cx ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out ++ rest)) /\
  (T <> 0 -> forall a, T <= a < T + req_size ATABLE -> inFP (lf_FP fr_FP cx) a) /\
  (forall b, In b (aout_blks cap out) -> forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a).
(* ---- the allocator-state invariant's facts op_add takes, at the state after the fake frame (LS_pro_oa), and the
   cut's two Variables at the first cut point (LS_pro, RI_pro): the model after op_add, k = 0 ---- *)
Hypothesis LS_pro_oa : forall cx Hp (S2 : astate) pos,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  mo_le MT (c_S cx) S2 0 ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S2 oa_cost.
Hypothesis RI_pro : forall cx Hp q T' pj c O cap out,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  RINV cx 0 (pro_m q T' pj c O cap out).
(* LS_pro at the PROPOSED text (as in Section w) *)
Hypothesis LS_pro : forall cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 ->
  mo_le MT S2 S oa_cost ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  LSx cx 0 (pro_m q T' pj c O cap out) ly S.
(* the room round's count row for SEG_PRO (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c); lib/A/ReplyLScnt.v fr_cnt_pro at
   commit ba8e99b5bd2): op_add's count premise at the seat's state S2, whose blocks are the entry's.  The counts come
   from the entry's xcnt_ok (fr_lib_pre_cf_x's XCNT, at the entry's table T0 and g_out), not from LS *)
Hypothesis LS_cnt : forall cx T0 cap out (S2 : astate),
  ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) ->
  cnt_ok_pk RP W_op_add.oa_peak (ablocks B (c_ly cx) S2).
(* ---- forced by the generic relation and the placement PST (add_x's texts) ---- *)
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct). The text is W_kit_x.v's BLKN (add_x's). *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): the ROM-view lemma's premise; trivial at PST = [] *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
Local Notation BASEx cx Hp := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp).
Local Notation IH := (INV_H_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation IX := (INV_X_x B NP G_fr fr_FP PST ARx LSx RINV).
Lemma lf_seg_pro_x_check : forall cx Hp, BASEx cx Hp ->
  SRr segs (c_W cx) (lf_entry cx) (fun W' c' => IH cx Hp 0 W' c' \/ IX cx Hp W' c').
Proof.
  exact (lf_seg_pro_x B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx LAWS
    HP0 HG LSx RINV RP RP_NP NPF MO_FR W2_op_add TL TLF OWNLOW WFx WFL SMALLOC ASM1 FFL GWL ERRL HEV HZS HG_obj HROM_G
    ROM_PIN SHV_oa HFP_pro LS_pro_oa RI_pro LS_pro LS_cnt BLKN HPST).
Qed.
Definition pro_x_slot :=
  fun SEG_HEAD ARM_add ARM_write ARM_drain ARM_close ARM_remove ARM_gone ARM_eintr ARM_event ARM_sendmax ARM_default
    SEG_LATCH SEG_EXIT =>
  lf_contract_of_segments_x B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx
    LAWS HG LSx RINV lf_seg_pro_x_check SEG_HEAD ARM_add ARM_write ARM_drain ARM_close ARM_remove ARM_gone ARM_eintr
    ARM_event ARM_sendmax ARM_default SEG_LATCH SEG_EXIT.
(* the route-R check: lf_seg_pro_xR's type is cut_x's Section wR hypothesis SEG_PRO_R
   (W_LLVMFuzzerTestOneInput_cut_x.v:451), restated and closed by `exact` at a Theorem Labs lane's argument layout (the strict
   lemma's arguments without W2_op_add, then R R_refl R_trans WLE_R W2_op_add_R), and it fills that slot of cut_x's
   lf_contract_of_segments_xR *)
Section chkR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Hypothesis W2_op_add_R : W_op_add.oa_spec_g_xR (PI := PB_fr) B PST ARx R MT RP (BASE + AF_fr_op_add).
Local Notation IHR := (INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation IXR := (INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R).
Lemma lf_seg_pro_xR_check : forall cx Hp, BASEx cx Hp ->
  SRrG segs R (c_W cx) (lf_entry cx) (fun W' c' => IHR cx Hp 0 W' c' \/ IXR cx Hp W' c').
Proof.
  exact (lf_seg_pro_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx LAWS
    HP0 HG LSx RINV RP RP_NP NPF MO_FR TL TLF OWNLOW WFx WFL SMALLOC ASM1 FFL GWL ERRL HEV HZS HG_obj HROM_G
    ROM_PIN SHV_oa HFP_pro LS_pro_oa RI_pro LS_pro LS_cnt BLKN HPST R R_refl R_trans WLE_R W2_op_add_R).
Qed.
Definition pro_x_slotR :=
  fun SEG_HEAD_R ARM_add_R ARM_write_R ARM_drain_R ARM_close_R ARM_remove_R ARM_gone_R ARM_eintr_R ARM_event_R
    ARM_sendmax_R ARM_default_R SEG_LATCH_R SEG_EXIT_R =>
  lf_contract_of_segments_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx
    LAWS HG LSx RINV R R_refl R_trans WLE_R lf_seg_pro_xR_check SEG_HEAD_R ARM_add_R ARM_write_R ARM_drain_R
    ARM_close_R ARM_remove_R ARM_gone_R ARM_eintr_R ARM_event_R ARM_sendmax_R ARM_default_R SEG_LATCH_R SEG_EXIT_R.
End chkR.
End chk.
