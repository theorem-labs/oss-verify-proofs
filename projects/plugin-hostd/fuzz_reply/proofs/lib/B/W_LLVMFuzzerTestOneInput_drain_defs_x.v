(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain of the ASan+UBSan walk (image B) of fuzz_reply's LLVMFuzzerTestOneInput
   over the GENERIC allocator relation ARx - the interface of the arm's ARx conversion: the ARx twin of
   lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v (a Theorem Labs lane's AR interface, a working branch
   af5c712458a), which is NOT edited.  Template: AddX's lib/A/W_LLVMFuzzerTestOneInput_drain_x.v (W8 integ).
   Proves no function (kind: segment walk - the interface of a segment of the entry function).
   The method (W8Entry-2's add_x method): this file Requires the AR file and CITES every item of it that reads no AR
   and no Section variable (the addresses, the model notions dr_k' / dr_at_op / dr_pick / dr_skip / dr_step /
   dr_step_ok, the pure lemmas); the item that reads a Section variable but no AR is restated VERBATIM
   (dr_regs_call); the AR-reading items are CONVERTED:
     DLK          the state at `jal pthread_mutex_lock`, with the entry's ghost list Hpe beside cx and the state's
                  Hp3 beside S3, the journal ajournal_gx_x at PST / ARx, LS -> cut_x's LSx;
     dr_env_x     the bundle of what the other lanes owe, each callee contract in its kit _x form
                  (dr_spec_x / alock_realizes_x / aunlock_realizes_x / cnlr_spec_x / csd_spec_x / cnl_spec_x at the
                  walk's PST / ARx; cut_x's errno_law_x), the G-coverage and image facts and the RI_ / LS_ rule
                  families verbatim (LS -> LSx), and two fields the AR proof read off AR itself, as on image A
                  (AddX's HPST / BLKR): the image is off PST, and a live block's request is in [0, 2 ^ 30).
   The Section header is cut_x's Section w header (B .. RINV), the arm's MMAX and the room round's RP / dr_cnl_pk.
   THE ROOM ROUND (an internal work row, the image-B twin of W8's A re-fit a working branch
   b5892edd1cb): DLK carries the cut's NP after LSx; dr_env_x takes the room record RP (dre_RP_NP ties its rp_RM to
   NP), DRAIN / CNL at RP, the count rules dre_DR_CNT_grow / dre_DR_CNT_cnl and dre_LS_cnt (at the parameter
   dr_cnl_pk), LS_drain_pre's peak form, and LS_cnl_pre / LS_drain_step at a Theorem Labs lane's TX_LS_cnl_pre /
   TX_LS_drain_step_t texts (image A's words, restated here with the step rules' model bundles).  dre_RI_drain_step is
   the B top_x's restated text (a Theorem Labs lane's RI_drain_step_btop_restated, a working branch 713767bda40). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_contract_x W_sites_x W_frame_x W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
(* the room round: the live counts (lib/B/ReplyCnt.v acnt / tr_peakP, the B kit's twin of lib/A/ReplyCnt.v), Required
   and named qualified.  A Theorem Labs lane's texts this arm takes (LS_cnt's guard msz_ok of ReplyLSCntM.v, the step
   rules' bundles of ReplyLSDrain3.v / ReplyLS3Arms.v, image A) are restated below (msz_ok, dr3_epre ..), and
   check_no_loss's peak after the drain is the parameter dr_cnl_pk, as on image A *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
(* the drain's functional half dr_dfun and dr_cap1 (lib/B/W_LLVMFuzzerTestOneInput_drain_calls.v:102 / :125, no AR, no
   Section variable), which the room round's count rule dre_DR_CNT_grow reads *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_calls.
(* LAST, so the names this file cites from the AR file are not shadowed by a kit file's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the cut's own Local Notation, which does not leave its file *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ---- the step rules' bundles, a Theorem Labs lane's texts restated word for word (image A's drain arm b5892edd1cb
   restates them the same way; the top's TX_LS_drain_step / TX_LS_cnl_pre name the originals, which unfold to these):
   dr3_epre / dr3_hpre / dr3_epost / dr3_hpost are lib/A/ReplyLSDrain3.v:80-100, ls3_kh / ls3_hn / ls3_dpost /
   ls3_cpost are lib/A/ReplyLS3Arms.v:306-328, at meet 393c0b2cb2a (image A; lib/B/W_rep.v is lib/A/W_rep.v's kit twin,
   the clause numbers below are its) ---- *)
(* LS_cnt's guard, lib/A/ReplyLSCntM.v:49-54: the model's sizes (amodel_at gives them, dr_msz_x) *)
Definition texts_ok (l : hlist) : Prop := Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs l).
Definition msz_ok (m : lmod) : Prop :=
  Forall (fun e => 0 <= re_cap e <= 16384 /\
    Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) /\
  Forall (fun o => match o with Some h => texts_ok (hs_expected h) /\ texts_ok (hs_held h) | None => True end)
    (lm_hs m).
(* aentry_ok's clauses at the drain call: the re_cap clause W_rep.v:126, |re_U| = re_used <= APARTIAL and no NUL in
   re_U :125, the held array's 8 <= re_kh :131-132, the keys' 14 <= |text| :139 *)
Definition dr3_epre (e : rentry) : Prop :=
  (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
  Z.of_nat (length (re_U e)) <= APARTIAL /\ ~ In (Z_to_bv 8 0) (re_U e) /\
  (re_hp e <> 0 -> 8 <= re_kh e) /\
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e).
(* asrc_at's pending list at the drain call: its offset clause (W_rep.v:106-107) and its texts' non-emptiness
   (alist_at (HA + 16) (hs_pending h) false, W_rep.v:93) *)
Definition dr3_hpre (h : hsrc) : Prop :=
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) /\
  Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h)).
(* dr_post's clauses on the entry it leaves: aentry_ok e' (W_rep.v:126), the held array, the keys *)
Definition dr3_epost (e e' : rentry) (h : hsrc) : Prop :=
  (re_cap e' = 0 \/ re_cap e' = 8192 \/ re_cap e' = 16384) /\
  ((re_hp e' = re_hp e /\ re_kh e' = re_kh e) \/ re_kh e' <= 2 ^ 30) /\
  NoDup (drain_b_c.keys_texts (re_keys e')) /\
  same_set (drain_b_c.keys_texts (re_keys e')) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)).
(* dr_post's clauses on the source it leaves: the pending list emptied, its capacity, the expected list's capacity *)
Definition dr3_hpost (h h' : hsrc) : Prop :=
  hl_recs (hs_pending h') = [] /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
  hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h'))).
(* aentry_ok's held-array clause, W_rep.v:133-134 *)
Definition ls3_kh (e : rentry) : Prop :=
  (re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e).
(* alist_at's count clause, W_rep.v:83, of the source's three lists *)
Definition ls3_hn (h : hsrc) : Prop :=
  hl_n (hs_pending h) <= hl_cap (hs_pending h) /\ hl_n (hs_expected h) <= hl_cap (hs_expected h) /\
  hl_n (hs_held h) <= hl_cap (hs_held h).
(* dr_post's clauses: the unfinished line, the key array, the read offset, the expected texts, the held list, and
   asrc_at h' (alist_at :81 of its expected list) *)
Definition ls3_dpost (m : lmod) (j : nat) (h : hsrc) (e' : rentry) (h1 : hsrc) : Prop :=
  let fin := dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h in
  bzs (re_U e') = drain_b_c.ds_u fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
  hs_off h1 = 0 /\
  map snd (hl_recs (hs_expected h1)) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
  hs_held h1 = hs_held h /\ hl_n (hs_expected h1) <= hl_cap (hs_expected h1).
(* cnl_post's clauses (dr_cfun) and its asrc_at (set_exp_held h1 E' H') (alist_at W_rep.v:83 of the held list) *)
Definition ls3_cpost (h1 : hsrc) (E' H' : hlist) : Prop :=
  hl_recs E' = [] /\ hl_cap E' = hl_cap (hs_expected h1) /\
  NoDup (texts H') /\ texts H' = RelayModel.upds (texts (hs_held h1)) (texts (hs_expected h1)) /\
  hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h1))
                             (2 * (hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1)))))) /\
  hl_n H' <= hl_cap H'.


Section dr_defsx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- cut_x's Section w (W_LLVMFuzzerTestOneInput_cut_x.v:199-244), verbatim ---- *)
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
(* ---- the arm's own parameter ---- *)
Variable MMAX : Z.                                   (* W7's request bound, dr_spec_x's parameter *)
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (a), (d)): drain's and check_no_loss's room record RP, at RM := the cut's
   NP (the cf instance: rp_RM := fun S _ => room_live_cf S = NP, so dre_RP_NP is iff_refl) *)
Variable RP : roomp.
(* check_no_loss's count peak after the drain, a function of the source the drain was called with: at the top it is
   ReplyTrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) (image A: the row's part of pk_drain) *)
Variable dr_cnl_pk : hsrc -> (Z -> bool) -> nat.

Definition dr_regs_call (cx : lfcx) (t : Z) (m : lmod) (j si : nat) (FF : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (FF + 32) /\ getr regs 24 = w64 (SB + FF / 8) /\
  getr regs 26 = w64 HI_G_NOUT /\ getr regs 27 = w64 SB /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 25 = w64 t /\ 0 <= t < OPS_MAX /\
  getr regs 20 = w64 (c_p cx + dr_k' cx m) /\
  getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si) /\
  getr regs 22 = w64 (lm_G m + AENT * Z.of_nat j).

(* ---- the state at `jal pthread_mutex_lock` (0x84900): everything lcut says at the found entry with eof = 0,
   plus in.n at F+144, at = 0 at F+192, a0 = s7 = &g_lock and ra = 0x84904 ---- *)

Definition DLK (cx : lfcx) (Hpe : list Z) (t : Z) (m : lmod) (j si : nat) (h : hsrc) (fpos : Z) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (k : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
  c = mkCfg (mkst regs (Z_to_bv 64 (SIGMA WS_pthread_mutex_lock)) mem (seg_rom segs)) md /\
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k /\
  aframe_at cx (frame_addr ly3 1 fpos) W mem /\
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
  amodel_at B ly3 S3 W mem m /\ ainput_at B cx ly3 S3 W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  ablocks_sep B fr_FP cx m ly3 S3 /\ LSx cx t m ly3 S3 /\ NP S3 /\ RINV cx t m /\
  dr_at_op cx m /\ dr_pick cx m si h /\ (j < length (lm_es m))%nat /\
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\ re_eof (nth j (lm_es m) dr_e0) = 0 /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\ sv8 W mem (lf_F cx + DR_AT) 0 /\
  getr regs 1 = Z_to_bv 64 (BASE + A_dr_r1) /\ getr regs 10 = w64 (rg_lock fr_RG) /\
  getr regs 23 = w64 (rg_lock fr_RG) /\
  dr_regs_call cx t m j si (frame_addr ly3 1 fpos) regs.

(* ------------------------------------------------------------------ the functional half of one drained
   operation: W7's dr_post over the entry and the source, then k4's cnl_post over the drained source's two lists
   (image A's dr_step_ok, at B's contracts) *)

Record dr_env_x : Prop := mk_dr_env_x {
  (* ---- the allocator instance and the callees, each the kit's _x form at the walk's PST / ARx ---- *)
  dre_TL : PALib (PI := PB_fr) B;
  (* the room round: RP's rp_RM is the cut's NP *)
  dre_RP_NP : forall S k, rp_RM RP S k <-> NP S;
  dre_DRAIN : dr_spec_x (PI := PB_fr) B PST ARx MT RP MMAX fr_RG (BASE + AF_fr_drain);
  dre_ALOCK : alock_realizes_x (PI := PB_fr) B ARx (SIGMA WS_pthread_mutex_lock);
  dre_AUNLOCK : aunlock_realizes_x (PI := PB_fr) B ARx (SIGMA WS_pthread_mutex_unlock);
  dre_CNLR : cnlr_spec_x (PI := PB_fr) B PST ARx (BASE + AF_fr_check_no_loss_read);
  dre_CSD : csd_spec_x (PI := PB_fr) B PST ARx (BASE + AF_fr_check_shape_done);
  (* the kit's check_no_loss over ARx (lib/B/W_contract_x.v Section w3n), at the G the call site takes: the slot's
     two list headers.  Its proof pb_check_no_loss takes gx_ok and (through its callees) rom_out at its own G. *)
  dre_CNL : forall G, gx_ok segs B G -> gx_rt (PI := PB_fr) B G -> rom_out segs B G ->
    cnl_spec_x (PI := PB_fr) B PST ARx MT RP G MMAX (BASE + AF_fr_check_no_loss);
  (* ---- the G-coverage facts: every global a callee writes is one of the entry's G_fr ---- *)
  dre_HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a;
  dre_HG_DR : forall a, inG (G_DR B fr_RG) a -> inG G_fr a;
  dre_HGlock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a;
  (* the other cells of amodel_at are G_fr's too (so they are no allocator static: gx_ok) *)
  dre_HG_GK : forall a, inG [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
    (rg_send_max fr_RG, 8); (rg_client fr_RG, 4); (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1);
    (rg_wake fr_RG, 8); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a -> inG G_fr a;
  (* errno's cell (0x5d994c on image B, lib/B/YF0m.v ts_errno) lies above every program global amodel_at names *)
  dre_HERR_HI : rg_out fr_RG + 8 <= as_errno B;
  (* cut_x's errno_law_x / _cut's glob_wr_law at G_fr, verbatim *)
  dre_ERR : errno_law_x B ARx;
  dre_GWR : glob_wr_law G_fr;
  (* W_journal.v's rom_out at G_fr *)
  dre_ROM_OUT : rom_out segs B G_fr;
  (* g_s lies in one of the instance's zero-shadow ranges (lib/B/W_LLVMFuzzerTestOneInput_G.v's measurement:
     Tfib_zero_shadow holds (0x5d8e60, 384)) *)
  dre_HZS : azs B (rg_s fr_RG) (4 * ASRC);
  (* the image objects this arm reads are apart from g_s; on image B the shadow GOT slot is A_OBJ 0 and
     __asan_shadow_memory_dynamic_address is A_OBJ 30 (lib/B/W_LLVMFuzzerTestOneInput_G.v c_HAP) *)
  dre_HAP : (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rg_s fr_RG) /\
            (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= rg_s fr_RG);
  (* ---- the generic relation's two facts the AR proof read off AR (AddX's A drain_x HPST / BLKR):
     the image is off PST (W_op_add.v Section x's HPST: a callee's journal keeps every image byte outside the
     callee's own G, and ROM; trivial at the instance's PST := []); a live block's request is in [0, 2 ^ 30)
     (AR's al_blocks carries 0 <= n < MALLOC_MAX = 2 ^ 28, AR_laws_x's alx_blocks does not; the cf instance has
     0 <= n < cf_malloc_max as AR_blocks_law_cf's last conjunct and cf_malloc_max + 15 <= 2 ^ 30) ---- *)
  dre_HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST;
  dre_BLKR : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
    0 <= n < 2 ^ 30;
  (* ---- the arm's open model obligations (pure, over lmod and the plain records) ---- *)
  dre_RI_drain_skip : forall cx t m si h,
    RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
    (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
     (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
        re_eof (nth j (lm_es m) dr_e0) = 1)) ->
    RINV cx (t + 1) (dr_skip m (dr_k' cx m));
  dre_RI_drain_step : forall cx t m si h j e' h' c' O' cap' out' ev' LB E' H',
    RINV cx t m -> 0 <= t < OPS_MAX ->
    hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h'))) < 2 ^ 22 ->
    dr_at_op cx m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
    length (re_pad1 e') = 4%nat -> length (re_pad2 e') = 4%nat ->
    hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h'))
      (2 * (hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h')))))) ->
    RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out');
  (* ---- the drain's count growth (the room round's count rule).  check_no_loss's count premise is at the state the
     drain leaves; dre_LS_cnt bounds the counts at the cut.  dr_post's two Permutations (W_contract_x.v dr_post_x) make
     the change of every count the change over the drained entry's, source's and g_out's blocks, with the same rest;
     this rule says that change is at most the drain trace's count peak, for every count predicate P.  A PURE MODEL
     rule (no astate; W8Entry-2's 04:20Z pattern, as the gone arm's GN_CNT_step), with the premises the walk holds at
     the drain's return (dc_stB): the cut's model facts at the call (dc_static, LS_cnt's guards, the dr3 / ls3
     bundles of the entry and the source) and dr_post's model clauses (dr_dfun, dr3_epost, dr3_hpost, ls3_dpost) ---- *)
  dre_DR_CNT_grow : forall cx t m si h j e' h' LB out' (P : Z -> bool),
    RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    msz_ok m -> 0 <= t < OPS_MAX ->
    Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
    (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
       0 < snd b) ->
    dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) ->
    dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
    dr_dfun m si h j e' h' LB ->
    dr3_epost (nth j (lm_es m) dr_e0) e' h ->
    (* added: the held-array clause of the entry drain leaves (aentry_ok e', W_rep.v:133-134) *)
    ((re_hp e' = 0 /\ re_keys e' = []) \/ (re_hp e' <> 0 /\ 8 <= re_kh e')) ->
    dr3_hpost h h' ->
    ls3_dpost m j h e' h' ->
    (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks (dr_cap1 m j h) out') <=
     ReplyCnt.acnt P (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) +
     Z.to_nat (ReplyCnt.tr_peakP P
       (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)))%nat;
  dre_RI_src : forall cx t m si h,
    RINV cx t m -> dr_pick cx m si h ->
    hl_recs (hs_expected h) = [] /\ NoDup (texts (hs_held h)) /\ 0 <= hs_fd h < 2 ^ 31;
  dre_RI_fds : forall cx t m i1 i2 h1 h2,
    RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
    nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2;
  dre_RI_pair : forall cx t m si h j,
    RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
    re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
    re_skip (nth j (lm_es m) dr_e0) = hs_overlong h /\
    (re_skip (nth j (lm_es m) dr_e0) = 0 -> bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h)) /\
    length (re_pad1 (nth j (lm_es m) dr_e0)) = 4%nat /\ length (re_pad2 (nth j (lm_es m) dr_e0)) = 4%nat;
  dre_RI_gone : forall cx t m,
    RINV cx t m ->
    (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
    (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1);
  (* ---- the allocator-state facts the two calls take, read off LSx ---- *)
  (* the peak form (a Theorem Labs lane's ROOM-ROUND row #19; dr_spec's byte premise is the drain trace's byte PEAK, C3), image A's
     text: conjunct 5 is s5-r1d's fr_LS_drain_pre_c5p (lib/A/ReplyTrPeak.v:942 on image A), and the three premises
     after re_eof are the ones its rows take (fr_LS3_drain_pre_c4 lib/A/ReplyLS3Arms.v:790, fr_LS_drain_pre_c5p):
     dc_regs' Ht, aentry_ok's |re_U| bound and the drained blocks' sizes (dc_stB's HXP).  The sum form (tr_alloc) was
     FALSE at reachable states. *)
  dre_LS_drain_pre : forall cx t m ly S si h j,
    LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    0 <= t < OPS_MAX ->
    Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
    (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
       0 < snd b) ->
    Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
    hl_cap (hs_expected h) < 2 ^ 26 /\
    re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
    tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < MMAX /\
    blocks_bytes S +
      tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
      <= LIVE_MAX /\
    mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h);
  (* after the drain: what check_no_loss takes of the state it is called in.  A Theorem Labs lane's TX_LS_cnl_pre
     (commit d0d75bf92db, lib/A/ReplyLS3cTopxPost.v:146 on image A; proved as ReplyLS3Arms.v:841 fr_LS3_cnl_pre_p),
     as image A's drain arm states it: the binders e' cap' out' and nine premises after the old ten, each held at
     dr_stage_calls (dc_regs' Ht, dr_at_op's lm_O m = [], and dc_stB's dcB_out: the cut's entry and source at the
     call, dr_post's frame and its entry / source clauses); and, last in the conclusion, check_no_loss's memmove
     bound `AREC * capb .. < 2 ^ 32`, as the B top_x's LS_cnl_pre states it (a Theorem Labs lane's TX_LS_cnl_pre,
     lib/B/ReplyB3LS3cTopxPost.v:173-201 at a working branch 92b82c11331) *)
  dre_LS_cnl_pre : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
    LSx cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                     (nth j (lm_es m) dr_e0) h) ->
    hl_cap (hs_expected h'') = drain_b_c.ds_ecap
      (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
    map snd (hl_recs (hs_expected h'')) =
      map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
    hs_held h'' = hs_held h ->
    0 <= t < OPS_MAX -> lm_O m = [] ->
    dr3_epre (nth j (lm_es m) dr_e0) -> dr3_hpre h -> 0 <= lm_cap m ->
    (exists rest,
       Permutation (ablocks B ly S)
         (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
       Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
    cap' = (if dr_live (lm_c m) h
            then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                     (nth j (lm_es m) dr_e0) h)
            else lm_cap m) ->
    dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h'' ->
    NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
    hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
    cnl_room MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h''))
      (hl_recs (hs_expected h'')) /\
    mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')) /\
    AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32;
  dre_LS_drain_skip : forall cx t m ly S,
    LSx cx t m ly S -> LSx cx (t + 1) (dr_skip m (dr_k' cx m)) ly S;
  (* the drain charges the meter dr_cost of the entry and source it was called with (S to S1), check_no_loss
     cnl_cost of the lists it was called with (S1 to S').  A Theorem Labs lane's TX_LS_drain_step (commit d0d75bf92db,
     lib/A/ReplyLS3cTopxPost.v:118 on image A; proved as ReplyLS3cArms.v:118 fr_LS3c_drain_step_p), as image A's drain
     arm states it: the binders ly1 h1 E' H' and twenty premises after the old five, each held at dr_stage_calls (the
     drain's and check_no_loss's frames, dcB_out and dc_stE's exports); and, last, dc_regs' `0 <= t < OPS_MAX`, as
     s5-r1d's TX_LS_drain_step_t (1318828167d lib/A/ReplyLSI.v:134, its LS instance's lsi_LS_drain_step :509) *)
  dre_LS_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
      si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
    LSx cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
    mo_le MT S S1
      (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
    mo_le MT S1 S' (cnl_cost MT E H) ->
    (exists rest,
       Permutation (ablocks B ly S)
         (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
       Permutation (ablocks B ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
    hl_recs (hs_pending h1) = [] ->
    E = hs_expected h1 -> H = hs_held h1 ->
    (forall rest, Permutation (ablocks B ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
       Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
    h'' = set_exp_held h1 E' H' ->
    dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) ->
    dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
    cap' = (if dr_live (lm_c m) h
            then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                     (nth j (lm_es m) dr_e0) h)
            else lm_cap m) ->
    dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 ->
    ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
    0 <= t < OPS_MAX ->
    LSx cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S';
  (* the kit's check_no_loss trace after a drain has at most dr_cnl_pk's peak: the expected list was empty at the
     operation's start (RI_src) and the drain appended the lines (dr_dfun), the held list is kept (a PURE MODEL rule;
     at the top ReplyLScnt.lsc_cnl_call proves it with = at j := 0, nm := fun _ => RelayRunF.adr0, image A) *)
  dre_DR_CNT_cnl : forall (h h'' : hsrc) (P : Z -> bool),
    hl_recs (hs_expected h) = [] ->
    map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
    hs_held h'' = hs_held h ->
    (Z.to_nat (ReplyCnt.tr_peakP P (cnl_tr (hs_expected h'') (hs_held h''))) <= dr_cnl_pk h P)%nat;
  (* the live counts at the cut leave room for the arm's peak (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c), CORRECTION 2):
     a Theorem Labs lane's row fr_LS3cp_cnt_drain (commit ba8e99b5bd2, lib/A/ReplyLScnt.v:371 on image A) with its guards,
     over the room record's count fields.  Its peak is the row's pk_drain m h j (ReplyLScnt.v:151) with
     check_no_loss's part the parameter dr_cnl_pk: drain's trace peak + check_no_loss's peak over the drained lines
     + 2, which covers dr_spec's count premise (dr_pk) at the cut and cnl_spec's (cnl_pk) at the state the drain
     leaves (dre_DR_CNT_grow, dre_DR_CNT_cnl) *)
  dre_LS_cnt : forall cx t m ly S si h j,
    LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    msz_ok m -> 0 <= t < OPS_MAX ->
    Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
    (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
       0 < snd b) ->
    ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
    cnt_ok_pk RP
      (fun P => (Z.to_nat (ReplyCnt.tr_peakP P
         (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)) +
         (dr_cnl_pk h P + 2))%nat)
      (ablocks B ly S)
}.



(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twin of DLK (journal at R) and the dr_env_xR bundle (DRAIN / CNL at
   their R specs dr_spec_xR / cnl_spec_xR; the non-re-hiding leaves ALOCK / AUNLOCK / CNLR / CSD keep their strict
   specs, lifted at the call; every model rule is the strict one).  Strict text above unchanged. ---- *)
Section dr_defsxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.

Definition DLK_xR (cx : lfcx) (Hpe : list Z) (t : Z) (m : lmod) (j si : nat) (h : hsrc) (fpos : Z) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (k : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
  c = mkCfg (mkst regs (Z_to_bv 64 (SIGMA WS_pthread_mutex_lock)) mem (seg_rom segs)) md /\
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k /\
  aframe_at cx (frame_addr ly3 1 fpos) W mem /\
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
  amodel_at B ly3 S3 W mem m /\ ainput_at B cx ly3 S3 W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  ablocks_sep B fr_FP cx m ly3 S3 /\ LSx cx t m ly3 S3 /\ NP S3 /\ RINV cx t m /\
  dr_at_op cx m /\ dr_pick cx m si h /\ (j < length (lm_es m))%nat /\
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\ re_eof (nth j (lm_es m) dr_e0) = 0 /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\ sv8 W mem (lf_F cx + DR_AT) 0 /\
  getr regs 1 = Z_to_bv 64 (BASE + A_dr_r1) /\ getr regs 10 = w64 (rg_lock fr_RG) /\
  getr regs 23 = w64 (rg_lock fr_RG) /\
  dr_regs_call cx t m j si (frame_addr ly3 1 fpos) regs.

Record dr_env_xR : Prop := mk_dr_env_xR {
  (* ---- the allocator instance and the callees, each the kit's _x form at the walk's PST / ARx ---- *)
  dreR_TL : PALib (PI := PB_fr) B;
  (* the room round: RP's rp_RM is the cut's NP *)
  dreR_RP_NP : forall S k, rp_RM RP S k <-> NP S;
  dreR_DRAIN : dr_spec_xR (PI := PB_fr) B PST ARx R MT RP MMAX fr_RG (BASE + AF_fr_drain);
  dreR_ALOCK : alock_realizes_x (PI := PB_fr) B ARx (SIGMA WS_pthread_mutex_lock);
  dreR_AUNLOCK : aunlock_realizes_x (PI := PB_fr) B ARx (SIGMA WS_pthread_mutex_unlock);
  dreR_CNLR : cnlr_spec_x (PI := PB_fr) B PST ARx (BASE + AF_fr_check_no_loss_read);
  dreR_CSD : csd_spec_x (PI := PB_fr) B PST ARx (BASE + AF_fr_check_shape_done);
  (* the kit's check_no_loss over ARx (lib/B/W_contract_x.v Section w3n), at the G the call site takes: the slot's
     two list headers.  Its proof pb_check_no_loss takes gx_ok and (through its callees) rom_out at its own G. *)
  dreR_CNL : forall G, gx_ok segs B G -> gx_rt (PI := PB_fr) B G -> rom_out segs B G ->
    cnl_spec_xR (PI := PB_fr) B PST ARx R MT RP G MMAX (BASE + AF_fr_check_no_loss);
  (* ---- the G-coverage facts: every global a callee writes is one of the entry's G_fr ---- *)
  dreR_HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a;
  dreR_HG_DR : forall a, inG (G_DR B fr_RG) a -> inG G_fr a;
  dreR_HGlock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a;
  (* the other cells of amodel_at are G_fr's too (so they are no allocator static: gx_ok) *)
  dreR_HG_GK : forall a, inG [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
    (rg_send_max fr_RG, 8); (rg_client fr_RG, 4); (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1);
    (rg_wake fr_RG, 8); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a -> inG G_fr a;
  (* errno's cell (0x5d994c on image B, lib/B/YF0m.v ts_errno) lies above every program global amodel_at names *)
  dreR_HERR_HI : rg_out fr_RG + 8 <= as_errno B;
  (* cut_x's errno_law_x / _cut's glob_wr_law at G_fr, verbatim *)
  dreR_ERR : errno_law_x B ARx;
  dreR_GWR : glob_wr_law G_fr;
  (* W_journal.v's rom_out at G_fr *)
  dreR_ROM_OUT : rom_out segs B G_fr;
  (* g_s lies in one of the instance's zero-shadow ranges (lib/B/W_LLVMFuzzerTestOneInput_G.v's measurement:
     Tfib_zero_shadow holds (0x5d8e60, 384)) *)
  dreR_HZS : azs B (rg_s fr_RG) (4 * ASRC);
  (* the image objects this arm reads are apart from g_s; on image B the shadow GOT slot is A_OBJ 0 and
     __asan_shadow_memory_dynamic_address is A_OBJ 30 (lib/B/W_LLVMFuzzerTestOneInput_G.v c_HAP) *)
  dreR_HAP : (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rg_s fr_RG) /\
            (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= rg_s fr_RG);
  (* ---- the generic relation's two facts the AR proof read off AR (AddX's A drain_x HPST / BLKR):
     the image is off PST (W_op_add.v Section x's HPST: a callee's journal keeps every image byte outside the
     callee's own G, and ROM; trivial at the instance's PST := []); a live block's request is in [0, 2 ^ 30)
     (AR's al_blocks carries 0 <= n < MALLOC_MAX = 2 ^ 28, AR_laws_x's alx_blocks does not; the cf instance has
     0 <= n < cf_malloc_max as AR_blocks_law_cf's last conjunct and cf_malloc_max + 15 <= 2 ^ 30) ---- *)
  dreR_HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST;
  dreR_BLKR : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
    0 <= n < 2 ^ 30;
  (* ---- the arm's open model obligations (pure, over lmod and the plain records) ---- *)
  dreR_RI_drain_skip : forall cx t m si h,
    RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
    (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
     (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
        re_eof (nth j (lm_es m) dr_e0) = 1)) ->
    RINV cx (t + 1) (dr_skip m (dr_k' cx m));
  dreR_RI_drain_step : forall cx t m si h j e' h' c' O' cap' out' ev' LB E' H',
    RINV cx t m -> 0 <= t < OPS_MAX ->
    hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h'))) < 2 ^ 22 ->
    dr_at_op cx m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
    length (re_pad1 e') = 4%nat -> length (re_pad2 e') = 4%nat ->
    hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h'))
      (2 * (hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h')))))) ->
    RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out');
  (* ---- the drain's count growth (the room round's count rule).  check_no_loss's count premise is at the state the
     drain leaves; dreR_LS_cnt bounds the counts at the cut.  dr_post's two Permutations (W_contract_x.v dr_post_x) make
     the change of every count the change over the drained entry's, source's and g_out's blocks, with the same rest;
     this rule says that change is at most the drain trace's count peak, for every count predicate P.  A PURE MODEL
     rule (no astate; W8Entry-2's 04:20Z pattern, as the gone arm's GN_CNT_step), with the premises the walk holds at
     the drain's return (dc_stB): the cut's model facts at the call (dc_static, LS_cnt's guards, the dr3 / ls3
     bundles of the entry and the source) and dr_post's model clauses (dr_dfun, dr3_epost, dr3_hpost, ls3_dpost) ---- *)
  dreR_DR_CNT_grow : forall cx t m si h j e' h' LB out' (P : Z -> bool),
    RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    msz_ok m -> 0 <= t < OPS_MAX ->
    Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
    (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
       0 < snd b) ->
    dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) ->
    dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
    dr_dfun m si h j e' h' LB ->
    dr3_epost (nth j (lm_es m) dr_e0) e' h ->
    (* added: the held-array clause of the entry drain leaves (aentry_ok e', W_rep.v:133-134) *)
    ((re_hp e' = 0 /\ re_keys e' = []) \/ (re_hp e' <> 0 /\ 8 <= re_kh e')) ->
    dr3_hpost h h' ->
    ls3_dpost m j h e' h' ->
    (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks (dr_cap1 m j h) out') <=
     ReplyCnt.acnt P (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) +
     Z.to_nat (ReplyCnt.tr_peakP P
       (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)))%nat;
  dreR_RI_src : forall cx t m si h,
    RINV cx t m -> dr_pick cx m si h ->
    hl_recs (hs_expected h) = [] /\ NoDup (texts (hs_held h)) /\ 0 <= hs_fd h < 2 ^ 31;
  dreR_RI_fds : forall cx t m i1 i2 h1 h2,
    RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
    nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2;
  dreR_RI_pair : forall cx t m si h j,
    RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
    re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
    re_skip (nth j (lm_es m) dr_e0) = hs_overlong h /\
    (re_skip (nth j (lm_es m) dr_e0) = 0 -> bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h)) /\
    length (re_pad1 (nth j (lm_es m) dr_e0)) = 4%nat /\ length (re_pad2 (nth j (lm_es m) dr_e0)) = 4%nat;
  dreR_RI_gone : forall cx t m,
    RINV cx t m ->
    (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
    (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1);
  (* ---- the allocator-state facts the two calls take, read off LSx ---- *)
  (* the peak form (a Theorem Labs lane's ROOM-ROUND row #19; dr_spec's byte premise is the drain trace's byte PEAK, C3), image A's
     text: conjunct 5 is s5-r1d's fr_LS_drain_pre_c5p (lib/A/ReplyTrPeak.v:942 on image A), and the three premises
     after re_eof are the ones its rows take (fr_LS3_drain_pre_c4 lib/A/ReplyLS3Arms.v:790, fr_LS_drain_pre_c5p):
     dc_regs' Ht, aentry_ok's |re_U| bound and the drained blocks' sizes (dc_stB's HXP).  The sum form (tr_alloc) was
     FALSE at reachable states. *)
  dreR_LS_drain_pre : forall cx t m ly S si h j,
    LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    0 <= t < OPS_MAX ->
    Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
    (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
       0 < snd b) ->
    Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
    hl_cap (hs_expected h) < 2 ^ 26 /\
    re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
    tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < MMAX /\
    blocks_bytes S +
      tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
      <= LIVE_MAX /\
    mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h);
  (* after the drain: what check_no_loss takes of the state it is called in.  A Theorem Labs lane's TX_LS_cnl_pre
     (commit d0d75bf92db, lib/A/ReplyLS3cTopxPost.v:146 on image A; proved as ReplyLS3Arms.v:841 fr_LS3_cnl_pre_p),
     as image A's drain arm states it: the binders e' cap' out' and nine premises after the old ten, each held at
     dr_stage_calls (dc_regs' Ht, dr_at_op's lm_O m = [], and dc_stB's dcB_out: the cut's entry and source at the
     call, dr_post's frame and its entry / source clauses); and, last in the conclusion, check_no_loss's memmove
     bound `AREC * capb .. < 2 ^ 32`, as the B top_x's LS_cnl_pre states it (a Theorem Labs lane's TX_LS_cnl_pre,
     lib/B/ReplyB3LS3cTopxPost.v:173-201 at a working branch 92b82c11331) *)
  dreR_LS_cnl_pre : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
    LSx cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                     (nth j (lm_es m) dr_e0) h) ->
    hl_cap (hs_expected h'') = drain_b_c.ds_ecap
      (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
    map snd (hl_recs (hs_expected h'')) =
      map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
    hs_held h'' = hs_held h ->
    0 <= t < OPS_MAX -> lm_O m = [] ->
    dr3_epre (nth j (lm_es m) dr_e0) -> dr3_hpre h -> 0 <= lm_cap m ->
    (exists rest,
       Permutation (ablocks B ly S)
         (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
       Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
    cap' = (if dr_live (lm_c m) h
            then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                     (nth j (lm_es m) dr_e0) h)
            else lm_cap m) ->
    dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h'' ->
    NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
    hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
    cnl_room MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h''))
      (hl_recs (hs_expected h'')) /\
    mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')) /\
    AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32;
  dreR_LS_drain_skip : forall cx t m ly S,
    LSx cx t m ly S -> LSx cx (t + 1) (dr_skip m (dr_k' cx m)) ly S;
  (* the drain charges the meter dr_cost of the entry and source it was called with (S to S1), check_no_loss
     cnl_cost of the lists it was called with (S1 to S').  A Theorem Labs lane's TX_LS_drain_step (commit d0d75bf92db,
     lib/A/ReplyLS3cTopxPost.v:118 on image A; proved as ReplyLS3cArms.v:118 fr_LS3c_drain_step_p), as image A's drain
     arm states it: the binders ly1 h1 E' H' and twenty premises after the old five, each held at dr_stage_calls (the
     drain's and check_no_loss's frames, dcB_out and dc_stE's exports); and, last, dc_regs' `0 <= t < OPS_MAX`, as
     s5-r1d's TX_LS_drain_step_t (1318828167d lib/A/ReplyLSI.v:134, its LS instance's lsi_LS_drain_step :509) *)
  dreR_LS_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
      si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
    LSx cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
    mo_le MT S S1
      (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
    mo_le MT S1 S' (cnl_cost MT E H) ->
    (exists rest,
       Permutation (ablocks B ly S)
         (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
       Permutation (ablocks B ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
    hl_recs (hs_pending h1) = [] ->
    E = hs_expected h1 -> H = hs_held h1 ->
    (forall rest, Permutation (ablocks B ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
       Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
    h'' = set_exp_held h1 E' H' ->
    dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) ->
    dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
    cap' = (if dr_live (lm_c m) h
            then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                     (nth j (lm_es m) dr_e0) h)
            else lm_cap m) ->
    dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 ->
    ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
    0 <= t < OPS_MAX ->
    LSx cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S';
  (* the kit's check_no_loss trace after a drain has at most dr_cnl_pk's peak: the expected list was empty at the
     operation's start (RI_src) and the drain appended the lines (dr_dfun), the held list is kept (a PURE MODEL rule;
     at the top ReplyLScnt.lsc_cnl_call proves it with = at j := 0, nm := fun _ => RelayRunF.adr0, image A) *)
  dreR_DR_CNT_cnl : forall (h h'' : hsrc) (P : Z -> bool),
    hl_recs (hs_expected h) = [] ->
    map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
    hs_held h'' = hs_held h ->
    (Z.to_nat (ReplyCnt.tr_peakP P (cnl_tr (hs_expected h'') (hs_held h''))) <= dr_cnl_pk h P)%nat;
  (* the live counts at the cut leave room for the arm's peak (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c), CORRECTION 2):
     a Theorem Labs lane's row fr_LS3cp_cnt_drain (commit ba8e99b5bd2, lib/A/ReplyLScnt.v:371 on image A) with its guards,
     over the room record's count fields.  Its peak is the row's pk_drain m h j (ReplyLScnt.v:151) with
     check_no_loss's part the parameter dr_cnl_pk: drain's trace peak + check_no_loss's peak over the drained lines
     + 2, which covers dr_spec's count premise (dr_pk) at the cut and cnl_spec's (cnl_pk) at the state the drain
     leaves (dreR_DR_CNT_grow, dreR_DR_CNT_cnl) *)
  dreR_LS_cnt : forall cx t m ly S si h j,
    LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    msz_ok m -> 0 <= t < OPS_MAX ->
    Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
    (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
       0 < snd b) ->
    ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
    cnt_ok_pk RP
      (fun P => (Z.to_nat (ReplyCnt.tr_peakP P
         (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)) +
         (dr_cnl_pk h P + 2))%nat)
      (ablocks B ly S)
}.
End dr_defsxR.

End dr_defsx.
