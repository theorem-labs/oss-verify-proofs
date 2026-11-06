(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 316 of its 361 lines of code are new or changed and 733 lines of the source are left out. *)
(* kb round (the kb Glue c580eb0fe37c, the B' twin of Crt102Kit.crt102rw_at_X at the A' kb head a54cc6d36c2c):
   crt_at_J_B's live state is at kb = prh_wk F_check_round_trip (66), its journal at a budget WS; X's run stores no
   wild trace (Crt102Kit.crt_run_to_xw_inv), so J_B is entered at the same budget, by identity. *)
(* fuzz_preset, image B' (asan-ubsan, pin d663f82d7f488d30, twin c90d4fa54d43160b): THE X SEGMENT
   of the walk of check_round_trip (fuzz_preset.c new:772-781): the shared re-poison of back and v, from X (+0x30c) to
   the join J (+0x348), against the contract text tcheck_round_trip_specX (lib/A/PRH_FnCheck.v).
   Its export is cb_at_X_B, the glue's CRT_B_AT_X at the B' instance:
   `crt_at_X_B .. -> SRr' SEGS RZ_cf Wc (crt_cfg fxk CRT_X_OFF_B rg memc mdc) QF`, given the J_B stretch TAIL (the Section
   hypothesis Crt102TailB.crt102_tail_B discharges at composition).
   STATUS: cb_at_X_B is Qed. The B' twin of Crt102Kit.crt102rw_at_X (lib/A/Prog/Crt102Kit.v fb64ea6c3126:1476-1582):
   the same design at the B' instance, the B' cut offsets and crt_bregs_B; the frame and stack facts are
   Crt102KitB's (cb4_ff, cb4_sp, cb4_doc_home, cb4_ro_img, cb4_fb), cited; the X-run's live-state lemmas
   (cxb_live_run, cxb_lam_app, cxb_foot_nw) are Crt102Kit.v's crt102rw_live_run / crt102rw_lam_app /
   crt102rw_foot_nw at B', over X's own write set only (cxb_wr: the frame's shadow bytes 4 .. 22). copy's freeable
   tree crosses the stores by PRH_PjOrder's pj_fdR_foR / pj_foR_frame / pj_foR_fdR (no image-free frame lemma of
   pj_fdR is on the B' side: Crt102Kit.v's crt102rw_fdR_frame lives in the A' file, whose Requires hold the A' image).

   INPUTS OF RECORD (by path, on commit 100c8e45583c; blobs by `git rev-parse --short=12`):
   - pins: B' asan-ubsan sha256 d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, its unstripped twin
     sha256 c90d4fa54d43160baf62e5aa387211a798dddbad13d2619d85acbf37aee0c175; this file is image B' only.
   - the glue lib/A/Prog/Crt102Glue.v d65f66b784a1: crt_at_X_B (fields crt_at_X_B_join / _back_open / _v_open),
     crt_at_J_B (fields crt_at_J_B_live / _frm_zero / _fregs / _bregs / _ret / _copy_fd / _r0 / _count), crt_live,
     crt_side, crt_frame, crt_bregs_B, QF; lib/B/Prog/Crt102KitB.v 72715b66ca60 (the B' kit, cited).
   - the contract texts: lib/A/PRH_FnCheck.v 0844ed8c0608 (the text, its post QT), lib/A/PRH_Base.v ee2f5cd7ed35 (fpre,
     prh_ledger, prh_ledger_hblock), lib/A/PRH_Reader.v 91d2dbd40054 (pj_nodeR_frame, pj_fdR), lib/A/PRH_PjOrder.v
     e5917626b82b (pj_foR, pj_fdR_foR, pj_foR_fdR, pj_foR_frame); lib/A/Prog/S1Ledger.v 8cf15eeb6311
     (prh_ledger_kept_aview); lib/A/CfParamsPreset.v b60d0f63c926.
   - the image: lib/A/Prog/Crt102Img.v 176eec830b61 (CRT_PC_B, CRT_X_OFF_B = 0x30c, CRT_J_OFF_B = 0x348;
     crt_cut_X_B / crt_cut_J_B check the listing's words there), lib/B/Prog/CrtImgB102.v e07deaef6b0d
     (crt_pst_img_B_cf), lib/B/PAImg_prog.v 15fab93fe702 (PI_prog_B, PL_prog_B), lib/B/PRH_ImgB.v 3216eca68342,
     lib/Reusable/YImgTop.v d2a97d3111ce.
   - the listing lib/B/Listing_prog.v c97cc46b3e13 (check_round_trip at slot 1111; X is
     the internal file crt.B.s lines 197-211, 0x82b34 .. 0x82b6c).
   - the model: lib/A/Prog/Crt102Kit.v fb64ea6c3126 (crt102rw_at_X, crt102rw_ssSH / crt102rw_SH_entry,
     crt102rw_live_run, crt102rw_lam_app, crt102rw_foot_nw), read, not Required.
   - the engine: YC1fPx 7814b594066f (paj_run_to_x_inv, paj_run_to_tok_x_inv), YC1fP 5a3e259a9c67, YCbqG
     c3b5d0111037, YSRrMemnorm 5ffa8525936b (srr_inv_laws_imp), YAkMemnorm 96c72061b4d4.
   - rule 24: proves function check_round_trip (B' X -> J). proof-index cb_at_X_B crt_at_X_B (index built
     2026-10-30T03:47Z): cb_at_X_B 0 hits on the released branches, the delivery, the 16815 cold/* branches and the
     live heads; crt_at_X_B only as the glue's Record declaration (UNRELEASED copies of Crt102Glue.v) and its
     consumers, no proof of CRT_B_AT_X. The walk's measurement (2026-10-30): no cold/* ref proves it,
     proof-index exit=4, the rule-24 check's verdict CONFIRM. Written new.

   THE SEGMENT (offsets from check_round_trip's entry, Crt102Img.v's names; byte-equal to A''s X at +0x304):
   - X (CRT_X_OFF_B = +0x30c): `addi a0, zero, -8`, then fourteen `sb a0, k(s2)` with k = 8 .. 0xa, 0x10 .. 0x16,
     4 .. 7: f8 into the frame's shadow bytes 4 .. 10 and 16 .. 22 (the shadow of back at F + 0x20 and of v at
     F + 0x80); one engine run to J (CRT_J_OFF_B = +0x348), no call and no branch. s2 = shadow_addr F
     (crt_bregs_B_s2) on B' as on A'. Then TAIL.

   NUMERALS. LENGTH: 4 / 23 (the frame's shadow bytes the run writes, 4 .. 22), 64 (the frame's shadow bytes),
   512 (the class-3 frame), 56 (struct pj), 2 ^ 44 / 2 ^ 47 / 2 ^ 63 / 2 ^ 64 (the shadow span, the stack band, the
   static span, the word). DERIVED: atom indices (the engine's numbering), the cut offsets (Crt102Img's names).
   No ADDRESS literal: every code address is pa_val / pa_sigma of PI_prog_B.

   SECTION HYPOTHESES (each with its source, at its definition below): LAWS (engine AR_laws_x fold; at ARcf
   AR_laws_x_cf), HPRE / HTREE (the contract text: tcheck_round_trip_specX's entry premises; Crt102Top discharges them
   from the text's), TAIL (row T8: Crt102TailB.crt102_tail_B). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base CfParamsPreset PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB CrtImgB102.
(* the B' kit: the frame, stack and document facts, cited *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Crt102KitB.
(* kb round: the image-free AJW runner of the A' kit (Crt102Kit.crt_run_to_xw_inv, Section kbw), used qualified with
   every implicit argument given at the B' instance *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Kit.
(* On the Step-1 contract texts (the re-hiding move): the step relation is
   YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf and the journals are at R := YA0nH.wle' SEGS RZ_cf (Crt102Glue / Kit / KitB);
   X's run is Kit's crt_run_to_xw_inv at R. Contract note: the internal file WLE-CONTRACT.md. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* the shadow-store segment shape (Crt102Kit.v's crt102rw_ssSH, image-free): one region, the frame's shadow bytes
   4 .. 22 through s2 *)
Definition cxb_ssSH (pc : Z) : sstate := mkSS pc cur_atoms
  [YP09.mkRegion (Some (xr 18)) 4 23 4 23 []] None (mkFacts [(xr 18, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)] [] []).

(* a register a run did not write (S10TxString.v's tskeep, as Crt102Kit.v's crt102rw_keep) *)
Ltac cxb_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

(* ======================================================================================================== *)
Section xb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
(* THE B' INSTANCE (lib/B/PAImg_prog.v): its PAImg and its listing's table instance *)
#[local] Notation PA := (PAImg_prog.PI_prog_B).
#[local] Notation PL := (PAImg_prog.PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).
#[local] Notation TEB := (TE (L := B_prog_listing) (PA := PA)).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild-trace budget WS (kb round: crt_live's journal is at a budget WS with wbudget [] kb WS) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).
(* ---- SECTION HYPOTHESES, each with its owner ---- *)
(* the allocator laws (owner: the engine fold, YCbqG c3b5d0111037; at ARcf: AR_laws_x_cf) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

Section g.
(* ---- the entry: tcheck_round_trip_specX's binders and the premises the segment reads ---- *)
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (doc : Z) (t : PjTree.jv) (D : list (Z * Z))
  (Lam : list (Z * Z)) (peak cnt ran most : Z).
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (@CRT_sp1 regs).
#[local] Notation liveB := (crt_live (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md)
  (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (most := most)).
(* the Section's fx is named: a local FPState binder (fxk) is also an instance candidate *)
#[local] Notation QFB := (QF (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x)
  (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs)
  (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran)
  (most := most)).
#[local] Notation JB := (crt_at_J_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK)
  (L := B_prog_listing) (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x)
  (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs)
  (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran)
  (most := most)).
#[local] Notation XB := (crt_at_X_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK)
  (L := B_prog_listing) (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x)
  (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs)
  (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran)
  (most := most)).
#[local] Notation CFG := (crt_cfg (L := B_prog_listing) (PA := PA) (CRT_PC := CRT_PC_B)).

(* tcheck_round_trip_specX's entry premises (the contract text lib/A/PRH_FnCheck.v 0844ed8c0608:1240, :1248; Crt102Top
   discharges them from the text's) *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
(* the join: the J_B stretch, J (+0x348) .. the `ret` (row T8; Crt102TailB.crt102_tail_B
   discharges it at composition) *)
Hypothesis TAIL : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  JB fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_J_OFF_B rg memc mdc) QFB.

(* ---- the symbolic state at X (Crt102Kit.v's crt102rw_SH_entry, at the B' instance) ---- *)
Lemma cxb_SH_entry : forall (fxk : YK11.FPState) pc (Wc : world SEGS) memc rg F,
  getr rg 18 = w64 (shadow_addr F) -> 0 <= F -> F + 512 <= 2 ^ 47 ->
  (forall i, 0 <= i < 64 -> apresent (w_H Wc) memc (shadow_addr F + i)) ->
  st_ok_pi SEGS VAL (TEB regs rg []) (cxb_ssSH pc)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TEB regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk pc Wc memc rg F R18 HF0 HF HP.
set (E := TEB regs rg []).
assert (X18 : bv_unsigned (ew E (xr 18)) = shadow_addr F).
{ unfold E, xr. rewrite (te_cur regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
split; [|unfold sh_ok; apply Forall_nil].
apply (ts_st_ok (fx := fxk)).
all: try change (TEB regs rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 18) (shadow_addr F)); [exact X18 | unfold shadow_addr, SHADOW_OFF; lia
    | unfold shadow_addr, SHADOW_OFF; lia | | constructor].
  intros o Ho. apply (apresent_writable SEGS). apply HP. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X18.
  split; [|exact I]. unfold shadow_addr, SHADOW_OFF. lia.
Qed.

(* ---- THE WRITES OF X's RUN: the frame's shadow bytes 4 .. 22 (Crt102Kit.v's crt102rw_wr, its first half: X writes
   no spill word) ---- *)
Definition cxb_wr (F a : Z) : Prop := shadow_addr F + 4 <= a < shadow_addr F + 23.

Lemma cxb_nw_low : forall F a, 0 <= F -> 0 <= a < kLowMemEnd -> ~ cxb_wr F a.
Proof.
intros F a HF Ha Hw. pose proof (YM05.alloc_ceiling_val).
unfold cxb_wr, shadow_addr, SHADOW_OFF, kLowMemEnd in *; lia.
Qed.
Lemma cxb_nw_app : forall F a, 0 <= F -> F + 512 <= YM05.alloc_ceiling -> in_app a 1 -> a < YM05.alloc_ceiling ->
  ~ cxb_wr F a.
Proof.
intros F a HF HF2 Ha Hac Hw. pose proof (YM05.alloc_ceiling_val).
unfold cxb_wr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *; lia.
Qed.
Lemma cxb_nw_stack : forall F a, 0 <= F -> F + 512 <= YM05.alloc_ceiling -> YM05.alloc_ceiling <= a ->
  ~ cxb_wr F a.
Proof.
intros F a HF HF2 Ha Hw. pose proof (YM05.alloc_ceiling_val).
unfold cxb_wr, shadow_addr, SHADOW_OFF in *; lia.
Qed.

(* ---- the live state across X's run (Crt102Kit.v's crt102rw_live_run at the B' instance, its writes in cxb_wr); kb
   round: the run stores no wild trace, so the live state stays at its budget kbg, the journal at the run's WS ---- *)
Lemma cxb_live_run : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc {kbg : nat}
    {WS : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc' mdc' kj' WS -> YCbqGwild.wbudget [] kbg WS ->
  (forall xw : word, ~ cxb_wr (frame_addr lyc CRT_CID pos) (bv_unsigned xw) ->
     mrestrict (w_H Wc) memc' xw = mrestrict (w_H Wc) memc xw) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc') ->
  liveB kbg lyc Sc Hpc Wc memc' mdc' kj' pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc kbg WS HL HJ' HB' Hag HMN'.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH. clear HL.
destruct (Crt102KitB.cb4_ff B ARx ly S Hp W regs mem md LAWS _ _ _ _ _ _ _ _ HJ)
  as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (Crt102KitB.cb4_ff B ARx ly S Hp W regs mem md LAWS _ _ _ _ _ _ _ _ HJ')
  as (_ & _ & _ & _ & _ & Ffr' & Fsh').
pose proof HJ as (HARc & _).
set (F := frame_addr lyc CRT_CID pos) in *.
pose proof (Crt102KitB.cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Crt102KitB.cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE)
  as (Hd1 & Hd2 & Hd3 & Hd4).
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ cxb_wr F a -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. apply aview_eq_of. apply Hag. rewrite unsigned_lit_small by lia. exact Hn. }
assert (Kmb : forall a, 0 <= a < 2 ^ 64 -> ~ cxb_wr F a ->
  mbyte SEGS (mrestrict (w_H Wc) memc') a = mbyte SEGS (mrestrict (w_H Wc) memc) a).
{ intros a Ha Hn. unfold mbyte. rewrite (Hag (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn. }
assert (Kw : forall a, 0 <= a < 2 ^ 64 -> ~ cxb_wr F a ->
  writable_at SEGS (mrestrict (w_H Wc) memc) a -> writable_at SEGS (mrestrict (w_H Wc) memc') a).
{ intros a Ha Hn Hw. unfold writable_at, wview in *. rewrite (Hag (Z_to_bv 64 a)); [exact Hw|].
  rewrite unsigned_lit_small by lia. exact Hn. }
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity.
assert (Kblk : forall a k, In (a, k) Lamc -> 0 <= k /\ forall i, 0 <= i < k + 16 ->
  0 <= a - 16 + i < 2 ^ 64 /\ ~ cxb_wr F (a - 16 + i)).
{ intros a k Hk. pose proof (crt_side_ledger HSD) as HLED.
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc a k _ _ HLED Hk) as (Hk0 & Hab & _).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & Bapp & _).
  rewrite Hch16 in *.
  assert (Hrs : k + 16 <= req_size (k + 16)) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
  split; [exact Hk0|]. intros i Hi.
  split; [lia|]. apply (cxb_nw_app F _ ltac:(lia) ltac:(lia)); [|lia].
  apply (in_app_sub _ _ _ _ Bapp); lia. }
refine {| crt_live_journal := ex_intro _ WS (conj HJ' HB'); crt_live_side := _; crt_live_lam_perm := HPL;
          crt_live_blocks_perm := HPB;
          crt_live_dx_apart := HAP; crt_live_saved := _; crt_live_frame := _; crt_live_fspill := _;
          crt_live_copy_open := _; crt_live_copy_hull := _; crt_live_memnorm := HMN' |}.
{ pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK.
  pose proof (crt_side_room HSD) as HRL. pose proof (crt_side_arodata HSD) as HRO.
  pose proof (crt_side_doc HSD) as HDOC. pose proof (crt_side_doc_blocks HSD) as HDL.
  refine {| crt_side_ledger := _; crt_side_peak := HPK; crt_side_room := HRL; crt_side_arodata := _;
            crt_side_doc := _; crt_side_doc_blocks := HDL |}.
  { apply (prh_ledger_kept_aview B lyc Sc Hpc Wc memc lyc Sc Hpc Wc memc' Lamc peakc cntc SIZE_MAXZ ranc most ownc HLED).
    - intros a Ha. pose proof (@pa_segs_low _ _ PA a (crt_pst_img_B_cf a Ha)) as Hl.
      apply K; [unfold kLowMemEnd in Hl; lia|]. apply cxb_nw_low; [lia | exact Hl].
    - intros a k i Hk Hi. destruct (Kblk a k Hk) as (Hk0 & Hb). rewrite Hch16.
      destruct (Hb i ltac:(lia)) as (H1 & H2). apply K; assumption.
    - intros a k _ Hab. exact Hab.
    - apply Permutation_refl. }
  { intros a Hro Ho He. pose proof (@pa_segs_low _ _ PA a (Crt102KitB.cb4_ro_img a Hro)) as Hl.
    rewrite K; [exact (HRO a Hro Ho He) | unfold kLowMemEnd in Hl; lia | apply cxb_nw_low; [lia | exact Hl]]. }
  { apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') (prh_lin Lamc) doc D HDOC).
    intros y Hy.
    assert (Hyr : 0 <= y < 2 ^ 64 /\ ~ cxb_wr F y).
    { destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
      - split; [lia|]. apply (cxb_nw_app F y ltac:(lia) ltac:(lia)); [|lia]. apply (in_app_sub _ _ _ _ Hd3); lia.
      - unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
        destruct (Kblk b kb (HDL _ Hb)) as (Hk0 & Hbb).
        destruct (Hbb (y - (b - 16)) ltac:(lia)) as (H1 & H2).
        replace (b - 16 + (y - (b - 16))) with y in H1, H2 by lia. split; assumption. }
    split; [apply Kmb; apply Hyr | apply Kw; apply Hyr]. } }
{ intros j Hj k Hk. rewrite Kmb; [exact (HSV j Hj k Hk) | lia |].
  apply (cxb_nw_stack F _ ltac:(lia) ltac:(lia)); lia. }
{ pose proof (crt_frame_listed HFRM) as Hinf. pose proof (crt_frame_flag_word HFRM) as Hfl.
  refine {| crt_frame_listed := Hinf; crt_frame_flag_word := _; crt_frame_present := _ |}.
  - rewrite <- Hfl. apply ts_rdword_keep. intros j Hj. rewrite Crt102KitB.cb4_fb.
    apply K; [lia|]. apply (cxb_nw_app F _ ltac:(lia) ltac:(lia)); [|lia]. apply (in_app_sub _ _ _ _ Fb3); lia.
  - intros a Ha. rewrite Crt102KitB.cb4_fb in Ha. exact (proj1 (Ffr' a Ha)). }
{ intros k Hk. unfold CRT_SP_F in *. rewrite Kmb; [exact (HSPF k Hk) | lia |].
  apply (cxb_nw_stack F _ ltac:(lia) ltac:(lia)); lia. }
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HCR].
  intros y Hy. unfold CRT_OFF_COPY in Hy. unfold shadow_of_addr. apply K; [unfold SHADOW_OFF; lia|].
  intros Hw. unfold cxb_wr, shadow_addr, SHADOW_OFF in *. pose proof (Z.div_mod F 32 ltac:(lia)).
  assert (F / 8 + 28 <= y / 8) by (apply Z.div_le_lower_bound; lia). lia. }
{ intros s Hs. pose proof (YM05.alloc_ceiling_val).
  rewrite K; [exact (HCH s Hs) | unfold CRT_OFF_COPY, shadow_addr, SHADOW_OFF in *; lia |].
  intros Hw; unfold cxb_wr, CRT_OFF_COPY, shadow_addr, SHADOW_OFF in *; lia. }
Qed.

(* ---- a byte of a live harness block, or of a tree in the frame whose blocks are harness blocks, is application
   memory below alloc_ceiling, so X's run does not write it (Crt102Kit.v's crt102rw_lam_app / crt102rw_foot_nw at
   the B' instance) ---- *)
Lemma cxb_lam_app : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc a k y {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  In (a, k) Lamc -> a <= y < a + k -> 4096 <= y < YM05.alloc_ceiling /\ in_app y 1.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc a k y kbg HL Hk Hy.
destruct (crt_live_journal HL) as (? & (HARc & _) & _).
pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc a k _ _ HLED Hk) as (Hk0 & Hab & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & Bapp & _).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity. rewrite Hch16 in *.
assert (Hrs : k + 16 <= req_size (k + 16)) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
split; [lia|]. apply (in_app_sub _ _ _ _ Bapp); lia.
Qed.
Lemma cxb_foot_nw : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc D' p y {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (forall bk, In bk D' -> In bk Lamc) ->
  frame_addr lyc CRT_CID pos <= p -> p + 56 <= frame_addr lyc CRT_CID pos + 512 ->
  pj_footR p D' y -> 0 <= y < 2 ^ 64 /\ ~ cxb_wr (frame_addr lyc CRT_CID pos) y.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc D' p y kbg HL HD Hp1 Hp2 Hy.
destruct (crt_live_journal HL) as (WSj & HJ & HBj).
destruct (Crt102KitB.cb4_ff B ARx ly S Hp W regs mem md LAWS _ _ _ _ _ _ _ _ HJ)
  as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- split; [lia|]. apply cxb_nw_app; [lia | lia | apply (in_app_sub _ _ _ _ Fb3); lia | lia].
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  destruct (cxb_lam_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ b kb y HL (HD _ Hb) Hy) as (H1 & H2).
  split; [lia|]. apply cxb_nw_app; [lia | lia | exact H2 | lia].
Qed.

(* ======================================================================================================== *)
(* ---- X (+0x30c .. +0x348): the shared re-poison of back and v (f8 into the frame's shadow bytes 4 .. 10 and
   16 .. 22), then the join J_B (TAIL). crt_at_X_B is read by its fields, crt_at_J_B is built by its named literal:
   the run writes only the frame's shadow, so the live state, copy's freeable tree and its count arm cross it; the
   registers it does not write (all but a0) keep crt_bregs_B and s5 = r. ---- *)
Lemma cb_at_X_B : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  XB fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_X_OFF_B rg memc mdc) QFB.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r HX.
pose proof (crt_at_X_B_join HX) as HXJ.
pose proof (crt_at_J_B_live HXJ) as HL. pose proof (crt_at_J_B_frm_zero HXJ) as HFZ.
pose proof (crt_at_J_B_fregs HXJ) as HFK. pose proof (crt_at_J_B_bregs HXJ) as HBR.
pose proof (crt_at_J_B_ret HXJ) as R21. pose proof (crt_at_J_B_copy_fd HXJ) as HFD.
pose proof (crt_at_J_B_r0 HXJ) as Er0. pose proof (crt_at_J_B_count HXJ) as HCNT.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_lam_perm HL) as HPL.
pose proof (crt_live_memnorm HL) as HMN.
destruct (Crt102KitB.cb4_ff B ARx ly S Hp W regs mem md LAWS _ _ _ _ _ _ _ _ HJ)
  as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (crt_bregs_B_s2 HBR) as R18.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Crt102KitB.cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (cxb_SH_entry fxk (CRT_PC_B + CRT_X_OFF_B) Wc memc rg F R18 ltac:(lia) ltac:(lia)
  (fun i Hi => proj1 (Fsh i Hi))) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TEB regs rg [])) by apply te_env.
assert (X18 : bv_unsigned (ew (TEB regs rg []) (xr 18)) = shadow_addr F).
{ unfold xr. rewrite (te_cur regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
pose proof HMN as HPM.
pose (RUNTO := @Crt102Kit.crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WSj).
unfold crt_cfg.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (2 ^ 63, 2 ^ 63) (CRT_PC_B + CRT_J_OFF_B).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 18) (shadow_addr F)); [reflexivity | exact X18 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists CRT_CID, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite Crt102KitB.cb4_fb.
    change (512 / 8) with 64. fold F. lia. }
  apply awr_ok_nil. }
pmkst HS.
set (WSH := ss_mem (cxb_ssSH (CRT_PC_B + CRT_X_OFF_B))) in *.
assert (Hwr : forall a, in_wrange (TEB regs rg []) WSH a -> shadow_addr F + 4 <= a < shadow_addr F + 23).
{ intros a (rr & Hr & Ha). cbv [WSH cxb_ssSH ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ts_bv_some, X18 in Ha. lia. }
assert (Hag : forall xw : word, ~ cxb_wr F (bv_unsigned xw) ->
  mrestrict (w_H Wc) (ms_mem ms) xw = mrestrict (w_H Wc) memc xw).
{ intros xw Hn. apply HFr. intros Hw. apply Hn. exact (Hwr _ Hw). }
pose proof (cxb_live_run lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ pos Dc Lamc peakc cntc ownc ranc HL HJ HBj Hag
  HPM) as HL1.
assert (KR : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) rr = getr rg rr).
{ intros rr Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [cxb_keep HS |]). destruct Hr. }
clear HF HG.
lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
  change n with (CRT_PC_B + CRT_J_OFF_B) end.
apply (TAIL fxk lyc Sc Hpc Wc (ms_mem ms) _ kj pos Lamc peakc cntc ownc ranc Dc (ms_regs ms) r).
assert (HDc : forall bk, In bk Dc -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hbk. }
(* copy's footprint is application memory below the ceiling, so the re-poison kept it *)
assert (HAGc : pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) (pj_footR (F + CRT_OFF_COPY) Dc)).
{ intros y Hy.
  destruct (cxb_foot_nw _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dc (F + CRT_OFF_COPY) y HL HDc
    ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) Hy) as (Hy1 & Hy2).
  assert (E : mrestrict (w_H Wc) (ms_mem ms) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y)).
  { apply Hag. rewrite unsigned_lit_small by lia. exact Hy2. }
  split; [unfold mbyte; rewrite E; reflexivity|].
  intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
refine {| crt_at_J_B_live := HL1; crt_at_J_B_frm_zero := HFZ; crt_at_J_B_fregs := HFK; crt_at_J_B_bregs := _;
          crt_at_J_B_ret := _; crt_at_J_B_copy_fd := _; crt_at_J_B_r0 := Er0; crt_at_J_B_count := _ |}.
{ refine {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _;
            crt_bregs_B_s1 := _; crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _;
            crt_bregs_B_s7 := _; crt_bregs_B_s9 := _; crt_bregs_B_s11 := _ |}; rewrite !KR by (cbv; tauto).
  - exact (crt_bregs_B_sp HBR).
  - exact (crt_bregs_B_gp HBR).
  - exact (crt_bregs_B_tp HBR).
  - exact (crt_bregs_B_s0 HBR).
  - exact (crt_bregs_B_s1 HBR).
  - exact (crt_bregs_B_s2 HBR).
  - exact (crt_bregs_B_s4 HBR).
  - exact (crt_bregs_B_s3 HBR).
  - exact (crt_bregs_B_s7 HBR).
  - exact (crt_bregs_B_s9 HBR).
  - exact (crt_bregs_B_s11 HBR). }
{ rewrite KR by (cbv; tauto). exact R21. }
{ (* copy's freeable tree, through its order list: pj_fdR -> pj_foR, the frame lemma of pj_foR, pj_foR -> pj_fdR *)
  destruct (PRH_PjOrder.pj_fdR_foR SEGS _ _ _ _ _ HFD) as (F0 & HF0).
  exact (proj1 (PRH_PjOrder.pj_foR_fdR SEGS _ _ _ _ _ _
    (PRH_PjOrder.pj_foR_frame SEGS DOC_D (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc)
      (prh_lin Lamc) (F + CRT_OFF_COPY) Dc F0 HF0 (fun a k Hk => HDc (a, k) Hk) HAGc))). }
destruct HCNT as (cset & Hc03 & Hcm & [HC1 | (Hr0 & Hown & Hran & Hcnt & Hpos & HND & Htblk & (Fc & HFo & HFoe) &
  Hdep)]).
- exists cset. split; [exact Hc03|]. split; [exact Hcm|]. left. exact HC1.
- exists cset. split; [exact Hc03|]. split; [exact Hcm|]. right.
  split; [exact Hr0|]. split; [exact Hown|]. split; [exact Hran|]. split; [exact Hcnt|]. split; [exact Hpos|].
  split.
  { exact (pj_nodeR_frame SEGS (crt_tree_J (t := t)) (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms))
      (prh_lin Lamc) (F + CRT_OFF_COPY) Dc HND HAGc). }
  split; [exact Htblk|].
  split; [|exact Hdep].
  (* copy's free order: its footprint is untouched by the shadow stores (the same agreement as pj_fdR's) *)
  exists Fc. split; [|exact HFoe].
  exact (PRH_PjOrder.pj_foR_frame SEGS DOC_D (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc)
    (prh_lin Lamc) (F + CRT_OFF_COPY) Dc Fc HFo (fun a k Hk => HDc (a, k) Hk) HAGc).
Qed.

End g.
End f.
End xb.

Print Assumptions cb_at_X_B.
