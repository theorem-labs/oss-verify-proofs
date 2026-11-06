(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_parse's image-B walk (fuzz_preset asan-ubsan, B 0x862ec), the segment from the cut
   pjp_C2ok (+0x54, parse_value returned 0) to the cuts pjp_C3 (+0x74, the value is the whole text) and pjp_C2ref
   (+0x68, junk after the value), over lib/B/Prog/pj_parse_defs.v's statements.
   proves no function (kind: segment lemma).
   The code (listing slots of lib/B/Listing_prog.v, pc offsets from pj_parse's entry):
     +0x54 addi a0,sp,8   +0x58 jal skip_ws   +0x5c ld a0,8(sp)   +0x60 ld a1,16(sp)   +0x64 beq a0,a1,+0x84
     +0x68 (cut C2ref) ... ; +0x84 li a0,0   +0x88 j +0x74 (cut C3).
   HOW: two engine stretches over YCbqG's ajournal_x (YC80x / YC1fPx paj_run_tok_x), each a symbolic state seated
   fresh from the facts at its start (PvB_D.v's form): the first runs to the `jal skip_ws`, which the kit's tskip_ws_specX
   closes through YCbqGcallW.v's aj_call_xW_sp at callee window e1 = 32 (the cursor [sp1 + 8, sp1 + 32) is in
   pj_parse's own frame: fp_sub_x's fourth disjunct); the second reloads p and end and branches. Neither stretch
   stores, so the memory after each is the memory before it, byte for byte. What the call keeps: pjp_frame_kept_stmt
   (the frame, the caller window, the read-only view), the callee's journal (the tree's bytes: a node in a live
   allocator block or a live fake frame, the harness blocks D), the allocator laws at the return state (presence,
   writability, ownership, the block shadow law: out's block holds no hidden head) and pjp_g_vis (a fake frame's
   shadow hull).
   Position and memory: skip_ws's text (kit-oldpin preset-tree-at-2026-10-29T16-29-35Z.tsv (sha256 119dcd5524fb; internal record)) keeps the allocator state (S' = S), so the cut's
   run position pjp_pos rides through the call unchanged; the memory overlay's normal form rides through the call by
   its m-form keep (fpostWm) and through each stretch because the stretch stores nothing (pjm_mn).
   THE RE-HIDING MOVE AND THE HULL: the cut's journal is at wle' SEGS RZ_cf (pjp_invR, after parse_value), so both
   stretches are the runners over R at that relation (paj_run_xR / paj_run_to_xR / paj_branchR) and the segment
   concludes SRr'; skip_ws's text is a plain SRr, lifted into SRrG at wle' (YA0nH.SRr_SRrG) with its post's journal
   moved to wle' (YCbqG.ajournal_xwR_mono), and bound by YCbqGcallW.aj_call_xW_spR at wle'. The keep lemmas below are
   stated over any world relation R. skip_ws keeps the allocator state, so parse_value's hull use (the cut's) is the
   text's hull use at C3 (pj_parse_counts.v pjc_hull_used_pv) and C2ref's.
   THE OUTCOME OF AN INJECTED READING (the text's GUARDED conjunct): parse_value's (the cut's pjp_inj); an accepted
   document's events under the model's grant list are parse_value's at that list, then nothing or the refusal's HBulk.
   Section hypotheses (all statements of pj_parse_defs.v or the kit, none of this file): pjp_texts (skip_ws's text is
   the one used), pjp_frame_kept_stmt, pjp_seg_C3, pjp_seg_C2ref, AR_laws_x SEGS B ARx cf_head, pjp_g_vis, and the glue
   pjp_g_node_fd / _depth / _run / _fail_in / _norefuse / _calls / _fail_after / _rest / _ab_hbl.
   Numerals: 8 / 16 / 24 / 32 / 48 / 56 / 64 are LENGTH (slots, cursor, window, frame, node); 2 ^ k LENGTH; every pc
   offset is DERIVED (pj_parse_defs.v's PJP_* and PJP_PC + 92, the return site of `jal skip_ws`). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis YGcfHeadSh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnParse PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_parse_defs pj_parse_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_Frees.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require pj_parse_counts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Existing Instance prh_img_B.
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the two seated symbolic states ---- *)
(* the return site of `jal skip_ws` (+0x5c) *)
Definition PJP2_RET : Z := PJP_PC + 92.
(* no shadow check in either stretch, no shadow entry: the span the entries may name is the point (0, 0) *)
Definition PJP2_Bx : sv := SLit SHADOW_OFF.
Definition PJP2_Bspan : Z * Z := (0, 0).
(* stretch 1 (+0x54 .. the `jal skip_ws`): every register its own atom, no memory region (it loads and stores
   nothing) *)
Definition pjp2_ss1 : sstate := mkSS PJP_C2OK sr_atoms [] None (mkFacts [] [] []).
(* stretch 2 (+0x5c .. the cuts): the cursor's p and end words at sp + 8 / sp + 16 (atom 2 = sp), atoms 32 = p after
   the white space, 33 = end; no write window *)
Definition pjp2_reg : YP09.region :=
  YP09.mkRegion (Some 2%nat) 8 24 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0))].
Definition pjp2_ss2 : sstate := mkSS PJP2_RET sr_atoms [pjp2_reg] None (mkFacts [] [] []).

Lemma pjp2_fs8 : forall cid, 56 <= fs_frame_bytes cid -> fs_frame_bytes cid mod 8 = 0.
Proof.
intros cid H. unfold fs_frame_bytes in *. destruct (Z_lt_le_dec cid 0) as [Hn|Hp].
- exfalso. replace cid with (- (- cid)) in H by lia. rewrite Z.shiftl_opp_r, Z.shiftr_div_pow2 in H by lia.
  assert (2 <= 2 ^ (- cid)) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
  assert (64 / 2 ^ (- cid) <= 64 / 2) by (apply Z.div_le_compat_l; lia). change (64 / 2) with 32 in *. lia.
- rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by ring. apply Z_mod_mult.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARx).
#[local] Notation AJR R := (ajournal_xR (SK := SK) SEGS B prh_pst ARx R).

(* ---- a stretch that stores nothing leaves every byte: the predicates ride along ---- *)
Section m.
Variable H : word -> bool.
Variables m m' : word -> option byte.
Hypothesis Hm : forall x, m' x = m x.
Lemma pjm_mb : forall a, mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof. intros a. unfold mbyte, mrestrict. cbv beta. rewrite Hm. reflexivity. Qed.
Lemma pjm_av : forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros a. unfold aview. rewrite pjm_mb. reflexivity. Qed.
Lemma pjm_val : forall a n v, val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof. intros a n v Hv. apply (pj_valR_frame SEGS (mrestrict H m) (mrestrict H m') a n v Hv). intros x _. apply pjm_mb. Qed.
Lemma pjm_garr : forall a l, garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof. intros a l Hg. apply (garr8R_frame SEGS (mrestrict H m) (mrestrict H m') a l Hg). intros x _. apply pjm_mb. Qed.
Lemma pjm_pres : forall a, apresent H m a -> apresent H m' a.
Proof. intros a (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite Hm. exact Hb. Qed.
Lemma pjm_wr : forall a, writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H m') a.
Proof. intros a Hw. unfold writable_at, wview, mrestrict in *. cbv beta in *. rewrite Hm. exact Hw. Qed.
Lemma pjm_ra : forall a n, range_addressable (aview SEGS H m) SHADOW_OFF a n ->
  range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof. intros a n Hr. apply (range_addressable_agree (aview SEGS H m) (aview SEGS H m') SHADOW_OFF a n); [|exact Hr].
intros x _. apply pjm_av. Qed.
Lemma pjm_hull : forall a n, shadow_hull_vis (aview SEGS H m) a n -> shadow_hull_vis (aview SEGS H m') a n.
Proof. intros a n Hh s Hs. rewrite pjm_av. exact (Hh s Hs). Qed.
Lemma pjm_rod : arodata_okP SEGS RLO RHI B (aview SEGS H m) -> arodata_okP SEGS RLO RHI B (aview SEGS H m').
Proof. intros Hr a H1 H2 H3. rewrite pjm_av. exact (Hr a H1 H2 H3). Qed.
Lemma pjm_in_ok : forall q text len p d tb, pj_in_okR SEGS (mrestrict H m) q text len p d tb ->
  pj_in_okR SEGS (mrestrict H m') q text len p d tb.
Proof.
intros q text len p d tb (V1 & V2 & V3 & Hrw & R).
refine (conj (pjm_val _ _ _ V1) (conj (pjm_val _ _ _ V2) (conj (pjm_val _ _ _ V3) (conj _ _)))).
- intros x Hx. apply pjm_wr. exact (Hrw x Hx).
- destruct R as (R1 & R2 & R3 & R4 & R5 & Hg & R6). repeat (split; [assumption|]).
  split; [exact (pjm_garr _ _ Hg) | exact R6].
Qed.
(* the memory overlay's normal form, across a stretch that stores nothing *)
Lemma pjm_mn : YAkMemnorm.memnorm SEGS m -> YAkMemnorm.memnorm SEGS m'.
Proof.
unfold YAkMemnorm.memnorm. intros [H1 H2].
split; intros a b E; rewrite Hm in E; [exact (H1 a b E) | exact (H2 a b E)].
Qed.
End m.

Lemma pjm_src : forall (W : world SEGS) m m' p l, (forall x, m' x = m x) ->
  src_rd (PA := PA) W m p l -> src_rd (PA := PA) W m' p l.
Proof.
intros W m m' p l Hm (Hg & H4 & Hc & Ham & Hra & Hh). unfold bytes_at in Hg.
refine (conj (pjm_garr _ _ _ Hm _ _ Hg) (conj H4 (conj Hc (conj Ham (conj (pjm_ra _ _ _ Hm _ _ Hra) _))))).
intros Hn. exact (pjm_hull _ _ _ Hm _ _ (Hh Hn)).
Qed.

Lemma pjm_ledger : forall ly S Hp (W : world SEGS) m m' Lam peak cnt fail ran most own, (forall x, m' x = m x) ->
  prh_ledger (PA := PA) B ly S Hp W m Lam peak cnt fail ran most own ->
  prh_ledger (PA := PA) B ly S Hp W m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W m m' Lam peak cnt fail ran most own Hm HL.
apply (prh_ledger_kept B ly S Hp W m ly S Hp W m' Lam peak cnt fail ran most own HL).
- intros a _. exact (pjm_mb (w_H W) m m' Hm a).
- intros a k i _ _. exact (pjm_mb (w_H W) m m' Hm (a - cf_head + i)).
- intros a k _ Hin. exact Hin.
- apply Permutation_refl.
Qed.

(* pjp_invR across a stretch that stores nothing and keeps sp, s0 and the callee-saved registers, at any world
   relation R *)
Lemma pjm_inv {R : world SEGS -> world SEGS -> Prop} : forall en Sb fy ly S Hp W regs mem md k ly' S' Hp' regs' mem'
  md' k',
  pjp_invR (fx := fx) B ARx R en Sb fy ly S Hp W regs mem md k ->
  AJR R (STK_pj_parse + je_d en) (je_sp0 en + je_d en) [(je_out en, je_out en + 56)]
    (je_ly en) Sb (je_Hp en) (je_W en) (je_mem en) (je_md en) [] ly' S' Hp' W mem' md' k' ->
  (forall x, mem' x = mem x) ->
  spZ regs' = spZ regs -> getr regs' 8 = getr regs 8 -> (forall r, In r PJP_KEPT -> getr regs' r = getr regs r) ->
  pjp_invR (fx := fx) B ARx R en Sb fy ly' S' Hp' W regs' mem' md' k'.
Proof.
intros en Sb fy ly S Hp W regs mem md k ly' S' Hp' regs' mem' md' k' HI HJ Hm Hsp H8 HK.
destruct HI as (Z1 & Z2 & _ & Hwin & Hsp1 & Hra & Hs0 & H8' & HK' & Hpres & Hra24 & Hrod & Hmn).
split; [exact Z1|]. split; [exact Z2|]. split; [exact HJ|].
split; [intros a Ha; rewrite (pjm_av _ _ _ Hm); exact (Hwin a Ha)|].
split; [rewrite Hsp; exact Hsp1|].
split; [exact (pjm_val _ _ _ Hm _ _ _ Hra)|].
split; [exact (pjm_val _ _ _ Hm _ _ _ Hs0)|].
split; [rewrite H8; exact H8'|].
split; [intros r Hr; rewrite (HK r Hr); exact (HK' r Hr)|].
split; [intros a Ha; exact (pjm_pres _ _ _ Hm a (Hpres a Ha))|].
split; [exact (pjm_ra _ _ _ Hm _ _ Hra24)|].
split; [exact (pjm_rod _ _ _ Hm Hrod) | exact (pjm_mn _ _ Hm Hmn)].
Qed.

(* the registers a call keeps (aregs_preserved): sp, s0 and pj_parse's untouched callee-saved registers *)
Lemma pjp2_kept_regs : forall regs regs', aregs_preserved regs regs' ->
  forall r, In r ((2%bv : bv 5) :: (8%bv : bv 5) :: PJP_KEPT) -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. cbv [PJP_KEPT In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [Hr | Hr] | False => destruct Hr | _ = _ => subst r end;
lazymatch goal with |- getr _ ?x = _ =>
  let z := eval vm_compute in (bv_unsigned x) in exact (HP z ltac:(unfold acallee_saved; lia)) end.
Qed.

(* out's facts and the tree, across a stretch that stores nothing *)
Lemma pjm_out : forall en ly S Lam (W : world SEGS) m m', (forall x, m' x = m x) ->
  pjp_out_ok B en ly S Lam W m -> pjp_out_ok B en ly S Lam W m'.
Proof.
intros en ly S Lam W m m' Hm (H1 & H2 & H3 & H4 & (Hal & Hrw) & H6 & H7 & H8 & H9).
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj (conj Hal _) (conj H6 (conj H7
  (conj (pjm_ra _ _ _ Hm _ _ H8) (pjm_hull _ _ _ Hm _ _ H9))))))))).
intros x Hx. exact (pjm_wr _ _ _ Hm x (Hrw x Hx)).
Qed.
Lemma pjm_node : forall (W : world SEGS) m m' lblk p t D, (forall x, m' x = m x) ->
  pj_nodeR SEGS (rdW W m) lblk p t D -> pj_nodeR SEGS (rdW W m') lblk p t D.
Proof.
intros W m m' lblk p t D Hm H. apply (pj_nodeR_frame SEGS t _ _ lblk p D H).
intros x _. split; [exact (pjm_mb _ _ _ Hm x) | exact (pjm_wr _ _ _ Hm x)].
Qed.
(* pj_free's order list of a tree, across a stretch that stores nothing *)
Lemma pjm_fo : forall (W : world SEGS) m m' lblk n p D F, (forall x, m' x = m x) ->
  pj_foR SEGS (rdW W m) lblk n p D F -> pj_foR SEGS (rdW W m') lblk n p D F.
Proof.
intros W m m' lblk n p D F Hm H. apply (pj_foR_frame SEGS n _ _ lblk lblk p D F H).
- exact (pj_foR_lblk SEGS _ _ _ _ _ _ H).
- intros x _. split; [exact (pjm_mb _ _ _ Hm x) | exact (pjm_wr _ _ _ Hm x)].
Qed.
(* the tree's capacity words (CAP, pj_ncapR), across a stretch that stores nothing (PvB_Frees.v pvf_ncap_ext) *)
Lemma pjm_ncap : forall (W : world SEGS) m m' p t, (forall x, m' x = m x) ->
  pj_ncapR SEGS (rdW W m) p t -> pj_ncapR SEGS (rdW W m') p t.
Proof.
intros W m m' p t Hm H. apply (PvB_Frees.pvf_ncap_ext SEGS t (rdW W m) (rdW W m') p); [|exact H].
intros x. exact (pjm_mb (w_H W) m m' Hm x).
Qed.

(* the code numbers the segment needs (computed from the listing and prh_img_B; no number typed) *)
Lemma pjp2_stk : 0 <= @STK_skip_ws prh_img_B /\ @STK_skip_ws prh_img_B + 48 <= @STK_pj_parse prh_img_B.
Proof.
assert (H : ((0 <=? @STK_skip_ws prh_img_B) && (@STK_skip_ws prh_img_B + 48 <=? @STK_pj_parse prh_img_B))%bool = true)
  by (vm_compute; reflexivity).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* ---- the segment's Section hypotheses: the callee texts, the frame keep, the two later segments; then the kit's
   allocator laws, the MARKED shadow-visibility facts and the pure glue (pj_parse_defs.v) ---- *)
Variable CTX0 : list (list Z).
Variable CW : list (list Z).
Hypothesis TEXTS : pjp_texts B ARx CTX0 CW.
Hypothesis KEPT : pjp_frame_kept_stmt B ARx.
Hypothesis SEG3 : pjp_seg_C3 B ARx CTX0 CW.
Hypothesis SEG2R : pjp_seg_C2ref B ARx CTX0 CW.
(* CFHEAD-16, the walk's Section hypothesis (PRH_Base.v prh_head16; reflexivity at CfParams_preset): the tree's
   free order in parse_value's post is stated under it *)
Hypothesis HH : prh_head16.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VIS : pjp_g_vis B ARx.
Hypothesis G_depth : pjp_g_depth.
Hypothesis G_run : pjp_g_run.
Hypothesis G_fail_in : pjp_g_fail_in.
Hypothesis G_norefuse : pjp_g_norefuse.
Hypothesis G_calls : pjp_g_calls.
Hypothesis G_fail_after : pjp_g_fail_after.
Hypothesis G_rest : pjp_g_rest.
Hypothesis G_ab_hbl : pjp_g_ab_hbl.

(* a block that is not a harness block holds no hidden head: every head of Hp is the base of a harness block, and
   blocks are pairwise apart (alx_blocks) *)
Lemma pjp2_nohead : forall ly S Hp W mem md Lam peak cnt fail ran most own b m,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) Lam ->
  forall h, In h Hp -> ~ (b <= h < b + req_size m).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hb Hn h Hh Hr.
pose proof HLED as HF. apply prh_ledger_blocks in HF. pose proof HLED as HP. apply prh_ledger_heads in HP.
clear HLED.
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a k] & Eh & Hin). cbn [fst] in Eh. subst h.
destruct (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hb) as (_ & _ & _ & _ & _ & Hpw).
pose proof cf_head_nonneg as Hc0.
destruct (Z.eq_dec b (a - cf_head)) as [E1|N1]; [destruct (Z.eq_dec m (k + cf_head)) as [E2|N2]|].
- apply Hn. replace (b + cf_head) with a by lia. replace (m - cf_head) with k by lia. exact Hin.
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E; injection E as _ E; exact (N2 E)).
  destruct (in_split_2 (b, m) (a - cf_head, k + cf_head) (ablocks B ly S) Hb Hab Hne) as (l1 & l2 & l3 & El).
  assert (HZ : zdisjoint (b, req_size m) (a - cf_head, req_size (k + cf_head))).
  { apply (pairwise_zdisjoint_split _ _ _ Hpw).
    exists (map (fun b0 => (fst b0, req_size (snd b0))) l1), (map (fun b0 => (fst b0, req_size (snd b0))) l2),
      (map (fun b0 => (fst b0, req_size (snd b0))) l3).
    destruct El as [El | El]; rewrite El; rewrite map_app; cbn [map fst snd]; rewrite map_app; cbn [map fst snd];
      [left | right]; reflexivity. }
  pose proof (req_size_pos (k + @cf_head cp) ltac:(lia)) as [R1 _]. unfold zdisjoint in HZ. cbn [fst snd] in HZ. lia.
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E; injection E as E _; exact (N1 E)).
  destruct (in_split_2 (b, m) (a - cf_head, k + cf_head) (ablocks B ly S) Hb Hab Hne) as (l1 & l2 & l3 & El).
  assert (HZ : zdisjoint (b, req_size m) (a - cf_head, req_size (k + cf_head))).
  { apply (pairwise_zdisjoint_split _ _ _ Hpw).
    exists (map (fun b0 => (fst b0, req_size (snd b0))) l1), (map (fun b0 => (fst b0, req_size (snd b0))) l2),
      (map (fun b0 => (fst b0, req_size (snd b0))) l3).
    destruct El as [El | El]; rewrite El; rewrite map_app; cbn [map fst snd]; rewrite map_app; cbn [map fst snd];
      [left | right]; reflexivity. }
  pose proof (req_size_pos (k + @cf_head cp) ltac:(lia)) as [R1 _]. unfold zdisjoint in HZ. cbn [fst snd] in HZ. lia.
Qed.

(* ---- WHAT THE CALL KEEPS of out's facts (skip_ws keeps the allocator blocks and the ledger list): its place, its
   writability and ownership by the laws at the return state, its shadow by the block shadow law (out's block holds no
   hidden head) or, in a caller's fake frame, by the callee journal's frame clause and pjp_g_vis' frame hull ---- *)
Lemma pjp2_out_kept {R : world SEGS -> world SEGS -> Prop} : forall en ly S Hp W mem md Lam ly2 S2 Hp2 W2 mem2 md2
  STK1 sp FP1 k1 peak cnt fail ran most own,
  pjp_out_ok B en ly S Lam W mem ->
  AJR R STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ARx ly S Hp W mem md ->
  (forall x, inFP FP1 x -> YM05.alloc_ceiling <= x) ->
  ablocks B ly2 S2 = ablocks B ly S ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam peak cnt fail ran most own ->
  pjp_out_ok B en ly2 S2 Lam W2 mem2.
Proof.
intros en ly S Hp W mem md Lam ly2 S2 Hp2 W2 mem2 md2 STK1 sp FP1 k1 peak cnt fail ran most own HO HJ HAR HFP Eab HL2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HO as (H4096 & Hceil & Hplace & Hapart & (Hal8 & _) & Hamr & _ & Hra & _).
destruct HJ as (HAR2 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & J4 & _).
destruct Hplace as [(b & m & Hbm & HnL & Hb & Hm) | (cid & pos & Hcp & Hf1 & Hf2)].
- (* out in a live allocator block that is no harness block *)
  assert (Hbm2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Eab; exact Hbm).
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hbm2) as (_ & _ & _ & _ & Hbown & _).
  pose proof (req_size_pos m ltac:(lia)) as [_ Rm].
  destruct (alx_shadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hbm2
    (pjp2_nohead ly2 S2 Hp2 W2 mem2 md2 Lam peak cnt fail ran most own b m HAR2 HL2 Hbm2 HnL)) as [Hbs Hbh].
  split; [exact H4096|]. split; [exact Hceil|].
  split; [left; exists b, m; auto|].
  split; [exact Hapart|].
  split; [split; [exact Hal8 | intros x Hx; apply (apresent_writable SEGS); exact (proj1 (Hbown x ltac:(lia)))]|].
  split; [exact Hamr|].
  split; [intros a Ha; exact (proj2 (Hbown a ltac:(lia)))|].
  split; [exact (block_shadow_range _ SHADOW_OFF b (req_size m) (je_out en) 56 Hbs ltac:(lia) ltac:(lia))|].
  exact (shadow_hull_vis_sub_cf _ b (req_size m) (je_out en) 56 Hbh ltac:(lia) ltac:(lia)).
- (* out in a live fake frame of a caller *)
  assert (Hcp2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; exact Hcp).
  assert (Efa : frame_addr ly2 cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (Hf0 & Hfc & Hfapp).
  destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (Hfal & _).
  destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hcp2) as (_ & _ & Hfown & _).
  rewrite Efa in Hfown.
  destruct VIS as (VF & _ & _).
  pose proof (VF ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hcp2) as Hfh. rewrite Efa in Hfh.
  split; [exact H4096|]. split; [exact Hceil|].
  split; [right; exists cid, pos; rewrite Efa; auto|].
  split; [exact Hapart|].
  split; [split; [exact Hal8 | intros x Hx; apply (apresent_writable SEGS); exact (proj1 (Hfown x ltac:(lia)))]|].
  split; [exact Hamr|].
  split; [intros a Ha; exact (proj2 (Hfown a ltac:(lia)))|].
  split.
  + eapply range_addressable_agree; [|exact Hra]. intros x Hx.
    apply (J4 cid pos); [exact Hcp | right | ].
    * unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
      pose proof (pjp2_fs8 cid ltac:(lia)) as Hfs8.
      assert (Hfa8 : frame_addr ly cid pos mod 8 = 0) by lia.
      lia.
    * intros Hin. pose proof (HFP _ Hin) as Hc. unfold shadow_of_addr in Hc. unfold SHADOW_OFF in Hc. lia.
  + exact (shadow_hull_vis_sub_cf _ _ _ (je_out en) 56 Hfh ltac:(lia) ltac:(lia)).
Qed.

(* ---- WHAT THE CALL KEEPS of the tree's footprint: its bytes (out's node in a live block or fake frame, the harness
   blocks D) by the callee journal's block and frame clauses (all below alloc_ceiling, the callee writes only at or
   above it), their writability by the laws at the return state ---- *)
Lemma pjp2_foot_kept {R : world SEGS -> world SEGS -> Prop} : forall en ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 STK1
    sp FP1 k1 Lam peak cnt fail ran most own D,
  pjp_out_ok B en ly S Lam W mem ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> (forall b, In b D -> In b Lam) ->
  AJR R STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ARx ly S Hp W mem md ->
  (forall x, inFP FP1 x -> YM05.alloc_ceiling <= x) ->
  ablocks B ly2 S2 = ablocks B ly S ->
  pj_agreeR SEGS (rdW W mem) (rdW W2 mem2) (pj_footR (je_out en) D).
Proof.
intros en ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 STK1 sp FP1 k1 Lam peak cnt fail ran most own D HO HL HDL HJ HAR
  HFP Eab.
destruct HO as (H4096 & Hceil & Hplace & _).
pose proof HL as HLF. apply prh_ledger_blocks in HLF. clear HL.
destruct HJ as (HAR2 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & J2 & _ & J4 & _).
assert (KBL : forall p n x, In (p, n) (ablocks B ly S) -> p <= x < p + req_size n ->
  mbyte SEGS (rdW W2 mem2) x = mbyte SEGS (rdW W mem) x /\
  (writable_at SEGS (rdW W mem) x -> writable_at SEGS (rdW W2 mem2) x)).
{ intros p n x Hin Hx.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md p n HAR Hin) as (_ & _ & Hpc & _).
  assert (Hin2 : In (p, n) (ablocks B ly2 S2)) by (rewrite Eab; exact Hin).
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 p n HAR2 Hin2) as (_ & _ & _ & _ & Hby & _).
  split.
  - apply (mbyte_of_aview SEGS). replace x with (p + (x - p)) by lia.
    apply (J2 p n (x - p) Hin Hin2 ltac:(lia)). intros Hf. pose proof (HFP _ Hf). lia.
  - intros _. apply (apresent_writable SEGS). exact (proj1 (Hby x Hx)). }
assert (KFR : forall cid pos x, In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid ->
  mbyte SEGS (rdW W2 mem2) x = mbyte SEGS (rdW W mem) x /\
  (writable_at SEGS (rdW W mem) x -> writable_at SEGS (rdW W2 mem2) x)).
{ intros cid pos x Hcp Hx.
  assert (Hcp2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; exact Hcp).
  assert (Efa : frame_addr ly2 cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (_ & Hfc & _).
  destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hcp2) as (_ & _ & Hfb & _).
  rewrite Efa in Hfb.
  split.
  - apply (mbyte_of_aview SEGS). apply (J4 cid pos x Hcp); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia |].
    intros Hf. pose proof (HFP _ Hf). lia.
  - intros _. apply (apresent_writable SEGS). exact (proj1 (Hfb x Hx)). }
intros x [Hx | (b0 & Hb0 & Hhx)].
- destruct Hplace as [(b & m & Hbm & _ & Hb & Hm) | (cid & pos & Hcp & Hf1 & Hf2)].
  + pose proof (req_size_pos m ltac:(lia)) as [_ Rm]. apply (KBL b m x Hbm). lia.
  + apply (KFR cid pos x Hcp). lia.
- destruct b0 as [a k]. unfold pj_holdsR in Hhx. cbn [fst snd] in Hhx.
  destruct (proj1 (Forall_forall _ _) HLF (a, k) (HDL _ Hb0)) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  pose proof (@cf_head_nonneg cp) as Hc0. pose proof (req_size_pos (k + @cf_head cp) ltac:(lia)) as [_ Rk].
  apply (KBL (a - cf_head) (k + cf_head) x Hab). lia.
Qed.

(* ... and so the tree (pj_nodeR) and its free order list (pj_foR) *)
Lemma pjp2_node_kept {R : world SEGS -> world SEGS -> Prop} : forall en ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 STK1
    sp FP1 k1 Lam peak cnt fail ran most own t D,
  pjp_out_ok B en ly S Lam W mem ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> (forall b, In b D -> In b Lam) ->
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam) (je_out en) t D ->
  AJR R STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ARx ly S Hp W mem md ->
  (forall x, inFP FP1 x -> YM05.alloc_ceiling <= x) ->
  ablocks B ly2 S2 = ablocks B ly S ->
  pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam) (je_out en) t D.
Proof.
intros en ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 STK1 sp FP1 k1 Lam peak cnt fail ran most own t D HO HL HDL HN HJ HAR
  HFP Eab.
exact (pj_nodeR_frame SEGS t _ _ (prh_lin Lam) (je_out en) D HN
  (pjp2_foot_kept en ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 STK1 sp FP1 k1 Lam peak cnt fail ran most own D
     HO HL HDL HJ HAR HFP Eab)).
Qed.

Lemma pjp2_fo_kept {R : world SEGS -> world SEGS -> Prop} : forall en ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 STK1 sp
    FP1 k1 Lam peak cnt fail ran most own n D F,
  pjp_out_ok B en ly S Lam W mem ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> (forall b, In b D -> In b Lam) ->
  pj_foR SEGS (rdW W mem) (prh_lin Lam) n (je_out en) D F ->
  AJR R STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ARx ly S Hp W mem md ->
  (forall x, inFP FP1 x -> YM05.alloc_ceiling <= x) ->
  ablocks B ly2 S2 = ablocks B ly S ->
  pj_foR SEGS (rdW W2 mem2) (prh_lin Lam) n (je_out en) D F.
Proof.
intros en ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 STK1 sp FP1 k1 Lam peak cnt fail ran most own n D F HO HL HDL HF HJ
  HAR HFP Eab.
apply (pj_foR_frame SEGS n _ _ (prh_lin Lam) (prh_lin Lam) (je_out en) D F HF).
- exact (pj_foR_lblk SEGS _ _ _ _ _ _ HF).
- exact (pjp2_foot_kept en ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 STK1 sp FP1 k1 Lam peak cnt fail ran most own D
    HO HL HDL HJ HAR HFP Eab).
Qed.

(* ... and the tree's capacity words (PvB_Frees.v pvf_ncap_frame over the same footprint) *)
Lemma pjp2_ncap_kept {R : world SEGS -> world SEGS -> Prop} : forall en ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 STK1
    sp FP1 k1 Lam peak cnt fail ran most own t D,
  pjp_out_ok B en ly S Lam W mem ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> (forall b, In b D -> In b Lam) ->
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam) (je_out en) t D ->
  pj_ncapR SEGS (rdW W mem) (je_out en) t ->
  AJR R STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ARx ly S Hp W mem md ->
  (forall x, inFP FP1 x -> YM05.alloc_ceiling <= x) ->
  ablocks B ly2 S2 = ablocks B ly S ->
  pj_ncapR SEGS (rdW W2 mem2) (je_out en) t.
Proof.
intros en ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 STK1 sp FP1 k1 Lam peak cnt fail ran most own t D HO HL HDL HN HC HJ
  HAR HFP Eab.
exact (PvB_Frees.pvf_ncap_frame SEGS t (w_H W) mem (rdW W2 mem2) (prh_lin Lam) (je_out en) D HN
  (pjp2_foot_kept en ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 STK1 sp FP1 k1 Lam peak cnt fail ran most own D
     HO HL HDL HJ HAR HFP Eab) HC).
Qed.

Ltac pjp2_in := cbn [In PJP_KEPT]; repeat (first [left; reflexivity | right]).

(* ---- THE SEGMENT ---- *)
Theorem pjp_seg_C2ok_holds : pjp_seg_C2ok B ARx CTX0 CW.
Proof.
intros en Sb fy ly S Hp W regs mem md k HPRE HWB HC.
destruct TEXTS as (_ & SKIPWS & _ & _).
destruct HC as (HINV & HROOM & HHUSE & ok & t & r & tr & D & Lam' & peak' & cnt' & fail' & ran' & HPV & HPOSPV &
  HOUTC & HCUR & HNODE & HNCAP & HOUT & HTXT & HTIE & HINJ).
pose proof HINV as (HFZ & HFK & HJ & HWIN0 & Hsp & Hra & Hs0 & H8 & HKP & Hpres & HRA24 & HROD & HMN).
pose proof HPRE as (HFPRE & HCLO & HDW1 & HDW2 & HROOM0 & HFZ0 & H10 & H11 & H12 & Hlen & HSRC0 & HHOME0 & HMAX &
  HFWIN & HSLOT & Hout & HLAM & HTXA & HLED0 & HCNT & HRQ & HBB & HFRB & HMN0 & HPKS & HPK24 & HTCEIL & HRQM & HHB0).
pose proof HFPRE as (HAFN & HROD0 & Hstkhi & _ & _).
pose proof HAFN as (HAR0 & Hrok & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPV as ((okr & Hjv) & HLED & HLM & HBM).
pose proof HLM as (Hoks & Hcnt' & Hfa' & HPL & HPD & HND & Hpk').
pose proof HBM as (Hnew & HPab & HPfr & Hhp).
pose proof HJ as (HARc & Hly & _).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof pjp2_stk as (HSK0 & HSK48).
pose proof (@cf_head_nonneg cp) as Hc0.
assert (Esp1 : je_sp1 en = spZ (je_regs en) - 48) by reflexivity.
assert (Esp0 : je_sp0 en = spZ (je_regs en)) by reflexivity.
assert (Hsp1c : YM05.alloc_ceiling + STK_skip_ws <= je_sp1 en) by lia.
assert (HFP1 : forall x, inFP [(je_sp1 en + 8, je_sp1 en + 8 + 8)] x -> YM05.alloc_ceiling <= x).
{ intros x (r0 & [<- | []] & Hr0). cbn [fst snd] in Hr0. lia. }
assert (HDL : forall b, In b D -> In b Lam').
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hb. }
assert (Erest : rest_atR (je_tl en) (je_t0 en) (je_t0 en + je_len en - Z.of_nat (length r)) = r).
{ destruct (G_rest (je_tl en) ok t r tr okr (je_t0 en) Hjv) as [_ E']. rewrite <- Hlen. exact E'. }
pose proof HCUR as (_ & _ & _ & _ & _ & Ht00 & Ht62 & Hp0r & _).
(* ---- stretch 1 (+0x54 .. the `jal skip_ws`): a0 := sp + 8 ---- *)
set (E := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EL : forall n (r0 : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r0 -> ew E n = getr regs r0).
{ intros n r0 Hn Hr0. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r0 Hr0). }
assert (HAE : env_agree 32 (Ereg regs []) E) by (unfold E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi (fx := fy) SEGS VAL E pjp2_ss1
  (restrict (w_H W) (@YK11.mkst fy regs (Z_to_bv 64 (BASE + PJP_C2OK)) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pjp2_ss1. apply (pa_entry_st_ok_full (fx := fy)).
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - cbn. repeat split. }
assert (SHOK : sh_ok SEGS PJP2_Bx [] E (mrestrict (w_H W) mem)) by exact (Forall_nil _).
(* the cut's journal is at wle' SEGS RZ_cf: the stretches are the runners over that relation, the goal SRrG at it *)
pose (RUN := paj_run_xR (fx := fy) (SK := SK) (PL := PL_prog_B) (PI := PA) B prh_pst ARx LAWS
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (RUNTO := paj_run_to_xR (fx := fy) (SK := SK) (PL := PL_prog_B) (PI := PA) B prh_pst ARx LAWS
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (BR := paj_branchR (fx := fy) (PI := PA) (wle' SEGS YGcfRehidePost.RZ_cf)).
unfold pjp_cfg, SRr'.
paj_run_tok_xR RUN HS HJ SHOK PJP2_Bspan.
{ intros a (r0 & Hr0 & _). unfold pjp2_ss1 in Hr0. cbn in Hr0. destruct Hr0. }
(* the stretch stored nothing *)
assert (Hm1 : forall x, ms_mem ms x = mem x).
{ intros x. apply HF. intros (r0 & Hr0 & _). unfold pjp2_ss1 in Hr0. cbn in Hr0. exact Hr0. }
pose proof HJ as (HAR1 & _).
(* the registers at the call: a0 = sp + 8, ra = the return site, the rest kept *)
pose proof (regs_kept_of_st_ok SEGS E _ (restrict (w_H W) ms) regs [] ((2%bv : bv 5) :: (8%bv : bv 5) :: PJP_KEPT)
  HS HAE ltac:(vm_compute; reflexivity)) as RK1.
cbn [ms_regs restrict] in RK1.
pose proof (st_ok_restrict_reg SEGS (w_H W) E _ ms 10%bv HS) as R10.
lazymatch type of R10 with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in R10 end.
cbn [ms_regs restrict sv_denot] in R10.
pose proof (st_ok_restrict_reg SEGS (w_H W) E _ ms 1%bv HS) as R1.
lazymatch type of R1 with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in R1 end.
cbn [ms_regs restrict sv_denot] in R1. rewrite (img_env_codeptr E HEI) in R1.
lazymatch type of R1 with _ = Z_to_bv 64 (_ + ?n) => replace n with PJP2_RET in R1 by (vm_compute; reflexivity) end.
assert (HRET : PJP2_RET = ltac:(let v := eval vm_compute in PJP2_RET in exact v)) by (vm_compute; reflexivity).
assert (Hsp1' : spZ (ms_regs ms) = je_sp1 en) by (unfold spZ; rewrite (RK1 2%bv) by pjp2_in; exact Hsp).
assert (Hq10 : getr (ms_regs ms) 10 = w64 (je_sp1 en + 8)).
{ rewrite R10. rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl). change (bv_unsigned (getr regs 2)) with (spZ regs).
  rewrite Hsp. reflexivity. }
(* pj_parse's state at the call *)
assert (HINV1 : pjp_invR (fx := fx) B ARx (wle' SEGS YGcfRehidePost.RZ_cf) en Sb fy ly S Hp W (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy md) mat md) k).
{ apply (pjm_inv en Sb fy ly S Hp W regs mem md k ly S Hp (ms_regs ms) (ms_mem ms) _ k HINV HJ Hm1).
  - rewrite Hsp1', Hsp. reflexivity.
  - exact (RK1 8%bv ltac:(pjp2_in)).
  - intros r0 Hr0. exact (RK1 r0 (or_intror (or_intror Hr0))). }
pose proof HOUT as (Ho4096 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
assert (Hhi1 : spZ (ms_regs ms) + 64 <= ly_stk_hi ly) by (rewrite Ehi, Hsp1'; lia).
(* fpre's return-address bound: the `jal skip_ws` return site, a code address below the shadow *)
assert (HRAc : raZ (ms_regs ms) < YM05.alloc_ceiling).
{ assert (HB : 0 <= BASE + PJP2_RET < kLowMemEnd) by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
  unfold raZ. rewrite R1, unsigned_lit_small by (unfold kLowMemEnd in HB; lia). lia. }
pose proof (pjm_rod (w_H W) mem (ms_mem ms) Hm1 HROD) as HROD1.
pose proof (pjm_in_ok (w_H W) mem (ms_mem ms) Hm1 _ _ _ _ _ _ HCUR) as HCUR1.
pose proof (pjm_ra (w_H W) mem (ms_mem ms) Hm1 _ _ HRA24) as HRA1.
pose proof (pjm_src W mem (ms_mem ms) _ _ Hm1 (proj1 HTXT)) as HSRC1.
pose proof (pjm_ledger ly S Hp W mem (ms_mem ms) Lam' peak' cnt' fail' ran' (je_most en) (je_own en) Hm1 HLED) as HLED1.
assert (Hsink : ~ YI16.sink_open_fp [(je_sp1 en + 8, je_sp1 en + 8 + 8)])
  by (apply sink_closed_pos; repeat constructor; cbn [fst]; lia).
(* ---- +0x58: `jal skip_ws`, its text at the callee window e1 = 32, by the call rule over R at wle' SEGS RZ_cf ---- *)
eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ eapply (aj_call_xW_spR (fx := fy) (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ B_prog_listing PA)
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
    W E _ ms
    (STK_pj_parse + je_d en) (je_sp0 en + je_d en) [(je_out en, je_out en + 56)]
    (je_ly en) Sb (je_Hp en) (je_W en) (je_mem en) (je_md en) [] ly S Hp _ k
    STK_skip_ws 32 [(je_sp1 en + 8, je_sp1 en + 8 + 8)] (je_sp1 en - (je_sp0 en + je_d en))
    (Z_to_bv 64 (BASE + PJP2_RET)) [] _ HS eq_refl HJ).
  - rewrite Hsp1'. lia.
  - lia.
  - lia.
  - exact HSK0.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite (RK1 3%bv) by pjp2_in. rewrite (HKP 3%bv) by pjp2_in. exact Hgp.
  - rewrite (RK1 4%bv) by pjp2_in. rewrite (HKP 4%bv) by pjp2_in. exact Htp.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); rewrite HRET; [lia | reflexivity].
  - apply Z.leb_le. vm_compute. reflexivity.
  - apply achain_low. unfold s0Z. rewrite (RK1 8%bv) by pjp2_in. rewrite H8. unfold w64.
    rewrite unsigned_lit_small by lia. exact Hout.
  - (* skip_ws's text is a plain SRr: lifted into SRrG at wle', its post's journal moved from wle to wle' *)
    intros HAFN1 HWIN1.
    eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf)).
    { apply (SRr_SRrG SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle_wle' SEGS YGcfRehidePost.RZ_cf)).
      exact (SKIPWS fy ly S Hp W (ms_regs ms) (ms_mem ms) _ [] 32 (je_sp1 en + 8) (je_t0 en) (je_len en)
        (je_t0 en + je_len en - Z.of_nat (length r)) 0 (je_tl en) Lam' peak' cnt' fail' ran' (je_most en) (je_own en)
        (conj HAFN1 (conj HROD1 (conj Hhi1 (conj HRAc HFZ)))) Hq10 HCUR1 HWIN1 ltac:(rewrite Hsp1'; lia)
        ltac:(rewrite Hsp1'; lia)
        HRA1 HSRC1 (proj2 HTXT) HLED1). }
    cbv beta. intros Ws cs _ (lys & Ss & Hps & regss & mems & mds & ks & Ecs & HJs & HXs & HPs & HKs).
    exists lys, Ss, Hps, regss, mems, mds, ks. split; [exact Ecs|].
    split; [exact (ajournal_xwR_mono (SK := SK) SEGS B prh_pst ARx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
              (wle_wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ HJs)|].
    exact (conj HXs (conj HPs HKs)).
  - intros a (r0 & [<- | []] & Hr0). cbn [fst snd] in Hr0. right; right; right. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HX & HP2 & HQ).
unfold fQmn in HQ. cbv beta in HQ.
destruct HQ as ((HRk & EHp2 & ES2 & Eab2 & HLED2 & HCUR2) & HMK2).
(* the memory overlay after the call (skip_ws's keep, the first stretch storing nothing) and the run position
   (skip_ws keeps the allocator state) *)
assert (HMN2 : YAkMemnorm.memnorm SEGS mem2) by exact (HMK2 (pjm_mn _ _ Hm1 HMN)).
assert (HPOS2 : pjp_pos_pv en S2 tr) by (rewrite ES2; exact HPOSPV).
assert (HOUTC2 : pjp_outc en S2 (Some (t, r)) tr ran') by (rewrite ES2; exact HOUTC).
replace (je_sp0 en + je_d en + (je_sp1 en - (je_sp0 en + je_d en)) + 32) with (je_sp1 en + 32) in HJc by lia.
rewrite Erest in HCUR2.
(* what the call keeps: the frame (pjp_frame_kept_stmt), out's facts and the tree *)
destruct (KEPT en Sb fy ly S Hp W (ms_regs ms) (ms_mem ms) _ k STK_skip_ws 32 [(je_sp1 en + 8, je_sp1 en + 8 + 8)]
  ly2 S2 Hp2 W2 mem2 md2 k1 [] HINV1 HJc HSK0 ltac:(lia) Hd0 Hsink) as (KW & KRA & KS0 & KPR & KCUR & KROD).
{ intros a (r0 & [<- | []] & Hr0). cbn [fst snd] in Hr0. lia. }
pose proof (pjp2_kept_regs (ms_regs ms) regs2 HP2) as RK2.
assert (HINV2 : pjp_invR (fx := fx) B ARx (wle' SEGS YGcfRehidePost.RZ_cf) en Sb fy ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1)).
{ split; [exact HFZ|]. split; [exact HFK|]. split; [exact HJ2|]. split; [exact KW|].
  split; [unfold spZ; rewrite (RK2 2%bv) by pjp2_in; exact Hsp1'|].
  split; [exact KRA|]. split; [exact KS0|].
  split; [rewrite (RK2 8%bv) by pjp2_in; rewrite (RK1 8%bv) by pjp2_in; exact H8|].
  split; [intros r0 Hr0; rewrite (RK2 r0) by (right; right; exact Hr0); rewrite (RK1 r0) by (right; right; exact Hr0);
          exact (HKP r0 Hr0)|].
  split; [exact KPR|]. split; [exact KCUR|]. split; [exact KROD | exact HMN2]. }
pose proof (pjp2_out_kept en ly S Hp W (ms_mem ms) _ Lam' ly2 S2 Hp2 W2 mem2 md2 _ _ _ k1 peak' cnt' fail' ran'
  (je_most en) (je_own en)
  (pjm_out en ly S Lam' W mem (ms_mem ms) Hm1 HOUT) HJc HAR1 HFP1 Eab2 HLED2) as HOUT2.
pose proof (pjp2_node_kept en ly S Hp W (ms_mem ms) _ ly2 S2 Hp2 W2 mem2 md2 _ _ _ k1 Lam' peak' cnt' fail' ran'
  (je_most en) (je_own en) t D
  (pjm_out en ly S Lam' W mem (ms_mem ms) Hm1 HOUT) HLED1 HDL (pjm_node W mem (ms_mem ms) _ _ _ _ Hm1 HNODE)
  HJc HAR1 HFP1 Eab2) as HNODE2.
(* the tree's capacity words and its free order (parse_value's post, the batch kit), kept across skip_ws; pj_free's order list F
   of out's tree at DOC_D (>= depth t, PjGrammar.jr_value_depth) for the refused path *)
pose proof (pjp2_ncap_kept en ly S Hp W (ms_mem ms) _ ly2 S2 Hp2 W2 mem2 md2 _ _ _ k1 Lam' peak' cnt' fail' ran'
  (je_most en) (je_own en) t D
  (pjm_out en ly S Lam' W mem (ms_mem ms) Hm1 HOUT) HLED1 HDL (pjm_node W mem (ms_mem ms) _ _ _ _ Hm1 HNODE)
  (pjm_ncap W mem (ms_mem ms) _ _ Hm1 HNCAP) HJc HAR1 HFP1 Eab2) as HNCAP2.
assert (HTIE2 : pjp_ftie en W2 mem2 Lam' D ok (PjTree.depth t)).
{ intros HH' n Hn. destruct (HTIE HH' n Hn) as (F' & HFO' & HT'). exists F'. split; [|exact HT'].
  exact (pjp2_fo_kept en ly S Hp W (ms_mem ms) _ ly2 S2 Hp2 W2 mem2 md2 _ _ _ k1 Lam' peak' cnt' fail' ran'
    (je_most en) (je_own en) n D F'
    (pjm_out en ly S Lam' W mem (ms_mem ms) Hm1 HOUT) HLED1 HDL (pjm_fo W mem (ms_mem ms) _ _ _ _ _ Hm1 HFO')
    HJc HAR1 HFP1 Eab2). }
assert (HdD : (PjTree.depth t <= DOC_D)%nat).
{ pose proof (G_depth _ _ _ _ _ _ Hjv) as Hdep. unfold DOC_D. lia. }
destruct (HTIE HH DOC_D HdD) as (F & HFO0 & HTIEF).
pose proof (pjp2_fo_kept en ly S Hp W (ms_mem ms) _ ly2 S2 Hp2 W2 mem2 md2 _ _ _ k1 Lam' peak' cnt' fail' ran'
  (je_most en) (je_own en) DOC_D D F
  (pjm_out en ly S Lam' W mem (ms_mem ms) Hm1 HOUT) HLED1 HDL (pjm_fo W mem (ms_mem ms) _ _ _ _ _ Hm1 HFO0)
  HJc HAR1 HFP1 Eab2) as HFO2.
pose proof HJc as (_ & _ & _ & _ & _ & HfrsC & _).
clear HS SHOK HJ HF HFr HG.
(* ---- stretch 2 (+0x5c .. the beq): p and end reloaded from the cursor ---- *)
set (p2 := je_t0 en + je_len en - Z.of_nat (length (PjGrammar.skip r))) in *.
pose proof HCUR2 as (V1 & V2 & _ & _ & _ & Ht0' & Ht62' & Hp2r & _).
pose proof HINV2 as (_ & _ & _ & _ & Hsp2 & _).
set (E2 := Eimg (Ereg regs2 [Z_to_bv 64 p2; Z_to_bv 64 (je_t0 en + je_len en)])).
assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2; apply Eimg_env).
assert (EL2 : forall n (r0 : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r0 -> ew E2 n = getr regs2 r0).
{ intros n r0 Hn Hr0. unfold E2. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs2 _ n r0 Hr0). }
assert (HAE2 : env_agree 32 (Ereg regs2 [Z_to_bv 64 p2; Z_to_bv 64 (je_t0 en + je_len en)]) E2)
  by (unfold E2; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E2 32 = Z_to_bv 64 p2)
  by (unfold E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E2 33 = Z_to_bv 64 (je_t0 en + je_len en))
  by (unfold E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (U2 : bv_unsigned (ew E2 2) = je_sp1 en).
{ rewrite (EL2 2%nat 2%bv ltac:(lia) eq_refl). change (bv_unsigned (getr regs2 2)) with (spZ regs2). exact Hsp2. }
assert (U32 : bv_unsigned (ew E2 32) = p2) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E2 33) = je_t0 en + je_len en) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi (fx := fy) SEGS VAL E2 pjp2_ss2
  (restrict (w_H W2) (@YK11.mkst fy regs2 (Z_to_bv 64 (BASE + PJP2_RET)) mem2 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pjp2_ss2. apply (pa_entry_st_ok_full (fx := fy)).
  - unfold E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pjp2_reg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val SEGS E2 _ (je_sp1 en) 8 8 (SOff 32 0) p2);
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | change (Z.of_N 8) with 8; lia | exact V1].
    + apply (chunk_ok_val SEGS E2 _ (je_sp1 en) 16 8 (SOff 33 0) (je_t0 en + je_len en));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | change (Z.of_N 8) with 8; lia |].
      replace (je_sp1 en + 16) with (je_sp1 en + 8 + 8) by lia. exact V2.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - cbn. repeat split. }
assert (SHOK : sh_ok SEGS PJP2_Bx [] E2 (mrestrict (w_H W2) mem2)) by exact (Forall_nil _).
pose proof HJ2 as HJ.
paj_run_tok_xR RUN HS HJ SHOK PJP2_Bspan.
{ intros a (r0 & Hr0 & Ha). unfold pjp2_ss2 in Hr0. cbn [ss_mem In] in Hr0. destruct Hr0 as [<- | []].
  unfold pjp2_reg in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
lazymatch goal with HFx : frame_of _ _ mem2 (ms_mem ?m) |- _ =>
  assert (Hmb : forall x, ms_mem m x = mem2 x)
    by (intros x; apply HFx; intros (r0 & Hr0 & Ha); unfold pjp2_ss2 in Hr0; cbn [ss_mem In] in Hr0;
        destruct Hr0 as [<- | []]; unfold pjp2_reg in Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia)
end.
clear HF HFr HG.
pose proof (G_calls _ _ _ _ _ Hjv) as Hcl.
pose proof HLED0 as HLB0. apply prh_ledger_bounds in HLB0. destruct HLB0 as (_ & _ & Hcn0 & _).
(* +0x64: `beq a0, a1` on p (atom 32) and end (atom 33) *)
psrr_branch_tok RUN BR HS SHOK PJP2_Bspan.
- (* p = end: the rest after the value is white space only; +0x84 a0 := 0, j +0x74: the cut C3 *)
  rewrite branch_eq_U, (U_atom E2 32 p2 E32 ltac:(lia)), (U_atom E2 33 _ E33 ltac:(lia)) in Hc.
  apply Z.eqb_eq in Hc.
  assert (Hsk : PjGrammar.skip r = []) by (apply length_zero_iff_nil; unfold p2 in Hc; lia).
  paj_run_to_tok_xR RUNTO HS HJ SHOK PJP2_Bspan PJP_C3.
  { intros a (r0 & Hr0 & Ha). cbn in Hr0. destruct Hr0 as [<- | []]. cbn in Ha. lia. }
  lazymatch goal with HFx : frame_of _ _ (ms_mem ms0) (ms_mem ?m) |- _ =>
    assert (HmE : forall x, ms_mem m x = mem2 x)
      by (intros x; rewrite <- (Hmb x); apply HFx; intros (r0 & Hr0 & Ha); cbn in Hr0; destruct Hr0 as [<- | []];
          cbn in Ha; lia) end.
  pose proof (regs_kept_of_st_ok_pi (fx := fy) (PI := PA) E2 _ _ regs2 _
    ((2%bv : bv 5) :: (8%bv : bv 5) :: PJP_KEPT) HS HAE2 ltac:(vm_compute; reflexivity)) as RKE.
  cbn [ms_regs restrict] in RKE.
  prreg HS (10%bv : bv 5) R10e.
  pmkst HS.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?n)) ?mm _; cfg_model := ?dd |} _ =>
    replace n with PJP_C3 by (vm_compute; reflexivity);
    apply (SEG3 en Sb fy ly2 S2 Hp2 W2 rg mm dd (k + k1) HPRE HWB) end.
  split.
  { apply (pjm_inv en Sb fy ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) ly2 S2 Hp2 _ _ _ (k + k1) HINV2 HJ HmE).
    - unfold spZ. rewrite (RKE 2%bv) by pjp2_in. reflexivity.
    - exact (RKE 8%bv ltac:(pjp2_in)).
    - intros r0 Hr0. exact (RKE r0 (or_intror (or_intror Hr0))). }
  assert (Hpost : PjGrammar.post (Some (t, r)) = Some t) by (unfold PjGrammar.post; rewrite Hsk; reflexivity).
  split; [exact (HRk HROOM)|].
  (* the hull use: parse_value's (the cut's; skip_ws keeps the allocator state), inside pj_parse's list *)
  split; [rewrite ES2; apply (pj_parse_counts.pjc_hull_used_pv ReaderRes.jr_strtod); exact HHUSE|].
  exists ok, (Some t), tr, Lam', peak', cnt', fail', ran'.
  split; [rewrite (G_run _ _ _ _ _ Hjv), Hpost; reflexivity|].
  split; [exact Hoks|].
  split; [rewrite Hcnt'; apply Z.mod_small; lia|].
  split; [exact (proj1 (G_fail_after _ _ _ _) Hfa')|].
  split; [rewrite <- (pjg_gtrace (je_tl en)); exact Hpk'|].
  split; [rewrite Hlen in Hhp; change (Z.of_nat (PjGrammar.MAXD - 0)) with 32 in Hhp; lia|].
  split; [intros Hf; pose proof (G_fail_in _ _ _ _ _ _ _ _ _ _ _ Hjv Hoks Hf) as Hn; rewrite Hpost in Hn;
          discriminate Hn|].
  split; [intros Hf Hnr; destruct (G_norefuse _ _ _ _ _ _ _ Hjv Hf Hnr) as [Q1 Q2]; rewrite Hpost in Q1;
          exact (conj Q1 Q2)|].
  split; [exact (pjm_ledger _ _ _ _ _ _ _ _ _ _ _ _ _ HmE HLED2)|].
  (* the text's position transfer: an accepted document makes the reader's events and no bulk (PresetReqAt.parse_evs
     at the outcomes ok of the run), so parse_value's transfer (the cut's pjp_pos_pv, kept across skip_ws) is it *)
  assert (Ep : PresetReqAt.parse_evs ReaderRes.jr_strtod (je_tl en) ok = PresetReqAt.rd_hevs tr).
  { unfold PresetReqAt.parse_evs, PresetReqAt.rtr, PjGrammar.jr_run. rewrite Hjv. cbn [fst snd].
    rewrite Hsk. cbv beta iota. apply app_nil_r. }
  split.
  { intros sm x os i H0 hist Hpos Hrun.
    rewrite Ep in Hrun |- *. exact (proj1 HPOS2 sm x os i H0 hist Hpos Hrun). }
  (* THE OUTCOME (the batch kit): at a run whose next events are the all-granted reading's, with no injected failure in its
     window, parse_value's outcome conjunct (the cut's pjp_outc, kept across skip_ws) makes the reading the
     all-granted one; an accepted document makes no bulk under either outcome list *)
  split.
  { intros sm x os i H0 hist Hpos Hrun Hcons Hwin.
    assert (Egt : prhPv_gtrace 0 (je_tl en) = snd (PjGrammar.jr_run ReaderRes.jr_strtod (je_tl en) [])).
    { rewrite (pjg_gtrace (je_tl en)). reflexivity. }
    assert (Ep0 : PresetReqAt.parse_evs ReaderRes.jr_strtod (je_tl en) [] =
      PresetReqAt.rd_hevs (prhPv_gtrace 0 (je_tl en)) ++
      match fst (PjGrammar.jr_run ReaderRes.jr_strtod (je_tl en) []) with
      | Some _ => [] | None => [PresetReqAt.HBulk (PresetReqAt.pj_frees ReaderRes.jr_strtod [] (je_tl en))] end).
    { rewrite Egt. reflexivity. }
    rewrite Ep0 in Hrun, Hcons. apply prh_run_at_app_iff in Hrun as (Hrun1 & _).
    rewrite length_app in Hcons. apply prh_cons_from_app_iff in Hcons as (Hcons1 & _).
    assert (Hwin' : je_fail en < je_cnt en \/
      je_cnt en + Z.of_nat (PjGrammar.calls (prhPv_gtrace 0 (je_tl en))) <= je_fail en).
    { rewrite Egt. exact Hwin. }
    destruct (HOUTC2 sm x os i H0 hist Hpos Hrun1 Hcons1 Hwin') as (Eran & Efst & h2 & Hpos2).
    destruct (PjGrammar.jr_value ReaderRes.jr_strtod 0 (je_tl en) []) as [[res0 tr0] okr0] eqn:Ev0.
    cbn [fst] in Efst. injection Efst as -> ->.
    pose proof (G_run _ _ _ _ _ Ev0) as Er0. rewrite Hpost in Er0.
    assert (Etr : prhPv_gtrace 0 (je_tl en) = tr).
    { unfold prhPv_gtrace. change prh_jr_strtod with ReaderRes.jr_strtod. rewrite Ev0. reflexivity. }
    split; [exact Eran|]. split; [exact Er0|].
    split; [rewrite Ep, Ep0, Etr, Er0; cbn [fst]; rewrite app_nil_r; reflexivity|].
    exists h2. rewrite Ep0, Etr, Er0, length_app. cbn [fst length]. rewrite Nat.add_0_r.
    rewrite Etr in Hpos2. exact Hpos2. }
  (* THE OUTCOME OF AN INJECTED READING (the text's GUARDED conjunct): parse_value's (the cut's pjp_inj); under the
     model's grant list the reading's events are parse_value's at that list, then nothing or the refusal's HBulk *)
  split.
  { intros sm x os i H0 hist Hpos Hrun Hcons HwinI.
    assert (Egt : prhPv_gtrace 0 (je_tl en) = snd (PjGrammar.jr_run ReaderRes.jr_strtod (je_tl en) [])).
    { rewrite (pjg_gtrace (je_tl en)). reflexivity. }
    destruct (PjGrammar.jr_value ReaderRes.jr_strtod 0 (je_tl en) (PresetReqAt.okk (Z.to_nat (je_fail en - je_cnt en))))
      as [[resk trk] okrk] eqn:Evk.
    assert (Epk : exists Rk, PresetReqAt.parse_evs ReaderRes.jr_strtod (je_tl en)
        (PresetReqAt.okk (Z.to_nat (je_fail en - je_cnt en))) = PresetReqAt.rd_hevs trk ++ Rk).
    { unfold PresetReqAt.parse_evs, PresetReqAt.rtr. rewrite (G_run _ _ _ _ _ Evk). cbn [fst snd].
      eexists. reflexivity. }
    destruct Epk as (Rk & Epk).
    rewrite Epk in Hrun, Hcons. apply prh_run_at_app_iff in Hrun as (Hrun1 & _).
    rewrite length_app in Hcons. apply prh_cons_from_app_iff in Hcons as (Hcons1 & _).
    apply (HINJ sm x os i H0 hist Hpos).
    - rewrite Evk. exact Hrun1.
    - rewrite Evk. exact Hcons1.
    - rewrite Egt. exact HwinI. }
  split; [exact R10e|].
  exists D. split; [exact HPL|]. split; [exact HPD|]. split; [exact HND|]. split; [exact Hnew|].
  split; [rewrite Eab2, <- G_ab_hbl; exact HPab|].
  split.
  { intros HH' n Hn. destruct (HTIE2 HH' n Hn) as (F' & HFO' & HT'). exists F'.
    split; [exact (pjm_fo _ _ _ _ _ _ _ _ HmE HFO') | exact HT']. }
  split; [exact (pjm_node _ _ _ _ _ _ _ HmE HNODE2) | exact (pjm_ncap _ _ _ _ _ HmE HNCAP2)].
- (* p <> end: junk after the value; falls through to +0x68: the cut C2ref *)
  rewrite branch_eq_U, (U_atom E2 32 p2 E32 ltac:(lia)), (U_atom E2 33 _ E33 ltac:(lia)) in Hc.
  apply Z.eqb_neq in Hc.
  assert (Hsk : PjGrammar.skip r <> []) by (intros E0; apply Hc; unfold p2; rewrite E0; cbn [length]; lia).
  paj_run_to_tok_xR RUNTO HS HJ SHOK PJP2_Bspan PJP_C2REF.
  { intros a (r0 & Hr0 & Ha). cbn in Hr0. destruct Hr0 as [<- | []]. cbn in Ha. lia. }
  lazymatch goal with HFx : frame_of _ _ (ms_mem ms0) (ms_mem ?m) |- _ =>
    assert (HmE : forall x, ms_mem m x = mem2 x)
      by (intros x; rewrite <- (Hmb x); apply HFx; intros (r0 & Hr0 & Ha); cbn in Hr0; destruct Hr0 as [<- | []];
          cbn in Ha; lia) end.
  pose proof (regs_kept_of_st_ok_pi (fx := fy) (PI := PA) E2 _ _ regs2 _
    ((2%bv : bv 5) :: (8%bv : bv 5) :: PJP_KEPT) HS HAE2 ltac:(vm_compute; reflexivity)) as RKE.
  cbn [ms_regs restrict] in RKE.
  pmkst HS.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?n)) ?mm _; cfg_model := ?dd |} _ =>
    replace n with PJP_C2REF by (vm_compute; reflexivity);
    apply (SEG2R en Sb fy ly2 S2 Hp2 W2 rg mm dd (k + k1) HPRE HWB) end.
  split.
  { apply (pjm_inv en Sb fy ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) ly2 S2 Hp2 _ _ _ (k + k1) HINV2 HJ HmE).
    - unfold spZ. rewrite (RKE 2%bv) by pjp2_in. reflexivity.
    - exact (RKE 8%bv ltac:(pjp2_in)).
    - intros r0 Hr0. exact (RKE r0 (or_intror (or_intror Hr0))). }
  split; [exact (HRk HROOM)|].
  split; [rewrite ES2; exact HHUSE|].
  exists ok, (Some (t, r)), tr, D, F, Lam', peak', cnt', fail', ran'.
  split.
  { split; [exists okr; exact Hjv|]. split; [exact (pjm_ledger _ _ _ _ _ _ _ _ _ _ _ _ _ HmE HLED2)|].
    split; [exact HLM|].
    split; [exact Hnew|]. split; [rewrite Eab2; exact HPab|]. split; [rewrite HfrsC; exact HPfr | exact Hhp]. }
  split; [exact HPOS2|].
  split; [exact HOUTC2|].
  split; [unfold PjGrammar.post; destruct (PjGrammar.skip r) eqn:Esk;
          [exfalso; first [exact (Hsk Esk) | exact (Hsk eq_refl)] | reflexivity]|].
  split; [exact (pjm_fo _ _ _ _ _ _ _ _ HmE HFO2)|].
  split; [exact HTIEF|].
  split; [exact (pjm_out _ _ _ _ _ _ _ HmE HOUT2)|].
  exact HINJ.
Qed.

End c.
