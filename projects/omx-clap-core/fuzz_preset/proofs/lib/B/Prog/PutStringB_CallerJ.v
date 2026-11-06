(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: COPY (image-generic, unchanged) of lib/A/Prog/PRW_CallerJ.v at origin/cold/h-hpreset-7-walk-S7B 7819c4b4583 (blob e7aacedc91b5); the #102 base lacks it *)
(* fuzz_preset, program walks: the DISCHARGE KIT of the caller-window post (PRH_Base.v fwin / fpostW / fpostWF,
   kit 5acdafdf5d6 :274-294), ONE copy for every lane (slice S4, sole writer). Statements and their proofs; no walk.
   What a walk of a function in the caller-window form needs that fpostW itself does not give:
   - START: ajournal_x_init_W, the widened journal (STK + e) (sp + e) at the entry state, from afn_pre_x and fwin.
   - CALL of a callee in caller-window form: aj_call_xW (aj_call_x of c-omx-alloc's YCbqGcall.v with the callee's
     post in fpostW form). It closed a gap of kit 5acdafdf5d6: that kit's ajournal_x_sub (on this tree YCbqG.v:1546, with fp_sub_x) asked the
     callee's FP inside the caller's FP-and-live-blocks or its new blocks, and fpostW's FP holds STACK cells.
     ajournal_x_sub_W widens that side condition by the caller's own window, and PROVES the widening sound (the
     side condition is used only on block bytes, frame bytes and the sink address 0, all below alloc_ceiling, while
     a window byte is at or above it).
   - END: the extension clause of fpostW ([sp, sp + e) outside FP unchanged) is NOT implied by the widened journal,
     whose window contains [sp, sp + e). The walk carries cj_kept (the keep clauses of ajournal_x relative to its
     entry, its own window and its written cells OR exempted) across its stretches (cj_kept_exec) and calls
     (cj_kept_of_journal), chains them (cj_kept_trans) and closes with fpostW_x_of_kept / fpostWF_x_of_kept.
   fpostW_x / fpostWF_x / fwin_x are PRH_Base's fpostW / fpostWF / fwin with the image (segs) and the statics PST as
   parameters: PRH_Base.fpostW B ARx SK STK d FP ... unfolds to fpostW_x segs B prh_pst ARx STK d FP ... (by
   reflexivity), so a walk closes the text with `exact` after unfolding.
   Donor of cj_kept: cgif_file_fuzzer lib/YC20.v:311-325 tlzw_kept and lib/YC8n.v:272-287 tlzw_kept_of_journal
   (origin/release/pau-projects-recipes), generalised to ajournal_x's keep clauses; of ajournal_x_sub_W and aj_call_xW:
   YCbqG.v:499-583 ajournal_x_sub / afn_pre_x_at and c-omx-alloc 09d7536b62b YCbqGcall.v aj_call_x.
   No address literal; numerals are LENGTH (16, 4096, 2 ^ 64). No image constant. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YK0o YCbqG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section cj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.

(* ---- PRH_Base.v's caller-window names, image- and statics-parametric (same bodies) ---- *)
Definition fwin_x (ly : alayout) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (d : Z) : Prop :=
  0 <= d /\ d mod 16 = 0 /\ spZ regs + d <= ly_top ly /\
  (forall a, spZ regs <= a < spZ regs + d -> apresent (w_H W) mem a).
Definition fpostW_x (STK d : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) (W : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' Hp' regs' mem' md' k,
    c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
    ajournal_x (SK := SK) segs B PST ARx (STK + d) (spZ regs + d) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
    (forall a, spZ regs <= a < spZ regs + d -> ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Definition fpostWF_x (STK d : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) (W : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k,
    c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
    ajournal_x (SK := SK) segs B PST ARx (STK + d) (spZ regs + d) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
    (forall a, spZ regs <= a < spZ regs + d -> ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.

(* ---- what a walk leaves relative to a state (lyc Sc W memc mdc) of its own, at a later state (ly2 S2 W2 mem2 md2):
   ajournal_x's keep clauses (YCbqG.v:115-138), with the walker's own window [sp - STKf, sp) and its written cells OR
   (the stack cells fpostW's FP names, or all of FP) exempted; FPc: the heap bytes (and sink) written in blocks live
   at the first state. Blocks allocated in between are free to write (they are not blocks of the first state). ---- *)
Definition cj_kept (STKf sp : Z) (OR FPc : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
  (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  layout_le (length (st_secs Sc)) lyc ly2 /\ (length (st_secs Sc) <= length (st_secs S2))%nat /\
  wle W W2 /\ aos_step FPc mdc md2 /\ frames S2 = frames Sc /\
  (* the machine stack (every byte at or above alloc_ceiling) *)
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STKf <= a < sp) -> ~ inFP OR a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (* the blocks live at both states *)
  (forall p m i, In (p, m) (ablocks B lyc Sc) -> In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
     ~ inFP FPc (p + i) -> ~ inFP OR (p + i) ->
     aview segs (w_H W2) mem2 (p + i) = aview segs (w_H W) memc (p + i)) /\
  (* a block of the first state freed in between lies in FPc *)
  (forall p m i, In (p, m) (ablocks B lyc Sc) -> ~ In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
     inFP FPc (p + i)) /\
  (* the image, but the runtime's own statics, errno and the program's statics PST *)
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> fp_spares (SK := SK) FPc a -> ~ inFP OR a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (* the ASan frames of the first state and their shadow *)
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ inFP FPc a -> ~ inFP OR a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (* the layout's extra ranges, but errno *)
  (forall a, Exists (in_zr a) (ly_extra lyc) -> ~ (as_errno B <= a < as_errno B + 4) -> ~ inFP OR a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).

(* nothing changed *)
Lemma cj_kept_refl : forall STKf sp OR FPc lyc Sc W memc mdc,
  cj_kept STKf sp OR FPc lyc Sc W memc mdc lyc Sc W memc mdc.
Proof.
intros. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|]. split; [apply aos_step_refl|].
split; [reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros p m i H1 H2; exfalso; exact (H2 H1)|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. intros; reflexivity.
Qed.

(* a stretch a journal from the first state covers (a callee's post from aj_call_x / aj_call_xW, window STKf below
   sp, own = []) is kept for every OR (cgif YC8n.v:272-287 tlzw_kept_of_journal) *)
Lemma cj_kept_of_journal : forall STKf sp FPc lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 OR,
  ajournal_x (SK := SK) segs B PST ARx STKf sp FPc lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  cj_kept STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2.
Proof.
intros STKf sp FPc lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 OR HJ.
pose proof (ajx_ly HJ) as Hly. pose proof (ajx_secs HJ) as Hsecs. pose proof (ajx_wle HJ) as Hwle.
pose proof (ajx_io HJ) as Hio. pose proof (ajx_frs HJ) as Hfrs. pose proof (ajx_hi HJ) as F1. pose proof (ajx_blk HJ) as F2.
pose proof (ajx_img HJ) as F3. pose proof (ajx_frm HJ) as F4. pose proof (ajx_gone HJ) as Hgone. pose proof (ajx_extra HJ) as F5.
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [rewrite Hfrs; reflexivity|].
split; [intros a Ha Hw _; exact (F1 a Ha Hw)|].
split; [intros p m i H1 H2 Hi Hf _; exact (F2 p m i H1 H2 Hi Hf)|].
split; [exact Hgone|].
split; [intros a Hi Hn He Hp Hs _; exact (F3 a Hi Hn He Hp Hs)|].
split; [intros cid pos a Hin Hr Hf _; exact (F4 cid pos a Hin Hr Hf)|].
intros a Hx He _. exact (F5 a Hx He).
Qed.

Section l.
(* the head length of a harness block, the parameter of the journal's law record (YCbqG walks-new d15706bda36) *)
Variable HL : Z.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* two stretches in a row with the same OR, the second one's window inside the first's. FP1 and FP2 lie in FP3, or
   (FP2) in a block allocated since the first state, or at / above alloc_ceiling (stack cells: they touch no block,
   frame or sink clause). ARx at the first and the middle state separates blocks, frames and the stack. *)
Lemma cj_kept_trans : forall STK1 sp1 STK2 sp2 OR FP1 FP2 FP3
  lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 ly3 S3 W3 mem3 md3,
  cj_kept STK1 sp1 OR FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 ->
  cj_kept STK2 sp2 OR FP2 ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md3 ->
  ARx lyc Sc Hpc W memc mdc -> ARx ly2 S2 Hp2 W2 mem2 md2 ->
  sp1 - STK1 <= sp2 - STK2 -> sp2 <= sp1 ->
  (forall a, inFP FP1 a -> inFP FP3 a \/ alloc_ceiling <= a) ->
  (forall a, inFP FP2 a -> inFP FP3 a \/ in_tmp_block (ablocks B lyc Sc) (ablocks B ly2 S2) a \/ alloc_ceiling <= a) ->
  cj_kept STK1 sp1 OR FP3 lyc Sc W memc mdc ly3 S3 W3 mem3 md3.
Proof.
intros STK1 sp1 STK2 sp2 OR FP1 FP2 FP3 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 ly3 S3 W3 mem3 md3
  (Hly & Hsecs & Hwle & Hio & Hfrs & F1 & F2 & Hgone & F3 & F4 & F5)
  (Hly2 & Hsecs2 & Hwle2 & Hio2 & Hfrs2 & G1 & G2 & Hgone2 & G3 & G4 & G5) HARc HAR2 Hlo Hhi H13 H23.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hs13 : YI16.sink_open_fp FP1 -> YI16.sink_open_fp FP3).
{ intros (r & Hr & H0). destruct (H13 0 (ex_intro _ r (conj Hr H0))) as [Hf | Hc]; [exact Hf | zlia]. }
assert (Hs23 : YI16.sink_open_fp FP2 -> YI16.sink_open_fp FP3).
{ intros (r & Hr & H0). destruct (H23 0 (ex_intro _ r (conj Hr H0))) as [Hf | [(b & m & Hbin & _ & Hb) | Hc]]; [exact Hf| |zlia].
  exfalso. pose proof (alx_blocks segs B ARx LAWS _ _ _ _ _ _ _ _ HAR2 Hbin) as (_ & H4096 & _). zlia. }
(* a byte of a first-state block is below alloc_ceiling *)
assert (Hblo : forall p m i, In (p, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> p + i < alloc_ceiling).
{ intros p m i H1 Hi. pose proof (alx_blocks segs B ARx LAWS _ _ _ _ _ _ _ _ HARc H1) as (_ & _ & Hc & _). zlia. }
(* a byte of a first-state block live at the middle state is not in a block allocated since the first state *)
assert (Htmp : forall p m i, In (p, m) (ablocks B lyc Sc) -> In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
  ~ in_tmp_block (ablocks B lyc Sc) (ablocks B ly2 S2) (p + i)).
{ intros p m i H1 H2 Hi (b & m' & Hbin & Hb0 & Hr).
  assert (Hne : (b, m') <> (p, m)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
  pose proof (sep_blocks_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m' p m HAR2 Hbin H2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
split; [eapply layout_le_trans; [exact Hsecs | exact Hly | exact Hly2]|].
split; [zlia|]. split; [eapply wle_trans; eassumption|].
split; [eapply aos_step_trans; [eapply aos_step_mono; [exact Hs13 | exact Hio] | eapply aos_step_mono; [exact Hs23 | exact Hio2]]|].
split; [rewrite Hfrs2, Hfrs; reflexivity|].
split.
{ intros a Ha Hw Hq. rewrite <- (F1 a Ha Hw Hq). apply G1; [exact Ha | zlia | exact Hq]. }
split.
{ intros p m i H1 H3 Hi Hf Hq.
  assert (Hn1 : ~ inFP FP1 (p + i)).
  { intros Hx1. destruct (H13 _ Hx1) as [Hx2 | Hc]; [exact (Hf Hx2) | pose proof (Hblo p m i H1 Hi); zlia]. }
  assert (H2 : In (p, m) (ablocks B ly2 S2)).
  { destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, m) (ablocks B ly2 S2)) as [Hc|Hc]; [exact Hc|].
    exfalso. exact (Hn1 (Hgone p m i H1 Hc Hi)). }
  rewrite <- (F2 p m i H1 H2 Hi Hn1 Hq). apply (G2 p m i H2 H3 Hi); [|exact Hq].
  intros Hf2. destruct (H23 _ Hf2) as [Hf3 | [Ht | Hc]]; [exact (Hf Hf3) | exact (Htmp p m i H1 H2 Hi Ht) |].
  pose proof (Hblo p m i H1 Hi). zlia. }
split.
{ intros p m i H1 H3 Hi.
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, m) (ablocks B ly2 S2)) as [H2|H2].
  - destruct (H23 _ (Hgone2 p m i H2 H3 Hi)) as [Hf3 | [Ht | Hc]]; [exact Hf3 | exfalso; exact (Htmp p m i H1 H2 Hi Ht) |].
    exfalso. pose proof (Hblo p m i H1 Hi). zlia.
  - destruct (H13 _ (Hgone p m i H1 H2 Hi)) as [Hf3 | Hc]; [exact Hf3|]. exfalso. pose proof (Hblo p m i H1 Hi). zlia. }
split.
{ intros a Hi Hn He Hp Hs Hq.
  rewrite <- (F3 a Hi Hn He Hp (fun Ho => Hs (Hs13 Ho)) Hq). exact (G3 a Hi Hn He Hp (fun Ho => Hs (Hs23 Ho)) Hq). }
split.
{ intros cid pos a Hin Hr Hf Hq.
  assert (Efr : frame_addr ly2 cid pos = frame_addr lyc cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; exact Hin).
  destruct (frames_bounds_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hin2) as (Hf0 & Hfc & Hfh).
  rewrite Efr in Hf0, Hfc, Hfh. pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)).
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)).
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
  assert (Hlow : a < alloc_ceiling) by (unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr; destruct Hr as [Hr|Hr]; zlia).
  assert (Hn1 : ~ inFP FP1 a) by (intros Hx1; destruct (H13 _ Hx1) as [Hx2 | Hc]; [exact (Hf Hx2) | zlia]).
  rewrite <- (F4 cid pos a Hin Hr Hn1 Hq).
  apply (G4 cid pos a Hin2); [unfold frame_rng in *; cbn [fst snd] in *; rewrite Efr; exact Hr | | exact Hq].
  intros Hf2. destruct (H23 _ Hf2) as [Hf3 | [(b & m & Hbin & Hb0 & Hrb) | Hc]]; [exact (Hf Hf3) | | zlia].
  destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
  pose proof (sep_block_frame_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m cid pos HAR2 Hbin Hin2) as Hd.
  unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *. rewrite Efr in Hd.
  destruct Hr as [Hr|Hr]; zlia. }
intros a Hx He Hq. rewrite <- (F5 a Hx He Hq).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
apply G5; [rewrite Eextra; exact Hx | exact He | exact Hq].
Qed.

(* an engine stretch at one allocator state: the bytes it writes (Wr, the run's write ranges, from run_post's frame_of)
   lie in the walker's window, in OR, or in FPs inside a block live at that state *)
Lemma cj_kept_exec : forall STKf sp OR FPs lyc Sc Hpc W memc mdc memc' mdc' (Wr : Z -> Prop),
  ARx lyc Sc Hpc W memc mdc ->
  alloc_ceiling <= ly_stk_lo lyc -> ly_stk_lo lyc <= sp - STKf -> sp <= ly_stk_hi lyc ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H W) memc' x = mrestrict (w_H W) memc x) ->
  (forall a, Wr a -> (sp - STKf <= a < sp) \/ inFP OR a \/
     (inFP FPs a /\ exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m)) ->
  same_but_materialized mdc mdc' ->
  cj_kept STKf sp OR FPs lyc Sc W memc mdc lyc Sc W memc' mdc'.
Proof.
intros STKf sp OR FPs lyc Sc Hpc W memc mdc memc' mdc' Wr HAR Hcl Hwlo Hwhi Hfr HW Hsame.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H W) memc' a = aview segs (w_H W) memc a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|].
split; [eapply aos_step_same_io; [apply aos_step_refl | apply same_io_materialized, Hsame]|].
split; [reflexivity|].
split.
{ intros a Ha Hw Hq. apply Heqw; [zlia|]. intros HWa.
  destruct (HW a HWa) as [Hs | [Ho | (_ & b & m & Hbin & Hr)]]; [exact (Hw Hs) | exact (Hq Ho)|].
  pose proof (alx_blocks segs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hbin) as (_ & _ & Hc & _). zlia. }
split.
{ intros p m i H1 _ Hi Hf Hq.
  pose proof (alx_blocks segs B ARx LAWS _ _ _ _ _ _ _ _ HAR H1) as (_ & H4096 & Hc & _).
  apply Heqw; [zlia|]. intros HWa.
  destruct (HW _ HWa) as [Hs | [Ho | (Hf' & _)]]; [zlia | exact (Hq Ho) | exact (Hf Hf')]. }
split; [intros p m i H1 H2; exfalso; exact (H2 H1)|].
split.
{ intros a Hi Hn He Hpst Hsp Hq. pose proof (segs_low a Hi) as Hal.
  apply Heqw; [zlia|]. intros HWa.
  destruct (HW a HWa) as [Hs | [Ho | (_ & b & m & Hbin & Hr)]]; [zlia | exact (Hq Ho)|].
  exact (blk_img_x segs B ARx LAWS lyc Sc Hpc W memc mdc b m a HAR Hbin Hr Hi). }
split.
{ intros cid pos a Hin Hr Hf Hq.
  destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)).
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)).
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
  unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr.
  assert (Ha : 0 <= a < alloc_ceiling) by (destruct Hr as [Hr|Hr]; zlia).
  apply Heqw; [zlia|]. intros HWa.
  destruct (HW a HWa) as [Hs | [Ho | (Hf' & _)]]; [zlia | exact (Hq Ho) | exact (Hf Hf')]. }
intros a Hx He Hq.
pose proof (alx_extra segs B ARx LAWS lyc Sc Hpc W memc mdc a HAR Hx) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros HWa.
destruct (HW a HWa) as [Hs | [Ho | (_ & b & m & Hbin & Hr)]]; [apply Xs; zlia | exact (Hq Ho) | exact (Xb b m Hbin Hr)].
Qed.

(* ---- START of a caller-window walk: the widened journal at the entry state ---- *)
Lemma ajournal_x_init_W : forall STK e FP ly S Hp W regs mem md ch,
  afn_pre_x segs B ARx STK ly S Hp W regs mem md ch -> fwin_x ly W regs mem e ->
  ajournal_x (SK := SK) segs B PST ARx (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly S Hp W mem md 0.
Proof.
intros STK e FP ly S Hp W regs mem md ch (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) (He0 & He16 & Hetop & Hepres).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
unfold ajournal_x, ajournal_xw. apply ajx_intro.
- exact HAR.
- apply layout_le_refl.
- zlia.
- apply wle_refl.
- apply aos_step_refl.
- reflexivity.
- zlia.
- zlia.
- intros; reflexivity.
- intros; reflexivity.
- intros; reflexivity.
- intros; reflexivity.
- intros p n i H1 H2; exfalso; exact (H2 H1).
- intros a Ha. destruct (Z_lt_le_dec a (spZ regs)) as [Hl|Hl]; [apply Hpres; zlia | apply Hepres; zlia].
- unfold astk_ok. repeat split; try zlia. all: rewrite Z.add_mod, Hal, He16 by zlia; reflexivity.
- intros; reflexivity.
- exact HQT.
- exact (incl_appl [] (incl_refl _)).
Qed.

(* ---- END of a caller-window walk: the widened journal from entry and the walk's kept relation from entry (its own
   window STK below sp, its written cells OR, every one of them in FP) give fpostW_x / fpostWF_x ---- *)
Lemma fpostW_x_of_kept : forall STK e FP regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k,
  0 <= STK ->
  ajournal_x (SK := SK) segs B PST ARx (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k ->
  cj_kept STK (spZ regs) OR FPs ly S W mem md ly2 S2 W2 mem2 md2 ->
  (forall a, inFP OR a -> inFP FP a) ->
  aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  fpostW_x STK e FP regs ly S Hp W mem md Q W2
    (mkCfg (YK11.mkst regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros STK e FP regs ly S Hp W mem md Q OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k HSTK HJ HK HOR HP HQ.
pose proof (ajx_stk HJ) as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HK as (_ & _ & _ & _ & _ & K1 & _).
exists ly2, S2, Hp2, regs2, mem2, md2, k. split; [reflexivity|]. split; [exact HJ|].
split; [|split; [exact HP | exact HQ]].
intros a Ha Hf. apply K1; [zlia | zlia | intros Ho; exact (Hf (HOR a Ho))].
Qed.
Lemma fpostWF_x_of_kept : forall STK e FP regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k (fx' : YK11.FPState),
  frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' -> 0 <= STK ->
  ajournal_x (SK := SK) segs B PST ARx (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k ->
  cj_kept STK (spZ regs) OR FPs ly S W mem md ly2 S2 W2 mem2 md2 ->
  (forall a, inFP OR a -> inFP FP a) ->
  aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  fpostWF_x STK e FP regs ly S Hp W mem md Q W2
    (mkCfg (@YK11.mkst fx' regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros STK e FP regs ly S Hp W mem md Q OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k fx' Hz Hkf HSTK HJ HK HOR HP HQ.
pose proof (ajx_stk HJ) as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HK as (_ & _ & _ & _ & _ & K1 & _).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k. split; [reflexivity|]. split; [exact Hz|]. split; [exact Hkf|].
split; [exact HJ|]. split; [|split; [exact HP | exact HQ]].
intros a Ha Hf. apply K1; [zlia | zlia | intros Ho; exact (Hf (HOR a Ho))].
Qed.
(* an apost_base_x text (PRH_Base fpost) is the caller-window post at e = 0, so aj_call_xW serves both forms *)
Lemma fpostW_x_of_apost : forall STK FP regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  apost_base_x (SK := SK) segs B PST ARx STK FP regs ly S Hp W mem md Q W' c' ->
  fpostW_x STK 0 FP regs ly S Hp W mem md Q W' c'.
Proof.
intros STK FP regs ly S Hp W mem md Q W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HP & HQ).
exists ly', S', Hp', regs', mem', md', k. split; [exact Hc|]. rewrite !Z.add_0_r. split; [exact HJ|].
split; [intros a Ha; exfalso; lia | split; [exact HP | exact HQ]].
Qed.

(* ---- CALL of a caller-window callee (the gap G8). The side condition on the callee's footprint FP1, ONE shape for every
   window-journal call rule: the first three disjuncts are the engine of record's ajournal_x_sub (YCbqG.v walks-new
   ea24ad37a3c, :666-677, as c-omx-alloc f3963d079661 uses it): the caller's FP, a block the callee made and kept, a
   frame the caller made since its entry (own); the FOURTH is this kit's: a byte of the caller's own window
   [sp0 - STK, sp0), which needs neither a block nor an entry in the caller's FP (hex4's out at parse_string's
   sp + 36; pj_parse's q at sp + 8). ---- *)
Definition fp_sub_xW (STK sp0 : Z) (FP FP1 : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) : Prop :=
  forall a, inFP FP1 a ->
    inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
    (exists f, In f own /\ in_zr a (frame_rng lyc f)) \/ (sp0 - STK <= a < sp0).
(* ajournal_x_sub over fp_sub_xW. Proof of soundness of the fourth disjunct: the side condition is consulted only for
   the sink address 0, for block bytes and for frame / frame-shadow bytes, all below alloc_ceiling, while the caller's
   window lies at or above ly_stk_lo >= alloc_ceiling (its astk_ok); each such use is refuted. The other three
   disjuncts are handled as the record's proof handles them. *)
Lemma ajournal_x_sub_W : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1,
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
  ajournal_x (SK := SK) segs B PST ARx STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
  fp_sub_xW STK sp0 FP FP1 ly S own lyc Sc ->
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W mem md (nf ++ own) ly2 S2 Hp2 W2 mem2 md2 (k + k1).
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1
HJ HJ1 Hlo Hhi HF.
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_secs HJ) as Hsecs.
pose proof (ajx_wle HJ) as Hwle. pose proof (ajx_io HJ) as Hio. pose proof (ajx_frs HJ) as Hfrs.
pose proof (ajx_nev HJ) as Hnev. pose proof (ajx_k HJ) as Hk. pose proof (ajx_hi HJ) as F1. pose proof (ajx_blk HJ) as F2.
pose proof (ajx_img HJ) as F3. pose proof (ajx_frm HJ) as F4. pose proof (ajx_gone HJ) as Hgone.
pose proof (ajx_pres HJ) as Hpres. pose proof (ajx_stk HJ) as Hstatic. pose proof (ajx_extra HJ) as F5.
pose proof (ajx_qt HJ) as HQT. pose proof (ajx_wild HJ) as Hwild.
pose proof (ajx_ar HJ1) as HAR2. pose proof (ajx_ly HJ1) as Hly2. pose proof (ajx_secs HJ1) as Hsecs2.
pose proof (ajx_wle HJ1) as Hwle2. pose proof (ajx_io HJ1) as Hio2. pose proof (ajx_frs HJ1) as Hfrs2.
pose proof (ajx_nev HJ1) as Hnev2. pose proof (ajx_k HJ1) as Hk2. pose proof (ajx_hi HJ1) as G1. pose proof (ajx_blk HJ1) as G2.
pose proof (ajx_img HJ1) as G3. pose proof (ajx_frm HJ1) as G4. pose proof (ajx_gone HJ1) as Hgone2.
pose proof (ajx_pres HJ1) as Hpres2. pose proof (ajx_stk HJ1) as Hstatic2. pose proof (ajx_extra HJ1) as G5.
pose proof (ajx_qt HJ1) as HQT2. pose proof (ajx_wild HJ1) as Hwild2.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the fourth disjunct lies at or above alloc_ceiling *)
assert (Hwin : forall a, sp0 - STK <= a < sp0 -> alloc_ceiling <= a) by (intros a Ha; zlia).
(* a byte of a frame the caller made since its entry is below alloc_ceiling *)
assert (Hown : forall a f, In f own -> in_zr a (frame_rng lyc f) -> 4096 <= a < alloc_ceiling).
{ intros a [cidf posf] Hfo Hfr. assert (HinF : In (cidf, posf) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hfo).
  destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc cidf posf HAR HinF) as (Hg0 & Hgc & Hgh).
  unfold frame_rng, in_zr in Hfr. cbn [fst snd] in Hfr. zlia. }
split; [exact HAR2|].
split; [eapply layout_le_trans; [exact Hsecs | exact Hly | exact Hly2]|].
split; [zlia|]. split; [eapply wle_trans; eassumption|].
assert (HFo : YI16.sink_open_fp FP1 -> YI16.sink_open_fp FP).
{ intros (r & Hr & H0). destruct (HF 0 (ex_intro _ r (conj Hr H0))) as [Hf | [(b & n & Hin & _ & Hb) | [(f & Hfo & Hfr) | Hw]]].
- exact Hf.
- exfalso. pose proof (alx_blocks segs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & _). zlia.
- exfalso. pose proof (Hown 0 f Hfo Hfr). zlia.
- exfalso. pose proof (Hwin 0 Hw). zlia. }
split; [eapply aos_step_trans_fp; [exact HFo | exact Hio | exact Hio2]|].
split; [rewrite Hfrs2, Hfrs, app_assoc; reflexivity|]. split; [zlia|]. split; [zlia|].
split.
{   intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply G1; [exact Ha | zlia]. }
split.
{   intros p n i H1 H2 Hi Hnf.
assert (Hc2 : In (p, n) (ablocks B lyc Sc)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [exact Hc|].
exfalso. exact (Hnf (Hgone p n i H1 Hc Hi)). }
pose proof (alx_blocks segs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hc2) as (_ & _ & Hcb & _).
rewrite <- (F2 p n i H1 Hc2 Hi Hnf). apply (G2 p n i Hc2); [exact H2 | exact Hi |].
intros Hf1. destruct (HF _ Hf1) as [Hf | [(b & m & Hbin & Hb0 & Hr) | [(f & Hfo & Hfr) | Hw]]]; [exact (Hnf Hf)| | |pose proof (Hwin _ Hw); zlia].
- assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
  pose proof (sep_blocks_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc b m p n HAR Hbin Hc2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- apply (frame_not_block_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc f p n (p + i) HAR);
  [rewrite Hfrs; apply in_or_app; left; exact Hfo | exact Hc2 | exact Hfr | zlia]. }
split.
{   intros a Hi Hns He Hpst Hsp. rewrite <- (F3 a Hi Hns He Hpst Hsp). apply (G3 a Hi Hns He Hpst). intros Ho1. exact (Hsp (HFo Ho1)). }
split.
{   intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
assert (Efr : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(rewrite <- Efr; zlia)).
pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(rewrite <- Efr; zlia)).
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
apply (G4 cid pos a HinC).
- unfold frame_rng in *. cbn [fst snd] in *. rewrite Efr. exact Hr.
- intros Hf1. destruct (HF _ Hf1) as [Hf | [(b & m & Hbin & Hb0 & Hrb) | [([cidf posf] & Hfo & Hfr) | Hw]]]; [exact (Hnf Hf)| | |].
  + destruct (alx_blocks segs B ARx LAWS lyc Sc Hpc Wc memc mdc b m HAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
    pose proof (sep_block_frame_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
    unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *. rewrite Efr in Hd, Hf0, Hfc, Hfh.
    destruct Hr as [Hr|Hr]; zlia.
  + (* the caller's own new frame (cidf, posf) and an entry frame (cid, pos) are two places of frames Sc *)
    assert (HinF : In (cidf, posf) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hfo).
    destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc cidf posf HAR HinF) as (Hg0 & Hgc & Hgh).
    destruct (in_split _ _ Hfo) as (o1 & o2 & Eo). destruct (in_split _ _ Hin) as (s1 & s2 & Es).
    assert (Esc : frames Sc = o1 ++ (cidf, posf) :: (o2 ++ s1) ++ (cid, pos) :: s2)
      by (rewrite Hfrs, Eo, Es, <- !app_assoc; reflexivity).
    pose proof (sep_frames_pos_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ _ HAR Esc) as Hd.
    unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *. rewrite Efr in Hd, Hf0, Hfc, Hfh.
    destruct Hr as [Hr|Hr]; zlia.
  + pose proof (Hwin _ Hw). unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. rewrite <- Efr in *.
    destruct Hr as [Hr|Hr]; zlia. }
split.
{   intros p n i H1 H2 Hi.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [|exact (Hgone p n i H1 Hc Hi)].
assert (Hf1 : inFP FP1 (p + i)) by (apply (Hgone2 p n i Hc); [exact H2 | exact Hi]).
pose proof (alx_blocks segs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hc) as (_ & _ & Hcb & _).
destruct (HF _ Hf1) as [Hf | [(b & m & Hbin & Hb0 & Hr) | [(f & Hfo & Hfr) | Hw]]]; [exact Hf| | |exfalso; pose proof (Hwin _ Hw); zlia].
- assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
  pose proof (sep_blocks_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc b m p n HAR Hbin Hc Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- exfalso. apply (frame_not_block_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc f p n (p + i) HAR);
  [rewrite Hfrs; apply in_or_app; left; exact Hfo | exact Hc | exact Hfr | zlia]. }
split.
{   intros a Ha.
destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb]; [|destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2]; [apply Hpres2; zlia|]].
- eapply apresent_transfer; [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; zlia | apply Hpres; exact Ha].
- eapply apresent_transfer; [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; zlia | apply Hpres; exact Ha]. }
split; [exact Hstatic|]. split; [|split; [exact HQT2 | exact (wild_incl_trans _ _ _ _ _ Hwild2 Hwild)]].
{   intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
apply G5; [rewrite Eextra; exact HXa | exact He]. }
Qed.

(* the call: the walk stands at the callee's entry (pc = the callee, ra = its return site raw) with its journal at the
   current memory; the callee's text gives fpostW_x at its widened window (STK1 + e1) (sp + e1), which lies inside
   the walk's window; fwin_x and afn_pre_x of the callee follow from the journal. The conclusion is aj_call_x's, with
   the callee's widened journal and extension clause in place of its plain journal. *)
Lemma aj_call_xW : forall W (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k
  STK1 e1 FP1 (o : Z) raw ch1
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 -> fwin_x lyc W regsc memc e1 ->
   SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (fpostW_x STK1 e1 FP1 regsc lyc Sc Hpc W memc mdc K)) ->
  fp_sub_xW STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_x (SK := SK) segs B PST ARx (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 K
  HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (ajx_ly HJ) as Hly. pose proof (ajx_pres HJ) as Hpres.
pose proof (ajx_stk HJ) as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (HPRE : afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1).
{ eapply (afn_pre_x_at (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp. exact Hch. }
assert (HWIN : fwin_x lyc W regsc memc e1).
{ split; [exact He0|]. split; [exact He16|]. split; [rewrite Hsp, Etop; zlia|].
  intros a Ha. apply Hpres. rewrite Hsp in Ha. zlia. }
eapply SRr_mono; [exact (Hcallee HPRE HWIN)|].
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HX & HP & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [rewrite Hra; reflexivity|]. rewrite Hsp in HJ1, HX.
split; [| split; [exact HJ1 | split; [exact HX | split; [exact HP | exact HK]]]].
change own with ([] ++ own). eapply ajournal_x_sub_W; [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.
(* the window AND float twin (check_as_written calling ex_value): the callee's text gives fpostWF_x; the continuation
   runs at the callee's float state fx' (frm back to 0, fs0-fs11 kept), as c-omx-alloc's aj_call_xF (YCbqGcall.v:106,
   0698be97255); a walk moves its st_ok there with YCbqGcall's st_ok_restrict_xfx. *)
Lemma aj_call_xWF : forall W (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k
  STK1 e1 FP1 (o : Z) raw ch1
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 -> fwin_x lyc W regsc memc e1 ->
   SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (fpostWF_x STK1 e1 FP1 regsc lyc Sc Hpc W memc mdc K)) ->
  fp_sub_xW STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
       ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_x (SK := SK) segs B PST ARx (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 K
  HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (ajx_ly HJ) as Hly. pose proof (ajx_pres HJ) as Hpres.
pose proof (ajx_stk HJ) as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (HPRE : afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1).
{ eapply (afn_pre_x_at (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp. exact Hch. }
assert (HWIN : fwin_x lyc W regsc memc e1).
{ split; [exact He0|]. split; [exact He16|]. split; [rewrite Hsp, Etop; zlia|].
  intros a Ha. apply Hpres. rewrite Hsp in Ha. zlia. }
eapply SRr_mono; [exact (Hcallee HPRE HWIN)|].
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ1 & HX & HP & HK).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1. split; [rewrite Hra; reflexivity|]. rewrite Hsp in HJ1, HX.
split; [exact HFZ|]. split; [exact HFK|].
split; [| split; [exact HJ1 | split; [exact HX | split; [exact HP | exact HK]]]].
change own with ([] ++ own). eapply ajournal_x_sub_W; [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.
End l.
End cj.
