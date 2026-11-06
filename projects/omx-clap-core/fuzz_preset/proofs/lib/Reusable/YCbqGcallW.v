(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the CALLER-WINDOW call kit over YCbqG.v's journal
   ajournal_x (allocator invariant a parameter ARx, ghost head set Hp after S, program statics PST), generic: no image
   class, no address, no ledger. Credit: WalkS4, lib/A/Prog/PRW_CallerJ.v at 85a188622c5 (statements and proofs taken
   from there; changes below). Donors there: cj_kept from cgif_file_fuzzer lib/YC20.v:311-325 tlzw_kept and
   lib/YC8n.v:272-287 tlzw_kept_of_journal (origin/release/pau-projects-recipes), generalised to ajournal_x's keep
   clauses; aj_call_xW from YCbqGcall.v aj_call_x (cgif YCbq.v:1845-1883 aj_call, origin/ossv/recipes).
   What a walk of a function in the caller-window form needs:
   - fwin_x / fpostW_x / fpostWF_x: lib/A/PRH_Base.v's fwin / fpostW / fpostWF (K0) restated with the image segs and
     the statics PST as parameters, same bodies: PRH_Base.fpostW B ARx SK STK d FP .. is
     fpostW_x (SK := SK) pa_segs B prh_pst ARx STK d FP .. by unfolding (this file does not Require lib/A).
   - START: ajournal_x_init_W, the widened journal (STK + e) (sp + e) at the entry state.
   - CALL of a caller-window callee: aj_call_xW / aj_call_xWF (callee state in mkst form), aj_call_xW_sp /
     aj_call_xWF_sp (the entry form of YCbqGcall.v's aj_call_x_sp: st_ok, ss_resv, the machine state ms).
     The footprint side condition is YCbqG.v's own fp_sub_x (h-hpreset-7 9052c7a7d74 :688-691), whose fourth
     disjunct `sp0 - STK <= a < sp0` is the caller's window: WalkS4's fp_sub_xW is that predicate, so this file
     no longer states one and ajournal_x_sub_W (the name WalkS4's callers use) is YCbqG's ajournal_x_sub.
   - vrd_call_W: h-verbs-3's lib/A/VrdArm.v call rule (6d4cddbdff5), premise shape kept, as a corollary of
     aj_call_xW_sp at e1 := - o.
   - aj_call_xWF_d: WalkH6's caller-window float call rule (h-walk-identity's S8aCallW.v aj_call_xWF), verbatim: no
     fwin_x for the callee and no window-kept clause on either side.
   - END: cj_kept (the keep clauses of ajournal_x relative to the entry, the walker's window and its written cells OR
     exempted) across stretches (cj_kept_exec) and calls (cj_kept_of_journal), chained (cj_kept_trans), closed by
     fpostW_x_of_kept / fpostWF_x_of_kept; fpostW_x_of_apost: apost_base_x is fpostW_x at e = 0.
   Numerals: 16, 4096, 8, 4 and 2 ^ 64 are LENGTH; 0 is LENGTH (the empty window e = 0) or DERIVED (event count);
   register numbers 1, 3, 4 (ra, gp, tp) are WORD. No address literal; no image constant. *)
(* Modified by Theorem Labs, 2026-10: the kit over a world relation R (suffix R). A free or realloc of a live block can
   hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle with its journal at that
   relation (YCbqG.v ajournal_xR). cj_keptR is cj_kept with the world conjunct R W W2 (a copy of the body; the guard
   cj_kept_R_wle shows by reflexivity that cj_kept is cj_keptR at wle). The R forms of cj_kept_refl / cj_kept_exec /
   ajournal_x_init_W take R and its reflexivity, of cj_kept_trans / ajournal_x_sub_W R and its transitivity, of
   cj_kept_of_journal / fpostW_x_of_apost / fpostW_x_of_kept / fpostWF_x_of_kept R alone; the call rules
   aj_call_xWR / aj_call_xW_spR / aj_call_xWFR / aj_call_xWF_spR / vrd_call_WR / aj_call_xWF_dR take R and both laws
   first, then the plain rule's binders, with the journals, the callee's post (fpostW_xR / fpostWF_xR) and the
   conclusion at R. Each plain lemma is its R form at wle (wle_refl / wle_trans); its statement is unchanged.
   fpostW_x_R_lift: a plain fpostW_x (journal at wle) is fpostW_xR at every R that contains wle. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section cj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
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
(* the two posts over a world relation R: COPIES of fpostW_x's / fpostWF_x's bodies with the journal at R
   (ajournal_xR R). The plain bodies stay as they are, because proof lines in other files unfold them and read the
   body; fpostW_x_R_wle / fpostWF_x_R_wle (by reflexivity) check that each plain post IS its R form at wle, so the
   copies cannot drift. *)
Definition fpostW_xR (R : world segs -> world segs -> Prop) (STK d : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S
  (Hp : list Z) (W : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' Hp' regs' mem' md' k,
    c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
    ajournal_xR (SK := SK) segs B PST ARx R (STK + d) (spZ regs + d) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
    (forall a, spZ regs <= a < spZ regs + d -> ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Lemma fpostW_x_R_wle : forall STK d FP regs ly S Hp W mem md Q,
  fpostW_x STK d FP regs ly S Hp W mem md Q = fpostW_xR (@wle segs) STK d FP regs ly S Hp W mem md Q.
Proof. reflexivity. Qed.
(* A PLAIN CALLEE IN A CALLER OVER R: a callee text that concludes fpostW_x (its journal at wle) concludes the R form
   at every R that contains wle (YCbqG.v ajournal_xwR_mono on the journal conjunct; the fpostW_x twin of YCbqG.v
   apost_base_x_R_lift) *)
Lemma fpostW_x_R_lift : forall (R : world segs -> world segs -> Prop), (forall W W', wle W W' -> R W W') ->
  forall STK d FP regs ly S Hp W mem md Q W' c',
  fpostW_x STK d FP regs ly S Hp W mem md Q W' c' -> fpostW_xR R STK d FP regs ly S Hp W mem md Q W' c'.
Proof.
intros R Hsub STK d FP regs ly S Hp W mem md Q W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HX & Hpr & HQ).
exists ly', S', Hp', regs', mem', md', k. split; [exact Hc|].
split; [exact (ajournal_xwR_mono (SK := SK) segs B PST ARx (@wle segs) R Hsub (STK + d) (spZ regs + d) FP ly S Hp W
                 mem md [] ly' S' Hp' W' mem' md' k [] HJ)
       | split; [exact HX | split; [exact Hpr | exact HQ]]].
Qed.
Definition fpostWF_xR (R : world segs -> world segs -> Prop) (STK d : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S
  (Hp : list Z) (W : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k,
    c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
    ajournal_xR (SK := SK) segs B PST ARx R (STK + d) (spZ regs + d) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
    (forall a, spZ regs <= a < spZ regs + d -> ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Lemma fpostWF_x_R_wle : forall STK d FP regs ly S Hp W mem md Q,
  fpostWF_x STK d FP regs ly S Hp W mem md Q = fpostWF_xR (@wle segs) STK d FP regs ly S Hp W mem md Q.
Proof. reflexivity. Qed.

(* ---- what a walk leaves relative to a state (lyc Sc W memc mdc) of its own, at a later state (ly2 S2 W2 mem2 md2):
   ajournal_x's keep clauses (YCbqG.v ajournal_x), with the walker's own window [sp - STKf, sp) and its written cells
   OR (the stack cells fpostW's FP names, or all of FP) exempted; FPc: the heap bytes (and sink) written in blocks live
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
(* cj_kept over a world relation R: a COPY of cj_kept's body with the world conjunct R W W2. The plain body stays as
   it is (walks destruct it by position); cj_kept_R_wle checks by reflexivity that cj_kept is cj_keptR at wle. *)
Definition cj_keptR (R : world segs -> world segs -> Prop) (STKf sp : Z) (OR FPc : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
  (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  layout_le (length (st_secs Sc)) lyc ly2 /\ (length (st_secs Sc) <= length (st_secs S2))%nat /\
  R W W2 /\ aos_step FPc mdc md2 /\ frames S2 = frames Sc /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STKf <= a < sp) -> ~ inFP OR a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall p m i, In (p, m) (ablocks B lyc Sc) -> In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
     ~ inFP FPc (p + i) -> ~ inFP OR (p + i) ->
     aview segs (w_H W2) mem2 (p + i) = aview segs (w_H W) memc (p + i)) /\
  (forall p m i, In (p, m) (ablocks B lyc Sc) -> ~ In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
     inFP FPc (p + i)) /\
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> fp_spares (SK := SK) FPc a -> ~ inFP OR a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ inFP FPc a -> ~ inFP OR a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall a, Exists (in_zr a) (ly_extra lyc) -> ~ (as_errno B <= a < as_errno B + 4) -> ~ inFP OR a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Lemma cj_kept_R_wle : forall STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2,
  cj_kept STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 =
  cj_keptR (@wle segs) STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2.
Proof. reflexivity. Qed.

(* cj_kept_refl over a reflexive world relation R *)
Lemma cj_kept_reflR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  forall STKf sp OR FPc lyc Sc W memc mdc,
  cj_keptR R STKf sp OR FPc lyc Sc W memc mdc lyc Sc W memc mdc.
Proof.
intros R Rr. intros. split; [apply layout_le_refl|]. split; [lia|]. split; [apply Rr|]. split; [apply aos_step_refl|].
split; [reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros p m i H1 H2; exfalso; exact (H2 H1)|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. intros; reflexivity.
Qed.

(* nothing changed *)
Lemma cj_kept_refl : forall STKf sp OR FPc lyc Sc W memc mdc,
  cj_kept STKf sp OR FPc lyc Sc W memc mdc lyc Sc W memc mdc.
Proof. exact (cj_kept_reflR (@wle segs) (wle_refl segs)). Qed.

(* cj_kept_of_journal over a world relation R *)
Lemma cj_kept_of_journalR : forall (R : world segs -> world segs -> Prop),
  forall STKf sp FPc lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 OR,
  ajournal_xR (SK := SK) segs B PST ARx R STKf sp FPc lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  cj_keptR R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2.
Proof.
intros R STKf sp FPc lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 OR HJ.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle.
pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2.
pose proof (ajxR_img HJ) as F3. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_gone HJ) as Hgone.
pose proof (ajxR_extra HJ) as F5.
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [rewrite Hfrs; reflexivity|].
split; [intros a Ha Hw _; exact (F1 a Ha Hw)|].
split; [intros p m i H1 H2 Hi Hf _; exact (F2 p m i H1 H2 Hi Hf)|].
split; [exact Hgone|].
split; [intros a Hi Hn He Hp Hs _; exact (F3 a Hi Hn He Hp Hs)|].
split; [intros cid pos a Hin Hr Hf _; exact (F4 cid pos a Hin Hr Hf)|].
intros a Hx He _. exact (F5 a Hx He).
Qed.

(* a stretch a journal from the first state covers (a callee's post from aj_call_x / aj_call_xW, window STKf below
   sp, own = []) is kept for every OR (cgif YC8n.v:272-287 tlzw_kept_of_journal) *)
Lemma cj_kept_of_journal : forall STKf sp FPc lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 OR,
  ajournal_x (SK := SK) segs B PST ARx STKf sp FPc lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  cj_kept STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2.
Proof. exact (cj_kept_of_journalR (@wle segs)). Qed.

(* fpostW_x_of_apost over a world relation R *)
Lemma fpostW_x_of_apostR : forall (R : world segs -> world segs -> Prop),
  forall STK FP regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  apost_base_xR (SK := SK) segs B PST ARx R STK FP regs ly S Hp W mem md Q W' c' ->
  fpostW_xR R STK 0 FP regs ly S Hp W mem md Q W' c'.
Proof.
intros R STK FP regs ly S Hp W mem md Q W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HP & HQ).
exists ly', S', Hp', regs', mem', md', k. split; [exact Hc|]. rewrite !Z.add_0_r. split; [exact HJ|].
split; [intros a Ha; exfalso; lia | split; [exact HP | exact HQ]].
Qed.

(* an apost_base_x text (PRH_Base fpost) is the caller-window post at e = 0, so aj_call_xW serves both forms *)
Lemma fpostW_x_of_apost : forall STK FP regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  apost_base_x (SK := SK) segs B PST ARx STK FP regs ly S Hp W mem md Q W' c' ->
  fpostW_x STK 0 FP regs ly S Hp W mem md Q W' c'.
Proof. exact (fpostW_x_of_apostR (@wle segs)). Qed.

(* ajournal_x_init_W over a reflexive world relation R *)
Lemma ajournal_x_init_WR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  forall STK e FP ly S Hp W regs mem md ch,
  afn_pre_x segs B ARx STK ly S Hp W regs mem md ch -> fwin_x ly W regs mem e ->
  ajournal_xR (SK := SK) segs B PST ARx R (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly S Hp W mem md 0.
Proof.
intros R Rr STK e FP ly S Hp W regs mem md ch (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) (He0 & He16 & Hetop & Hepres).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
split; [exact HAR|]. split; [apply layout_le_refl|]. split; [zlia|]. split; [apply Rr|]. split; [apply aos_step_refl|].
split; [reflexivity|]. split; [zlia|]. split; [zlia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros p n i H1 H2; exfalso; exact (H2 H1)|].
split.
{ intros a Ha. destruct (Z_lt_le_dec a (spZ regs)) as [Hl|Hl]; [apply Hpres; zlia | apply Hepres; zlia]. }
split; [|split; [intros; reflexivity | split; [exact HQT | apply wild_part_same]]].
unfold astk_ok. repeat split; try zlia. all: rewrite Z.add_mod, Hal, He16 by zlia; reflexivity.
Qed.

(* ---- START of a caller-window walk: the widened journal at the entry state ---- *)
Lemma ajournal_x_init_W : forall STK e FP ly S Hp W regs mem md ch,
  afn_pre_x segs B ARx STK ly S Hp W regs mem md ch -> fwin_x ly W regs mem e ->
  ajournal_x (SK := SK) segs B PST ARx (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly S Hp W mem md 0.
Proof. exact (ajournal_x_init_WR (@wle segs) (wle_refl segs)). Qed.

(* fpostW_x_of_kept / fpostWF_x_of_kept over a world relation R *)
Lemma fpostW_x_of_keptR : forall (R : world segs -> world segs -> Prop),
  forall STK e FP regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k,
  0 <= STK ->
  ajournal_xR (SK := SK) segs B PST ARx R (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k ->
  cj_keptR R STK (spZ regs) OR FPs ly S W mem md ly2 S2 W2 mem2 md2 ->
  (forall a, inFP OR a -> inFP FP a) ->
  aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  fpostW_xR R STK e FP regs ly S Hp W mem md Q W2
    (mkCfg (YK11.mkst regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros R STK e FP regs ly S Hp W mem md Q OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k HSTK HJ HK HOR HP HQ.
pose proof (ajxR_stk HJ) as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HK as (_ & _ & _ & _ & _ & K1 & _).
exists ly2, S2, Hp2, regs2, mem2, md2, k. split; [reflexivity|]. split; [exact HJ|].
split; [|split; [exact HP | exact HQ]].
intros a Ha Hf. apply K1; [zlia | zlia | intros Ho; exact (Hf (HOR a Ho))].
Qed.
Lemma fpostWF_x_of_keptR : forall (R : world segs -> world segs -> Prop),
  forall STK e FP regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k (fx' : YK11.FPState),
  frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' -> 0 <= STK ->
  ajournal_xR (SK := SK) segs B PST ARx R (STK + e) (spZ regs + e) FP ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k ->
  cj_keptR R STK (spZ regs) OR FPs ly S W mem md ly2 S2 W2 mem2 md2 ->
  (forall a, inFP OR a -> inFP FP a) ->
  aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  fpostWF_xR R STK e FP regs ly S Hp W mem md Q W2
    (mkCfg (@YK11.mkst fx' regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros R STK e FP regs ly S Hp W mem md Q OR FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k fx' Hz Hkf HSTK HJ HK HOR HP HQ.
pose proof (ajxR_stk HJ) as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HK as (_ & _ & _ & _ & _ & K1 & _).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k. split; [reflexivity|]. split; [exact Hz|]. split; [exact Hkf|].
split; [exact HJ|]. split; [|split; [exact HP | exact HQ]].
intros a Ha Hf. apply K1; [zlia | zlia | intros Ho; exact (Hf (HOR a Ho))].
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
Proof. exact (fpostW_x_of_keptR (@wle segs)). Qed.
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
Proof. exact (fpostWF_x_of_keptR (@wle segs)). Qed.

(* The side condition on a callee's footprint FP1 is YCbqG.v's fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc: the
   caller's FP, a block the callee made and kept, a slot of a frame the caller made since its entry (own), or a byte
   of the caller's own window [sp0 - STK, sp0) (hex4's out at parse_string's sp + 36; pj_parse's q at sp + 8).
   WalkS4's fp_sub_xW had exactly this body, so it is dropped here and every rule below takes fp_sub_x. *)

Section l.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
#[local] Abbreviation AJR R := (ajournal_xR (SK := SK) segs B PST ARx R).
(* cj_kept_trans below over a transitive world relation R *)
Lemma cj_kept_transR : forall (R : world segs -> world segs -> Prop), (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall STK1 sp1 STK2 sp2 OR FP1 FP2 FP3
  lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 ly3 S3 W3 mem3 md3,
  cj_keptR R STK1 sp1 OR FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 ->
  cj_keptR R STK2 sp2 OR FP2 ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md3 ->
  ARx lyc Sc Hpc W memc mdc -> ARx ly2 S2 Hp2 W2 mem2 md2 ->
  sp1 - STK1 <= sp2 - STK2 -> sp2 <= sp1 ->
  (forall a, inFP FP1 a -> inFP FP3 a \/ alloc_ceiling <= a) ->
  (forall a, inFP FP2 a -> inFP FP3 a \/ in_tmp_block (ablocks B lyc Sc) (ablocks B ly2 S2) a \/ alloc_ceiling <= a) ->
  cj_keptR R STK1 sp1 OR FP3 lyc Sc W memc mdc ly3 S3 W3 mem3 md3.
Proof.
intros R Rt STK1 sp1 STK2 sp2 OR FP1 FP2 FP3 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 ly3 S3 W3 mem3 md3
  (Hly & Hsecs & Hwle & Hio & Hfrs & F1 & F2 & Hgone & F3 & F4 & F5)
  (Hly2 & Hsecs2 & Hwle2 & Hio2 & Hfrs2 & G1 & G2 & Hgone2 & G3 & G4 & G5) HARc HAR2 Hlo Hhi H13 H23.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hs13 : YI16.sink_open_fp FP1 -> YI16.sink_open_fp FP3).
{ intros (r & Hr & H0). destruct (H13 0 (ex_intro _ r (conj Hr H0))) as [Hf | Hc]; [exact Hf | zlia]. }
assert (Hs23 : YI16.sink_open_fp FP2 -> YI16.sink_open_fp FP3).
{ intros (r & Hr & H0). destruct (H23 0 (ex_intro _ r (conj Hr H0))) as [Hf | [(b & m & Hbin & _ & Hb) | Hc]]; [exact Hf| |zlia].
  exfalso. pose proof (alx_blocks segs B ARx LAWS _ _ _ _ _ _ _ _ HAR2 Hbin) as (_ & H4096 & _). zlia. }
assert (Hblo : forall p m i, In (p, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> p + i < alloc_ceiling).
{ intros p m i H1 Hi. pose proof (alx_blocks segs B ARx LAWS _ _ _ _ _ _ _ _ HARc H1) as (_ & _ & Hc & _). zlia. }
assert (Htmp : forall p m i, In (p, m) (ablocks B lyc Sc) -> In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
  ~ in_tmp_block (ablocks B lyc Sc) (ablocks B ly2 S2) (p + i)).
{ intros p m i H1 H2 Hi (b & m' & Hbin & Hb0 & Hr).
  assert (Hne : (b, m') <> (p, m)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
  pose proof (sep_blocks_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m' p m HAR2 Hbin H2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
split; [eapply layout_le_trans; [exact Hsecs | exact Hly | exact Hly2]|].
split; [zlia|]. split; [exact (Rt _ _ _ Hwle Hwle2)|].
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
Proof. exact (cj_kept_transR (@wle segs) (wle_trans segs)). Qed.

(* cj_kept_exec below over a reflexive world relation R *)
Lemma cj_kept_execR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  forall STKf sp OR FPs lyc Sc Hpc W memc mdc memc' mdc' (Wr : Z -> Prop),
  ARx lyc Sc Hpc W memc mdc ->
  alloc_ceiling <= ly_stk_lo lyc -> ly_stk_lo lyc <= sp - STKf -> sp <= ly_stk_hi lyc ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H W) memc' x = mrestrict (w_H W) memc x) ->
  (forall a, Wr a -> (sp - STKf <= a < sp) \/ inFP OR a \/
     (inFP FPs a /\ exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m)) ->
  same_but_materialized mdc mdc' ->
  cj_keptR R STKf sp OR FPs lyc Sc W memc mdc lyc Sc W memc' mdc'.
Proof.
intros R Rr STKf sp OR FPs lyc Sc Hpc W memc mdc memc' mdc' Wr HAR Hcl Hwlo Hwhi Hfr HW Hsame.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H W) memc' a = aview segs (w_H W) memc a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
split; [apply layout_le_refl|]. split; [lia|]. split; [apply Rr|].
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
Proof. exact (cj_kept_execR (@wle segs) (wle_refl segs)). Qed.

(* ajournal_x_sub_W below over a transitive world relation R: YCbqG.v's ajournal_x_subR *)
Lemma ajournal_x_sub_WR : forall (R : world segs -> world segs -> Prop), (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1,
  AJR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
  AJR R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  AJR R STK sp0 FP ly S Hp W mem md (nf ++ own) ly2 S2 Hp2 W2 mem2 md2 (k + k1).
Proof.
intros R Rt STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 HJ HJ1 Hlo Hhi HF.
exact (ajournal_x_subR (SK := SK) segs B PST ARx LAWS segs_low R Rt STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k
  STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 HJ HJ1 Hlo Hhi HF).
Qed.

(* ajournal_x_sub at the footprint predicate the window rules take. WalkS4 proved this separately because the engine
   then asked a narrower side condition; at YCbqG 9052c7a7d74 the engine asks fp_sub_x itself, so this is
   ajournal_x_sub under the name WalkS4's callers use. *)
Lemma ajournal_x_sub_W : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1,
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
  ajournal_x (SK := SK) segs B PST ARx STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W mem md (nf ++ own) ly2 S2 Hp2 W2 mem2 md2 (k + k1).
Proof. exact (ajournal_x_sub_WR (@wle segs) (wle_trans segs)). Qed.

(* aj_call_xW below over a world relation R: R and its two laws first; the journals, the callee's post fpostW_xR and
   the conclusion at R *)
Lemma aj_call_xWR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k
  STK1 e1 FP1 (o : Z) raw ch1
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 -> fwin_x lyc W regsc memc e1 ->
   SRrG segs R W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (fpostW_xR R STK1 e1 FP1 regsc lyc Sc Hpc W memc mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs R W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       AJR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJR R (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 K
  HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (HPRE : afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1).
{ eapply (afn_pre_x_atR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp. exact Hch. }
assert (HWIN : fwin_x lyc W regsc memc e1).
{ split; [exact He0|]. split; [exact He16|]. split; [rewrite Hsp, Etop; zlia|].
  intros a Ha. apply Hpres. rewrite Hsp in Ha. zlia. }
eapply (SRrG_mono segs R); [exact (Hcallee HPRE HWIN)|].
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HX & HP & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [rewrite Hra; reflexivity|]. rewrite Hsp in HJ1, HX.
split; [| split; [exact HJ1 | split; [exact HX | split; [exact HP | exact HK]]]].
change own with ([] ++ own). eapply (ajournal_x_sub_WR R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
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
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_x (SK := SK) segs B PST ARx (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xWR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* aj_call_xW_sp below over a world relation R *)
Lemma aj_call_xW_spR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 (o : Z) raw ch1
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 -> fwin_x lyc W (ms_regs ms) (ms_mem ms) e1 ->
   SRrG segs R W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom segs)) mdc)
     (fpostW_xR R STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs R W (mkCfg ms mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       AJR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJR R (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 K
  HS Hrv HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (aj_call_xWR R Rr Rt W (ms_regs ms) (ms_mem ms) (ss_pc ss) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k
  STK1 e1 FP1 o raw ch1 K HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF) as G.
rewrite <- (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv) in G. exact G.
Qed.
(* aj_call_xW in the entry form of YCbqGcall.v's aj_call_x_sp: the walk's machine state ms with st_ok and ss_resv
   (the callee's text runs from ms written in mkst form at the symbolic pc); premises and conclusion otherwise
   aj_call_xW's at regsc := ms_regs ms, memc := ms_mem ms, pc := ss_pc ss *)
Lemma aj_call_xW_sp : forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 (o : Z) raw ch1
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 -> fwin_x lyc W (ms_regs ms) (ms_mem ms) e1 ->
   SRr segs W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom segs)) mdc)
     (fpostW_x STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg ms mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_x (SK := SK) segs B PST ARx (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xW_spR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* aj_call_xWF below over a world relation R *)
Lemma aj_call_xWFR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k
  STK1 e1 FP1 (o : Z) raw ch1
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 -> fwin_x lyc W regsc memc e1 ->
   SRrG segs R W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (fpostWF_xR R STK1 e1 FP1 regsc lyc Sc Hpc W memc mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs R W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
       AJR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJR R (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 K
  HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (HPRE : afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1).
{ eapply (afn_pre_x_atR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp. exact Hch. }
assert (HWIN : fwin_x lyc W regsc memc e1).
{ split; [exact He0|]. split; [exact He16|]. split; [rewrite Hsp, Etop; zlia|].
  intros a Ha. apply Hpres. rewrite Hsp in Ha. zlia. }
eapply (SRrG_mono segs R); [exact (Hcallee HPRE HWIN)|].
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ1 & HX & HP & HK).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1. split; [rewrite Hra; reflexivity|]. rewrite Hsp in HJ1, HX.
split; [exact HFZ|]. split; [exact HFK|].
split; [| split; [exact HJ1 | split; [exact HX | split; [exact HP | exact HK]]]].
change own with ([] ++ own). eapply (ajournal_x_sub_WR R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.
(* the window AND float twin (check_as_written calling ex_value): the callee's text gives fpostWF_x; the continuation
   runs at the callee's float state fx' (frm back to 0, fs0-fs11 kept), as YCbqGcall.v's aj_call_xF; a walk moves its
   st_ok there with YCbqGcall.v's st_ok_restrict_xfx. *)
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
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
       ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_x (SK := SK) segs B PST ARx (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xWFR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* aj_call_xWF_sp below over a world relation R *)
Lemma aj_call_xWF_spR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 (o : Z) raw ch1
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 -> fwin_x lyc W (ms_regs ms) (ms_mem ms) e1 ->
   SRrG segs R W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom segs)) mdc)
     (fpostWF_xR R STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs R W (mkCfg ms mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
       AJR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJR R (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 K
  HS Hrv HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (aj_call_xWFR R Rr Rt W (ms_regs ms) (ms_mem ms) (ss_pc ss) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k
  STK1 e1 FP1 o raw ch1 K HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch Hcallee HF) as G.
rewrite <- (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv) in G. exact G.
Qed.
(* aj_call_xWF in aj_call_xW_sp's entry form *)
Lemma aj_call_xWF_sp : forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 (o : Z) raw ch1
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  0 <= e1 -> e1 mod 16 = 0 -> o + e1 <= 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 -> fwin_x lyc W (ms_regs ms) (ms_mem ms) e1 ->
   SRr segs W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom segs)) mdc)
     (fpostWF_x STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg ms mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
       ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_x (SK := SK) segs B PST ARx (STK1 + e1) (sp0 + o + e1) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 + o + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xWF_spR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* vrd_call_W below over a world relation R *)
Lemma vrd_call_WR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 (o : Z) raw ch1
    (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> o + e1 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRrG segs R W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom segs)) mdc)
     (fpostW_xR R STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (exists f, In f own /\ in_zr a (frame_rng lyc f))) ->
  SRrG segs R W (mkCfg ms mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       AJR R STK sp0 FP ly S Hp W0 mem md own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       (forall a, sp0 + o <= a < sp0 -> ~ inFP FP1 a ->
          aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 Q
  HS Hrv HJ Hsp Hal Hneg Hstk1 Hbud Hoe Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
assert (He0 : 0 <= e1) by lia.
assert (He16 : e1 mod 16 = 0) by (replace e1 with (- o) by lia; apply Z.mod_opp_l_z; [lia | exact Hal]).
assert (Hetop : o + e1 <= 0) by lia.
assert (HFW : fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc).
{ intros a Ha. destruct (HF a Ha) as [H1 | [H2 | H3]]; [left | right; left | right; right; left]; assumption. }
eapply (SRrG_mono segs R); [exact (aj_call_xW_spR R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 Q
  HS Hrv HJ Hsp Hal Hneg Hstk1 Hbud He0 He16 Hetop Hgp Htp Hra Hraw Hra4 Hch (fun HPRE _ => Hcallee HPRE) HFW)|].
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc & HJ2 & _ & HX & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [exact Hc|]. split; [exact HJ2|].
split; [|split; [exact HP | exact HQ]]. intros a Ha Hn. apply HX; [lia | exact Hn].
Qed.

(* h-verbs-3's call rule (lib/A/VrdArm.v:164-205 at 6d4cddbdff5, there over PRH_Base.fpostW at image A, PST :=
   prh_pst), premise shape kept: the caller's journal is already in window form, so the callee's window top
   sp0 + o + e1 is the caller's sp0 (o + e1 = 0); the callee's text needs no fwin_x; its footprint takes YCbqG.v's
   first three disjuncts; the callee's journal is dropped from the conclusion. It is aj_call_xW_sp at e1 := - o. *)
Lemma vrd_call_W :
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 (o : Z) raw ch1
    (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> o + e1 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr segs W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom segs)) mdc)
     (fpostW_x STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (exists f, In f own /\ in_zr a (frame_rng lyc f))) ->
  SRr segs W (mkCfg ms mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       (forall a, sp0 + o <= a < sp0 -> ~ inFP FP1 a ->
          aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (vrd_call_WR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* aj_call_xWF_d below over a world relation R: the journals and the callee's post at R *)
Lemma aj_call_xWF_dR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o d : Z) spw raw ch1
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> 0 <= d -> o + d <= 0 ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
 SRrG segs R W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
   (fun W' c' => exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k',
      c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr (ms_regs ms) 1) mem' (YK11.seg_rom segs)) md' /\
      frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
      AJR R (STK1 + d) (spZ (ms_regs ms) + d) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly' S' Hp' W' mem' md' k' /\
      aregs_preserved (ms_regs ms) regs' /\ Q ly' S' Hp' W' regs' mem' md')) ->
fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
SRrG segs R W (mkCfg ms mdc)
 (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
  frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
  AJR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
  AJR R (STK1 + d) (sp0 + o + d) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rr Rt W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o d spw raw ch1 Q
HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hd0 Hdo Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (ajxR_stk HJ) as (_ & _ & Hceil & Hslo & Hshi & H47 & _). pose proof (ajxR_qt HJ) as HQT.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv).
eapply (SRrG_mono segs R).
{ apply Hcallee. eapply (afn_pre_x_atR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k
(ms_regs ms) STK1 o ch1); try eassumption.
- rewrite Hra. exact Hraw.
- unfold raZ. rewrite Hra. exact Hra4.
- rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ1 & HP & HQ).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|].
split; [exact HFZ|]. split; [exact HFK|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own). eapply (ajournal_x_subR segs B PST ARx LAWS segs_low R Rt); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.
(* WalkH6's caller-window float call rule, offered by h-walk-identity (origin/cold/h-walk-identity-s8a34-interim
   fa47eb682cc lib/A/Prog/S8aCallW.v, blob 53f2aabd579, there named aj_call_xWF; donor WalkH6 78f9b475ee95,
   the internal file kit-aj_call_xF.patch), statement and proof verbatim under the name aj_call_xWF_d. The callee's journal runs at
   (STK1 + d) (sp_c + d), d bytes above its entry sp, inside the caller's frame (o + d <= 0). It is NOT a corollary
   of aj_call_xWF / aj_call_xWF_sp, nor they of it: this rule asks no `d mod 16 = 0`, hands the callee no fwin_x, and
   its callee post has no window-kept clause (a caller folds that into Q), so it concludes none; aj_call_xWF asks
   `e1 mod 16 = 0`, asks the callee for fpostWF_x (window-kept clause included) and concludes that clause.
   AJ is S8aCallW.v's notation, here a local abbreviation (PRH_Base.v's form) with SK given explicitly. *)
#[local] Abbreviation AJ := (ajournal_x (SK := SK) segs B PST ARx).
Lemma aj_call_xWF_d : forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o d : Z) spw raw ch1
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> 0 <= d -> o + d <= 0 ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
(afn_pre_x segs B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
 SRr segs W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
   (fun W' c' => exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k',
      c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr (ms_regs ms) 1) mem' (YK11.seg_rom segs)) md' /\
      frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
      AJ (STK1 + d) (spZ (ms_regs ms) + d) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly' S' Hp' W' mem' md' k' /\
      aregs_preserved (ms_regs ms) regs' /\ Q ly' S' Hp' W' regs' mem' md')) ->
fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
SRr segs W (mkCfg ms mdc)
 (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
  frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
  AJ STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
  AJ (STK1 + d) (sp0 + o + d) FP1 lyc Sc Hpc W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (aj_call_xWF_dR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End l.
End cj.
