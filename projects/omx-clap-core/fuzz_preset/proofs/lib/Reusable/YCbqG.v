(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the per-function frame of proofs/cgif/cgif_file_fuzzer/lib/YCbq.v (:210-216, :335-342, :349-371, :384-393, :419-458, :480-671, :724-791, :1809-1825) and lib/YC20.v:90-96, with three changes: the allocator invariant is a parameter ARx, and the YG0d.v:423-495 / YG0p.v:20-27 laws the lemmas use are the record AR_laws_x over it (AR_laws_x_of_AR below instantiates it at cgif's AR); Hp (the ghost poisoned-head set of YGcfNames.v:178-183) threaded as YGcfNames.v:319-329 orders it, with cgif's relative event count k kept as YGcfNames.v:311-315 decides; the image clause exempts the program's own written statics PST (port-fm's FM_PSTAT form). No address literal. *)
(* Modified by Theorem Labs, 2026-10: the journal carries the run's wild-trace count (ajournal_xw, last conjunct;
   ajournal_x is its form at an empty budget, so every statement that names ajournal_x keeps its text but ajournal_x_after_write, which gains `st_depot S' = st_depot Sc` (:1091)) and is read
   through the named projections ajx_*; AR_laws_x gains fields 19-24 (frames' class range, band presence, the
   high-arm block margin, the hidden-head shadow, the fake-frame flag byte, the +8 ceiling margin of live blocks) and
   field 25 (the depot holds no repeat, YG01.v depot_fits' first conjunct: the admission premise at a wild allocator
   call). *)
(* Modified by Theorem Labs, 2026-10: the journal is generic in its world relation R. ajournal_xbR / ajournal_xwR /
   ajournal_xR are the three forms with the world conjunct R W W'; ajxR_intro and the projections ajxR_* read them
   (ajxR_rel the world conjunct); ajournal_xbR_mono / ajournal_xwR_mono move a journal from R1 to every R2 that
   contains R1; ajournal_x_initR holds at a reflexive R, ajournal_xw_subR / ajournal_x_subR at a transitive R, and
   afn_pre_x_atR and ajournal_x_materializeR (with awr_byte_cases_xR, ajournal_x_after_writeR and ajournal_x_execR,
   which it rests on) and ajournal_x_pst_writeR at every R; apost_base_xR / apost_base_xFR are the call posts over R.
   ajournal_xb is ajournal_xbR at wle, and each old name keeps its statement (but ajournal_x_after_write, above) and is proved as the instance at wle
   (wle_refl / wle_trans); the plain posts keep their bodies, and apost_base_x_R_wle / apost_base_xF_R_wle show by
   reflexivity that each is its R form at wle. Why: the free and realloc contracts move to posts that re-hide shadow,
   whose world step is not wle; a caller whose segment crosses such a call needs its journal, and the rules over it,
   at a wider relation R. *)
(* Modified by Theorem Labs, 2026-10: ajx_budgetR (a journal under another budget, over any R; ajx_budget is its
   instance at wle) for the budgeted call rules over R, and apost_base_x_R_lift / apost_base_xF_R_lift: a callee whose
   text concludes the plain post concludes its R form at every R that contains wle, so a caller over R calls it with
   the R call rules unchanged. apost_base_xR_F is apost_base_x_F over R (the float form at frm_zero, at any R). *)
(* Modified by Theorem Labs, 2026-10: ajournal_x_frame_writeR and ajournal_x_exec_frR, the caller-frame write lemmas
   over any world relation R (the world is unchanged; YC80xf.v's R runners rest on them); ajournal_x_frame_write and
   ajournal_x_exec_fr are their instances at wle, statements unchanged. The table-engine runners of Section e over R:
   run_post_AJxR / run_post_tok_AJxR (the journal at R, the conclusion YA0nH.SRrG segs R) and the R forms of
   SRr_chain_AJx / SRr_run_AJx / SRr_run_to_AJx, SRr_chain_tok_AJx / SRr_run_tok_AJx / SRr_run_to_tok_AJx, their _pst,
   _frame and _fr forms (suffix R; R and its two laws, reflexive and transitive, first, then the plain binders); each
   plain runner is its R form at wle (wle_refl / wle_trans), statement unchanged. Their run step is YA0n.v's
   SRr_msteps, read at R through SRr_SRrG_same: an SRr run whose post keeps the world W and states SRrG at W is an
   SRrG run, at any R. YA0nH is imported for SRrG. ajournal_xw_fix1R: ajournal_xw_fix1 with the journal at any R (R
   implicit, read off the journal); ajournal_xw_fix1 is its instance at wle, statement unchanged. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From LinuxProcessSemantics.Riscv Require Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The callee-saved float registers fs0-fs11 (f8, f9, f18-f27) are kept: the RISC-V calling convention's float half. *)
Definition fregs_kept_x (f f' : YK11.FPState) : Prop :=
forall r, r = 8 \/ r = 9 \/ 18 <= r <= 27 ->
LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs f') (Z_to_bv 5 r) =
LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs f) (Z_to_bv 5 r).
(* THE WILD-TRACE COUNT of the journal (the internal file TRACE-CARRIER.md section 7 items 12-13; the count is a journal conjunct,
   ruled (a), a Theorem Labs lane 12:58Z): list facts over YG01.v's wild_part, the stored traces that are not fixed ones. *)
Lemma wild_part_In : forall U t d, In t (wild_part U d) <-> In t d /\ mem_trace t (u_fix U) = false.
Proof.
intros U t d. unfold wild_part. rewrite filter_In. split; intros [H1 H2]; split; try exact H1.
- apply negb_true_iff in H2. exact H2.
- apply negb_true_iff. exact H2.
Qed.
(* a step that stores at most the trace tr grows the wild part by at most tr *)
Lemma wild_part_step : forall U d d' tr, incl d' (d ++ [tr]) -> incl (wild_part U d') (wild_part U d ++ [tr]).
Proof.
intros U d d' tr Hi t Ht. apply wild_part_In in Ht as [Ht Hf]. apply in_or_app.
destruct (in_app_or _ _ _ (Hi t Ht)) as [H|[H|[]]].
- left. apply wild_part_In. split; [exact H | exact Hf].
- right. left. exact H.
Qed.
(* an unchanged depot is within every budget *)
Lemma wild_part_same : forall U d (ws : list (list Z)), incl (wild_part U d) (wild_part U d ++ ws).
Proof. intros U d ws. apply incl_appl, incl_refl. Qed.
(* two stretches in a row: the budgets add *)
Lemma wild_incl_trans : forall (a b c w0 w1 : list (list Z)),
incl a (b ++ w1) -> incl b (c ++ w0) -> incl a (c ++ w0 ++ w1).
Proof.
intros a b c w0 w1 H1 H2 t Ht. destruct (in_app_or _ _ _ (H1 t Ht)) as [H|H].
- rewrite app_assoc. apply in_or_app. left. exact (H2 t H).
- apply in_or_app. right. apply in_or_app. right. exact H.
Qed.
(* a FIXED trace in the budget pays for nothing: no stored wild trace is a fixed one *)
Lemma wild_incl_fix : forall U d (m : list (list Z)) tr, In tr (u_fix U) ->
incl (wild_part U d) (m ++ [tr]) -> incl (wild_part U d) m.
Proof.
intros U d m tr Hf Hi t Ht. destruct (in_app_or _ _ _ (Hi t Ht)) as [H|[E|[]]]; [exact H|].
exfalso. subst t. apply wild_part_In in Ht as [_ Ht]. apply mem_trace_In in Hf. congruence.
Qed.
(* a wider budget *)
Lemma wild_incl_mono : forall (a b w w' : list (list Z)), incl w w' -> incl a (b ++ w) -> incl a (b ++ w').
Proof. intros a b w w' Hw Hi. eapply incl_tran; [exact Hi|]. apply incl_app; [apply incl_appl, incl_refl | apply incl_appr, Hw]. Qed.
(* THE ADMISSION of an allocator call's trace (YG01.v admits) from a FIXED trace: a call trace has at most
   kUnwindMax frames (YG0d.v call_trace_len), so a fixed one is admitted at every state. *)
Lemma admits_ct_fix : forall U ly pc0 regs ch s,
In (call_trace ly pc0 regs ch) (u_fix U) -> admits U (call_trace ly pc0 regs ch) s.
Proof.
intros U ly pc0 regs ch s H. split; [split; [apply call_trace_len | left; exact H]|].
right. left. apply mem_trace_In. exact H.
Qed.
(* cgif's call_trace0 form of the trace (YCbq.v call_trace_in): with the one-frame trace [pc0] fixed, the admission of
   call_trace0 gives the admission of call_trace *)
Lemma admits_call_trace0 : forall U ly pc0 regs ch s, In [pc0] (u_fix U) ->
admits U (call_trace0 pc0 regs ch) s -> admits U (call_trace ly pc0 regs ch) s.
Proof.
intros U ly pc0 regs ch s H0 H1. unfold call_trace. destruct (frame0_ok ly regs); [exact H1|].
split; [split; [unfold kUnwindMax; cbn; lia | left; exact H0]|]. right. left. apply mem_trace_In. exact H0.
Qed.
(* fs_frame_bytes cid = Z.shiftl 64 cid (YG00.v): a frame of class cid >= 0 spans at least 64 bytes, a multiple of
   64 (moved here from YGcallMxmn.v, for frame_bytes_x below) *)
Lemma fs_frame_bytes_ok : forall cid, 0 <= cid -> 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
Proof.
intros cid Hc. unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by exact Hc.
pose proof (Z.pow_le_mono_r 2 0 cid ltac:(lia) Hc) as H1. change (2 ^ 0) with 1 in H1.
split; [lia | rewrite Z.mul_comm; apply Z.mod_mul; lia].
Qed.
(* round_up x a is at least x (YG00.v round_up); for field 24's secondary-block margin *)
Lemma round_up_ge_x : forall x a, 0 < a -> x <= round_up x a.
Proof.
intros x a Ha. unfold round_up.
pose proof (Z.div_mod (x + a - 1) a ltac:(lia)). pose proof (Z.mod_pos_bound (x + a - 1) a Ha). lia.
Qed.
Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* the head length of a harness block (cf_head for the second instance, 0 for cgif's AR): the parameter of the
   harness-block shadow law. IMPLICIT in every lemma of this file, so an explicit citation `.. ARx LAWS ..` is
   unchanged (hl is inferred from LAWS); EXPLICIT on the record type: `AR_laws_x segs B ARx hl`. *)
Context {hl : Z}.
Definition ARx_blocks_law : Prop :=
forall ly S Hp W mem md p n,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= YM05.alloc_ceiling /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)).
Definition ARx_frame_law : Prop :=
forall ly S Hp W mem md mem' md',
ARx ly S Hp W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARx ly S Hp W mem' md'.
Definition ARx_frames_law : Prop :=
forall ly S Hp W mem md cid pos,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos mod 32 = 0 /\ in_app (frame_addr ly cid pos) (fs_frame_bytes cid) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
(forall i, 0 <= i < fs_frame_bytes cid / 8 ->
apresent (w_H W) mem (shadow_addr (frame_addr ly cid pos) + i) /\
~ aowned B ly S (shadow_addr (frame_addr ly cid pos) + i)).
Definition ARx_stack_law : Prop :=
forall ly S Hp W mem md a,
ARx ly S Hp W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly S a.
Definition ARx_owned_image_law : Prop :=
forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_img segs a -> (aowned B ly S a <-> Exists (in_zr a) (as_owned_static B)).
Definition ARx_sep_law : Prop :=
forall ly S Hp W mem md, ARx ly S Hp W mem md ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)
++ map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) (frames S)) /\
Forall (fun f => 4096 <= frame_addr ly (fst f) (snd f) /\ frame_addr ly (fst f) (snd f) + fs_frame_bytes (fst f) <= YM05.alloc_ceiling) (frames S).
Definition ARx_layout_law : Prop :=
forall ly S Hp W mem md ly',
ARx ly S Hp W mem md -> layout_le (length (st_secs S)) ly ly' ->
ablocks B ly' S = ablocks B ly S /\ (forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) /\
(forall a, aowned B ly' S a <-> aowned B ly S a).
Definition ARx_client_img_law : Prop :=
forall ly S Hp W mem md a, ARx ly S Hp W mem md ->
((exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) \/
(exists cid pos, In (cid, pos) (frames S) /\ a = flag_addr ly cid pos)) ->
~ in_zr a (ly_img ly) /\ ~ in_img segs a.
Definition ARx_extra_law : Prop :=
forall ly S Hp W mem md a, ARx ly S Hp W mem md -> Exists (in_zr a) (ly_extra ly) ->
~ aowned B ly S a /\
(forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)) /\
(forall cid pos, In (cid, pos) (frames S) ->
~ (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) /\
~ (shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8)) /\
~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_img segs a /\ ~ (SHADOW_OFF <= a < kHighShadowEnd) /\ app_addr a.
(* cgif's YG0d.v:430-434 AR_shadow_law over ARx, with the blocks whose hidden head is in Hp excluded: for a block
   whose bytes hold no hidden head, its shadow is a block shadow and its hull is visible. A harness block of the
   second instance has its first bytes hidden by construction (its base is in Hp), so this law says nothing about it;
   the user-range form for such a block needs that instance's head length and belongs to the cf layer, not here. *)
Definition ARx_shadow_law : Prop :=
forall ly S Hp W mem md p n,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
(forall h, In h Hp -> ~ (p <= h < p + req_size n)) ->
block_shadow (aview segs (w_H W) mem) SHADOW_OFF p (req_size n) /\
shadow_hull_vis (aview segs (w_H W) mem) p (req_size n).
(* cgif's YG0d.v:435-438 AR_zshadow_law over ARx (= YG0dcf.v:278 of the second instance): the ranges the runtime keeps
   at shadow 0 - the REAL STACK (the head of zero_shadow_ranges, (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) and the
   image's own zero-shadow ranges - read 0. A walk that reads a caller's struct on the real stack needs it. *)
Definition ARx_zshadow_law : Prop :=
forall ly S Hp W mem md r,
ARx ly S Hp W mem md -> In r (zero_shadow_ranges B ly) ->
zero_shadow (aview segs (w_H W) mem) SHADOW_OFF (fst r) (snd r).
(* THE FORM THE CONSUMERS USE: the shadow byte of an ADDRESS in the real stack, which is what an instrumented check on
   a caller's struct reads. The range form above cannot give it without the 8-alignment of both stack bounds (lo = 3,
   hi = 11, x = 10 is a counterexample: (hi - lo) / 8 = 0), and ARx gives no alignment - so the law is stated per byte
   and a range form is derived from it, not the other way round (WalkS8b). *)
Definition ARx_zshadow_byte_law : Prop :=
forall ly S Hp W mem md a,
ARx ly S Hp W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly ->
aview segs (w_H W) mem (SHADOW_OFF + a / 8) = Some 0.
(* FIELD 14: the harness-block shadow law (WalkS7b's PRW_HShadow.v text, d9e14d9927a): a block whose base is in Hp
   has its hidden head first, then a block shadow over its user range (b + hl, req_size n - hl). *)
Definition ARx_hshadow_law (hl0 : Z) : Prop :=
forall ly S Hp W mem md b n,
ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> In b Hp ->
block_shadow (aview segs (w_H W) mem) SHADOW_OFF (b + hl0) (req_size n - hl0) /\
(hl0 < req_size n -> shadow_hull_vis (aview segs (w_H W) mem) (b + hl0) (req_size n - hl0)).
(* FIELD 15: a block's TAIL GRANULE is present - the bytes from its end to the end of that 8-byte granule, which a
   granule-wise string scan reads after a NUL near the end (h-hpreset-7's text, verbatim but over ARx). Separate
   from field 14. *)
Definition ARx_blocks_tail_law : Prop :=
forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n <= a < (p + req_size n + 7) / 8 * 8 ->
aview segs (w_H W) mem a <> None.
(* FIELD 16: ARx KEEPS THE IMAGE'S CONST SHADOW CELLS - every cell of `as_const B ly` holds its constant value in the
   current view. A reviewer who reads "const shadow" will reach for in_zs or a zero-shadow argument: THAT IS WRONG
   HERE. These cells have CONSTANT NON-ZERO shadow - the C-RO measurement puts the last granule of a read-only
   string at 03 or 05, a partial granule, outside every as_zero_shadow range - so the field says the cells are KEPT,
   not that their shadow is zero. It is what a kept_at disjunct over the image's read-only strings needs, and only the
   journal can state it for a generic ARx. At ARcf it is am_const (YG0ncf.v, a conjunct of the invariant), so the
   instance discharges it by citation. *)
Definition ARx_const_cells_law : Prop :=
forall ly S Hp W mem md,
ARx ly S Hp W mem md -> Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly).
Definition ARx_const_law : Prop :=
forall ly S Hp W mem md,
ARx ly S Hp W mem md ->
rdword (aview segs (w_H W) mem) (as_shadow_cell B) = Some SHADOW_OFF /\
rd32 (aview segs (w_H W) mem) (as_uar_cell B) 1 /\
rdword (aview segs (w_H W) mem) (as_got_shadow B) = Some (as_shadow_cell B) /\
rdword (aview segs (w_H W) mem) (as_got_uar B) = Some (as_uar_cell B).
(* FIELD 17: WHERE THE RUNTIME PUTS ITS OBJECTS RELATIVE TO THE IMAGE. Two conjuncts, both already true at
   both instances and neither derivable from fields 1-16: ly_img covers every segment of the image (the
   ledger's al_img / alc_img, FCiface's fi_img), and a live fake frame lies at or above the image's top (the
   fake stack is a static extent disjoint from ly_img, and it is longer than the image). From these two a
   consumer derives the NUMERIC band forms its row asks - a live block off [L, H), a live fake frame at or
   above H - for any L, H its own image facts cover. No address appears here: L and H enter at the
   consumer. *)
Definition ARx_img_law : Prop :=
forall ly S Hp W mem md,
ARx ly S Hp W mem md ->
(forall sg, In sg segs -> fst (ly_img ly) <= Z.of_N (seg_base sg) /\
   Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= fst (ly_img ly) + snd (ly_img ly)) /\
(forall cid pos, In (cid, pos) (frames S) ->
   fst (ly_img ly) + snd (ly_img ly) <= frame_addr ly cid pos).
(* FIELD 18: THE LAYOUT IS WELL FORMED. The layout of every ARx state is layout_ok (YG0f.v), as at both instances
   (cgif's AR: ARm's am_layout, as FCiface.v:184; ARcf: ARmcf's amc_layout, as FCifaceCf.v:135). Not derivable
   from fields 1-17: none bounds ly_stk_lo / ly_stk_hi absolutely. Named ARx_layout_ok_law, not ARx_layout_law
   (field 7, the layout_le monotonicity law). Section l derives the stack bounds stk_bounds_x and the stack
   alignment stk_aligned_x from it. *)
Definition ARx_layout_ok_law : Prop :=
forall ly S Hp W mem md, ARx ly S Hp W mem md -> layout_ok ly.
(* FIELD 19: A LIVE FAKE FRAME'S CLASS IS ONE OF ASan's 11 FAKE-STACK SIZE CLASSES (64 << 0 .. 64 << 10; 10 is cgif's
   literal in frame_facts, DERIVED, not an address). Not derivable from fields 1-18: they use cid only through
   frame_addr / fs_frame_bytes / flag_addr. At both instances it is frame_facts' first conjunct. *)
Definition ARx_frames_cid_law : Prop :=
forall ly S Hp W mem md cid pos,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> 0 <= cid <= 10.
(* FIELD 20: EVERY BYTE OF THE SHADOW BAND THAT IS NOT HIDDEN AND NOT IN THE ZERO-SHADOW VIEW IS VISIBLE (a Theorem Labs lane's
   text). Not derivable: the presence facts of fields 1-18 cover block, frame, shadow-hull, stack and const bytes
   only. At both instances: ahs_pres with client_band_vis(_cf) and aview_band. *)
Definition ARx_band_pres_law : Prop :=
forall ly S Hp W mem md a,
ARx ly S Hp W mem md -> in_band_rw a -> w_H W (w64 a) = false -> ~ in_vis0 ly a ->
aview segs (w_H W) mem a <> None.
(* FIELD 21: A LIVE BLOCK ON THE HIGH ARM STARTS AT LEAST 16 BYTES (ASan's smallest redzone, LENGTH) ABOVE
   kHighMemBeg (a Theorem Labs lane's high-arm margin). Not derivable: field 1's in_app admits p = kHighMemBeg. With field 1
   it gives blocks_range8_x (YGcallMx.v), the strcmp rule's amem_range8 premise. *)
Definition ARx_blocks_hi_law : Prop :=
forall ly S Hp W mem md p n,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> kHighMemBeg <= p -> kHighMemBeg + 16 <= p.
(* FIELD 22: THE SHADOW OF EVERY BYTE OF A HIDDEN HEAD (the first hl0 bytes of a block whose base is in Hp) IS
   0xf7, ASan's kAsanUserPoisonedMemoryMagic (a shadow VALUE, WORD; YGcfNames.shUserPoison, written as a literal
   because this file does not import YGcfNames). Not derivable: fields 11 and 14 say nothing about the head's
   shadow. hhead_not_addressable_x below is the consumer form. Vacuous at hl0 = 0 (cgif's AR). *)
Definition ARx_hhead_law (hl0 : Z) : Prop :=
forall ly S Hp W mem md b n a,
ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> In b Hp -> b <= a < b + hl0 ->
aview segs (w_H W) mem (shadow_addr a) = Some 0xf7.
(* FIELD 23: cgif's AR_flag_law (YG0d.v) over ARx, word for word: a live fake frame's flag byte is present, runtime
   owned, in application memory and below alloc_ceiling. Not derivable: the flag byte is in no block or frame range.
   With field 8 it gives fflx_of_flag_law below (YGcallSx.v's FFLX). *)
Definition ARx_flag_law : Prop :=
forall ly S Hp (W : world segs) mem md cid pos,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned B ly S (flag_addr ly cid pos) /\
in_app (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < YM05.alloc_ceiling.
(* FIELD 24 (F21b, a Theorem Labs lane 17:29Z): EVERY LIVE BLOCK ENDS AT LEAST 8 BYTES BELOW alloc_ceiling (a LENGTH margin;
   three kit texts read it). Not derivable: field 1 bounds a block's end by alloc_ceiling only. At both instances:
   a primary block ends at least 2^31 (cgif) / 2^32 - kFreeArrayOffset (cf) below the ceiling; a secondary block ends at
   least its right redzone (rz_size >= 16, needed_size YG00.v) below its map's end, which is at or below the ceiling
   (sec_placed, YG0n.v). *)
Definition ARx_blocks_ceil8_law : Prop :=
forall ly S Hp W mem md p n,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> p + req_size n + 8 <= YM05.alloc_ceiling.
(* FIELD 25: THE DEPOT HOLDS NO REPEAT (YG01.v depot_fits, first conjunct). Not derivable: fields 1-24 do not read
   st_depot, so they hold at a relation whose state stores one wild trace u_wmax times (a Theorem Labs lane's countermodel).
   At both instances it is the depot invariant of the allocator's Wf: cgif's AR: ARm's am_wf, wf_depot; ARcf: ARmcf's
   amc_wf, wfc_depot (YGcallcf.v ARcf_depot_nodup). The admission of a wild allocator call reads it
   (YCbqGwild.v wild_room_admits_laws / ajournal_xw_admits_laws). ARx_depot_nodup_law_dup below is the negative
   control. *)
Definition ARx_depot_nodup_law : Prop :=
forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (st_depot S).
(* the negative control of field 25: a depot that holds one trace twice is not NoDup, so the law fails at every ARx
   that holds at such a state *)
Lemma ARx_depot_nodup_law_dup : forall ly S Hp W mem md t, st_depot S = [t; t] ->
~ List.NoDup (st_depot S) /\ (ARx ly S Hp W mem md -> ~ ARx_depot_nodup_law).
Proof.
intros ly S Hp W mem md t E.
assert (ND : ~ List.NoDup (st_depot S)).
{ rewrite E. intros H. apply NoDup_cons_iff in H as [Hn _]. apply Hn. left. reflexivity. }
split; [exact ND|]. intros HAR L. exact (ND (L ly S Hp W mem md HAR)).
Qed.
Record AR_laws_x : Prop := {
alx_blocks : ARx_blocks_law;
alx_frame : ARx_frame_law;
alx_frames : ARx_frames_law;
alx_stack : ARx_stack_law;
alx_owned_image : ARx_owned_image_law;
alx_sep : ARx_sep_law;
alx_layout : ARx_layout_law;
alx_client_img : ARx_client_img_law;
alx_extra : ARx_extra_law;
alx_const : ARx_const_law;
alx_shadow : ARx_shadow_law;
alx_zshadow : ARx_zshadow_law;
alx_zshadow_byte : ARx_zshadow_byte_law;
alx_hshadow : ARx_hshadow_law hl;
alx_blocks_tail : ARx_blocks_tail_law;
alx_const_cells : ARx_const_cells_law;
alx_img : ARx_img_law;
alx_layout_ok : ARx_layout_ok_law;
alx_frames_cid : ARx_frames_cid_law;
alx_band_pres : ARx_band_pres_law;
alx_blocks_hi : ARx_blocks_hi_law;
alx_hhead : ARx_hhead_law hl;
alx_flag : ARx_flag_law;
alx_blocks_ceil8 : ARx_blocks_ceil8_law;
alx_depot_nodup : ARx_depot_nodup_law
}.
Definition afn_pre_x (STK : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
ARx ly S Hp W mem md /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
astk_ok STK ly (spZ regs) /\
(forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) /\
achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch /\
qtight S.
(* THE JOURNAL from the function's entry state to the current one, with the run's WILD-TRACE BUDGET WS (the internal file TRACE-CARRIER.md
   section 7 item 13): the last conjunct says the wild traces stored now are those stored at entry plus at most WS,
   the wild traces the segment's own allocator calls may store (YG01.v wild_part; a fixed trace is never wild).
   ajournal_x is the journal at the empty budget, the form of every function with no wild site: Coq has no default
   arguments, so the budget WS is a parameter of ajournal_xw and ajournal_x is ajournal_xw at WS = []; every
   statement that names ajournal_x keeps its text except ajournal_x_after_write (its premise `st_depot S' = st_depot Sc`, :1091). Read a journal through the projections ajx_* below, never by a
   positional destruct. ajournal_xb is the journal's body: the entry ghost set Hp occurs in no conjunct, so the
   projections are stated over ajournal_xb, whose every argument occurs in its body (Coq infers each of them from a
   journal hypothesis of any of the three forms). ajournal_xbR is the body over a world relation R (the fourth
   conjunct is R W W'); ajournal_xb is ajournal_xbR at wle, so every statement over ajournal_xb keeps its text. *)
Definition ajournal_xbR (R : world segs -> world segs -> Prop) (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z)
(WS : list (list Z)) : Prop :=
ARx ly' S' Hp' W' mem' md' /\
layout_le (length (st_secs S)) ly ly' /\ (length (st_secs S) <= length (st_secs S'))%nat /\ R W W' /\ aos_step FP md md' /\
frames S' = own ++ frames S /\
st_nev S' <= st_nev S + k /\ 0 <= k /\
(forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> inFP FP (p + i)) /\
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
astk_ok STK ly sp0 /\
(forall a, Exists (in_zr a) (ly_extra ly) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
qtight S' /\
incl (wild_part (as_universe B) (st_depot S')) (wild_part (as_universe B) (st_depot S) ++ WS).
Definition ajournal_xb (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z)
(WS : list (list Z)) : Prop :=
ajournal_xbR (@wle segs) STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS.
Definition ajournal_xw (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z)
(WS : list (list Z)) : Prop :=
ajournal_xb STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS.
Definition ajournal_x (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal_xw STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k [].
(* the WS form and the empty-budget form over R, layered as ajournal_xw / ajournal_x over ajournal_xb *)
Definition ajournal_xwR (R : world segs -> world segs -> Prop) (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z)
(WS : list (list Z)) : Prop :=
ajournal_xbR R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS.
Definition ajournal_xR (R : world segs -> world segs -> Prop) (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal_xwR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k [].
(* THE JOURNAL'S CONJUNCTS BY NAME over R (projections ajxR_*; ajxR_rel is the world conjunct) and its constructor
   ajxR_intro. The projections ajx_* below are these at wle. *)
Section ajxR.
Context {R : world segs -> world segs -> Prop}.
Context {STK sp0 : Z} {FP : list (Z * Z)} {ly : alayout} {S : astate} {W : world segs}
{mem : word -> option byte} {md : Model} {own : list (Z * Z)} {ly' : alayout} {S' : astate} {Hp' : list Z}
{W' : world segs} {mem' : word -> option byte} {md' : Model} {k : Z} {WS : list (list Z)}.
Lemma ajxR_intro :
ARx ly' S' Hp' W' mem' md' ->
layout_le (length (st_secs S)) ly ly' -> (length (st_secs S) <= length (st_secs S'))%nat -> R W W' -> aos_step FP md md' ->
frames S' = own ++ frames S ->
st_nev S' <= st_nev S + k -> 0 <= k ->
(forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
(forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) ->
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
(forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
(forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> inFP FP (p + i)) ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) ->
astk_ok STK ly sp0 ->
(forall a, Exists (in_zr a) (ly_extra ly) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
qtight S' ->
incl (wild_part (as_universe B) (st_depot S')) (wild_part (as_universe B) (st_depot S) ++ WS) ->
ajournal_xbR R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS.
Proof.
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18.
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
  (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 H18))))))))))))))))).
Qed.
Hypothesis J0 : ajournal_xbR R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS.
Lemma ajxR_ar : ARx ly' S' Hp' W' mem' md'.
Proof. destruct J0 as (H & _). exact H. Qed.
Lemma ajxR_ly : layout_le (length (st_secs S)) ly ly'.
Proof. destruct J0 as (_ & H & _). exact H. Qed.
Lemma ajxR_secs : (length (st_secs S) <= length (st_secs S'))%nat.
Proof. destruct J0 as (_ & _ & H & _). exact H. Qed.
Lemma ajxR_rel : R W W'.
Proof. destruct J0 as (_ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_io : aos_step FP md md'.
Proof. destruct J0 as (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_frs : frames S' = own ++ frames S.
Proof. destruct J0 as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_nev : st_nev S' <= st_nev S + k.
Proof. destruct J0 as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_k : 0 <= k.
Proof. destruct J0 as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_hi : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. destruct J0 as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_blk : forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof. destruct J0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_img : forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. destruct J0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_frm : forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. destruct J0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_gone : forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
inFP FP (p + i).
Proof. destruct J0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_pres : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof. destruct J0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_stk : astk_ok STK ly sp0.
Proof. destruct J0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_extra : forall a, Exists (in_zr a) (ly_extra ly) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. destruct J0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_qt : qtight S'.
Proof. destruct J0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma ajxR_wild : incl (wild_part (as_universe B) (st_depot S')) (wild_part (as_universe B) (st_depot S) ++ WS).
Proof. destruct J0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
End ajxR.
(* THE JOURNAL'S CONJUNCTS BY NAME (projections) and its constructor ajx_intro: each is its ajxR_* form at wle. *)
Section ajx.
Context {STK sp0 : Z} {FP : list (Z * Z)} {ly : alayout} {S : astate} {W : world segs}
{mem : word -> option byte} {md : Model} {own : list (Z * Z)} {ly' : alayout} {S' : astate} {Hp' : list Z}
{W' : world segs} {mem' : word -> option byte} {md' : Model} {k : Z} {WS : list (list Z)}.
Lemma ajx_intro :
ARx ly' S' Hp' W' mem' md' ->
layout_le (length (st_secs S)) ly ly' -> (length (st_secs S) <= length (st_secs S'))%nat -> wle W W' -> aos_step FP md md' ->
frames S' = own ++ frames S ->
st_nev S' <= st_nev S + k -> 0 <= k ->
(forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
(forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) ->
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
(forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
(forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> inFP FP (p + i)) ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) ->
astk_ok STK ly sp0 ->
(forall a, Exists (in_zr a) (ly_extra ly) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
qtight S' ->
incl (wild_part (as_universe B) (st_depot S')) (wild_part (as_universe B) (st_depot S) ++ WS) ->
ajournal_xb STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS.
Proof. exact (ajxR_intro (R := @wle segs)). Qed.
Hypothesis J0 : ajournal_xb STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS.
Lemma ajx_ar : ARx ly' S' Hp' W' mem' md'.
Proof. exact (ajxR_ar (R := @wle segs) J0). Qed.
Lemma ajx_ly : layout_le (length (st_secs S)) ly ly'.
Proof. exact (ajxR_ly (R := @wle segs) J0). Qed.
Lemma ajx_secs : (length (st_secs S) <= length (st_secs S'))%nat.
Proof. exact (ajxR_secs (R := @wle segs) J0). Qed.
Lemma ajx_wle : wle W W'.
Proof. exact (ajxR_rel (R := @wle segs) J0). Qed.
Lemma ajx_io : aos_step FP md md'.
Proof. exact (ajxR_io (R := @wle segs) J0). Qed.
Lemma ajx_frs : frames S' = own ++ frames S.
Proof. exact (ajxR_frs (R := @wle segs) J0). Qed.
Lemma ajx_nev : st_nev S' <= st_nev S + k.
Proof. exact (ajxR_nev (R := @wle segs) J0). Qed.
Lemma ajx_k : 0 <= k.
Proof. exact (ajxR_k (R := @wle segs) J0). Qed.
Lemma ajx_hi : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. exact (ajxR_hi (R := @wle segs) J0). Qed.
Lemma ajx_blk : forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof. exact (ajxR_blk (R := @wle segs) J0). Qed.
Lemma ajx_img : forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. exact (ajxR_img (R := @wle segs) J0). Qed.
Lemma ajx_frm : forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. exact (ajxR_frm (R := @wle segs) J0). Qed.
Lemma ajx_gone : forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
inFP FP (p + i).
Proof. exact (ajxR_gone (R := @wle segs) J0). Qed.
Lemma ajx_pres : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof. exact (ajxR_pres (R := @wle segs) J0). Qed.
Lemma ajx_stk : astk_ok STK ly sp0.
Proof. exact (ajxR_stk (R := @wle segs) J0). Qed.
Lemma ajx_extra : forall a, Exists (in_zr a) (ly_extra ly) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. exact (ajxR_extra (R := @wle segs) J0). Qed.
Lemma ajx_qt : qtight S'.
Proof. exact (ajxR_qt (R := @wle segs) J0). Qed.
Lemma ajx_wild : incl (wild_part (as_universe B) (st_depot S')) (wild_part (as_universe B) (st_depot S) ++ WS).
Proof. exact (ajxR_wild (R := @wle segs) J0). Qed.
End ajx.
(* THE WEAKENING over R: a journal at R1 is a journal at every R2 that contains R1 (only the world conjunct reads R);
   e.g. a journal at wle is one at a wider re-hiding relation *)
Lemma ajournal_xbR_mono : forall (R1 R2 : world segs -> world segs -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS,
  ajournal_xbR R1 STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS ->
  ajournal_xbR R2 STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS.
Proof.
intros R1 R2 H12 STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS HJ.
exact (ajxR_intro (R := R2) (ajxR_ar HJ) (ajxR_ly HJ) (ajxR_secs HJ) (H12 W W' (ajxR_rel HJ)) (ajxR_io HJ) (ajxR_frs HJ)
  (ajxR_nev HJ) (ajxR_k HJ) (ajxR_hi HJ) (ajxR_blk HJ) (ajxR_img HJ) (ajxR_frm HJ) (ajxR_gone HJ) (ajxR_pres HJ)
  (ajxR_stk HJ) (ajxR_extra HJ) (ajxR_qt HJ) (ajxR_wild HJ)).
Qed.
Lemma ajournal_xwR_mono : forall (R1 R2 : world segs -> world segs -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS,
  ajournal_xwR R1 STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  ajournal_xwR R2 STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS.
Proof.
intros R1 R2 H12 STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS.
exact (ajournal_xbR_mono R1 R2 H12 STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS).
Qed.
(* the same journal under another budget, over any world relation R *)
Lemma ajx_budgetR {R : world segs -> world segs -> Prop} {STK sp0 : Z} {FP : list (Z * Z)} {ly : alayout}
{S : astate} {W : world segs}
{mem : word -> option byte} {md : Model} {own : list (Z * Z)} {ly' : alayout} {S' : astate} {Hp' : list Z}
{W' : world segs} {mem' : word -> option byte} {md' : Model} {k : Z} {WS : list (list Z)} (WS' : list (list Z)) :
ajournal_xbR R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS ->
incl (wild_part (as_universe B) (st_depot S')) (wild_part (as_universe B) (st_depot S) ++ WS') ->
ajournal_xbR R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS'.
Proof.
intros HJ Hw. exact (ajxR_intro (ajxR_ar HJ) (ajxR_ly HJ) (ajxR_secs HJ) (ajxR_rel HJ) (ajxR_io HJ) (ajxR_frs HJ)
  (ajxR_nev HJ) (ajxR_k HJ) (ajxR_hi HJ) (ajxR_blk HJ) (ajxR_img HJ) (ajxR_frm HJ) (ajxR_gone HJ) (ajxR_pres HJ)
  (ajxR_stk HJ) (ajxR_extra HJ) (ajxR_qt HJ) Hw).
Qed.
(* the same journal under another budget *)
Lemma ajx_budget {STK sp0 : Z} {FP : list (Z * Z)} {ly : alayout} {S : astate} {W : world segs}
{mem : word -> option byte} {md : Model} {own : list (Z * Z)} {ly' : alayout} {S' : astate} {Hp' : list Z}
{W' : world segs} {mem' : word -> option byte} {md' : Model} {k : Z} {WS : list (list Z)} (WS' : list (list Z)) :
ajournal_xb STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS ->
incl (wild_part (as_universe B) (st_depot S')) (wild_part (as_universe B) (st_depot S) ++ WS') ->
ajournal_xb STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS'.
Proof. exact (ajx_budgetR (R := @wle segs) WS'). Qed.
(* a wider budget *)
Lemma ajournal_xw_incl : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS WS',
incl WS WS' ->
ajournal_xw STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
ajournal_xw STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS'.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS WS' Hi HJ.
exact (ajx_budget WS' HJ (wild_incl_mono _ _ _ _ Hi (ajx_wild HJ))).
Qed.
(* ajournal_xw_fix1 below over any world relation R: `exact (ajournal_xw_fix1R Hfix HJ)` reads R off the journal *)
Lemma ajournal_xw_fix1R {R : world segs -> world segs -> Prop} {STK sp0 : Z} {FP : list (Z * Z)} {ly : alayout}
{S : astate} {Hp : list Z} {W : world segs}
{mem : word -> option byte} {md : Model} {own : list (Z * Z)} {ly' : alayout} {S' : astate} {Hp' : list Z}
{W' : world segs} {mem' : word -> option byte} {md' : Model} {k : Z} {WS : list (list Z)} {tr : list Z} :
In tr (u_fix (as_universe B)) ->
ajournal_xwR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (WS ++ [tr]) ->
ajournal_xwR R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS.
Proof.
intros Hf HJ.
apply (ajx_budgetR WS HJ). apply (wild_incl_fix _ _ _ tr Hf). rewrite <- app_assoc. exact (ajxR_wild HJ).
Qed.
(* an allocator call's own trace, when it is a FIXED one, leaves the budget: the step from a call rule's post
   (budget WS ++ [trace]) back to the caller's budget WS (for WS = [], back to ajournal_x). Every argument is read
   off the journal and the goal: `exact (ajournal_xw_fix1 Hfix HJ)`. *)
Lemma ajournal_xw_fix1 {STK sp0 : Z} {FP : list (Z * Z)} {ly : alayout} {S : astate} {Hp : list Z} {W : world segs}
{mem : word -> option byte} {md : Model} {own : list (Z * Z)} {ly' : alayout} {S' : astate} {Hp' : list Z}
{W' : world segs} {mem' : word -> option byte} {md' : Model} {k : Z} {WS : list (list Z)} {tr : list Z} :
In tr (u_fix (as_universe B)) ->
ajournal_xw STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (WS ++ [tr]) ->
ajournal_xw STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS.
Proof. exact (ajournal_xw_fix1R (R := @wle segs) (Hp := Hp)). Qed.
Definition apost_base_x (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) W mem md
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k,
c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
ajournal_x STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
(* apost_base_x with the float state after the call existential (cgif_rgb_fuzzer lib/YCaq.v:27-32, apost_baseF), for a
   function whose callees change the f registers or fcsr (musl strtod): the rounding mode is back at 0 (frm_zero) and
   the callee-saved f registers are kept. Same parameters in the same positions as apost_base_x. *)
Definition apost_base_xF (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) W mem md
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
ajournal_x STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
(* a function that leaves the float state alone meets the float form when the entry rounding mode is 0 *)
Lemma apost_base_x_F : forall STK FP regs ly S Hp W mem md Q W' c',
frm_zero (@YK11.fp_csr fx) ->
apost_base_x STK FP regs ly S Hp W mem md Q W' c' -> apost_base_xF STK FP regs ly S Hp W mem md Q W' c'.
Proof.
intros STK FP regs ly S Hp W mem md Q W' c' Hz (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & Hpr & HQ).
exists fx, ly', S', Hp', regs', mem', md', k. split; [exact Hc|]. split; [exact Hz|].
split; [intros r _; reflexivity|]. split; [exact HJ|]. split; [exact Hpr | exact HQ].
Qed.
Lemma apost_base_xF_mono : forall STK FP regs ly S Hp W mem md (Q Q' : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
(forall ly' S' Hp' W'' regs' mem' md', Q ly' S' Hp' W'' regs' mem' md' -> Q' ly' S' Hp' W'' regs' mem' md') ->
apost_base_xF STK FP regs ly S Hp W mem md Q W' c' -> apost_base_xF STK FP regs ly S Hp W mem md Q' W' c'.
Proof.
intros STK FP regs ly S Hp W mem md Q Q' W' c' HQQ (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hz & Hk & HJ & Hpr & HQ).
exists fx', ly', S', Hp', regs', mem', md', k. repeat (split; [eassumption|]). exact (HQQ _ _ _ _ _ _ _ HQ).
Qed.
(* THE CALL-POST FORMS OVER R: apost_base_x / apost_base_xF with the journal at R (ajournal_xR R). Each body is a
   COPY of its plain form's with ajournal_x replaced by ajournal_xR R, not the plain form defined through it: 66 proof lines in 37 files outside this one (comments stripped; each a line with `unfold` before apost_base_x / apost_base_xF)
   read the plain body after the unfold, and
   a plain form defined as the R form at wle would stop that unfold at the R form. The guard lemmas
   apost_base_x_R_wle / apost_base_xF_R_wle (by reflexivity) check that each plain form IS its R form at wle, so the
   two copies cannot drift. *)
Definition apost_base_xR (R : world segs -> world segs -> Prop) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word)
ly S (Hp : list Z) W mem md
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k,
c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
ajournal_xR R STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Lemma apost_base_x_R_wle : forall STK FP regs ly S Hp W mem md Q,
apost_base_x STK FP regs ly S Hp W mem md Q = apost_base_xR (@wle segs) STK FP regs ly S Hp W mem md Q.
Proof. reflexivity. Qed.
(* the float form over R: a copy of apost_base_xF's body, guarded by apost_base_xF_R_wle (see above) *)
Definition apost_base_xFR (R : world segs -> world segs -> Prop) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word)
ly S (Hp : list Z) W mem md
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
ajournal_xR R STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Lemma apost_base_xF_R_wle : forall STK FP regs ly S Hp W mem md Q,
apost_base_xF STK FP regs ly S Hp W mem md Q = apost_base_xFR (@wle segs) STK FP regs ly S Hp W mem md Q.
Proof. reflexivity. Qed.
(* apost_base_x_F over R: a function that leaves the float state alone meets the float form at R when the entry
   rounding mode is 0 (any R; the journal is passed through) *)
Lemma apost_base_xR_F : forall (R : world segs -> world segs -> Prop) STK FP regs ly S Hp W mem md Q W' c',
frm_zero (@YK11.fp_csr fx) ->
apost_base_xR R STK FP regs ly S Hp W mem md Q W' c' -> apost_base_xFR R STK FP regs ly S Hp W mem md Q W' c'.
Proof.
intros R STK FP regs ly S Hp W mem md Q W' c' Hz (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & Hpr & HQ).
exists fx, ly', S', Hp', regs', mem', md', k. split; [exact Hc|]. split; [exact Hz|].
split; [intros r _; reflexivity|]. split; [exact HJ|]. split; [exact Hpr | exact HQ].
Qed.
(* A PLAIN CALLEE IN A CALLER OVER R: a callee text that concludes apost_base_x / apost_base_xF (its journal at wle)
   concludes the R form at every R that contains wle (ajournal_xwR_mono on the journal conjunct). *)
Lemma apost_base_x_R_lift : forall (R : world segs -> world segs -> Prop), (forall W W', wle W W' -> R W W') ->
forall STK FP regs ly S Hp W mem md Q W' c',
apost_base_x STK FP regs ly S Hp W mem md Q W' c' -> apost_base_xR R STK FP regs ly S Hp W mem md Q W' c'.
Proof.
intros R Hsub STK FP regs ly S Hp W mem md Q W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & Hpr & HQ).
exists ly', S', Hp', regs', mem', md', k. split; [exact Hc|].
split; [exact (ajournal_xwR_mono (@wle segs) R Hsub STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k [] HJ)
       | split; [exact Hpr | exact HQ]].
Qed.
Lemma apost_base_xF_R_lift : forall (R : world segs -> world segs -> Prop), (forall W W', wle W W' -> R W W') ->
forall STK FP regs ly S Hp W mem md Q W' c',
apost_base_xF STK FP regs ly S Hp W mem md Q W' c' -> apost_base_xFR R STK FP regs ly S Hp W mem md Q W' c'.
Proof.
intros R Hsub STK FP regs ly S Hp W mem md Q W' c' (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hz & Hkf & HJ & Hpr & HQ).
exists fx', ly', S', Hp', regs', mem', md', k. split; [exact Hc|]. split; [exact Hz|]. split; [exact Hkf|].
split; [exact (ajournal_xwR_mono (@wle segs) R Hsub STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k [] HJ)
       | split; [exact Hpr | exact HQ]].
Qed.
Section l.
Hypothesis LAWS : AR_laws_x.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Lemma blk_img_x : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> ~ in_img segs a.
Proof. intros ly S Hp W mem md p n a HAR Hin Hr. apply (alx_client_img LAWS ly S Hp W mem md a HAR). left. exists p, n. auto. Qed.
Lemma frm_img_x : forall ly S Hp W mem md cid pos a,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> ~ in_img segs a.
Proof. intros ly S Hp W mem md cid pos a HAR Hin Hr. apply (alx_client_img LAWS ly S Hp W mem md a HAR). right. left. exists cid, pos. auto. Qed.
(* the image band of a unit, from its own two segment witnesses (the shape of PAImg_prog.v:167-172 and
   ADIfacePostNA.v:57-62, both decided by vm_compute at the instance) *)
Lemma img_band_x : forall ly S Hp W mem md L H,
ARx ly S Hp W mem md ->
(exists sg, In sg segs /\ Z.of_N (seg_base sg) <= L) ->
(exists sg, In sg segs /\ H <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) ->
fst (ly_img ly) <= L /\ H <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S Hp W mem md L H HAR (sg1 & Hs1 & HL) (sg2 & Hs2 & HH).
destruct (alx_img LAWS ly S Hp W mem md HAR) as [Hseg _].
destruct (Hseg sg1 Hs1) as [A1 _]. destruct (Hseg sg2 Hs2) as [_ A2]. split; lia.
Qed.
(* HOFFB's shape *)
Lemma blk_off_band_x : forall ly S Hp W mem md L H p n,
ARx ly S Hp W mem md -> fst (ly_img ly) <= L -> H <= fst (ly_img ly) + snd (ly_img ly) -> L < H ->
In (p, n) (ablocks B ly S) -> p + req_size n <= L \/ H <= p.
Proof.
intros ly S Hp W mem md L H p n HAR HL HH HLH Hin.
destruct (Z_le_gt_dec (p + req_size n) L) as [E1|E1]; [left; exact E1|].
destruct (Z_le_gt_dec H p) as [E2|E2]; [right; exact E2|]. exfalso.
(* a live block is not empty: an empty one holds no hidden head, so alx_shadow's block_shadow gives
   0 <= req_size n, and req_size is never 0 *)
assert (Hpos : 0 < req_size n).
{ destruct (Z_lt_le_dec 0 (req_size n)) as [Q|Q]; [exact Q|].
  destruct (alx_shadow LAWS ly S Hp W mem md p n HAR Hin ltac:(intros h _ Hh; lia)) as [(_ & Q0 & _) _].
  exfalso. revert Q Q0. unfold req_size. destruct (Z.eqb_spec n 0); cbv beta iota; intros; lia. }
(* a := Z.max p L is in [p, p + req_size n) and in ly_img, which alx_client_img's block disjunct forbids *)
apply (proj1 (alx_client_img LAWS ly S Hp W mem md (Z.max p L) HAR
  ltac:(left; exists p, n; split; [exact Hin | lia]))).
unfold in_zr. lia.
Qed.
(* HOFFF / FS_HI's shape *)
Lemma frm_above_band_x : forall ly S Hp W mem md H cid pos,
ARx ly S Hp W mem md -> H <= fst (ly_img ly) + snd (ly_img ly) ->
In (cid, pos) (frames S) -> H <= frame_addr ly cid pos.
Proof.
intros ly S Hp W mem md H cid pos HAR HH Hin.
pose proof (proj2 (alx_img LAWS ly S Hp W mem md HAR) cid pos Hin). lia.
Qed.
(* the real stack's bounds and alignment, from field 18 (layout_ok's lo_top): the stack is inside
   [kHighMemBeg, kHighMemEnd], and both its bounds are page aligned, so 64-byte aligned *)
Lemma stk_bounds_x : forall ly S Hp W mem md,
ARx ly S Hp W mem md -> kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof.
intros ly S Hp W mem md HAR.
pose proof (lo_top _ (alx_layout_ok LAWS ly S Hp W mem md HAR)) as (_ & _ & _ & Hhi & _ & _ & Hbeg).
exact (conj Hbeg Hhi).
Qed.
Lemma stk_aligned_x : forall ly S Hp W mem md,
ARx ly S Hp W mem md -> ly_stk_lo ly mod 64 = 0 /\ ly_stk_hi ly mod 64 = 0.
Proof.
intros ly S Hp W mem md HAR.
pose proof (lo_top _ (alx_layout_ok LAWS ly S Hp W mem md HAR)) as (_ & _ & _ & _ & Plo & Phi & _).
unfold page_aligned in Plo, Phi. split.
- apply Z.mod_divide in Plo as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((q * 64) * 64) by lia. apply Z.mod_mul. lia.
- apply Z.mod_divide in Phi as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((q * 64) * 64) by lia. apply Z.mod_mul. lia.
Qed.
(* field 19 with fs_frame_bytes_ok: a live fake frame spans at least 64 bytes, a multiple of 64 *)
Lemma frame_bytes_x : forall ly S Hp W mem md cid pos,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
Proof.
intros ly S Hp W mem md cid pos HAR Hin. apply fs_frame_bytes_ok.
exact (proj1 (alx_frames_cid LAWS ly S Hp W mem md cid pos HAR Hin)).
Qed.
(* field 22's consumer form: a range that starts inside a hidden head is not addressable (it refutes prhPj_rslot's
   case `doc < b + cf_head`, PRH_FnPj.v) *)
Lemma hhead_not_addressable_x : forall ly S Hp W mem md b n p len,
ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> In b Hp -> b <= p < b + hl -> 0 < len ->
~ range_addressable (aview segs (w_H W) mem) SHADOW_OFF p len.
Proof.
intros ly S Hp W mem md b n p len HAR Hb Hin Hpr Hl RA.
destruct (RA p ltac:(lia)) as (s & Hs & Ok).
pose proof (alx_hhead LAWS ly S Hp W mem md b n p HAR Hb Hin Hpr) as E.
unfold shadow_addr in E. unfold shadow_of_addr in Hs. rewrite E in Hs. injection Hs as <-.
unfold saddr_ok in Ok. lia.
Qed.
(* field 23 with field 8: YGcallSx.v's FFLX (the flag byte is runtime owned, in application memory, off the image) *)
Lemma fflx_of_flag_law : forall ly S Hp (W : world segs) mem md cid pos,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img segs (flag_addr ly cid pos)).
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
destruct (alx_flag LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Hown & Hia & _).
destruct (alx_client_img LAWS ly S Hp W mem md (flag_addr ly cid pos) HAR
  (or_intror (or_intror (ex_intro _ cid (ex_intro _ pos (conj Hin eq_refl)))))) as [_ Himg].
split; [exact Hown|]. split; [apply (in_app_addr _ _ _ Hia); lia | exact Himg].
Qed.
(* the journal at a function's entry, over a reflexive world relation R *)
Lemma ajournal_x_initR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
forall STK FP ly S Hp W regs mem md ch,
afn_pre_x STK ly S Hp W regs mem md ch -> ajournal_xR R STK (spZ regs) FP ly S Hp W mem md [] ly S Hp W mem md 0.
Proof.
intros R R_refl STK FP ly S Hp W regs mem md ch (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
split; [exact HAR|]. split; [apply layout_le_refl|]. split; [zlia|]. split; [apply R_refl|]. split; [apply aos_step_refl|].
split; [reflexivity|]. split; [zlia|]. split; [zlia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros p n i H1 H2; exfalso; exact (H2 H1)|].
split; [exact Hpres|]. split; [exact Hstk|]. split; [intros; reflexivity|]. split; [exact HQT | apply wild_part_same].
Qed.
Lemma ajournal_x_init : forall STK FP ly S Hp W regs mem md ch,
afn_pre_x STK ly S Hp W regs mem md ch -> ajournal_x STK (spZ regs) FP ly S Hp W mem md [] ly S Hp W mem md 0.
Proof. exact (ajournal_x_initR (@wle segs) (wle_refl segs)). Qed.
Lemma ajournal_x_mono_k : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k k',
ajournal_x STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> k <= k' ->
ajournal_x STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k'.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k k' HJ Hkk.
pose proof (ajx_nev HJ) as Hnev. pose proof (ajx_k HJ) as Hk.
refine (ajx_intro (ajx_ar HJ) (ajx_ly HJ) (ajx_secs HJ) (ajx_wle HJ) (ajx_io HJ) (ajx_frs HJ) _ _ (ajx_hi HJ) (ajx_blk HJ)
  (ajx_img HJ) (ajx_frm HJ) (ajx_gone HJ) (ajx_pres HJ) (ajx_stk HJ) (ajx_extra HJ) (ajx_qt HJ) (ajx_wild HJ)); zlia.
Qed.
Lemma sep_blocks_x : forall ly S Hp W mem md b m p n,
ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
zdisjoint (b, req_size m) (p, req_size n).
Proof.
intros ly S Hp W mem md b m p n HAR H1 H2 Hne.
destruct (alx_sep LAWS ly S Hp W mem md HAR) as [Hq _]. apply pairwise_app_l in Hq as [Hq _].
apply (pairwise_zdisjoint_split _ (b, req_size m) (p, req_size n) Hq).
exact (map_split_2 (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ _ _ (in_split_2 _ _ _ H1 H2 Hne)).
Qed.
Lemma sep_block_frame_x : forall ly S Hp W mem md b m cid pos,
ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> In (cid, pos) (frames S) ->
zdisjoint (b, req_size m) (frame_addr ly cid pos, fs_frame_bytes cid).
Proof.
intros ly S Hp W mem md b m cid pos HAR H1 H2.
destruct (alx_sep LAWS ly S Hp W mem md HAR) as [Hq _].
apply in_split in H1 as (l1 & l2 & E1). apply in_split in H2 as (f1 & f2 & E2).
eapply (pairwise_In2 zdisjoint _ _ _ (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l1)
(map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l2 ++ map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) f1)
(map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) f2) Hq).
rewrite E1, E2, !map_app. cbn. rewrite <- !app_assoc. cbn. reflexivity.
Qed.
Lemma sep_frames_pos_x : forall ly S Hp W mem md f g l1 l2 l3,
ARx ly S Hp W mem md -> frames S = l1 ++ f :: l2 ++ g :: l3 ->
zdisjoint (frame_rng ly f) (frame_rng ly g).
Proof.
intros ly S Hp W mem md f g l1 l2 l3 HAR E.
destruct (alx_sep LAWS ly S Hp W mem md HAR) as [Hq _]. apply pairwise_app_l in Hq as [_ Hq].
rewrite E, !map_app in Hq. cbn in Hq. rewrite map_app in Hq. cbn in Hq.
exact (pairwise_In2 zdisjoint _ _ _ _ _ _ Hq eq_refl).
Qed.
Lemma frames_bounds_x : forall ly S Hp W mem md cid pos,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= YM05.alloc_ceiling /\
in_app (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
destruct (alx_sep LAWS ly S Hp W mem md HAR) as [_ Hf].
pose proof (proj1 (Forall_forall _ _) Hf _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2.
destruct (alx_frames LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Happ & _). auto.
Qed.
Lemma awr_byte_cases_xR : forall (R : world segs -> world segs -> Prop),
forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k a,
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
~ aowned B lyc Sc a /\
((YM05.alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))))).
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k a HJ Hw.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfr. pose proof (ajxR_stk HJ) as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & _). pose proof (ajxR_qt HJ) as HQT. clear HJ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hw as [Hs | [(Hfp & b & n & Hin & Hr) | [(b & n & Hin & Hn0 & Hr) | Hof]]].
- split; [|left; zlia]. apply (alx_stack LAWS lyc Sc Hpc Wc memc mdc a HAR).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _). rewrite Elo, Ehi. zlia.
- destruct (alx_blocks LAWS lyc Sc Hpc Wc memc mdc b n HAR Hin) as (_ & H4096 & Hceilb & [Hh1 Hh2] & Hb & _).
split; [exact (proj2 (Hb a Hr))|]. right; left. split; [exact (in_app_addr _ _ _ (conj Hh1 Hh2) Hr)|]. exists b, n. auto.
- destruct (alx_blocks LAWS lyc Sc Hpc Wc memc mdc b n HAR Hin) as (_ & H4096 & Hceilb & [Hh1 Hh2] & Hb & _).
split; [exact (proj2 (Hb a Hr))|]. right; left. split; [exact (in_app_addr _ _ _ (conj Hh1 Hh2) Hr)|]. exists b, n. auto.
- destruct Hof as (cid & pos & Hin & Hr).
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hin).
destruct (alx_frames LAWS lyc Sc Hpc Wc memc mdc cid pos HAR Hin') as (_ & [Hh1 Hh2] & Hb & Hsh).
destruct (frames_bounds_x lyc Sc Hpc Wc memc mdc cid pos HAR Hin') as (Hf0 & Hfc & _).
destruct Hr as [Hr | Hr].
+ unfold in_zr in Hr; cbn [fst snd] in Hr. split; [exact (proj2 (Hb a Hr))|].
right; right. exists cid, pos. split; [exact Hin|]. left. split; [exact (in_app_addr _ _ _ (conj Hh1 Hh2) Hr)|]. exact Hr.
+ unfold in_zr in Hr; cbn [fst snd] in Hr. split.
* specialize (Hsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh by zlia.
exact (proj2 Hsh).
* right; right. exists cid, pos. split; [exact Hin|]. right. split; [|exact Hr].
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)).
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)). zlia.
Qed.
Lemma awr_byte_cases_x : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k a,
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
~ aowned B lyc Sc a /\
((YM05.alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))))).
Proof. exact (awr_byte_cases_xR (@wle segs)). Qed.
(* a write inside the segment's permission keeps the journal, over any world relation R (the world is unchanged) *)
Lemma ajournal_x_after_writeR : forall (R : world segs -> world segs -> Prop),
forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' Hp' own2,
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) ->
ARx lyc S' Hp' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' -> st_depot S' = st_depot Sc ->
ajournal_xR R STK sp0 FP ly S Hp W mem md own2 lyc S' Hp' Wc memc' mdc' k.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr S' Hp' own2 HJ Heqw Hgr Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT' Edep'.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hrel. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_img HJ) as F3. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_gone HJ) as Hgone. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWw : forall a, Wr a ->
(~ aowned B lyc Sc a /\
((YM05.alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))))))
\/ (aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)).
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx]; [left; exact (awr_byte_cases_xR R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hrel|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs'|]. split; [zlia|]. split; [exact Hk|]. rewrite !Eab'. split.
{
intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[_ Hs'] | [[[_ Hlow] _] | (cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]])]]) | (_ & Hx)]; [exact (Hs Hs') | zlia | zlia | zlia | zlia]. }
split.
{
intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
destruct (alx_blocks LAWS lyc Sc Hpc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx)].
- zlia.
- exact (Hnf Hfp).
-
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
pose proof (sep_blocks_x lyc Sc Hpc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (sep_block_frame_x lyc Sc Hpc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in Hd, Hr. zlia.
- zlia.
-
exfalso. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (alx_blocks LAWS lyc Sc Hpc Wc memc mdc p n HAR H2))))) (p + i) ltac:(zlia)) Hxo). }
split.
{
intros a Hi Hns He Hpst Hsp. rewrite <- (F3 a Hi Hns He Hpst Hsp). pose proof (segs_low a Hi) as Hal'.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx & Hxi)].
- zlia.
- exact (blk_img_x _ _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img_x _ _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- zlia.
- exact (Hxi Hi). }
split.
{
intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds_x lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)) as Hse.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]) | (Hxo & Hx)].
- zlia.
- destruct Hr as [Hr | Hr]; [|zlia].
pose proof (sep_block_frame_x lyc Sc Hpc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
{ eapply (sep_frames_pos_x lyc Sc Hpc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
destruct (frames_bounds_x lyc Sc Hpc Wc memc mdc c' p' HAR ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity)) as (Hf0' & Hfc' & Hfh').
pose proof (shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
pose proof (fs_frame_bytes_nonneg c') as Hnn'.
destruct Hr' as [[[Hlo0' Hlo'] Hr'] | [[Hlo1' Hhi'] Hr']]; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'.
+ destruct Hr as [Hr | Hr]; [zlia | zlia].
+ destruct Hr as [Hr | Hr]; [zlia |].
destruct Hd as [Hd | Hd].
* pose proof (shadow_mono _ _ Hd). zlia.
* pose proof (shadow_mono _ _ Hd). zlia.
-
destruct (alx_frames LAWS lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (_ & _ & Hfb & Hfsh).
rewrite <- ?Efa in Hr.
exfalso. destruct Hr as [Hr|Hr]; [exact (proj2 (Hfb a Hr) Hxo)|].
specialize (Hfsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hfsh by zlia.
exact (proj2 Hfsh Hxo). }
split; [exact Hgone|].
split; [intros a Ha; apply Hgr; apply Hpres, Ha|].
split; [exact Hstatic|]. split; [|split; [exact HQT' | rewrite Edep'; exact (ajxR_wild HJ)]].
{
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (alx_extra LAWS lyc Sc Hpc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros HWa. exfalso.
destruct (HWw a HWa) as [(_ & [[Hc' Hs'] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] Hr]])]]) | (Hxo & Hx)].
- apply Xs. rewrite Eslo, Eshi. zlia.
- exact (Xb b m Hbin Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (proj1 (Xf cid pos Hin') Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr in Hr; cbn [fst snd] in Hr. exact (proj2 (Xf cid pos Hin') Hr).
- exact (Xo Hxo). }
Qed.
Lemma ajournal_x_after_write : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' Hp' own2,
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) ->
ARx lyc S' Hp' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' -> st_depot S' = st_depot Sc ->
ajournal_x STK sp0 FP ly S Hp W mem md own2 lyc S' Hp' Wc memc' mdc' k.
Proof. exact (ajournal_x_after_writeR (@wle segs)). Qed.
(* a step that writes only bytes the segment may write keeps the journal, over any world relation R *)
Lemma ajournal_x_execR : forall (R : world segs -> world segs -> Prop),
forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr HJ Hfr Hgr Hhid Hsame HW.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_frs HJ) as Hfrs.
pose proof (ajxR_qt HJ) as HQT.
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
pose proof (same_but_materialized_wvb mdc mdc' Hsame) as Emd.
eapply (ajournal_x_after_writeR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr Sc Hpc own HJ Heqw
ltac:(intros a Ha; eapply apresent_grows; [exact Hgr | exact Ha]) Hsame);
[intros a Ha; left; exact (HW a Ha) | | reflexivity | reflexivity | zlia | exact Hfrs | exact HQT | reflexivity].
eapply (alx_frame LAWS); [exact HAR | | | | | |].
- intros a Ha Ho. apply Heqw; [exact Ha|]. intros HWa. exact (proj1 (awr_byte_cases_xR R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (HW _ HWa)) Ho).
- intros a Hv. eapply aview_keeps_vis; [exact Hgr | exact Hv].
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- intros a _ Hh. exact (Hhid _ Hh).
Qed.
Lemma ajournal_x_exec : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof. exact (ajournal_x_execR (@wle segs)). Qed.
(* materializing the lazy memory keeps the journal, over any world relation R *)
Lemma ajournal_x_materializeR : forall (R : world segs -> world segs -> Prop),
forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k X,
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc (with_vm_backing (m_vm_lazy mdc) X mdc) k.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k X HJ.
eapply (ajournal_x_execR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc _ (fun _ => False) HJ);
[intros x _; reflexivity | apply mem_grows_refl | intros x _; reflexivity | apply same_but_materialized_wvb_any | intros a Ha; destruct Ha].
Qed.
Lemma ajournal_x_materialize : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k X,
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc (with_vm_backing (m_vm_lazy mdc) X mdc) k.
Proof. exact (ajournal_x_materializeR (@wle segs)). Qed.
(* A write of the program's own statics only (PST), over any world relation R: the bytes are image bytes the runtime
   does not own, so the invariant and every clause of the journal but the PST-exempt image clause hold unchanged. *)
Lemma ajournal_x_pst_writeR : forall (R : world segs -> world segs -> Prop),
forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc',
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Exists (in_zr (bv_unsigned x)) PST -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' HJ Hfr Hgr Hhid Hsame.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_img HJ) as F3. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_gone HJ) as Hgone. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ Exists (in_zr a) PST -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
assert (HPl : forall a, Exists (in_zr a) PST -> 0 <= a < kLowMemEnd).
{ intros a Ha. exact (segs_low a (proj1 (PST_ok a Ha))). }
pose proof (same_but_materialized_wvb mdc mdc' Hsame) as Emd.
assert (HAR' : ARx lyc Sc Hpc Wc memc' mdc').
{ eapply (alx_frame LAWS); [exact HAR | | | | | |].
- intros a Ha Ho. apply Heqw; [exact Ha|]. intros Hq. destruct (PST_ok a Hq) as [Hi Hno].
exact (Hno (proj1 (alx_owned_image LAWS lyc Sc Hpc Wc memc mdc a HAR Hi) Ho)).
- intros a Hv. eapply aview_keeps_vis; [exact Hgr | exact Hv].
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- intros a _ Hh. exact (Hhid _ Hh). }
split; [exact HAR'|].
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split.
{ intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [zlia|]. intros Hq. pose proof (HPl a Hq). zlia. }
split.
{ intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
destruct (alx_blocks LAWS lyc Sc Hpc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & _).
apply Heqw; [zlia|]. intros Hq.
exact (blk_img_x lyc Sc Hpc Wc memc mdc p n (p + i) HAR H2 ltac:(zlia) (proj1 (PST_ok _ Hq))). }
split.
{ intros a Hi Hns He Hpst Hsp. rewrite <- (F3 a Hi Hns He Hpst Hsp). pose proof (segs_low a Hi).
apply Heqw; [zlia | exact Hpst]. }
split.
{ intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds_x lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. rewrite <- Efa in Hr.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)) as Hse.
apply Heqw; [destruct Hr as [Hr|Hr]; zlia|]. intros Hq. pose proof (HPl a Hq) as Hpl.
destruct Hr as [Hr|Hr]; [|zlia].
exact (frm_img_x lyc Sc Hpc Wc memc mdc cid pos a HAR HinC Hr (proj1 (PST_ok _ Hq))). }
split; [exact Hgone|].
split; [intros a Ha; eapply apresent_grows; [exact Hgr | apply Hpres, Ha]|].
split; [exact Hstatic|]. split; [|split; [exact HQT | exact (ajxR_wild HJ)]].
{ intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (alx_extra LAWS lyc Sc Hpc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros Hq. exact (Xi (proj1 (PST_ok a Hq))). }
Qed.
(* A write of the program's own statics only (PST): the bytes are image bytes the runtime does not own, so the
   invariant and every clause of the journal but the PST-exempt image clause hold unchanged. *)
Lemma ajournal_x_pst_write : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc',
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Exists (in_zr (bv_unsigned x)) PST -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof. exact (ajournal_x_pst_writeR (@wle segs)). Qed.
(* A write confined to bytes of the CALLER'S OWN FRAMES that the footprint names: the journal's frames clause exempts
   exactly the FP bytes of a frame of S, so every other clause holds unchanged. This is what a function that writes an
   output through a caller's pointer into the caller's frame needs; awr_byte does not reach those bytes (its frame case
   is the function's own frames). *)
Definition wr_fp_frame (FP : list (Z * Z)) (S : astate) (lyc : alayout) (a : Z) : Prop :=
inFP FP a /\ exists cid pos, In (cid, pos) (frames S) /\ in_zr a (frame_rng lyc (cid, pos)).
(* ajournal_x_frame_write below over any world relation R (the world is unchanged) *)
Lemma ajournal_x_frame_writeR : forall (R : world segs -> world segs -> Prop),
forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc',
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ wr_fp_frame FP S lyc (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' HJ Hfr Hgr Hhid Hsame.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_img HJ) as F3. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_gone HJ) as Hgone. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ wr_fp_frame FP S lyc a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
(* a written byte sits in a frame of Sc: not owned, in application memory, below the ceiling, outside the image *)
assert (HWf : forall a, wr_fp_frame FP S lyc a ->
~ aowned B lyc Sc a /\ ~ in_img segs a /\ 4096 <= a < YM05.alloc_ceiling /\
(forall b n, In (b, n) (ablocks B lyc Sc) -> ~ (b <= a < b + req_size n))).
{ intros a (Hfp & cid & pos & Hin & Hr).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
destruct (frames_bounds_x lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
destruct (alx_frames LAWS lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (_ & _ & Hfb & _).
split; [exact (proj2 (Hfb a Hr))|].
split; [exact (frm_img_x lyc Sc Hpc Wc memc mdc cid pos a HAR HinC Hr)|].
split; [zlia|].
intros b n Hbin Hrb.
pose proof (sep_block_frame_x lyc Sc Hpc Wc memc mdc b n cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
pose proof (same_but_materialized_wvb mdc mdc' Hsame) as Emd.
assert (HAR' : ARx lyc Sc Hpc Wc memc' mdc').
{ eapply (alx_frame LAWS); [exact HAR | | | | | |].
- intros a Ha Ho. apply Heqw; [exact Ha|]. intros Hq. exact (proj1 (HWf a Hq) Ho).
- intros a Hv. eapply aview_keeps_vis; [exact Hgr | exact Hv].
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- intros a _ Hh. exact (Hhid _ Hh). }
split; [exact HAR'|].
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split.
{ intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [zlia|]. intros Hq. pose proof (HWf a Hq) as (_ & _ & Hb & _). zlia. }
split.
{ intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
destruct (alx_blocks LAWS lyc Sc Hpc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & _).
apply Heqw; [zlia|]. intros Hq. exact (proj2 (proj2 (proj2 (HWf _ Hq))) p n H2 ltac:(zlia)). }
split.
{ intros a Hi Hns He Hpst Hsp. rewrite <- (F3 a Hi Hns He Hpst Hsp). pose proof (segs_low a Hi).
apply Heqw; [zlia|]. intros Hq. exact (proj1 (proj2 (HWf a Hq)) Hi). }
split.
{ intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds_x lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. rewrite <- Efa in Hr.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)) as Hse.
apply Heqw; [destruct Hr as [Hr|Hr]; zlia|]. intros (Hfp & _). exact (Hnf Hfp). }
split; [exact Hgone|].
split; [intros a Ha; eapply apresent_grows; [exact Hgr | apply Hpres, Ha]|].
split; [exact Hstatic|]. split; [|split; [exact HQT | exact (ajxR_wild HJ)]].
{ intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (alx_extra LAWS lyc Sc Hpc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros (Hfp & cid & pos & Hin & Hr).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact (proj1 (Xf cid pos HinC) Hr). }
Qed.
Lemma ajournal_x_frame_write : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc',
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ wr_fp_frame FP S lyc (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof. exact (ajournal_x_frame_writeR (@wle segs)). Qed.
(* a byte of a live frame is in no live block (sep_block_frame_x, both read at one state) *)
Lemma frame_not_block_x : forall ly S Hp W mem md f p n a,
ARx ly S Hp W mem md -> In f (frames S) -> In (p, n) (ablocks B ly S) ->
in_zr a (frame_rng ly f) -> p <= a < p + req_size n -> False.
Proof.
intros ly S Hp W mem md [cid pos] p n a HAR Hf Hb Ha Hpn.
pose proof (sep_block_frame_x ly S Hp W mem md p n cid pos HAR Hb Hf) as Hd.
unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *. zlia.
Qed.
(* A segment that writes BOTH its own window (awr_byte) AND an output through a caller's pointer into one of the
   caller's frames that its footprint names: the two write sets are separated and the two write lemmas composed, so
   no clause of the journal is re-proved. Every harness function with a frame of its own that fills a caller's output
   needs this. *)
Definition wr_fp_frame_b (FP : list (Z * Z)) (S : astate) (lyc : alayout) (a : Z) : bool :=
existsb (fun r => (fst r <=? a) && (a <? snd r)) FP &&
existsb (fun f => (frame_addr lyc (fst f) (snd f) <=? a) &&
                  (a <? frame_addr lyc (fst f) (snd f) + fs_frame_bytes (fst f))) (frames S).
Lemma wr_fp_frame_b_true : forall FP S lyc a, wr_fp_frame_b FP S lyc a = true -> wr_fp_frame FP S lyc a.
Proof.
intros FP S lyc a Hb. unfold wr_fp_frame_b in Hb. apply andb_prop in Hb as [H1 H2].
apply existsb_exists in H1 as (r & Hr & Hb1). apply andb_prop in Hb1 as [Ha1 Ha2].
apply Z.leb_le in Ha1. apply Z.ltb_lt in Ha2.
apply existsb_exists in H2 as (f & Hf & Hb2). apply andb_prop in Hb2 as [Hc1 Hc2].
apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2.
split; [exists r; split; [exact Hr | zlia]|].
exists (fst f), (snd f). split; [rewrite <- surjective_pairing; exact Hf|].
unfold in_zr, frame_rng. cbn [fst snd]. zlia.
Qed.
Lemma wr_fp_frame_b_complete : forall FP S lyc a, wr_fp_frame FP S lyc a -> wr_fp_frame_b FP S lyc a = true.
Proof.
intros FP S lyc a ((r & Hr & Ha) & cid & pos & Hf & Hz). unfold wr_fp_frame_b. apply andb_true_intro. split.
- apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; zlia.
- apply existsb_exists. exists (cid, pos). split; [exact Hf|]. unfold in_zr, frame_rng in Hz. cbn [fst snd] in *.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; zlia.
Qed.
(* ajournal_x_exec_fr below over any world relation R: the same split, over ajournal_x_frame_writeR and
   ajournal_x_execR *)
Lemma ajournal_x_exec_frR : forall (R : world segs -> world segs -> Prop),
forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr HJ Hfr Hgr Hhid Hsame HW.
pose (memc1 := fun x : word => if wr_fp_frame_b FP S lyc (bv_unsigned x) then memc' x else memc x).
assert (E1 : forall x, wr_fp_frame_b FP S lyc (bv_unsigned x) = false -> memc1 x = memc x)
  by (intros x Hx; unfold memc1; rewrite Hx; reflexivity).
assert (E2 : forall x, wr_fp_frame_b FP S lyc (bv_unsigned x) = true -> memc1 x = memc' x)
  by (intros x Hx; unfold memc1; rewrite Hx; reflexivity).
assert (Hmr : forall (m m' : word -> option byte) x, m x = m' x -> mrestrict (w_H Wc) m x = mrestrict (w_H Wc) m' x)
  by (intros m m' x Hx; unfold mrestrict; destruct (w_H Wc x); [reflexivity | exact Hx]).
assert (HJ1 : ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc1 mdc k).
{ eapply (ajournal_x_frame_writeR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc1 mdc HJ).
  - intros x Hx. apply Hmr. apply E1.
    destruct (wr_fp_frame_b FP S lyc (bv_unsigned x)) eqn:Eb; [exfalso; exact (Hx (wr_fp_frame_b_true _ _ _ _ Eb)) | reflexivity].
  - intros x Hx. destruct (wr_fp_frame_b FP S lyc (bv_unsigned x)) eqn:Eb.
    + rewrite (Hmr memc1 memc' x (E2 x Eb)). apply Hgr. exact Hx.
    + rewrite (Hmr memc1 memc x (E1 x Eb)). exact Hx.
  - intros x Hx. destruct (wr_fp_frame_b FP S lyc (bv_unsigned x)) eqn:Eb;
      [rewrite (E2 x Eb); exact (Hhid x Hx) | exact (E1 x Eb)].
  - apply same_but_materialized_refl. }
eapply (ajournal_x_execR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc1 mdc k memc' mdc'
  (fun a => Wr a /\ ~ wr_fp_frame FP S lyc a) HJ1).
- intros x Hx. destruct (wr_fp_frame_b FP S lyc (bv_unsigned x)) eqn:Eb.
  + apply Hmr. symmetry. exact (E2 x Eb).
  + rewrite (Hmr memc1 memc x (E1 x Eb)). apply Hfr. intros HWx. apply Hx. split; [exact HWx|].
    intros Hq. rewrite (wr_fp_frame_b_complete _ _ _ _ Hq) in Eb. discriminate Eb.
- intros x Hx. destruct (wr_fp_frame_b FP S lyc (bv_unsigned x)) eqn:Eb.
  + rewrite (Hmr memc1 memc' x (E2 x Eb)) in Hx. exact Hx.
  + rewrite (Hmr memc1 memc x (E1 x Eb)) in Hx. apply Hgr. exact Hx.
- intros x Hx. destruct (wr_fp_frame_b FP S lyc (bv_unsigned x)) eqn:Eb;
    [rewrite (E2 x Eb); reflexivity | rewrite (E1 x Eb); exact (Hhid x Hx)].
- exact Hsame.
- intros a (HWa & Hnf). destruct (HW a HWa) as [Hw | Hq]; [exact Hw | exfalso; exact (Hnf Hq)].
Qed.
Lemma ajournal_x_exec_fr : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof. exact (ajournal_x_exec_frR (@wle segs)). Qed.
(* THE callee-footprint side condition of a call, one name for every caller (WalkS4's fp_sub_xW, PRW_CallerJ.v at
   origin/cold/h-hpreset-7-walk-S4 85a188622c5): a byte the callee's footprint names is the caller's footprint, a
   temporary block, a slot of a frame the caller took since its entry, or a byte of the caller's own stack window.
   The fourth case needs no `alloc_ceiling <= a`: the caller's journal carries astk_ok, so its window lies at or above
   alloc_ceiling and the block, frame and sink clauses refute the case themselves. *)
Definition fp_sub_x (STK sp0 : Z) (FP FP1 : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) : Prop :=
  forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
    (exists f, In f own /\ in_zr a (frame_rng lyc f)) \/ (sp0 - STK <= a < sp0).
(* the caller's journal to the call and the callee's journal over the call compose; the budgets add; over a
   transitive world relation R *)
Lemma ajournal_xw_subR : forall (R : world segs -> world segs -> Prop), (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 WS0 WS1,
ajournal_xwR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS0 ->
ajournal_xwR R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
fp_sub_x STK sp0 FP FP1 ly S own lyc Sc ->
ajournal_xwR R STK sp0 FP ly S Hp W mem md (nf ++ own) ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1).
Proof.
intros R R_trans STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 WS0 WS1
HJ HJ1 Hlo Hhi HF.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs.
pose proof (ajxR_rel HJ) as Hrel. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs.
pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2.
pose proof (ajxR_img HJ) as F3. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_gone HJ) as Hgone.
pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5.
pose proof (ajxR_qt HJ) as HQT. pose proof (ajxR_wild HJ) as Hwild.
pose proof (ajxR_ar HJ1) as HAR2. pose proof (ajxR_ly HJ1) as Hly2. pose proof (ajxR_secs HJ1) as Hsecs2.
pose proof (ajxR_rel HJ1) as Hrel2. pose proof (ajxR_io HJ1) as Hio2. pose proof (ajxR_frs HJ1) as Hfrs2.
pose proof (ajxR_nev HJ1) as Hnev2. pose proof (ajxR_k HJ1) as Hk2. pose proof (ajxR_hi HJ1) as G1. pose proof (ajxR_blk HJ1) as G2.
pose proof (ajxR_img HJ1) as G3. pose proof (ajxR_frm HJ1) as G4. pose proof (ajxR_gone HJ1) as Hgone2.
pose proof (ajxR_pres HJ1) as Hpres2. pose proof (ajxR_stk HJ1) as Hstatic2. pose proof (ajxR_extra HJ1) as G5.
pose proof (ajxR_qt HJ1) as HQT2. pose proof (ajxR_wild HJ1) as Hwild2.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_layout LAWS _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
split; [exact HAR2|].
split; [eapply layout_le_trans; [exact Hsecs | exact Hly | exact Hly2]|].
split; [zlia|]. split; [eapply R_trans; eassumption|].
assert (HFo : YI16.sink_open_fp FP1 -> YI16.sink_open_fp FP).
{ intros (r & Hr & H0). destruct (HF 0 (ex_intro _ r (conj Hr H0))) as [Hf | [(b & n & Hin & _ & Hb) | [([cid pos] & Hfo & Hfr) | Hw4]]].
- exact Hf.
- exfalso. pose proof (alx_blocks LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & _). zlia.
- exfalso. assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hfo).
  destruct (frames_bounds_x lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & _).
  unfold frame_rng, in_zr in Hfr. cbn [fst snd] in Hfr. zlia.
- exfalso. zlia. }
split; [eapply aos_step_trans_fp; [exact HFo | exact Hio | exact Hio2]|].
split; [rewrite Hfrs2, Hfrs, app_assoc; reflexivity|]. split; [zlia|]. split; [zlia|].
split.
{   intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply G1; [exact Ha | zlia]. }
split.
{   intros p n i H1 H2 Hi Hnf.
assert (Hc2 : In (p, n) (ablocks B lyc Sc)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [exact Hc|].
exfalso. exact (Hnf (Hgone p n i H1 Hc Hi)). }
rewrite <- (F2 p n i H1 Hc2 Hi Hnf). apply (G2 p n i Hc2); [exact H2 | exact Hi |].
intros Hf1. destruct (HF _ Hf1) as [Hf | [(b & m & Hbin & Hb0 & Hr) | [(f & Hfo & Hfr) | Hw4]]]; [exact (Hnf Hf)| | |].
- assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
  pose proof (sep_blocks_x lyc Sc Hpc Wc memc mdc b m p n HAR Hbin Hc2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- exfalso. apply (frame_not_block_x lyc Sc Hpc Wc memc mdc f p n (p + i) HAR);
  [rewrite Hfrs; apply in_or_app; left; exact Hfo | exact Hc2 | exact Hfr | zlia].
- exfalso. destruct (alx_blocks LAWS lyc Sc Hpc Wc memc mdc p n HAR Hc2) as (_ & _ & Hce & _). zlia. }
split.
{   intros a Hi Hns He Hpst Hsp. rewrite <- (F3 a Hi Hns He Hpst Hsp). apply (G3 a Hi Hns He Hpst). intros Ho1. exact (Hsp (HFo Ho1)). }
split.
{   intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
assert (Efr : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
apply (G4 cid pos a HinC).
- unfold frame_rng in *. cbn [fst snd] in *. rewrite Efr. exact Hr.
- intros Hf1. destruct (HF _ Hf1) as [Hf | [(b & m & Hbin & Hb0 & Hrb) | [([cidf posf] & Hfo & Hfr) | Hw4]]]; [exact (Hnf Hf)| | |].
  + destruct (frames_bounds_x lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
    destruct (alx_blocks LAWS lyc Sc Hpc Wc memc mdc b m HAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
    pose proof (sep_block_frame_x lyc Sc Hpc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
    unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *. rewrite Efr in Hd.
    pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)).
    pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)).
    pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
    destruct Hr as [Hr|Hr]; zlia.
  + (* the caller's own new frame (cidf, posf) and an entry frame (cid, pos) are two places of frames Sc *)
    assert (HinF : In (cidf, posf) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hfo).
    destruct (frames_bounds_x lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
    destruct (frames_bounds_x lyc Sc Hpc Wc memc mdc cidf posf HAR HinF) as (Hg0 & Hgc & Hgh).
    destruct (in_split _ _ Hfo) as (o1 & o2 & Eo). destruct (in_split _ _ Hin) as (s1 & s2 & Es).
    assert (Esc : frames Sc = o1 ++ (cidf, posf) :: (o2 ++ s1) ++ (cid, pos) :: s2)
      by (rewrite Hfrs, Eo, Es, <- !app_assoc; reflexivity).
    pose proof (sep_frames_pos_x lyc Sc Hpc Wc memc mdc _ _ _ _ _ HAR Esc) as Hd.
    unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *. rewrite Efr in Hd, Hf0, Hfc, Hfh.
    pose proof (fs_frame_bytes_nonneg cid).
    pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)).
    pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)).
    pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
    destruct Hr as [Hr|Hr]; zlia.
  + (* a byte of the caller's own stack window: a frame and its shadow are both below the ceiling *)
    exfalso.
    destruct (frames_bounds_x lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
    pose proof (fs_frame_bytes_nonneg cid).
    pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)).
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    destruct Hr as [Hr|Hr]; rewrite <- ?Efr in Hr; zlia. }
split.
{   intros p n i H1 H2 Hi.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [|exact (Hgone p n i H1 Hc Hi)].
assert (Hf1 : inFP FP1 (p + i)) by (apply (Hgone2 p n i Hc); [exact H2 | exact Hi]).
destruct (HF _ Hf1) as [Hf | [(b & m & Hbin & Hb0 & Hr) | [(f & Hfo & Hfr) | Hw4]]]; [exact Hf| | |].
- assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
  pose proof (sep_blocks_x lyc Sc Hpc Wc memc mdc b m p n HAR Hbin Hc Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- exfalso. apply (frame_not_block_x lyc Sc Hpc Wc memc mdc f p n (p + i) HAR);
  [rewrite Hfrs; apply in_or_app; left; exact Hfo | exact Hc | exact Hfr | zlia].
- exfalso. destruct (alx_blocks LAWS lyc Sc Hpc Wc memc mdc p n HAR Hc) as (_ & _ & Hce & _). zlia. }
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
(* the caller's journal to the call and the callee's journal over the call compose; the budgets add *)
Lemma ajournal_xw_sub : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 WS0 WS1,
ajournal_xw STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS0 ->
ajournal_xw STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
fp_sub_x STK sp0 FP FP1 ly S own lyc Sc ->
ajournal_xw STK sp0 FP ly S Hp W mem md (nf ++ own) ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1).
Proof. exact (ajournal_xw_subR (@wle segs) (wle_trans segs)). Qed.
(* the composition at the empty budget (every caller with no wild site), over a transitive R *)
Lemma ajournal_x_subR : forall (R : world segs -> world segs -> Prop), (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1,
ajournal_xR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
ajournal_xR R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
fp_sub_x STK sp0 FP FP1 ly S own lyc Sc ->
ajournal_xR R STK sp0 FP ly S Hp W mem md (nf ++ own) ly2 S2 Hp2 W2 mem2 md2 (k + k1).
Proof.
intros R R_trans STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 HJ HJ1 Hlo Hhi HF.
exact (ajournal_xw_subR R R_trans STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2
  mem2 md2 k1 [] [] HJ HJ1 Hlo Hhi HF).
Qed.
(* the composition at the empty budget (every caller with no wild site) *)
Lemma ajournal_x_sub : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1,
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
ajournal_x STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
fp_sub_x STK sp0 FP FP1 ly S own lyc Sc ->
ajournal_x STK sp0 FP ly S Hp W mem md (nf ++ own) ly2 S2 Hp2 W2 mem2 md2 (k + k1).
Proof. exact (ajournal_x_subR (@wle segs) (wle_trans segs)). Qed.
(* the callee's entry precondition at a call, from the caller's journal over any world relation R *)
Lemma afn_pre_x_atR : forall (R : world segs -> world segs -> Prop),
forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc STK1 (o : Z) ch1,
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
YK0s.ret_ok (getr regsc 1) -> 4096 <= raZ regsc ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
achain lyc (aview segs (w_H W) memc) (spZ regsc) (s0Z regsc) ch1 ->
afn_pre_x STK1 lyc Sc Hpc W regsc memc mdc ch1.
Proof.
intros R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc STK1 o ch1 HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop). pose proof (ajxR_qt HJ) as HQT.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
split; [exact HAR|]. split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp|]. split; [exact Htp|]. split.
- unfold astk_ok, ly_bot in *. rewrite Hsp, Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity.
- split; [|split; [exact Hch | exact HQT]]. intros a Ha. apply Hpres. rewrite Hsp in Ha. zlia.
Qed.
Lemma afn_pre_x_at : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc STK1 (o : Z) ch1,
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
YK0s.ret_ok (getr regsc 1) -> 4096 <= raZ regsc ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
achain lyc (aview segs (w_H W) memc) (spZ regsc) (s0Z regsc) ch1 ->
afn_pre_x STK1 lyc Sc Hpc W regsc memc mdc ch1.
Proof. exact (afn_pre_x_atR (@wle segs)). Qed.
(* An SRr run whose post keeps the world W and states SRrG at R there is an SRrG run at R: the post's world is W
   itself, so no law of R is used. The runners of Section e read YA0n.v's SRr_msteps at R through it. *)
Lemma SRr_SRrG_same : forall (R : world segs -> world segs -> Prop) W c Q,
SRr segs W c (fun W' c' => W' = W /\ SRrG segs R W c' Q) -> SRrG segs R W c Q.
Proof.
intros R W c Q H HI T HK. apply (H HI T). intros W' c' _ HI' [-> HG]. exact (HG HI' T HK).
Qed.
Section e.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.
Definition run_post_AJx (W : world segs) (E : env) (ss ss' : sstate)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ms' mat',
st_ok segs E ss' (restrict (w_H W) ms') ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* run_post_AJx over a world relation R: the journal at R and the conclusion SRrG segs R. *)
Definition run_post_AJxR (R : world segs -> world segs -> Prop) (W : world segs) (E : env) (ss ss' : sstate)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ms' mat',
st_ok segs E ss' (restrict (w_H W) ms') ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRrG segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* SRr_chain_AJx over a world relation R; the journal step is ajournal_x_execR. *)
Lemma SRr_chain_AJxR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
st_ok segs E ss' msr' ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJxR R W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R _ _ W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms HS' Hfr HJ Hwr Hk.
apply SRr_SRrG_same. apply (SRr_msteps segs Hwx W ms msr' mdc _ Hms).
intros model' Hsame Hcl. apply SRr_ret. split; [reflexivity|].
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply (ajournal_x_execR R) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_chain_AJx : forall W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
st_ok segs E ss' msr' ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_AJxR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_AJx over a world relation R. *)
Lemma SRr_run_AJxR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJxR R W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply (SRr_chain_AJxR R Rr Rt); [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_AJx : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_AJxR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_to_AJx over a world relation R. *)
Lemma SRr_run_to_AJxR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJxR R W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply (SRr_chain_AJxR R Rr Rt); [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_to_AJx : forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_AJxR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
Definition run_post_tok_AJx (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* run_post_tok_AJx over a world relation R: the journal at R and the conclusion SRrG segs R. *)
Definition run_post_tok_AJxR (R : world segs -> world segs -> Prop) (W : world segs) (E : env) (K : nat) (Bx : sv)
(SH : list shent) (ss : sstate) (st' : shst)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRrG segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* SRr_chain_tok_AJx over a world relation R; the journal step is ajournal_x_execR. *)
Lemma SRr_chain_tok_AJxR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJxR R W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R _ _ W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HS' Hsh' Hfr HJ Hwr Hk.
apply SRr_SRrG_same. apply (SRr_msteps segs Hwx W ms msr' mdc _ Hms).
intros model' Hsame Hcl. apply SRr_ret. split; [reflexivity|].
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_execR R) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_chain_tok_AJx : forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJx W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_tok_AJxR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_tok_AJx over a world relation R. *)
Lemma SRr_run_tok_AJxR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok segs tbl K Bx Bspan SH n ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJxR R W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_tok_sound segs tbl K Bx Bspan SH tbl_ok n E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply (SRr_chain_tok_AJxR R Rr Rt); [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_tok_AJx : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok segs tbl K Bx Bspan SH n ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJx W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_tok_AJxR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_to_tok_AJx over a world relation R. *)
Lemma SRr_run_to_tok_AJxR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJxR R W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_to_tok_sound segs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply (SRr_chain_tok_AJxR R Rr Rt); [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_to_tok_AJx : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJx W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_tok_AJxR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_chain_AJx_pst over a world relation R; the journal step is ajournal_x_pst_writeR. *)
Lemma SRr_chain_AJx_pstR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
st_ok segs E ss' msr' ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> Exists (in_zr a) PST) ->
run_post_AJxR R W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R _ _ W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms HS' Hfr HJ Hwr Hk.
apply SRr_SRrG_same. apply (SRr_msteps segs Hwx W ms msr' mdc _ Hms).
intros model' Hsame Hcl. apply SRr_ret. split; [reflexivity|].
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply (ajournal_x_pst_writeR R); [exact HJ | | | |].
+ rewrite Hmm. intros x Hx. apply Hfr. intros Hw. exact (Hx (Hwr _ Hw)).
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_chain_AJx_pst : forall W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
st_ok segs E ss' msr' ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> Exists (in_zr a) PST) ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_AJx_pstR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_AJx_pst over a world relation R. *)
Lemma SRr_run_AJx_pstR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> Exists (in_zr a) PST) ->
run_post_AJxR R W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply (SRr_chain_AJx_pstR R Rr Rt); [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_AJx_pst : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> Exists (in_zr a) PST) ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_AJx_pstR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_chain_tok_AJx_frame over a world relation R; the journal step is ajournal_x_frame_writeR. *)
Lemma SRr_chain_tok_AJx_frameR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> wr_fp_frame FP S lyc a) ->
run_post_tok_AJxR R W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R _ _ W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HS' Hsh' Hfr HJ Hwr Hk.
apply SRr_SRrG_same. apply (SRr_msteps segs Hwx W ms msr' mdc _ Hms).
intros model' Hsame Hcl. apply SRr_ret. split; [reflexivity|].
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_frame_writeR R); [exact HJ | | | |].
+ rewrite Hmm. intros x Hx. apply Hfr. intros Hw. exact (Hx (Hwr _ Hw)).
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
(* the same runs when every byte the segment writes is an FP byte of a frame of S (an output through the caller's
   pointer), which awr_ok cannot state *)
Lemma SRr_chain_tok_AJx_frame : forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> wr_fp_frame FP S lyc a) ->
run_post_tok_AJx W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_tok_AJx_frameR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_to_tok_AJx_frame over a world relation R. *)
Lemma SRr_run_to_tok_AJx_frameR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> wr_fp_frame FP S lyc a) ->
run_post_tok_AJxR R W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_to_tok_sound segs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply (SRr_chain_tok_AJx_frameR R Rr Rt); [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_to_tok_AJx_frame : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> wr_fp_frame FP S lyc a) ->
run_post_tok_AJx W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_tok_AJx_frameR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* the write permission of a segment that writes its own window and a caller-frame output the footprint names *)
Definition awr_ok_fr (E : env) (rs : smem) (STK sp0 : Z) (FP : list (Z * Z)) (bl0 blc : list (Z * Z))
(S : astate) (ly : alayout) (own : list (Z * Z)) : Prop :=
forall a, in_wrange E rs a -> awr_byte STK sp0 FP bl0 blc ly own a \/ wr_fp_frame FP S ly a.
(* SRr_chain_AJx_fr over a world relation R; the journal step is ajournal_x_exec_frR. *)
Lemma SRr_chain_AJx_frR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
st_ok segs E ss' msr' ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_AJxR R W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R _ _ W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms HS' Hfr HJ Hwr Hk.
apply SRr_SRrG_same. apply (SRr_msteps segs Hwx W ms msr' mdc _ Hms).
intros model' Hsame Hcl. apply SRr_ret. split; [reflexivity|].
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply (ajournal_x_exec_frR R) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_chain_AJx_fr : forall W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
st_ok segs E ss' msr' ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_AJx_frR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_AJx_fr over a world relation R. *)
Lemma SRr_run_AJx_frR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_AJxR R W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply (SRr_chain_AJx_frR R Rr Rt); [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_AJx_fr : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_AJx_frR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_to_AJx_fr over a world relation R. *)
Lemma SRr_run_to_AJx_frR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_AJxR R W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply (SRr_chain_AJx_frR R Rr Rt); [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_to_AJx_fr : forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_AJx_frR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_chain_tok_AJx_fr over a world relation R; the journal step is ajournal_x_exec_frR. *)
Lemma SRr_chain_tok_AJx_frR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_tok_AJxR R W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R _ _ W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HS' Hsh' Hfr HJ Hwr Hk.
apply SRr_SRrG_same. apply (SRr_msteps segs Hwx W ms msr' mdc _ Hms).
intros model' Hsame Hcl. apply SRr_ret. split; [reflexivity|].
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec_frR R) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_chain_tok_AJx_fr : forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_tok_AJx W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_tok_AJx_frR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_tok_AJx_fr over a world relation R. *)
Lemma SRr_run_tok_AJx_frR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok segs tbl K Bx Bspan SH n ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_tok_AJxR R W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_tok_sound segs tbl K Bx Bspan SH tbl_ok n E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply (SRr_chain_tok_AJx_frR R Rr Rt); [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_tok_AJx_fr : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok segs tbl K Bx Bspan SH n ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_tok_AJx W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_tok_AJx_frR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_to_tok_AJx_fr over a world relation R. *)
Lemma SRr_run_to_tok_AJx_frR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_tok_AJxR R W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_to_tok_sound segs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply (SRr_chain_tok_AJx_frR R Rr Rt); [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_to_tok_AJx_fr : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_tok_AJx W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_tok_AJx_frR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End e.
End l.
End x.
Arguments AR_laws_x {rc} segs B ARx hl.
(* the journal's projections, constructor and budget step read every argument off the journal (or its conjuncts) *)
Arguments ajx_intro {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS}
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Arguments ajx_ar {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_ly {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_secs {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_wle {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_io {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_frs {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_nev {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_k {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_hi {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_blk {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_img {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_frm {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_gone {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_pres {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_stk {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_extra {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_qt {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_wild {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajournal_xw_fix1 {rc SK segs B PST ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS tr} _ _.
Arguments ajournal_xw_fix1R {rc SK segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS tr} _ _.
Arguments ajx_budget {rc SK segs B PST ARx STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} WS' _ _.
(* the same over R: R too is read off the journal *)
Arguments ajxR_intro {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS}
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Arguments ajxR_ar {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_ly {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_secs {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_rel {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_io {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_frs {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_nev {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_k {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_hi {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_blk {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_img {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_frm {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_gone {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_pres {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_stk {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_extra {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_qt {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajxR_wild {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} _.
Arguments ajx_budgetR {rc SK segs B PST ARx R STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k WS} WS' _ _.
(* The laws are cgif's: at ARx := cgif's AR they follow from AR_laws and AR_extra_law_ok (non-vacuity witness). *)
Lemma AR_laws_x_of_AR : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (segs : list Segment) (B : asyms),
AR_laws segs B ->
(forall ly S W mem md, AR segs B ly S W mem md -> ly_stk_lo ly mod 8 = 0 /\ ly_stk_hi ly mod 8 = 0) ->
(* cgif's laws state neither the tail granule nor the const cells; the witness takes both, in the fields' own words *)
(forall ly S W mem md p n a, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
   p + req_size n <= a < (p + req_size n + 7) / 8 * 8 -> aview segs (w_H W) mem a <> None) ->
(forall ly S W mem md, AR segs B ly S W mem md ->
   Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly)) ->
AR_laws_x segs B (fun ly S (_ : list Z) W mem md => AR segs B ly S W mem md) 0.
Proof.
intros fx rc segs B L Lal Ltail Lconst. constructor.
- intros ly S Hp W mem md p n HAR Hin. destruct (al_blocks _ _ L ly S W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6 & _).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
- intros ly S Hp. exact (al_frame _ _ L ly S).
- intros ly S Hp. exact (al_frames _ _ L ly S).
- intros ly S Hp. exact (al_stack _ _ L ly S).
- intros ly S Hp. exact (al_owned_image _ _ L ly S).
- intros ly S Hp. exact (al_sep _ _ L ly S).
- intros ly S Hp. exact (al_layout _ _ L ly S).
- intros ly S Hp. exact (al_client_img _ _ L ly S).
- intros ly S Hp. exact (AR_extra_law_ok segs B ly S).
- intros ly S Hp. exact (al_const _ _ L ly S).
- intros ly S Hp W mem md p n HAR Hin _. exact (al_shadow _ _ L ly S W mem md p n HAR Hin).
- intros ly S Hp. exact (al_zshadow _ _ L ly S).
- (* the per-byte form from the range form: with both stack bounds 8-aligned the index a / 8 - lo / 8 is in range *)
  intros ly S Hp W mem md a HAR Ha.
  destruct (Lal ly S W mem md HAR) as [Elo Ehi].
  pose proof (al_zshadow _ _ L ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
    ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
  cbn [fst snd] in HZ. unfold zero_shadow in HZ.
  assert (Hdlo : ly_stk_lo ly = 8 * (ly_stk_lo ly / 8)) by (apply Z.div_exact; [lia | exact Elo]).
  assert (Hdhi : ly_stk_hi ly = 8 * (ly_stk_hi ly / 8)) by (apply Z.div_exact; [lia | exact Ehi]).
  assert (Hi1 : ly_stk_lo ly / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (Hi2 : a / 8 < ly_stk_hi ly / 8)
    by (apply Z.div_lt_upper_bound; [lia | rewrite <- Hdhi at 1; lia]).
  specialize (HZ (a / 8 - ly_stk_lo ly / 8)).
  unfold shadow_of_addr in HZ.
  replace (SHADOW_OFF + ly_stk_lo ly / 8 + (a / 8 - ly_stk_lo ly / 8)) with (SHADOW_OFF + a / 8) in HZ by lia.
  apply HZ. split; [lia|].
  replace (ly_stk_hi ly - ly_stk_lo ly) with (8 * (ly_stk_hi ly / 8 - ly_stk_lo ly / 8)) by lia.
  rewrite (Z.mul_comm 8), Z.div_mul by lia. lia.
- (* field 14 at hl = 0: cgif's block shadow law, the head being empty *)
  intros ly S Hp W mem md b n HAR Hin _. rewrite Z.add_0_r, Z.sub_0_r.
  destruct (al_shadow _ _ L ly S W mem md b n HAR Hin) as [H1 H2]. split; [exact H1 | intros _; exact H2].
- intros ly S Hp W mem md p n a HAR Hin Ha. exact (Ltail ly S W mem md p n a HAR Hin Ha).
- intros ly S Hp W mem md HAR. exact (Lconst ly S W mem md HAR).
- (* field 17: ly_img covers every segment (ALedger's al_img, as FCiface.v:185), and a live fake frame lies at or
     above the image's top: the fake stack is disjoint from ly_img (YG0s.frame_facts), starts at or above 4096
     and is longer than kImgLo (= fst (ly_img ly), layout_ok's lo_img), so it cannot start below the image's end *)
  intros ly S Hp W mem md HAR. pose proof HAR as (M & LG & _). split.
  + intros sg Hsg. exact (al_img _ _ _ _ LG sg Hsg).
  + intros cid pos Hin. pose proof (lo_img _ (am_layout _ _ _ _ M)) as (I1 & I2 & _).
    destruct (YG0s.frame_facts B ly S _ cid pos M Hin) as (C1 & _ & [F1 _] & D & _ & P1 & _).
    assert (HF : fst (ly_img ly) + snd (ly_img ly) <= ly_F ly).
    { destruct (Z_lt_le_dec (ly_F ly) (fst (ly_img ly) + snd (ly_img ly))) as [Hlt|Hge]; [|exact Hge].
      exfalso. apply D. exists (Z.max (ly_F ly) (fst (ly_img ly))). unfold in_zr. cbn [fst snd].
      unfold kImgLo, kFakeStackSize in *. split; [lia | left; lia]. }
    pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CN.
    unfold frame_addr, kFakeFramesOff in *. lia.
- (* field 18: the layout is layout_ok, ARm's am_layout (as FCiface.v:184) *)
  intros ly S Hp W mem md HAR. exact (am_layout _ _ _ _ (proj1 HAR)).
- (* field 19: YG0s.frame_facts' first conjunct *)
  intros ly S Hp W mem md cid pos (M & _) Hin. exact (proj1 (YG0s.frame_facts B ly S _ cid pos M Hin)).
- (* field 20: ahs_pres off the client bytes (YG0q.client_band_vis), and YG0q.aview_band *)
  intros ly S Hp W mem md a (M & LG & _ & _ & [HP _]) Ha Hh Hv AV.
  assert (IMG : forall sg, In sg segs ->
    4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd).
  { intros sg Hsg. eapply YG0q.al_img_env; [exact (am_layout _ _ _ _ M) | exact LG | exact Hsg]. }
  assert (NC : ~ aclient_byte B ly S a).
  { intros C. assert (X : aview segs (w_H W) mem a <> None)
      by (eapply YG0q.client_band_vis; [exact M | exact Ha | exact C]). exact (X AV). }
  apply (proj2 (YG0q.aview_band segs (w_H W) mem a IMG Ha Hh)); [| exact AV].
  exact (HP a Ha NC (or_intror Hv)).
- (* field 21: a live block is an allocated chunk's user range, ck_base + ck_rz with 16 <= ck_rz, and its extent
     lies on one arm (YG0s.chunk_facts) *)
  intros ly S Hp W mem md p n (M & _) Hin Hhi.
  unfold ablocks, blocks in Hin. rewrite map_map in Hin.
  apply in_map_iff in Hin as (k & Ek & Hk). apply filter_In in Hk as [Hk _].
  cbn [fst snd] in Ek. injection Ek as Ep _.
  pose proof (YG0s.chunk_facts B ly S _ k M Hk) as (G1 & _ & _ & G4 & G5 & _ & G7 & G8 & _).
  assert (R1 : 1 <= req_size (ck_req k)) by (unfold req_size; destruct (Z.eqb_spec (ck_req k) 0); lia).
  rewrite G4 in Ep. subst p. destruct G1 as [_ [Lo | [Hi _]]]; unfold kLowShadowBeg, kHighMemBeg in *; lia.
- (* field 22 at hl = 0: the head is empty *)
  intros ly S Hp W mem md b n a _ _ _ Ha. lia.
- (* field 23: cgif's al_flag *)
  intros ly S Hp. exact (al_flag _ _ L ly S).
- (* field 24 (F21b): the chunk's extent, by its kind (YG0s.chunk_facts): a primary chunk's region ends far below
     the ceiling (YG0s.region_in_prim); a secondary chunk's map keeps the right redzone above the block (am_placed) *)
  intros ly S Hp W mem md p n (M & _) Hin.
  unfold ablocks, blocks in Hin. rewrite map_map in Hin.
  apply in_map_iff in Hin as (k & Ek & Hk). apply filter_In in Hk as [Hk _].
  cbn [fst snd] in Ek. injection Ek as Ep En. subst n.
  pose proof (am_layout _ _ _ _ M) as LO. pose proof (am_placed _ _ _ _ M) as [PL _].
  pose proof (YG0s.chunk_facts B ly S _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & G7 & G8 & GG).
  rewrite G4 in Ep. subst p.
  destruct (ck_beg k) as [|off|r o|c q] eqn:Eb; try solve [destruct GG].
  + cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
    pose proof (YG0s.region_in_prim ly (prim_class off) LO ltac:(lia)) as (_ & _ & _ & _ & R5).
    unfold ASAN_CEIL in *. lia.
  + destruct GG as (-> & Hfp & Gbase & Gext & Gin & _).
    pose proof (proj1 (Forall_forall _ _) PL _ Gin) as (_ & _ & I3). cbn [fst snd] in I3.
    unfold sec_map_size, needed_size in Gext, I3. rewrite Hfp in Gext, I3. cbv beta iota in Gext, I3.
    unfold needed_primary in Gext, I3.
    pose proof (round_up_ge_x (rounded_size (ck_req k) + rz_size (ck_req k) + rz_size (ck_req k)) kPage
      ltac:(unfold kPage; lia)) as RU.
    assert (RS : req_size (ck_req k) <= rounded_size (ck_req k)).
    { unfold rounded_size. pose proof (round_up_ge_x (Z.max (ck_req k) 8) 8 ltac:(lia)).
      unfold req_size. destruct (Z.eqb_spec (ck_req k) 0); lia. }
    unfold ck_rz in *. unfold kPage in *. lia.
- (* field 25: the depot holds no repeat, ARm's am_wf (YG01.v Wf's wf_depot, depot_fits' first conjunct) *)
  intros ly S Hp W mem md HAR. exact (proj1 (wf_depot _ _ _ _ _ (am_wf _ _ _ _ (proj1 HAR)))).
Qed.
