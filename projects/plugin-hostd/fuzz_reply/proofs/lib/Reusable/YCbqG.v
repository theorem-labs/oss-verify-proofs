(* reply-own since route R (a Theorem Labs lane 16:55Z); lineage: carried from preset a0fed4266a1b18b1453af093bfe2ee477dcbe241,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCbqG.v, sha256 c72125eb2b187a4f934f230c8e3be2e2feed984fa60935492b62d2fd32b69355,
   with the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.
   QMm W0' (a Theorem Labs lane, a Theorem Labs lane 2026-10-30 20:48Z, option Q): kept_x (the image's as_kept ranges outside the owned statics;
   reply: the non-owned RELRO, written only at start-up); ARx_frame_law keeps them. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the per-function frame of proofs/cgif/cgif_file_fuzzer/lib/YCbq.v (:210-216, :335-342, :349-371, :384-393, :419-458, :480-671, :724-791, :1809-1825) and lib/YC20.v:90-96, with three changes: the allocator invariant is a parameter ARx, and the YG0d.v:435-507 / YG0p.v:20-27 laws the lemmas use are the record AR_laws_x over it (AR_laws_x_of_AR below instantiates it at cgif's AR); Hp (the ghost poisoned-head set of YGcfNames.v:178-183) threaded as YGcfNames.v:319-329 orders it, with cgif's relative event count k kept as YGcfNames.v:574-578 decides; the image clause exempts the program's own written statics PST (a Theorem Labs lane's FM_PSTAT form). No address literal. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p YCbq YK0o.
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
(* QMm W0' (option Q): the KEPT bytes, image bytes in the image's as_kept ranges outside the owned statics (reply: the
   non-owned RELRO, written only at start-up). They are the bytes arodata_ok_cf (YG0dcf.v:82-84) reads, so a frame step
   that keeps them keeps it. Not over PST: the record AR_laws_x takes no PST (PST enters by the hypothesis PST_nk). *)
Definition kept_x (a : Z) : Prop :=
in_img segs a /\ Exists (in_zr a) (as_kept B) /\ ~ Exists (in_zr a) (as_owned_static B).
(* a byte off the image is not kept: every write of a stack, frame, block or shadow byte *)
Lemma kept_x_off_img : forall a, ~ in_img segs a -> ~ kept_x a.
Proof. intros a Hn (Hi & _). exact (Hn Hi). Qed.
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
(forall a, 0 <= a < 2 ^ 64 -> kept_x a -> mem' (w64 a) = mem (w64 a)) ->
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
(* cgif's YG0d.v:442-446 AR_shadow_law over ARx, with the blocks whose hidden head is in Hp excluded: for a block
   whose bytes hold no hidden head, its shadow is a block shadow and its hull is visible. A harness block of the
   second instance has its first bytes hidden by construction (its base is in Hp), so this law says nothing about it;
   the user-range form for such a block needs that instance's head length and belongs to the cf layer, not here. *)
Definition ARx_shadow_law : Prop :=
forall ly S Hp W mem md p n,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
(forall h, In h Hp -> ~ (p <= h < p + req_size n)) ->
block_shadow (aview segs (w_H W) mem) SHADOW_OFF p (req_size n) /\
shadow_hull_vis (aview segs (w_H W) mem) p (req_size n).
(* cgif's YG0d.v:447-450 AR_zshadow_law over ARx (= YG0dcf.v:278 of the second instance): the ranges the runtime keeps
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
   HERE. These cells have CONSTANT NON-ZERO shadow - K0's K0C-RO measurement puts the last granule of a read-only
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
   (cgif's AR: ARm's am_layout, as FCiface.v:188; ARcf: ARmcf's amc_layout, as FCifaceCf.v:135). Not derivable
   from fields 1-17: none bounds ly_stk_lo / ly_stk_hi absolutely. Named ARx_layout_ok_law, not ARx_layout_law
   (field 7, the layout_le monotonicity law). Section l derives the stack bounds stk_bounds_x and the stack
   alignment stk_aligned_x from it. *)
Definition ARx_layout_ok_law : Prop :=
forall ly S Hp W mem md, ARx ly S Hp W mem md -> layout_ok ly.
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
alx_layout_ok : ARx_layout_ok_law
}.
Definition afn_pre_x (STK : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
ARx ly S Hp W mem md /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
astk_ok STK ly (spZ regs) /\
(forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) /\
achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch /\
qtight S.
Definition ajournal_xR (R : world segs -> world segs -> Prop) (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
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
qtight S'.
(* ROUTE R (a Theorem Labs lane, 2026-10-30): the journal is generic in its WORLD RELATION R, the fourth conjunct R W W'.
   ajournal_x below is the journal at wle: its body is ajournal_xR's at R := wle (ajournal_x_wle checks it by conversion;
   the body is kept so that a proof that unfolds ajournal_x sees the text it always saw), so every statement over
   ajournal_x keeps its text. Each rule below that reaches the journal has an R twin NAMER (R implicit, inferred from the
   journal), proved once over R from R's reflexivity (the start, ajournal_x_initR) and transitivity (the sub-journal,
   ajournal_x_subR) only, and the rule NAME is its twin at wle. A call that re-hides shadow takes R := wle' segs RZ_cf. *)
Definition ajournal_x (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ARx ly' S' Hp' W' mem' md' /\
layout_le (length (st_secs S)) ly ly' /\ (length (st_secs S) <= length (st_secs S'))%nat /\ wle W W' /\ aos_step FP md md' /\
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
qtight S'.
(* ajournal_x keeps its body, for the proofs that unfold it; ajournal_x_wle checks that it is ajournal_xR at wle *)
Lemma ajournal_x_wle : ajournal_x = ajournal_xR (@wle segs). Proof. reflexivity. Qed.
(* the weakening over R: a journal at R1 is one at every R2 that contains R1 (only the world conjunct reads R) *)
Lemma ajournal_xR_mono : forall (R1 R2 : world segs -> world segs -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
  ajournal_xR R1 STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR R2 STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros R1 R2 H12 STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (H1 & H2 & H3 & H4 & H5).
exact (conj H1 (conj H2 (conj H3 (conj (H12 W W' H4) H5)))).
Qed.
Definition apost_base_xR (R : world segs -> world segs -> Prop) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) W mem md
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k,
c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
(ajournal_xR R) STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Definition apost_base_x (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) W mem md
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k,
c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
ajournal_x STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
(* apost_base_x keeps its body, for the proofs that unfold it; apost_base_x_wle checks that it is apost_base_xR at wle *)
Lemma apost_base_x_wle : apost_base_x = apost_base_xR (@wle segs). Proof. reflexivity. Qed.
(* apost_base_x with the float state after the call existential (cgif_rgb_fuzzer lib/YCaq.v:27-32, apost_baseF), for a
   function whose callees change the f registers or fcsr (musl strtod): the rounding mode is back at 0 (frm_zero) and
   the callee-saved f registers are kept. Same parameters in the same positions as apost_base_x. *)
Definition apost_base_xFR (R : world segs -> world segs -> Prop) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) W mem md
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
(ajournal_xR R) STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Definition apost_base_xF (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (Hp : list Z) W mem md
(Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) md' /\
frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
ajournal_x STK (spZ regs) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
(* apost_base_xF keeps its body, for the proofs that unfold it; apost_base_xF_wle checks that it is apost_base_xFR at wle *)
Lemma apost_base_xF_wle : apost_base_xF = apost_base_xFR (@wle segs). Proof. reflexivity. Qed.
(* a function that leaves the float state alone meets the float form when the entry rounding mode is 0 *)
Lemma apost_base_x_FR {R : world segs -> world segs -> Prop} : forall STK FP regs ly S Hp W mem md Q W' c',
frm_zero (@YK11.fp_csr fx) ->
(apost_base_xR R) STK FP regs ly S Hp W mem md Q W' c' -> (apost_base_xFR R) STK FP regs ly S Hp W mem md Q W' c'.
Proof.
intros STK FP regs ly S Hp W mem md Q W' c' Hz (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & Hpr & HQ).
exists fx, ly', S', Hp', regs', mem', md', k. split; [exact Hc|]. split; [exact Hz|].
split; [intros r _; reflexivity|]. split; [exact HJ|]. split; [exact Hpr | exact HQ].
Qed.
Lemma apost_base_x_F : forall STK FP regs ly S Hp W mem md Q W' c',
frm_zero (@YK11.fp_csr fx) ->
apost_base_x STK FP regs ly S Hp W mem md Q W' c' -> apost_base_xF STK FP regs ly S Hp W mem md Q W' c'.
Proof. exact (@apost_base_x_FR (@wle segs)). Qed.
Lemma apost_base_xF_monoR {R : world segs -> world segs -> Prop} : forall STK FP regs ly S Hp W mem md (Q Q' : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
(forall ly' S' Hp' W'' regs' mem' md', Q ly' S' Hp' W'' regs' mem' md' -> Q' ly' S' Hp' W'' regs' mem' md') ->
(apost_base_xFR R) STK FP regs ly S Hp W mem md Q W' c' -> (apost_base_xFR R) STK FP regs ly S Hp W mem md Q' W' c'.
Proof.
intros STK FP regs ly S Hp W mem md Q Q' W' c' HQQ (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hz & Hk & HJ & Hpr & HQ).
exists fx', ly', S', Hp', regs', mem', md', k. repeat (split; [eassumption|]). exact (HQQ _ _ _ _ _ _ _ HQ).
Qed.
Lemma apost_base_xF_mono : forall STK FP regs ly S Hp W mem md (Q Q' : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
(forall ly' S' Hp' W'' regs' mem' md', Q ly' S' Hp' W'' regs' mem' md' -> Q' ly' S' Hp' W'' regs' mem' md') ->
apost_base_xF STK FP regs ly S Hp W mem md Q W' c' -> apost_base_xF STK FP regs ly S Hp W mem md Q' W' c'.
Proof. exact (@apost_base_xF_monoR (@wle segs)). Qed.
Section l.
Hypothesis LAWS : AR_laws_x.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
(* QMm W0: the program's own written statics are not kept bytes (taken only by the PST-write lemmas) *)
Hypothesis PST_nk : forall a, Exists (in_zr a) PST -> ~ kept_x a.
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
Lemma ajournal_x_initR {R : world segs -> world segs -> Prop} (R_refl : forall W, R W W) : forall STK FP ly S Hp W regs mem md ch,
afn_pre_x STK ly S Hp W regs mem md ch -> (ajournal_xR R) STK (spZ regs) FP ly S Hp W mem md [] ly S Hp W mem md 0.
Proof.
intros STK FP ly S Hp W regs mem md ch (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
split; [exact HAR|]. split; [apply layout_le_refl|]. split; [zlia|]. split; [apply R_refl|]. split; [apply aos_step_refl|].
split; [reflexivity|]. split; [zlia|]. split; [zlia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros p n i H1 H2; exfalso; exact (H2 H1)|].
split; [exact Hpres|]. split; [exact Hstk|]. split; [intros; reflexivity | exact HQT].
Qed.
Lemma ajournal_x_init : forall STK FP ly S Hp W regs mem md ch,
afn_pre_x STK ly S Hp W regs mem md ch -> ajournal_x STK (spZ regs) FP ly S Hp W mem md [] ly S Hp W mem md 0.
Proof. exact (@ajournal_x_initR (@wle segs) (wle_refl segs)). Qed.
Lemma ajournal_x_mono_kR {R : world segs -> world segs -> Prop} : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k k',
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> k <= k' ->
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k'.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k k'
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & REST) Hkk.
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [exact Hfrs|]. split; [zlia|]. split; [zlia|]. exact REST.
Qed.
Lemma ajournal_x_mono_k : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k k',
ajournal_x STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> k <= k' ->
ajournal_x STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k'.
Proof. exact (@ajournal_x_mono_kR (@wle segs)). Qed.
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
Lemma awr_byte_cases_xR {R : world segs -> world segs -> Prop} : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k a,
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
~ aowned B lyc Sc a /\
((YM05.alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))))).
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k a HJ Hw.
destruct HJ as (HAR & Hly & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & _) & _ & HQT).
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
Proof. exact (@awr_byte_cases_xR (@wle segs)). Qed.
(* QMm W0': a byte a function may write (stack window, a live block, its own frames and their shadow) is not kept: it
   is off the image *)
Lemma awr_byte_not_kept_xR {R : world segs -> world segs -> Prop} : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k a,
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a -> ~ kept_x a.
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k a HJ Hw.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (awr_byte_cases_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as
  (_ & [[Hc Hs] | [(Happ & b & n & Hin & Hr & _) | (cid & pos & Hown & [[Happ Hr] | [Hsh Hr]])]]);
  apply kept_x_off_img.
- intros Hi. pose proof (segs_low a Hi). zlia.
- exact (blk_img_x lyc Sc Hpc Wc memc mdc b n a HAR Hin Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hown).
  unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img_x lyc Sc Hpc Wc memc mdc cid pos a HAR Hin' Hr).
- intros Hi. pose proof (segs_low a Hi). zlia.
Qed.
Lemma ajournal_x_after_writeR {R : world segs -> world segs -> Prop} : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' Hp' own2,
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) ->
ARx lyc S' Hp' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' ->
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own2 lyc S' Hp' Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr S' Hp' own2 HJ Heqw Hgr Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT'.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
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
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx]; [left; exact (awr_byte_cases_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hwle|].
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
split; [exact Hstatic|]. split; [|exact HQT'].
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
qtight S' ->
ajournal_x STK sp0 FP ly S Hp W mem md own2 lyc S' Hp' Wc memc' mdc' k.
Proof. exact (@ajournal_x_after_writeR (@wle segs)). Qed.
Lemma ajournal_x_execR {R : world segs -> world segs -> Prop} : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr HJ Hfr Hgr Hhid Hsame HW.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
pose proof (same_but_materialized_wvb mdc mdc' Hsame) as Emd.
assert (HKr : forall a, 0 <= a < 2 ^ 64 -> kept_x a -> memc' (w64 a) = memc (w64 a)).
{ intros a Ha Hkx. destruct (w_H Wc (w64 a)) eqn:Eh; [exact (Hhid _ Eh)|].
pose proof (Hfr (w64 a)) as E. unfold mrestrict in E. rewrite Eh in E. apply E. intros HWa.
rewrite Z_to_bv_unsigned in HWa. unfold bv_wrap, bv_modulus in HWa.
change (2 ^ Z.of_N 64) with (2 ^ 64) in HWa. rewrite Z.mod_small in HWa by zlia.
exact (awr_byte_not_kept_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (HW _ HWa) Hkx). }
eapply (ajournal_x_after_writeR STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr Sc Hpc own HJ Heqw
ltac:(intros a Ha; eapply apresent_grows; [exact Hgr | exact Ha]) Hsame);
[intros a Ha; left; exact (HW a Ha) | | reflexivity | reflexivity | zlia | exact Hfrs | exact HQT].
eapply (alx_frame LAWS); [exact HAR | | | | | | |].
- intros a Ha Ho. apply Heqw; [exact Ha|]. intros HWa. exact (proj1 (awr_byte_cases_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (HW _ HWa)) Ho).
- intros a Hv. eapply aview_keeps_vis; [exact Hgr | exact Hv].
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- intros a _ Hh. exact (Hhid _ Hh).
- exact HKr.
Qed.
Lemma ajournal_x_exec : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof. exact (@ajournal_x_execR (@wle segs)). Qed.
Lemma ajournal_x_materializeR {R : world segs -> world segs -> Prop} : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k X,
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc (with_vm_backing (m_vm_lazy mdc) X mdc) k.
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k X HJ.
eapply (ajournal_x_execR STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc _ (fun _ => False) HJ);
[intros x _; reflexivity | apply mem_grows_refl | intros x _; reflexivity | apply same_but_materialized_wvb_any | intros a Ha; destruct Ha].
Qed.
Lemma ajournal_x_materialize : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k X,
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc (with_vm_backing (m_vm_lazy mdc) X mdc) k.
Proof. exact (@ajournal_x_materializeR (@wle segs)). Qed.
(* A write of the program's own statics only (PST): the bytes are image bytes the runtime does not own, so the
   invariant and every clause of the journal but the PST-exempt image clause hold unchanged. *)
Lemma ajournal_x_pst_writeR {R : world segs -> world segs -> Prop} : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc',
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Exists (in_zr (bv_unsigned x)) PST -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' HJ Hfr Hgr Hhid Hsame.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ Exists (in_zr a) PST -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
assert (HPl : forall a, Exists (in_zr a) PST -> 0 <= a < kLowMemEnd).
{ intros a Ha. exact (segs_low a (proj1 (PST_ok a Ha))). }
pose proof (same_but_materialized_wvb mdc mdc' Hsame) as Emd.
assert (HKr : forall a, 0 <= a < 2 ^ 64 -> kept_x a -> memc' (w64 a) = memc (w64 a)).
{ intros a Ha Hkx. destruct (w_H Wc (w64 a)) eqn:Eh; [exact (Hhid _ Eh)|].
pose proof (Hfr (w64 a)) as E. unfold mrestrict in E. rewrite Eh in E. apply E. intros Hq.
rewrite Z_to_bv_unsigned in Hq. unfold bv_wrap, bv_modulus in Hq.
change (2 ^ Z.of_N 64) with (2 ^ 64) in Hq. rewrite Z.mod_small in Hq by zlia.
exact (PST_nk a Hq Hkx). }
assert (HAR' : ARx lyc Sc Hpc Wc memc' mdc').
{ eapply (alx_frame LAWS); [exact HAR | | | | | | |].
- intros a Ha Ho. apply Heqw; [exact Ha|]. intros Hq. destruct (PST_ok a Hq) as [Hi Hno].
exact (Hno (proj1 (alx_owned_image LAWS lyc Sc Hpc Wc memc mdc a HAR Hi) Ho)).
- intros a Hv. eapply aview_keeps_vis; [exact Hgr | exact Hv].
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- intros a _ Hh. exact (Hhid _ Hh).
- exact HKr. }
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
split; [exact Hstatic|]. split; [|exact HQT].
{ intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (alx_extra LAWS lyc Sc Hpc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros Hq. exact (Xi (proj1 (PST_ok a Hq))). }
Qed.
Lemma ajournal_x_pst_write : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc',
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Exists (in_zr (bv_unsigned x)) PST -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof. exact (@ajournal_x_pst_writeR (@wle segs)). Qed.
(* A write confined to bytes of the CALLER'S OWN FRAMES that the footprint names: the journal's frames clause exempts
   exactly the FP bytes of a frame of S, so every other clause holds unchanged. This is what a function that writes an
   output through a caller's pointer into the caller's frame needs; awr_byte does not reach those bytes (its frame case
   is the function's own frames). *)
Definition wr_fp_frame (FP : list (Z * Z)) (S : astate) (lyc : alayout) (a : Z) : Prop :=
inFP FP a /\ exists cid pos, In (cid, pos) (frames S) /\ in_zr a (frame_rng lyc (cid, pos)).
Lemma ajournal_x_frame_writeR {R : world segs -> world segs -> Prop} : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc',
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ wr_fp_frame FP S lyc (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' HJ Hfr Hgr Hhid Hsame.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
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
assert (HKr : forall a, 0 <= a < 2 ^ 64 -> kept_x a -> memc' (w64 a) = memc (w64 a)).
{ intros a Ha Hkx. destruct (w_H Wc (w64 a)) eqn:Eh; [exact (Hhid _ Eh)|].
pose proof (Hfr (w64 a)) as E. unfold mrestrict in E. rewrite Eh in E. apply E. intros Hq.
rewrite Z_to_bv_unsigned in Hq. unfold bv_wrap, bv_modulus in Hq.
change (2 ^ Z.of_N 64) with (2 ^ 64) in Hq. rewrite Z.mod_small in Hq by zlia.
pose proof (HWf a Hq) as (_ & Hni & _).
exact (kept_x_off_img a Hni Hkx). }
assert (HAR' : ARx lyc Sc Hpc Wc memc' mdc').
{ eapply (alx_frame LAWS); [exact HAR | | | | | | |].
- intros a Ha Ho. apply Heqw; [exact Ha|]. intros Hq. exact (proj1 (HWf a Hq) Ho).
- intros a Hv. eapply aview_keeps_vis; [exact Hgr | exact Hv].
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
- intros a _ Hh. exact (Hhid _ Hh).
- exact HKr. }
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
split; [exact Hstatic|]. split; [|exact HQT].
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
Proof. exact (@ajournal_x_frame_writeR (@wle segs)). Qed.
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
Lemma ajournal_x_exec_frR {R : world segs -> world segs -> Prop} : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr HJ Hfr Hgr Hhid Hsame HW.
pose (memc1 := fun x : word => if wr_fp_frame_b FP S lyc (bv_unsigned x) then memc' x else memc x).
assert (E1 : forall x, wr_fp_frame_b FP S lyc (bv_unsigned x) = false -> memc1 x = memc x)
  by (intros x Hx; unfold memc1; rewrite Hx; reflexivity).
assert (E2 : forall x, wr_fp_frame_b FP S lyc (bv_unsigned x) = true -> memc1 x = memc' x)
  by (intros x Hx; unfold memc1; rewrite Hx; reflexivity).
assert (Hmr : forall (m m' : word -> option byte) x, m x = m' x -> mrestrict (w_H Wc) m x = mrestrict (w_H Wc) m' x)
  by (intros m m' x Hx; unfold mrestrict; destruct (w_H Wc x); [reflexivity | exact Hx]).
assert (HJ1 : (ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc1 mdc k).
{ eapply (ajournal_x_frame_writeR STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc1 mdc HJ).
  - intros x Hx. apply Hmr. apply E1.
    destruct (wr_fp_frame_b FP S lyc (bv_unsigned x)) eqn:Eb; [exfalso; exact (Hx (wr_fp_frame_b_true _ _ _ _ Eb)) | reflexivity].
  - intros x Hx. destruct (wr_fp_frame_b FP S lyc (bv_unsigned x)) eqn:Eb.
    + rewrite (Hmr memc1 memc' x (E2 x Eb)). apply Hgr. exact Hx.
    + rewrite (Hmr memc1 memc x (E1 x Eb)). exact Hx.
  - intros x Hx. destruct (wr_fp_frame_b FP S lyc (bv_unsigned x)) eqn:Eb;
      [rewrite (E2 x Eb); exact (Hhid x Hx) | exact (E1 x Eb)].
  - apply same_but_materialized_refl. }
eapply (ajournal_x_execR STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc1 mdc k memc' mdc'
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
Proof. exact (@ajournal_x_exec_frR (@wle segs)). Qed.
(* THE callee-footprint side condition of a call, one name for every caller (WalkS4's fp_sub_xW, PRW_CallerJ.v at
   origin/cold/h-hpreset-7-walk-S4 85a188622c5): a byte the callee's footprint names is the caller's footprint, a
   temporary block, a slot of a frame the caller took since its entry, or a byte of the caller's own stack window.
   The fourth case needs no `alloc_ceiling <= a`: the caller's journal carries astk_ok, so its window lies at or above
   alloc_ceiling and the block, frame and sink clauses refute the case themselves. *)
Definition fp_sub_x (STK sp0 : Z) (FP FP1 : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) : Prop :=
  forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
    (exists f, In f own /\ in_zr a (frame_rng lyc f)) \/ (sp0 - STK <= a < sp0).
Lemma ajournal_x_subR {R : world segs -> world segs -> Prop} (R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1,
(ajournal_xR R) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(ajournal_xR R) STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
fp_sub_x STK sp0 FP FP1 ly S own lyc Sc ->
(ajournal_xR R) STK sp0 FP ly S Hp W mem md (nf ++ own) ly2 S2 Hp2 W2 mem2 md2 (k + k1).
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT)
(HAR2 & Hly2 & Hsecs2 & Hwle2 & Hio2 & Hfrs2 & Hnev2 & Hk2 & G1 & G2 & G3 & G4 & Hgone2 & Hpres2 & Hstatic2 & G5 & HQT2) Hlo Hhi HF.
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
split; [exact Hstatic|]. split; [|exact HQT2].
{   intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
apply G5; [rewrite Eextra; exact HXa | exact He]. }
Qed.
Lemma ajournal_x_sub : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1,
ajournal_x STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
ajournal_x STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
fp_sub_x STK sp0 FP FP1 ly S own lyc Sc ->
ajournal_x STK sp0 FP ly S Hp W mem md (nf ++ own) ly2 S2 Hp2 W2 mem2 md2 (k + k1).
Proof. exact (@ajournal_x_subR (@wle segs) (wle_trans segs)). Qed.
Lemma afn_pre_x_atR {R : world segs -> world segs -> Prop} : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc STK1 (o : Z) ch1,
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
YK0s.ret_ok (getr regsc 1) -> 4096 <= raZ regsc ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
achain lyc (aview segs (w_H W) memc) (spZ regsc) (s0Z regsc) ch1 ->
afn_pre_x STK1 lyc Sc Hpc W regsc memc mdc ch1.
Proof.
intros STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regsc STK1 o ch1 HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & HQT).
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
Proof. exact (@afn_pre_x_atR (@wle segs)). Qed.
Section e.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.
Definition run_post_AJxR (R : world segs -> world segs -> Prop) (W : world segs) (E : env) (ss ss' : sstate)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ms' mat',
st_ok segs E ss' (restrict (w_H W) ms') ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
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
(* run_post_AJx keeps its body, for the proofs that unfold it; run_post_AJx_wle checks that it is run_post_AJxR at wle *)
Lemma run_post_AJx_wle : run_post_AJx = run_post_AJxR (@wle segs). Proof. reflexivity. Qed.
Lemma SRr_chain_AJxR {R : world segs -> world segs -> Prop} : forall W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
st_ok segs E ss' msr' ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
(run_post_AJxR R) W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms HS' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply ajournal_x_execR with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
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
Proof. exact (@SRr_chain_AJxR (@wle segs)). Qed.
Lemma SRr_run_AJxR {R : world segs -> world segs -> Prop} : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
(run_post_AJxR R) W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply SRr_chain_AJxR; [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_AJx : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (@SRr_run_AJxR (@wle segs)). Qed.
Lemma SRr_run_to_AJxR {R : world segs -> world segs -> Prop} : forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
(run_post_AJxR R) W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply SRr_chain_AJxR; [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_to_AJx : forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (@SRr_run_to_AJxR (@wle segs)). Qed.
Definition run_post_tok_AJxR (R : world segs -> world segs -> Prop) (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
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
(* run_post_tok_AJx keeps its body, for the proofs that unfold it; run_post_tok_AJx_wle checks that it is run_post_tok_AJxR at wle *)
Lemma run_post_tok_AJx_wle : run_post_tok_AJx = run_post_tok_AJxR (@wle segs). Proof. reflexivity. Qed.
Lemma SRr_chain_tok_AJxR {R : world segs -> world segs -> Prop} : forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
(run_post_tok_AJxR R) W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply ajournal_x_execR with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
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
Proof. exact (@SRr_chain_tok_AJxR (@wle segs)). Qed.
Lemma SRr_run_tok_AJxR {R : world segs -> world segs -> Prop} : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok segs tbl K Bx Bspan SH n ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
(run_post_tok_AJxR R) W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_tok_sound segs tbl K Bx Bspan SH tbl_ok n E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply SRr_chain_tok_AJxR; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
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
Proof. exact (@SRr_run_tok_AJxR (@wle segs)). Qed.
Lemma SRr_run_to_tok_AJxR {R : world segs -> world segs -> Prop} : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
(run_post_tok_AJxR R) W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_to_tok_sound segs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply SRr_chain_tok_AJxR; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
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
Proof. exact (@SRr_run_to_tok_AJxR (@wle segs)). Qed.
Lemma SRr_chain_AJx_pstR {R : world segs -> world segs -> Prop} : forall W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
st_ok segs E ss' msr' ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> Exists (in_zr a) PST) ->
(run_post_AJxR R) W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms HS' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply ajournal_x_pst_writeR; [exact HJ | | | |].
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
Proof. exact (@SRr_chain_AJx_pstR (@wle segs)). Qed.
Lemma SRr_run_AJx_pstR {R : world segs -> world segs -> Prop} : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> Exists (in_zr a) PST) ->
(run_post_AJxR R) W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply SRr_chain_AJx_pstR; [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_AJx_pst : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> Exists (in_zr a) PST) ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (@SRr_run_AJx_pstR (@wle segs)). Qed.
(* the same runs when every byte the segment writes is an FP byte of a frame of S (an output through the caller's
   pointer), which awr_ok cannot state *)
Lemma SRr_chain_tok_AJx_frameR {R : world segs -> world segs -> Prop} : forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> wr_fp_frame FP S lyc a) ->
(run_post_tok_AJxR R) W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply ajournal_x_frame_writeR; [exact HJ | | | |].
+ rewrite Hmm. intros x Hx. apply Hfr. intros Hw. exact (Hx (Hwr _ Hw)).
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
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
Proof. exact (@SRr_chain_tok_AJx_frameR (@wle segs)). Qed.
Lemma SRr_run_to_tok_AJx_frameR {R : world segs -> world segs -> Prop} : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> wr_fp_frame FP S lyc a) ->
(run_post_tok_AJxR R) W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_to_tok_sound segs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply SRr_chain_tok_AJx_frameR; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
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
Proof. exact (@SRr_run_to_tok_AJx_frameR (@wle segs)). Qed.
(* the write permission of a segment that writes its own window and a caller-frame output the footprint names *)
Definition awr_ok_fr (E : env) (rs : smem) (STK sp0 : Z) (FP : list (Z * Z)) (bl0 blc : list (Z * Z))
(S : astate) (ly : alayout) (own : list (Z * Z)) : Prop :=
forall a, in_wrange E rs a -> awr_byte STK sp0 FP bl0 blc ly own a \/ wr_fp_frame FP S ly a.
Lemma SRr_chain_AJx_frR {R : world segs -> world segs -> Prop} : forall W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
st_ok segs E ss' msr' ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
(run_post_AJxR R) W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms HS' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply ajournal_x_exec_frR with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
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
Proof. exact (@SRr_chain_AJx_frR (@wle segs)). Qed.
Lemma SRr_run_AJx_frR {R : world segs -> world segs -> Prop} : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
(run_post_AJxR R) W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply SRr_chain_AJx_frR; [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_AJx_fr : forall W n E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (@SRr_run_AJx_frR (@wle segs)). Qed.
Lemma SRr_run_to_AJx_frR {R : world segs -> world segs -> Prop} : forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
(run_post_AJxR R) W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply SRr_chain_AJx_frR; [exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_to_AJx_fr : forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal_x STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_AJx W E ss ss' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (@SRr_run_to_AJx_frR (@wle segs)). Qed.
Lemma SRr_chain_tok_AJx_frR {R : world segs -> world segs -> Prop} : forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
(run_post_tok_AJxR R) W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply ajournal_x_exec_frR with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
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
Proof. exact (@SRr_chain_tok_AJx_frR (@wle segs)). Qed.
Lemma SRr_run_tok_AJx_frR {R : world segs -> world segs -> Prop} : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok segs tbl K Bx Bspan SH n ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
(run_post_tok_AJxR R) W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_tok_sound segs tbl K Bx Bspan SH tbl_ok n E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply SRr_chain_tok_AJx_frR; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
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
Proof. exact (@SRr_run_tok_AJx_frR (@wle segs)). Qed.
Lemma SRr_run_to_tok_AJx_frR {R : world segs -> world segs -> Prop} : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
(ajournal_xR R) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
(run_post_tok_AJxR R) W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_to_tok_sound segs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply SRr_chain_tok_AJx_frR; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
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
Proof. exact (@SRr_run_to_tok_AJx_frR (@wle segs)). Qed.
End e.
End l.
End x.
Arguments AR_laws_x {rc} segs B ARx hl.
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
- intros ly S Hp W mem md mem' md' HAR H1 H2 H3 H4 H5 H6 _. exact (al_frame _ _ L ly S W mem md mem' md' HAR H1 H2 H3 H4 H5 H6).
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
- (* field 17: ly_img covers every segment (ALedger's al_img, as FCiface.v:189), and a live fake frame lies at or
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
- (* field 18: the layout is layout_ok, ARm's am_layout (as FCiface.v:188) *)
  intros ly S Hp W mem md HAR. exact (am_layout _ _ _ _ (proj1 HAR)).
Qed.
