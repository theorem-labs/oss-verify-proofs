(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (G-BRA): the SEGMENT INTERFACE of the image-B walk of relay_add over a generic
   allocator relation ARx (route (b), CONVERSION.md (sha256 1015972e02a9; internal record)): the twin of lib/B/W_relay_add_cut.v
   (the AR walk's interface, whose machine-code account of 0x82af4 .. 0x82ca0 holds unchanged) with afn_pre ->
   afn_pre_x, ajournal_gx -> ajournal_gx_x (Section variables PST and ARx after B, Hp after S, Hp' after S'), ra_spec /
   ra_post -> W_contract_x's ra_spec_x / ra_post_x.  The AR-free parts of the AR interface (the cut addresses A_ra_*,
   RA_SAVED, RA_HI_*, ra_cells, ra_aligned, the rebase lemmas, ra_apart and the placement facts of Section fr) are
   cited from lib/B/W_relay_add_cut.v, not copied.

   The ROOM round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record); the B kit's room texts, W_contract_x.v Section w5 `Variable RP : roomp`):
   ra_spec_x quantifies the room budget kr after its premises and asks rp_RM RP S (Z.to_nat (ra_cost MT_rk T) + kr) and
   cnt_ok_pk RP (ra_peak T) (ablocks B ly S); ra_post_x gives rp_RM RP S' kr.  relay_add itself takes no fake frame
   (0x82af4: no frame pointer, no __asan_stack_malloc call), so the room moves only at the realloc (the rule's post
   gives rp_RM RP S2 kr) and at wake's fake frame (W_wake_c_x.v's seat fact S' = set_fs f S, then rp_RPF); the fd < 0
   return and the T <> 0 arm make no allocator call (rp_RMM).

   The entry context gains the ghost head set bxHp and the room budget bxkr; every cut predicate names the head set of
   its state, and the cuts after the realloc's place (RBA, RBU) carry rp_RM RP S1 bxkr.  The Section below has only
   Variables: the cut predicates and segment statements depend on B PST ARx MT RP G RG CTX alone, and every segment file
   (W_relay_add_{ent,held,app,tail}_x.v) states its own hypotheses.  ra_all_x composes the four segment statements into
   ra_spec_x B PST ARx MT RP G RG CTX A_relay_addP (W_contract_x.v Section w5). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal W_sites W_rep W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_contract_x W_relay_add_cut.
(* route R: relay_add's contract at R (W_contract_srlf_xR.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_srlf_xR.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round's record (W_journal_x.v Record roomp): the room invariant rp_RM with its laws rp_RMM / rp_RPF *)
Variable RP : roomp.
Variable G : list (Z * Z).
Variable RG : rep_globals.
(* the allocator rules' caller-context table (W_contract_x.v Section w5's CTX; W_journal_x.v Section hc, the _c rules) *)
Variable CTX : list (list Z).

(* ---- The entry context: everything ra_spec_x quantifies over at the entry (W_relay_add_cut.v racx + the head set and
   the room budget). ---- *)
Record racx_x : Type := mkRacxX {
  bxregs : bvmap 5 word;
  bxly : alayout; bxS : astate; bxHp : list Z; bxW : world SEGS; bxmem : word -> option byte; bxmd : Model;
  bxch : list (Z * Z * Z);
  bxfd : Z; bxT : Z; bxes : list rentry; bxkr : nat }.

Definition bsp0 (cx : racx_x) : Z := spZ (bxregs cx).
Definition bFP (cx : racx_x) : list (Z * Z) := ra_FP (bxT cx) (bxes cx).
Definition bPOST (cx : racx_x) : world SEGS -> config -> Prop :=
ra_post_x B PST ARx MT RP G RG (bxregs cx) (bxly cx) (bxS cx) (bxHp cx) (bxW cx) (bxmem cx) (bxmd cx)
  (bxfd cx) (bxT cx) (bxes cx) (bxkr cx).

(* BBASE: exactly ra_spec_x's premises at the entry, in its order (W_contract_x.v Section w5 ra_spec_x), the room's two
   after the budget kr. *)
Definition BBASE (cx : racx_x) : Prop :=
afn_pre_x SEGS B ARx RA_STK (bxly cx) (bxS cx) (bxHp cx) (bxW cx) (bxregs cx) (bxmem cx) (bxmd cx) (bxch cx) /\
bsp0 cx mod 32 = 0 /\ count_cid 0 (frames (bxS cx)) < fs_frames 0 /\
getr (bxregs cx) 10 = Z_to_bv 64 (bxfd cx) /\ - 2 ^ 31 <= bxfd cx < 2 ^ 31 /\
alock_at RG (bxW cx) (bxmem cx) false /\ awake_at RG (bxW cx) (bxmem cx) /\ rom_view SEGS (bxW cx) (bxmem cx) /\
ra_rel B RG (bxly cx) (bxS cx) (bxW cx) (bxmem cx) (bxT cx) (bxes cx) /\
(0 <= bxfd cx -> (length (bxes cx) < 4)%nat /\ ~ In (bxfd cx) (map re_fd (bxes cx))) /\
(forall a, inG (RA_G RG) a -> inG G a) /\
(forall a, inG (RA_G RG) a -> ~ (as_errno B <= a < as_errno B + 4)) /\
(0 <= bxfd cx -> bxT cx = 0 -> blocks_bytes (bxS cx) + ATABLE <= LIVE_MAX) /\
In [A_relay_addP + 144] CTX /\
mo_ok MT (bxS cx) (ra_cost MT (bxT cx)) /\
rp_RM RP (bxS cx) (Z.to_nat (ra_cost MT_rk (bxT cx)) + bxkr cx) /\
cnt_ok_pk RP (ra_peak (bxT cx)) (ablocks B (bxly cx) (bxS cx)).

(* ---- The frame: after the prologue, sp = the entry sp - 64, the eight saved registers in their slots. ---- *)
Definition rb_saved (cx : racx_x) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
forall i, (i < 8)%nat ->
val_mem SEGS (arm W1 m1) (bsp0 cx - RA_FRAME + 8 * Z.of_nat i) 8 (bv_unsigned (getr (bxregs cx) (nth i RA_SAVED 0%bv))).

(* The registers every cut holds: sp, gp, tp and s7 .. s11 (never saved by relay_add, kept in their registers). *)
Definition bregs_base (cx : racx_x) (regs1 : bvmap 5 word) : Prop :=
spZ regs1 = bsp0 cx - RA_FRAME /\
getr regs1 3 = getr (bxregs cx) 3 /\ getr regs1 4 = getr (bxregs cx) 4 /\
getr regs1 23 = getr (bxregs cx) 23 /\ getr regs1 24 = getr (bxregs cx) 24 /\
getr regs1 25 = getr (bxregs cx) 25 /\ getr regs1 26 = getr (bxregs cx) 26 /\
getr regs1 27 = getr (bxregs cx) 27.
(* ... and, after the lock: s0 = fd and s2 = the shadow offset (ld through the GOT at 0x82b24-0x82b2c). *)
Definition bregs_held (cx : racx_x) (regs1 : bvmap 5 word) : Prop :=
bregs_base cx regs1 /\ getr regs1 8 = w64 (bxfd cx) /\ getr regs1 18 = w64 SHADOW_OFF.

(* errno's four bytes keep their view from (W, mem) to (W', mem') (ra_post_x's last conjunct, in its orientation). *)
Definition berrno_kept (W : world SEGS) (mem : word -> option byte) (W' : world SEGS) (mem' : word -> option byte) : Prop :=
forall i, 0 <= i < 4 -> aview SEGS (w_H W') mem' (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i).

(* BLIVE: the journal from the entry (at RA_G, the stack RA_STK and the footprint ra_FP) owning no frame, over ARx; the
   .rodata view (wake's premise), the presence of image bytes (ra_post_x's apres_kept), the saved registers, g_lock
   held, g_wake[1] = -1, the fake-frame count of the entry, errno's view as at the entry. *)
Definition BLIVE (cx : racx_x) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) : Prop :=
ajournal_gx_x SEGS B PST ARx (RA_G RG) 0 [] RA_STK (bsp0 cx) (bFP cx)
  (bxly cx) (bxS cx) (bxHp cx) (bxW cx) (bxmem cx) (bxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (bxW cx) (bxmem cx) W1 m1 /\
rb_saved cx W1 m1 /\ alock_at RG W1 m1 true /\ awake_at RG W1 m1 /\ frames S1 = frames (bxS cx) /\
berrno_kept (bxW cx) (bxmem cx) W1 m1.

(* ---- The cut predicates (W_relay_add_cut.v RAH / RAA / RAU, with the head set). ---- *)
(* RBH (0x82b3c): the lock taken; the allocator state, its head set, the relay and the live blocks as at the entry. *)
Definition RBH (cx : racx_x) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 m1 md1,
c1 = cfg_at SEGS (BASE + A_ra_held) regs1 m1 md1 /\
bregs_held cx regs1 /\ 0 <= bxfd cx /\
BLIVE cx (bxly cx) (bxS cx) (bxHp cx) W1 m1 md1 0 /\
ra_rel B RG (bxly cx) (bxS cx) W1 m1 (bxT cx) (bxes cx).

(* RBA (0x82b90): the table at T1 holds the entry's es (T1 = T, or the realloc's block when T = 0), g_capsrc = 16;
   s3 / s4 the auipc images of g_nsrc and g_src; the meter charged the realloc (ra_cost) when T = 0; the room is the
   post's budget kr (the realloc's rule post when T = 0; the entry's, ra_cost MT_rk T = 0, when T <> 0). *)
Definition RBA (cx : racx_x) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 T1,
c1 = cfg_at SEGS (BASE + A_ra_app) regs1 m1 md1 /\
bregs_held cx regs1 /\
getr regs1 19 = w64 (rg_nsrc RG - RA_HI_NSRC) /\ getr regs1 20 = w64 (rg_src RG - RA_HI_SRC) /\
0 <= bxfd cx /\
BLIVE cx ly1 S1 Hp1 W1 m1 md1 k1 /\
arelay_at B RG ly1 S1 W1 m1 T1 (bxes cx) /\
mo_le MT (bxS cx) S1 (ra_cost MT (bxT cx)) /\
rp_RM RP S1 (bxkr cx) /\
((bxT cx = 0 /\ Permutation (ablocks B ly1 S1) ((T1, ATABLE) :: ablocks B (bxly cx) (bxS cx))) \/
 (bxT cx <> 0 /\ T1 = bxT cx /\ ablocks B ly1 S1 = ablocks B (bxly cx) (bxS cx))).

(* RBU (0x82c04, after `sw s0,0(s1)`): the entry ra_new fd appended (the table at T1 holds es ++ [ra_new fd],
   g_nsrc = |es| + 1), the lock still held, the room as at RBA (memset keeps the allocator state). *)
Definition RBU (cx : racx_x) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 T1,
c1 = cfg_at SEGS (BASE + A_ra_unlock) regs1 m1 md1 /\
bregs_held cx regs1 /\ 0 <= bxfd cx /\
BLIVE cx ly1 S1 Hp1 W1 m1 md1 k1 /\
arelay_at B RG ly1 S1 W1 m1 T1 (bxes cx ++ [ra_new (bxfd cx)]) /\
mo_le MT (bxS cx) S1 (ra_cost MT (bxT cx)) /\
rp_RM RP S1 (bxkr cx) /\
((bxT cx = 0 /\ Permutation (ablocks B ly1 S1) ((T1, ATABLE) :: ablocks B (bxly cx) (bxS cx))) \/
 (bxT cx <> 0 /\ T1 = bxT cx /\ ablocks B ly1 S1 = ablocks B (bxly cx) (bxS cx))).

(* ---- The segment statements (W_relay_add_cut.v ra_*_stmt over the _x cuts). ---- *)
(* ENT: the prologue 0x82af4-0x82b14, the fd < 0 test 0x82b1c (fd < 0: the epilogue 0x82c18 and the return), the
   shadow offset 0x82b24-0x82b2c and pthread_mutex_lock (&g_lock) 0x82b38 -> RBH. *)
Definition rb_ent_stmt : Prop :=
forall cx,
BBASE cx ->
(forall W2 c2, RBH cx W2 c2 -> SRr SEGS W2 c2 (bPOST cx)) ->
SRr SEGS (bxW cx) (cfg_at SEGS A_relay_addP (bxregs cx) (bxmem cx) (bxmd cx)) (bPOST cx).

(* HELD: RBH 0x82b3c -> the globals, `bne` 0x82b50, the empty table's realloc 0x82b80 (the doubling arm with its TRAP
   0x82b60 refuted: |es| < 4 < 16), `beqz a0` 0x82b84 not taken, the stores of g_src and g_capsrc -> RBA. *)
Definition rb_held_stmt : Prop :=
forall cx W1 c1,
BBASE cx -> RBH cx W1 c1 ->
(forall W2 c2, RBA cx W2 c2 -> SRr SEGS W2 c2 (bPOST cx)) ->
SRr SEGS W1 c1 (bPOST cx).

(* APP: RBA 0x82b90 -> the slot, TRAPS 0x82bb0 / 0x82bc4, __asan_memset (s1, 0, 56) 0x82bd4, TRAP 0x82bdc,
   g_nsrc += 1, TRAPS 0x82be4 / 0x82bec, the shadow check 0x82bf0-0x82bfc, s1->fd = fd 0x82c00 -> RBU. *)
Definition rb_app_stmt : Prop :=
forall cx W1 c1,
BBASE cx -> RBA cx W1 c1 ->
(forall W2 c2, RBU cx W2 c2 -> SRr SEGS W2 c2 (bPOST cx)) ->
SRr SEGS W1 c1 (bPOST cx).

(* TAIL: RBU 0x82c04 -> pthread_mutex_unlock (&g_lock) 0x82c0c, wake () 0x82c10 (wk_spec_x, W_wake_c_x.v), s1 = 0, the
   epilogue 0x82c18-0x82c3c and the return -> ra_post_x's fd >= 0 arm. *)
Definition rb_tail_stmt : Prop :=
forall cx W1 c1,
BBASE cx -> RBU cx W1 c1 ->
SRr SEGS W1 c1 (bPOST cx).

(* The walk: the segments give relay_add's _x contract. *)
Lemma ra_all_x : rb_ent_stmt -> rb_held_stmt -> rb_app_stmt -> rb_tail_stmt ->
ra_spec_x B PST ARx MT RP G RG CTX A_relay_addP.
Proof.
intros ENT HELD APP TAIL W ly S Hp regs mem md ch fd T es H1 H2 H3 H4 H5 H6 H7 H7r H8 H9 H10 H11 H12 H12c H13
  kr HRM HPK.
set (cx := mkRacxX regs ly S Hp W mem md ch fd T es kr).
assert (HB : BBASE cx)
  by exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H7r (conj H8 (conj H9 (conj H10
    (conj H11 (conj H12 (conj H12c (conj H13 (conj HRM HPK)))))))))))))))).
apply (ENT cx HB). intros W2 c2 HR. apply (HELD cx W2 c2 HB HR). intros W3 c3 HA. apply (APP cx W3 c3 HB HA).
intros W4 c4 HU. exact (TAIL cx W4 c4 HB HU).
Qed.

(* ---- Shared lemmas. ---- *)
(* The walk's journal at RA_G is a journal at the caller's G (ra_spec_x's premise). *)
Lemma rb_lift : forall cx XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
BBASE cx ->
ajournal_gx_x SEGS B PST ARx (RA_G RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros cx XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HB HJ.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGin & _).
exact (ajournal_gx_G_mono_x SEGS B PST ARx (RA_G RG) G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k
  HGin HJ).
Qed.
Lemma rb_errno_notG : forall cx, BBASE cx -> forall i, 0 <= i < 4 -> ~ inG (RA_G RG) (as_errno B + i).
Proof.
intros cx HB i Hi HG. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGerr & _).
apply (HGerr _ HG). lia.
Qed.
Lemma rb_errno_step : forall W m W1 m1 W2 m2, berrno_kept W m W1 m1 ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) m2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
berrno_kept W m W2 m2.
Proof. intros W m W1 m1 W2 m2 H1 H2 i Hi. rewrite (H2 i Hi). exact (H1 i Hi). Qed.
Lemma rb_errno_refl : forall W m, berrno_kept W m W m.
Proof. intros W m i Hi. reflexivity. Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the segment interface at a world relation R.  relay_add's realloc of the table
   re-hides at the cf instance (R := wle' SEGS RZ_cf), so the walk's cut journal (BLIVE) and every segment's step relation
   are at R: BLIVER (ajournal_gx_xR .. R ..), RBHR / RBAR / RBUR, the four segment statements at SRrG SEGS R, and
   ra_all_xR composing them into ra_spec_xR (W_contract_srlf_xR.v).  BBASE, the register, frame and errno
   predicates are R-free and shared.  At R := wle each is its strict twin above by conversion. *)
Section cR.
Variable R : world SEGS -> world SEGS -> Prop.
Definition bPOSTR (cx : racx_x) : world SEGS -> config -> Prop :=
ra_post_xR B PST ARx R MT RP G RG (bxregs cx) (bxly cx) (bxS cx) (bxHp cx) (bxW cx) (bxmem cx) (bxmd cx)
  (bxfd cx) (bxT cx) (bxes cx) (bxkr cx).
Definition BLIVER (cx : racx_x) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) : Prop :=
ajournal_gx_xR SEGS B PST ARx R (RA_G RG) 0 [] RA_STK (bsp0 cx) (bFP cx)
  (bxly cx) (bxS cx) (bxHp cx) (bxW cx) (bxmem cx) (bxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (bxW cx) (bxmem cx) W1 m1 /\
rb_saved cx W1 m1 /\ alock_at RG W1 m1 true /\ awake_at RG W1 m1 /\ frames S1 = frames (bxS cx) /\
berrno_kept (bxW cx) (bxmem cx) W1 m1.
Definition RBHR (cx : racx_x) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 m1 md1,
c1 = cfg_at SEGS (BASE + A_ra_held) regs1 m1 md1 /\
bregs_held cx regs1 /\ 0 <= bxfd cx /\
BLIVER cx (bxly cx) (bxS cx) (bxHp cx) W1 m1 md1 0 /\
ra_rel B RG (bxly cx) (bxS cx) W1 m1 (bxT cx) (bxes cx).
Definition RBAR (cx : racx_x) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 T1,
c1 = cfg_at SEGS (BASE + A_ra_app) regs1 m1 md1 /\
bregs_held cx regs1 /\
getr regs1 19 = w64 (rg_nsrc RG - RA_HI_NSRC) /\ getr regs1 20 = w64 (rg_src RG - RA_HI_SRC) /\
0 <= bxfd cx /\
BLIVER cx ly1 S1 Hp1 W1 m1 md1 k1 /\
arelay_at B RG ly1 S1 W1 m1 T1 (bxes cx) /\
mo_le MT (bxS cx) S1 (ra_cost MT (bxT cx)) /\
rp_RM RP S1 (bxkr cx) /\
((bxT cx = 0 /\ Permutation (ablocks B ly1 S1) ((T1, ATABLE) :: ablocks B (bxly cx) (bxS cx))) \/
 (bxT cx <> 0 /\ T1 = bxT cx /\ ablocks B ly1 S1 = ablocks B (bxly cx) (bxS cx))).
Definition RBUR (cx : racx_x) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 T1,
c1 = cfg_at SEGS (BASE + A_ra_unlock) regs1 m1 md1 /\
bregs_held cx regs1 /\ 0 <= bxfd cx /\
BLIVER cx ly1 S1 Hp1 W1 m1 md1 k1 /\
arelay_at B RG ly1 S1 W1 m1 T1 (bxes cx ++ [ra_new (bxfd cx)]) /\
mo_le MT (bxS cx) S1 (ra_cost MT (bxT cx)) /\
rp_RM RP S1 (bxkr cx) /\
((bxT cx = 0 /\ Permutation (ablocks B ly1 S1) ((T1, ATABLE) :: ablocks B (bxly cx) (bxS cx))) \/
 (bxT cx <> 0 /\ T1 = bxT cx /\ ablocks B ly1 S1 = ablocks B (bxly cx) (bxS cx))).
Definition rb_ent_stmtR : Prop :=
forall cx,
BBASE cx ->
(forall W2 c2, RBHR cx W2 c2 -> SRrG SEGS R W2 c2 (bPOSTR cx)) ->
SRrG SEGS R (bxW cx) (cfg_at SEGS A_relay_addP (bxregs cx) (bxmem cx) (bxmd cx)) (bPOSTR cx).
Definition rb_held_stmtR : Prop :=
forall cx W1 c1,
BBASE cx -> RBHR cx W1 c1 ->
(forall W2 c2, RBAR cx W2 c2 -> SRrG SEGS R W2 c2 (bPOSTR cx)) ->
SRrG SEGS R W1 c1 (bPOSTR cx).
Definition rb_app_stmtR : Prop :=
forall cx W1 c1,
BBASE cx -> RBAR cx W1 c1 ->
(forall W2 c2, RBUR cx W2 c2 -> SRrG SEGS R W2 c2 (bPOSTR cx)) ->
SRrG SEGS R W1 c1 (bPOSTR cx).
Definition rb_tail_stmtR : Prop :=
forall cx W1 c1,
BBASE cx -> RBUR cx W1 c1 ->
SRrG SEGS R W1 c1 (bPOSTR cx).
Lemma ra_all_xR : rb_ent_stmtR -> rb_held_stmtR -> rb_app_stmtR -> rb_tail_stmtR ->
ra_spec_xR B PST ARx R MT RP G RG CTX A_relay_addP.
Proof.
intros ENT HELD APP TAIL W ly S Hp regs mem md ch fd T es H1 H2 H3 H4 H5 H6 H7 H7r H8 H9 H10 H11 H12 H12c H13
  kr HRM HPK.
set (cx := mkRacxX regs ly S Hp W mem md ch fd T es kr).
assert (HB : BBASE cx)
  by exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H7r (conj H8 (conj H9 (conj H10
    (conj H11 (conj H12 (conj H12c (conj H13 (conj HRM HPK)))))))))))))))).
apply (ENT cx HB). intros W2 c2 HR. apply (HELD cx W2 c2 HB HR). intros W3 c3 HA. apply (APP cx W3 c3 HB HA).
intros W4 c4 HU. exact (TAIL cx W4 c4 HB HU).
Qed.
Lemma rb_liftR : forall cx XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
BBASE cx ->
ajournal_gx_xR SEGS B PST ARx R (RA_G RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros cx XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HB HJ.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGin & _).
exact (ajournal_gx_G_mono_xR SEGS B PST ARx (RA_G RG) G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k
  HGin HJ).
Qed.
End cR.
End c.
End b.
End a.
