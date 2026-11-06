(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment GS of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x837c8 .. 0x839b8, gesture_seen's held-array search and update, relay.c:100-119
   inlined), in the form of the cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (a loop over
   concrete cut states) and lib/A/AC8h.v (call sites), and of this lane's W_send_line_entry.v.
   The statement is lib/A/W_drain_cx.v's dr_gs_stmt; the Section header below is that file's, verbatim.

   DGS (0x837c8) -> DLN (S q) (0x836f4), in three stages:
     gs_scan  0x837c8 .. 0x8389c   nheld <= 0, or the held-key search loop 0x83838 .. 0x83874
                                   (strlen 0x83850, strncmp 0x83864; its own induction, below)
     gs_add   0x8389c .. 0x839b8   a begin not held: realloc #2 0x838c0, strndup 0x838e0,
                                   s->held = res, held[nheld] = copy, nheld += 1
     gs_free  0x83940 .. 0x839b8   an end held at slot n: free #2 0x8394c, nheld -= 1,
                                   held[n] = held[nheld]
   and the three other exits of the search go straight to DLN (an end not held, a begin held). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_gs.v; 61 of its 208 lines of code are new or changed and 731 lines of the source are left out. *)
(* The CUT GAR and the statement of the second half of segment GS-ADD of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x838d8 .. 0x839b8, relay.c:115-118 inlined).  Nothing is proved here: the file fixes the
   machine state the first half leaves and the statement the second half takes, so that the two are proved in
   parallel.  The Section header is lib/A/W_drain_cx.v's, verbatim.

   GS-ADD is split at 0x838d8, just after `sd a0, 0(a1)` at 0x838d4 wrote s->held = res:
     GA  (0x8389c) -> GAR (0x838d8)   realloc(s->held, 8 * nheld + 8) at 0x838c0 and the store of its result
                                      (W_gsadd_scratch.v, gs_add with gs_addb_stmt as a premise);
     GAR (0x838d8) -> DLN (S q)       strndup(start, last - start) at 0x838e0, s->nheld = nheld + 1 at
                                      0x83914, s->held[nheld] = copy at 0x839b4 (gs_addb_stmt).

   WHAT GAR PINS, and why each conjunct is there.
   - the pc 0x838d8 and the registers the rest of the arm reads: s7 = s->buf + q (DLN wants it), s8 = the
     line's start and s9 = its last space (the strndup arguments, `sub a1, s9, s8` then `mv a0, s8`), s3 = the
     shadow address of &s->held (the checks at 0x838e8 and, through 128(sp), at 0x838fc), and dregs_line's
     own pins (sp, gp, tp, s6 = s, s11, s2 / s1 / s0 of g_s, s5 = the shadow base, dr_frame with 96(sp) =
     &s->nheld and 128(sp) = &s->held);
   - 72(sp) = the shadow address of &s->nheld, which the partial-granule test at 0x838f0-f4 reads;
   - the relay entry after realloc #2: its held array is the GROWN block, s->nheld and the key list are still
     the old ones, so `re_kh e1 = 8 * re_nheld e1 + 8` and `re_hp e1 <> 0`.  aentry_okx of that entry holds as
     it stands (8 * nheld <= kh, 8 <= kh, and the array image is the copied key_ptrs), so GARB is LCORE with
     only the ARRAY SIZE moved on: ka = seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q), the value
     DLINK's `ent_ka e1 = ds_ka` now needs.  The held KEYS move on only at 0x839b4, in the second half;
   - GARW: the held array is a block drain itself made, so a store into it is an awr_byte at ANY later block
     list (the engine's awr_ok_x obligation at 0x839b4, after strndup has added one more block).  This is
     awr_new_block_any's conclusion, carried across the cut because realloc's post is a Permutation, not the
     append shape that lemma takes;
   - rom_view as its own conjunct (it is also inside GARB's DMEM): by the stream's rule the second half must
     not have to re-derive it from rom_out;
   - the model: the line is a BEGIN whose key is not held, so seen_tr's two requests are the realloc the
     first half charged and the strndup the second half charges.  GARfut therefore owes
     `RMalloc (|x| + 1) :: tl2`, and the array's slot addresses (jb, o, ha, ks) are existential: the walk
     reads a request's SIZE through the meter, never its address. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx W_drain_gs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* 0x838d8 - 0x830dc = 0x7fc (fuzz_reply.asan; AF_fr_drain = 0xdf0). *)
Definition A_dr_addb : Z := AF_fr_drain + 0x7fc.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the instance's laws *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* the runtime entries drain calls, at their SIGMA pcs *)
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
(* the allocator's site rules (W_journal.v), at the trampolines the program calls *)
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the callees drain calls as a program *)
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
(* instance facts *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.

(* ---- The line loop's core at GAR.  Exactly W_drain_gs.v's GSB with the held array's SIZE moved on to the
   grown block (the keys themselves move at 0x839b4), so composing GA -> GAR -> DLN is an application. ---- *)
Definition GARB (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE B MT MMAX RG cx s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
  (GSno cx s1 p q) (GSoc cx s1 p q)
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

(* ---- What the walk still owes: strndup's request, then the lines and rounds after this one.  The base and
   the addresses are existential (no walk reads a request's address). ---- *)
Definition GARfut (cx : dcx) (s1 : drain_b_c.dstate) (p q : nat) (x : list Z)
(a : drain_b_c.dadr) (tl : dtrace) : Prop :=
exists (tl2 : dtrace) (jb' : nat) (o' ha' : dadrF) (ks' : list dadrF),
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a
  (GSno cx s1 p q) (GSoc cx s1 p q)
  (seen_arr (dlH cx s1 p) (dline s1 p q)) (seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
  (drlq s1 (S q)) jb' o' ha' ks' tl2 /\
tl = RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2.

(* ---- GAR (0x838d8): realloc #2 has returned a non-NULL grown array and s->held holds it; the key itself is
   still to be made.  a0 and a1 are dead here (0x838d8 and 0x838dc overwrite both). ---- *)
Definition GAR (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent a tl (jj : nat),
c1 = cfg_at SEGS (BASE + A_dr_addb) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 25 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) /\
getr regs1 19 = w64 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
(* the held array is the block realloc #2 returned: one free slot past the live ones *)
re_hp e1 <> 0 /\ re_kh e1 = 8 * re_nheld e1 + 8 /\
(* a store into that array is an awr_byte at any later block list (awr_new_block_any's conclusion) *)
(forall blc lyq ownq i, In (re_hp e1, re_kh e1) blc -> 0 <= i < req_size (re_kh e1) ->
   awr_byte DRAIN_STK (dsp0 cx) (dFP cx) (ablocks B (dxly cx) (dxS cx)) blc lyq ownq (re_hp e1 + i)) /\
rom_view SEGS W1 m1 /\
(* the model: a begin whose key is not held *)
gesture (dline s1 p q) = Some (GBegin, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None /\
GSF s1 p q /\
GARB cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GARfut cx s1 p q (firstn jj (dline s1 p q)) a tl.

(* ---- The second half: strndup (0x838e0, ASTRNDUP; NULL refuted by the forced-success rule), s->nheld =
   nheld + 1 (0x83914), s->held[nheld] = copy (0x839b4), then on to the next line. ---- *)
Definition gs_addb_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE B MT MMAX RG cx -> GAR cx s1 D p q W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x slice D, 2026-10-30): GARB, GAR and gs_addb_stmt over W_drain_cx_x.v's
   Section variables (B PST ARx MT RP MMAX RG), the entry's ghost list Hp and budget kr after cx, the cut's own ghost
   list Hp1 after S1.  GARfut (what the walk still owes: strndup's request, then the lines and rounds after this
   one) is AR-free and CITED.  Everything above is unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_cx W_drain_cx_x W_drain_gs.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.

(* The carriers of this Section at a world relation R (route R): each <name>R below is <name> with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, and every carrier or spec it names -> its R twin;
   every other token is the strict text's. The strict <name> is <name>R at R := wle. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Definition GARB_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])
  (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
  (GSno cx s1 p q) (GSoc cx s1 p q)
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

Definition GAR_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent a tl (jj : nat),
c1 = cfg_at SEGS (BASE + A_dr_addb) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 25 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) /\
getr regs1 19 = w64 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
(* the held array is the block realloc #2 returned: one free slot past the live ones *)
re_hp e1 <> 0 /\ re_kh e1 = 8 * re_nheld e1 + 8 /\
(* a store into that array is an awr_byte at any later block list (awr_new_block_any's conclusion) *)
(forall blc lyq ownq i, In (re_hp e1, re_kh e1) blc -> 0 <= i < req_size (re_kh e1) ->
   awr_byte DRAIN_STK_x (dsp0 cx) (dFP cx) (ablocks B (dxly cx) (dxS cx)) blc lyq ownq (re_hp e1 + i)) /\
rom_view SEGS W1 m1 /\
(* the model: a begin whose key is not held *)
gesture (dline s1 p q) = Some (GBegin, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None /\
GSF s1 p q /\
GARB_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GARfut cx s1 p q (firstn jj (dline s1 p q)) a tl.

Definition gs_addb_stmt_xR : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GAR_xR cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
End wR.


(* GARB over LCORE_x: GSB_x with the held array's SIZE moved on to the grown block *)
Definition GARB_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
GARB_xR (@wle SEGS) cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

(* GAR (0x838d8), the cut's ghost list Hp1 an existential after S1 *)
Definition GAR_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
GAR_xR (@wle SEGS) cx Hp kr s1 D p q W1 c1.

(* the second half: strndup (0x838e0), s->nheld = nheld + 1 (0x83914), s->held[nheld] = copy (0x839b4) *)
Definition gs_addb_stmt_x : Prop :=
gs_addb_stmt_xR (@wle SEGS).

End cx.
End bx.
End ax.
