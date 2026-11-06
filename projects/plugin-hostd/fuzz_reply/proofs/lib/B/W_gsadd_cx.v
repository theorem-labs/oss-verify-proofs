(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the CUT GAR and the statement of the second half of the GS-ADD arm of
   segment GS of the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's drain (0x83c00 .. 0x83ca8,
   relay.c:115-118 inlined).  Proves no function (kind: segment lemma of drain's image-B walk, GS piece gs_add).
   Nothing is proved here: the file fixes the machine state the first half leaves and the statement the second
   half takes.  The Section header is lib/B/W_drain_gs.v's (= lib/B/W_drain_cx.v's), verbatim.

   GS-ADD (lib/B/W_drain_gs.v gs_add_stmt, GA 0x83ba0 -> DLN 0x839d4 at S q) is split at 0x83c00, just after
   `sd a0, 0(a1)` at 0x83bfc wrote e->held = res, as image A's lib/A/W_gsaddb_cx.v (a working branch)
   splits its arm at 0x838d8:
     GA  (0x83ba0) -> GAR (0x83c00)   the two tests, realloc(e->held, 8 * (nheld + 1)) at 0x83be8 and the store
                                      of its result (lib/B/W_gsadd_a.v, gs_adda with gs_addb_stmt as a premise);
     GAR (0x83c00) -> DLN (S q)       strndup(s8, 192(sp)) at 0x83c08, e->nheld = nheld + 1 at 0x83c5c,
                                      e->held[nheld] = copy at 0x83ca4 (lib/B/W_gsadd_b.v, gs_addb).
   Every pc, register and frame slot below is image B's (fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) 0x83ba0 .. 0x83ca8).

   WHAT GAR PINS, and why each conjunct is there.
   - the pc 0x83c00 and what the second half reads: dregs_gs (sp, gp, tp, s0 / s1 / s2 and dr_frame, whose slots
     32 = SA + 48, 88 = SA + 40, 128 / 136 / 144 = SA + 16 / SA + 24 / SA and 240 = SHADOW_OFF the arm reloads),
     s11 = SA + 32 (DLN's dregs_line wants it and the arm never writes it), s7 = buf + q (DLN), s8 = buf + p
     (strndup's a0, `mv a0, s8` at 0x83c00), s3 = the shadow address of &e->held (`lbu a1, 0(s3)` at 0x83c2c);
     the two scratch slots the arm reads: 16(sp) = the shadow address of &e->nheld (0x83c10, 0x83c34) and
     192(sp) = jj, strndup's length (0x83c04);
   - dinband / 0 < cap of the relay's buffer: DLN carries them;
   - the relay entry after realloc #2: its held array is the GROWN block, e->nheld and the key list are still the
     old ones, so `re_kh e1 = 8 * re_nheld e1 + 8` and `re_hp e1 <> 0`; GARB is LCORE with only the ARRAY SIZE
     moved on (ka = seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q));
   - the awr_byte conjunct: the held array is a block drain made, so a store into it is an awr_byte at any later
     block list (the engine's awr_ok_x obligation at 0x83ca4, after strndup added one more block);
   - rom_view, as its own conjunct;
   - the model: the line is a BEGIN whose key is not held; GARfut owes strndup's RMalloc (|x| + 1) and then the
     rest tl2, and carries the two signs 0 <= tr_cost tl2 and 0 <= tr_alloc tl2 that split the budget at the
     strndup call (the first half has them from tr_sizes_ok of the whole owed trace). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx W_drain_gs.
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

(* 0x83c00 - 0x83278 = 0x988 (fuzz_reply.asan-ubsan; AF_fr_drain = 0xf34, fr_B0 = 0x82344). *)
Definition A_dr_addb : Z := AF_fr_drain + 0x988.
Lemma P0_dr_addb : fr_B0 + A_dr_addb = 0x83c00.
Proof. reflexivity. Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

(* ---- The line loop's core at GAR: W_drain_gs.v's GSB with the held array's SIZE moved on to the grown block
   (the keys themselves move at 0x83ca4), so composing GA -> GAR -> DLN is an application. ---- *)
Definition GARB (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE B MT MMAX RG cx s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
  (GSno cx s1 p q) (GSoc cx s1 p q)
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

(* ---- What the walk still owes: strndup's request, then the lines and rounds after this one, whose cost and
   live bytes are nonnegative.  The base and the addresses are existential (no walk reads a request's
   address). ---- *)
Definition GARfut (cx : dcx) (s1 : drain_b_c.dstate) (p q : nat) (x : list Z)
(a : drain_b_c.dadr) (tl : dtrace) : Prop :=
exists (tl2 : dtrace) (jb' : nat) (o' ha' : dadrF) (ks' : list dadrF),
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a
  (GSno cx s1 p q) (GSoc cx s1 p q)
  (seen_arr (dlH cx s1 p) (dline s1 p q)) (seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
  (drlq s1 (S q)) jb' o' ha' ks' tl2 /\
tl = RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2 /\
0 <= tr_cost MT tl2 /\ 0 <= tr_alloc tl2.

(* ---- GAR (0x83c00): realloc #2 has returned a non-NULL grown array and e->held holds it; the key itself is
   still to be made.  a0 / a1 are dead here (0x83c00 and 0x83c04 overwrite both). ---- *)
Definition GAR (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent a tl (jj : nat),
c1 = cfg_at SEGS (BASE + A_dr_addb) regs1 m1 md1 /\
dregs_gs RG cx regs1 W1 m1 /\
getr regs1 27 = w64 (dxSA cx + 32) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
(* the held array is the block realloc #2 returned: one free slot past the live ones *)
re_hp e1 <> 0 /\ re_kh e1 = 8 * re_nheld e1 + 8 /\
(* a store into that array is an awr_byte at any later block list *)
(forall blc lyq ownq i, In (re_hp e1, re_kh e1) blc -> 0 <= i < req_size (re_kh e1) ->
   awr_byte DRAIN_STK (dsp0 cx) (dFP cx) (ablocks B (dxly cx) (dxS cx)) blc lyq ownq (re_hp e1 + i)) /\
rom_view SEGS W1 m1 /\
(* the model: a begin whose key is not held *)
gesture (dline s1 p q) = Some (GBegin, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None /\
GSF s1 p q /\
GARB cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GARfut cx s1 p q (firstn jj (dline s1 p q)) a tl.

(* ---- The second half: strndup (0x83c08, ASTRNDUP; NULL refuted by the forced-success rule), e->nheld =
   nheld + 1 (0x83c5c), e->held[nheld] = copy (0x83ca4), then on to the next line. ---- *)
Definition gs_addb_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE B MT MMAX RG cx -> GAR cx s1 D p q W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (image B's DR_x slice D, 2026-10-30; the B twin of lib/A/W_gsaddb_cx.v's Section cx
   at a working branch 50623273289): GARB, GAR and gs_addb_stmt over lib/B/W_drain_cx_x.v's Section variables
   (B PST ARx MT RP MMAX RG), the entry's ghost list Hp and budget kr after cx, the cut's own ghost list Hp1 after S1.
   GARB_x / GAR_x are GARB / GAR above (image B's registers and scratch slots) with W_drain_cx_x.v's LCORE_x; GARfut
   (what the walk still owes: strndup's request, then the lines and rounds after this one) and A_dr_addb are AR-free
   and CITED.  Everything above this line is unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_cx W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
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

(* GARB over LCORE_x: W_drain_gs.v's GSB_x with the held array's SIZE moved on to the grown block *)
Definition GARB_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])
  (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
  (GSno cx s1 p q) (GSoc cx s1 p q)
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

(* GAR (0x83c00), the cut's ghost list Hp1 an existential after S1 *)
Definition GAR_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent a tl (jj : nat),
c1 = cfg_at SEGS (BASE + A_dr_addb) regs1 m1 md1 /\
dregs_gs RG cx regs1 W1 m1 /\
getr regs1 27 = w64 (dxSA cx + 32) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
(* the held array is the block realloc #2 returned: one free slot past the live ones *)
re_hp e1 <> 0 /\ re_kh e1 = 8 * re_nheld e1 + 8 /\
(* a store into that array is an awr_byte at any later block list *)
(forall blc lyq ownq i, In (re_hp e1, re_kh e1) blc -> 0 <= i < req_size (re_kh e1) ->
   awr_byte DRAIN_STK_x (dsp0 cx) (dFP cx) (ablocks B (dxly cx) (dxS cx)) blc lyq ownq (re_hp e1 + i)) /\
rom_view SEGS W1 m1 /\
(* the model: a begin whose key is not held *)
gesture (dline s1 p q) = Some (GBegin, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None /\
GSF s1 p q /\
GARB_x cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GARfut MT cx s1 p q (firstn jj (dline s1 p q)) a tl.

(* the second half: strndup (0x83c08), e->nheld = nheld + 1 (0x83c5c), e->held[nheld] = copy (0x83ca4) *)
Definition gs_addb_stmt_x : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GAR_x cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).

Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Local Notation LCORE_R := (LCORE_xR B PST ARx MT RP MMAX RG R).
Local Notation DLN_R := (DLN_xR B PST ARx MT RP MMAX RG R).
Local Notation dPOST_R := (dPOST_xR B PST ARx MT RP RG R).
Definition GARB_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE_R cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])
  (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
  (GSno cx s1 p q) (GSoc cx s1 p q)
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.
Definition GAR_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent a tl (jj : nat),
c1 = cfg_at SEGS (BASE + A_dr_addb) regs1 m1 md1 /\
dregs_gs RG cx regs1 W1 m1 /\
getr regs1 27 = w64 (dxSA cx + 32) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
re_hp e1 <> 0 /\ re_kh e1 = 8 * re_nheld e1 + 8 /\
(forall blc lyq ownq i, In (re_hp e1, re_kh e1) blc -> 0 <= i < req_size (re_kh e1) ->
   awr_byte DRAIN_STK_x (dsp0 cx) (dFP cx) (ablocks B (dxly cx) (dxS cx)) blc lyq ownq (re_hp e1 + i)) /\
rom_view SEGS W1 m1 /\
gesture (dline s1 p q) = Some (GBegin, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None /\
GSF s1 p q /\
GARB_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GARfut MT cx s1 p q (firstn jj (dline s1 p q)) a tl.
Definition gs_addb_stmt_xR : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GAR_xR cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_R cx Hp kr).
End wR.
Lemma GARB_x_wle : GARB_x = GARB_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma GAR_x_wle : GAR_x = GAR_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma gs_addb_stmt_x_wle : gs_addb_stmt_x = gs_addb_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.

End cx.
End bx.
End ax.
