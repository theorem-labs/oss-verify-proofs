(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segments FEED and FEEDS of the ASan walk of fuzz_reply's drain -
   reference_feed's byte loop (fuzz_reply.asan 0x8347c .. 0x83550, the call to list_push at 0x834f0) and
   its composition.  The statements are W_drain_cx.v:805 dr_feed_stmt and :851 dr_feeds_stmt; the cut
   predicates are W_drain_cx.v:601 DRB (the loop head, after k of the n bytes) and :619 DE (the loop left).
   The Section header below is W_drain_top.v:44-102 verbatim, so that dr_feed_p / dr_feeds_p carry exactly
   the premises of that file's dr_feed / dr_feeds.

   THE LOOP, as the pinned listing holds it (W_listing.v; address a is entry (a - 0x822ec) / 4, line 41 +
   entry; fr_prog_start = 0x822ec, AF_fr_drain = 0xdf0, AF_fr_list_push = 0x2da4):

     0x8347c  srli a0, s8, 3          the shadow address of the source byte p0 + k
     0x83480  add  a0, a0, s5         s5 = SHADOW_OFF
     0x83484  lb   a0, 0(a0)
     0x83488  bne  a0, zero, 0x83558  -> the partial-granule check, then back to 0x8348c
     0x8348c  lb   a0, 0(s6)          the shadow byte of h->overlong
     0x83490  lbu  a1, 0(s10)         b = *(p0 + k)
     0x83494  bne  a0, zero, 0x83564  -> the 4-byte partial-granule check, then back to 0x83498
     0x83498  lw   a0, 56(s7)         overlong  (s7 = HA = &g_s[j])
     0x8349c  beq  a1, zero, 0x834d0  b = 0: the NUL case
     0x834a0  bne  a0, zero, 0x83544  overlong <> 0: drop the byte
     0x834a4  lbu  a0, 0(s11)         the shadow byte of h->npartial
     0x834a8  bne  a0, zero, 0x83c54  -> __asan_report_load8 (HA + 48)
     0x834ac  ld   a0, 48(s7)         npartial
     0x834b0  lui  a2, 0x1
     0x834b4  addiw a2, a2, 1904      a2 = 6000 = APARTIAL
     0x834b8  bne  a0, a2, 0x83510    npartial <> 6000: the ordinary case
     0x834bc  lb   a0, 0(s6)
     0x834c0  bne  a0, zero, 0x8358c  -> the 4-byte store check, then back to 0x834c4
     0x834c4  addi a0, zero, 1
     0x834c8  sw   a0, 56(s7)         h->overlong = 1
     0x834cc  jal  zero, 0x83544

     the NUL case:
     0x834d0  bne  a0, zero, 0x834f4  overlong <> 0: no push, only the reset
     0x834d4  lbu  a0, 0(s4)          the shadow byte of h->partial
     0x834d8  bne  a0, zero, 0x83c5c  -> __asan_report_load8 (HA + 40)
     0x834dc  lbu  a0, 0(s11)
     0x834e0  bne  a0, zero, 0x83c64  -> __asan_report_load8 (HA + 48)
     0x834e4  ld   a1, 40(s7)         partial
     0x834e8  ld   a2, 48(s7)         npartial
     0x834ec  ld   a0, 72(sp)         &h->expected = HA + 64
     0x834f0  jal  ra, 0x85090        list_push (LPSPEC, BASE + AF_fr_list_push)
     0x834f4  lbu  a0, 0(s11)
     0x834f8  bne  a0, zero, 0x83c6c  -> __asan_report_store8 (HA + 48)
     0x834fc  sd   zero, 48(s7)       h->npartial = 0
     0x83500  lb   a0, 0(s6)
     0x83504  bne  a0, zero, 0x83578  -> the 4-byte store check, then back to 0x83508
     0x83508  sw   zero, 56(s7)       h->overlong = 0
     0x8350c  jal  zero, 0x83544

     the ordinary case:
     0x83510  lbu  a2, 0(s4)
     0x83514  bne  a2, zero, 0x83c74  -> __asan_report_load8 (HA + 40)
     0x83518  lbu  a2, 0(s11)
     0x8351c  bne  a2, zero, 0x83c7c  -> __asan_report_store8 (HA + 48)
     0x83520  ld   a2, 40(s7)         partial
     0x83524  addi a3, a0, 1
     0x83528  sd   a3, 48(s7)         h->npartial = npartial + 1
     0x8352c  add  a0, a2, a0         &partial[npartial]
     0x83530  srli a2, a0, 3
     0x83534  add  a2, a2, s5
     0x83538  lb   a2, 0(a2)
     0x8353c  bne  a2, zero, 0x835a0  -> the 1-byte store check, then back to 0x83540
     0x83540  sb   a1, 0(a0)          partial[npartial] = b

     the loop's tail:
     0x83544  addi s9, s9, -1
     0x83548  addi s8, s8, 1
     0x8354c  addi s10, s10, 1
     0x83550  bne  s9, zero, 0x8347c  -> DRB (S k)
     0x83554  jal  zero, 0x835ac      -> DE (A_dr_fed)

   FEEDS is the composition: by induction on the bytes left, dnum s1 - k.  Each turn of the loop is one
   dr_feed_stmt, and the induction stops because DRB carries `Z.of_nat k < dnum s1`, so a DRB at S k with
   S k = dnum s1 is uninhabited. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_feed.v; 66 of its 196 lines of code are new or changed and 6467 lines of the source are left out. *)
(* The INTERFACE of the second half of fuzz_reply's drain TOP segment, so that the two halves are proved in
   parallel.  Nothing is proved here.  The cut and the statement are a Theorem Labs lane's own (a working branch
   ace6b76eb51, W_drain_top.v: DT2 at :492 and dt_tail at :1109), moved here verbatim so a second prover can take
   the tail while b1 proves the growth and the source_of scan:
     half A (b1, W_drain_top.v): DI 0x831f8 -> NOGROW / GROW (realloc #1, 0x83248) -> DT1 0x8326c -> the
       source_of scan (0x83294 .. 0x832e8) -> DT2 0x83314;
     half B (dr_toptail_stmt): DT2 0x83314 (the harness slot g_s[j] found) -> the EINTR round (eintr = 0 at
       0x83338, errno = EINTR through __errno_location 0x8333c / AERRNO, store 0x83358, back to DI 0x831f8 in the
       round state dclr sg), the empty-pending test (0x83364 -> DEND 0x83bbc), or the data round's n (0x833c0 ..
       0x833d0) and __asan_memcpy (0x833f4, AMEMCPY) and the byte loop's setup (-> DRB 0 at 0x8347c).
   DT2 carries every fact the tail reads: the registers (sp, gp, tp, s6 = SA, s9 / s11 / s10 = SA + 32 / 24 / 16,
   s2 = g_s, s1 / s0 = g_s / 8 and (g_s + 4) / 8, s5 = the shadow base, s7 = &g_s[j], s8 = shadow + 12 j,
   a0 = s->buf + s->used, a3 = s->cap - s->used), DI's memory core DMEM, the round's model facts and the budget. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

(* the pure lemmas below need no Section hypothesis; clear them so that lia's proof term mentions none *)
Ltac clr0 := repeat match goal with H : _ |- _ => clear H end.

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
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) ->
  p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
  aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
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
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

Definition A_dr_slot : Z := AF_fr_drain + 0x238.   (* 0x83314, the slot found *)
Definition DT2 (cx : dcx) (sg : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_slot) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 22 = w64 (dxSA cx) /\ getr regs1 25 = w64 (dxSA cx + 32) /\
getr regs1 27 = w64 (dxSA cx + 24) /\ getr regs1 26 = w64 (dxSA cx + 16) /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
getr regs1 23 = w64 (dHA RG cx) /\ getr regs1 24 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) /\
getr regs1 10 = w64 (re_buf e1 + re_used e1) /\ getr regs1 13 = w64 (re_cap e1 - re_used e1) /\
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud MT MMAX cx S1 spent tl.

(* TAIL: DT2 0x83314 -> the EINTR round (back to DI), the empty-pending test (-> DEND), the data round (-> DRB 0).
   dr_top = NOGROW / GROW, then the scan, then this. *)
Definition dr_toptail_stmt : Prop :=
forall cx sg D W1 c1,
DBASE B MT MMAX RG cx -> DT2 cx sg D W1 c1 ->
(drain_b_c.ds_eintr sg = true ->
   forall W2 c2, DI B MT MMAX RG cx (dclr sg) D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, DEND B MT MMAX RG cx sg D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, DRB B MT MMAX RG cx sg D 0 W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

End c.
End b.
End a.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_journal_x W_sites_x W_contract_x W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again; and the scopes
   this file opens, again on top of the ones the imports above open *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---- THE GENERIC CUT (route (b), the ARx drain walk DR_x): DT2_x and dr_toptail_stmt_x are DT2 and
   dr_toptail_stmt over any allocator relation ARx in W_drain_cx_x.v's forms: the entry's ghost list Hp and budget kr
   after cx, the cut's ghost list Hp1 an existential after S1, DMEM_x / dbud_x in place of DMEM / dbud, and the cut
   predicates, DBASE and the post in their _x forms.  The AR texts above are unchanged; W_drain_topb.v proves
   dr_toptail_stmt_x (dr_toptail_x) beside its AR theorem, and W_drain_top.v takes it as dr_top_x's premise. ---- *)
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
Definition DT2_xR (cx : dcx) (Hp : list Z) (kr : nat) (sg : drain_b_c.dstate) (D : list Z) (W1 : world SEGS)
(c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_slot) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 22 = w64 (dxSA cx) /\ getr regs1 25 = w64 (dxSA cx + 32) /\
getr regs1 27 = w64 (dxSA cx + 24) /\ getr regs1 26 = w64 (dxSA cx + 16) /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
getr regs1 23 = w64 (dHA RG cx) /\ getr regs1 24 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) /\
getr regs1 10 = w64 (re_buf e1 + re_used e1) /\ getr regs1 13 = w64 (re_cap e1 - re_used e1) /\
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud_x B MT RP MMAX cx kr ly1 S1 spent tl.

Definition dr_toptail_stmt_xR : Prop :=
forall cx Hp kr sg D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DT2_xR cx Hp kr sg D W1 c1 ->
(drain_b_c.ds_eintr sg = true ->
   forall W2 c2, DI_xR B PST ARx MT RP MMAX RG R cx Hp kr (dclr sg) D W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, DEND_xR B PST ARx MT RP MMAX RG R cx Hp kr sg D W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr sg D 0 W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
End wR.

Definition DT2_x (cx : dcx) (Hp : list Z) (kr : nat) (sg : drain_b_c.dstate) (D : list Z) (W1 : world SEGS)
(c1 : config) : Prop :=
DT2_xR (@wle SEGS) cx Hp kr sg D W1 c1.

Definition dr_toptail_stmt_x : Prop :=
dr_toptail_stmt_xR (@wle SEGS).
End cx.
End bx.
End ax.
