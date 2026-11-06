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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_gs.v, with its module paths changed; 58 of its 129 lines of code are new or changed and 807 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10 (an internal work row): Section cx below adds the ARx-generic twins DLS_x / dr_lineb_stmt_x
   (lib/B/W_drain_cx_x.v's forms: the entry's ghost list Hp and budget kr after cx, LCORE -> LCORE_x with the cut's
   Hp1); Section c is unchanged. *)
(* Modified by Theorem Labs, 2026-10: the image-B (asan-ubsan) twin of lib/A/W_drain_lineb_cx.v
   (a working branch e6b5f95b285): the cut that splits drain's LINEA segment at the return of send_line.
   Nothing is proved here.

   LINEA (lib/B/W_drain_cx.v dr_linea_stmt) runs DLL (0x8399c) to DLN (S q) at 0x839d4 or DGS at 0x83aa4.
   It splits at the return of send_line:

     half A (lib/B/W_drain_linea.v):  DLL 0x8399c -> the shadow check of s->skip (0x8399c .. 0x839b0, report
       arm 0x83db4), the skip / overlong test (0x839b4 .. 0x839c4) and the skip arm (0x839c8 .. 0x839d0,
       report arm 0x83dc4) to DLN at 0x839d4; or the PROGRAM CALL send_line (0x839e8 addi a1,a1,1;
       0x839ec mv a0,s8; 0x839f0 jal 82854 <send_line>) -> DLS.
     half B (dr_lineb_stmt, below):   DLS 0x839f4 -> gesture_seen's classification tests (li a1,32 / strrchr
       0x839fc -> s3 = last; .str.6 / strncmp "param_gesture" 0x83a14; the UBSan traps at 0x83a1c (line
       non-null) and 0x83a24 (line < -13); the shadow check of line + 13 (0x83a28 .. 0x83a3c, report arm
       0x83dd4); line[13] == ' ' at 0x83a54; last != NULL 0x83a58; last != line + 13 0x83a5c; the UBSan trap
       at 0x83a64 (last != -1); .str.7 / strcmp "begin" 0x83a78 -> s9; .str.8 / strcmp "end" 0x83a9c) ->
       DLN (S q) when the line is not a gesture, or DGS when it is.

   THE CUT.  DLS (0x839f4) is lib/B/W_drain_cx.v's DGS with the gesture classification removed: the same
   registers (s7 = s->buf + q, s8 = s->buf + p and dregs_line's pinned set and frame), the same LCORE - the
   line [p, q) HAS been sent (send_line's sl_post is already folded in: g_nout is dlno s1 p + |line| + 1,
   g_capout is send_line_cap, the output journal and aout_at have moved, the held keys have NOT), and the
   same model continuation dsfut.  DGS adds only s3 = the last space, s10 = last + 1, s9 = bg, the kind kd,
   the key length jj and `gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q))`, all of which half B
   establishes.  Every fact half B needs is a conjunct here: nothing is implicit. *)
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
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_drain_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_contract_x W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* 0x839f4 - 0x83278 = 0x77c: the instruction after `jal 82854 <send_line>`. *)
Definition A_dr_send : Z := AF_fr_drain + 0x77c.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.

(* ---- DLS (0x839f4): send_line has returned for the line [p, q); gesture_seen's tests are to come. ----
   The existentials and every conjunct are lib/B/W_drain_cx.v's DGS, minus DGS's gesture data (s3 = the
   last space, s10 = last + 1, s9 = bg, the kind kd, the key length jj and the `gesture ... = Some ...`
   equation), and at the pc of the instruction after the call.  `dregs_line RG cx regs1 W1 m1` carries
   sp, gp / tp, s5 = SA, s4 = SA + 16, s6 = SA + 24, s11 = SA + 32, s0 = g_s, s1 = g_s >> 3,
   s2 = (g_s + 4) >> 3 and dr_frame (its constants, including 240(sp) = SHADOW_OFF and 208(sp) = SA + 8, and
   the 13 saved registers): callee-saved registers and frame bytes send_line does not touch, so half A
   proves them and half B reads them as given. *)
Definition DLS (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_send) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
dbound s1 p /\ (p <= q < length (dW s1))%nat /\ nth_error (dW s1) q = Some 0 /\
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) /\
dskp s1 p = false /\ (q - p <= LINE_LIMIT)%nat /\
(* the line is sent; the held keys are not yet updated with it *)
LCORE B MT MMAX RG cx s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (drlq s1 (S q)) jb o ha ks tl.

(* ---- LINEB: DLS 0x839f4 -> gesture_seen's classification tests -> DLN (S q) or DGS 0x83aa4. ---- *)
Definition dr_lineb_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE B MT MMAX RG cx -> DLS cx s1 D p q W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, DGS B MT MMAX RG cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

End c.

(* ---- The ARx-generic twins (lib/B/W_drain_cx_x.v's Section c variables), at the room texts: the entry's ghost list
   Hp and budget kr follow cx, the cut's ghost list Hp1 is an existential after S1, LCORE -> LCORE_x. ---- *)
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

Definition DLS_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS)
(c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_send) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
dbound s1 p /\ (p <= q < length (dW s1))%nat /\ nth_error (dW s1) q = Some 0 /\
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) /\
dskp s1 p = false /\ (q - p <= LINE_LIMIT)%nat /\
(* the line is sent; the held keys are not yet updated with it *)
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])
  (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (drlq s1 (S q)) jb o ha ks tl.

Definition dr_lineb_stmt_xR : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DLS_xR cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, DGS_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
End wR.

(* DLS (above), over ARx *)
Definition DLS_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS)
(c1 : config) : Prop :=
DLS_xR (@wle SEGS) cx Hp kr s1 D p q W1 c1.

(* dr_lineb_stmt (above), over ARx *)
Definition dr_lineb_stmt_x : Prop :=
dr_lineb_stmt_xR (@wle SEGS).
End cx.
End b.
End a.
