(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the INTERFACE of the second half of fuzz_reply's drain LINEA segment,
   so that the two halves are proved in parallel.  Nothing is proved here.

   LINEA (W_drain_cx.v dr_linea_stmt) runs DLL (0x836bc) to DLN (S q) or DGS (0x837c8).  It splits at the
   return of send_line:

     half A (W_drain_linea.v, dr_linea):   DLL 0x836bc -> the skip / overlong test (0x836bc .. 0x836f0, to
       DLN) or the length test and the PROGRAM CALL send_line (0x8373c addi a1,a1,1; 0x83740 mv a0,s8;
       0x83744 jal 82734 <send_line>) -> DLS.
     half B (dr_lineb_stmt, below):        DLS 0x83748 -> gesture_seen's classification tests
       (li a1,32 / strrchr 0x83750 -> s9 = last; .str.5 / strncmp "param_gesture" 0x83768; line[13] == ' '
       at 0x83784 with its shadow check 0x83774-0x83780; last != NULL 0x83790; last != line + 13 0x83794;
       .str.6 / strcmp "begin" 0x837a8 -> s3; .str.7 / strcmp "end" 0x837c0) -> DLN (S q) when the line is
       not a gesture, or DGS when it is.

   THE CUT.  DLS (0x83748) is exactly W_drain_cx.v's DGS with the gesture classification removed: the same
   registers (s7 = s->buf + q, s8 = s->buf + p, and dregs_line's pinned set and frame), the same LCORE - the
   line [p, q) HAS been sent (send_line's sl_post is already folded in: g_nout is dlno s1 p + |line| + 1,
   g_capout is send_line_cap, the output journal and aout_at have moved, the held keys have NOT), and the
   same model continuation dsfut.  DGS adds only s9 = the last space, s3 = bg, the kind kd, the key length
   jj and `gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q))`, all of which half B establishes.
   Every fact half B needs is a conjunct here: nothing is implicit. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_lineb_cx.v, with its module paths changed; 66 of its 187 lines of code are new or changed and 19 lines of the source are left out. *)
(* The INTERFACE of the second half of fuzz_reply's drain LINEA segment,
   so that the two halves are proved in parallel.  Nothing is proved here.

   LINEA (W_drain_cx.v dr_linea_stmt) runs DLL (0x836bc) to DLN (S q) or DGS (0x837c8).  It splits at the
   return of send_line:

     half A (W_drain_linea.v, dr_linea):   DLL 0x836bc -> the skip / overlong test (0x836bc .. 0x836f0, to
       DLN) or the length test and the PROGRAM CALL send_line (0x8373c addi a1,a1,1; 0x83740 mv a0,s8;
       0x83744 jal 82734 <send_line>) -> DLS.
     half B (dr_lineb_stmt, below):        DLS 0x83748 -> gesture_seen's classification tests
       (li a1,32 / strrchr 0x83750 -> s9 = last; .str.5 / strncmp "param_gesture" 0x83768; line[13] == ' '
       at 0x83784 with its shadow check 0x83774-0x83780; last != NULL 0x83790; last != line + 13 0x83794;
       .str.6 / strcmp "begin" 0x837a8 -> s3; .str.7 / strcmp "end" 0x837c0) -> DLN (S q) when the line is
       not a gesture, or DGS when it is.

   THE CUT.  DLS (0x83748) is exactly W_drain_cx.v's DGS with the gesture classification removed: the same
   registers (s7 = s->buf + q, s8 = s->buf + p, and dregs_line's pinned set and frame), the same LCORE - the
   line [p, q) HAS been sent (send_line's sl_post is already folded in: g_nout is dlno s1 p + |line| + 1,
   g_capout is send_line_cap, the output journal and aout_at have moved, the held keys have NOT), and the
   same model continuation dsfut.  DGS adds only s9 = the last space, s3 = bg, the kind kd, the key length
   jj and `gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q))`, all of which half B establishes.
   Every fact half B needs is a conjunct here: nothing is implicit. *)
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

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* 0x83748 - 0x830dc = 0x66c: the instruction after `jal 82734 <send_line>`. *)
Definition A_dr_send : Z := AF_fr_drain + 0x66c.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the instance's laws *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
(* the walk's globals are .data / .bss cells, never read-only image bytes (the pinned placement decides it) *)
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
(* the walk's globals, the allocator's statics, errno and the sink's overflow head are never read-only image
   bytes: what a callee's journal may change is disjoint from ROM, so rom_view survives it (W_journal.v
   rom_out / ajournal_gx_rom_view).  The pinned placement decides it by vm_compute. *)
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* the runtime entries drain calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v) *)
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

(* ---- DLS (0x83748): send_line has returned for the line [p, q); gesture_seen's tests are to come. ----
   The existentials and every conjunct are W_drain_cx.v's DGS, minus DGS's gesture data (s9 = the last
   space, s3 = bg, the kind kd, the key length jj and the `gesture ... = Some ...` equation), and at the
   pc of the instruction after the call.  In particular:
   - `dregs_line RG cx regs1 W1 m1` carries sp = dsp0 cx - DRAIN_FRAME, gp / tp, s6 = SA, s11 = SA + 24,
     s2 = g_s, s1 = g_s >> 3, s0 = (g_s + 4) >> 3, s5 = SHADOW_OFF, the 13 saved registers and all of
     dr_frame's constants, and the five frame slots DLL carries (192 / 200 / 56 / 48 / 64).  Those are the
     callee-saved registers and frame bytes send_line does not touch (its journal's window is its own
     frame, below drain's), so half A proves them, and half B may read them as given.
   - `LCORE` contains DMEM (the journal from drain's entry at G_DR with send_line's journal composed in,
     rom_view, apres_kept, frames, dr_frame, the relay entry's bytes at SA and its 56 writable bytes,
     aentry_okx - which gives the buffer block (re_buf e1, re_cap e1) and the held keys' blocks -, the
     harness source at HA, the other three slots of g_s kept, aout_at after the send and the blocks'
     permutation), DLINK, DSAME, DHIST, RSTART and dbud.
   - The line's geometry: dbound, p <= q < |dW s1|, the NUL at q, no NUL inside, s->skip was 0 and the
     line is not overlong.  With DLINK's `bzs (re_U e1) = dW s1` these give the bytes of the line and its
     terminating NUL, which is what strrchr / strncmp / strcmp read. *)
Definition DLS (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_send) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
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

(* ---- LINEB: DLS 0x83748 -> gesture_seen's classification tests -> DLN (S q) or DGS 0x837c8. ----
   The calls are strrchr (0x83750, ASTRRCHR), strncmp (0x83768, ASTRNCMP) and strcmp twice (0x837a8 and
   0x837c0, ASTRCMP); the only shadow check is of s->buf + p + 13 (0x83774 .. 0x83780, whose report arm at
   0x839e4 is not taken because the byte lies in the buffer block).  No store, no allocation: the journal,
   aout_at and the meter are carried through unchanged, and on the DLN arm `gesture (dline s1 p q) = None`
   turns LCORE's held-key clause (upds .. kl) into DLC at S q. *)
Definition dr_lineb_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE B MT MMAX RG cx -> DLS cx s1 D p q W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, DGS B MT MMAX RG cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

End c.
End b.
End a.

(* ---- THE GENERIC INTERFACE (DR_x, route (b), step 3): the cut DLS and LINEB's statement over any allocator relation
   ARx, at the room texts of lib/A/W_drain_cx_x.v.  The AR text above is unchanged; this part sits after it, so the
   AR Sections never see the generic kit.  DLS_x is DLS with W_drain_cx_x.v's threading: the entry's ghost list Hp
   and budget kr after cx, the cut's own ghost list Hp1 an existential right after S1, and LCORE_x for LCORE.
   dr_lineb_stmt_x is dr_lineb_stmt over DBASE_x / DLS_x / DLN_x / DGS_x / dPOST_x.  Nothing is proved here. ---- *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
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
Definition DLS_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_send) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
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


(* DLS over ARx: W_drain_cx_x.v's DGS_x minus the gesture data, at the pc after the call *)
Definition DLS_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
DLS_xR (@wle SEGS) cx Hp kr s1 D p q W1 c1.

(* LINEB over ARx: DLS_x 0x83748 -> gesture_seen's classification tests -> DLN_x (S q) or DGS_x 0x837c8 *)
Definition dr_lineb_stmt_x : Prop :=
dr_lineb_stmt_xR (@wle SEGS).

End cx.
End bx.
End ax.
