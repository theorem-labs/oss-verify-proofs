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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_gs.v; 75 of its 213 lines of code are new or changed and 740 lines of the source are left out. *)
(* The INTERFACE of the held-key search loop of segment GS of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x83838 .. 0x83874, gesture_seen's loop over s->held, relay.c:104-108 inlined).
   Nothing is proved here: the file fixes the loop head's cut predicate GSL and the statement
   gs_scan_loop_stmt of the loop lemma, so that the loop and the stage around it are proved in parallel.
   The Section header is lib/A/W_drain_cx.v's, plus HV9 / HV12 / HSM (the three cells of aout_at that are
   not in G_DR, which the cut's transport across the stage needs).

   GSL (0x83838) holds after n of the nheld slots were read and none matched.  It carries:
   - the registers dregs_line pins MINUS s6 and s11, which the search clobbers and the two exits restore
     from 56(sp) and 48(sp);
   - the frame this stage set up: 8(sp) = shadow (&s->held), 16(sp) = (&s->held) >> 3, 24(sp) = nheld,
     32(sp) = line + jj, 40(sp) = bg, 72(sp) = shadow (&s->nheld), 80(sp) = s->held, and the slots
     dregs_line / dr_frame already carry;
   - the loop's own four: s3 = the shadow byte of &held[n], s4 = 8 n, s9 = 8 nheld, s11 = jj;
   - the search's progress: no slot below n holds the line's key;
   - the line loop's core at this point (GSB) and what the round still owes (GSfut), both quoted from
     lib/A/W_drain_gs.v unchanged, so that composing the loop with the stage is an application.
   `kf` is the number of slots left (n + kf = |re_keys e1|): re_nheld e1 is existential inside GSL, so the
   loop's induction must be on an external nat.

   gs_scan_loop_stmt takes the SAME three continuations as W_drain_gs.v's gs_scan_stmt, because a match at
   slot n leaves the loop at 0x83930, which restores s6 / s11, reloads bg from 40(sp) and then splits: a
   BEGIN whose key is held returns to DLN (S q), an END whose key is held goes to GF.  No match in any slot
   leaves at 0x83878 and reaches GA.
   The loop body: the shadow check of &held[n] (0x83838), held[n] (0x83848), strlen (0x83850, ASTRLEN; a
   key's strlen reads to its granule end, hence ALLOC_TAIL), and, when the length matches jj, strncmp
   (0x83864, ASTRNCMP) over the jj bytes of the line's key. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx W_drain_gs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).

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
(* the instance's laws *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
(* the walk's globals are .data / .bss cells, never read-only image bytes (the pinned placement decides it) *)
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
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
(* the granule-tail fact is W_alloc_tail.v's alloc_tail, a theorem of AR (not a hypothesis here) *)
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
(* placement of the three cells of aout_at that are not in G_DR (W_drain_cx.v HV9 / HV12 / HSM, as
   W_drain_next.v:266-268 and W_drain_pro.v:74-76 take them) *)
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

Definition GSL (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hloop) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
dr_frame RG cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 ((dxSA cx + 8) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 200) 8 (dxSA cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 56) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 48) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 64) 8 (dxSA cx + 32) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 8) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 (re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 32) 8 (re_buf e1 + Z.of_nat p + Z.of_nat jj) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 bg /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 80) 8 (re_hp e1) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) /\
getr regs1 20 = w64 (8 * Z.of_nat n) /\
getr regs1 25 = w64 (8 * re_nheld e1) /\
getr regs1 27 = w64 (Z.of_nat jj) /\
(n + kf = length (re_keys e1))%nat /\ (0 < kf)%nat /\
(forall i, (i < n)%nat -> nth i (dlH cx s1 p) [] <> firstn jj (dline s1 p q)) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
GSF s1 p q /\
GSB B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

(* The loop, by induction on kf.  It consumes GSL at n and reaches one of the segment's three exits. *)
Definition gs_scan_loop_stmt : Prop :=
forall cx s1 D p q n kf W1 c1,
DBASE B MT MMAX RG cx -> GSL cx s1 D p q n kf W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, GA B MT MMAX RG cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, GF B MT MMAX RG cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x slice D, 2026-10-30): GSL and gs_scan_loop_stmt over W_drain_cx_x.v's
   Section variables (B PST ARx MT RP MMAX RG), the entry's ghost list Hp and budget kr after cx, the cut's own ghost
   list Hp1 an existential after S1 (W_drain_gs.v's GSB_x).  Everything above is unchanged. *)
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
Definition GSL_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_hloop) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
dr_frame RG cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 ((dxSA cx + 8) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 200) 8 (dxSA cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 56) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 48) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 64) 8 (dxSA cx + 32) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 8) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 (re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 32) 8 (re_buf e1 + Z.of_nat p + Z.of_nat jj) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 bg /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 80) 8 (re_hp e1) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) /\
getr regs1 20 = w64 (8 * Z.of_nat n) /\
getr regs1 25 = w64 (8 * re_nheld e1) /\
getr regs1 27 = w64 (Z.of_nat jj) /\
(n + kf = length (re_keys e1))%nat /\ (0 < kf)%nat /\
(forall i, (i < n)%nat -> nth i (dlH cx s1 p) [] <> firstn jj (dline s1 p q)) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
GSF s1 p q /\
GSB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

Definition gs_scan_loop_stmt_xR : Prop :=
forall cx Hp kr s1 D p q n kf W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GSL_xR cx Hp kr s1 D p q n kf W1 c1 ->
(forall W2 c2, DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, GA_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, GF_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
End wR.


Definition GSL_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q n kf : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
GSL_xR (@wle SEGS) cx Hp kr s1 D p q n kf W1 c1.

(* The loop, by induction on kf, over the entry's ghost list Hp and budget kr. *)
Definition gs_scan_loop_stmt_x : Prop :=
gs_scan_loop_stmt_xR (@wle SEGS).

End cx.
End bx.
End ax.
