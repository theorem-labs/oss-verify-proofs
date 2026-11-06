(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane, a Theorem Labs lane's dr_sa_align row): pb_drain_of loses the premise dr_sa_align; the kit's dr_spec states SA mod 8 = 0. *)
(* Modified by Theorem Labs, 2026-10: pb_drain_of, the published assembly of the image-B
   (fuzz_reply.asan-ubsan) walk of fuzz_reply's drain: ONE application of lib/B/W_drain.v's dr_assemble.  The
   image-independent compositions are proved on B's cuts and applied here, each by
   `assert (X : <stmt>) by (eapply <thm>; eassumption)` (W7's style on A, lib/A/W_drain_pb.v):
     dr_feeds  lib/B/W_drain_feeds.v   the byte loop, by induction on dnum s1 - k
     dr_lines  lib/B/W_drain_lines.v   the line loop, by induction on |dW s1| - p
     dr_outer  lib/B/W_drain_outer.v   the outer loop, by induction on dneed s1
     dr_all    lib/B/W_drain_all.v     the prologue and the outer loop give dr_spec
     dr_top_of lib/B/W_drain_tophead.v TOP from its head and tail halves, split at 0x83524
   and the walked stages proved so far, applied the same way over the Section hypotheses of
   lib/B/W_drain_cx.v (which therefore become pb_drain_of's own premises, those a stage uses):
     dr_feed   lib/B/W_drain_feed.v    FEED 0x836fc .. 0x8389c -> DRB (S k) / DE  (a Theorem Labs lane,
                                       a working branch f02afb993d6)
     dr_pro    lib/B/W_drain_pro.v     PRO  0x83278 .. 0x833bc -> DI           (a Theorem Labs lane,
                                       a working branch 814e1b83f19)
     dr_epi    lib/B/W_drain_epi.v     EPI  0x83fc8 .. 0x84000                 (a Theorem Labs lane,
     dr_end    lib/B/W_drain_epi.v     END  0x83e94 .. 0x83fc4                  a working branch 1072b214260)
     pb_dr_gs  lib/B/W_drain_gs_top.v  GS   0x83aa4 .. 0x83d98 -> DLN (S q)    (a Theorem Labs lane,
                                       a working branch 63e7043187e)
     dr_next   lib/B/W_drain_next.v    NEXT 0x839d4 .. -> DLL p q / DLR p     (a Theorem Labs lane,
     dr_rest   lib/B/W_drain_rest.v    REST 0x83e34 .. 0x83e90 -> DI          a working branch 6670c18e144)
     dr_linea  lib/B/W_drain_linea.v   LINEA 0x8399c .. 0x839f4 -> DLN (S q) / DLS (a Theorem Labs lane,
     dr_lineb  lib/B/W_drain_lineb.v   DLS  0x839f4 .. 0x83aa0 -> DLN (S q) / DGS   a working branch
                                       81eebc35a0b); dr_linea takes dr_lineb as its LINEB.  Both are Required, not
                                       Imported: dr_linea's W_drain_tr.v and the GS stage's W_drain_gs_aux.v define
                                       some of the same names, so their names are used qualified here.
     dr_toptail lib/B/W_drain_topb.v   TOP tail 0x83524 .. 0x836f8 -> DI (EINTR) / DEND / DRB 0 (a Theorem Labs lane,
                                       a working branch 01c09263227); Required, not Imported.
     dr_drop   lib/B/W_drain_drop.v    DROP 0x838a0 .. 0x83998 -> DLL 0 q / DLR 0, list_drop called at 0x83914 through
                                       W_list_drop.v pb_list_drop_ro_c (a Theorem Labs lane, a working branch
                                       d76927ef99b); Required, not Imported.
     TOP head, by dr_tophead_of from dt_nogrow and dt_grow (lib/B/W_drain_tophead.v; dt_grow is the growth arm,
               realloc #1, 0x833ec .. 0x83434) and dt_scan_of over dt_scan_entry / dt_scan_step
               (lib/B/W_drain_topscan.v, this lane's scan sub-walk), so TOP's head is proved in full.
   The walk owes nothing more: pb_drain_of has no statement premise (dr_sa_align, the entry address's
   8-alignment, is closed: the kit's dr_spec states it, W_drain_cx.v FINDING 1).
   Print Assumptions pb_drain_of: the engine's primitives and functional_extensionality_dep only. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_drain_pb.v, with its module paths and module names changed; 74 of its 188 lines of code are new or changed and 326 lines of the source are left out. *)
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
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx.
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

Definition A_dr_slot : Z := AF_fr_drain + 0x2ac.

Lemma P0_dr_slot : fr_B0 + A_dr_slot = 0x83524.
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

Definition DT2 (cx : dcx) (sg : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_slot) regs1 m1 md1 /\
dregs_top RG cx regs1 /\
getr regs1 23 = w64 (dHA RG cx) /\ getr regs1 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) /\
getr regs1 10 = w64 (re_buf e1 + re_used e1) /\ getr regs1 13 = w64 (re_cap e1 - re_used e1) /\
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
dinband (re_buf e1) (re_cap e1) /\
DLINK sg e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sg D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u sg) (drain_b_c.ds_skip sg) (drain_b_c.ds_ref sg) /\
4096 <= drain_b_c.ds_cap sg - ulen sg /\
dlater cx sg jb a tl /\ dbud MT MMAX cx S1 spent tl.

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

(* ---- THE GENERIC CUT (an internal work row, the ARx drain walk DR_x; the image-B twin of lib/A/W_drain_topb_cx.v's Section cx,
   a working branch af2f55b6679): DT2_x and dr_toptail_stmt_x are DT2 and dr_toptail_stmt above over any
   allocator relation ARx, in lib/B/W_drain_cx_x.v's forms: the entry's ghost list Hp and budget kr after cx, the cut's
   ghost list Hp1 an existential after S1, DMEM_x / dbud_x in place of DMEM / dbud, and DBASE, the cut predicates and
   the post in their _x forms.  The AR texts above are unchanged; they are compiled before the Requires below, so
   nothing the generic kit loads can reach them.  W_drain_topb.v proves dr_toptail_stmt_x (dr_toptail_x) beside its AR
   theorem; W_drain_tophead.v's dr_top_of_x and W_drain_topscan.v's dr_top_x take it as a premise.  No bridge to the AR
   texts: the stack bound DRAIN_STK_x of the _x pre makes the two forms incomparable. ---- *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_journal_x W_sites_x W_contract_x W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* the zify flag this file's AR text runs with (its own setting above), whatever the Requires above leave *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

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
dregs_top RG cx regs1 /\
getr regs1 23 = w64 (dHA RG cx) /\ getr regs1 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) /\
getr regs1 10 = w64 (re_buf e1 + re_used e1) /\ getr regs1 13 = w64 (re_cap e1 - re_used e1) /\
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
dinband (re_buf e1) (re_cap e1) /\
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
End b.
End a.
