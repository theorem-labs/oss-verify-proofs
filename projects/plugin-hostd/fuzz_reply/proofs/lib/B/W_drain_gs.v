(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the INTERFACE of segment GS of the ASan+UBSan walk (image B,
   fuzz_reply.asan-ubsan) of fuzz_reply's drain -- gesture_seen's held-array search and update
   (relay.c:89-121, inlined), 0x83aa4 .. 0x83d98, and the composition of its three stages.
   The statement is lib/B/W_drain_cx.v's dr_gs_stmt (DGS 0x83aa4 -> DLN 0x839d4 at S q) and the Section
   header below is that file's, verbatim.  Nothing of the three stages is proved here.
   Split and statement names mirror image A's lib/A/W_drain_gs.v (a working branch ed12337f74d,
   gs_scan_stmt :863, gs_add_stmt :871, gs_free_stmt :877, dr_gs_of :884); every pc, register and frame
   slot below is read from image B's own listing (fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) 0x83aa4 .. 0x83d98) and from
   lib/B/W_drain_cx.v's dregs_line (:769) and dr_frame (:537).  The structure of the walk (the cut pcs,
   the case split and the symbolic states) agrees with the closed old-framework B walk of this stage,
   a working branch 89040c52421 lib/B/Prog/drain_p_seen_scan.v (entry 0x83aa4, add path 0x83ba0,
   loop head 0x83b34), drain_p_seen_scan_body.v, drain_p_seen_strncmp.v, drain_p_seen_add_{a,b,b2}.v and
   drain_p_seen_drop.v; those theorems are stated over SR rsegs / a_call_pre and do NOT transport, so
   only their geometry is used.

   THE THREE STAGES (B pc = 0x83278 + the offset each definition carries; fr_B0 = 0x82344,
   AF_fr_drain = 0xf34, so 0x83278 = fr_B0 + AF_fr_drain):

     gs_scan  DGS 0x83aa4 (+0x82c) .. GA 0x83ba0 (+0x928) / GF 0x83cb4 (+0xa3c) / DLN 0x839d4
              0x83aa4 .. 0x83ae0 write the eight scratch slots the two arms read (24(sp) = bg,
              16(sp) = shadow &e->nheld, 192(sp) = the key's length jj = s3 - s8, 96(sp) = (SA + 40) / 8,
              112(sp) = e->nheld) and branch on `blez nheld` straight to the join 0x83ba0; otherwise
              0x83ae4 .. 0x83b30 seat the loop (0(sp) = shadow &e->hp, s6 = e->hp, s4 = 0, s3 = nheld,
              s9 = snez s6, 168(sp) = (s6 aligned and non-null), 160(sp) = 8 nheld) and the search loop
              0x83b34 .. 0x83b9c (A_dr_hloop) compares every held key: strlen 0x83b6c against 192(sp),
              then strncmp 0x83b84 against the line at s8.  Its three exits:
                not found (loop exhausted, `bne 160(sp),s4` at 0x83b9c falls through) -> GA, the same
                  join the nheld <= 0 branch takes;
                found and the gesture is an end (0x83cac `ld 24(sp)`, 0x83cb0 `beqz` not taken) -> GF;
                found and the gesture is a begin (0x83cb0 taken) -> 0x83d9c, which restores s5 / s6 / s4 /
                  s11 and leaves at `bnez s3, 0x839d4` -> DLN.  The NOT-TAKEN edge of that bnez
                  (`j 0x83bbc`, into the add arm past its two tests) is DEAD: s3 = nheld - n and the
                  search found the key at slot n < nheld, so s3 >= 1.  Only the loop's own invariant
                  refutes it, which is why the begin-held tail belongs to gs_scan and GF is placed after
                  the bg test (0x83cb4), exactly as image A's GF sits after A's bg test at 0x8393c.
              Traps: 0x83b38 PTR_BLTU, 0x83b44 NULL_XOR (folded, the atom s9), 0x83b4c NONNULL on the
              one-time flag 168(sp).  Shadow side-exits: 0x83de0, 0x840e4, 0x84078.

     gs_add   GA 0x83ba0 .. DLN 0x839d4
              0x83ba0 .. 0x83ba8 restore s5 = SA, s6 = SA + 24, s4 = SA + 16 from the frame, then the two
              tests decide: 0x83bb0 `bnez 24(sp)` (an end whose key is not held) and 0x83bb8
              `bltz 112(sp)` (dead: re_nheld e = Z.of_nat (length (re_keys e)) >= 0) leave for DLN; a
              begin not held runs the add proper 0x83bbc .. 0x83ca8: realloc #2 0x83be8 for
              8 (nheld + 1) bytes (its failure arm 0x83bec -> DLN), e->held = res, strndup 0x83c08 of
              (s8, 192(sp)) (failure 0x83c0c -> DLN), e->nheld = nheld + 1 at 0x83c5c and
              held[nheld] = copy at 0x83ca4, then `j 0x839d4`.
              Traps: 0x83bc4 and 0x83c28 ADDW1, 0x83c60 NULL_BEQ, 0x83c74 PTR_SOVF, 0x83c78 NONNULL,
              0x83c80 ALIGN8.  Shadow side-exits: 0x840ec, 0x840f4, 0x83df0, 0x840fc, 0x83e04, 0x84104.

     gs_free  GF 0x83cb4 .. DLN 0x839d4
              an end whose key is held at slot n: free #2 0x83ccc of held[n] (s10 = &held[n], s4 = 8 n,
              s5 = its shadow byte, s6 = e->hp), then e->nheld = nheld - 1 at 0x83d1c and
              held[n] = held[nheld - 1] at 0x83d90 from the RE-READ e->held (0x83ce8, after the free),
              then `j 0x839d4`.
              Traps: 0x83cbc and 0x83d5c PTR_NOT, 0x83cfc DECW, 0x83d20 NULL_BEQ, 0x83d34 PTR_SOVF,
              0x83d38 NONNULL, 0x83d40 and 0x83d68 ALIGN8.  Shadow side-exits: 0x8410c, 0x84114,
              0x83e14, 0x83e24, 0x8411c, 0x84120.
   3 + 6 + 8 = the 17 trap sites W_drain_cx.v's census lists for stage GS (rows 0x83b38 .. 0x83d68); all
   are shapes of the trap kit a working branch 6c73ae99620 (lib/B/W_traps.v).

   REGISTERS AT THE TWO CUTS.  The GS stage CLOBBERS s5 / s4 / s6 / s11 (x21 / x20 / x22 / x27), the four
   SA-derived pins of W_drain_cx.v's dregs_line, and restores them from the frame only on the way out
   (0x83ba0 .. 0x83ba8, 0x83b94, 0x83c94 .. 0x83c9c, 0x83cb8, 0x83d80 .. 0x83d94, 0x83d9c .. 0x83da8), so
   NEITHER cut can carry dregs_line -- where image A's GA / GF do.  dregs_gs below is dregs_line minus
   those four pins (sp, gp, tp, s0 = g_s, s1 = g_s / 8, s2 = (g_s + 4) / 8 and dr_frame survive the whole
   stage, the calls included); each cut then names what is live in the four:
     GA  s11 = SA + 32 (0x83b94 on the loop path, untouched on the nheld <= 0 path), s7 = buf + q,
         s8 = buf + p; s5 / s4 / s6 are DEAD at 0x83ba0 (the three loads overwrite them) and s3 / s9 /
         s10 differ between the two incoming edges and are dead as well, so none is named.
     GF  s6 = e->hp, s4 = 8 n, s10 = e->hp + 8 n, s5 = (e->hp + 8 n) / 8 + SHADOW_OFF, s7 = buf + q,
         s8 = buf + p; s11 still holds held[n] at 0x83cb4 and is restored at 0x83cb8, so it is not named.
   The scratch frame slots each arm reads are named by the cut that hands them over (dr_frame covers only
   the 23 one-time slots; 0, 16, 24, 96, 112, 160, 168 and 192 are scratch).  dsp0 cx - DRAIN_FRAME is sp
   inside drain's frame, so slot k is at (dsp0 cx - DRAIN_FRAME + k). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx.
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

(* The segment's own program counters, read from fuzz_reply.asan-ubsan's listing. *)
Definition A_dr_hloop : Z := AF_fr_drain + 0x8bc.   (* 0x83b34, the held-key search loop's head *)
Definition A_dr_add : Z := AF_fr_drain + 0x928.     (* 0x83ba0, the search is over: the key is not held *)
Definition A_dr_free : Z := AF_fr_drain + 0xa3c.    (* 0x83cb4, an end whose key is held at slot n *)

Lemma P0_dr_hloop : fr_B0 + A_dr_hloop = 0x83b34.
Proof. reflexivity. Qed.
Lemma P0_dr_add : fr_B0 + A_dr_add = 0x83ba0.
Proof. reflexivity. Qed.
Lemma P0_dr_free : fr_B0 + A_dr_free = 0x83cb4.
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

(* ---- The line that gesture_seen was called on, and the line loop's core at that point: exactly the
   geometry and the LCORE that W_drain_cx.v's DGS (:828) carries, so that the two intermediate cut
   predicates and the three stage statements quote it unchanged and composing them is an application. ---- *)
Definition GSF (s1 : drain_b_c.dstate) (p q : nat) : Prop :=
dbound s1 p /\ (p <= q < length (dW s1))%nat /\ nth_error (dW s1) q = Some 0 /\
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) /\
dskp s1 p = false /\ (q - p <= LINE_LIMIT)%nat.

Definition GSno (cx : dcx) (s1 : drain_b_c.dstate) (p q : nat) : Z :=
dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1.
Definition GSoc (cx : dcx) (s1 : drain_b_c.dstate) (p q : nat) : Z :=
send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
  (Z.of_nat (length (dline s1 p q)) + 1).

Definition GSB (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE B MT MMAX RG cx s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q)
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

Definition GSfut (cx : dcx) (s1 : drain_b_c.dstate) (p q : nat)
(a : drain_b_c.dadr) (jb : nat) (o ha : dadrF) (ks : list dadrF) (tl : dtrace) : Prop :=
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (GSno cx s1 p q) (GSoc cx s1 p q) (drlq s1 (S q)) jb o ha ks tl.

(* ---- The registers of W_drain_cx.v's dregs_line (:769) that the GS stage never writes: sp, gp, tp,
   s0 = g_s, s1 = g_s / 8, s2 = (g_s + 4) / 8, and drain's one-time frame.  The stage's own values of
   s5 / s4 / s6 / s11 are named by the cut that has them live. ---- *)
Definition dregs_gs (cx : dcx) (regs1 : bvmap 5 word) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 8 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 18 = w64 ((rg_s RG + 4) / 8) /\
dr_frame RG cx W1 m1.

(* ---- GA (0x83ba0): the search is over and the key is NOT held -- the join of the `blez nheld` branch
   of 0x83ae0 and of the exhausted loop.  s11 = SA + 32 and s7 / s8 are the line's ends; 0x83ba0 .. 0x83ba8
   restore s5 / s6 / s4 from the frame, and the two tests at 0x83bac and 0x83bb8 decide: an end (24(sp)
   non-zero) returns, a begin adds the key.  112(sp) = e->nheld, 192(sp) = the key's length,
   96(sp) = (SA + 40) / 8 and 16(sp) = the shadow byte of &e->nheld are what the add arm reads. ---- *)
Definition GA (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_add) regs1 m1 md1 /\
dregs_gs cx regs1 W1 m1 /\
getr regs1 27 = w64 (dxSA cx + 32) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 bg /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 96) 8 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 112) 8 (re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None /\
GSF s1 p q /\
GSB cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

(* ---- GF (0x83cb4): an end whose key is held at slot n, after the bg test of 0x83cb0.  s6 = e->hp,
   s4 = 8 n, s10 = &e->held[n], s5 = that slot's shadow byte; 0(sp) and 16(sp) are the shadow bytes of
   &e->hp and &e->nheld, which the arm re-reads after the free. ---- *)
Definition GF (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (jj n : nat),
c1 = cfg_at SEGS (BASE + A_dr_free) regs1 m1 md1 /\
dregs_gs cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 22 = w64 (re_hp e1) /\
getr regs1 20 = w64 (8 * Z.of_nat n) /\
getr regs1 26 = w64 (re_hp e1 + 8 * Z.of_nat n) /\
getr regs1 21 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
(n < length (re_keys e1))%nat /\
gesture (dline s1 p q) = Some (GEnd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = Some n /\
GSF s1 p q /\
GSB cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

(* ---- The three stages. ---- *)

Definition gs_scan_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE B MT MMAX RG cx -> DGS B MT MMAX RG cx s1 D p q W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, GA cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, GF cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Definition gs_add_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE B MT MMAX RG cx -> GA cx s1 D p q W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Definition gs_free_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE B MT MMAX RG cx -> GF cx s1 D p q W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

(* ---- The segment: the search, then whichever of the two updates the search chose. ---- *)
Theorem dr_gs_of : gs_scan_stmt -> gs_add_stmt -> gs_free_stmt -> dr_gs_stmt B MT MMAX RG.
Proof.
intros SCAN ADD FREE cx s1 D p q W1 c1 HB HGS HN.
apply (SCAN cx s1 D p q W1 c1 HB HGS HN).
- intros W2 c2 HGA. exact (ADD cx s1 D p q W2 c2 HB HGA HN).
- intros W2 c2 HGF. exact (FREE cx s1 D p q W2 c2 HB HGF HN).
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (image B's DR_x slice D, 2026-10-30; the B twin of lib/A/W_drain_gs.v's
   Sections ax / bx / rk / cx at a working branch 50623273289): the gs stage over lib/B/W_drain_cx_x.v's
   Section variables (B PST ARx MT RP MMAX RG), with the entry's ghost list Hp and budget kr after cx and a cut's own
   ghost list Hp1 after S1, as W_drain_cx_x.v threads them.  Everything above this line is unchanged, so every AR
   statement of this file keeps its text and its Section list; the twin only adds names (the AR name with _x).  The
   AR-free names of Section c above (GSF, GSno, GSoc, GSfut, dregs_gs, A_dr_add / A_dr_free) are CITED.
   - The cut predicates GA_x / GF_x and the stage statements gs_scan_stmt_x / gs_add_stmt_x / gs_free_stmt_x are the
     AR texts above (image B's registers and scratch frame slots) with W_drain_cx_x.v's twins (DBASE_x, DGS_x, DLN_x,
     dPOST_x, LCORE_x); dr_gs_of_x composes them into W_drain_cx_x.v:762 dr_gs_stmt_x, unchanged.
   - The journal's open / close at an allocator site over W_journal_x.ajournal_gx_x (gs_gx_open_x / gs_gx_close_x,
     the twins of lib/B/W_drain_gs_aux.v's gs_gx_open / gs_gx_close).
   - The room round's bookkeeping at a call (W_drain_cx_x.v dbud_x: the room rp_RM at MT_rk's charge of the requests
     still owed plus kr, and the live counts plus their peak tr_peakP + 2): the head request's room and count premise
     (gs_rm_take, gs_cnt_call) and the counts after it for the three request kinds (gs_cnt_malloc, gs_cnt_realloc,
     gs_cnt_free). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_cx W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* the room round's bookkeeping (Section rk: gs_rk_app, gs_rk_nonneg, gs_rm_take, gs_cnt_call / step / malloc / realloc / free):
   moved to lib/B/W_drain_room_x.v, the drain stages' one text (twin of lib/A/W_drain_room_x.v); re-exported so every name this
   file's users cite stays reachable from here *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Export W_drain_room_x.

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.



(* ---- The line loop's core at gesture_seen's entry (GSB over LCORE_x). ---- *)
Definition GSB_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])
  (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q)
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

(* ---- GA (0x83ba0), the cut's ghost list Hp1 an existential after S1. ---- *)
Definition GA_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_add) regs1 m1 md1 /\
dregs_gs RG cx regs1 W1 m1 /\
getr regs1 27 = w64 (dxSA cx + 32) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 bg /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 96) 8 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 112) 8 (re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None /\
GSF s1 p q /\
GSB_x cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

(* ---- GF (0x83cb4), the cut's ghost list Hp1 an existential after S1. ---- *)
Definition GF_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (jj n : nat),
c1 = cfg_at SEGS (BASE + A_dr_free) regs1 m1 md1 /\
dregs_gs RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 22 = w64 (re_hp e1) /\
getr regs1 20 = w64 (8 * Z.of_nat n) /\
getr regs1 26 = w64 (re_hp e1 + 8 * Z.of_nat n) /\
getr regs1 21 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
(n < length (re_keys e1))%nat /\
gesture (dline s1 p q) = Some (GEnd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = Some n /\
GSF s1 p q /\
GSB_x cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

(* ---- The three stages, over the entry's ghost list Hp and budget kr. ---- *)
Definition gs_scan_stmt_x : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DGS_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
(forall W2 c2, GA_x cx Hp kr s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
(forall W2 c2, GF_x cx Hp kr s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).

Definition gs_add_stmt_x : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GA_x cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).

Definition gs_free_stmt_x : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GF_x cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).


(* ==== route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0; the wave-2 commit (1) form): the R twins of this section's journal facts, gs
   carriers and stage statements.  Each X_xR is X_x with ajournal_gx_x -> ajournal_gx_xR .. R, ajournal_x ->
   ajournal_xR .. R, SRr SEGS -> SRrG SEGS R and each carrier name of W_drain_cx_x.v / this file -> its R twin (at the
   nested order: the strict's section variables, then R); the strict text above is untouched.  DBASE_x has no twin. ==== *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.

Lemma gs_gx_open_xR : forall G STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc (W : world SEGS) memc mdc k,
@ajournal_gx_xR _ SK SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
exists memS, 0 <= STK /\ gagree G (w_H W0) mem memS /\
  ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memc mdc k.
Proof.
intros G STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k (HSTK & _ & (memS & HJi & Hag) & _).
rewrite !Z.add_0_r in HJi. exists memS. split; [exact HSTK|]. split; [exact Hag | exact HJi].
Qed.

Lemma gs_gx_close_xR : forall G STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k2 memS,
0 <= STK -> gagree G (w_H W0) mem memS ->
ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 memS md own ly2 S2 Hp2 W2 mem2 md2 k2 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2.
Proof.
intros G STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2 memS HSTK Hag HJ.
apply (@ajournal_gx_pack_xR _ SK SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2 memS);
  [exact HSTK | lia | rewrite !Z.add_0_r; exact HJ | exact Hag | intros a Ha; lia].
Qed.

(* R twin of GSB_x *)
Definition GSB_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])
  (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q)
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

(* R twin of GA_x *)
Definition GA_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_add) regs1 m1 md1 /\
dregs_gs RG cx regs1 W1 m1 /\
getr regs1 27 = w64 (dxSA cx + 32) /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 bg /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 96) 8 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 112) 8 (re_nheld e1) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None /\
GSF s1 p q /\
GSB_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

(* R twin of GF_x *)
Definition GF_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (jj n : nat),
c1 = cfg_at SEGS (BASE + A_dr_free) regs1 m1 md1 /\
dregs_gs RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 22 = w64 (re_hp e1) /\
getr regs1 20 = w64 (8 * Z.of_nat n) /\
getr regs1 26 = w64 (re_hp e1 + 8 * Z.of_nat n) /\
getr regs1 21 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
(n < length (re_keys e1))%nat /\
gesture (dline s1 p q) = Some (GEnd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = Some n /\
GSF s1 p q /\
GSB_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

(* R twins of the three stage statements *)
Definition gs_scan_stmt_xR : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DGS_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, GA_xR cx Hp kr s1 D p q W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, GF_xR cx Hp kr s1 D p q W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).

Definition gs_add_stmt_xR : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GA_xR cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).

Definition gs_free_stmt_xR : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GF_xR cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).

(* R twin of dr_gs_of_x, same proof *)
Theorem dr_gs_of_xR : gs_scan_stmt_xR -> gs_add_stmt_xR -> gs_free_stmt_xR -> dr_gs_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros SCAN ADD FREE cx Hp kr s1 D p q W1 c1 HB HGS HN.
apply (SCAN cx Hp kr s1 D p q W1 c1 HB HGS HN).
- intros W2 c2 HGA. exact (ADD cx Hp kr s1 D p q W2 c2 HB HGA HN).
- intros W2 c2 HGF. exact (FREE cx Hp kr s1 D p q W2 c2 HB HGF HN).
Qed.

End wR.

(* commit (2): each strict lemma below is its R twin at R := wle (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0) *)
Local Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* ---- Opening and closing the walk's journal at an allocator site (gs_gx_open / gs_gx_close of
   W_drain_gs_aux.v over ARx): the W_journal_x.v rules (<rule>_c_x) are stated over ajournal_x; at XO = 0 the
   walk's ajournal_gx_x is ajournal_x at the overlaid start memory memS, which the rules leave alone. ---- *)
Lemma gs_gx_open_x : forall G STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc (W : world SEGS) memc mdc k,
@ajournal_gx_x _ SK SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
exists memS, 0 <= STK /\ gagree G (w_H W0) mem memS /\
  ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memc mdc k.
Proof. eapply (gs_gx_open_xR (@wle SEGS)); wle_inst. Qed.

Lemma gs_gx_close_x : forall G STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k2 memS,
0 <= STK -> gagree G (w_H W0) mem memS ->
ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own ly2 S2 Hp2 W2 mem2 md2 k2 ->
@ajournal_gx_x _ SK SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2.
Proof. eapply (gs_gx_close_xR (@wle SEGS)); wle_inst. Qed.

(* ---- The segment over ARx: W_drain_cx_x.v:762 dr_gs_stmt_x, from the three stages. ---- *)
Theorem dr_gs_of_x : gs_scan_stmt_x -> gs_add_stmt_x -> gs_free_stmt_x -> dr_gs_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (dr_gs_of_xR (@wle SEGS)); wle_inst. Qed.

End cx.
End bx.
End ax.
