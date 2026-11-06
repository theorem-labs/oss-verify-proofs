(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the cut points of fuzz_reply's gestures_end walk on image B (asan-ubsan), lane W4,
   in the form of lib/A/W_gse_cut.v (A's frozen cut) and the cgif loop walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v.  A NEW WALK, not a relocation: B's code allocates registers differently
   and inserts UBSan trap branches to `unimp` (0x827b0).  FROZEN interface once pushed: change it only through lane
   W4's owner.
   Route (b), step 3 (CONVERSION.md sha256 1015972e02a9; internal record): each statement has its generic twin over an allocator relation ARx
   (gse_pre_x, gse_inv_x, gse_loop_at_x, gse_tail_at_x, Section cx), which the pieces prove; Section br0 bridges the
   two at ARx := W_journal_x.ARi0, PST := [] in both directions. *)
(* gestures_end (s) at 0x82618 on fuzz_reply.asan-ubsan:
     0x82618-0x82640  prologue (frame 80: ra, s0..s8 at sp+72 .. sp+0).
     0x82644-0x8264c  TRAPS: `beqz a0` (s null) and `andi a1,a0,7; bnez a1` (s misaligned) -> unimp; refuted by
                      SA mod 8 = 0 and 4096 <= TB <= SA.
     0x82650-0x8267c  s3 = SB (from the GOT slot 0x9df50), s0 = s+48, s2 = (s0 >> 3) + SB, nheld's load4 check,
                      a1 = nheld, s1 = s+40, s4 = s1 >> 3; `blez a1, 0x82754`.
     0x82680-0x82690  s5 = 0 (8i), s6 = 0 (i), s7 = s4 + SB, s8 = (s0 & 7) + 3 = 3.
     0x82694          LOOP HEAD (gse_loop_at): load8 check of s->held; a0 = held + 8i with the TRAPS `bltu a0,a1`
                      (wrap), `(held != 0) xor (a0 == 0)` = 0, `beqz held`, `(8i + held) & 7 != 0` -> unimp; held[i]'s
                      load8 check, gesture_end (held[i]) at 0x826dc; the same checks and traps again, free (held[i]) at
                      0x82728, nheld's load4 check, i++, 8i += 8, `blt s6, nheld, 0x82694`, else `j 0x82754`.
     0x82754          TAIL (gse_tail_at): s3 = s4 + SB, load8 check of s->held, free (s->held) at 0x82764, store8
                      check and `sd zero, 0(s1)`, store4 check and `sw zero, 0(s0)`, epilogue, ret.
   The traps are refuted from the alignment facts the A walk already carries: SA mod 8 = 0, held (re_hp e) a live
   block's 16-aligned start, 8 * nheld <= re_kh e and the block below alloc_ceiling (so held + 8i neither wraps nor is 0).
   The state at both cut points is gse_inv: the first i held keys have been ended (gesture_end) and freed, in array
   order; the journal, meter, block list and output are those of gse_post (lib/B/W_contract.v) after those i keys.
   The generic pieces are proved in Sections over B PST ARx {hl} MT RP MMAX RG with these hypotheses (each piece takes
   the ones it uses; W_gestures_end_top.v Section c lists their union):
     LAWS   : AR_laws_x SEGS B ARx hl
     HP0    : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = []      (a Theorem Labs lane's HP0 ruling)
     TL     : PALib B
     HG     : gx_ok SEGS B (G_SL B RG)
     MTL    : ameter_laws MT
     GE     : ge_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gesture_end)   (pb_gesture_end_x, W_gesture_end.v)
     AFREE  : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE          (W_journal_x.v Section hc)
     AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE     (W_journal_x.v Section hc)
     HCTX_gse_loop : In [BASE + AF_fr_gestures_end + 0x114] CTX_AFREE  (the loop's free, ra 0x8272c)
     HCTX_gse_tail : In [BASE + AF_fr_gestures_end + 0x150] CTX_AFREE  (the tail's free, ra 0x82768)
     HROMO  : rom_out SEGS B (G_SL B RG)
     HOUTG  : forall r a, In r (aout_fp B RG 0 0) -> fst r <= a < snd r -> ~ (as_errno B <= a < as_errno B + 4) ->
              in_img SEGS a /\ ~ in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)
     HEND5I / HEND5G : as in W_gesture_end.v (" end\0" lies in the image, and is none of the bytes send_line may
              change; the earlier zero-shadow claim was false and is gone)
     PSTR / HEND5P : no ROM byte, and no byte of " end\0", is one of the program statics PST
     IMGC / BLKN : W_kit_xb.v Section g (for blk_off_imgB_x, image B's top 0x5fc000; the tail piece takes BLKN only)
   and the loop-body piece additionally takes GSE_TAIL_X : gse_tail_at_x (BASE + A_gse_tail).  The AR pieces
   (pb_gse_loop, pb_gse_tail, pb_gestures_end) are re-derived from them at ARi0, in Sections with the AR hypotheses
   (GE : ge_spec, AFREE : afree_cf_rule, ..., GSE_TAIL : gse_tail_at) and LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0 in
   place of LAWS : AR_laws SEGS B; there the free rules' caller-context forms are taken at
   CTX_AFREE := [[BASE + AF_fr_gestures_end + 0x114]; [BASE + AF_fr_gestures_end + 0x150]]. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
(* the count names (acnt and its list lemmas) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
Definition A_gse_loop : Z := AF_fr_gestures_end + 0x7c.   (* 0x82694: the loop head *)
Definition A_gse_tail : Z := AF_fr_gestures_end + 0x13c.  (* 0x82754: after the loop *)
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.

(* the held array's block and the keys' blocks (gse_blks e = gse_hpblk (re_hp e) (re_kh e) ++ kblks (re_keys e)) *)
Definition gse_hpblk (hp kh : Z) : list (Z * Z) := if hp =? 0 then [] else [(hp, kh)].
Definition kblks (ks : list (Z * list byte * list byte)) : list (Z * Z) :=
map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks.
(* a held key's bytes: its text and NUL (aheld_ok's key clause, after ruling (A)) *)
Definition key_ok (W : world SEGS) (mem : word -> option byte) (k : Z * list byte * list byte) : Prop :=
garr8 SEGS (arm W mem) (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])) /\
~ In (Z_to_bv 8 0) (key_text k) /\ 14 <= Z.of_nat (length (key_text k)) <= APARTIAL.
(* the meter spent on the keys xs (gesture_end's two sends and one free per key), without the final free *)
Fixpoint gse_spent (c : ctl) (mx no cap : Z) (xs : list (list byte)) : Z :=
match xs with
| [] => 0
| x :: xs' => ge_cost MT c mx no cap (Z.of_nat (length x)) + mo_free MT +
    gse_spent (ge_ctl c (Z.of_nat (length x))) mx (ge_no c no (Z.of_nat (length x))) (ge_cap c mx no cap (Z.of_nat (length x))) xs'
end.
(* the journal's footprint: gse_post's *)
Definition gse_FP (SA : Z) (e : rentry) (cap out : Z) : list (Z * Z) :=
(SA + 40, SA + 52) :: ablocks_fp (gse_blks e ++ aout_blks cap out).

(* gse_spec's premises (W_contract.v), bundled *)
Definition gse_pre (W : world SEGS) ly S (regs : bvmap 5 word) (mem : word -> option byte) md ch (SA TB : Z) (e : rentry)
  (c : ctl) (O : list byte) (mx no cap out : Z) (rest : list (Z * Z)) : Prop :=
afn_pre SEGS B GSE_STK ly S W regs mem md ch /\
getr regs 10 = w64 SA /\
In (TB, ATABLE) (ablocks B ly S) /\ TB <= SA /\ SA + AENT <= TB + ATABLE /\ SA mod 8 = 0 /\
garr8 SEGS (arm W mem) SA (bzs (entry_bytes e)) /\ awr W mem SA AENT /\ aheld_ok B ly S W mem e /\
aout_at B RG ly S W mem c O mx no cap out /\
Permutation (ablocks B ly S) ((TB, ATABLE) :: gse_blks e ++ aout_blks cap out ++ rest) /\
garr8 SEGS (arm W mem) (VAL A_lit_end5) (bzs END5) /\ rom_view SEGS W mem /\
gse_room MMAX (blocks_bytes S) c mx no cap (gse_keys e) /\
mo_ok MT S (gse_cost MT c mx no cap (gse_keys e)).

(* The state at 0x82694 / 0x82754 after the first i held keys: world Wc, allocator lyc Sc, registers regsc, memory
   memc, model mdc, journal count k, output block outi.  s0 = s+48, s1 = s+40, s2 = shadow (s0), s3 = SB,
   s4 = s1 >> 3; s9..s11 are the caller's; ra and s0..s8 of the caller sit in the frame [sp - 80, sp) of the entry sp. *)
Definition gse_inv (W : world SEGS) ly S (regs : bvmap 5 word) (mem : word -> option byte) md (SA TB : Z) (e : rentry)
  (c : ctl) (O : list byte) (mx no cap out : Z) (rest : list (Z * Z)) (i : nat)
  (Wc : world SEGS) lyc Sc (regsc : bvmap 5 word) (memc : word -> option byte) mdc k (outi : Z) : Prop :=
let xs := gse_keys e in
let r := gse_run c O mx no cap (firstn i xs) in
ajournal_gx SEGS B (G_SL B RG) 0 [] GSE_STK (spZ regs) (gse_FP SA e cap out) ly S W mem md [] lyc Sc Wc memc mdc k /\
apres_kept B W mem Wc memc /\
mo_le MT S Sc (gse_spent c mx no cap (firstn i xs)) /\
mo_ok MT Sc (gse_cost MT (gse_c r) mx (gse_no r) (gse_cap r) (skipn i xs)) /\
gse_room MMAX (blocks_bytes Sc) (gse_c r) mx (gse_no r) (gse_cap r) (skipn i xs) /\
Permutation (ablocks B lyc Sc)
  ((TB, ATABLE) :: gse_hpblk (re_hp e) (re_kh e) ++ kblks (skipn i (re_keys e)) ++ aout_blks (gse_cap r) outi ++ rest) /\
aout_at B RG lyc Sc Wc memc (gse_c r) (gse_O r) mx (gse_no r) (gse_cap r) outi /\
garr8 SEGS (arm Wc memc) SA (bzs (entry_bytes e)) /\ awr Wc memc SA AENT /\
garr8 SEGS (arm Wc memc) (re_hp e) (bzs (key_ptrs (re_keys e))) /\
Forall (key_ok Wc memc) (skipn i (re_keys e)) /\
garr8 SEGS (arm Wc memc) (VAL A_lit_end5) (bzs END5) /\ rom_view SEGS Wc memc /\
spZ regsc = spZ regs - GSE_FRAME /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\
getr regsc 8 = w64 (SA + 48) /\ getr regsc 9 = w64 (SA + 40) /\
getr regsc 18 = w64 ((SA + 48) / 8 + SB) /\ getr regsc 19 = w64 SB /\ getr regsc 20 = w64 ((SA + 40) / 8) /\
(forall rr, 25 <= rr <= 27 -> getr regsc (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 80) 8 (bv_unsigned (getr regs 24)).

(* LOOP HEAD 0x82694, with i < nheld: s5 = 8i, s6 = i, s7 = shadow (s1), s8 = 3. *)
Definition gse_loop_at (pc : Z) : Prop :=
forall W ly S regs mem md ch SA TB e c O mx no cap out rest (i : nat) Wc lyc Sc regsc memc mdc k outi,
gse_pre W ly S regs mem md ch SA TB e c O mx no cap out rest ->
(i < length (re_keys e))%nat ->
gse_inv W ly S regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc regsc memc mdc k outi ->
getr regsc 21 = w64 (8 * Z.of_nat i) -> getr regsc 22 = w64 (Z.of_nat i) ->
getr regsc 23 = w64 ((SA + 40) / 8 + SB) -> getr regsc 24 = w64 3 ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc)
  (gse_post B MT RG regs ly S W mem md SA TB e c O mx no cap out rest).

(* TAIL 0x82754, every key ended and freed (s5..s8 arbitrary: the `blez` path never sets them). *)
Definition gse_tail_at (pc : Z) : Prop :=
forall W ly S regs mem md ch SA TB e c O mx no cap out rest Wc lyc Sc regsc memc mdc k outi,
gse_pre W ly S regs mem md ch SA TB e c O mx no cap out rest ->
gse_inv W ly S regs mem md SA TB e c O mx no cap out rest (length (re_keys e)) Wc lyc Sc regsc memc mdc k outi ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc)
  (gse_post B MT RG regs ly S W mem md SA TB e c O mx no cap out rest).

(* The model's arithmetic the pieces use. *)
Lemma gse_blks_split : forall e, gse_blks e = gse_hpblk (re_hp e) (re_kh e) ++ kblks (re_keys e).
Proof. reflexivity. Qed.
Lemma gse_run_app : forall xs1 xs2 c O mx no cap,
gse_run c O mx no cap (xs1 ++ xs2) =
gse_run (gse_c (gse_run c O mx no cap xs1)) (gse_O (gse_run c O mx no cap xs1)) mx
  (gse_no (gse_run c O mx no cap xs1)) (gse_cap (gse_run c O mx no cap xs1)) xs2.
Proof.
induction xs1 as [|x xs1 IH]; intros xs2 c O mx no cap; [reflexivity|].
cbn [app gse_run]. apply IH.
Qed.
Lemma gse_spent_app : forall xs1 xs2 c O mx no cap,
gse_spent c mx no cap (xs1 ++ xs2) =
gse_spent c mx no cap xs1 +
gse_spent (gse_c (gse_run c O mx no cap xs1)) mx (gse_no (gse_run c O mx no cap xs1)) (gse_cap (gse_run c O mx no cap xs1)) xs2.
Proof.
induction xs1 as [|x xs1 IH]; intros xs2 c O mx no cap; [cbn; lia|].
cbn [app gse_spent gse_run]. rewrite (IH xs2 _ (ge_O c O x)). lia.
Qed.
Lemma gse_cost_app : forall xs1 xs2 c O mx no cap,
gse_cost MT c mx no cap (xs1 ++ xs2) =
gse_spent c mx no cap xs1 +
gse_cost MT (gse_c (gse_run c O mx no cap xs1)) mx (gse_no (gse_run c O mx no cap xs1)) (gse_cap (gse_run c O mx no cap xs1)) xs2.
Proof.
induction xs1 as [|x xs1 IH]; intros xs2 c O mx no cap; [cbn; lia|].
cbn [app gse_cost gse_spent gse_run]. rewrite (IH xs2 _ (ge_O c O x)). lia.
Qed.
Lemma gse_cost_spent : forall xs c mx no cap, gse_cost MT c mx no cap xs = gse_spent c mx no cap xs + mo_free MT.
Proof.
induction xs as [|x xs IH]; intros c mx no cap; [cbn; lia|].
cbn [gse_cost gse_spent]. rewrite IH. lia.
Qed.
End c.

(* ---- THE GENERIC CUT STATEMENTS (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): gse_pre / gse_inv / gse_loop_at /
   gse_tail_at over any allocator relation ARx, in W_contract_x's vocabulary (afn_pre_x and ajournal_gx_x with the
   ghost list Hp after S and Hpc after Sc; the post gse_post_x).  Each text is the AR one's otherwise.  The pieces
   prove them over ARx (pb_gse_loop_x, pb_gse_tail_x) and pb_gestures_end_x composes them; Section br0 below turns
   each into its AR form at ARi0 and back.
   The room round (commit 67327a6003d, lib/A/W_contract_x.v), threaded as gse_spec_x threads it: the Section takes RP
   after MT; gse_pre_x gains the parameter kr and, after its mo_ok, gse_spec_x's two premises (the room invariant RM at
   the entry S with the whole run's allocator-call count, the entry's live counts under gse_spec_x's peak); gse_inv_x
   gains kr and, after its mo_ok, RM at the cut's state Sc with the count of the calls left; the cut statements bind
   kr, pass it to both, and conclude gse_post_x .. kr.  The counts at Sc are not in gse_inv_x: its block permutation
   and the entry's give them (gse_cnt_at below). ---- *)
Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Definition gse_pre_x (W : world SEGS) ly S (Hp : list Z) (regs : bvmap 5 word) (mem : word -> option byte) md ch
  (SA TB : Z) (e : rentry) (c : ctl) (O : list byte) (mx no cap out : Z) (rest : list (Z * Z)) (kr : nat) : Prop :=
afn_pre_x SEGS B ARx GSE_STK ly S Hp W regs mem md ch /\
getr regs 10 = w64 SA /\
In (TB, ATABLE) (ablocks B ly S) /\ TB <= SA /\ SA + AENT <= TB + ATABLE /\ SA mod 8 = 0 /\
garr8 SEGS (arm W mem) SA (bzs (entry_bytes e)) /\ awr W mem SA AENT /\ aheld_ok B ly S W mem e /\
aout_at B RG ly S W mem c O mx no cap out /\
Permutation (ablocks B ly S) ((TB, ATABLE) :: gse_blks e ++ aout_blks cap out ++ rest) /\
garr8 SEGS (arm W mem) (VAL A_lit_end5) (bzs END5) /\ rom_view SEGS W mem /\
gse_room MMAX (blocks_bytes S) c mx no cap (gse_keys e) /\
mo_ok MT S (gse_cost MT c mx no cap (gse_keys e)) /\
rp_RM RP S (Z.to_nat (gse_cost MT_rk c mx no cap (gse_keys e)) + kr) /\
cnt_ok_pk RP gse_pk (ablocks B ly S).
Definition gse_inv_x (W : world SEGS) ly S (Hp : list Z) (regs : bvmap 5 word) (mem : word -> option byte) md
  (SA TB : Z) (e : rentry) (c : ctl) (O : list byte) (mx no cap out : Z) (rest : list (Z * Z)) (i : nat)
  (Wc : world SEGS) lyc Sc (Hpc : list Z) (regsc : bvmap 5 word) (memc : word -> option byte) mdc k (outi : Z)
  (kr : nat) : Prop :=
let xs := gse_keys e in
let r := gse_run c O mx no cap (firstn i xs) in
ajournal_gx_x SEGS B PST ARx (G_SL B RG) 0 [] GSE_STK (spZ regs) (gse_FP SA e cap out) ly S Hp W mem md []
  lyc Sc Hpc Wc memc mdc k /\
apres_kept B W mem Wc memc /\
mo_le MT S Sc (gse_spent MT c mx no cap (firstn i xs)) /\
mo_ok MT Sc (gse_cost MT (gse_c r) mx (gse_no r) (gse_cap r) (skipn i xs)) /\
rp_RM RP Sc (Z.to_nat (gse_cost MT_rk (gse_c r) mx (gse_no r) (gse_cap r) (skipn i xs)) + kr) /\
gse_room MMAX (blocks_bytes Sc) (gse_c r) mx (gse_no r) (gse_cap r) (skipn i xs) /\
Permutation (ablocks B lyc Sc)
  ((TB, ATABLE) :: gse_hpblk (re_hp e) (re_kh e) ++ kblks (skipn i (re_keys e)) ++ aout_blks (gse_cap r) outi ++ rest) /\
aout_at B RG lyc Sc Wc memc (gse_c r) (gse_O r) mx (gse_no r) (gse_cap r) outi /\
garr8 SEGS (arm Wc memc) SA (bzs (entry_bytes e)) /\ awr Wc memc SA AENT /\
garr8 SEGS (arm Wc memc) (re_hp e) (bzs (key_ptrs (re_keys e))) /\
Forall (key_ok Wc memc) (skipn i (re_keys e)) /\
garr8 SEGS (arm Wc memc) (VAL A_lit_end5) (bzs END5) /\ rom_view SEGS Wc memc /\
spZ regsc = spZ regs - GSE_FRAME /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\
getr regsc 8 = w64 (SA + 48) /\ getr regsc 9 = w64 (SA + 40) /\
getr regsc 18 = w64 ((SA + 48) / 8 + SB) /\ getr regsc 19 = w64 SB /\ getr regsc 20 = w64 ((SA + 40) / 8) /\
(forall rr, 25 <= rr <= 27 -> getr regsc (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 80) 8 (bv_unsigned (getr regs 24)).
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): gse_inv_x at a world relation R.  The journal conjunct ajournal_gx_x becomes
   ajournal_gx_xR R; every other conjunct is verbatim.  At R := wle it is gse_inv_x (gse_inv_x_wle below). *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* :249 gse_inv_x *)
Definition gse_inv_xR (W : world SEGS) ly S (Hp : list Z) (regs : bvmap 5 word) (mem : word -> option byte) md
  (SA TB : Z) (e : rentry) (c : ctl) (O : list byte) (mx no cap out : Z) (rest : list (Z * Z)) (i : nat)
  (Wc : world SEGS) lyc Sc (Hpc : list Z) (regsc : bvmap 5 word) (memc : word -> option byte) mdc k (outi : Z)
  (kr : nat) : Prop :=
let xs := gse_keys e in
let r := gse_run c O mx no cap (firstn i xs) in
ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] GSE_STK (spZ regs) (gse_FP SA e cap out) ly S Hp W mem md []
  lyc Sc Hpc Wc memc mdc k /\
apres_kept B W mem Wc memc /\
mo_le MT S Sc (gse_spent MT c mx no cap (firstn i xs)) /\
mo_ok MT Sc (gse_cost MT (gse_c r) mx (gse_no r) (gse_cap r) (skipn i xs)) /\
rp_RM RP Sc (Z.to_nat (gse_cost MT_rk (gse_c r) mx (gse_no r) (gse_cap r) (skipn i xs)) + kr) /\
gse_room MMAX (blocks_bytes Sc) (gse_c r) mx (gse_no r) (gse_cap r) (skipn i xs) /\
Permutation (ablocks B lyc Sc)
  ((TB, ATABLE) :: gse_hpblk (re_hp e) (re_kh e) ++ kblks (skipn i (re_keys e)) ++ aout_blks (gse_cap r) outi ++ rest) /\
aout_at B RG lyc Sc Wc memc (gse_c r) (gse_O r) mx (gse_no r) (gse_cap r) outi /\
garr8 SEGS (arm Wc memc) SA (bzs (entry_bytes e)) /\ awr Wc memc SA AENT /\
garr8 SEGS (arm Wc memc) (re_hp e) (bzs (key_ptrs (re_keys e))) /\
Forall (key_ok Wc memc) (skipn i (re_keys e)) /\
garr8 SEGS (arm Wc memc) (VAL A_lit_end5) (bzs END5) /\ rom_view SEGS Wc memc /\
spZ regsc = spZ regs - GSE_FRAME /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\
getr regsc 8 = w64 (SA + 48) /\ getr regsc 9 = w64 (SA + 40) /\
getr regsc 18 = w64 ((SA + 48) / 8 + SB) /\ getr regsc 19 = w64 SB /\ getr regsc 20 = w64 ((SA + 40) / 8) /\
(forall rr, 25 <= rr <= 27 -> getr regsc (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) /\
val_mem SEGS (arm Wc memc) (spZ regs - 80) 8 (bv_unsigned (getr regs 24)).
End wR.
Lemma gse_inv_x_wle : gse_inv_x = gse_inv_xR (@wle SEGS). Proof. reflexivity. Qed.
Definition gse_loop_at_x (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch SA TB e c O mx no cap out rest (i : nat) Wc lyc Sc Hpc regsc memc mdc k outi (kr : nat),
gse_pre_x W ly S Hp regs mem md ch SA TB e c O mx no cap out rest kr ->
(i < length (re_keys e))%nat ->
gse_inv_x W ly S Hp regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc Hpc regsc memc mdc k outi kr ->
getr regsc 21 = w64 (8 * Z.of_nat i) -> getr regsc 22 = w64 (Z.of_nat i) ->
getr regsc 23 = w64 ((SA + 40) / 8 + SB) -> getr regsc 24 = w64 3 ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc)
  (gse_post_x B PST ARx MT RP RG regs ly S Hp W mem md SA TB e c O mx no cap out rest kr).
Definition gse_tail_at_x (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch SA TB e c O mx no cap out rest Wc lyc Sc Hpc regsc memc mdc k outi (kr : nat),
gse_pre_x W ly S Hp regs mem md ch SA TB e c O mx no cap out rest kr ->
gse_inv_x W ly S Hp regs mem md SA TB e c O mx no cap out rest (length (re_keys e)) Wc lyc Sc Hpc regsc memc mdc k outi
  kr ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc)
  (gse_post_x B PST ARx MT RP RG regs ly S Hp W mem md SA TB e c O mx no cap out rest kr).
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the two cut statements at a world relation R.  gse_inv_x -> gse_inv_xR R,
   SRr SEGS -> SRrG SEGS R, gse_post_x -> W_contract_xR.gse_post_xR (R right after ARx); every other premise verbatim.
   At R := wle each is its strict twin (_wle below). *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* :284 gse_loop_at_x *)
Definition gse_loop_at_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch SA TB e c O mx no cap out rest (i : nat) Wc lyc Sc Hpc regsc memc mdc k outi (kr : nat),
gse_pre_x W ly S Hp regs mem md ch SA TB e c O mx no cap out rest kr ->
(i < length (re_keys e))%nat ->
gse_inv_xR R W ly S Hp regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc Hpc regsc memc mdc k outi kr ->
getr regsc 21 = w64 (8 * Z.of_nat i) -> getr regsc 22 = w64 (Z.of_nat i) ->
getr regsc 23 = w64 ((SA + 40) / 8 + SB) -> getr regsc 24 = w64 3 ->
SRrG SEGS R Wc (mkCfg (mkst regsc (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc)
  (gse_post_xR B PST ARx R MT RP RG regs ly S Hp W mem md SA TB e c O mx no cap out rest kr).
(* :293 gse_tail_at_x *)
Definition gse_tail_at_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch SA TB e c O mx no cap out rest Wc lyc Sc Hpc regsc memc mdc k outi (kr : nat),
gse_pre_x W ly S Hp regs mem md ch SA TB e c O mx no cap out rest kr ->
gse_inv_xR R W ly S Hp regs mem md SA TB e c O mx no cap out rest (length (re_keys e)) Wc lyc Sc Hpc regsc memc mdc k outi
  kr ->
SRrG SEGS R Wc (mkCfg (mkst regsc (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc)
  (gse_post_xR B PST ARx R MT RP RG regs ly S Hp W mem md SA TB e c O mx no cap out rest kr).
End wR.
Lemma gse_loop_at_x_wle : gse_loop_at_x = gse_loop_at_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma gse_tail_at_x_wle : gse_tail_at_x = gse_tail_at_xR (@wle SEGS). Proof. reflexivity. Qed.
End cx.

(* ---- THE ROOM ROUND's counts and calls (commit 67327a6003d: a call's count premise from its caller's).  At every
   state of the key run the live blocks are the entry's less the keys freed so far, with the output block (at most one)
   in place of the entry's: a live P-count there is at most the entry's plus one.  So a call's count premise of peak pk
   follows from the entry premise of peak pk0 whenever pk P + 1 <= pk0 P.  The peaks are arguments, read off the
   premises at each call site; the specs name them (W_contract_x.v gse_pk = ge_pk + 1), so a constant peak change edits
   no line of this walk. ---- *)
Lemma gse_acnt_aout : forall P cap out, (acnt P (aout_blks cap out) <= 1)%nat.
Proof.
intros P cap out. unfold aout_blks. destruct (cap =? 0); [cbn; lia|].
rewrite acnt_cons, acnt_nil. destruct (P (snd (out, cap))); lia.
Qed.
Lemma gse_acnt_skipn : forall P ks j, (acnt P (kblks (skipn j ks)) <= acnt P (kblks ks))%nat.
Proof.
intros P ks j. unfold kblks. rewrite <- (firstn_skipn j ks) at 2. rewrite map_app, acnt_app. lia.
Qed.
Lemma gse_cnt_at : forall RP (pk0 pk : (Z -> bool) -> nat) e l0 l TB j cap out cap' out' rest,
(forall P, (pk P + 1 <= pk0 P)%nat) ->
Permutation l0 ((TB, ATABLE) :: gse_blks e ++ aout_blks cap out ++ rest) ->
Permutation l ((TB, ATABLE) :: gse_hpblk (re_hp e) (re_kh e) ++ kblks (skipn j (re_keys e)) ++ aout_blks cap' out' ++ rest) ->
cnt_ok_pk RP pk0 l0 -> cnt_ok_pk RP pk l.
Proof.
intros RP pk0 pk e l0 l TB j cap out cap' out' rest Hpk H0 H1 HC.
apply (cnt_ok_pk_mono RP pk0 pk l0 l); [|exact HC].
intros P. rewrite (acnt_perm P _ _ H0), (acnt_perm P _ _ H1), gse_blks_split.
rewrite !acnt_cons, !acnt_app.
pose proof (gse_acnt_aout P cap' out'). pose proof (gse_acnt_skipn P (re_keys e) j). pose proof (Hpk P). lia.
Qed.
(* MT_rk (W_contract_x.v, the allocator-call count) is a meter *)
Lemma gse_rk_laws : ameter_laws MT_rk.
Proof. constructor; unfold MT_rk; cbn; intros; first [exact I | lia]. Qed.

(* ---- THE ARi0 BRIDGES of the cut statements (the HP0 ruling; CONVERSION.md (sha256 1015972e02a9; internal record) 3.): at ARx := W_journal_x.ARi0
   (cgif's AR /\ Hp = []) and PST := [], each generic cut statement gives the AR one (_x_AR0, for a re-derived piece)
   and each AR one gives the generic one (_x_of_AR0, for a re-derived composition that takes the AR cut as its
   hypothesis).  The pre and the invariant move through W_journal_x.afn_pre_x_ARi0_of_AR / _to_AR and
   ajournal_gx_AR_x_ARi0 / ajournal_gx_x_ARi0_AR, the post through W_contract_x.gse_post_x_AR0 / gse_post_x_of_AR0
   (the latter at the entry Hp = [], which an ARi0 pre forces). ---- *)
Section br0.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Lemma gse_pre_x_ARi0_of_AR : forall W ly S regs mem md ch SA TB e c O mx no cap out rest kr,
gse_pre B MT MMAX RG W ly S regs mem md ch SA TB e c O mx no cap out rest ->
gse_pre_x B (ARi0 SEGS B) MT RP_AR MMAX RG W ly S [] regs mem md ch SA TB e c O mx no cap out rest kr.
Proof.
intros W ly S regs mem md ch SA TB e c O mx no cap out rest kr
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
split; [apply afn_pre_x_ARi0_of_AR; exact H1|].
refine (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12 (conj H13
  (conj H14 (conj H15 (conj (rp_RM_AR _ _) _))))))))))))))).
apply cnt_ok_pk_AR. cbv [gse_pk]. lia.
Qed.
Lemma gse_pre_x_ARi0_to_AR : forall W ly S Hp regs mem md ch SA TB e c O mx no cap out rest kr,
gse_pre_x B (ARi0 SEGS B) MT RP_AR MMAX RG W ly S Hp regs mem md ch SA TB e c O mx no cap out rest kr ->
gse_pre B MT MMAX RG W ly S regs mem md ch SA TB e c O mx no cap out rest.
Proof.
intros W ly S Hp regs mem md ch SA TB e c O mx no cap out rest kr
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & _).
split; [eapply afn_pre_x_ARi0_to_AR; exact H1|].
exact (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12 (conj H13
  (conj H14 H15))))))))))))).
Qed.
Lemma gse_inv_x_ARi0_of_AR : forall W ly S Hp regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc regsc memc mdc k outi
  kr,
gse_inv B MT MMAX RG W ly S regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc regsc memc mdc k outi ->
gse_inv_x B [] (ARi0 SEGS B) MT RP_AR MMAX RG W ly S Hp regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc [] regsc
  memc mdc k outi kr.
Proof.
intros W ly S Hp regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc regsc memc mdc k outi kr H.
unfold gse_inv in H. unfold gse_inv_x. cbv zeta in H |- *. destruct H as (HJ & HA & HL & HO & R).
split; [apply ajournal_gx_AR_x_ARi0; exact HJ|].
exact (conj HA (conj HL (conj HO (conj (rp_RM_AR _ _) R)))).
Qed.
Lemma gse_inv_x_ARi0_to_AR : forall W ly S Hp regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc Hpc regsc memc mdc k
  outi kr,
gse_inv_x B [] (ARi0 SEGS B) MT RP_AR MMAX RG W ly S Hp regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc Hpc regsc
  memc mdc k outi kr ->
gse_inv B MT MMAX RG W ly S regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc regsc memc mdc k outi.
Proof.
intros W ly S Hp regs mem md SA TB e c O mx no cap out rest i Wc lyc Sc Hpc regsc memc mdc k outi kr H.
unfold gse_inv_x in H. unfold gse_inv. cbv zeta in H |- *. destruct H as (HJ & HA & HL & HO & _ & R).
split; [eapply ajournal_gx_x_ARi0_AR; exact HJ|].
exact (conj HA (conj HL (conj HO R))).
Qed.
Lemma gse_tail_at_x_AR0 : forall pc, gse_tail_at_x B [] (ARi0 SEGS B) MT RP_AR MMAX RG pc -> gse_tail_at B MT MMAX RG pc.
Proof.
intros pc H W ly S regs mem md ch SA TB e c O mx no cap out rest Wc lyc Sc regsc memc mdc k outi HP HI.
eapply SRr_mono.
{ apply (H W ly S [] regs mem md ch SA TB e c O mx no cap out rest Wc lyc Sc [] regsc memc mdc k outi 0%nat);
  [apply gse_pre_x_ARi0_of_AR; exact HP | apply gse_inv_x_ARi0_of_AR; exact HI]. }
cbv beta. intros W2 c2 _ HQ. apply gse_post_x_AR0 in HQ. exact HQ.
Qed.
Lemma gse_tail_at_x_of_AR0 : forall pc, gse_tail_at B MT MMAX RG pc -> gse_tail_at_x B [] (ARi0 SEGS B) MT RP_AR MMAX RG pc.
Proof.
intros pc H W ly S Hp regs mem md ch SA TB e c O mx no cap out rest Wc lyc Sc Hpc regsc memc mdc k outi kr HP HI.
assert (E : Hp = []) by exact (ARi0_hp0 SEGS B _ _ _ _ _ _ (proj1 (proj1 HP))). subst Hp.
eapply SRr_mono.
{ apply (H W ly S regs mem md ch SA TB e c O mx no cap out rest Wc lyc Sc regsc memc mdc k outi);
  [eapply gse_pre_x_ARi0_to_AR; exact HP | eapply gse_inv_x_ARi0_to_AR; exact HI]. }
cbv beta. intros W2 c2 _ HQ. apply gse_post_x_of_AR0. exact HQ.
Qed.
Lemma gse_loop_at_x_AR0 : forall pc, gse_loop_at_x B [] (ARi0 SEGS B) MT RP_AR MMAX RG pc -> gse_loop_at B MT MMAX RG pc.
Proof.
intros pc H W ly S regs mem md ch SA TB e c O mx no cap out rest i Wc lyc Sc regsc memc mdc k outi HP Hi HI R20 R21 R22 R23.
eapply SRr_mono.
{ apply (H W ly S [] regs mem md ch SA TB e c O mx no cap out rest i Wc lyc Sc [] regsc memc mdc k outi 0%nat);
  [apply gse_pre_x_ARi0_of_AR; exact HP | exact Hi | apply gse_inv_x_ARi0_of_AR; exact HI
  | exact R20 | exact R21 | exact R22 | exact R23]. }
cbv beta. intros W2 c2 _ HQ. apply gse_post_x_AR0 in HQ. exact HQ.
Qed.
Lemma gse_loop_at_x_of_AR0 : forall pc, gse_loop_at B MT MMAX RG pc -> gse_loop_at_x B [] (ARi0 SEGS B) MT RP_AR MMAX RG pc.
Proof.
intros pc H W ly S Hp regs mem md ch SA TB e c O mx no cap out rest i Wc lyc Sc Hpc regsc memc mdc k outi kr HP Hi HI
  R20 R21 R22 R23.
assert (E : Hp = []) by exact (ARi0_hp0 SEGS B _ _ _ _ _ _ (proj1 (proj1 HP))). subst Hp.
eapply SRr_mono.
{ apply (H W ly S regs mem md ch SA TB e c O mx no cap out rest i Wc lyc Sc regsc memc mdc k outi);
  [eapply gse_pre_x_ARi0_to_AR; exact HP | exact Hi | eapply gse_inv_x_ARi0_to_AR; exact HI
  | exact R20 | exact R21 | exact R22 | exact R23]. }
cbv beta. intros W2 c2 _ HQ. apply gse_post_x_of_AR0. exact HQ.
Qed.
End br0.
End b.
End a.
