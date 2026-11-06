(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the second segment of the ASan walk of fuzz_reply's list_push (lane W2): from the
   malloc call at 0x8515c to the return, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v (allocator call sites) and lib/A/ACbk.v (return). *)
(* list_push (A/W_list_push.v) reaches the malloc call on two paths: directly when the list has room, and after
   growing the vector with realloc when it is full.  Both paths meet here; this file states what holds at the call
   (lp_tail_pre, in terms of values, not of a symbolic state) and proves the rest of the function from it:
   malloc(n + 1) through AMA (amalloc_cf_rule, forced success through the meter), the store of the new block into
   the vector slot v + 16 * N (an address computed from two atoms), __asan_memcpy of the n source bytes through
   AMEMCPY (aintrin_realizes OCpy), the NUL at d + n, the length into the slot, l->n = N + 1, and the epilogue. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_journal W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
(* the malloc call: 0x8515c = list_push + 0xcc *)
Definition A_lp_mcall : Z := AF_fr_list_push + 0xcc.
(* list_push's frame: ra at 88, s0 .. s10 at 80 .. 0 *)
Definition lp_saved : list (Z * Z) :=
[(88, 1); (80, 8); (72, 9); (64, 18); (56, 19); (48, 20); (40, 21); (32, 22); (24, 23); (16, 24); (8, 25); (0, 26)].
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable G : list (Z * Z).
(* What holds at the malloc call, on both paths.
   - (W ly S regs mem md) is list_push's entry, with the spec's arguments LA SRC l lines x q k;
   - (Wc lyc Sc memc mdc kc regsc) is the state at the call, and lc the list as it is there: the same texts as l,
     the vector grown when l was full (its capacity is grow_cap N CAP > N), the count still N;
   - the registers hold what the code put there (s0 = LA+8, s1 = n, s2 = LA, s3 = SRC, s4 = LA+12, s5 = the shadow
     base SB, s6 / s8 the shadow addresses of LA+8 / LA+12, s7 = LA >> 3, a0 = n + 1; s9 / s10 are scratch), and
     the frame holds the caller's ra and s0 .. s10;
   - the blocks: the old vector replaced by the new one when l was full; the source still a live block other than
     the vector, holding x; the meter has paid the growth. *)
Definition lp_tail_pre (W : world SEGS) ly S (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(LA SRC : Z) (l : hlist) (lines : bool) (x : list byte) (q k : Z)
(Wc : world SEGS) lyc Sc (regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (kc : Z) (lc : hlist) : Prop :=
let n := Z.of_nat (length x) in
ajournal_gx SEGS B G 0 [] LP_STK (spZ regs) (lp_FP l) ly S W mem md [] lyc Sc Wc memc mdc kc /\
(exists ch, afn_pre SEGS B LP_STK ly S W regs mem md ch) /\
(forall a, LA <= a < LA + 16 -> inG G a) /\ azs B LA 16 /\
alist_at B lyc Sc Wc memc LA lc lines /\
hl_recs lc = hl_recs l /\ hl_cap lc = grow_cap (hl_n l) (hl_cap l) /\ hl_n lc < hl_cap lc /\
(lp_grow l = false -> hl_v lc = hl_v l) /\
(lp_grow l = true -> ~ In (hl_v lc, AREC * hl_cap lc) (ablocks B ly S)) /\
(forall rest,
 Permutation (ablocks B ly S) ((if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []) ++ rest) ->
 Permutation (ablocks B lyc Sc) ((if lp_grow l then [(hl_v lc, AREC * hl_cap lc)] else []) ++ rest)) /\
frames Sc = frames S /\
mo_le MT S Sc (if lp_grow l then mo_malloc MT (lp_vbytes l) + mo_free MT else 0) /\
mo_ok MT S (lp_cost MT l n) /\
blocks_bytes Sc + (n + 1) <= LIVE_MAX /\ n < 2 ^ 16 /\
garr8 SEGS (mrestrict (w_H Wc) memc) SRC (bzs x) /\
(lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= APARTIAL) /\
(lines = false -> (1 <= length x)%nat) /\
getr regsc 2 = Z_to_bv 64 (spZ regs - 96) /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\ getr regsc 27 = getr regs 27 /\
getr regsc 8 = w64 (LA + 8) /\ getr regsc 9 = w64 n /\ getr regsc 18 = w64 LA /\ getr regsc 19 = w64 SRC /\
getr regsc 20 = w64 (LA + 12) /\ getr regsc 21 = w64 SB /\
getr regsc 22 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3) /\
getr regsc 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 10 = w64 (n + 1) /\
Forall (fun p => val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 96 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved /\
apres_kept B W mem Wc memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H Wc) memc (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
Definition lp_tail_stmt : Prop :=
forall W ly S regs mem md LA SRC l lines x q k Wc lyc Sc regsc memc mdc kc lc,
In (q, k) (ablocks B lyc Sc) -> q <> hl_v lc -> q <= SRC -> SRC + Z.of_nat (length x) <= q + req_size k ->
lp_tail_pre W ly S regs mem md LA SRC l lines x q k Wc lyc Sc regsc memc mdc kc lc ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_lp_mcall)) memc (seg_rom SEGS)) mdc)
(lp_post B MT G regs ly S W mem md LA l lines x).
End c.
(* The ARx-generic twins (a Theorem Labs lane's route (b), step 3): lp_tail_pre / lp_tail_stmt's text over
   W_journal_x.ajournal_gx_x, YCbqG.afn_pre_x and W_contract_x.lp_post_x at a relation ARx and program statics PST,
   with the ghost list Hp after S and Hpc after Sc; nothing else changes. lp_tail_stmt_x_AR0 below gives lp_tail_stmt
   from the twin at ARx := ARi0, PST := []. *)
Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Definition lp_tail_pre_x (W : world SEGS) ly S (Hp : list Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(LA SRC : Z) (l : hlist) (lines : bool) (x : list byte) (q k : Z)
(Wc : world SEGS) lyc Sc (Hpc : list Z) (regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (kc : Z) (lc : hlist)
(kr : nat) : Prop :=
let n := Z.of_nat (length x) in
ajournal_gx_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc /\
(exists ch, afn_pre_x SEGS B ARx LP_STK ly S Hp W regs mem md ch) /\
(forall a, LA <= a < LA + 16 -> inG G a) /\ azs B LA 16 /\
alist_at B lyc Sc Wc memc LA lc lines /\
hl_recs lc = hl_recs l /\ hl_cap lc = grow_cap (hl_n l) (hl_cap l) /\ hl_n lc < hl_cap lc /\
(lp_grow l = false -> hl_v lc = hl_v l) /\
(lp_grow l = true -> ~ In (hl_v lc, AREC * hl_cap lc) (ablocks B ly S)) /\
(forall rest,
 Permutation (ablocks B ly S) ((if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []) ++ rest) ->
 Permutation (ablocks B lyc Sc) ((if lp_grow l then [(hl_v lc, AREC * hl_cap lc)] else []) ++ rest)) /\
frames Sc = frames S /\
mo_le MT S Sc (if lp_grow l then mo_malloc MT (lp_vbytes l) + mo_free MT else 0) /\
mo_ok MT S (lp_cost MT l n) /\
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the tail's malloc at its own pre state Sc *)
rp_RM RP Sc (1 + kr) /\ cnt_ok RP (ablocks B lyc Sc) /\
blocks_bytes Sc + (n + 1) <= LIVE_MAX /\ n < 2 ^ 16 /\
garr8 SEGS (mrestrict (w_H Wc) memc) SRC (bzs x) /\
(lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= APARTIAL) /\
(lines = false -> (1 <= length x)%nat) /\
getr regsc 2 = Z_to_bv 64 (spZ regs - 96) /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\ getr regsc 27 = getr regs 27 /\
getr regsc 8 = w64 (LA + 8) /\ getr regsc 9 = w64 n /\ getr regsc 18 = w64 LA /\ getr regsc 19 = w64 SRC /\
getr regsc 20 = w64 (LA + 12) /\ getr regsc 21 = w64 SB /\
getr regsc 22 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3) /\
getr regsc 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 10 = w64 (n + 1) /\
Forall (fun p => val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 96 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved /\
apres_kept B W mem Wc memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H Wc) memc (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
Definition lp_tail_stmt_x : Prop :=
forall W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr,
In (q, k) (ablocks B lyc Sc) -> q <> hl_v lc -> q <= SRC -> SRC + Z.of_nat (length x) <= q + req_size k ->
lp_tail_pre_x W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_lp_mcall)) memc (seg_rom SEGS)) mdc)
(lp_post_x B PST ARx MT RP G regs ly S Hp W mem md LA l lines x kr).
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): lp_tail_pre_x / lp_tail_stmt_x at a world relation R.  The journal is
   ajournal_gx_xR R, the step relation SRrG SEGS R and the post W_contract_xR.lp_post_xR R; every other conjunct is
   verbatim.  At R := wle they are the strict texts above (lp_tail_pre_x_wle / lp_tail_stmt_x_wle, by reflexivity). *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Definition lp_tail_pre_xR (W : world SEGS) ly S (Hp : list Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(LA SRC : Z) (l : hlist) (lines : bool) (x : list byte) (q k : Z)
(Wc : world SEGS) lyc Sc (Hpc : list Z) (regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (kc : Z) (lc : hlist)
(kr : nat) : Prop :=
let n := Z.of_nat (length x) in
ajournal_gx_xR SEGS B PST ARx R G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc /\
(exists ch, afn_pre_x SEGS B ARx LP_STK ly S Hp W regs mem md ch) /\
(forall a, LA <= a < LA + 16 -> inG G a) /\ azs B LA 16 /\
alist_at B lyc Sc Wc memc LA lc lines /\
hl_recs lc = hl_recs l /\ hl_cap lc = grow_cap (hl_n l) (hl_cap l) /\ hl_n lc < hl_cap lc /\
(lp_grow l = false -> hl_v lc = hl_v l) /\
(lp_grow l = true -> ~ In (hl_v lc, AREC * hl_cap lc) (ablocks B ly S)) /\
(forall rest,
 Permutation (ablocks B ly S) ((if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []) ++ rest) ->
 Permutation (ablocks B lyc Sc) ((if lp_grow l then [(hl_v lc, AREC * hl_cap lc)] else []) ++ rest)) /\
frames Sc = frames S /\
mo_le MT S Sc (if lp_grow l then mo_malloc MT (lp_vbytes l) + mo_free MT else 0) /\
mo_ok MT S (lp_cost MT l n) /\
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) v3): the tail's malloc at its own pre state Sc *)
rp_RM RP Sc (1 + kr) /\ cnt_ok RP (ablocks B lyc Sc) /\
blocks_bytes Sc + (n + 1) <= LIVE_MAX /\ n < 2 ^ 16 /\
garr8 SEGS (mrestrict (w_H Wc) memc) SRC (bzs x) /\
(lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= APARTIAL) /\
(lines = false -> (1 <= length x)%nat) /\
getr regsc 2 = Z_to_bv 64 (spZ regs - 96) /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\ getr regsc 27 = getr regs 27 /\
getr regsc 8 = w64 (LA + 8) /\ getr regsc 9 = w64 n /\ getr regsc 18 = w64 LA /\ getr regsc 19 = w64 SRC /\
getr regsc 20 = w64 (LA + 12) /\ getr regsc 21 = w64 SB /\
getr regsc 22 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3) /\
getr regsc 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 10 = w64 (n + 1) /\
Forall (fun p => val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 96 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved /\
apres_kept B W mem Wc memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H Wc) memc (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
Definition lp_tail_stmt_xR : Prop :=
forall W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr,
In (q, k) (ablocks B lyc Sc) -> q <> hl_v lc -> q <= SRC -> SRC + Z.of_nat (length x) <= q + req_size k ->
lp_tail_pre_xR W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr ->
SRrG SEGS R Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_lp_mcall)) memc (seg_rom SEGS)) mdc)
(lp_post_xR B PST ARx R MT RP G regs ly S Hp W mem md LA l lines x kr).
End wR.
Lemma lp_tail_pre_x_wle : lp_tail_pre_x = lp_tail_pre_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma lp_tail_stmt_x_wle : lp_tail_stmt_x = lp_tail_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
End cx.
(* THE BRIDGES for the re-derivation (ARx := ARi0, PST := []). lp_tail_stmt_x_AR0: the twin gives lp_tail_stmt (the
   AR pre is the twin's pre at Hp = Hpc = [], through ajournal_gx_AR_x_ARi0 / afn_pre_x_ARi0_of_AR; the post through
   W_contract_x.lp_post_x_AR0). lp_tail_stmt_x_of_AR0: lp_tail_stmt gives the twin (afn_pre_x at ARi0 fixes Hp = [];
   the pre through ajournal_gx_x_ARi0_AR / afn_pre_x_ARi0_to_AR, the post through W_contract_x.lp_post_x_of_AR0). *)
Lemma lp_tail_stmt_x_AR0 : forall B MT G, lp_tail_stmt_x B [] (ARi0 SEGS B) MT RP_AR G -> lp_tail_stmt B MT G.
Proof.
intros B MT G H W ly S regs mem md LA SRC l lines x q k Wc lyc Sc regsc memc mdc kc lc Hq Hqv HqS HqE HPRE.
eapply SRr_mono.
{ apply (H W ly S [] regs mem md LA SRC l lines x q k Wc lyc Sc [] regsc memc mdc kc lc 0%nat Hq Hqv HqS HqE).
  unfold lp_tail_pre, lp_tail_pre_x in *. cbv zeta in HPRE |- *.
  destruct HPRE as (HJ & (ch & HAF) & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & HR).
  split; [apply ajournal_gx_AR_x_ARi0; exact HJ|].
  split; [exists ch; apply afn_pre_x_ARi0_of_AR; exact HAF|].
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
    (conj (rp_RM_AR Sc (1 + 0)%nat) (conj (cnt_ok_AR (ablocks B lyc Sc)) HR)))))))))))))). }
cbv beta. intros W2 c2 _ HQ. exact (lp_post_x_AR0 B MT G regs ly S [] W mem md LA l lines x 0%nat W2 c2 HQ).
Qed.
Lemma lp_tail_stmt_x_of_AR0 : forall B MT G, lp_tail_stmt B MT G -> lp_tail_stmt_x B [] (ARi0 SEGS B) MT RP_AR G.
Proof.
intros B MT G H W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr Hq Hqv HqS HqE HPRE.
unfold lp_tail_pre_x in HPRE. cbv zeta in HPRE.
destruct HPRE as (HJ & (ch & HAF) & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & _ & _ & HR).
assert (EHp : Hp = []) by exact (proj2 (proj1 HAF)). subst Hp.
eapply SRr_mono.
{ apply (H W ly S regs mem md LA SRC l lines x q k Wc lyc Sc regsc memc mdc kc lc Hq Hqv HqS HqE).
  unfold lp_tail_pre. cbv zeta.
  split; [eapply (ajournal_gx_x_ARi0_AR SEGS B); exact HJ|].
  split; [exists ch; eapply (afn_pre_x_ARi0_to_AR SEGS B); exact HAF|].
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
    HR)))))))))))). }
cbv beta. intros W2 c2 _ HQ. exact (lp_post_x_of_AR0 B MT G regs ly S W mem md LA l lines x kr W2 c2 HQ).
Qed.
End b.
End a.
