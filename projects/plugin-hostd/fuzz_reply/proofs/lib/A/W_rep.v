(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan twins of the plain representation predicates of
   lib/Prog/HarnessRep.v (list_at, src_at) and lib/Prog/RelayRep.v (entry_ok, table_at), shared by every
   ASan walk of fuzz_reply that reads or writes the harness's sources or the relay's table. *)
(* The model is the plain proof's: the records hlist / hsrc (Prog/HarnessRep.v) and rentry (Prog/RelayRep.v),
   with the keys of Prog/gestures_end_b_c.v.  Only the memory side changes:
   - a cell `rw_cells segs mem a [C8 v]` becomes `val_mem SEGS (mrestrict (w_H W) mem) a 8 v`, and its
     writability `writable_at SEGS (mrestrict (w_H W) mem)` over the cell's bytes (awr);
   - a byte string `rw_cells .. [CB n bs]` / `bytes_at segs mem a bs` becomes `garr8 SEGS (mrestrict (w_H W) mem) a (bzs bs)`;
   - a heap block `In (p, n) (blocks L A) /\ fresh_block Bm p n` becomes `In (p, n) (ablocks B ly S)`
     (its bytes are present and writable, and blocks are disjoint, by AR_blocks_law, Reusable/YG0d.v:435).
   The globals' addresses are Section variables (rep_globals), because the ASan and ASan+UBSan images place
   them differently (maps/EvBound/GLOBALS.md); fuzz_reply.asan's values are fr_globals below. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YP09 YI04 YI00 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The globals the representation names.  Each is the address of the object (not of its redzone). *)
Record rep_globals := mkRepGlobals {
  rg_s : Z;              (* g_s: 4 x struct source, 96 bytes each *)
  rg_src : Z;            (* g_src: source_t *, the relay's table *)
  rg_nsrc : Z;           (* g_nsrc: int *)
  rg_capsrc : Z;         (* g_capsrc: int *)
  rg_out : Z;            (* g_out: char * *)
  rg_nout : Z;           (* g_nout: size_t *)
  rg_capout : Z;         (* g_capout: size_t *)
  rg_send_max : Z;       (* g_send_max: size_t *)
  rg_send_eintr : Z;     (* g_send_eintr: int, one byte stored *)
  rg_send_dead : Z;      (* g_send_dead: int, one byte stored *)
  rg_gone : Z;           (* g_gone: int, one byte stored *)
  rg_client : Z;         (* g_client: int (.data, init -1) *)
  rg_client_broken : Z;  (* g_client_broken: one byte *)
  rg_lock : Z;           (* g_lock: musl pthread_mutex_t, type +0, lock +4, waiters +8 *)
  rg_wake : Z            (* g_wake: int[2] (.data, init {-1, -1}) *)
}.
(* fuzz_reply.asan (maps/EvBound/GLOBALS.md). *)
Definition fr_globals : rep_globals :=
  mkRepGlobals 0x5d88e0 0x5d87c0 0x5d87a0 0x5d8800 0x5d8b40 0x5d88c0 0x5d8b20
    0x5d8840 0x5d88a0 0x5d8880 0x5d8860 0xa1fe0 0x5d87e0 0x5d8ac0 0xa1fa0.
(* fuzz_reply.asan-ubsan (maps/EvBound/GLOBALS.md), for the B lane. *)
Definition fr_globals_b : rep_globals :=
  mkRepGlobals 0x5d8e60 0x5d8d40 0x5d8d20 0x5d8d80 0x5d90c0 0x5d8e40 0x5d90a0
    0x5d8dc0 0x5d8e20 0x5d8e00 0x5d8de0 0xa2560 0x5d8d60 0x5d9040 0xa2520.
(* The flags the output stream depends on: g_client (3 or -1), g_client_broken, g_send_dead, g_send_eintr
   (each 0 or 1), and the value of errno. *)
Record ctl := CTL { ct_cl : Z; ct_br : Z; ct_dd : Z; ct_ei : Z; ct_ev : Z }.

Definition AREC : Z := 16.         (* sizeof(struct text) *)
Definition ASRC : Z := 96.         (* sizeof(struct source) *)
Definition AENT : Z := 56.         (* sizeof(source_t) *)
Definition ATABLE : Z := 896.      (* the relay's table: 16 entries of source_t *)
Definition APARTIAL : Z := 6000.   (* LINE_LIMIT: the reference splitter's buffer *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.

(* what a reader sees: the ASan view of the memory *)
Definition arm (W : world SEGS) (mem : word -> option byte) : word -> option byte := mrestrict (w_H W) mem.

(* the n bytes at a are writable (a cell of a global the program stores to) *)
Definition awr (W : world SEGS) (mem : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> writable_at SEGS (arm W mem) (a + i).

(* struct list { struct text *v; int n, cap; } at LA, and what it holds.  `lines`: its texts are lines of
   the protocol (expected, held), else writes of the worker (pending). *)
Definition alist_at (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
    (LA : Z) (l : hlist) (lines : bool) : Prop :=
  val_mem SEGS (arm W mem) LA 8 (hl_v l) /\ val_mem SEGS (arm W mem) (LA + 8) 4 (hl_n l) /\
  val_mem SEGS (arm W mem) (LA + 12) 4 (hl_cap l) /\ awr W mem LA 16 /\
  hl_n l <= hl_cap l < 2 ^ 30 /\
  ((hl_cap l = 0 /\ hl_v l = 0) \/
   (0 < hl_cap l /\ In (hl_v l, AREC * hl_cap l) (ablocks B ly S) /\
    Z.of_nat (length (hl_junk l)) = AREC * (hl_cap l - hl_n l) /\
    garr8 SEGS (arm W mem) (hl_v l) (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l)))) /\
  NoDup (map fst (hl_recs l)) /\ ~ In (hl_v l) (map fst (hl_recs l)) /\
  Forall (fun r =>
    In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B ly S) /\
    garr8 SEGS (arm W mem) (fst r) (bzs (snd r ++ [Z_to_bv 8 0])) /\
    (lines = true -> ~ In (Z_to_bv 8 0) (snd r) /\ Z.of_nat (length (snd r)) <= APARTIAL) /\
    (lines = false -> (1 <= length (snd r))%nat)) (hl_recs l).

(* struct source at HA (one of g_s[0..3]), open, and what it holds *)
Definition asrc_at (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
    (HA : Z) (h : hsrc) : Prop :=
  val_mem SEGS (arm W mem) HA 4 (hs_fd h) /\ val_mem SEGS (arm W mem) (HA + 4) 4 (hs_open h) /\
  val_mem SEGS (arm W mem) (HA + 8) 4 (hs_closed h) /\ val_mem SEGS (arm W mem) (HA + 12) 4 (hs_eintr h) /\
  awr W mem HA ASRC /\
  (hs_closed h = 0 \/ hs_closed h = 1) /\ (hs_eintr h = 0 \/ hs_eintr h = 1) /\
  hs_open h = 1 /\ 0 <= hs_fd h < 2 ^ 31 /\
  alist_at ly S W mem (HA + 16) (hs_pending h) false /\
  val_mem SEGS (arm W mem) (HA + 32) 8 (hs_off h) /\ val_mem SEGS (arm W mem) (HA + 40) 8 (hs_partial h) /\
  val_mem SEGS (arm W mem) (HA + 48) 8 (hs_npartial h) /\ val_mem SEGS (arm W mem) (HA + 56) 4 (hs_overlong h) /\
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) /\
  0 <= hs_npartial h <= APARTIAL /\ (hs_overlong h = 0 \/ hs_overlong h = 1) /\
  In (hs_partial h, APARTIAL) (ablocks B ly S) /\
  Z.of_nat (length (hs_pjunk h)) = APARTIAL /\
  garr8 SEGS (arm W mem) (hs_partial h) (bzs (hs_pjunk h)) /\
  ~ In (Z_to_bv 8 0) (hs_W h) /\
  alist_at ly S W mem (HA + 64) (hs_expected h) true /\
  alist_at ly S W mem (HA + 80) (hs_held h) true /\
  NoDup (hs_blocks h).

(* a struct source not in use: all 96 bytes zero (source_reset's memset) *)
Definition asrc_closed (W : world SEGS) (mem : word -> option byte) (HA : Z) : Prop :=
  garr8 SEGS (arm W mem) HA (repeat 0 (Z.to_nat ASRC)) /\ awr W mem HA ASRC.

(* one source_t of the relay's table, and what it holds *)
Definition aentry_ok (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (e : rentry) : Prop :=
  (re_eof e = 0 \/ re_eof e = 1) /\ (re_skip e = 0 \/ re_skip e = 1) /\
  length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\
  0 <= re_fd e < 2 ^ 31 /\
  (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
  Z.of_nat (length (re_U e)) = re_used e /\ re_used e <= APARTIAL /\ ~ In (Z_to_bv 8 0) (re_U e) /\
  ((re_cap e = 0 /\ re_buf e = 0 /\ re_used e = 0) \/
   (0 < re_cap e /\ In (re_buf e, re_cap e) (ablocks B ly S) /\
    Z.of_nat (length (re_junk e)) = re_cap e - re_used e /\
    garr8 SEGS (arm W mem) (re_buf e) (bzs (re_U e ++ re_junk e)))) /\
  re_nheld e < 2 ^ 26 /\
  ((re_hp e = 0 /\ re_keys e = []) \/
   (re_hp e <> 0 /\ In (re_hp e, re_kh e) (ablocks B ly S) /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e /\
    garr8 SEGS (arm W mem) (re_hp e) (bzs (key_ptrs (re_keys e))))) /\
  NoDup (map key_addr (re_keys e)) /\
  NoDup (map key_text (re_keys e)) /\
  Forall (fun k =>
    In (key_addr k, Z.of_nat (length (key_text k)) + 1) (ablocks B ly S) /\
    garr8 SEGS (arm W mem) (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])) /\
    ~ In (Z_to_bv 8 0) (key_text k) /\ 14 <= Z.of_nat (length (key_text k)) <= APARTIAL) (re_keys e).

(* the relay's table at G: the entries, then what is left of its 896 bytes *)
Definition atable_at (W : world SEGS) (mem : word -> option byte) (G : Z) (es : list rentry) (tail : list byte) : Prop :=
  Z.of_nat (length tail) = ATABLE - AENT * Z.of_nat (length es) /\
  Z.of_nat (length (concat (map entry_bytes es) ++ tail)) = ATABLE /\
  garr8 SEGS (arm W mem) G (bzs (concat (map entry_bytes es) ++ tail)).

(* the relay's state: g_src = G, a live block of 896 bytes holding the table; g_nsrc = |es|; g_capsrc = 16 *)
(* the blocks an entry owns: its partial buffer, its key-pointer array and its key texts (defined here, before
   arelay_at, which states that none of them is the table) *)
Definition aentry_blks (e : rentry) : list (Z * Z) :=
  (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
  (if re_hp e =? 0 then [] else [(re_hp e, re_kh e)]) ++
  map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e).
Definition arelay_at (RG : rep_globals) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
    (G : Z) (es : list rentry) : Prop :=
  val_mem SEGS (arm W mem) (rg_src RG) 8 G /\ awr W mem (rg_src RG) 8 /\
  val_mem SEGS (arm W mem) (rg_nsrc RG) 4 (Z.of_nat (length es)) /\ awr W mem (rg_nsrc RG) 4 /\
  val_mem SEGS (arm W mem) (rg_capsrc RG) 4 16 /\ awr W mem (rg_capsrc RG) 4 /\
  (length es <= 16)%nat /\
  In (G, ATABLE) (ablocks B ly S) /\
  (exists tail, atable_at W mem G es tail) /\
  Forall (aentry_ok ly S W mem) es /\
  NoDup (map re_fd es) /\
  (* no entry's block is the table's (the plain RelayRep.v:56 fresh_block; W5's relay_add finding, ruled 14:0xZ):
     AR's pairwise disjointness separates an entry's blocks from the table only when they are different list
     elements.  Appended last, so a positional destruct of the eleven conjuncts still binds. *)
  Forall (fun e => forall b, In b (aentry_blks e) -> b <> (G, ATABLE)) es.

(* The controller's side of the stream, the ASan twin of the cells of Prog/send_line_b_c.v:93-102:
   g_send_max = mx (at most 255), g_nout = no, g_capout = cap, g_out = out; the flags of c (g_client,
   g_client_broken, g_send_dead, g_send_eintr) and errno; and the g_out block, which holds the bytes O the
   controller read (|O| = no), then cap - no bytes of junk.  RelayOut.send is the step of this model. *)
Definition aout_at (RG : rep_globals) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
    (c : ctl) (O : list byte) (mx no cap out : Z) : Prop :=
  val_mem SEGS (arm W mem) (rg_send_max RG) 8 mx /\ awr W mem (rg_send_max RG) 8 /\
  val_mem SEGS (arm W mem) (rg_nout RG) 8 no /\ awr W mem (rg_nout RG) 8 /\
  val_mem SEGS (arm W mem) (rg_capout RG) 8 cap /\ awr W mem (rg_capout RG) 8 /\
  val_mem SEGS (arm W mem) (rg_out RG) 8 out /\ awr W mem (rg_out RG) 8 /\
  val_mem SEGS (arm W mem) (rg_client RG) 4 (ct_cl c mod 2 ^ 32) /\ awr W mem (rg_client RG) 4 /\
  val_mem SEGS (arm W mem) (rg_client_broken RG) 1 (ct_br c) /\ awr W mem (rg_client_broken RG) 1 /\
  val_mem SEGS (arm W mem) (rg_send_dead RG) 1 (ct_dd c) /\ awr W mem (rg_send_dead RG) 1 /\
  val_mem SEGS (arm W mem) (rg_send_eintr RG) 1 (ct_ei c) /\ awr W mem (rg_send_eintr RG) 1 /\
  val_mem SEGS (arm W mem) (as_errno B) 4 (ct_ev c) /\ awr W mem (as_errno B) 4 /\ 0 <= ct_ev c < 2 ^ 32 /\
  (ct_cl c = 3 \/ ct_cl c = -1) /\ (ct_br c = 0 \/ ct_br c = 1) /\ (ct_dd c = 0 \/ ct_dd c = 1) /\
  (ct_ei c = 0 \/ ct_ei c = 1) /\
  0 <= mx <= 255 /\ Z.of_nat (length O) = no /\
  ((cap = 0 /\ out = 0 /\ no = 0) \/
   (0 < cap /\ no <= cap /\ In (out, cap) (ablocks B ly S) /\
    exists junk, Z.of_nat (length junk) = cap - no /\ garr8 SEGS (arm W mem) out (bzs (O ++ junk)))).

(* g_gone (one byte, 0 or 1): the controller went away *)
Definition agone_at (RG : rep_globals) (W : world SEGS) (mem : word -> option byte) (gn : Z) : Prop :=
  val_mem SEGS (arm W mem) (rg_gone RG) 1 gn /\ awr W mem (rg_gone RG) 1 /\ (gn = 0 \/ gn = 1).

(* g_lock (musl pthread_mutex_t): type word 0, lock word 16 while held and 0 when free, waiters 0 *)
Definition alock_at (RG : rep_globals) (W : world SEGS) (mem : word -> option byte) (held : bool) : Prop :=
  val_mem SEGS (arm W mem) (rg_lock RG) 4 0 /\
  val_mem SEGS (arm W mem) (rg_lock RG + 4) 4 (if held then 16 else 0) /\
  val_mem SEGS (arm W mem) (rg_lock RG + 8) 4 0 /\ awr W mem (rg_lock RG) 12.

(* g_wake[1] = -1: no wake pipe (what refutes relay_remove's write(g_wake[1], ...); Prog/relay_remove_b_c.v:111) *)
Definition awake_at (RG : rep_globals) (W : world SEGS) (mem : word -> option byte) : Prop :=
  val_mem SEGS (arm W mem) (rg_wake RG + 4) 4 (2 ^ 32 - 1).

(* ------------------------------------------------------------------ frame lemmas *)
(* A byte is kept from (W, mem) to (W', mem') when its ASan view is the same and it stays writable if it was. *)
Definition abyte_kept (W : world SEGS) (mem : word -> option byte) (W' : world SEGS) (mem' : word -> option byte)
    (a : Z) : Prop :=
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a /\
  (writable_at SEGS (arm W mem) a -> writable_at SEGS (arm W' mem') a).
(* every byte of every range [lo, hi) of fp is kept *)
Definition akept (W : world SEGS) (mem : word -> option byte) (W' : world SEGS) (mem' : word -> option byte)
    (fp : list (Z * Z)) : Prop :=
  forall r, In r fp -> forall a, fst r <= a < snd r -> abyte_kept W mem W' mem' a.
Definition gfp (a : Z) (l : list Z) : Z * Z := (a, a + Z.of_nat (length l)).

Lemma akept_sub : forall W mem W' mem' fp fp', akept W mem W' mem' fp -> (forall r, In r fp' -> In r fp) ->
  akept W mem W' mem' fp'.
Proof. intros W mem W' mem' fp fp' HK Hs r Hr. exact (HK r (Hs r Hr)). Qed.
Lemma akept_vm : forall W mem W' mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> abyte_kept W mem W' mem' x) ->
  val_mem SEGS (arm W mem) a n v -> val_mem SEGS (arm W' mem') a n v.
Proof.
  intros W mem W' mem' a n v HK Hv k Hk. unfold arm.
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') mem mem' (a + Z.of_nat k)); [exact (Hv k Hk)|].
  exact (proj1 (HK (a + Z.of_nat k) ltac:(lia))).
Qed.
Lemma akept_garr8 : forall W mem W' mem' a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> abyte_kept W mem W' mem' x) ->
  garr8 SEGS (arm W mem) a l -> garr8 SEGS (arm W' mem') a l.
Proof.
  intros W mem W' mem' a l HK Hg. apply (garr8_frame SEGS (arm W mem) (arm W' mem') a l Hg).
  intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (proj1 (HK x Hx)).
Qed.
Lemma akept_awr : forall W mem W' mem' a n,
  (forall x, a <= x < a + n -> abyte_kept W mem W' mem' x) -> awr W mem a n -> awr W' mem' a n.
Proof. intros W mem W' mem' a n HK Hw i Hi. apply (proj2 (HK (a + i) ltac:(lia))). exact (Hw i Hi). Qed.

Ltac w_infp := repeat (first [left; reflexivity | right]).

(* the bytes a list's predicate reads, and the blocks it names *)
Definition alist_fp (LA : Z) (l : hlist) : list (Z * Z) :=
  (LA, LA + 16) ::
  (if hl_cap l =? 0 then [] else [gfp (hl_v l) (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))]) ++
  map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l).
Definition alist_blks (l : hlist) : list (Z * Z) :=
  (if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]) ++
  map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l).
Lemma alist_at_kept : forall ly S W mem ly' S' W' mem' LA l lines,
  alist_at ly S W mem LA l lines ->
  akept W mem W' mem' (alist_fp LA l) ->
  (forall b, In b (alist_blks l) -> In b (ablocks B ly' S')) ->
  alist_at ly' S' W' mem' LA l lines.
Proof.
  intros ly S W mem ly' S' W' mem' LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HK HB.
  assert (KH : forall x, LA <= x < LA + 16 -> abyte_kept W mem W' mem' x)
    by (intros x Hx; apply (HK (LA, LA + 16)); [left; reflexivity | exact Hx]).
  split; [apply (akept_vm W mem); [intros x Hx; apply KH; cbn in Hx; lia | exact H1]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KH; cbn in Hx; lia | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KH; cbn in Hx; lia | exact H3]|].
  split; [apply (akept_awr W mem); [exact KH | exact H4]|].
  split; [exact H5|].
  split.
  { destruct H6 as [H6 | (Hc & Hin & Hj & Hg)]; [left; exact H6|right].
    assert (Ec : (hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [exact Hc|].
    split; [apply HB; unfold alist_blks; rewrite Ec; apply in_or_app; left; left; reflexivity|].
    split; [exact Hj|].
    apply (akept_garr8 W mem); [|exact Hg].
    intros x Hx. apply (HK (gfp (hl_v l) (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l)))); [|exact Hx].
    unfold alist_fp. rewrite Ec. right. apply in_or_app. left. left. reflexivity. }
  split; [exact H7|]. split; [exact H8|].
  rewrite Forall_forall in H9 |- *. intros r Hr. destruct (H9 r Hr) as (R1 & R2 & R3 & R4).
  split; [apply HB; unfold alist_blks; apply in_or_app; right;
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Hr|].
  split; [|split; [exact R3 | exact R4]].
  apply (akept_garr8 W mem); [|exact R2].
  intros x Hx. apply (HK (gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0])))); [|exact Hx].
  unfold alist_fp. right. apply in_or_app. right.
  apply (in_map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0])))). exact Hr.
Qed.

Definition asrc_fp (HA : Z) (h : hsrc) : list (Z * Z) :=
  (HA, HA + ASRC) :: gfp (hs_partial h) (bzs (hs_pjunk h)) ::
  alist_fp (HA + 16) (hs_pending h) ++ alist_fp (HA + 64) (hs_expected h) ++ alist_fp (HA + 80) (hs_held h).
Definition asrc_blks (h : hsrc) : list (Z * Z) :=
  (hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks (hs_expected h) ++ alist_blks (hs_held h).
Lemma asrc_at_kept : forall ly S W mem ly' S' W' mem' HA h,
  asrc_at ly S W mem HA h ->
  akept W mem W' mem' (asrc_fp HA h) ->
  (forall b, In b (asrc_blks h) -> In b (ablocks B ly' S')) ->
  asrc_at ly' S' W' mem' HA h.
Proof.
  intros ly S W mem ly' S' W' mem' HA h
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
     H21 & H22 & H23 & H24) HK HB.
  assert (KH : forall x, HA <= x < HA + 96 -> abyte_kept W mem W' mem' x)
    by (intros x Hx; apply (HK (HA, HA + ASRC)); [left; reflexivity | exact Hx]).
  assert (Hvm : forall a n v, HA <= a -> a + Z.of_nat n <= HA + 96 ->
    val_mem SEGS (arm W mem) a n v -> val_mem SEGS (arm W' mem') a n v)
    by (intros a n v Ha Hn Hv; apply (akept_vm W mem); [intros x Hx; apply KH; lia | exact Hv]).
  split; [apply Hvm; [lia | cbn; lia | exact H1]|].
  split; [apply Hvm; [lia | cbn; lia | exact H2]|].
  split; [apply Hvm; [lia | cbn; lia | exact H3]|].
  split; [apply Hvm; [lia | cbn; lia | exact H4]|].
  split; [apply (akept_awr W mem); [exact KH | exact H5]|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  split; [apply (alist_at_kept ly S W mem); [exact H10
    | eapply akept_sub; [exact HK | intros r Hr; right; right; apply in_or_app; left; exact Hr]
    | intros b Hb; apply HB; right; apply in_or_app; left; exact Hb]|].
  split; [apply Hvm; [lia | cbn; lia | exact H11]|].
  split; [apply Hvm; [lia | cbn; lia | exact H12]|].
  split; [apply Hvm; [lia | cbn; lia | exact H13]|].
  split; [apply Hvm; [lia | cbn; lia | exact H14]|].
  split; [exact H15|]. split; [exact H16|]. split; [exact H17|].
  split; [apply HB; left; reflexivity|].
  split; [exact H19|].
  split; [apply (akept_garr8 W mem); [intros x Hx; apply (HK (gfp (hs_partial h) (bzs (hs_pjunk h))));
    [right; left; reflexivity | exact Hx] | exact H20]|].
  split; [exact H21|].
  split; [apply (alist_at_kept ly S W mem); [exact H22
    | eapply akept_sub; [exact HK | intros r Hr; right; right; apply in_or_app; right; apply in_or_app; left; exact Hr]
    | intros b Hb; apply HB; right; apply in_or_app; right; apply in_or_app; left; exact Hb]|].
  split; [apply (alist_at_kept ly S W mem); [exact H23
    | eapply akept_sub; [exact HK | intros r Hr; right; right; apply in_or_app; right; apply in_or_app; right; exact Hr]
    | intros b Hb; apply HB; right; apply in_or_app; right; apply in_or_app; right; exact Hb]|].
  exact H24.
Qed.

Definition aentry_fp (e : rentry) : list (Z * Z) :=
  (if re_cap e =? 0 then [] else [gfp (re_buf e) (bzs (re_U e ++ re_junk e))]) ++
  gfp (re_hp e) (bzs (key_ptrs (re_keys e))) ::
  map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e).
Lemma aentry_ok_kept : forall ly S W mem ly' S' W' mem' e,
  aentry_ok ly S W mem e ->
  akept W mem W' mem' (aentry_fp e) ->
  (forall b, In b (aentry_blks e) -> In b (ablocks B ly' S')) ->
  aentry_ok ly' S' W' mem' e.
Proof.
  intros ly S W mem ly' S' W' mem' e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15)
    HK HB.
  do 9 (split; [assumption|]).
  split.
  { destruct H10 as [H10 | (Hc & Hin & Hj & Hg)]; [left; exact H10|right].
    assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [exact Hc|].
    split; [apply HB; unfold aentry_blks; rewrite Ec; left; reflexivity|].
    split; [exact Hj|].
    apply (akept_garr8 W mem); [|exact Hg].
    intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
    unfold aentry_fp. rewrite Ec. left. reflexivity. }
  split; [exact H11|].
  split.
  { destruct H12 as [H12 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H12|right].
    assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
    split; [exact Hz|].
    split; [apply HB; unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity|].
    split; [exact Hk1|]. split; [exact Hk2|].
    apply (akept_garr8 W mem); [|exact Hg].
    intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [|exact Hx].
    unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
  split; [exact H13|]. split; [exact H14|].
  rewrite Forall_forall in H15 |- *. intros k Hk. destruct (H15 k Hk) as (K1 & K2 & K3).
  split; [apply HB; unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
  split; [|exact K3].
  apply (akept_garr8 W mem); [|exact K2].
  intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
  unfold aentry_fp. apply in_or_app. right. right.
  apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

Definition arelay_fp (RG : rep_globals) (G : Z) (es : list rentry) : list (Z * Z) :=
  (rg_src RG, rg_src RG + 8) :: (rg_nsrc RG, rg_nsrc RG + 4) :: (rg_capsrc RG, rg_capsrc RG + 4) ::
  (G, G + ATABLE) :: concat (map aentry_fp es).
Definition arelay_blks (G : Z) (es : list rentry) : list (Z * Z) := (G, ATABLE) :: concat (map aentry_blks es).
Lemma arelay_at_kept : forall RG ly S W mem ly' S' W' mem' G es,
  arelay_at RG ly S W mem G es ->
  akept W mem W' mem' (arelay_fp RG G es) ->
  (forall b, In b (arelay_blks G es) -> In b (ablocks B ly' S')) ->
  arelay_at RG ly' S' W' mem' G es.
Proof.
  intros RG ly S W mem ly' S' W' mem' G es (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) HK HB.
  assert (KC : forall a n, In (a, a + n) (arelay_fp RG G es) -> forall x, a <= x < a + n -> abyte_kept W mem W' mem' x)
    by (intros a n Hin x Hx; exact (HK (a, a + n) Hin x Hx)).
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_src RG) 8); [w_infp | cbn in Hx; lia] | exact H1]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_src RG) 8); w_infp | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_nsrc RG) 4); [w_infp | cbn in Hx; lia] | exact H3]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_nsrc RG) 4); w_infp | exact H4]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_capsrc RG) 4); [w_infp | cbn in Hx; lia] | exact H5]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_capsrc RG) 4); w_infp | exact H6]|].
  split; [exact H7|].
  split; [apply HB; left; reflexivity|].
  split.
  { destruct H9 as (tail & T1 & T2 & T3). exists tail. split; [exact T1|]. split; [exact T2|].
    apply (akept_garr8 W mem); [|exact T3].
    intros x Hx. unfold bzs in Hx. rewrite length_map, T2 in Hx. apply (KC G ATABLE); [w_infp | exact Hx]. }
  split; [|exact H11].
  rewrite Forall_forall in H10 |- *. intros e He.
  apply (aentry_ok_kept ly S W mem); [exact (H10 e He)| |].
  - eapply akept_sub; [exact HK|]. intros r Hr. right; right; right; right.
    apply in_concat. exists (aentry_fp e). split; [apply (in_map aentry_fp); exact He | exact Hr].
  - intros b Hb. apply HB. right.
    apply in_concat. exists (aentry_blks e). split; [apply (in_map aentry_blks); exact He | exact Hb].
Qed.

Definition aout_fp (RG : rep_globals) (cap out : Z) : list (Z * Z) :=
  (rg_send_max RG, rg_send_max RG + 8) :: (rg_nout RG, rg_nout RG + 8) :: (rg_capout RG, rg_capout RG + 8) ::
  (rg_out RG, rg_out RG + 8) :: (rg_client RG, rg_client RG + 4) :: (rg_client_broken RG, rg_client_broken RG + 1) ::
  (rg_send_dead RG, rg_send_dead RG + 1) :: (rg_send_eintr RG, rg_send_eintr RG + 1) ::
  (as_errno B, as_errno B + 4) ::
  (if cap =? 0 then [] else [(out, out + cap)]).
Definition aout_blks (cap out : Z) : list (Z * Z) := if cap =? 0 then [] else [(out, cap)].
Lemma aout_at_kept : forall RG ly S W mem ly' S' W' mem' c O mx no cap out,
  aout_at RG ly S W mem c O mx no cap out ->
  akept W mem W' mem' (aout_fp RG cap out) ->
  (forall b, In b (aout_blks cap out) -> In b (ablocks B ly' S')) ->
  aout_at RG ly' S' W' mem' c O mx no cap out.
Proof.
  intros RG ly S W mem ly' S' W' mem' c O mx no cap out
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HB.
  assert (KC : forall a n, In (a, a + n) (aout_fp RG cap out) -> forall x, a <= x < a + n -> abyte_kept W mem W' mem' x)
    by (intros a n Hin x Hx; exact (HK (a, a + n) Hin x Hx)).
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_max RG) 8); [w_infp | cbn in Hx; lia] | exact H1]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_send_max RG) 8); w_infp | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_nout RG) 8); [w_infp | cbn in Hx; lia] | exact H3]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_nout RG) 8); w_infp | exact H4]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_capout RG) 8); [w_infp | cbn in Hx; lia] | exact H5]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_capout RG) 8); w_infp | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_out RG) 8); [w_infp | cbn in Hx; lia] | exact H7]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_out RG) 8); w_infp | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_client RG) 4); [w_infp | cbn in Hx; lia] | exact H9]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_client RG) 4); w_infp | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_client_broken RG) 1); [w_infp | cbn in Hx; lia] | exact H11]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_client_broken RG) 1); w_infp | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_dead RG) 1); [w_infp | cbn in Hx; lia] | exact H13]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_send_dead RG) 1); w_infp | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [w_infp | cbn in Hx; lia] | exact H15]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_send_eintr RG) 1); w_infp | exact H16]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (as_errno B) 4); [w_infp | cbn in Hx; lia] | exact H17]|].
  split; [apply (akept_awr W mem); [apply (KC (as_errno B) 4); w_infp | exact H18]|].
  do 7 (split; [assumption|]).
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|]. split; [exact Hno|].
  split; [apply HB; unfold aout_blks; rewrite Ec; left; reflexivity|].
  exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  apply (KC out cap); [unfold aout_fp; rewrite Ec; w_infp | lia].
Qed.

Lemma agone_at_kept : forall RG W mem W' mem' gn,
  agone_at RG W mem gn -> akept W mem W' mem' [(rg_gone RG, rg_gone RG + 1)] -> agone_at RG W' mem' gn.
Proof.
  intros RG W mem W' mem' gn (H1 & H2 & H3) HK.
  split; [apply (akept_vm W mem); [intros x Hx; apply (HK (rg_gone RG, rg_gone RG + 1)); [left; reflexivity | cbn in Hx |- *; lia] | exact H1]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (HK (rg_gone RG, rg_gone RG + 1)); [left; reflexivity | exact Hx] | exact H2] | exact H3].
Qed.
Lemma alock_at_kept : forall RG W mem W' mem' held,
  alock_at RG W mem held -> akept W mem W' mem' [(rg_lock RG, rg_lock RG + 12)] -> alock_at RG W' mem' held.
Proof.
  intros RG W mem W' mem' held (H1 & H2 & H3 & H4) HK.
  assert (KH : forall x, rg_lock RG <= x < rg_lock RG + 12 -> abyte_kept W mem W' mem' x)
    by (intros x Hx; apply (HK (rg_lock RG, rg_lock RG + 12)); [left; reflexivity | exact Hx]).
  split; [apply (akept_vm W mem); [intros x Hx; apply KH; cbn in Hx; lia | exact H1]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KH; cbn in Hx; lia | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KH; cbn in Hx; lia | exact H3]|].
  apply (akept_awr W mem); [exact KH | exact H4].
Qed.
Lemma awake_at_kept : forall RG W mem W' mem',
  awake_at RG W mem -> akept W mem W' mem' [(rg_wake RG + 4, rg_wake RG + 8)] -> awake_at RG W' mem'.
Proof.
  intros RG W mem W' mem' H1 HK.
  apply (akept_vm W mem); [intros x Hx; apply (HK (rg_wake RG + 4, rg_wake RG + 8)); [left; reflexivity | cbn in Hx |- *; lia] | exact H1].
Qed.

End b.
End a.
