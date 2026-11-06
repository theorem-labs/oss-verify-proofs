(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths, module names and numbers changed; 892 of its 1130 lines of code are new or changed and 693 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from fuzz_grant's lib/A/Prog/GrantEntrySeat.v (a working branch
   b47e973d564) for libreac/fuzz_boxreg B (fuzz_boxreg.asan-ubsan) over BoxBLxDefs.v: the context is BoxBLxDefs.v's
   lxcx / lx_base / lx_body; the environment is built here from the registers at the seat (the grant context's c_E0
   has no boxreg counterpart); the machine frame's saved words, its spill area, the class-3 side-stack frame
   (512 bytes, flag word at F + 504) and its 64 shadow bytes take boxreg B's numbers; the GOT / shadow-cell regions
   of the prologue are not part of a cut (no phase after the prologue reads them) and were dropped; the landing reads
   the memory facts from the phase's own lemmas (lx_saved_of_ss, lx_shadow_of_ss, lx_word_of_ss) instead of from a
   fixed region shape, and the shent / atom-fact lemmas a token walk needs were added.

   The seat and the landing of a phase of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput, stated once for all
   of its phases, at ANY pc of the body (a cut of BoxBLxDefs.v or a phase's own loop head).

   A phase carries its machine state as `lx_body` and its own facts; the walk engine wants a symbolic state
   (`st_ok_pi`). `lx_seat` turns the first into the second, and `lx_land` turns the symbolic state back into
   `lx_body`.

   The environment (`lx_env cx fp regs ex`): atoms 0 .. 31 are the registers at the seat (regs = ms_regs ms3);
   32 is SHADOW_OFF; 33 .. 45 the caller's saved words (33 ra, 34 s0, 35 s1, 36 .. 45 s2 .. s11); 46 the frame F
   on the side stack; 47 its flag word's address; 48 up the phase's own words `ex`; 240 .. 511 the image (Eimg).
   The registers (`lx_sr ov`): sr_atoms with the overrides ov; LX_OV makes s1 the atom of sp (2) and s2 the atom of
   SHADOW_OFF (32), LX_OVP also s5 = F + 64 (prev).
   The regions (`lx_regions`), by index: 0 the saved words (base s0 = sp0, read-only); 1 the spill slots
   sp1 + 0 .. sp1 + 0x97 (base sp, writable); 2 the frame (base 46, writable, flag word chunk at 504); 3 its shadow
   bytes (base s6, window [wlo, whi), which may be empty); then the phase's `extra`. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxSeat.v; 171 of its 210 lines of code are new or changed and 1091 lines of the source are left out. *)
(* The cuts inside the case op & 3 = 0 (declare, fuzz_boxreg.c:213-286) of the B walk of fuzz_boxreg's
   LLVMFuzzerTestOneInput (fuzz_boxreg.asan-ubsan 0x8034c .. 0x80b08), between the phase cuts LI_T 0 and LI_K of
   BoxBLxDefs.v.

   The case calls read_name (&in) at 0x80520, range_free (&prev, base, nch, fabric) at 0x80568 or, in the inlined
   lowest_free loop, at 0x80940, reac_boxreg_declare (r, nch, given, base) at 0x805a0, bcmp (row mac, ZERO, 6) at
   0x8062c, strncmp (row name, given or "", 31) at 0x80698 and free (name) at 0x808f4. The walk is cut after each
   call and where the ways of computing `want` meet, so that each piece is one walk from a seat to the next call:
     N   0x80524  read_name returned the name (a0);
     RF  0x8056c  range_free returned (a0), base >= 0;
     L   0x80930  the head of the lowest_free loop (s3 = the candidate base), base < 0;
     LR  0x80944  range_free returned in the loop (a0);
     W   0x80584  `want` is in the slot 0x20, s3 = the name;
     D   0x805a4  reac_boxreg_declare returned idx (a0);
     BC  0x80630  bcmp of the new row's MAC with ZERO returned 0 (a placed row only);
     SC  0x8069c  strncmp of the new row's name returned 0 (a placed row only);
     F   0x808f0  every check is passed; free (name) follows;
     FR  0x808f8  free returned.
   Each cut keeps the facts of LI_T the rest of the turn needs (c0_com), the table before the turn (bs, also in
   prev) and the case's own values, from the input left after the op byte (Pau's lib/Prog/
   LLVMFuzzerTestOneInput_case0.v c0_nch / c0_base / c0_used, read_name_c.v rn_k, LLVMFuzzerTestOneInput_rn.v
   nm_str). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h BoxBLxDefs BoxBLxSeat BoxBReadName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd read_name_c range_free_c
  lowest_free_c reac_boxreg_declare_c LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the cuts' pcs, as offsets in the listing (address - 0x7ffac) ---- *)
Definition C0P_N : Z := 0x578.    (* 0x80524: read_name returned               *)
Definition C0P_RF : Z := 0x5c0.   (* 0x8056c: range_free returned, base >= 0   *)
Definition C0P_W : Z := 0x5d8.    (* 0x80584: want in the slot 0x20            *)
Definition C0P_D : Z := 0x5f8.    (* 0x805a4: reac_boxreg_declare returned     *)
Definition C0P_BC : Z := 0x684.   (* 0x80630: bcmp returned                    *)
Definition C0P_SC : Z := 0x6f0.   (* 0x8069c: strncmp returned                 *)
Definition C0P_F : Z := 0x944.    (* 0x808f0: free (name) follows              *)
Definition C0P_FR : Z := 0x94c.   (* 0x808f8: free returned                    *)
Definition C0P_L : Z := 0x984.    (* 0x80930: lowest_free loop head            *)
Definition C0P_LR : Z := 0x998.   (* 0x80944: range_free returned in the loop  *)

(* ---- the case's values, from the input left after the op byte at pos ---- *)
Definition c0_pl0 (pl : list byte) (pos : nat) : list byte := skipn (S pos) pl.
Definition c0_nchv (pl : list byte) (pos : nat) : Z := LLVMFuzzerTestOneInput_case0.c0_nch (c0_pl0 pl pos).
Definition c0_basev (pl : list byte) (pos : nat) : Z := LLVMFuzzerTestOneInput_case0.c0_base (c0_pl0 pl pos).
(* What read_name reads: the input after nch and base. *)
Definition c0_pl2 (pl : list byte) (pos : nat) : list byte := skipn 2 (c0_pl0 pl pos).
Definition c0_nk (pl : list byte) (pos : nat) : Z := read_name_c.rn_k (c0_pl2 pl pos).
(* The name block's bytes, its C string, and the cursor after read_name. *)
Definition c0_nb (pl : list byte) (pos : nat) : list byte :=
  Boxreg.bsub (c0_pl2 pl pos) 1 (c0_nk pl pos) ++ [Z_to_bv 8 0].
Definition c0_s (pl : list byte) (pos : nat) : list Z := LLVMFuzzerTestOneInput_rn.nm_str (c0_nb pl pos).
Definition c0_pos1 (pl : list byte) (pos : nat) : nat :=
  (S pos + Z.to_nat (LLVMFuzzerTestOneInput_case0.c0_used (c0_pl0 pl pos)))%nat.
Definition c0_pos2 (pl : list byte) (pos : nat) : nat :=
  (c0_pos1 pl pos + Z.to_nat (tbread_name_used (c0_pl2 pl pos)))%nat.
(* The name declare gets: NULL when op & 8, else the name. *)
Definition c0_given (op nm : Z) : Z := if Z.land op 8 =? 0 then nm else 0.
Definition c0_gs (pl : list byte) (pos : nat) (op : Z) : list Z := if Z.land op 8 =? 0 then c0_s pl pos else [].
(* The table after a placed declare (the contract's bytes). *)
Definition c0_placed (bs : list byte) (b k p : Z) (s : list Z) : list byte :=
  BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b k p s).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).

(* Any byte, and any word, the memory view holds is in range (so a spill slot's value is a 64-bit word). *)
Lemma c0_aview_byte : forall (H : word -> bool) m a v, aview SEGS H m a = Some v -> 0 <= v < 256.
Proof.
  intros H m a v Hv. unfold aview in Hv.
  destruct (mbyte SEGS (mrestrict H m) a) as [b|]; cbn [option_map] in Hv; [|discriminate].
  injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as R.
  change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma c0_rdword_range : forall (H : word -> bool) m a v, rdword (aview SEGS H m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros H m a v Hv. unfold rdword in Hv.
  destruct (aview SEGS H m a) as [b0|] eqn:E0; [|discriminate].
  destruct (aview SEGS H m (a + 1)) as [b1|] eqn:E1; [|discriminate].
  destruct (aview SEGS H m (a + 2)) as [b2|] eqn:E2; [|discriminate].
  destruct (aview SEGS H m (a + 3)) as [b3|] eqn:E3; [|discriminate].
  destruct (aview SEGS H m (a + 4)) as [b4|] eqn:E4; [|discriminate].
  destruct (aview SEGS H m (a + 5)) as [b5|] eqn:E5; [|discriminate].
  destruct (aview SEGS H m (a + 6)) as [b6|] eqn:E6; [|discriminate].
  destruct (aview SEGS H m (a + 7)) as [b7|] eqn:E7; [|discriminate].
  injection Hv as <-.
  pose proof (c0_aview_byte H m a b0 E0). pose proof (c0_aview_byte H m (a + 1) b1 E1).
  pose proof (c0_aview_byte H m (a + 2) b2 E2). pose proof (c0_aview_byte H m (a + 3) b3 E3).
  pose proof (c0_aview_byte H m (a + 4) b4 E4). pose proof (c0_aview_byte H m (a + 5) b5 E5).
  pose proof (c0_aview_byte H m (a + 6) b6 E6). pose proof (c0_aview_byte H m (a + 7) b7 E7).
  change (2 ^ 64) with 18446744073709551616. lia.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* The facts of LI_T every cut of the case keeps: the machine state at pc with the frame's shadow as a loop turn
   has it, the turn number, prev = bs (a table that passes Pau's checks), the op byte, the loop's slots, the turn
   number in the slot 0x58 and r->n in the slot 0x48, and s4 = r, s5 = prev, s11 = the fabric. *)
Definition c0_com (i : nat) (cx : lxcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (pc : Z)
  (pos : nat) (r fab op : Z) (bs : list byte) : Prop :=
  lx_body cx fp pc W3 ms3 LSH_iter /\ (i < 64)%nat /\
  lprev cx fp W3 ms3 bs /\ Boxreg.boxreg_inv bs /\ Boxreg.bx_fabric bs = fab /\
  (pos < length (lc_pl cx))%nat /\ op = bv_unsigned (nth pos (lc_pl cx) (Z_to_bv 8 0)) /\ Z.land op 3 = 0 /\
  lslots_loop cx fp W3 ms3 r fab /\ lslot cx W3 ms3 0x58 (Z.of_nat i) /\ lslot cx W3 ms3 0x48 (Boxreg.bx_n bs) /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) /\
  getr (ms_regs ms3) 27 = w64 fab.

(* The name block, while the case holds it (from read_name to free): the journal's events and the allocator's
   spending of the turn so far, the blocks (the caller's, r, the name), the name's bytes and the cursor after
   read_name. *)
Definition c0_nm (i : nat) (cx : lxcx) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (pos : nat) (r nm : Z) : Prop :=
  k <= 2 + 2 * Z.of_nat i /\ acc <= LX_A1 MT + Z.of_nat i * LX_AI MT + mo_malloc MT (c0_nk (lc_pl cx) pos + 1) /\
  ablocks B ly3 S3 = ablocks B (lc_ly cx) (lc_S cx) ++ [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] /\
  aftok [] (ablocks B (lc_ly cx) (lc_S cx)) (nm, c0_nk (lc_pl cx) pos + 1) /\ 4096 <= nm /\
  (forall j, 0 <= j <= c0_nk (lc_pl cx) pos ->
     lview W3 ms3 (nm + j) = Some (bv_unsigned (nth (Z.to_nat j) (c0_nb (lc_pl cx) pos) (Z_to_bv 8 0)))) /\
  lcur cx W3 ms3 (c0_pos2 (lc_pl cx) pos).

(* What the case's registers hold from N to D: s9 = nch, s10 = base (sign-extended), s7 = op, and the slot 0x50 the
   base shifted to the top byte. *)
Definition c0_args (cx : lxcx) (W3 : world SEGS) (ms3 : machine_state) (pos : nat) (op : Z) : Prop :=
  getr (ms_regs ms3) 23 = w64 op /\ getr (ms_regs ms3) 25 = w64 (c0_nchv (lc_pl cx) pos) /\
  getr (ms_regs ms3) 26 = w64 (c0_basev (lc_pl cx) pos) /\
  lslot cx W3 ms3 0x50 ((c0_basev (lc_pl cx) pos * 2 ^ 56) mod 2 ^ 64).

(* N, 0x80524: read_name returned the name in a0. *)
Definition C0_N (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab op nm : Z) (bs : list byte),
  c0_com i cx fp W3 ms3 C0P_N pos r fab op bs /\ c0_nm i cx k acc ly3 S3 W3 ms3 pos r nm /\
  lreg W3 ms3 r bs /\ c0_args cx W3 ms3 pos op /\ getr (ms_regs ms3) 10 = w64 nm.

(* RF, 0x8056c (base >= 0): range_free (prev, base, nch, fabric) returned; s3 = the name in the slot 0x60 too. *)
Definition C0_RF (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab op nm : Z) (bs : list byte),
  c0_com i cx fp W3 ms3 C0P_RF pos r fab op bs /\ c0_nm i cx k acc ly3 S3 W3 ms3 pos r nm /\
  lreg W3 ms3 r bs /\ c0_args cx W3 ms3 pos op /\
  getr (ms_regs ms3) 19 = w64 nm /\ lslot cx W3 ms3 0x60 nm /\
  reac_boxreg_declare_c.box_width_ok (c0_nchv (lc_pl cx) pos) fab /\ Boxreg.bx_n bs < 5 /\
  0 <= c0_basev (lc_pl cx) pos /\
  ((range_free_c.range_free_ok bs (c0_basev (lc_pl cx) pos) (c0_nchv (lc_pl cx) pos) fab /\
    getr (ms_regs ms3) 10 = w64 1) \/
   (~ range_free_c.range_free_ok bs (c0_basev (lc_pl cx) pos) (c0_nchv (lc_pl cx) pos) fab /\
    getr (ms_regs ms3) 10 = w64 0)).

(* L j, 0x80930 (base < 0): the head of the lowest_free loop at the candidate j: no base below j is free; s3 = j,
   s8 = the bound fabric - nch + 1, the slot 0x20 = -1. *)
Definition C0_L (i : nat) (j : Z) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab op nm : Z) (bs : list byte),
  c0_com i cx fp W3 ms3 C0P_L pos r fab op bs /\ c0_nm i cx k acc ly3 S3 W3 ms3 pos r nm /\
  lreg W3 ms3 r bs /\ c0_args cx W3 ms3 pos op /\ lslot cx W3 ms3 0x60 nm /\
  lslot cx W3 ms3 0x20 (2 ^ 64 - 1) /\
  reac_boxreg_declare_c.box_width_ok (c0_nchv (lc_pl cx) pos) fab /\ Boxreg.bx_n bs < 5 /\
  c0_basev (lc_pl cx) pos < 0 /\
  0 <= j <= fab - c0_nchv (lc_pl cx) pos /\
  (forall b, 0 <= b < j -> ~ range_free_c.range_free_ok bs b (c0_nchv (lc_pl cx) pos) fab) /\
  getr (ms_regs ms3) 19 = w64 j /\ getr (ms_regs ms3) 24 = w64 (fab - c0_nchv (lc_pl cx) pos + 1).

(* LR j, 0x80944: range_free (prev, j, nch, fabric) returned in the loop. *)
Definition C0_LR (i : nat) (j : Z) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab op nm : Z) (bs : list byte),
  c0_com i cx fp W3 ms3 C0P_LR pos r fab op bs /\ c0_nm i cx k acc ly3 S3 W3 ms3 pos r nm /\
  lreg W3 ms3 r bs /\ c0_args cx W3 ms3 pos op /\ lslot cx W3 ms3 0x60 nm /\
  lslot cx W3 ms3 0x20 (2 ^ 64 - 1) /\
  reac_boxreg_declare_c.box_width_ok (c0_nchv (lc_pl cx) pos) fab /\ Boxreg.bx_n bs < 5 /\
  c0_basev (lc_pl cx) pos < 0 /\
  0 <= j <= fab - c0_nchv (lc_pl cx) pos /\
  (forall b, 0 <= b < j -> ~ range_free_c.range_free_ok bs b (c0_nchv (lc_pl cx) pos) fab) /\
  getr (ms_regs ms3) 19 = w64 j /\ getr (ms_regs ms3) 24 = w64 (fab - c0_nchv (lc_pl cx) pos + 1) /\
  ((range_free_c.range_free_ok bs j (c0_nchv (lc_pl cx) pos) fab /\ getr (ms_regs ms3) 10 = w64 1) \/
   (~ range_free_c.range_free_ok bs j (c0_nchv (lc_pl cx) pos) fab /\ getr (ms_regs ms3) 10 = w64 0)).

(* W, 0x80584: Pau's `want` (c0_want) is in the slot 0x20; s3 = the name. *)
Definition C0_W (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab op nm want : Z) (bs : list byte),
  c0_com i cx fp W3 ms3 C0P_W pos r fab op bs /\ c0_nm i cx k acc ly3 S3 W3 ms3 pos r nm /\
  lreg W3 ms3 r bs /\ c0_args cx W3 ms3 pos op /\
  getr (ms_regs ms3) 19 = w64 nm /\ lslot cx W3 ms3 0x60 nm /\
  LLVMFuzzerTestOneInput_case0.c0_want bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) want /\
  -1 <= want <= 40 /\ lslot cx W3 ms3 0x20 (want mod 2 ^ 64).

(* D, 0x805a4: reac_boxreg_declare returned idx in a0; s8 = op & 8; the table holds bs' as the contract gives it:
   refused (idx = -1, bs' = bs) or placed (idx = n, the new row). *)
Definition C0_D (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab op nm want : Z) (bs : list byte),
  c0_com i cx fp W3 ms3 C0P_D pos r fab op bs /\ c0_nm i cx k acc ly3 S3 W3 ms3 pos r nm /\
  c0_args cx W3 ms3 pos op /\ lslot cx W3 ms3 0x60 nm /\
  LLVMFuzzerTestOneInput_case0.c0_want bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) want /\
  -1 <= want <= 40 /\ lslot cx W3 ms3 0x20 (want mod 2 ^ 64) /\
  getr (ms_regs ms3) 24 = w64 (Z.land op 8) /\
  ((reac_boxreg_declare_c.declare_refused bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) /\
    lreg W3 ms3 r bs /\ getr (ms_regs ms3) 10 = w64 (-1)) \/
   (exists b p, reac_boxreg_declare_c.declare_placed bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) b p /\
    lreg W3 ms3 r (c0_placed bs b (c0_nchv (lc_pl cx) pos) p (c0_gs (lc_pl cx) pos op)) /\
    getr (ms_regs ms3) 10 = w64 (Boxreg.bx_n bs))).

(* BC, 0x80630 (a placed row only): bcmp returned 0; s3 = idx = n, s7 = the row r + 56 n. *)
Definition C0_BC (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab op nm want b p : Z) (bs : list byte),
  c0_com i cx fp W3 ms3 C0P_BC pos r fab op bs /\ c0_nm i cx k acc ly3 S3 W3 ms3 pos r nm /\
  getr (ms_regs ms3) 25 = w64 (c0_nchv (lc_pl cx) pos) /\
  getr (ms_regs ms3) 26 = w64 (c0_basev (lc_pl cx) pos) /\
  lslot cx W3 ms3 0x50 ((c0_basev (lc_pl cx) pos * 2 ^ 56) mod 2 ^ 64) /\ lslot cx W3 ms3 0x60 nm /\
  LLVMFuzzerTestOneInput_case0.c0_want bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) want /\
  -1 <= want <= 40 /\ lslot cx W3 ms3 0x20 (want mod 2 ^ 64) /\
  getr (ms_regs ms3) 24 = w64 (Z.land op 8) /\
  reac_boxreg_declare_c.declare_placed bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) b p /\
  lreg W3 ms3 r (c0_placed bs b (c0_nchv (lc_pl cx) pos) p (c0_gs (lc_pl cx) pos op)) /\
  getr (ms_regs ms3) 10 = w64 0 /\ getr (ms_regs ms3) 19 = w64 (Boxreg.bx_n bs) /\
  getr (ms_regs ms3) 23 = w64 (r + 56 * Boxreg.bx_n bs).

(* SC, 0x8069c (a placed row only): strncmp returned 0; s3 = idx = n, s7 = the row, s9 = the row's base field. *)
Definition C0_SC (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab op nm want b p : Z) (bs : list byte),
  c0_com i cx fp W3 ms3 C0P_SC pos r fab op bs /\ c0_nm i cx k acc ly3 S3 W3 ms3 pos r nm /\
  getr (ms_regs ms3) 26 = w64 (c0_basev (lc_pl cx) pos) /\ lslot cx W3 ms3 0x60 nm /\
  LLVMFuzzerTestOneInput_case0.c0_want bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) want /\
  -1 <= want <= 40 /\ lslot cx W3 ms3 0x20 (want mod 2 ^ 64) /\
  reac_boxreg_declare_c.declare_placed bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) b p /\
  lreg W3 ms3 r (c0_placed bs b (c0_nchv (lc_pl cx) pos) p (c0_gs (lc_pl cx) pos op)) /\
  getr (ms_regs ms3) 10 = w64 0 /\ getr (ms_regs ms3) 19 = w64 (Boxreg.bx_n bs) /\
  getr (ms_regs ms3) 23 = w64 (r + 56 * Boxreg.bx_n bs) /\
  getr (ms_regs ms3) 25 = w64 (r + 56 * Boxreg.bx_n bs + 8).

(* F, 0x808f0: every check is passed: r holds bs', which passes Pau's checks and keeps prev's rows. *)
Definition C0_F (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab op nm : Z) (bs bs' : list byte),
  c0_com i cx fp W3 ms3 C0P_F pos r fab op bs /\ c0_nm i cx k acc ly3 S3 W3 ms3 pos r nm /\
  lslot cx W3 ms3 0x60 nm /\
  lreg W3 ms3 r bs' /\ Boxreg.boxreg_inv bs' /\ Boxreg.bx_fabric bs' = fab /\ lkept bs bs' (-1).

(* FR, 0x808f8: free (name) returned: the turn's events and spending are those of LI_K. *)
Definition C0_FR (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab op : Z) (bs bs' : list byte),
  c0_com i cx fp W3 ms3 C0P_FR pos r fab op bs /\
  k <= 3 + 2 * Z.of_nat i /\ acc <= LX_A1 MT + (Z.of_nat i + 1) * LX_AI MT /\
  lblk B cx ly3 S3 r /\ lcur cx W3 ms3 (c0_pos2 (lc_pl cx) pos) /\
  lreg W3 ms3 r bs' /\ Boxreg.boxreg_inv bs' /\ Boxreg.bx_fabric bs' = fab /\ lkept bs bs' (-1).

End c.
End b.
End a.
