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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxSeat.v, with its module paths and module names changed; 184 of its 237 lines of code are new or changed and 1077 lines of the source are left out. *)
(* The cuts inside case 1 of the switch of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput (op & 3 = 1, the
   "join" operation of fuzz/fuzz_boxreg.c:312-373), and the model facts the case needs.

   BoxBLxDefs.v fixes the two ends of the phase: LI_T 1 i at 0x8034c and LI_K i at 0x80b08. The case runs through
   two loops, so this file states the invariant at every cut inside it; the segments between the cuts are proved
   in BoxBLxCase1S*.v and BoxBLxCase1.v composes them into lx_case1.

   The pcs inside the case (offsets in the listing, address - 0x7ffac):
   - C1_P1 0x4d8 (0x80484): the switch chose case 1; the turn number is at sp1 + 0x58 and n_before at sp1 + 0x48;
   - C1_P2 0x728 (0x806d4): read_mac left the six MAC bytes in the frame and the inlined fuzz_u8 left nch at
     sp1 + 0x50;
   - C1_P3 0x754 (0x80700): bcmp (mac, ZERO, 6) left `nonzero` at sp1 + 0x60, lf = -1 at sp1 + 0x20, held and
     bind are -1 and s7 holds prev->n;
   - C1_P4 0x76c (0x80718): the head of the scan of prev's rows, after j rows;
   - C1_P5 0x830 (0x807dc): the scan is done; held is in s9 and bind in s3;
   - C1_P6 0x9d8 (0x80984): the head of the inlined lowest_free loop, at the candidate base b;
   - C1_P7 0x9fc (0x809a8): `want` is in s9 and lf at sp1 + 0x20; reac_boxreg_find and reac_boxreg_add follow.

   The registers the case keeps (x-numbers): s3 = 19, s4 = 20, s5 = 21, s6 = 22, s7 = 23, s8 = 24, s9 = 25,
   s10 = 26, s11 = 27. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBCJ.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import
BoxBReacBoxregInit BoxBCheck BoxBReadMac BoxBReadName BoxBRangeFree BoxBReacBoxregFind
BoxBReacBoxregDeclare BoxBReacBoxregAdd BoxBReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require
Boxreg reac_boxreg_add_c reac_boxreg_find_c lowest_free_base_c lowest_free_c range_free_c
reac_boxreg_add_inv LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_case1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module LC1 := LLVMFuzzerTestOneInput_case1.

(* ---- the pcs of the cuts inside the case ---- *)
Definition C1_P1 : Z := 0x4d8.
Definition C1_P2 : Z := 0x728.
Definition C1_P3 : Z := 0x754.
Definition C1_P4 : Z := 0x76c.
Definition C1_P5 : Z := 0x830.
Definition C1_P6 : Z := 0x9d8.
Definition C1_P7 : Z := 0x9fc.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The model facts of the case, over Pau's plain model: what the two scan trackers mean when the scan is done,
   what the inlined lowest_free loop proves, and what the registry looks like at the cut LP_K. *)

(* `held` (s9) at the end of the scan: a row that holds the MAC, or none. *)
Lemma lxc1_held_pos : forall bs M nz h,
  LC1.c1_sh bs M nz (Boxreg.bx_n bs) h -> 0 <= h -> reac_boxreg_add_c.add_held bs M h.
Proof.
  intros bs M nz h [(E & _) | (_ & Hh & Hm & Hn)] H0; [lia|].
  split; [exact Hh|]. split; [exact Hm | exact Hn].
Qed.

Lemma lxc1_held_neg : forall bs M nz h,
  LC1.c1_sh bs M nz (Boxreg.bx_n bs) h -> h < 0 -> nz <> 0 -> reac_boxreg_add_c.add_none_held bs M.
Proof.
  intros bs M nz h [(_ & [E | N]) | (_ & Hh & _)] Hneg Hnz; [contradiction | exact N | lia].
Qed.

(* `bind` (s3) at the end of the scan: the first unbound row of this width, or none. *)
Lemma lxc1_unb_pos : forall bs k u,
  LC1.c1_su bs k (Boxreg.bx_n bs) u -> 0 <= u -> reac_boxreg_add_c.add_unbound bs k u.
Proof.
  intros bs k u [(E & _) | (Hu & Hm & Hk & Hn)] H0; [lia|].
  split; [exact Hu|]. split; [exact Hm|]. split; [exact Hk | exact Hn].
Qed.

Lemma lxc1_unb_neg : forall bs k u,
  LC1.c1_su bs k (Boxreg.bx_n bs) u -> u < 0 -> reac_boxreg_add_c.add_none_unbound bs k.
Proof.
  intros bs k u [(_ & N) | (Hu & _)] Hneg; [exact N | lia].
Qed.

(* The bounds the two trackers keep: a tracker is -1 or a row that was scanned. *)
Lemma lxc1_sh_bound : forall bs M nz j h, LC1.c1_sh bs M nz j h -> -1 <= h < Z.max j 1.
Proof.
  intros bs M nz j h [(-> & _) | (_ & Hh & _)]; lia.
Qed.

Lemma lxc1_su_bound : forall bs k j u, LC1.c1_su bs k j u -> -1 <= u < Z.max j 1.
Proof.
  intros bs k j u [(-> & _) | (Hu & _)]; lia.
Qed.

(* The inlined lowest_free loop (0x80960 .. 0x809a0): no base below i leaves the asked range free. *)
Definition lxc1_lfinv (bs : list byte) (nch fab i : Z) : Prop :=
  forall b, 0 <= b < i -> ~ range_free_c.range_free_ok bs b nch fab.

Lemma lxc1_lf0 : forall bs nch fab, lxc1_lfinv bs nch fab 0.
Proof. intros bs nch fab b Hb. lia. Qed.

Lemma lxc1_lf_step : forall bs nch fab i,
  lxc1_lfinv bs nch fab i -> ~ range_free_c.range_free_ok bs i nch fab -> lxc1_lfinv bs nch fab (i + 1).
Proof.
  intros bs nch fab i HI HN b Hb. destruct (Z.eq_dec b i) as [-> | Hne]; [exact HN | apply HI; lia].
Qed.

Lemma lxc1_lf_hit : forall bs nch fab i,
  lxc1_lfinv bs nch fab i -> range_free_c.range_free_ok bs i nch fab ->
  lowest_free_c.lowest_free_res bs nch fab i.
Proof.
  intros bs nch fab i HI HR. right. pose proof HR as (Hr & _).
  split; [exact Hr|]. split; [exact HR | exact HI].
Qed.

Lemma lxc1_lf_miss : forall bs nch fab i,
  lxc1_lfinv bs nch fab i -> fab - nch < i -> lowest_free_c.lowest_free_res bs nch fab (-1).
Proof.
  intros bs nch fab i HI Hi. left. split; [reflexivity|]. intros b Hb. apply HI. lia.
Qed.

(* The registry at LP_K: add keeps Pau's checks, the fabric and every row of prev, and renames nothing. *)
Lemma lxc1_add_keeps : forall bs M nch z bs',
  Boxreg.boxreg_inv bs -> length M = 6%nat -> reac_boxreg_add_c.add_out bs M nch z bs' ->
  Boxreg.boxreg_inv bs' /\ Boxreg.bx_fabric bs' = Boxreg.bx_fabric bs /\ lkept bs bs' (-1).
Proof.
  intros bs M nch z bs' HI HM HA.
  split; [exact (reac_boxreg_add_inv.reac_boxreg_add_keeps_inv_holds bs M bs' nch z HI HM HA)|].
  split; [exact (LC1.c1_add_fab bs M nch z bs' HI HM HA) | exact (LC1.c1_kept bs M nch z bs' HI HM HA)].
Qed.

(* The six MAC bytes read_mac leaves: tbread_mac_out is six bytes long whichever branch it took. *)
Lemma lxc1_mac_len : forall full pl, length (tbread_mac_out full pl) = 6%nat.
Proof.
  intros full pl. unfold tbread_mac_out. destruct (full =? 0).
  - rewrite length_app. unfold tbread_mac_base. rewrite length_map. cbn [length].
    rewrite length_firstn, length_app. cbn [length]. lia.
  - rewrite length_firstn, length_app, repeat_length. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).

(* Any byte, and any word, the memory view holds is in range (so a spill slot's value is a 64-bit word). *)
Lemma c1_aview_byte : forall (H : word -> bool) m a v, aview SEGS H m a = Some v -> 0 <= v < 256.
Proof.
  intros H m a v Hv. unfold aview in Hv.
  destruct (mbyte SEGS (mrestrict H m) a) as [b|]; cbn [option_map] in Hv; [|discriminate].
  injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as R.
  change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma c1_rdword_range : forall (H : word -> bool) m a v, rdword (aview SEGS H m) a = Some v -> 0 <= v < 2 ^ 64.
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
  pose proof (c1_aview_byte H m a b0 E0). pose proof (c1_aview_byte H m (a + 1) b1 E1).
  pose proof (c1_aview_byte H m (a + 2) b2 E2). pose proof (c1_aview_byte H m (a + 3) b3 E3).
  pose proof (c1_aview_byte H m (a + 4) b4 E4). pose proof (c1_aview_byte H m (a + 5) b5 E5).
  pose proof (c1_aview_byte H m (a + 6) b6 E6). pose proof (c1_aview_byte H m (a + 7) b7 E7).
  change (2 ^ 64) with 18446744073709551616. lia.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- what every cut inside the case carries ---- *)
(* The machine state of the turn, as LI_T leaves it, with the two spill slots the switch wrote (the turn number
   at sp1 + 0x58, n_before at sp1 + 0x48) and the registry's address and prev's address in s4 and s5. *)
Definition c1_body (i : nat) (cx : lxcx) (fp pc k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (r fab : Z) (bs : list byte) (q : nat) : Prop :=
  lx_body cx fp pc W3 ms3 LSH_iter /\ (i < 64)%nat /\
  k <= 1 + 2 * Z.of_nat i /\ acc <= LX_A1 MT + Z.of_nat i * LX_AI MT /\
  lblk B cx ly3 S3 r /\ lreg W3 ms3 r bs /\ Boxreg.boxreg_inv bs /\ Boxreg.bx_fabric bs = fab /\
  lprev cx fp W3 ms3 bs /\ lcur cx W3 ms3 q /\ lslots_loop cx fp W3 ms3 r fab /\
  lslot cx W3 ms3 0x58 (Z.of_nat i) /\ lslot cx W3 ms3 0x48 (Boxreg.bx_n bs) /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 21 = w64 (lF cx fp + 64).

(* The six bytes of the turn's `mac` array, at F + 32. *)
Definition c1_mac (cx : lxcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (M : list byte) : Prop :=
  length M = 6%nat /\
  forall j, 0 <= j < 6 ->
    lview W3 ms3 (lF cx fp + 32 + j) = Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0))).

(* What the cuts after the width byte carry: the MAC, nch and (from C1_P3 on) the bcmp result `nonzero`. *)
Definition c1_read (cx : lxcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (M : list byte) (nch : Z) : Prop :=
  c1_mac cx fp W3 ms3 M /\ lslot cx W3 ms3 0x50 nch /\ 0 <= nch < 256.

Definition c1_nz (cx : lxcx) (W3 : world SEGS) (ms3 : machine_state) (M : list byte) (nz : Z) : Prop :=
  lslot cx W3 ms3 0x60 nz /\ 0 <= nz < 2 ^ 64 /\ (nz = 0 <-> M = Boxreg.zero6).

(* ---- the invariant at each cut inside the case ---- *)

(* 0x80484: the switch chose case 1 (op & 3 = 1); nothing of the turn is read yet. *)
Definition C1_I1 (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (q : nat) (r fab op : Z) (bs : list byte),
  c1_body i cx fp C1_P1 k acc ly3 S3 W3 ms3 r fab bs q /\
  0 <= op < 256 /\ Z.land op 3 = 1 /\ (q <= length (lc_pl cx))%nat /\
  getr (ms_regs ms3) 19 = w64 1 /\ getr (ms_regs ms3) 23 = w64 op /\
  getr (ms_regs ms3) 24 = w64 (Z.of_nat i) /\ getr (ms_regs ms3) 26 = w64 (Boxreg.bx_n bs) /\
  getr (ms_regs ms3) 27 = w64 fab.

(* 0x806d4: read_mac left the MAC in the frame and the inlined fuzz_u8 left nch at sp1 + 0x50. *)
Definition C1_I2 (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (q : nat) (r fab : Z) (bs M : list byte) (nch : Z),
  c1_body i cx fp C1_P2 k acc ly3 S3 W3 ms3 r fab bs q /\
  c1_read cx fp W3 ms3 M nch.

(* 0x80700: bcmp (mac, ZERO, 6) left `nonzero` at sp1 + 0x60; lf = -1 at sp1 + 0x20; held and bind are -1 and
   s7 holds prev->n. *)
Definition C1_I3 (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (q : nat) (r fab : Z) (bs M : list byte) (nch nz : Z),
  c1_body i cx fp C1_P3 k acc ly3 S3 W3 ms3 r fab bs q /\
  c1_read cx fp W3 ms3 M nch /\ c1_nz cx W3 ms3 M nz /\
  lslot cx W3 ms3 0x20 (2 ^ 64 - 1) /\
  getr (ms_regs ms3) 19 = w64 (-1) /\ getr (ms_regs ms3) 23 = w64 (Boxreg.bx_n bs) /\
  getr (ms_regs ms3) 25 = w64 (-1).

(* 0x80718, the head of the scan of prev's rows: j rows have been scanned, held is h and bind is u. *)
Definition C1_I4 (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (q : nat) (r fab : Z) (bs M : list byte) (nch nz j h u : Z),
  c1_body i cx fp C1_P4 k acc ly3 S3 W3 ms3 r fab bs q /\
  c1_read cx fp W3 ms3 M nch /\ c1_nz cx W3 ms3 M nz /\
  lslot cx W3 ms3 0x20 (2 ^ 64 - 1) /\
  0 <= j < Boxreg.bx_n bs /\ LC1.c1_sh bs M nz j h /\ LC1.c1_su bs nch j u /\
  getr (ms_regs ms3) 19 = w64 u /\ getr (ms_regs ms3) 23 = w64 (Boxreg.bx_n bs) /\
  getr (ms_regs ms3) 24 = w64 j /\ getr (ms_regs ms3) 25 = w64 h /\
  getr (ms_regs ms3) 26 = w64 (12 + 56 * j) /\ getr (ms_regs ms3) 27 = w64 j.

(* 0x807dc: the scan is done; held is in s9 and bind in s3. *)
Definition C1_I5 (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (q : nat) (r fab : Z) (bs M : list byte) (nch nz h u : Z),
  c1_body i cx fp C1_P5 k acc ly3 S3 W3 ms3 r fab bs q /\
  c1_read cx fp W3 ms3 M nch /\ c1_nz cx W3 ms3 M nz /\
  lslot cx W3 ms3 0x20 (2 ^ 64 - 1) /\
  LC1.c1_sh bs M nz (Boxreg.bx_n bs) h /\ LC1.c1_su bs nch (Boxreg.bx_n bs) u /\
  getr (ms_regs ms3) 19 = w64 u /\ getr (ms_regs ms3) 25 = w64 h.

(* 0x80984, the head of the inlined lowest_free loop: the candidate base is b and no base below it is free.
   The loop is reached only for a legal width and a nonzero MAC that no row holds and no unbound row of this
   width can take, with room for a new row; s7 still holds the width word (its low bit 0: the width is legal),
   which the checks after 0x809a8 read. *)
Definition C1_I6 (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (q : nat) (r fab : Z) (bs M : list byte) (nch nz b w7 : Z),
  c1_body i cx fp C1_P6 k acc ly3 S3 W3 ms3 r fab bs q /\
  c1_read cx fp W3 ms3 M nch /\ c1_nz cx W3 ms3 M nz /\
  lslot cx W3 ms3 0x20 (2 ^ 64 - 1) /\
  reac_boxreg_add_c.add_width_ok nch fab /\ M <> Boxreg.zero6 /\
  reac_boxreg_add_c.add_none_held bs M /\ reac_boxreg_add_c.add_none_unbound bs nch /\
  Boxreg.bx_n bs < 5 /\ lxc1_lfinv bs nch fab b /\ 0 <= b <= fab - nch /\
  0 <= w7 < 2 ^ 64 /\ Z.land w7 1 = 0 /\ getr (ms_regs ms3) 23 = w64 w7 /\
  getr (ms_regs ms3) 19 = w64 b /\ getr (ms_regs ms3) 24 = w64 (fab - nch + 1) /\
  getr (ms_regs ms3) 26 = w64 (Boxreg.bx_n bs) /\ getr (ms_regs ms3) 27 = w64 fab.

(* 0x809a8: `want` is in s9 and lf at sp1 + 0x20; s7's low bit says the width is not legal. *)
Definition C1_I7 (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (q : nat) (r fab : Z) (bs M : list byte) (nch nz lf want w7 : Z),
  c1_body i cx fp C1_P7 k acc ly3 S3 W3 ms3 r fab bs q /\
  c1_read cx fp W3 ms3 M nch /\ c1_nz cx W3 ms3 M nz /\
  lslot cx W3 ms3 0x20 (lf mod 2 ^ 64) /\ -1 <= lf <= 38 /\
  LC1.c1_wantP bs M nch lf want /\ -1 <= want <= 4 /\
  0 <= w7 < 2 ^ 64 /\ (Z.land w7 1 = 0 <-> reac_boxreg_add_c.add_width_ok nch fab) /\
  getr (ms_regs ms3) 23 = w64 w7 /\ getr (ms_regs ms3) 25 = w64 want /\
  getr (ms_regs ms3) 26 = w64 (Boxreg.bx_n bs) /\ getr (ms_regs ms3) 27 = w64 fab.

(* ---- the statement of each segment ---- *)
(* Each segment takes the walk's hypotheses and the phases after it, and gives the phase at its own cut. *)
Definition C1_SEG_head : Prop :=
  lx_hyps B MT -> forall POST i, lx_from B MT POST (C1_I1 i) -> lx_from B MT POST (LI_T B MT 1 i).
Definition C1_SEG_read : Prop :=
  lx_hyps B MT -> forall POST i, lx_from B MT POST (C1_I2 i) -> lx_from B MT POST (C1_I1 i).
Definition C1_SEG_zero : Prop :=
  lx_hyps B MT -> forall POST i, lx_from B MT POST (C1_I3 i) -> lx_from B MT POST (C1_I2 i).
Definition C1_SEG_scan0 : Prop :=
  lx_hyps B MT -> forall POST i,
  lx_from B MT POST (C1_I4 i) -> lx_from B MT POST (C1_I5 i) -> lx_from B MT POST (C1_I3 i).
Definition C1_SEG_scan : Prop :=
  lx_hyps B MT -> forall POST i, lx_from B MT POST (C1_I5 i) -> lx_from B MT POST (C1_I4 i).
Definition C1_SEG_want : Prop :=
  lx_hyps B MT -> forall POST i,
  lx_from B MT POST (C1_I6 i) -> lx_from B MT POST (C1_I7 i) -> lx_from B MT POST (C1_I5 i).
Definition C1_SEG_lf : Prop :=
  lx_hyps B MT -> forall POST i, lx_from B MT POST (C1_I7 i) -> lx_from B MT POST (C1_I6 i).
Definition C1_SEG_tail : Prop :=
  lx_hyps B MT -> forall POST i, lx_from B MT POST (LI_K B MT i) -> lx_from B MT POST (C1_I7 i).

End c.
End b.
End a.
