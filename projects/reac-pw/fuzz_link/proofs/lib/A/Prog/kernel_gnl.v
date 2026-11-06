(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 327 of its 364 lines of code are new or changed and 1268 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readDefs.v, with its module names changed; 1004 of its 1049 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/copy_attr.v, with its module names changed; 373 of its 423 lines of code are new or changed and 999 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_setup.v, with its addresses and numbers changed; 1356 of its 1423 lines of code are new or changed and 356 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: kernel's g_nl phase, kin_err (+0x3b4) -> kin_setup (+0x494) / kin_exit (+0x2140)
   (link-a/plan/kernel-plan.md (internal record, sha256 440bf3b40ab7) section 4).

   WHAT THE CODE DOES HERE (listing (internal path) (internal record, sha256 7bc02d6772b3)):
   - +0x3b4 .. +0x3b8: the slots 0x18 := shadow(F), 0x20 := F;
   - +0x3bc .. +0x3d8: the end index in a0: a0 := nl_errno.e + 4 * ei, the instrumented check of the 4-byte read
     (the shadow byte of that granule is 0: the last byte of each of the three granules of [nl_errno.e, +24) is
     in the range and has x mod 8 = 7, so saddr_ok leaves only s = 0), the slot 0x30 := F;
   - +0x3dc: `lw a0, 0(a0)`, the end errno; +0x3e4 .. +0x3f8: the two masked errno words
     (socket_errno = bit 0 of the flags ? e : 0, send_errno = bit 1 ? e : 0);
   - +0x3fc .. +0x418: g_nl (A_OBJ 2): the slot 0x38 := g_nl, `sd zero, 0x200(a2)` (n_chunks and next := 0),
     `sw` the three errno words at +0x208, +0x20c, +0x210 (a2 = g_nl + 0x40000);
   - +0x41c .. +0x434: the cursor's n (its instrumented check passes from range_addressable of the 16 bytes at
     a0: each 8-byte access holds the last byte of its granule); n = 0 -> +0x2140 (kin_exit);
   - +0x438 .. +0x47c: n := n - 1, the slot 0xc0 := shadow(a0), p := p + 1, the instrumented check of the byte
     at p (the ONLY check of this phase whose granule may be partial: the slow path is out of line at +0x21ec,
     which the walk kit's slow_block does not recognise, so the walk resolves the shadow byte itself through a
     region and an alias, and refutes the errpath arm from saddr_ok);
   - +0x480 .. +0x48c: c := byte & 3, the slot 0x60 := c; c = 0 -> +0x2140, else +0x494.

   THE PROOF (`kn_gnl`). The symbolic state at kin_err (gn_ss): the registers are their own atoms but for a1
   (= cursor >> 3) and s8 (= (cursor + 8 >> 3) + s4), which the invariant fixes as VALUES and which the engine's
   `match_x` needs in the (x >> 3) + Bx shape; Bx = SOff 20 0 (s4). SH holds one entry, (18, 0, 16): the four
   cursor checks are decided by `covered x 8` (its sh_ok: the cursor's range_addressable of kernel_apre, moved to
   the cut by kgn_saddr_transport). nl_errno.e's element (atom 38) and its shadow byte (atom 39, provably 0) are
   regions reached through ALIASES on the exact address expressions the engine builds (no case split on the end
   index), and so are the input byte (atom 32) and its shadow byte (atom 35). Two read-only regions may overlap
   (the input may lie in .rodata), so the walk runs +0x3b4 .. +0x418 with nl_errno.e's two regions, drops them
   (st_ok_pi_submem) and adds the input byte's two (st_ok_pi_add_region) for +0x41c .. Cases: (a) the cursor is
   empty: one run to +0x2140; (b) a byte is left, with its shadow byte 0 (b0: one run to +0x48c) or in [1, 7]
   (b1: the run stops at `bge` +0x21f0, whose taken arm is refuted by saddr_ok, then on to +0x48c); `bnez a0`
   +0x48c splits into kin_setup (+0x494) and kin_exit (+0x2140). Every end state goes to its cut by `kgn_kat`
   (kernel_kit.v's part lemmas over the written bytes kgn_X: the spill area, the cursor, g_nl's five words).
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0q YF0v YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide LinkWalkShadow LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_setup.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   The ALU facts the denotations of this phase's symbolic values need
   ========================================================================== *)

Lemma kgn_land63 : forall k, 0 <= k < 64 -> Z.land k 63 = k.
Proof.
  intros k Hk. change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2 ^ 6) with 64. lia.
Qed.

Lemma kgn_add64 : forall (x y : word),
  bv_unsigned (alu64 ALU_ADD x y) = (bv_unsigned x + bv_unsigned y) mod 2 ^ 64.
Proof.
  intros x y. rewrite alu64_unsigned. cbn [zalu_raw]. reflexivity.
Qed.

Lemma kgn_shl64 : forall (x : word) (k : Z), 0 <= k < 64 ->
  bv_unsigned (alu64 ALU_SLL x (Z_to_bv 64 k)) = (bv_unsigned x * 2 ^ k) mod 2 ^ 64.
Proof.
  intros x k Hk. rewrite alu64_unsigned. cbn [zalu_raw].
  rewrite unsigned_lit_small by lia.
  rewrite kgn_land63 by lia.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma kgn_shr64 : forall (x : word) (k : Z), 0 <= k < 64 ->
  bv_unsigned (alu64 ALU_SRL x (Z_to_bv 64 k)) = bv_unsigned x / 2 ^ k.
Proof.
  intros x k Hk. rewrite alu64_unsigned. cbn [zalu_raw].
  rewrite unsigned_lit_small by lia.
  rewrite kgn_land63 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (u64_range x). pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64).
  split; [apply Z.div_pos; lia|].
  apply (Z.le_lt_trans _ (bv_unsigned x)); [apply Z.div_le_upper_bound; nia | lia].
Qed.

(* the mask the compiler builds for `-(flags & 1) & e`: all ones or zero *)
Lemma kgn_mask64 : forall (x : word),
  bv_unsigned (alu64 ALU_SRA (alu64 ALU_SLL x (Z_to_bv 64 63)) (Z_to_bv 64 63)) = 0 \/
  bv_unsigned (alu64 ALU_SRA (alu64 ALU_SLL x (Z_to_bv 64 63)) (Z_to_bv 64 63)) = 2 ^ 64 - 1.
Proof.
  intros x. pose proof (u64_range x) as Hx.
  rewrite alu64_unsigned. cbn [zalu_raw].
  rewrite (kgn_shl64 x 63 ltac:(lia)).
  rewrite unsigned_lit_small by lia.
  rewrite kgn_land63 by lia.
  set (X := bv_unsigned x) in *.
  pose proof (Z.mod_pos_bound X 2 ltac:(lia)) as HB.
  assert (HM : (X * 2 ^ 63) mod 2 ^ 64 = (X mod 2) * 2 ^ 63).
  { rewrite (Z.div_mod X 2) at 1 by lia.
    replace ((2 * (X / 2) + X mod 2) * 2 ^ 63) with ((X mod 2) * 2 ^ 63 + (X / 2) * 2 ^ 64) by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  rewrite HM.
  destruct (Z.eq_dec (X mod 2) 0) as [E0|E1].
  - left. rewrite E0. reflexivity.
  - right. replace (X mod 2) with 1 by lia. reflexivity.
Qed.

Lemma kgn_and_mask : forall (m y : word),
  bv_unsigned m = 0 \/ bv_unsigned m = 2 ^ 64 - 1 ->
  bv_unsigned (alu64 ALU_AND m y) = 0 \/ bv_unsigned (alu64 ALU_AND m y) = bv_unsigned y.
Proof.
  intros m y [H|H]; rewrite alu64_unsigned; cbn [zalu_raw]; rewrite H; pose proof (u64_range y).
  - left. rewrite Z.land_0_l. reflexivity.
  - right. replace (2 ^ 64 - 1) with (Z.ones 64) by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_comm, Z.land_ones by lia.
    rewrite (Z.mod_small (bv_unsigned y) (2 ^ 64)) by lia.
    apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* ==========================================================================
   Where an akb byte lies: never in the shadow band, and below 2 ^ 47
   ========================================================================== *)

Section band. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

Lemma kgn_akb_rng : forall lyc Sc (W : world segs) memc mdc slo shi a,
  AR segs B lyc Sc W memc mdc -> alloc_ceiling <= ly_stk_lo lyc -> ly_stk_hi lyc <= 2 ^ 47 ->
  akb segs B lyc Sc slo shi a ->
  0 <= a < 2 ^ 47 /\ (a < SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= a).
Proof using SK LAWS segs_low.
  intros lyc Sc W memc mdc slo shi a HAR Hlo Hhi Hb.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HS : SHADOW_OFF = 0x7fff8000) by reflexivity.
  assert (HSB : SHADOW_OFF + 2 ^ 44 = kHighMemBeg) by (unfold SHADOW_OFF, kHighMemBeg; lia).
  destruct Hb as [(H1 & _) | [(b & m & Hin & Hr) | [(H1 & _ & _) | (cid & pos & Hin & Hr)]]].
  - split; [lia|]. right. lia.
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & H4096 & Hbc & Hbapp & _).
    unfold in_app, kLowShadowBeg, ASAN_CEIL in Hbapp. split; [lia|].
    destruct Hbapp as (_ & [Hq | (Hq1 & Hq2)]); [left; lia | right; lia].
  - pose proof (segs_low a H1). split; [lia|]. left. lia.
  - destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4 & Hfc & Happ).
    unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ.
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    pose proof (fs_frame_bytes_nonneg cid).
    split; [lia|]. destruct Happ as (_ & [Hq | (Hq1 & Hq2)]); [left; lia | right; lia].
Qed.

(* a whole range of akb bytes misses the shadow band (the band is an interval) *)
Lemma kgn_akb_band : forall lyc Sc (W : world segs) memc mdc slo shi a n,
  AR segs B lyc Sc W memc mdc -> alloc_ceiling <= ly_stk_lo lyc -> ly_stk_hi lyc <= 2 ^ 47 ->
  0 < n -> (forall x, a <= x < a + n -> akb segs B lyc Sc slo shi x) ->
  0 <= a /\ a + n <= 2 ^ 47 /\ (a + n <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= a).
Proof using SK LAWS segs_low.
  intros lyc Sc W memc mdc slo shi a n HAR Hlo Hhi Hn Hall.
  destruct (kgn_akb_rng lyc Sc W memc mdc slo shi a HAR Hlo Hhi (Hall a ltac:(lia))) as (Ha & Hba).
  destruct (kgn_akb_rng lyc Sc W memc mdc slo shi (a + n - 1) HAR Hlo Hhi (Hall (a + n - 1) ltac:(lia)))
    as (Hz & Hbz).
  split; [lia|]. split; [lia|].
  destruct Hba as [Hba | Hba]; [|right; lia].
  destruct Hbz as [Hbz | Hbz]; [left; lia|].
  exfalso.
  destruct (kgn_akb_rng lyc Sc W memc mdc slo shi SHADOW_OFF HAR Hlo Hhi (Hall SHADOW_OFF ltac:(lia)))
    as (_ & [Hq | Hq]); unfold SHADOW_OFF in *; lia.
Qed.
End band.

(* ==========================================================================
   g_nl's byte list after the four stores
   ========================================================================== *)

Definition kgn_b4 (v : Z) : list byte :=
  [Z_to_bv 8 (le_byte v 4 0); Z_to_bv 8 (le_byte v 4 1); Z_to_bv 8 (le_byte v 4 2); Z_to_bv 8 (le_byte v 4 3)].
Definition kgn_nb (ve vs vd : Z) : list byte :=
  repeat (Z_to_bv 8 0) 8 ++ kgn_b4 ve ++ kgn_b4 vs ++ kgn_b4 vd.
Definition kgn_bs (kbs : list byte) (ve vs vd : Z) : list byte :=
  firstn (Z.to_nat NK_N_CHUNKS) kbs ++ kgn_nb ve vs vd ++ skipn (Z.to_nat NK_OPEN) kbs.

Lemma kgn_nb_len : forall ve vs vd, length (kgn_nb ve vs vd) = 20%nat.
Proof. intros. reflexivity. Qed.

Lemma kgn_lo_hi : (Z.to_nat NK_N_CHUNKS + 20 = Z.to_nat NK_OPEN)%nat.
Proof. unfold NK_N_CHUNKS, NK_OPEN. lia. Qed.

Lemma kgn_bs_len : forall kbs ve vs vd, (Z.to_nat NK_OPEN <= length kbs)%nat ->
  length (kgn_bs kbs ve vs vd) = length kbs.
Proof.
  intros kbs ve vs vd H. pose proof kgn_lo_hi as HLH. unfold kgn_bs.
  rewrite !length_app, length_firstn, length_skipn, kgn_nb_len. lia.
Qed.

Lemma kgn_bs_lo : forall kbs ve vs vd i,
  (Z.to_nat NK_N_CHUNKS <= length kbs)%nat -> (i < Z.to_nat NK_N_CHUNKS)%nat ->
  nth_error (kgn_bs kbs ve vs vd) i = nth_error kbs i.
Proof.
  intros kbs ve vs vd i Hl Hi. unfold kgn_bs.
  rewrite nth_error_app1 by (rewrite length_firstn; lia).
  apply lw_nth_error_firstn. exact Hi.
Qed.

Lemma kgn_bs_mid : forall kbs ve vs vd i,
  (Z.to_nat NK_N_CHUNKS <= length kbs)%nat ->
  (Z.to_nat NK_N_CHUNKS <= i)%nat -> (i < Z.to_nat NK_OPEN)%nat ->
  nth_error (kgn_bs kbs ve vs vd) i = nth_error (kgn_nb ve vs vd) (i - Z.to_nat NK_N_CHUNKS).
Proof.
  intros kbs ve vs vd i Hl H1 H2. pose proof kgn_lo_hi as HLH. unfold kgn_bs.
  rewrite nth_error_app2 by (rewrite length_firstn; lia).
  rewrite length_firstn.
  replace (Nat.min (Z.to_nat NK_N_CHUNKS) (length kbs)) with (Z.to_nat NK_N_CHUNKS) by lia.
  rewrite nth_error_app1 by (rewrite kgn_nb_len; lia). reflexivity.
Qed.

Lemma kgn_bs_hi : forall kbs ve vs vd i,
  (Z.to_nat NK_OPEN <= length kbs)%nat -> (Z.to_nat NK_OPEN <= i)%nat ->
  nth_error (kgn_bs kbs ve vs vd) i = nth_error kbs i.
Proof.
  intros kbs ve vs vd i Hl Hi. pose proof kgn_lo_hi as HLH. unfold kgn_bs.
  rewrite nth_error_app2 by (rewrite length_firstn; lia).
  rewrite length_firstn.
  replace (Nat.min (Z.to_nat NK_N_CHUNKS) (length kbs)) with (Z.to_nat NK_N_CHUNKS) by lia.
  rewrite nth_error_app2 by (rewrite kgn_nb_len; lia).
  rewrite kgn_nb_len, lw_nth_error_skipn. f_equal. lia.
Qed.

Lemma kgn_bs_skipn : forall kbs ve vs vd, (Z.to_nat NK_OPEN <= length kbs)%nat ->
  skipn (Z.to_nat NK_OPEN) (kgn_bs kbs ve vs vd) = skipn (Z.to_nat NK_OPEN) kbs.
Proof.
  intros kbs ve vs vd Hl.
  apply lw_list_ext.
  - rewrite !length_skipn, kgn_bs_len by exact Hl. reflexivity.
  - intros k Hk. rewrite !lw_nth_error_skipn. apply kgn_bs_hi; [exact Hl | lia].
Qed.

(* The four fields the stores leave in the new bytes. The index arithmetic goes through `lia` on the nat terms,
   never through reduction: `Z.to_nat 262656` as a unary nat is this unit's performance trap. *)
Lemma kgn_rdn_field : forall kbs ve vs vd off (j : nat) v,
  (Z.to_nat NK_OPEN <= length kbs)%nat -> 0 <= v < 2 ^ 32 ->
  NK_N_CHUNKS <= off -> off + 4 <= NK_OPEN ->
  (Z.to_nat off = Z.to_nat NK_N_CHUNKS + j)%nat ->
  (forall k, (k < 4)%nat -> nth_error (kgn_nb ve vs vd) (j + k) = Some (Z_to_bv 8 (le_byte v 4 k))) ->
  rdn (kgn_bs kbs ve vs vd) off 4 = v.
Proof.
  intros kbs ve vs vd off j v Hl Hv Hlo Hhi Hj Hnb.
  pose proof kgn_lo_hi as HLH.
  assert (HoffZ : 0 <= off) by (unfold NK_N_CHUNKS in Hlo; lia).
  assert (HlenZ : off + Z.of_nat 4 <= Z.of_nat (length (kgn_bs kbs ve vs vd))).
  { rewrite kgn_bs_len by exact Hl. unfold NK_OPEN in *. lia. }
  replace 4 with (Z.of_nat 4) by reflexivity.
  apply (rdn_of_vals _ off 4%nat v HoffZ HlenZ ltac:(cbn [Z.of_nat]; exact Hv)).
  intros k Hk.
  rewrite kgn_bs_mid by lia.
  replace (Z.to_nat off + k - Z.to_nat NK_N_CHUNKS)%nat with (j + k)%nat by lia.
  exact (Hnb k Hk).
Qed.

Lemma kgn_rdn_n_chunks : forall kbs ve vs vd, (Z.to_nat NK_OPEN <= length kbs)%nat ->
  rdn (kgn_bs kbs ve vs vd) NK_N_CHUNKS 4 = 0.
Proof.
  intros kbs ve vs vd Hl.
  apply (kgn_rdn_field kbs ve vs vd NK_N_CHUNKS 0%nat 0 Hl ltac:(lia) ltac:(lia)
    ltac:(unfold NK_N_CHUNKS, NK_OPEN; lia) ltac:(lia)).
  intros k Hk. do 4 (destruct k as [|k]; [reflexivity|]). lia.
Qed.

Lemma kgn_rdn_next : forall kbs ve vs vd, (Z.to_nat NK_OPEN <= length kbs)%nat ->
  rdn (kgn_bs kbs ve vs vd) NK_NEXT 4 = 0.
Proof.
  intros kbs ve vs vd Hl.
  apply (kgn_rdn_field kbs ve vs vd NK_NEXT 4%nat 0 Hl ltac:(lia)
    ltac:(unfold NK_N_CHUNKS, NK_NEXT; lia) ltac:(unfold NK_NEXT, NK_OPEN; lia)
    ltac:(unfold NK_N_CHUNKS, NK_NEXT; lia)).
  intros k Hk. do 4 (destruct k as [|k]; [reflexivity|]). lia.
Qed.

Lemma kgn_rdn_end : forall kbs ve vs vd, (Z.to_nat NK_OPEN <= length kbs)%nat -> 0 <= ve < 2 ^ 32 ->
  rdn (kgn_bs kbs ve vs vd) NK_END_ERRNO 4 = ve.
Proof.
  intros kbs ve vs vd Hl Hv.
  apply (kgn_rdn_field kbs ve vs vd NK_END_ERRNO 8%nat ve Hl Hv
    ltac:(unfold NK_N_CHUNKS, NK_END_ERRNO; lia) ltac:(unfold NK_END_ERRNO, NK_OPEN; lia)
    ltac:(unfold NK_N_CHUNKS, NK_END_ERRNO; lia)).
  intros k Hk. do 4 (destruct k as [|k]; [reflexivity|]). lia.
Qed.

Lemma kgn_rdn_socket : forall kbs ve vs vd, (Z.to_nat NK_OPEN <= length kbs)%nat -> 0 <= vs < 2 ^ 32 ->
  rdn (kgn_bs kbs ve vs vd) NK_SOCKET_ERRNO 4 = vs.
Proof.
  intros kbs ve vs vd Hl Hv.
  apply (kgn_rdn_field kbs ve vs vd NK_SOCKET_ERRNO 12%nat vs Hl Hv
    ltac:(unfold NK_N_CHUNKS, NK_SOCKET_ERRNO; lia) ltac:(unfold NK_SOCKET_ERRNO, NK_OPEN; lia)
    ltac:(unfold NK_N_CHUNKS, NK_SOCKET_ERRNO; lia)).
  intros k Hk. do 4 (destruct k as [|k]; [reflexivity|]). lia.
Qed.

Lemma kgn_rdn_send : forall kbs ve vs vd, (Z.to_nat NK_OPEN <= length kbs)%nat -> 0 <= vd < 2 ^ 32 ->
  rdn (kgn_bs kbs ve vs vd) NK_SEND_ERRNO 4 = vd.
Proof.
  intros kbs ve vs vd Hl Hv.
  apply (kgn_rdn_field kbs ve vs vd NK_SEND_ERRNO 16%nat vd Hl Hv
    ltac:(unfold NK_N_CHUNKS, NK_SEND_ERRNO; lia) ltac:(unfold NK_SEND_ERRNO, NK_OPEN; lia)
    ltac:(unfold NK_N_CHUNKS, NK_SEND_ERRNO; lia)).
  intros k Hk. do 4 (destruct k as [|k]; [reflexivity|]). lia.
Qed.

(* ==========================================================================
   Bit facts of the values the phase computes
   ========================================================================== *)

Lemma kgn_le_byte_0 : forall w k, le_byte 0 w k = 0.
Proof.
  intros w k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
  rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma kgn_nb_nth : forall ve vs vd (j : nat), (j < 20)%nat ->
  nth_error (kgn_nb ve vs vd) j =
  Some (Z_to_bv 8 (if (j <? 8)%nat then 0 else if (j <? 12)%nat then le_byte ve 4 (j - 8)
                   else if (j <? 16)%nat then le_byte vs 4 (j - 12) else le_byte vd 4 (j - 16))).
Proof. intros ve vs vd j Hj. do 20 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Lemma kgn_swrap32_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.

(* the mask of `sraiw a3, a3, 0x1f` (+0x3f0): all ones or zero *)
Lemma kgn_mask32 : forall y z : bv 32, bv_unsigned z = 31 ->
  bv_unsigned (sext 64 (alu32 ALU_SRA y z)) = 0 \/
  bv_unsigned (sext 64 (alu32 ALU_SRA y z)) = 2 ^ 64 - 1.
Proof.
  intros y z H31. rewrite sext32_unsigned, alu32_unsigned. cbn [zalu_raw].
  rewrite H31.
  change (Z.land 31 31) with 31.
  pose proof (bv_unsigned_in_range 32 y) as Hy. change (bv_modulus 32) with 4294967296 in Hy.
  set (Y := bv_unsigned y) in *.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 31) with 2147483648.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (4294967296 / 2) with 2147483648.
  change (2 ^ 64 - 1) with 18446744073709551615.
  lia.
Qed.


Lemma kgn_mask32s : forall E a,
  bv_unsigned (sv_denot E (SAluw ALU_SRA a (SLit 31))) = 0 \/
  bv_unsigned (sv_denot E (SAluw ALU_SRA a (SLit 31))) = 2 ^ 64 - 1.
Proof. intros E a. cbn [sv_denot]. apply kgn_mask32. rewrite low32_lit_unsigned. reflexivity. Qed.
Lemma kgn_sext32_small : forall v, 0 <= v < 2 ^ 31 -> sext 64 (bv_extract 0 32 (Z_to_bv 64 v)) = Z_to_bv 64 v.
Proof.
  intros v Hv. apply bv_eq. rewrite sext32_unsigned.
  change (bv_extract 0 32 (Z_to_bv 64 v)) with (low32 (Z_to_bv 64 v)).
  rewrite low32_lit_unsigned, unsigned_lit_small by lia. unfold zu32, M32.
  rewrite Z.mod_small by lia. rewrite kgn_swrap32_small by lia.
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma kgn_shadow_u : forall a, 0 <= a < 2 ^ 64 ->
  bv_unsigned (alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 a) (Z_to_bv 64 3)) (Z_to_bv 64 SHADOW_OFF)) =
  shadow_of_addr SHADOW_OFF a.
Proof.
  intros a Ha. rewrite kgn_add64, kgn_shr64 by lia.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  unfold shadow_of_addr. change (2 ^ 3) with 8. rewrite Z.mod_small by (unfold SHADOW_OFF; lia). lia.
Qed.

Lemma kgn_and7_u : forall a, 0 <= a < 2 ^ 64 ->
  bv_unsigned (alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 7)) = a mod 8.
Proof.
  intros a Ha. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
  replace (Z.land a 7) with (a mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). pose proof (Z.mod_pos_bound a 8). lia.
Qed.

Lemma kgn_and3_u : forall x : word, 0 <= bv_unsigned (alu64 ALU_AND x (Z_to_bv 64 3)) <= 3.
Proof.
  intros x. rewrite alu64_unsigned. cbn [zalu_raw].
  rewrite (unsigned_lit_small 3) by lia.
  replace (Z.land (bv_unsigned x) 3) with (bv_unsigned x mod 4)
    by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
  pose proof (Z.mod_pos_bound (bv_unsigned x) 4).
  rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Lemma kgn_signed_small : forall x : word, bv_unsigned x < 2 ^ 63 -> bv_signed x = bv_unsigned x.
Proof.
  intros x Hx. pose proof (u64_range x). unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (18446744073709551616 / 2) with 9223372036854775808.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma kgn_bge_small : forall x y : word, bv_unsigned x < 2 ^ 63 -> bv_unsigned y < 2 ^ 63 ->
  branch_taken BC_GE x y = negb (bv_unsigned x <? bv_unsigned y).
Proof.
  intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts.
  rewrite (kgn_signed_small x Hx), (kgn_signed_small y Hy). reflexivity.
Qed.

Lemma kgn_aview_byte : forall (segs : list Segment) H (mem : word -> option byte) a v,
  aview segs H mem a = Some v -> mbyte segs (mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof.
  intros segs H mem a v Hv. unfold aview in Hv.
  destruct (mbyte segs (mrestrict H mem) a) as [b|]; cbn in Hv; [|discriminate].
  injection Hv as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma kgn_aview_range : forall (segs : list Segment) H (mem : word -> option byte) a v,
  aview segs H mem a = Some v -> 0 <= v < 256.
Proof.
  intros segs H mem a v Hv. unfold aview in Hv.
  destruct (mbyte segs (mrestrict H mem) a) as [b|]; cbn in Hv; [|discriminate].
  injection Hv as <-. exact (u8_range b).
Qed.

(* ==========================================================================
   A read-set byte's shadow byte, from the call to a later AR state (LinkWalkShadow.v sbyte_transport without its
   group-visibility half: the cursor and nl_errno.e have range_addressable in kernel_apre but no shadow_hull_vis)
   ========================================================================== *)

Section sh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis segs_img : forall a, in_img segs a -> 0x10000 <= a < pcap_img_end.

Lemma kgn_saddr_transport : forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi
    (E : Z -> Prop) x,
  AR segs B lyc Sc W memc mdc -> AR segs B ly2 S2 W2 mem2 md2 ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  akept segs B lyc Sc W memc W2 mem2 slo shi E -> fmiss lyc Sc E ->
  akb segs B lyc Sc slo shi x ->
  saddr (aview segs (w_H W) memc) x -> saddr (aview segs (w_H W2) mem2) x.
Proof using LAWS TB segs_img.
  intros lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E x HAR1 HAR2 Elo Ehi Hbl HK HE Hc Hs1.
  pose proof HAR1 as (M1 & _). pose proof HAR2 as (M2 & _).
  destruct Hc as [(Hst & _) | [(b & m & Hin & Hb) | [(Hi & _) | (c & q & Hin & Hf)]]].
  - (* the real stack: zero at every AR state *)
    pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly2 S2 _ M2) (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2)
      ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
    cbn [fst snd] in HZ. unfold zero_shadow, shadow_of_addr in HZ.
    pose proof (am_layout B ly2 S2 _ M2) as LO. destruct (lo_top _ LO) as (_ & _ & _ & _ & Pl & Ph & _).
    unfold page_aligned in Pl, Ph. rewrite Elo, Ehi in *.
    exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + ly_stk_lo lyc / 8 + (x / 8 - ly_stk_lo lyc / 8)) by lia.
    apply HZ. lia.
  - (* a heap block still alive *)
    pose proof (Hbl b m Hin) as Hin2.
    destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin2) as [HBS _].
    exact (block_shadow_range _ _ _ _ x 1 HBS ltac:(lia) ltac:(lia) x ltac:(lia)).
  - (* the image *)
    pose proof (segs_img x Hi) as Hi'. rewrite img_end_val in Hi'.
    assert (Hsx : SHADOW_OFF + 0x2000 <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 0xca800)
      by (unfold shadow_of_addr; lia).
    destruct (img_sh_eq B TB lyc Sc _ ly2 S2 _ _ M1 M2 Hsx) as [Eq _].
    destruct Hs1 as (v & Hv & Hok). exists v. rewrite Eq. split; [exact Hv | exact Hok].
  - (* a side frame of the call *)
    unfold frame_rng, in_zr in Hf. cbn [fst snd] in Hf.
    pose proof HK as (_ & _ & _ & K4 & _).
    destruct (frame_facts B lyc Sc _ c q M1 Hin) as (_ & _ & Happ & _ & PF & _ & _ & Hoff & H64 & Hb64 & _).
    unfold page_aligned in PF. unfold in_app, kFakeStackSize in Happ.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c q HAR1 Hin) as (Hf4096 & Hfceil & _).
    pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    assert (HF64 : frame_addr lyc c q mod 64 = 0) by (unfold frame_addr; lia).
    assert (Hsf : shadow_addr (frame_addr lyc c q) <= shadow_of_addr SHADOW_OFF x <
                  shadow_addr (frame_addr lyc c q) + fs_frame_bytes c / 8)
      by (unfold shadow_addr, shadow_of_addr, SHADOW_OFF in *; lia).
    destruct Hs1 as (v & Hv & Hok). exists v. split; [|exact Hok].
    rewrite (K4 c q (shadow_of_addr SHADOW_OFF x) Hin); [exact Hv | | exact (HE c q _ Hin Hsf)].
    right. unfold in_zr. cbn [fst snd]. exact Hsf.
Qed.
End sh.

Lemma kgn_vm1 : forall (segs : list Segment) H (m : word -> option byte) a v,
  aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
  intros segs H m a v Hv k Hk. destruct k as [|k]; [|lia].
  pose proof (kgn_aview_range segs H m a v Hv) as Hr.
  cbn [Z.of_nat]. rewrite Z.add_0_r, (kgn_aview_byte segs H m a v Hv).
  change (Some (Z_to_bv 8 v) = Some (Z_to_bv 8 ((Z.shiftr (v mod 256) 0) mod 256))).
  rewrite Z.shiftr_0_r. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* ==========================================================================
   The symbolic state at +0x3b4 (measured by the probe: header)
   ========================================================================== *)

Definition gn_Bx : sv := SOff 20 0.
Definition gn_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition gn_SH : list shent := [mkSHE 18 0 16].
Definition gn_e11 : sv := SAlu ALU_SRL (SOff 18 0) (SLit 3).
Definition gn_e24 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 20 0).
Definition gn_regs0 : list sv := sr_set (sr_set sr_atoms (Z_to_bv 5 11) gn_e11) (Z_to_bv 5 24) gn_e24.
Definition gn_spill : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x18 0xf8 0x18 0xf8
    [YP09.mkChunk 0x50 (CVal 8 (SOff 22 4)); YP09.mkChunk 0x80 (CVal 8 (SOff 22 0x226));
     YP09.mkChunk 0xb0 (CVal 8 (SOff 18 8)); YP09.mkChunk 0xf0 (CVal 8 (SOff 19 0))].
Definition gn_cur (nv : sv) : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 nv)].
Definition gn_g : YP09.region := YP09.mkRegion (Some 243%nat) 262656 262676 262656 262676 [].
Definition gn_ne : YP09.region := YP09.mkRegion (Some 38%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 37 0))].
Definition gn_nesh : YP09.region := YP09.mkRegion (Some 39%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition gn_in : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition gn_shb (v : sv) : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 v)].
Definition gn_atoms (nf : afact) : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5); (18%nat, mkAF 0 (2 ^ 47 - 16) 0);
   (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (243%nat, mkAF LA_G_NL LA_G_NL 3); (33%nat, nf)].
(* the address expressions the engine builds for nl_errno.e's element, its shadow byte and the input byte's *)
Definition gn_a38 : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 2)) (SOff 12 0).
Definition gn_a39 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 38 0) (SLit 3)) (SOff 20 0).
Definition gn_a35 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0) (SLit 3)) (SOff 20 0).
Definition gn_alias_ne : list (sv * sv) :=
  [(gn_a38, SOff 38 0); (gn_a39, SOff 39 0); (SAlu ALU_ADD gn_a39 (SLit 0), SOff 39 0)].
Definition gn_ss (nv : sv) (nf : afact) : sstate :=
  mkSS (kpc KP_ERR) gn_regs0 [gn_spill; gn_cur nv; gn_g; gn_ne; gn_nesh] None
    (mkFacts (gn_atoms nf) [] gn_alias_ne).
(* the values the end states hold: the two masked errno words, c = byte & 3, shadow(a0) *)
Definition gn_es : sv := SAlu ALU_AND (SAlu ALU_SRA (SAlu ALU_SLL (SOff 13 0) (SLit 63)) (SLit 63)) (SOff 15 0).
Definition gn_ed : sv := SAlu ALU_AND (SAluw ALU_SRA (SAlu ALU_SLL (SOff 13 0) (SLit 30)) (SLit 31)) (SOff 15 0).
Definition gn_ec : sv := SAlu ALU_AND (SExt false 8 (SOff 34 0)) (SLit 3).
Definition gn_esh : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 20 0).
Definition kgn_off_band (a n : Z) : Prop := a + n <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= a.
(* an errno word kgnl allows (folded, so that lia does not split on it) *)
Definition kgn_ok0 (v : Z) : Prop := v = 0 \/ In v nl_errno_tab.
(* the extra atoms 32 .. 39: p, n', the input byte, shadow(p), its shadow byte, nl_errno.e[ei], its address and
   shadow address *)
Definition gn_ext (p n bv sh ve ei : Z) : list word :=
  [w64 p; w64 n; w64 bv; w64 (shadow_of_addr SHADOW_OFF p); w64 sh; w64 ve; w64 (LA_NL_ERRNO_E + 4 * ei);
   w64 (shadow_of_addr SHADOW_OFF (LA_NL_ERRNO_E + 4 * ei))].

Ltac gn_inl := cbn [In]; repeat (first [left; reflexivity | right]).

(* ==========================================================================
   The phase's frame: the bytes it writes, and the cut it reaches
   ========================================================================== *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : AF0m.PcapSyms B.

(* the bytes +0x3b4 .. +0x48c may write: the spill area [s1 + 0x18, s1 + 0xf8), the cursor, and g_nl's n_chunks,
   next and three errno words *)
Definition kgn_X (cx : kcx) (a : Z) : Prop :=
  (ksp1 cx + 0x18 <= a < ksp1 cx + 0xf8) \/ (ka0 cx <= a < ka0 cx + 16) \/
  (LA_G_NL + NK_N_CHUNKS <= a < LA_G_NL + NK_OPEN).

Lemma kgn_kE_cur : forall cx a, ka0 cx <= a < ka0 cx + 16 -> kE cx a.
Proof.
  intros cx a Ha. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16). split.
  - unfold kernel_awr. cbn [In]. right; right; left. reflexivity.
  - cbn [fst snd]. unfold ka0 in Ha. exact Ha.
Qed.

Lemma kgn_kE_gnl : forall cx a, LA_G_NL + NK_N_CHUNKS <= a < LA_G_NL + NK_OPEN -> kE cx a.
Proof.
  intros cx a Ha. exists (LA_G_NL + NK_CHUNK, LA_G_NL + NK_OPEN). split.
  - unfold kernel_awr. cbn [In]. left. reflexivity.
  - cbn [fst snd]. unfold NK_CHUNK, NK_N_CHUNKS in *. lia.
Qed.

Lemma kgn_cur_ard : forall cx a, ka0 cx <= a < ka0 cx + 16 -> kernel_ard SEGS (k_regs cx) (km0 cx) a.
Proof. intros cx a Ha. unfold kernel_ard. left. unfold ka0 in Ha. exact Ha. Qed.

(* the phase's cut at a later state: every part of kat moved across the writes kgn_X (kernel_kit.v's part
   lemmas), the cursor at adv', and g_nl's queue reset with the three errno words ve, vs, vd *)
Lemma kgn_kat : forall cx fpos rl sl adv k2 ly3 S3 W3 ms3 md3 pc' rl' sl' adv' ms4 md4 ve vs vd,
  kbase SK B cx ->
  kat B cx fpos KP_ERR rl sl (kfsh 0xf8 0xf8 0xf3) true adv None k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> kslots_eq cx W3 ms4 sl' ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ kgn_X cx a ->
     aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms4) a) ->
  0 <= adv' <= k_wn cx ->
  au64_at SEGS (rdW W3 (ms_mem ms4)) (ka0 cx) (k_wp cx + adv') ->
  au64_at SEGS (rdW W3 (ms_mem ms4)) (ka0 cx + 8) (k_wn cx - adv') ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + NK_N_CHUNKS) 8 0 ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + NK_END_ERRNO) 4 ve ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + NK_SOCKET_ERRNO) 4 vs ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + NK_SEND_ERRNO) 4 vd ->
  In ve nl_errno_tab -> (vs = 0 \/ In vs nl_errno_tab) -> (vd = 0 \/ In vd nl_errno_tab) ->
  kat B cx fpos pc' rl' sl' (kfsh 0xf8 0xf8 0xf3) true adv' (Some 0) k2 ly3 S3 W3 ms4 md4.
Proof.
  intros cx fpos rl sl adv k2 ly3 S3 W3 ms3 md3 pc' rl' sl' adv' ms4 md4 ve vs vd
    HB HK HMS HR0 HRL HSL Hfds Hfs UN HP Hadv Hc0 Hc8 Hg0 Hge Hgs Hgd Hve Hvs Hvd.
  destruct HK as (_ & _ & _ & HSAV & HFR & HSH & _ & HJB & HKEPT & HCUR & HGNL & HLA).
  pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (HPRE & HRD & HKP & _).
  destruct HKP as (kbs0 & _ & _ & _ & _ & _ & _ & _ & _ & HCAG & HCAL & _).
  destruct (kn_base_facts SK B cx HB) as (Hsp & Hs1 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (HF4 & HFc & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  (* where the written bytes lie *)
  assert (XC : forall a, kgn_X cx a -> ka0 cx <= a < ka0 cx + 16 ->
            0 <= a < 2 ^ 47 /\ ~ (ksp cx - KERNEL_AK <= a < ksp cx) /\ ~ aside_rng (k_lyc cx) KN_CID fpos a).
  { intros a _ Ha.
    destruct (kn_ard_bound SK B LAWS cx a HB (kgn_cur_ard cx a Ha)) as (H1 & H2).
    split; [exact H1|]. split; [exact H2|].
    exact (kn_ard_not_side SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB (or_introl (kgn_cur_ard cx a Ha))). }
  assert (XG : forall a, LA_G_NL + NK_N_CHUNKS <= a < LA_G_NL + NK_OPEN -> ~ aside_rng (k_lyc cx) KN_CID fpos a).
  { intros a Ha. exact (kn_ard_not_side SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB (or_intror (kgn_kE_gnl cx a Ha))). }
  assert (NSIDE : forall a, kgn_X cx a -> (ksp1 cx + 0x18 <= a < ksp1 cx + 0xf8) \/ ~ aside_rng (k_lyc cx) KN_CID fpos a).
  { intros a [Hx | [Hx | Hx]]; [left; exact Hx | right | right].
    - exact (proj2 (proj2 (XC a (or_intror (or_introl Hx)) Hx))).
    - exact (XG a Hx). }
  pose proof (kk_grows_of_apresent _ _ _ _ HP) as HG.
  unfold kat.
  refine (conj HMS (conj HR0 (conj HRL (conj _ (conj _ (conj _ (conj HSL (conj _ (conj _ (conj _ (conj _ _))))))))))).
  - (* ksaved *)
    apply (ksaved_frame SK B (kgn_X cx) cx W3 ms3 W3 ms4 HB UN); [|exact HSAV].
    intros a Ha [Hx | [Hx | Hx]].
    + lia.
    + destruct (XC a (or_intror (or_introl Hx)) Hx) as (_ & Hw & _). apply Hw. lia.
    + unfold LA_G_NL, NK_OPEN in Hx. lia.
  - (* kframe *)
    apply (kframe_frame B LAWS (kgn_X cx) cx fpos true k2 ly3 S3 md3 W3 ms3 W3 ms4 HJB UN HP); [| |exact HFR].
    + intros a Ha Hx. destruct (NSIDE a Hx) as [Hs | Hs]; [lia|]. apply Hs. left. unfold in_zr, frame_rng.
      cbn [fst snd]. unfold kF in Ha. rewrite Hfb. lia.
    + intros a Ha Hx. destruct (NSIDE a Hx) as [Hs | Hs]; [rewrite Hfb in Ha; lia|]. apply Hs. left.
      unfold in_zr, frame_rng. cbn [fst snd]. unfold kF in Ha. rewrite Hfb in Ha |- *. lia.
  - (* kshadow *)
    apply (kshadow_frame B LAWS (kgn_X cx) cx fpos (kfsh 0xf8 0xf8 0xf3) k2 ly3 S3 md3 W3 ms3 W3 ms4 HJB UN
             (kfsh_fits _ _ _)); [|exact HSH].
    intros a Ha Hx. rewrite kfsh_length in Ha. change (Z.of_nat 0x448) with 1096 in Ha.
    destruct (NSIDE a Hx) as [Hs | Hs]; [unfold kFSH, shadow_of_addr, SHADOW_OFF in Ha; lia|].
    apply Hs. right; left. unfold in_zr. cbn [fst snd]. rewrite Hfb.
    unfold kFSH, kF, shadow_of_addr in Ha. unfold shadow_addr. lia.
  - (* kjbk *)
    exact (kjbk_md B cx fpos k2 ly3 S3 md3 md4 HJB Hfds Hfs).
  - (* kkept *)
    apply (kkept_frame SK B LAWS (kgn_X cx) cx fpos k2 ly3 S3 md3 W3 ms3 W3 ms4 HB HJB UN HP); [|exact HKEPT].
    intros a [Hx | [Hx | Hx]]; unfold kX_in.
    + right; right; right. rewrite HKA. lia.
    + left. exact (kgn_kE_cur cx a Hx).
    + left. exact (kgn_kE_gnl cx a Hx).
  - (* kcursor *)
    destruct HCUR as (_ & _ & _ & HCW).
    split; [exact Hadv|]. split; [exact Hc0|]. split; [exact Hc8|].
    intros i Hi. exact (writable_at_grows SEGS _ _ _ HG (HCW i Hi)).
  - (* kgnl_at (Some 0) *)
    cbn [kgnl_at] in HGNL |- *. destruct HGNL as ((HAB & HAW) & HAL).
    assert (HL0 : (Z.to_nat NK_OPEN <= length (k_kbs cx))%nat) by (unfold NK_SIZE, NK_OPEN in *; lia).
    exists (kgn_bs (k_kbs cx) ve vs vd).
    assert (HL3 : Z.of_nat (length (kgn_bs (k_kbs cx) ve vs vd)) = NK_SIZE) by (rewrite kgn_bs_len by exact HL0; exact HAL).
    assert (Rve : 0 <= ve < 2 ^ 32) by (cbn [nl_errno_tab In] in Hve; unfold E_NOBUFS, E_INTR, E_AGAIN, E_PERM,
      E_MFILE, E_CONNREFUSED in Hve; lia).
    assert (Rvs : 0 <= vs < 2 ^ 32) by (destruct Hvs as [Hvs|Hvs]; [lia|]; cbn [nl_errno_tab In] in Hvs;
      unfold E_NOBUFS, E_INTR, E_AGAIN, E_PERM, E_MFILE, E_CONNREFUSED in Hvs; lia).
    assert (Rvd : 0 <= vd < 2 ^ 32) by (destruct Hvd as [Hvd|Hvd]; [lia|]; cbn [nl_errno_tab In] in Hvd;
      unfold E_NOBUFS, E_INTR, E_AGAIN, E_PERM, E_MFILE, E_CONNREFUSED in Hvd; lia).
    split; [split; [split|] | ].
    + (* the bytes *)
      destruct HAB as (HA0 & HA1 & HAb).
      split; [exact HA0|]. split; [rewrite HL3; rewrite HAL in HA1; exact HA1|].
      intros i Hi. rewrite kgn_bs_len in Hi by exact HL0.
      destruct (Nat.lt_ge_cases i (Z.to_nat NK_N_CHUNKS)) as [Hlo | Hlo].
      * rewrite kgn_bs_lo by (unfold NK_N_CHUNKS, NK_SIZE in *; lia).
        rewrite <- (HAb i Hi). apply (mbyte_of_aview SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms4)).
        apply UN; [unfold LA_G_NL, NK_SIZE in *; lia|].
        intros [Hx | [Hx | Hx]].
        -- unfold LA_G_NL, NK_SIZE in *. rewrite HKA in Hsp. lia.
        -- unfold apart_gnl in HCAG. unfold ka0 in Hx. unfold NK_SIZE in *. lia.
        -- unfold NK_N_CHUNKS in *. lia.
      * destruct (Nat.lt_ge_cases i (Z.to_nat NK_OPEN)) as [Hhi | Hhi].
        -- rewrite kgn_bs_mid by (unfold NK_N_CHUNKS, NK_OPEN, NK_SIZE in *; lia).
           assert (Hj : (i - Z.to_nat NK_N_CHUNKS < 20)%nat) by (unfold NK_N_CHUNKS, NK_OPEN in *; lia).
           rewrite (kgn_nb_nth ve vs vd _ Hj).
           set (j := (i - Z.to_nat NK_N_CHUNKS)%nat) in *.
           assert (Hij : LA_G_NL + Z.of_nat i = LA_G_NL + NK_N_CHUNKS + Z.of_nat j)
             by (unfold j, NK_N_CHUNKS in *; lia).
           rewrite Hij.
           destruct (j <? 8)%nat eqn:J8; [apply Nat.ltb_lt in J8 | apply Nat.ltb_ge in J8].
           { rewrite (Hg0 j J8). rewrite kgn_le_byte_0. reflexivity. }
           destruct (j <? 12)%nat eqn:J12; [apply Nat.ltb_lt in J12 | apply Nat.ltb_ge in J12].
           { replace (LA_G_NL + NK_N_CHUNKS + Z.of_nat j) with (LA_G_NL + NK_END_ERRNO + Z.of_nat (j - 8))
               by (unfold NK_N_CHUNKS, NK_END_ERRNO; lia).
             exact (Hge (j - 8)%nat ltac:(lia)). }
           destruct (j <? 16)%nat eqn:J16; [apply Nat.ltb_lt in J16 | apply Nat.ltb_ge in J16].
           { replace (LA_G_NL + NK_N_CHUNKS + Z.of_nat j) with (LA_G_NL + NK_SOCKET_ERRNO + Z.of_nat (j - 12))
               by (unfold NK_N_CHUNKS, NK_SOCKET_ERRNO; lia).
             exact (Hgs (j - 12)%nat ltac:(lia)). }
           replace (LA_G_NL + NK_N_CHUNKS + Z.of_nat j) with (LA_G_NL + NK_SEND_ERRNO + Z.of_nat (j - 16))
             by (unfold NK_N_CHUNKS, NK_SEND_ERRNO; lia).
           exact (Hgd (j - 16)%nat ltac:(lia)).
        -- rewrite kgn_bs_hi by (exact HL0 || exact Hhi).
           rewrite <- (HAb i Hi). apply (mbyte_of_aview SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms4)).
           apply UN; [unfold LA_G_NL, NK_SIZE in *; lia|].
           intros [Hx | [Hx | Hx]].
           ++ unfold LA_G_NL, NK_SIZE in *. rewrite HKA in Hsp. lia.
           ++ unfold apart_gnl in HCAG. unfold ka0 in Hx. unfold NK_SIZE in *. lia.
           ++ unfold NK_OPEN in *. lia.
    + (* writable *)
      intros i Hi. rewrite HL3, <- HAL in Hi. exact (writable_at_grows SEGS _ _ _ HG (HAW i Hi)).
    + exact HL3.
    + (* kgnl *)
      unfold kgnl. split; [exact HL3|]. split; [exact (kgn_bs_skipn _ ve vs vd HL0)|].
      unfold nk_n_chunks, nk_next, nk_end_errno, nk_socket_errno, nk_send_errno, fld_u32.
      rewrite (kgn_rdn_n_chunks _ ve vs vd HL0), (kgn_rdn_next _ ve vs vd HL0),
        (kgn_rdn_end _ ve vs vd HL0 Rve), (kgn_rdn_socket _ ve vs vd HL0 Rvs), (kgn_rdn_send _ ve vs vd HL0 Rvd).
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Hve|]. split; [exact Hvs|]. split; [exact Hvd|].
      intros i Hi. lia.
  - (* kla_at *)
    apply (kla_frame (kgn_X cx) W3 ms3 W3 ms4 UN HP); [|exact HLA].
    intros a Ha [Hx | [Hx | Hx]].
    + unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in Ha. rewrite HKA in Hsp. lia.
    + unfold apart in HCAL. unfold ka0 in Hx. unfold LONG_ALIAS_SIZE in *. lia.
    + unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE, LA_G_NL, NK_N_CHUNKS, NK_OPEN in *. lia.
Qed.

(* ==========================================================================
   THE PHASE: kin_err (+0x3b4) -> kin_setup (+0x494) / kin_exit (+0x2140)
   ========================================================================== *)

(* a symbolic value of an atom, its value substituted *)
Ltac gn_den :=
  cbn [sv_denot];
  repeat match goal with H : bv_unsigned (ew ?E ?n) = _ |- context [bv_unsigned (ew ?E ?n)] => rewrite H end;
  first [reflexivity | f_equal; ring].

(* after a run: the bytes outside kgn_X are the cut's and presence grows, from the run's frame and growth *)
Ltac gn_un HFr HF HG UN HP cx ms3 :=
  lazymatch type of HFr with
  | frame_of ?Ex ?rs (mrestrict ?H (ms_mem ?m0)) (mrestrict ?H (ms_mem ?m1)) =>
    let UN' := fresh "UNn" in let HP' := fresh "HPn" in
    assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ kgn_X cx a ->
              aview pa_segs H (ms_mem m1) a = aview pa_segs H (ms_mem ms3) a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hx := fresh "Hx" in
      intros a Ha Hx; refine (eq_trans _ (UN a Ha Hx));
      refine (kept_of_frame Ex rs H (ms_mem m0) (ms_mem m1) (kgn_X cx) HFr _ a Ha Hx);
      let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let x := fresh "x" in
      let Hin := fresh "Hin" in let Hxx := fresh "Hxx" in
      intros bb wl wh x Hin Hxx; vm_compute in Hin;
      repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
        [ injection Hq as <- <- <-; cbn [base_val] in Hxx;
          repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Hxx end;
          unfold kgn_X, NK_N_CHUNKS, NK_OPEN; clear - Hxx; lia
        | ]);
      destruct Hin
    | ];
    assert (HP' : forall a, apresent H (ms_mem ms3) a -> apresent H (ms_mem m1) a)
      by (let a := fresh "a" in let Hp := fresh "Hp" in
          intros a Hp; exact (su_apres_grows H (ms_mem m0) (ms_mem m1) a HG (HP a Hp)));
    clear UN HP HFr HF HG; rename UN' into UN; rename HP' into HP
  end.

(* a run's writes: the spill area lies in kernel's window, the cursor and g_nl's words in its write set *)
Ltac gn_awr AJW cx SPW :=
  cbn [ss_mem];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Ha end;
      first [ exfalso; clear - Ha; lia
            | left; split; [left; clear - Ha SPW; lia | clear - Ha SPW; lia]
            | exact (AJW a (kgn_kE_cur cx a ltac:(clear - Ha; lia)))
            | exact (AJW a (kgn_kE_gnl cx a ltac:(unfold NK_N_CHUNKS, NK_OPEN; clear - Ha; lia))) ]
    | ]);
  apply awr_ok_x_nil.

Theorem kn_gnl : forall POST,
  kfrom SK B POST (kin_setup B) -> kfrom SK B POST (kin_exit B) -> kfrom SK B POST (kin_err B).
Proof.
intros POST HSET HEX cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
destruct HI as (fl & e & ei & adv & Hfl & He & Hei & Hadv3 & HK).
pose proof HK as HK0.
destruct HK as (Hkms & Hkr0 & Hkre & Hksv & Hkfr & Hksh & Hksl & Hkjbk & Hkkept & Hkcur & Hkg & Hkla).
pose proof HB as HB'. unfold kbase in HB'.
destruct HB' as (HPRE & HRD & HKP & HNK & HWF & HWP & HWN & HWPr & HWNr & HD & HDL & HLA & HLAL).
pose proof HPRE as (HJ0 & HGok & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _ & _ & Hajw & _).
destruct HKP as (kbs0 & _ & _ & _ & _ & HCUR0 & _ & HCR & HCAF & HCAG & HCAL & HNE & HNER & HNEAP & _).
destruct HCUR0 as (wp' & wn' & HWP' & HWN' & HWPr' & HWNr' & _ & _ & HIR & HIH & HIAP).
assert (Ewp : wp' = k_wp cx).
{ pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HWP' HWPr') as A1.
  pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HWP HWPr) as A2.
  unfold ka0 in A2. rewrite A1 in A2. injection A2 as A2. exact A2. }
assert (Ewn : wn' = k_wn cx).
{ pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HWN' HWNr') as A1.
  pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HWN HWNr) as A2.
  unfold ka0 in A2. rewrite A1 in A2. injection A2 as A2. exact A2. }
subst wp' wn'. clear HWP' HWN' HWPr' HWNr'.
change (spZ (k_regs cx)) with (ksp cx) in Hwlo, Hwhi.
assert (HKA : KERNEL_AK = 4640) by reflexivity. rewrite HKA in Hwlo.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (kn_base_facts SK B cx HB) as (Hsp & Hs1 & Hrow1 & Hrow2). rewrite HKA in Hsp.
assert (Hs1al : ksp1 cx mod 32 = 0) by (unfold ksp1, ksp1_of; rewrite Z.mul_comm; apply Z_mod_mult).
destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 Hkjbk) as (HF4 & HFc & _ & _ & _ & _ & Hfpos).
assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity. rewrite Hfb in HFc.
pose proof HJ0 as HAR0. apply ajournal_gx_AR in HAR0.
pose proof HJ as HAR3. apply ajournal_gx_AR in HAR3.
pose proof (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as (RW0l & RW0h).
pose proof (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (RW3l & RW3h).
pose proof (aj_frame_addr SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as FA0.
pose proof (aj_frame_addr SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as FA3.
pose proof (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HPRES.
pose proof Hkjbk as (_ & _ & HPERM & HNIN & (S1 & W1 & mem1 & md1 & HAR1 & Hfr1 & Hbl1) & _).
pose proof Hkkept as (HAK & _).
pose proof (akept_drop_side SK SEGS B LAWS pa_segs_low (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) W3 (ms_mem ms3)
  (ksp cx - KERNEL_AK) (ksp cx) (kE cx) S1 W1 mem1 md1 KN_CID fpos HAR1 Hfr1 Hbl1 HAK) as HAKE.
(* the bytes kernel reads but does not write are the call's *)
assert (VIEW : forall a, kernel_ard SEGS (k_regs cx) (km0 cx) a -> ~ kE cx a ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (k_W cx)) (k_memc cx) a).
{ intros a Hrd Hne.
  exact (akept_akb_gx SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W3 (ms_mem ms3) _ _ (kE cx) a HJ0 HAKE
    (HRD a Hrd) Hne). }
assert (NKE : forall lo n a, apart_gnl LA_G_NL lo n -> apart lo n LA_LONG_ALIAS (LONG_ALIAS_SIZE + 3) ->
  apart lo n (ka0 cx) 16 -> lo <= a < lo + n -> ~ kE cx a).
{ intros lo n a G1 G2 G3 Ha (r & Hin & Hr). unfold kernel_awr in Hin. cbn [In] in Hin.
  unfold apart_gnl, apart, ka0 in *.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr;
    clear - G1 G2 G3 Ha Hr; unfold NK_CHUNK, NK_OPEN, NK_SIZE, LONG_ALIAS_SIZE in *; lia. }
assert (CB : 0 <= ka0 cx /\ ka0 cx + 16 <= 2 ^ 47 /\ kgn_off_band (ka0 cx) 16).
{ destruct (kgn_akb_band (SK := SK) SEGS B LAWS pa_segs_low (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx)
    (ksp cx - KERNEL_AK) (ksp cx) (ka0 cx) 16 HAR0 Hrow1 Hrow2 ltac:(lia) (fun x Hx => HRD x (kgn_cur_ard cx x Hx)))
    as (B1 & B2 & B3).
  split; [exact B1|]. split; [exact B2|]. exact B3. }
assert (FM : fmiss (k_lyc cx) (k_Sc cx) (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a)).
{ apply fmiss_or.
  - apply (fmiss_app SEGS B LAWS (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx) (kE cx) HAR0).
    intros a (r & Hin & Hr). unfold kernel_awr in Hin. cbn [In] in Hin.
    pose proof CB as (_ & _ & CB3). unfold kgn_off_band in CB3.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + left. unfold LA_G_NL, NK_CHUNK, NK_OPEN, kLowMemEnd in *. lia.
    + left. unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE, kLowMemEnd in *. lia.
    + unfold ka0 in CB3. unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia.
  - exact (fmiss_side SEGS B (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx) KN_CID fpos HAR0
      ltac:(unfold KN_CID; lia) Hfpos HNIN). }
(* the shadow byte of a read-set byte is the call's (LinkWalkShadow.v sbyte_transport's saddr half) *)
assert (SADDR : forall x, kernel_ard SEGS (k_regs cx) (km0 cx) x ->
  saddr (aview SEGS (w_H (k_W cx)) (k_memc cx)) x -> saddr (aview SEGS (w_H W3) (ms_mem ms3)) x).
{ intros x Hrd Hs.
  refine (kgn_saddr_transport SEGS B LAWS TB pa_img_range (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx)
    ly3 S3 W3 (ms_mem ms3) md3 (ksp cx - KERNEL_AK) (ksp cx) _ x HAR0 HAR3 _ _ _ HAK FM (HRD x Hrd) Hs).
  - rewrite RW3l, RW0l. reflexivity.
  - rewrite RW3h, RW0h. reflexivity.
  - intros b m Hin. exact (Permutation_in _ (Permutation_sym HPERM) Hin). }
(* nl_errno.e's element and its shadow byte at the cut *)
set (ve := nth (Z.to_nat ei) nl_errno_tab 0) in *.
assert (Hve : In ve nl_errno_tab) by (apply nth_In; cbn [length nl_errno_tab]; lia).
assert (Rve : 0 <= ve < 2 ^ 31).
{ pose proof Hve as H. cbn [nl_errno_tab In] in H.
  unfold E_NOBUFS, E_INTR, E_AGAIN, E_PERM, E_MFILE, E_CONNREFUSED in H. lia. }
assert (Re : 0 <= e < 2 ^ 31).
{ pose proof He as H. cbn [nl_errno_tab In] in H.
  unfold E_NOBUFS, E_INTR, E_AGAIN, E_PERM, E_MFILE, E_CONNREFUSED in H. lia. }
assert (NEV : val_mem SEGS (rdW W3 (ms_mem ms3)) (LA_NL_ERRNO_E + 4 * ei) 4 ve).
{ pose proof HNEAP as (_ & NG & NL & NC).
  apply (val_mem_moved SEGS (w_H (k_W cx)) (w_H W3) (k_memc cx) (ms_mem ms3)
           (LA_NL_ERRNO_E + 4 * ei) (LA_NL_ERRNO_E + 4 * ei) 4 ve); [|exact (HNE ei Hei)].
  intros k Hk. apply VIEW.
  - unfold kernel_ard. right; right; right; left. lia.
  - apply (NKE LA_NL_ERRNO_E 24); [exact NG | exact NL | exact NC | lia]. }
assert (NESH : aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (LA_NL_ERRNO_E + 4 * ei)) = Some 0).
{ set (x := LA_NL_ERRNO_E + 8 * (ei / 2) + 7).
  assert (Hx : LA_NL_ERRNO_E <= x < LA_NL_ERRNO_E + 24) by (unfold x; lia).
  destruct (SADDR x ltac:(unfold kernel_ard; right; right; right; left; exact Hx) (HNER x Hx)) as (s & Hs & Hok).
  assert (Esh : shadow_of_addr SHADOW_OFF x = shadow_of_addr SHADOW_OFF (LA_NL_ERRNO_E + 4 * ei))
    by (unfold x, shadow_of_addr, LA_NL_ERRNO_E; lia).
  rewrite <- Esh, Hs. f_equal. destruct Hok as [Hok | (Hok & Hok8)]; [exact Hok|].
  exfalso. unfold x, LA_NL_ERRNO_E in Hok. clear - Hok Hok8 Hei. lia. }
(* the cursor's shadow at the cut *)
assert (CURSH : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (ka0 cx) 16).
{ intros x Hx. exact (SADDR x (kgn_cur_ard cx x Hx) (HCR x Hx)). }
(* the cursor at the cut *)
pose proof Hkcur as (Hadv & HCP & HCN & HCWR).
assert (PR : 0 <= k_wp cx + adv < 2 ^ 64).
{ destruct (Z.eq_dec (k_wn cx) 0) as [Hz | Hnz]; [lia|].
  assert (Hrd : kernel_ard SEGS (k_regs cx) (km0 cx) (k_wp cx + k_wn cx - 1)).
  { unfold kernel_ard. right; left. exists (k_wp cx), (k_wn cx).
    refine (conj HWP (conj HWN (conj HWPr (conj HWNr _)))). lia. }
  destruct (kn_ard_bound SK B LAWS cx _ HB Hrd) as (Hb & _). lia. }
set (p := k_wp cx + adv) in *.
set (bvv := match aview SEGS (w_H W3) (ms_mem ms3) p with Some v => v | None => 0 end).
set (shv := match aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF p) with Some v => v | None => 0 end).
assert (Rbvv : 0 <= bvv < 256).
{ unfold bvv. destruct (aview SEGS (w_H W3) (ms_mem ms3) p) as [v|] eqn:Q; [exact (kgn_aview_range _ _ _ _ _ Q) | lia]. }
assert (Rshv : 0 <= shv < 256).
{ unfold shv. destruct (aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF p)) as [v|] eqn:Q;
    [exact (kgn_aview_range _ _ _ _ _ Q) | lia]. }
(* ---- the environment ---- *)
remember (Eimg (Ereg (ms_regs ms3) (gn_ext p (k_wn cx - adv) bvv shv ve ei))) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
assert (ER : forall (j : nat) (r : bv 5), Z.of_nat j = bv_unsigned r -> ew E j = getr (ms_regs ms3) r)
  by (intros j r Hj; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ j r Hj)).
assert (EXT : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (gn_ext p (k_wn cx - adv) bvv shv ve ei) (Z_to_bv 64 0))
  by (intros j Hj; rewrite HEdef, Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EXT 0%nat ltac:(lia)) as E32. pose proof (EXT 1%nat ltac:(lia)) as E33.
pose proof (EXT 2%nat ltac:(lia)) as E34. pose proof (EXT 3%nat ltac:(lia)) as E35.
pose proof (EXT 4%nat ltac:(lia)) as E36. pose proof (EXT 5%nat ltac:(lia)) as E37.
pose proof (EXT 6%nat ltac:(lia)) as E38. pose proof (EXT 7%nat ltac:(lia)) as E39.
cbn [gn_ext nth Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39.
unfold kregs_eq in Hkre. rewrite Forall_forall in Hkre.
pose proof (Hkre (19%nat, kF cx fpos) ltac:(gn_inl)) as R19. pose proof (Hkre (21%nat, kF cx fpos) ltac:(gn_inl)) as R21.
pose proof (Hkre (22%nat, kFSH cx fpos) ltac:(gn_inl)) as R22. pose proof (Hkre (24%nat, kS8 cx) ltac:(gn_inl)) as R24.
pose proof (Hkre (10%nat, ei) ltac:(gn_inl)) as R10. pose proof (Hkre (11%nat, ka0 cx / 8) ltac:(gn_inl)) as R11.
pose proof (Hkre (12%nat, LA_NL_ERRNO_E) ltac:(gn_inl)) as R12. pose proof (Hkre (13%nat, fl) ltac:(gn_inl)) as R13.
pose proof (Hkre (15%nat, e) ltac:(gn_inl)) as R15.
cbn [fst snd] in R19, R21, R22, R24, R10, R11, R12, R13, R15.
pose proof Hkr0 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
assert (RF : 0 <= kF cx fpos < 2 ^ 64) by lia.
assert (RFSH : 0 <= kFSH cx fpos < 2 ^ 64) by (unfold kFSH, shadow_of_addr, SHADOW_OFF; lia).
assert (RA0 : 0 <= ka0 cx < 2 ^ 64) by (pose proof CB as (CB1 & CB2 & _); lia).
assert (U9 : bv_unsigned (ew E 9) = ksp1 cx)
  by (rewrite (ER 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = ka0 cx)
  by (rewrite (ER 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite (ER 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U19 : bv_unsigned (ew E 19) = kF cx fpos)
  by (rewrite (ER 19%nat (Z_to_bv 5 (Z.of_nat 19)) ltac:(reflexivity)), R19; unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = kF cx fpos)
  by (rewrite (ER 21%nat (Z_to_bv 5 (Z.of_nat 21)) ltac:(reflexivity)), R21; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = kFSH cx fpos)
  by (rewrite (ER 22%nat (Z_to_bv 5 (Z.of_nat 22)) ltac:(reflexivity)), R22; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = ei)
  by (rewrite (ER 10%nat (Z_to_bv 5 (Z.of_nat 10)) ltac:(reflexivity)), R10; unfold w64; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = LA_NL_ERRNO_E)
  by (rewrite (ER 12%nat (Z_to_bv 5 (Z.of_nat 12)) ltac:(reflexivity)), R12; unfold w64; apply unsigned_lit_small;
      unfold LA_NL_ERRNO_E; lia).
assert (U13 : bv_unsigned (ew E 13) = fl)
  by (rewrite (ER 13%nat (Z_to_bv 5 (Z.of_nat 13)) ltac:(reflexivity)), R13; unfold w64; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E 15) = e)
  by (rewrite (ER 15%nat (Z_to_bv 5 (Z.of_nat 15)) ltac:(reflexivity)), R15; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = p) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = k_wn cx - adv) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = bvv) by (rewrite E34; unfold w64; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = shadow_of_addr SHADOW_OFF p)
  by (rewrite E35; unfold w64; apply unsigned_lit_small; unfold shadow_of_addr, SHADOW_OFF; lia).
assert (U36 : bv_unsigned (ew E 36) = shv) by (rewrite E36; unfold w64; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = ve) by (rewrite E37; unfold w64; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = LA_NL_ERRNO_E + 4 * ei)
  by (rewrite E38; unfold w64; apply unsigned_lit_small; unfold LA_NL_ERRNO_E; lia).
assert (U39 : bv_unsigned (ew E 39) = shadow_of_addr SHADOW_OFF (LA_NL_ERRNO_E + 4 * ei))
  by (rewrite E39; unfold w64; apply unsigned_lit_small; unfold shadow_of_addr, SHADOW_OFF, LA_NL_ERRNO_E; lia).
assert (U243 : bv_unsigned (ew E 243) = LA_G_NL).
{ rewrite HEdef, Eimg_img by (unfold A_TEXT, A_LIM; lia). change 243%nat with (A_OBJ 2).
  rewrite (lv_obj LV 2%nat) by (unfold link_nobj; lia). change (link_obj 2) with 6146752.
  apply unsigned_lit_small. unfold LA_G_NL. lia. }
(* the registers of the state: a1 and s8 as the (x >> 3) + Bx expressions *)
assert (HRG0 : regs_ok E gn_regs0 (ms_regs ms3)).
{ assert (BVD : forall (r : bv 5) (z : Z), 0 <= z < 32 -> {r = Z_to_bv 5 z} + {r <> Z_to_bv 5 z}).
  { intros r z Hz. destruct (Z.eq_dec (bv_unsigned r) z) as [Q | Q].
    - left. apply bv_eq. rewrite Q, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
      change (bv_modulus 5) with 32. lia.
    - right. intros Hq. apply Q. rewrite Hq, Z_to_bv_unsigned. apply bv_wrap_small.
      change (bv_modulus 5) with 32. lia. }
  intros r. unfold gn_regs0.
  destruct (BVD r 24 ltac:(lia)) as [-> | N24].
  - rewrite sr_get_set_same by reflexivity. change (Z_to_bv 5 24) with (Z_to_bv 5 (Z.of_nat 24)). rewrite R24.
    unfold w64, kS8. apply bv_eq. unfold gn_e24. cbn [sv_denot]. rewrite U18, U20, Z.add_0_r.
    rewrite kgn_shadow_u by lia. apply unsigned_lit_small. unfold shadow_of_addr, SHADOW_OFF. lia.
  - rewrite sr_get_set_other by exact N24. destruct (BVD r 11 ltac:(lia)) as [-> | N11].
    + rewrite sr_get_set_same by reflexivity. change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)). rewrite R11.
      unfold w64. apply bv_eq. unfold gn_e11. cbn [sv_denot]. rewrite U18, Z.add_0_r, kgn_shr64 by lia.
      rewrite !unsigned_lit_small by lia. change (2 ^ 3) with 8. reflexivity.
    + rewrite sr_get_set_other by exact N11. rewrite HEdef. apply regs_ok_Eimg_Ereg. }
unfold kslots_eq in Hksl. rewrite Forall_forall in Hksl.
pose proof (Hksl (KS_W1SH, kFSH cx fpos + 4) ltac:(gn_inl)) as SL_W1SH.
pose proof (Hksl (KS_W2SH, kFSH cx fpos + 0x226) ltac:(gn_inl)) as SL_W2SH.
pose proof (Hksl (KS_F2, kF cx fpos) ltac:(gn_inl)) as SL_F2.
pose proof (Hksl (KS_CN, ka0 cx + 8) ltac:(gn_inl)) as SL_CN.
cbn [fst snd] in SL_W1SH, SL_W2SH, SL_F2, SL_CN.
pose proof Hkg as HKG. cbn [kgnl_at] in HKG. destruct HKG as ((HGB & HGW) & HGL).
(* ---- the symbolic state at +0x3b4, for the cursor's n as nv ---- *)
assert (HSgen : forall nv nf, sv_denot E nv = Z_to_bv 64 (k_wn cx - adv) -> afact_ok E 33 nf ->
  st_ok_pi SEGS pa_val E (gn_ss nv nf) (restrict (w_H W3) ms3)).
{ intros nv nf Hnv Hnf.
  pose proof Hkms as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  rewrite (su_ms_shape ms3 (BASE + kpc KP_ERR) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
  rewrite restrict_mkst_fx. unfold gn_ss. apply pa_entry_st_ok_full.
  - exact HRG0.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
    + unfold gn_spill, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply kn_apresent_writable. apply HPRES. lia. }
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * apply (su_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x50 (SOff 22 4) (kFSH cx fpos + 4));
          [gn_den | exact SL_W1SH].
      * apply (su_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x80 (SOff 22 0x226) (kFSH cx fpos + 0x226));
          [gn_den | exact SL_W2SH].
      * apply (su_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xb0 (SOff 18 8) (ka0 cx + 8));
          [gn_den | exact SL_CN].
      * apply (su_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xf0 (SOff 19 0) (kF cx fpos));
          [gn_den | exact SL_F2].
    + unfold gn_cur, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U18.
      pose proof CB as (CB1 & CB2 & _).
      split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HCWR o Ho)|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E _ (ka0 cx) 0 8 (SOff 32 0) p);
          [gn_den | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | rewrite Z.add_0_r; exact HCP].
      * apply (chunk_ok_val SEGS E _ (ka0 cx) 8 8 nv (k_wn cx - adv));
          [exact Hnv | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact HCN].
    + unfold gn_g, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U243.
      split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply HGW. rewrite HGL. unfold NK_SIZE. lia.
    + unfold gn_ne, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U38.
      split; [unfold LA_NL_ERRNO_E; lia|]. split; [unfold LA_NL_ERRNO_E; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (LA_NL_ERRNO_E + 4 * ei) 0 4 (SOff 37 0) ve);
        [gn_den | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia | rewrite Z.add_0_r; exact NEV].
    + unfold gn_nesh, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U39.
      split; [unfold shadow_of_addr, SHADOW_OFF, LA_NL_ERRNO_E; lia|].
      split; [unfold shadow_of_addr, SHADOW_OFF, LA_NL_ERRNO_E; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 1 (SLit 0) 0);
        [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact (kgn_vm1 _ _ _ _ _ NESH)].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, gn_spill, gn_cur, gn_g, gn_ne, gn_nesh.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18, U243, U38, U39.
    pose proof CB as (CB1 & CB2 & CB3). unfold kgn_off_band in CB3.
    pose proof HNEAP as (_ & _ & _ & NC).
    unfold apart in NC. unfold apart_frame in HCAF. unfold apart_gnl in HCAG.
    change (aarg (k_regs cx) 0) with (ka0 cx) in NC, HCAF, HCAG. change (spZ (k_regs cx)) with (ksp cx) in HCAF.
    clear - CB1 CB2 CB3 NC HCAF HCAG Hsp Hs1 C1a Hei HKA.
    unfold LA_G_NL, LA_NL_ERRNO_E, shadow_of_addr, SHADOW_OFF, NK_SIZE in *.
    repeat split; lia.
  - unfold facts_ok, gn_atoms, gn_alias_ne. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    + split; [|split; [|split; [|split; [|split; [exact Hnf | exact I]]]]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
      * rewrite U9. change (2 ^ 5) with 32. split; [lia | split; [exact Hs1al | lia]].
      * rewrite U18. change (2 ^ 0) with 1. rewrite Z.mod_1_r. pose proof CB as (CB1 & CB2 & _). lia.
      * rewrite U20. change (2 ^ 0) with 1. rewrite Z.mod_1_r. unfold SHADOW_OFF. lia.
      * rewrite U243. unfold LA_G_NL. split; [lia|]. split; [reflexivity | lia].
    + assert (AL2 : sv_denot E gn_a39 = sv_denot E (SOff 39 0)).
      { unfold gn_a39. apply bv_eq. cbn [sv_denot]. rewrite U38, U20, U39, !Z.add_0_r.
        rewrite kgn_shadow_u by (unfold LA_NL_ERRNO_E; lia). symmetry. apply unsigned_lit_small.
        unfold shadow_of_addr, SHADOW_OFF, LA_NL_ERRNO_E. lia. }
      split; [|split; [exact AL2 | split; [|exact I]]].
      * unfold gn_a38. apply bv_eq. cbn [sv_denot]. rewrite kgn_add64, kgn_shl64 by lia.
        rewrite U10, U12, U38. rewrite !unsigned_lit_small by (unfold LA_NL_ERRNO_E; lia).
        unfold LA_NL_ERRNO_E. lia.
      * change (sv_denot E (SAlu ALU_ADD gn_a39 (SLit 0))) with (alu64 ALU_ADD (sv_denot E gn_a39) (Z_to_bv 64 0)).
        rewrite AL2. apply bv_eq. rewrite kgn_add64. rewrite (Z_to_bv_unsigned 64 0). change (bv_wrap 64 0) with 0.
        rewrite Z.add_0_r. apply Z.mod_small. apply u64_range. }
(* the shadow-table entry of the cursor: its 16 bytes addressable, outside the shadow band *)
assert (SHOK : sh_ok SEGS gn_Bx gn_SH E (mrestrict (w_H W3) (ms_mem ms3))).
{ unfold sh_ok, gn_SH. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (UBx : U E gn_Bx = SHADOW_OFF)
    by (unfold U, gn_Bx; cbn [sv_denot]; rewrite U20, Z.add_0_r; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (UA : U E (SOff 18 0) = ka0 cx)
    by (unfold U; cbn [sv_denot]; rewrite U18, Z.add_0_r; apply unsigned_lit_small; lia).
  rewrite UBx, UA. split.
  - rewrite Z.add_0_r. change (16 - 0) with 16. exact CURSH.
  - intros a Ha. pose proof CB as (_ & _ & CB3). unfold kgn_off_band in CB3.
    change (Z.min 0 16) with 0 in Ha. change (Z.max 0 16) with 16 in Ha. lia. }
(* ---- what the runs share ---- *)
assert (AJW : forall a, kE cx a -> ajw B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
  (k_ly cx) (k_S cx) ly3 S3 ((KN_CID, fpos) :: k_own cx) a).
{ intros a Ha. eapply ajw_mono; [exact (Hajw a Ha) | | |].
  - intros b m Hin. exact (Permutation_in _ (Permutation_sym HPERM) Hin).
  - intros x Hx. right. exact Hx.
  - intros c q. rewrite (FA3 c q), (FA0 c q). reflexivity. }
assert (SPW : k_sp0 cx - k_STK cx <= ksp1 cx + 24 /\ ksp1 cx + 248 <= k_sp0 cx) by lia.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ kgn_X cx a ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H W3) (ms_mem ms3) a) by reflexivity.
assert (HP : forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms3) a) by (intros a Ha; exact Ha).
assert (RX : forall ssx msx (r : bv 5), st_ok_pi SEGS pa_val E ssx (restrict (w_H W3) msx) ->
  sr_get (ss_regs ssx) r = sr_get gn_regs0 r -> getr (ms_regs msx) r = getr (ms_regs ms3) r).
{ intros ssx msx r HSx Hr. rewrite (st_ok_pi_restrict_reg (w_H W3) E ssx msx r HSx), Hr. symmetry. exact (HRG0 r). }
assert (RV : forall ssx msx (r : bv 5) ex v, st_ok_pi SEGS pa_val E ssx (restrict (w_H W3) msx) ->
  sr_get (ss_regs ssx) r = ex -> sv_denot E ex = Z_to_bv 64 v -> getr (ms_regs msx) r = Z_to_bv 64 v).
{ intros ssx msx r ex v HSx Hr Hv. rewrite (st_ok_pi_restrict_reg (w_H W3) E ssx msx r HSx), Hr. exact Hv. }
(* the two masked errno words, 0 or e *)
set (vs := bv_unsigned (sv_denot E gn_es)).
set (vd := bv_unsigned (sv_denot E gn_ed)).
assert (UE15 : bv_unsigned (sv_denot E (SOff 15 0)) = e)
  by (cbn [sv_denot]; rewrite U15, Z.add_0_r; apply unsigned_lit_small; lia).
assert (Hvs : vs = 0 \/ vs = e).
{ unfold vs. change (sv_denot E gn_es) with (alu64 ALU_AND (alu64 ALU_SRA (alu64 ALU_SLL (sv_denot E (SOff 13 0))
    (Z_to_bv 64 63)) (Z_to_bv 64 63)) (sv_denot E (SOff 15 0))).
  rewrite <- UE15. exact (kgn_and_mask _ _ (kgn_mask64 _)). }
assert (Hvd : vd = 0 \/ vd = e).
{ unfold vd. change (sv_denot E gn_ed) with (alu64 ALU_AND (sv_denot E (SAluw ALU_SRA (SAlu ALU_SLL (SOff 13 0)
    (SLit 30)) (SLit 31))) (sv_denot E (SOff 15 0))).
  rewrite <- UE15. exact (kgn_and_mask _ _ (kgn_mask32s _ _)). }
assert (Rvs : 0 <= vs < 2 ^ 32) by (destruct Hvs as [-> | ->]; lia).
assert (Rvd : 0 <= vd < 2 ^ 32) by (destruct Hvd as [-> | ->]; lia).
assert (Ivs : kgn_ok0 vs) by (unfold kgn_ok0; destruct Hvs as [-> | ->]; [left; reflexivity | right; exact He]).
assert (Ivd : kgn_ok0 vd) by (unfold kgn_ok0; destruct Hvd as [-> | ->]; [left; reflexivity | right; exact He]).
clear Hvs Hvd.
pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
pose (BR := paj_branch (PI := PI)).
destruct (Z.eq_dec (k_wn cx - adv) 0) as [Hn0 | Hn1].
- (* ---- (a) the cursor is empty: +0x3b4 .. +0x434 -> +0x2140, j = 0, adv unchanged ---- *)
  assert (HS : st_ok_pi SEGS pa_val E (gn_ss (SLit 0) (mkAF 0 0 0)) (restrict (w_H W3) ms3)).
  { apply HSgen.
    - cbn [sv_denot]. rewrite Hn0. reflexivity.
    - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U33, Hn0. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
  norm_pi HS.
  paj_run_to_tok RUNTO HS HJ SHOK gn_span (kpc KP_EXIT).
  { gn_awr AJW cx SPW. }
  gn_un HFr HF HG UN HP cx ms3.
  spregion HS 0%nat HRs. spregion HS 1%nat HRc. spregion HS 2%nat HRg.
  pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ ms HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
  destruct (ms_shape_mkst SEGS ms _ _ _ Hshape) as (Q2 & Q3 & Q4 & Q5 & Q6 & Q1).
  lazymatch type of HJ with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdF _ =>
    apply (HEX cx fpos k2 ly3 S3 W3 ms mdF HB HJ Hfrm) end.
  unfold kin_exit. exists 0, adv. split; [lia|].
  apply (kgn_kat cx fpos _ _ adv k2 ly3 S3 W3 ms3 md3 KP_EXIT _ _ adv ms _ ve vs vd HB HK0).
  + split; [rewrite Q1; reflexivity|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
    split; [exact Q5 | exact Q6].
  + refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite (RX _ _ _ HS) by (vm_compute; reflexivity); assumption.
  + apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    rewrite (RX _ _ _ HS) by (vm_compute; reflexivity). exact R24.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
    * apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ KS_FSH (SOff 22 0) (kFSH cx fpos)
        HRs U9); [gn_inl | gn_den | exact RFSH].
    * apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ KS_FRES (SOff 19 0) (kF cx fpos)
        HRs U9); [gn_inl | gn_den | exact RF].
    * apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ KS_F (SOff 21 0) (kF cx fpos)
        HRs U9); [gn_inl | gn_den | exact RF].
  + repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  + repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  + exact UN.
  + exact HP.
  + lia.
  + pose proof (field_of_region E _ 18%nat (ka0 cx) _ _ _ _ _ 0 8 (SOff 32 0) p HRc U18 ltac:(gn_inl) ltac:(gn_den)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as F.
    rewrite Z.add_0_r in F. exact F.
  + pose proof (field_of_region E _ 18%nat (ka0 cx) _ _ _ _ _ 8 8 (SLit 0) 0 HRc U18 ltac:(gn_inl) ltac:(reflexivity)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as F.
    rewrite Hn0. exact F.
  + exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262656 8 (SLit 0) 0 HRg U243 ltac:(gn_inl) ltac:(reflexivity)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)).
  + exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262664 4 (SExt true 32 (SOff 37 0)) ve HRg U243
      ltac:(gn_inl) ltac:(cbn [sv_denot]; rewrite U37, Z.add_0_r; apply kgn_sext32_small; lia)
      ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)).
  + exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262668 4 gn_es vs HRg U243
      ltac:(gn_inl) ltac:(symmetry; apply Z_to_bv_bv_unsigned)
      ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)).
  + exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262672 4 gn_ed vd HRg U243
      ltac:(gn_inl) ltac:(symmetry; apply Z_to_bv_bv_unsigned)
      ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)).
  + exact Hve.
  + exact Ivs.
  + exact Ivd.
- (* ---- (b) a byte is left: +0x3b4 .. +0x418, the input byte's regions, +0x41c .. +0x48c ---- *)
  assert (Hn1' : 1 <= k_wn cx - adv) by lia. clear Hn1.
  assert (Hpi : k_wp cx <= p < k_wp cx + k_wn cx) by (unfold p; lia).
  assert (Hpard : kernel_ard SEGS (k_regs cx) (km0 cx) p).
  { unfold kernel_ard. right; left. exists (k_wp cx), (k_wn cx).
    refine (conj HWP (conj HWN (conj HWPr (conj HWNr _)))). exact Hpi. }
  destruct (kgn_akb_rng (SK := SK) SEGS B LAWS pa_segs_low (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx)
    (ksp cx - KERNEL_AK) (ksp cx) p HAR0 Hrow1 Hrow2 (HRD p Hpard)) as (PB1 & PB2).
  assert (PB : kgn_off_band p 1) by (unfold kgn_off_band; unfold SHADOW_OFF in *; lia). clear PB2.
  pose proof HIAP as (IAF & IAG & IAL & IAC).
  assert (IA : (k_wp cx + k_wn cx <= ksp cx - 4640 \/ ksp cx <= k_wp cx) /\
               (k_wp cx + k_wn cx <= LA_G_NL \/ LA_G_NL + NK_SIZE <= k_wp cx) /\
               (k_wp cx + k_wn cx <= ka0 cx \/ ka0 cx + 16 <= k_wp cx)).
  { unfold apart_frame, apart_gnl, apart in IAF, IAG, IAC. rewrite HKA in IAF. exact (conj IAF (conj IAG IAC)). }
  (* the input byte at p, at the cut *)
  assert (PV : aview SEGS (w_H W3) (ms_mem ms3) p = Some bvv).
  { pose proof (VIEW p Hpard (NKE (k_wp cx) (k_wn cx) p IAG IAL IAC Hpi)) as PV0.
    pose proof HD as (_ & _ & HDb).
    assert (Hi : (Z.to_nat adv < length (k_d cx))%nat) by lia.
    pose proof (HDb (Z.to_nat adv) Hi) as Hb. rewrite Z2Nat.id in Hb by lia.
    change (km0 cx) with (mrestrict (w_H (k_W cx)) (k_memc cx)) in Hb. fold p in Hb.
    destruct (nth_error (k_d cx) (Z.to_nat adv)) as [b|] eqn:Q; [|apply nth_error_None in Q; lia].
    assert (PV1 : aview SEGS (w_H W3) (ms_mem ms3) p = Some (bv_unsigned b)).
    { rewrite PV0. unfold aview. rewrite Hb. reflexivity. }
    unfold bvv. rewrite PV1. reflexivity. }
  (* its shadow byte, at the cut *)
  destruct (SADDR p Hpard (HIR p Hpi)) as (s & Hs & Hsok).
  assert (PSV : aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF p) = Some shv)
    by (unfold shv; rewrite Hs; reflexivity).
  assert (Es : s = shv) by (unfold shv; rewrite Hs; reflexivity). rewrite Es in Hsok. clear Hs Es.
  assert (HS : st_ok_pi SEGS pa_val E (gn_ss (SOff 33 0) (mkAF 1 (2 ^ 64 - 1) 0)) (restrict (w_H W3) ms3)).
  { apply HSgen; [gn_den|].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U33. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
  norm_pi HS.
  (* +0x3b4 .. +0x418: the end errno, the masks, g_nl's words *)
  paj_run_to_tok RUNTO HS HJ SHOK gn_span (kpc 0x41c).
  { gn_awr AJW cx SPW. }
  gn_un HFr HF HG UN HP cx ms3.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  (* the input byte and its shadow byte lie outside the writes *)
  assert (PX : ~ kgn_X cx p).
  { clear - IA Hpi Hs1 Hsp. unfold kgn_X, LA_G_NL, NK_N_CHUNKS, NK_OPEN, NK_SIZE in *. lia. }
  assert (PSX : ~ kgn_X cx (shadow_of_addr SHADOW_OFF p)).
  { pose proof CB as (_ & _ & CB3). unfold kgn_off_band in PB, CB3.
    clear - PB PB1 CB3 Hs1 Hsp C1a. unfold kgn_X, shadow_of_addr, SHADOW_OFF, LA_G_NL, NK_N_CHUNKS, NK_OPEN in *. lia. }
  assert (PVn : aview SEGS (w_H W3) (ms_mem ms1) p = Some bvv) by (rewrite UN; [exact PV | lia | exact PX]).
  assert (PSVn : aview SEGS (w_H W3) (ms_mem ms1) (shadow_of_addr SHADOW_OFF p) = Some shv)
    by (rewrite UN; [exact PSV | unfold shadow_of_addr, SHADOW_OFF; lia | exact PSX]).
  (* the input byte's aliases *)
  assert (AL35 : sv_denot E gn_a35 = sv_denot E (SOff 35 0)).
  { unfold gn_a35. apply bv_eq. cbn [sv_denot]. rewrite U32, U20, U35, !Z.add_0_r.
    rewrite kgn_shadow_u by lia. symmetry. apply unsigned_lit_small. unfold shadow_of_addr, SHADOW_OFF. lia. }
  assert (AL35' : sv_denot E (SAlu ALU_ADD gn_a35 (SLit 0)) = sv_denot E (SOff 35 0)).
  { change (sv_denot E (SAlu ALU_ADD gn_a35 (SLit 0))) with (alu64 ALU_ADD (sv_denot E gn_a35) (Z_to_bv 64 0)).
    rewrite AL35. apply bv_eq. rewrite kgn_add64. rewrite (Z_to_bv_unsigned 64 0). change (bv_wrap 64 0) with 0.
    rewrite Z.add_0_r. apply Z.mod_small. apply u64_range. }
  (* drop nl_errno.e's regions (read) *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let rs := eval vm_compute in (firstn 3 (ss_mem ss)) in
    pose proof (st_ok_pi_submem E ss _ rs HS ltac:(vm_compute; submem_tac) ltac:(vm_compute; reflexivity)) as HS1
  end.
  clear HS.
  assert (RIN : region_ok SEGS E (ms_mem (restrict (w_H W3) ms1)) gn_in).
  { cbn [ms_mem restrict mkst]. unfold gn_in, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ p 0 1 (SOff 34 0) bvv);
      [gn_den | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | rewrite Z.add_0_r; exact (kgn_vm1 _ _ _ _ _ PVn)]. }
  pose proof (st_ok_pi_add_region E _ _ gn_in HS1 ltac:(vm_compute; reflexivity) RIN
    ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, gn_in; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu end;
          clear - IA Hpi Hs1 Hsp; unfold LA_G_NL, NK_SIZE in *; repeat split; lia)) as HS2.
  clear HS1 RIN IA.
  assert (SB : SHADOW_OFF <= shadow_of_addr SHADOW_OFF p < SHADOW_OFF + 2 ^ 44) by (unfold shadow_of_addr; lia).
  destruct (Z.eq_dec shv 0) as [Hs0 | Hs1n].
  + (* ---- (b0) the granule of p is whole: its shadow byte is 0 ---- *)
    clear Hsok.
    assert (RSH : region_ok SEGS E (ms_mem (restrict (w_H W3) ms1)) (gn_shb (SLit 0))).
    { cbn [ms_mem restrict mkst]. unfold gn_shb, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U35.
      split; [clear - SB; unfold SHADOW_OFF in *; lia|]. split; [clear - SB; unfold SHADOW_OFF in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 1 (SLit 0) 0); [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
      rewrite Z.add_0_r. rewrite Hs0 in PSVn. exact (kgn_vm1 _ _ _ _ _ PSVn). }
    pose proof (st_ok_pi_add_region E _ _ (gn_shb (SLit 0)) HS2 ltac:(vm_compute; reflexivity) RSH
      ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, gn_shb, gn_in; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
            repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu end;
            pose proof CB as (_ & _ & CB3); unfold kgn_off_band in PB, CB3;
            clear - SB PB PB1 CB3 Hs1 Hsp C1a; unfold LA_G_NL, SHADOW_OFF in *; repeat split; lia)) as HS3.
    pose proof (st_ok_pi_add_alias E _ _ _ _ HS3 AL35') as HS4.
    pose proof (st_ok_pi_add_alias E _ _ _ _ HS4 AL35) as HS.
    clear HS2 HS3 HS4 RSH PVn PSVn. norm_pi HS.
    (* +0x41c .. +0x488: the cursor's n, n - 1, p + 1, the input byte, c := byte & 3; the engine stops at +0x48c *)
    paj_run_tok RUN HS HJ SHOK gn_span.
    { gn_awr AJW cx SPW. }
    gn_un HFr HF HG UN HP cx ms3.
    psrr_branch_tok RUN BR HS SHOK gn_span.
    * (* c <> 0: +0x494 *)
      paj_run_to_tok RUNTO HS HJ SHOK gn_span (kpc KP_SETUP).
      { gn_awr AJW cx SPW. }
      gn_un HFr HF HG UN HP cx ms3.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
      lazymatch goal with Hb : branch_taken BC_NE _ _ = true |- _ => rename Hb into Hcne end.
      assert (Hc0 : bv_unsigned (sv_denot E gn_ec) <> 0).
      { rewrite branch_ne_U in Hcne. apply negb_true_iff, Z.eqb_neq in Hcne.
        change (U E (SLit 0)) with 0 in Hcne. exact Hcne. }
      assert (Hc3 : 0 <= bv_unsigned (sv_denot E gn_ec) <= 3).
      { change (sv_denot E gn_ec) with (alu64 ALU_AND (sv_denot E (SExt false 8 (SOff 34 0))) (Z_to_bv 64 3)).
        apply kgn_and3_u. }
      assert (Hc1 : 1 <= bv_unsigned (sv_denot E gn_ec) <= 3) by lia. clear Hc0 Hc3.
      spregion HS 2%nat HRs. spregion HS 3%nat HRc. spregion HS 4%nat HRg.
      pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ msF HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
      destruct (ms_shape_mkst SEGS msF _ _ _ Hshape) as (Q2 & Q3 & Q4 & Q5 & Q6 & Q1).
      lazymatch type of HJ with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdF _ =>
        apply (HSET cx fpos k2 ly3 S3 W3 msF mdF HB HJ Hfrm) end.
      unfold kin_setup. exists (bv_unsigned (sv_denot E gn_ec)), (adv + 1). split; [lia|].
      apply (kgn_kat cx fpos _ _ adv k2 ly3 S3 W3 ms3 md3 KP_SETUP _ _ (adv + 1) msF _ ve vs vd HB HK0).
      { split; [rewrite Q1; reflexivity|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
        split; [exact Q5 | exact Q6]. }
      { refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
          rewrite (RX _ _ _ HS) by (vm_compute; reflexivity); assumption. }
      { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
        { rewrite (RV _ _ _ (SOff 18 8) (ka0 cx + 8) HS); [reflexivity | vm_compute; reflexivity | gn_den]. }
        { rewrite (RX _ _ _ HS) by (vm_compute; reflexivity). exact R21. }
        { rewrite (RX _ _ _ HS) by (vm_compute; reflexivity). exact R24. } }
      { repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_FSH (SOff 22 0) (kFSH cx fpos)
            HRs U9); [gn_inl | gn_den | exact RFSH]. }
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_FRES (SOff 19 0) (kF cx fpos)
            HRs U9); [gn_inl | gn_den | exact RF]. }
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_F (SOff 21 0) (kF cx fpos)
            HRs U9); [gn_inl | gn_den | exact RF]. }
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_GNL (SOff 243 0) LA_G_NL
            HRs U9); [gn_inl | gn_den | unfold LA_G_NL; lia]. }
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_W1SH (SOff 22 4) (kFSH cx fpos + 4)
            HRs U9); [gn_inl | gn_den | unfold kFSH, shadow_of_addr, SHADOW_OFF; lia]. }
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_W2SH (SOff 22 550)
            (kFSH cx fpos + 0x226) HRs U9); [gn_inl | gn_den | unfold kFSH, shadow_of_addr, SHADOW_OFF; lia]. }
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_F2 (SOff 19 0) (kF cx fpos)
            HRs U9); [gn_inl | gn_den | exact RF]. }
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_CN (SOff 18 8) (ka0 cx + 8)
            HRs U9); [gn_inl | gn_den | lia]. }
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_CSH gn_esh
            (shadow_of_addr SHADOW_OFF (ka0 cx)) HRs U9); [gn_inl | | unfold shadow_of_addr, SHADOW_OFF; lia].
          unfold gn_esh. apply bv_eq. cbn [sv_denot]. rewrite U18, U20, !Z.add_0_r, kgn_shadow_u by lia.
          symmetry. apply unsigned_lit_small. unfold shadow_of_addr, SHADOW_OFF. lia. }
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_C gn_ec
            (bv_unsigned (sv_denot E gn_ec)) HRs U9); [gn_inl | symmetry; apply Z_to_bv_bv_unsigned | apply u64_range]. } }
      { repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity. }
      { repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity. }
      { exact UN. }
      { exact HP. }
      { lia. }
      { pose proof (field_of_region E _ 18%nat (ka0 cx) _ _ _ _ _ 0 8 (SOff 32 1) (p + 1) HRc U18 ltac:(gn_inl)
          ltac:(gn_den) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as F.
        rewrite Z.add_0_r in F. replace (k_wp cx + (adv + 1)) with (p + 1) by (unfold p; lia). exact F. }
      { pose proof (field_of_region E _ 18%nat (ka0 cx) _ _ _ _ _ 8 8 (SOff 33 (-1)) (k_wn cx - adv - 1) HRc U18
          ltac:(gn_inl) ltac:(gn_den) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as F.
        replace (k_wn cx - (adv + 1)) with (k_wn cx - adv - 1) by lia. exact F. }
      { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262656 8 (SLit 0) 0 HRg U243 ltac:(gn_inl)
          ltac:(reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)). }
      { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262664 4 (SExt true 32 (SOff 37 0)) ve HRg U243
          ltac:(gn_inl) ltac:(cbn [sv_denot]; rewrite U37, Z.add_0_r; apply kgn_sext32_small; lia)
          ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
      { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262668 4 gn_es vs HRg U243
          ltac:(gn_inl) ltac:(symmetry; apply Z_to_bv_bv_unsigned)
          ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
      { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262672 4 gn_ed vd HRg U243
          ltac:(gn_inl) ltac:(symmetry; apply Z_to_bv_bv_unsigned)
          ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
      { exact Hve. }
      { exact Ivs. }
      { exact Ivd. }
    * (* c = 0: +0x2140 *)
      paj_run_to_tok RUNTO HS HJ SHOK gn_span (kpc KP_EXIT).
      { gn_awr AJW cx SPW. }
      gn_un HFr HF HG UN HP cx ms3.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
      spregion HS 2%nat HRs. spregion HS 3%nat HRc. spregion HS 4%nat HRg.
      pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ msF HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
      destruct (ms_shape_mkst SEGS msF _ _ _ Hshape) as (Q2 & Q3 & Q4 & Q5 & Q6 & Q1).
      lazymatch type of HJ with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdF _ =>
        apply (HEX cx fpos k2 ly3 S3 W3 msF mdF HB HJ Hfrm) end.
      unfold kin_exit. exists 0, (adv + 1). split; [lia|].
      apply (kgn_kat cx fpos _ _ adv k2 ly3 S3 W3 ms3 md3 KP_EXIT _ _ (adv + 1) msF _ ve vs vd HB HK0).
      { split; [rewrite Q1; reflexivity|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
        split; [exact Q5 | exact Q6]. }
      { refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
          rewrite (RX _ _ _ HS) by (vm_compute; reflexivity); assumption. }
      { apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
        rewrite (RX _ _ _ HS) by (vm_compute; reflexivity). exact R24. }
      { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_FSH (SOff 22 0) (kFSH cx fpos)
            HRs U9); [gn_inl | gn_den | exact RFSH]. }
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_FRES (SOff 19 0) (kF cx fpos)
            HRs U9); [gn_inl | gn_den | exact RF]. }
        { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_F (SOff 21 0) (kF cx fpos)
            HRs U9); [gn_inl | gn_den | exact RF]. } }
      { repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity. }
      { repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity. }
      { exact UN. }
      { exact HP. }
      { lia. }
      { pose proof (field_of_region E _ 18%nat (ka0 cx) _ _ _ _ _ 0 8 (SOff 32 1) (p + 1) HRc U18 ltac:(gn_inl)
          ltac:(gn_den) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as F.
        rewrite Z.add_0_r in F. replace (k_wp cx + (adv + 1)) with (p + 1) by (unfold p; lia). exact F. }
      { pose proof (field_of_region E _ 18%nat (ka0 cx) _ _ _ _ _ 8 8 (SOff 33 (-1)) (k_wn cx - adv - 1) HRc U18
          ltac:(gn_inl) ltac:(gn_den) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as F.
        replace (k_wn cx - (adv + 1)) with (k_wn cx - adv - 1) by lia. exact F. }
      { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262656 8 (SLit 0) 0 HRg U243 ltac:(gn_inl)
          ltac:(reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)). }
      { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262664 4 (SExt true 32 (SOff 37 0)) ve HRg U243
          ltac:(gn_inl) ltac:(cbn [sv_denot]; rewrite U37, Z.add_0_r; apply kgn_sext32_small; lia)
          ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
      { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262668 4 gn_es vs HRg U243
          ltac:(gn_inl) ltac:(symmetry; apply Z_to_bv_bv_unsigned)
          ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
      { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262672 4 gn_ed vd HRg U243
          ltac:(gn_inl) ltac:(symmetry; apply Z_to_bv_bv_unsigned)
          ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
      { exact Hve. }
      { exact Ivs. }
      { exact Ivd. }
  + (* ---- (b1) the granule of p is partial: its shadow byte s is in [1, 7] with p mod 8 < s ---- *)
    destruct Hsok as [Hz | (Hsm & Hs8)]; [exfalso; exact (Hs1n Hz)|]. clear Hs1n.
    assert (AF36 : afact_ok E 36 (mkAF 1 7 0)).
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U36. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
      pose proof (Z.mod_pos_bound p 8). lia. }
    assert (RSH : region_ok SEGS E (ms_mem (restrict (w_H W3) ms1)) (gn_shb (SOff 36 0))).
    { cbn [ms_mem restrict mkst]. unfold gn_shb, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U35.
      split; [clear - SB; unfold SHADOW_OFF in *; lia|]. split; [clear - SB; unfold SHADOW_OFF in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 1 (SOff 36 0) shv); [gn_den | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (kgn_vm1 _ _ _ _ _ PSVn). }
    pose proof (st_ok_pi_add_region E _ _ (gn_shb (SOff 36 0)) HS2 ltac:(vm_compute; reflexivity) RSH
      ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, gn_shb, gn_in; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
            repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu end;
            pose proof CB as (_ & _ & CB3); unfold kgn_off_band in PB, CB3;
            clear - SB PB PB1 CB3 Hs1 Hsp C1a; unfold LA_G_NL, SHADOW_OFF in *; repeat split; lia)) as HS3.
    pose proof (st_ok_pi_add_alias E _ _ _ _ HS3 AL35') as HS4.
    pose proof (st_ok_pi_add_alias E _ _ _ _ HS4 AL35) as HS5.
    pose proof (st_ok_pi_add_fact E _ _ 36%nat (mkAF 1 7 0) HS5 AF36) as HS.
    clear HS2 HS3 HS4 HS5 RSH PVn PSVn. norm_pi HS.
    (* +0x41c .. +0x47c, then the out-of-line slow path +0x21ec: the engine stops at `bge a2, a1` (+0x21f0) *)
    paj_run_tok RUN HS HJ SHOK gn_span.
    { gn_awr AJW cx SPW. }
    gn_un HFr HF HG UN HP cx ms3.
    psrr_branch_tok RUN BR HS SHOK gn_span.
    * (* p mod 8 >= s: the error path, refuted by saddr_ok *)
      exfalso.
      lazymatch goal with Hb : branch_taken BC_GE _ _ = true |- _ => rename Hb into Hge end.
      assert (A1 : bv_unsigned (sv_denot E (SAlu ALU_AND (SOff 32 0) (SLit 7))) = p mod 8)
        by (cbn [sv_denot]; rewrite U32, Z.add_0_r; apply kgn_and7_u; lia).
      assert (A2 : bv_unsigned (sv_denot E (SOff 36 0)) = shv)
        by (cbn [sv_denot]; rewrite U36, Z.add_0_r; apply unsigned_lit_small; lia).
      rewrite kgn_bge_small in Hge by (first [rewrite A1 | rewrite A2]; pose proof (Z.mod_pos_bound p 8); lia).
      rewrite A1, A2 in Hge. apply negb_true_iff, Z.ltb_ge in Hge. lia.
    * (* p mod 8 < s: back to +0x480; the engine stops at +0x48c *)
      paj_run_tok RUN HS HJ SHOK gn_span.
      { gn_awr AJW cx SPW. }
      gn_un HFr HF HG UN HP cx ms3.
      psrr_branch_tok RUN BR HS SHOK gn_span.
      -- (* c <> 0: +0x494 *)
         paj_run_to_tok RUNTO HS HJ SHOK gn_span (kpc KP_SETUP).
         { gn_awr AJW cx SPW. }
         gn_un HFr HF HG UN HP cx ms3.
         lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
         lazymatch goal with Hb : branch_taken BC_NE _ _ = true |- _ => rename Hb into Hcne end.
         assert (Hc0 : bv_unsigned (sv_denot E gn_ec) <> 0).
         { rewrite branch_ne_U in Hcne. apply negb_true_iff, Z.eqb_neq in Hcne.
           change (U E (SLit 0)) with 0 in Hcne. exact Hcne. }
         assert (Hc3 : 0 <= bv_unsigned (sv_denot E gn_ec) <= 3).
         { change (sv_denot E gn_ec) with (alu64 ALU_AND (sv_denot E (SExt false 8 (SOff 34 0))) (Z_to_bv 64 3)).
           apply kgn_and3_u. }
         assert (Hc1 : 1 <= bv_unsigned (sv_denot E gn_ec) <= 3) by lia. clear Hc0 Hc3.
         spregion HS 2%nat HRs. spregion HS 3%nat HRc. spregion HS 4%nat HRg.
         pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ msF HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
         destruct (ms_shape_mkst SEGS msF _ _ _ Hshape) as (Q2 & Q3 & Q4 & Q5 & Q6 & Q1).
         lazymatch type of HJ with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdF _ =>
           apply (HSET cx fpos k2 ly3 S3 W3 msF mdF HB HJ Hfrm) end.
         unfold kin_setup. exists (bv_unsigned (sv_denot E gn_ec)), (adv + 1). split; [lia|].
         apply (kgn_kat cx fpos _ _ adv k2 ly3 S3 W3 ms3 md3 KP_SETUP _ _ (adv + 1) msF _ ve vs vd HB HK0).
         { split; [rewrite Q1; reflexivity|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
           split; [exact Q5 | exact Q6]. }
         { refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
             rewrite (RX _ _ _ HS) by (vm_compute; reflexivity); assumption. }
         { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
           { rewrite (RV _ _ _ (SOff 18 8) (ka0 cx + 8) HS); [reflexivity | vm_compute; reflexivity | gn_den]. }
           { rewrite (RX _ _ _ HS) by (vm_compute; reflexivity). exact R21. }
           { rewrite (RX _ _ _ HS) by (vm_compute; reflexivity). exact R24. } }
         { repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_FSH (SOff 22 0) (kFSH cx fpos)
               HRs U9); [gn_inl | gn_den | exact RFSH]. }
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_FRES (SOff 19 0) (kF cx fpos)
               HRs U9); [gn_inl | gn_den | exact RF]. }
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_F (SOff 21 0) (kF cx fpos)
               HRs U9); [gn_inl | gn_den | exact RF]. }
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_GNL (SOff 243 0) LA_G_NL
               HRs U9); [gn_inl | gn_den | unfold LA_G_NL; lia]. }
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_W1SH (SOff 22 4)
               (kFSH cx fpos + 4) HRs U9); [gn_inl | gn_den | unfold kFSH, shadow_of_addr, SHADOW_OFF; lia]. }
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_W2SH (SOff 22 550)
               (kFSH cx fpos + 0x226) HRs U9); [gn_inl | gn_den | unfold kFSH, shadow_of_addr, SHADOW_OFF; lia]. }
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_F2 (SOff 19 0) (kF cx fpos)
               HRs U9); [gn_inl | gn_den | exact RF]. }
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_CN (SOff 18 8) (ka0 cx + 8)
               HRs U9); [gn_inl | gn_den | lia]. }
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_CSH gn_esh
               (shadow_of_addr SHADOW_OFF (ka0 cx)) HRs U9); [gn_inl | | unfold shadow_of_addr, SHADOW_OFF; lia].
             unfold gn_esh. apply bv_eq. cbn [sv_denot]. rewrite U18, U20, !Z.add_0_r, kgn_shadow_u by lia.
             symmetry. apply unsigned_lit_small. unfold shadow_of_addr, SHADOW_OFF. lia. }
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_C gn_ec
               (bv_unsigned (sv_denot E gn_ec)) HRs U9); [gn_inl | symmetry; apply Z_to_bv_bv_unsigned | apply u64_range]. } }
         { repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity. }
         { repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity. }
         { exact UN. }
         { exact HP. }
         { lia. }
         { pose proof (field_of_region E _ 18%nat (ka0 cx) _ _ _ _ _ 0 8 (SOff 32 1) (p + 1) HRc U18 ltac:(gn_inl)
             ltac:(gn_den) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as F.
           rewrite Z.add_0_r in F. replace (k_wp cx + (adv + 1)) with (p + 1) by (unfold p; lia). exact F. }
         { pose proof (field_of_region E _ 18%nat (ka0 cx) _ _ _ _ _ 8 8 (SOff 33 (-1)) (k_wn cx - adv - 1) HRc U18
             ltac:(gn_inl) ltac:(gn_den) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as F.
           replace (k_wn cx - (adv + 1)) with (k_wn cx - adv - 1) by lia. exact F. }
         { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262656 8 (SLit 0) 0 HRg U243 ltac:(gn_inl)
             ltac:(reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)). }
         { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262664 4 (SExt true 32 (SOff 37 0)) ve HRg U243
             ltac:(gn_inl) ltac:(cbn [sv_denot]; rewrite U37, Z.add_0_r; apply kgn_sext32_small; lia)
             ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
         { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262668 4 gn_es vs HRg U243
             ltac:(gn_inl) ltac:(symmetry; apply Z_to_bv_bv_unsigned)
             ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
         { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262672 4 gn_ed vd HRg U243
             ltac:(gn_inl) ltac:(symmetry; apply Z_to_bv_bv_unsigned)
             ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
         { exact Hve. }
         { exact Ivs. }
         { exact Ivd. }
      -- (* c = 0: +0x2140 *)
         paj_run_to_tok RUNTO HS HJ SHOK gn_span (kpc KP_EXIT).
         { gn_awr AJW cx SPW. }
         gn_un HFr HF HG UN HP cx ms3.
         lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
         spregion HS 2%nat HRs. spregion HS 3%nat HRc. spregion HS 4%nat HRg.
         pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ msF HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
         destruct (ms_shape_mkst SEGS msF _ _ _ Hshape) as (Q2 & Q3 & Q4 & Q5 & Q6 & Q1).
         lazymatch type of HJ with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdF _ =>
           apply (HEX cx fpos k2 ly3 S3 W3 msF mdF HB HJ Hfrm) end.
         unfold kin_exit. exists 0, (adv + 1). split; [lia|].
         apply (kgn_kat cx fpos _ _ adv k2 ly3 S3 W3 ms3 md3 KP_EXIT _ _ (adv + 1) msF _ ve vs vd HB HK0).
         { split; [rewrite Q1; reflexivity|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
           split; [exact Q5 | exact Q6]. }
         { refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
             rewrite (RX _ _ _ HS) by (vm_compute; reflexivity); assumption. }
         { apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
           rewrite (RX _ _ _ HS) by (vm_compute; reflexivity). exact R24. }
         { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_FSH (SOff 22 0) (kFSH cx fpos)
               HRs U9); [gn_inl | gn_den | exact RFSH]. }
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_FRES (SOff 19 0) (kF cx fpos)
               HRs U9); [gn_inl | gn_den | exact RF]. }
           { apply (su_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_F (SOff 21 0) (kF cx fpos)
               HRs U9); [gn_inl | gn_den | exact RF]. } }
         { repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity. }
         { repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity. }
         { exact UN. }
         { exact HP. }
         { lia. }
         { pose proof (field_of_region E _ 18%nat (ka0 cx) _ _ _ _ _ 0 8 (SOff 32 1) (p + 1) HRc U18 ltac:(gn_inl)
             ltac:(gn_den) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as F.
           rewrite Z.add_0_r in F. replace (k_wp cx + (adv + 1)) with (p + 1) by (unfold p; lia). exact F. }
         { pose proof (field_of_region E _ 18%nat (ka0 cx) _ _ _ _ _ 8 8 (SOff 33 (-1)) (k_wn cx - adv - 1) HRc U18
             ltac:(gn_inl) ltac:(gn_den) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as F.
           replace (k_wn cx - (adv + 1)) with (k_wn cx - adv - 1) by lia. exact F. }
         { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262656 8 (SLit 0) 0 HRg U243 ltac:(gn_inl)
             ltac:(reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)). }
         { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262664 4 (SExt true 32 (SOff 37 0)) ve HRg U243
             ltac:(gn_inl) ltac:(cbn [sv_denot]; rewrite U37, Z.add_0_r; apply kgn_sext32_small; lia)
             ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
         { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262668 4 gn_es vs HRg U243
             ltac:(gn_inl) ltac:(symmetry; apply Z_to_bv_bv_unsigned)
             ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
         { exact (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262672 4 gn_ed vd HRg U243
             ltac:(gn_inl) ltac:(symmetry; apply Z_to_bv_bv_unsigned)
             ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)). }
         { exact Hve. }
         { exact Ivs. }
         { exact Ivd. }
Qed.

End b.
End a.

Print Assumptions kn_gnl.
