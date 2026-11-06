(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD1d.v, with its module paths and module names changed; 315 of its 356 lines of code are new or changed and 270 lines of the source are left out. *)
(* The satisfiability witness of LLVMFuzzerTestOneInput's image-A entry Pre: lib/A/Prog/LinkEntry.v tfib_lib_pre_x at
   lib/A/Prog/LinkEntryA.v's instance (tfibsegs, PCAP_RLO / PCAP_RHI, A_LLVMF, RA_LLVMF, A_EMPTY, LLVMF_STK, G_HARNESS,
   link_amf, LA_NUL), at link's own start state. Image: fuzz_link.asan, the PUBLISHED pin (sha256 059dae63e07c...); listings
   link-a/listings/slot/target_run.fuzz_link.asan.s (internal record, sha256 fd94c6a37bf3) and link-a/listings/slot/main.fuzz_link.asan.s
   (internal record, sha256 ff5ac23f2c4c) (made by link-a/tools/adis.py (internal record, sha256 ba8c20cb31c5)).
   Proves no function (kind: start-up facts).

   THE FIRST CALL. The start-up certificate (lib/A/AB1n.v tfib_startup_T1) hands main (0x81d2c) one of the 50 states
   of lib/A/AB01.v HS_tfib_list (AB1n.v HS_ok h ... c, c = cfg_of TSEGS R (pc ch) FULL model), with the world
   AD2i.v W1 (w_H = AD2i.H1) and the memory FULL, which the contract reads as m1 = mrestrict H1 FULL (AD2i.v:508-513);
   the allocator is at init_state (AD1g.v tfib_ARm at ly0: no block, no frame, empty depot, st_nev 0). Then:
   - main opens argv[1] (0x81d68) and mallocs its 65536-byte buffer (0x81d7c, trace [0x5436c; 0x81d80]); it reads
     the file into read_stage [0x5cca90, 0x5dca90) (read at 0x81e10) and copies each piece into the buffer (0x81da8);
     a full buffer doubles (malloc 0x81dd0, copy, free 0x81df4), up to 2^26 bytes. It closes the file (0x81e24),
     splits the input of length L into the config (c = in[0] | (in[1] & 0x7f) << 8 bytes at in + 2) and the payload
     (n = L - c - 6 bytes at in + c + 6), and calls target_run(in + 2, c, in + c + 6, n) (0x81e9c).
   - target_run's first call sets initialized (0x5dca90, 0x82080), registers oft_exit_guard with atexit (0x8208c),
     and then: n = 0: s1 = 0x5dca90 + 0x10 = A_EMPTY (0x820a8), no allocation; n > 0: malloc(n) (0x8205c, trace
     [0x5436c; 0x82060]), memcpy(block, payload, n) (0x82070), s1 = block (0x82074). It sets running (0x5dca94,
     0x820b8) and calls LLVMFuzzerTestOneInput at 0x820c4.
   - For an input file shorter than 65536 bytes the allocator at the call is lw_S1 n (n > 0: two live blocks
     (buffer, 65536) and (copy, n), st_nev 2, depot LW_DEPOT1) or lw_S0 (n = 0: the buffer, st_nev 1, depot
     LW_DEPOT0); for every input, the driver's tail_at (staged AD1w.v:47-56: blocks [(pb, cap)], st_nev <= 64,
     65536 <= cap <= 2^26, length < cap) plus target_run's one malloc give st_nev <= 65, blocks_bytes <= 2^27 and a
     depot of driver traces only (lw_budget_drv, lw_wild_drv).
   - The memory at the call is m1 changed only by the driver: its stack frames (main and target_run, 0x50 bytes
     each), read_stage, the buffer and copy blocks, the driver windows AD1y.v DRV_IVS (target_run.initialized /
     running, atexit's records), the allocator's statics and the shadow. The bytes the image conjuncts read miss all
     of them (lw_rd_not_drvw, lw_rd_not_stage, lw_rd_not_owned, lw_rd_range: image bytes, below every block and the
     stack), so they keep their start-up values, which are the image's own bytes (lw_handoff). lw_handoff reads
     them from the KImg entries of each hand-off state's knowledge (bytes the start-up did not write), not from the
     start-up's regions, from which AD2j.v:4 cuts the harness bodies (g_sink, g_say, long_alias).

   THE WHOLE PRE AT THAT CALL: tfib_lib_pre_x SK regs ly S W mem md p n pl T, at SK = link_asink_head, B = PcapB,
   MT = ameter_triv, XM_LIB = fun _ => 0 (the driver's instance, staged AD2o.v:53), T = []. Registers after the jal
   at 0x820c4: pc = A_LLVMF = 0x827d4, ra = 0x820c8, a0 = p (0x820bc mv a0, s1), a1 = n (0x820c0 mv a1, s0),
   sp = main's entry sp - 0x50 - 0x50 (0x81d2c, 0x81ffc), gp = as_gp B and tp = as_tp B as the start-up left them.
   The journal of the post starts at this state (ly, S, W, mem, md) with the footprint amf_harness_fp [] =
   [sink_token] (AMemFile.v amf_harness_fp_nil). Conjunct by conjunct:
   1. afn_pre segs B LLVMF_STK ly S W regs mem md []: AR, ret_ok ra, 4096 <= ra, gp / tp, astk_ok LLVMF_STK at sp,
      the LLVMF_STK bytes below sp present, the empty chain, qtight S. These need AR at the call state: the driver's
      lib_pre (staged AD1w.v:78-85), given to the contract by the staged AD1m.v tfib_lib_site_x, which is
      re-pointed.
   2. raZ regs = RA_LLVMF: lib_pre (AD1w.v:79).
   3. getr regs 10 = w64 p, getr regs 11 = w64 n: lib_site_x premises (AD1w.v:89).
   4. (n = 0 /\ p = A_EMPTY) \/ (0 < n < 2^26 /\ In (p, n) (ablocks B ly S)): lib_site_x premise (AD1w.v:90);
      lw_args_empty, lw_args_block.
   5. n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p pl: lib_site_x premise (AD1w.v:91); lw_args_empty,
      lw_args_block.
   6. frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX: lib_site_x premise
      (AD1w.v:92); lw_frames0 / lw_frames1, lw_ev0 / lw_ev1, lw_live0 / lw_live1; lw_budget_drv.
   7. arodata_okP segs PCAP_RLO PCAP_RHI B (aview segs (w_H W) mem): the driver's arodata_ok B (AD1w.v:93), through
      the re-pointing.
   8. amf_gi segs link_amf [] (rd W mem), its first arm (g_sink = g_say = ofl_head = 0, lw_heads0 /
      lw_gi_nil_heads): lw_amf_gi; lw_handoff / lw_startup; lw_rd_not_*.
   9. incl [] (ablocks B ly S): lw_kept_nil.
   10. 0 < n -> ~ In (p, n) []: lw_kept_nil.
   11. amf_env segs link_amf (rd W mem): lw_amf_env; lw_handoff / lw_startup; lw_rd_not_*.
   12. amf_head_law link_asink_head link_amf: lw_head_law (AMemFile.v link_amf_head_law).
   13. val_mem segs (rd W mem) LA_NUL 1 0: lw_la_nul (long_alias[300] is 0 in the image: lw_la_nul_rom);
       lw_handoff / lw_startup; lw_rd_not_*.
   14. Namei.fd_names_path (m_fds md) sink_path = false, Fs.fs_sorted (m_fs md) = true: lib_site_x premises
       (AD1w.v:96-97).
   15. mo_ok MT S (XM_LIB n): lw_meter (MT = ameter_triv).
   16. link_wild_room (as_universe B) S: lw_wild0 / lw_wild1 (LinkWildRoom.v link_wild_room_state from the start-up's
       empty depot, lw_wild_start, and link_wild_room_fits; the depot's wild part is [] at the call, lw_wild_part0 /
       lw_wild_part1); lw_wild_drv.
   lw_pre_link_empty and lw_pre_link_block state 4-6 and 8-16 together at the named states and memories. The
   contract's other premises are not Pre conjuncts: AI (the driver) and the zero rounding mode, which holds at the
   start-up's float state fx0 (lw_frm0, YK0o.v fp_frm_zero_fx0). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB12 AB1h AB13 AB01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YI04 YI00 YGwildCount YC5d YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AD2i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AD1y AB1n AMemFileT06 ACejTfib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import ACejUniv AD2l AMemFile LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr LinkEntry LinkEntryA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.

(* ==========================================================================
   1. The bytes the image conjuncts read
   ========================================================================== *)

(* amf_gi / amf_env at link_amf read g_sink, g_say and ofl_head (8 bytes each), __libc.threaded and
   __libc.need_locks (1 byte each) and ofl_lock (4 bytes) (AMemFileSink.v amf_head_addr / amf_env_addr); the val_mem
   conjunct reads long_alias[300]. *)
Definition LW_RANGES : list (Z * Z) :=
  [(LA_G_SINK, 8); (LA_G_SAY, 8); (LA_OFL_HEAD, 8); (0x651ea1, 1); (0x651ea3, 1); (0x652300, 4); (LA_NUL, 1)].
Definition lw_rd (a : Z) : Prop := exists r, In r LW_RANGES /\ fst r <= a < fst r + snd r.

Local Ltac lw_in := unfold LW_RANGES; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma lw_rd_amf : forall a, amf_head_addr link_amf a \/ amf_env_addr link_amf a -> lw_rd a.
Proof.
  intros a Ha. cbv [amf_head_addr amf_env_addr amf_ofl_head amf_sink_addr amf_say_addr amf_threaded
    amf_need_locks amf_ofl_lock link_amf] in Ha.
  destruct Ha as [[H | [H | H]] | [H | [H | H]]];
    [ exists (LA_G_SINK, 8) | exists (LA_G_SAY, 8) | exists (LA_OFL_HEAD, 8)
    | exists (0x651ea1, 1) | exists (0x651ea3, 1) | exists (0x652300, 4) ];
    (split; [lw_in | unfold LA_G_SINK, LA_G_SAY, LA_OFL_HEAD; cbn [fst snd]; lia]).
Qed.

Lemma lw_rd_nul : lw_rd LA_NUL.
Proof. exists (LA_NUL, 1). split; [lw_in | cbn [fst snd]; lia]. Qed.

Lemma lw_ranges_img : forallb (fun r => (0x10000 <=? fst r) && (fst r + snd r <=? 0x654000)) LW_RANGES = true.
Proof. vm_compute. reflexivity. Qed.

(* every byte read is an image byte below the image's end 0x654000 (AB12.v TFIB img_hi), so below every block,
   frame and stack byte of the run *)
Lemma lw_rd_range : forall a, lw_rd a -> 0x10000 <= a < 0x654000.
Proof.
  intros a (r & Hr & Ha). pose proof (proj1 (forallb_forall _ _) lw_ranges_img r Hr) as X.
  apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

(* long_alias[300] (.bss) is 0 in the image *)
Lemma lw_la_nul_rom : seg_rom tfibsegs (Z_to_bv 64 LA_NUL) = Some (Z_to_bv 8 0).
Proof. vm_compute. reflexivity. Qed.

(* The three image conjuncts hold at every memory that holds the image's own bytes where they read
   (AMemFileT06.v link_amf_start for the first two). *)
Lemma lw_rom_conj : forall m, (forall a, lw_rd a -> mbyte tfibsegs m a = seg_rom tfibsegs (Z_to_bv 64 a)) ->
  amf_gi tfibsegs link_amf [] m /\ amf_env tfibsegs link_amf m /\ val_mem tfibsegs m LA_NUL 1 0.
Proof.
  intros m Hm.
  assert (Hh : forall a, amf_head_addr link_amf a \/ amf_env_addr link_amf a ->
    mbyte tfibsegs m a = seg_rom tfibsegs (Z_to_bv 64 a)) by (intros a Ha; apply Hm; exact (lw_rd_amf a Ha)).
  destruct (AMemFileT06.link_amf_start m Hh) as [HG HE].
  split; [exact HG|]. split; [exact HE|].
  intros k Hk. destruct k as [|k]; [|lia]. change (LA_NUL + Z.of_nat 0) with LA_NUL.
  rewrite (Hm LA_NUL lw_rd_nul). vm_compute. reflexivity.
Qed.

(* What the driver writes before the call misses those bytes: its windows (AD1y.v DRV_IVS: target_run.initialized
   and running, atexit's records), read_stage [0x5cca90, 0x5dca90) (main 0x81d8c-0x81d90, read at 0x81e10), and the
   allocator's statics (AF0m.v Tfib_owned_static). *)
Lemma lw_drv_apart :
  forallb (fun r => forallb (fun iv => (fst r + snd r <=? fst iv) || (snd iv <=? fst r)) AD1y.DRV_IVS) LW_RANGES
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lw_rd_not_drvw : forall a, lw_rd a -> AD1y.DRVW a = false.
Proof.
  intros a (r & Hr & Ha). unfold AD1y.DRVW. apply not_true_iff_false. intros X.
  apply existsb_exists in X as (iv & Hiv & Hb). apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (proj1 (forallb_forall _ _) lw_drv_apart r Hr) as Y.
  pose proof (proj1 (forallb_forall _ _) Y iv Hiv) as Z.
  apply orb_prop in Z as [Z|Z]; apply Z.leb_le in Z; lia.
Qed.

Definition LW_STAGE_LO : Z := 0x5cca90.
Definition LW_STAGE_HI : Z := 0x5dca90.

Lemma lw_stage_apart :
  forallb (fun r => (fst r + snd r <=? LW_STAGE_LO) || (LW_STAGE_HI <=? fst r)) LW_RANGES = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lw_rd_not_stage : forall a, lw_rd a -> ~ (LW_STAGE_LO <= a < LW_STAGE_HI).
Proof.
  intros a (r & Hr & Ha) Hs. pose proof (proj1 (forallb_forall _ _) lw_stage_apart r Hr) as X.
  apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
Qed.

Lemma lw_avoids_owned :
  forallb (fun r => forallb (g_avoids (fst r) (snd r)) Tfib_owned_static) LW_RANGES = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lw_rd_not_owned : forall a, lw_rd a -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros a (r & Hr & Ha) Ho. apply Exists_exists in Ho as (o & Ho & Hz). unfold in_zr in Hz.
  pose proof (proj1 (forallb_forall _ _) lw_avoids_owned r Hr) as X.
  pose proof (proj1 (forallb_forall _ _) X o Ho) as Y. unfold g_avoids in Y.
  apply orb_prop in Y as [Y|Y]; apply Z.leb_le in Y; lia.
Qed.

(* ==========================================================================
   2. The named memories: the image's own bytes, and the payload at the input block
   ========================================================================== *)

(* the image's own bytes everywhere (n = 0: nothing else is read) *)
Definition lw_img : word -> option byte := fun _ => None.

(* the image's own bytes, and the payload pl at p *)
Definition lw_inp (p : Z) (pl : list byte) : word -> option byte := fun w =>
  if (p <=? bv_unsigned w) && (bv_unsigned w <? p + Z.of_nat (length pl))
  then nth_error pl (Z.to_nat (bv_unsigned w - p)) else None.

Lemma lw_img_rom : forall (H : word -> bool) a, mbyte tfibsegs (mrestrict H lw_img) a = seg_rom tfibsegs (Z_to_bv 64 a).
Proof. intros H a. unfold mbyte, mrestrict, lw_img. destruct (H (Z_to_bv 64 a)); reflexivity. Qed.

Lemma lw_inp_rom : forall (H : word -> bool) p pl a, lw_rd a -> 0x654000 <= p ->
  mbyte tfibsegs (mrestrict H (lw_inp p pl)) a = seg_rom tfibsegs (Z_to_bv 64 a).
Proof.
  intros H p pl a Ha Hp. pose proof (lw_rd_range a Ha) as R.
  unfold mbyte, mrestrict. destruct (H (Z_to_bv 64 a)); [reflexivity|].
  unfold lw_inp. rewrite amf_unsigned64 by lia.
  replace (p <=? a) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

Lemma lw_inp_at : forall (H : word -> bool) p (pl : list byte) j, 0 <= p -> p + Z.of_nat (length pl) <= 2 ^ 64 ->
  (j < length pl)%nat -> H (Z_to_bv 64 (p + Z.of_nat j)) = false ->
  mrestrict H (lw_inp p pl) (Z_to_bv 64 (p + Z.of_nat j)) = nth_error pl j.
Proof.
  intros H p pl j H0 H1 Hj Hh. unfold mrestrict. rewrite Hh. unfold lw_inp. rewrite amf_unsigned64 by lia.
  replace ((p <=? p + Z.of_nat j) && (p + Z.of_nat j <? p + Z.of_nat (length pl))) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  replace (p + Z.of_nat j - p) with (Z.of_nat j) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

(* the payload's bytes at the input block, which the world shows (AR: a live block's bytes are present) *)
Lemma lw_garr8 : forall (H : word -> bool) p (pl : list byte), 0 <= p -> p + Z.of_nat (length pl) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length pl) -> H (Z_to_bv 64 (p + i)) = false) ->
  garr8 tfibsegs (mrestrict H (lw_inp p pl)) p (map (fun b : byte => bv_unsigned b) pl).
Proof.
  intros H p pl H0 H1 Hvis j Hj. rewrite length_map in Hj.
  assert (Hn : nth j (map (fun b : byte => bv_unsigned b) pl) 0 = bv_unsigned (nth j pl (Z_to_bv 8 0))).
  { rewrite <- (map_nth (fun b : byte => bv_unsigned b)). reflexivity. }
  rewrite Hn. pose proof (u8_range (nth j pl (Z_to_bv 8 0))) as R.
  split; [| lia].
  intros k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold mbyte. rewrite (lw_inp_at H p pl j H0 H1 Hj (Hvis (Z.of_nat j) ltac:(lia))).
  rewrite (nth_error_nth' pl (Z_to_bv 8 0) Hj). cbv beta iota. f_equal.
  unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite !(Z.mod_small _ 256 R).
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* Conjuncts 8, 11, 13 at the named memories, for every world (H = w_H W). *)
Lemma lw_amf_gi : forall (H : word -> bool) p pl, 0x654000 <= p ->
  amf_gi tfibsegs link_amf [] (mrestrict H lw_img) /\ amf_gi tfibsegs link_amf [] (mrestrict H (lw_inp p pl)).
Proof.
  intros H p pl Hp. split.
  - exact (proj1 (lw_rom_conj _ (fun a _ => lw_img_rom H a))).
  - exact (proj1 (lw_rom_conj _ (fun a Ha => lw_inp_rom H p pl a Ha Hp))).
Qed.

Lemma lw_amf_env : forall (H : word -> bool) p pl, 0x654000 <= p ->
  amf_env tfibsegs link_amf (mrestrict H lw_img) /\ amf_env tfibsegs link_amf (mrestrict H (lw_inp p pl)).
Proof.
  intros H p pl Hp. split.
  - exact (proj1 (proj2 (lw_rom_conj _ (fun a _ => lw_img_rom H a)))).
  - exact (proj1 (proj2 (lw_rom_conj _ (fun a Ha => lw_inp_rom H p pl a Ha Hp)))).
Qed.

Lemma lw_la_nul : forall (H : word -> bool) p pl, 0x654000 <= p ->
  val_mem tfibsegs (mrestrict H lw_img) LA_NUL 1 0 /\ val_mem tfibsegs (mrestrict H (lw_inp p pl)) LA_NUL 1 0.
Proof.
  intros H p pl Hp. split.
  - exact (proj2 (proj2 (lw_rom_conj _ (fun a _ => lw_img_rom H a)))).
  - exact (proj2 (proj2 (lw_rom_conj _ (fun a Ha => lw_inp_rom H p pl a Ha Hp)))).
Qed.

(* With T = [] amf_gi is its first arm: g_sink = g_say = ofl_head = 0. *)
Lemma lw_gi_nil_heads : forall m, amf_gi tfibsegs link_amf [] m -> amf_heads tfibsegs link_amf m 0.
Proof. intros m [[Hh _] | (f & _ & Ht & _)]; [exact Hh | discriminate Ht]. Qed.

Lemma lw_heads0 : forall (H : word -> bool) p pl, 0x654000 <= p ->
  amf_heads tfibsegs link_amf (mrestrict H lw_img) 0 /\ amf_heads tfibsegs link_amf (mrestrict H (lw_inp p pl)) 0.
Proof.
  intros H p pl Hp. destruct (lw_amf_gi H p pl Hp) as [G1 G2].
  exact (conj (lw_gi_nil_heads _ G1) (lw_gi_nil_heads _ G2)).
Qed.

(* The rounding mode at the first call: the start-up's float state fx0 has frm 0 (the premise of
   tfib_lib_contract_xf; YK0o.v fp_frm_zero_fx0). *)
Lemma lw_frm0 : YK0o.frm_zero (@fp_csr YK11.fx0).
Proof. exact YK0o.fp_frm_zero_fx0. Qed.

(* ==========================================================================
   3. The allocator at the first call (input file shorter than 65536 bytes)
   ========================================================================== *)

(* main's buffer (malloc(0x10000) at 0x81d7c) and target_run's copy (malloc(n) at 0x8205c). The two chunks' slot
   positions (PPrim 0, PPrim 0x20000) are named for the witness; no conjunct reads them except through
   ablocks, whose address of a chunk is sptr_addr B ly of it at the call's layout. *)
Definition LW_CAP : Z := 65536.
Definition lw_buf : YG00.chunk := YG00.mkChunk (PPrim 0) LW_CAP CAllocated.
Definition lw_copy (n : Z) : YG00.chunk := YG00.mkChunk (PPrim (2 * LW_CAP)) n CAllocated.
Definition lw_pq (n : Z) : sptr := ck_user (lw_copy n).
(* the depot's traces: malloc's trace start 0x5436c, then the return address of the call of the malloc wrapper
   (AF0m.v DRV_TRACES; ACejTfib.v:20-23) *)
Definition LW_DEPOT0 : list (list Z) := [[0x5436c; 0x81d80]].
Definition LW_DEPOT1 : list (list Z) := [[0x5436c; 0x81d80]; [0x5436c; 0x82060]].
(* from the start-up's allocator state init_state (AD1g.v tfib_ARm): n = 0 and n > 0 *)
Definition lw_S0 : astate := set_nev 1 (set_depot LW_DEPOT0 (set_chunks [lw_buf] init_state)).
Definition lw_S1 (n : Z) : astate := set_nev 2 (set_depot LW_DEPOT1 (set_chunks [lw_buf; lw_copy n] init_state)).

Lemma lw_frames0 : frames lw_S0 = [].
Proof. reflexivity. Qed.
Lemma lw_frames1 : forall n, frames (lw_S1 n) = [].
Proof. intros n. reflexivity. Qed.

Lemma lw_ev0 : st_nev lw_S0 + EV_LIB <= EV_MAX.
Proof. change (st_nev lw_S0) with 1. unfold EV_LIB, EV_MAX. lia. Qed.
Lemma lw_ev1 : forall n, st_nev (lw_S1 n) + EV_LIB <= EV_MAX.
Proof. intros n. change (st_nev (lw_S1 n)) with 2. unfold EV_LIB, EV_MAX. lia. Qed.

Lemma lw_live0 : blocks_bytes lw_S0 + LIVE_LIB <= LIVE_MAX.
Proof. change (blocks_bytes lw_S0) with (LW_CAP + 0). unfold LW_CAP, LIVE_LIB, LIVE_MAX. lia. Qed.
Lemma lw_live1 : forall n, 0 <= n <= 2 ^ 26 -> blocks_bytes (lw_S1 n) + LIVE_LIB <= LIVE_MAX.
Proof.
  intros n Hn. change (blocks_bytes (lw_S1 n)) with (LW_CAP + (n + 0)). unfold LW_CAP, LIVE_LIB, LIVE_MAX. lia.
Qed.

(* every first call, from the driver's bounds: tail_at's st_nev <= 64 plus target_run's malloc, and the buffer
   (cap <= 2^26) and the copy (n < cap) *)
Lemma lw_budget_drv : forall S, st_nev S <= 65 -> blocks_bytes S <= 2 ^ 27 ->
  st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX.
Proof. intros S H1 H2. unfold EV_LIB, EV_MAX, LIVE_LIB, LIVE_MAX. lia. Qed.

Lemma lw_block_in : forall ly n, In (sptr_addr PcapB ly (lw_pq n), n) (ablocks PcapB ly (lw_S1 n)).
Proof.
  intros ly n. unfold ablocks. apply in_map_iff. exists (lw_pq n, n). split; [reflexivity|].
  unfold blocks. apply in_map_iff. exists (lw_copy n). split; [reflexivity|].
  apply filter_In. split; [right; left; reflexivity | reflexivity].
Qed.

(* link's universe (AD2l.v PcapB_universe: ACejUniv.v Tfib_univ): 32 fixed traces, room for 4064 wild ones *)
Lemma lw_univ_fix_len : length (u_fix (as_universe PcapB)) = 32%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma lw_univ_wmax : u_wmax (as_universe PcapB) = (Z.to_nat DEPOT_MAX - length (u_fix (as_universe PcapB)))%nat.
Proof. reflexivity. Qed.
Lemma lw_fits : (LINK_CALLS_MAX * LINK_WILD_PER_CALL <= u_wmax (as_universe PcapB))%nat.
Proof. exact (link_wild_room_fits (as_universe PcapB) lw_univ_fix_len lw_univ_wmax). Qed.

(* the driver's puts, from the start-up's empty depot *)
Lemma lw_depot_run0 : depot_run LW_DEPOT0 (st_depot init_state) LW_DEPOT0.
Proof.
  unfold LW_DEPOT0. cbn [st_depot init_state].
  apply (depot_run_cons _ _ _ [[0x5436c; 0x81d80]]); [right; split; reflexivity | apply depot_run_nil].
Qed.
Lemma lw_depot_run1 : depot_run LW_DEPOT1 (st_depot init_state) LW_DEPOT1.
Proof.
  unfold LW_DEPOT1. cbn [st_depot init_state].
  apply (depot_run_cons _ _ _ [[0x5436c; 0x81d80]]); [right; split; reflexivity|].
  apply (depot_run_cons _ _ _ [[0x5436c; 0x81d80]; [0x5436c; 0x82060]]);
    [right; split; [reflexivity | vm_compute; reflexivity] | apply depot_run_nil].
Qed.

Lemma lw_wild_puts0 : (length (wild_part (as_universe PcapB) LW_DEPOT0) <= 0 * LINK_WILD_PER_CALL)%nat.
Proof. vm_compute. lia. Qed.
Lemma lw_wild_puts1 : (length (wild_part (as_universe PcapB) LW_DEPOT1) <= 0 * LINK_WILD_PER_CALL)%nat.
Proof. vm_compute. lia. Qed.

Lemma lw_wild0 : link_wild_room (as_universe PcapB) lw_S0.
Proof.
  apply (link_wild_room_state (as_universe PcapB) init_state lw_S0 LW_DEPOT0 0);
    [reflexivity | exact lw_depot_run0 | exact lw_wild_puts0 | unfold LINK_CALLS_MAX; lia | exact lw_fits].
Qed.
Lemma lw_wild1 : forall n, link_wild_room (as_universe PcapB) (lw_S1 n).
Proof.
  intros n.
  apply (link_wild_room_state (as_universe PcapB) init_state (lw_S1 n) LW_DEPOT1 0);
    [reflexivity | exact lw_depot_run1 | exact lw_wild_puts1 | unfold LINK_CALLS_MAX; lia | exact lw_fits].
Qed.

(* the start-up's depot is empty, so its wild part is [] *)
Lemma lw_wild_start : wild_part (as_universe PcapB) (st_depot init_state) = [] /\
  link_wild_room (as_universe PcapB) init_state.
Proof.
  split; [reflexivity|].
  apply (link_wild_room_count (as_universe PcapB) init_state 0); [| unfold LINK_CALLS_MAX; lia | exact lw_fits].
  change (length (wild_part (as_universe PcapB) (st_depot init_state))) with 0%nat. apply Nat.le_0_l.
Qed.

(* at the first call the depot holds the driver's traces only, each a fixed row: its wild part is still [] *)
Lemma lw_wild_part0 : wild_part (as_universe PcapB) (st_depot lw_S0) = [].
Proof. vm_compute. reflexivity. Qed.
Lemma lw_wild_part1 : forall n, wild_part (as_universe PcapB) (st_depot (lw_S1 n)) = [].
Proof. intros n. vm_compute. reflexivity. Qed.

(* every first call: before it only the driver's traces are put (AF0m.v DRV_TRACES), all of them fixed rows *)
Lemma lw_wild_drv : forall S, incl (st_depot S) DRV_TRACES -> link_wild_room (as_universe PcapB) S.
Proof.
  intros S Hd.
  apply (link_wild_room_count (as_universe PcapB) S 0); [| unfold LINK_CALLS_MAX; lia | exact lw_fits].
  assert (E : wild_part (as_universe PcapB) (st_depot S) = []).
  { destruct (wild_part (as_universe PcapB) (st_depot S)) as [|t l] eqn:Ew; [reflexivity|]. exfalso.
    assert (Ht : In t (wild_part (as_universe PcapB) (st_depot S))) by (rewrite Ew; left; reflexivity).
    apply In_wild_part in Ht as [H1 H2].
    pose proof (ACejTfib.Tfib_universe_drv t (Hd t H1)) as H3.
    apply (proj2 (mem_trace_In t _)) in H3.
    change (u_fix (as_universe PcapB)) with ACej.Tfib_universe in H2. congruence. }
  rewrite E. apply Nat.le_0_l.
Qed.

(* conjunct 15 at the driver's meter, conjunct 12, conjuncts 9 and 10 at T = [] *)
Lemma lw_meter : forall S x, mo_ok ameter_triv S x.
Proof. intros S x. exact I. Qed.

Lemma lw_head_law : amf_head_law link_asink_head link_amf.
Proof. exact link_amf_head_law. Qed.

Lemma lw_kept_nil : forall (bl : list (Z * Z)) p n, incl [] bl /\ (0 < n -> ~ In (p, n) ([] : list (Z * Z))).
Proof. intros bl p n. split; [apply incl_nil_l | intros _ []]. Qed.

(* conjuncts 4 and 5: the two inputs the driver passes *)
Lemma lw_args_empty : forall (B : asyms) ly S (m : word -> option byte),
  ((0 = 0 /\ A_EMPTY = A_EMPTY) \/ (0 < 0 < 2 ^ 26 /\ In (A_EMPTY, 0) (ablocks B ly S))) /\
  0 = Z.of_nat (length ([] : list byte)) /\ garr8 tfibsegs m A_EMPTY (map (fun b : byte => bv_unsigned b) []).
Proof.
  intros B ly S m. split; [left; split; reflexivity|]. split; [reflexivity|]. apply garr8_nil.
Qed.

Lemma lw_args_block : forall ly (H : word -> bool) (pl : list byte) n p,
  n = Z.of_nat (length pl) -> 0 < n < 2 ^ 26 -> p = sptr_addr PcapB ly (lw_pq n) -> 0 <= p -> p + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> H (Z_to_bv 64 (p + i)) = false) ->
  ((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks PcapB ly (lw_S1 n)))) /\
  n = Z.of_nat (length pl) /\ garr8 tfibsegs (mrestrict H (lw_inp p pl)) p (map (fun b : byte => bv_unsigned b) pl).
Proof.
  intros ly H pl n p Hn Hr Hp H0 H1 Hvis.
  split; [right; split; [exact Hr | rewrite Hp; exact (lw_block_in ly n)]|].
  split; [exact Hn|]. subst n. exact (lw_garr8 H p pl H0 H1 Hvis).
Qed.

(* ==========================================================================
   4. The link-specific conjuncts together, at the named states and memories
   ========================================================================== *)

Theorem lw_pre_link_empty : forall ly (H : word -> bool) (XM : Z -> Z),
  let S := lw_S0 in let m := mrestrict H lw_img in let n := 0 in let p := A_EMPTY in
  ((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks PcapB ly S))) /\
  n = Z.of_nat (length ([] : list byte)) /\ garr8 tfibsegs m p (map (fun b : byte => bv_unsigned b) []) /\
  frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
  amf_gi tfibsegs link_amf [] m /\ incl [] (ablocks PcapB ly S) /\ (0 < n -> ~ In (p, n) ([] : list (Z * Z))) /\
  amf_env tfibsegs link_amf m /\ amf_head_law link_asink_head link_amf /\
  val_mem tfibsegs m LA_NUL 1 0 /\ mo_ok ameter_triv S (XM n) /\ link_wild_room (as_universe PcapB) S.
Proof.
  intros ly H XM. cbv zeta.
  destruct (lw_args_empty PcapB ly lw_S0 (mrestrict H lw_img)) as (A1 & A2 & A3).
  destruct (lw_rom_conj _ (fun a _ => lw_img_rom H a)) as (G & Env & Nul).
  destruct (lw_kept_nil (ablocks PcapB ly lw_S0) A_EMPTY 0) as [K1 K2].
  refine (conj A1 (conj A2 (conj A3 (conj _ (conj _ (conj _ (conj G (conj K1 (conj K2 (conj Env
    (conj _ (conj Nul (conj _ _)))))))))))));
    [exact lw_frames0 | exact lw_ev0 | exact lw_live0 | exact lw_head_law | exact (lw_meter _ _) | exact lw_wild0].
Qed.

Theorem lw_pre_link_block : forall ly (H : word -> bool) (XM : Z -> Z) (pl : list byte) n p,
  n = Z.of_nat (length pl) -> 0 < n <= 65529 -> p = sptr_addr PcapB ly (lw_pq n) ->
  0x654000 <= p -> p + n <= 2 ^ 64 -> (forall i, 0 <= i < n -> H (Z_to_bv 64 (p + i)) = false) ->
  let S := lw_S1 n in let m := mrestrict H (lw_inp p pl) in
  ((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks PcapB ly S))) /\
  n = Z.of_nat (length pl) /\ garr8 tfibsegs m p (map (fun b : byte => bv_unsigned b) pl) /\
  frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
  amf_gi tfibsegs link_amf [] m /\ incl [] (ablocks PcapB ly S) /\ (0 < n -> ~ In (p, n) ([] : list (Z * Z))) /\
  amf_env tfibsegs link_amf m /\ amf_head_law link_asink_head link_amf /\
  val_mem tfibsegs m LA_NUL 1 0 /\ mo_ok ameter_triv S (XM n) /\ link_wild_room (as_universe PcapB) S.
Proof.
  intros ly H XM pl n p Hn Hr Hp Hp0 Hp1 Hvis. cbv zeta.
  destruct (lw_args_block ly H pl n p Hn ltac:(lia) Hp ltac:(lia) Hp1 Hvis) as (A1 & A2 & A3).
  destruct (lw_rom_conj _ (fun a Ha => lw_inp_rom H p pl a Ha Hp0)) as (G & Env & Nul).
  destruct (lw_kept_nil (ablocks PcapB ly (lw_S1 n)) p n) as [K1 K2].
  refine (conj A1 (conj A2 (conj A3 (conj _ (conj _ (conj _ (conj G (conj K1 (conj K2 (conj Env
    (conj _ (conj Nul (conj _ _)))))))))))));
    [exact (lw_frames1 n) | exact (lw_ev1 n) | exact (lw_live1 n ltac:(lia)) | exact lw_head_law
    | exact (lw_meter _ _) | exact (lw_wild1 n)].
Qed.

(* ==========================================================================
   5. The memory the start-up hands main: the image's own bytes where the conjuncts read
   ========================================================================== *)

(* In each of the 50 hand-off states of the start-up certificate, every range read is inside one KImg entry of the
   state's knowledge: bytes the start-up did not write (AD2i.v cjust_sound's KImg arm reads them the same way). *)
Definition lw_check (ch : acs) : bool := forallb (fun r => kn_img ch (fst r) (snd r)) LW_RANGES.
Lemma lw_check_all : forallb lw_check HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.

Section handoff. Context {fx : YK11.FPState}.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Variable h : nat.
Variable FS0 : Fs.Fs.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH FS0 E ch R FULL model.
#[local] Notation m1 := (mrestrict (AD2i.H1 sp rdraw inp ch E model) FULL).

Lemma lw_handoff_rom : forall a, lw_rd a -> mbyte tfibsegs m1 a = seg_rom tfibsegs (Z_to_bv 64 a).
Proof.
  intros a Ha. pose proof (lw_rd_range a Ha) as Rg. destruct Ha as (r & Hr & Ha).
  pose proof (proj1 (forallb_forall _ _) lw_check_all ch (HS_tfib_In h ch Hch)) as C. unfold lw_check in C.
  pose proof (proj1 (forallb_forall _ _) C r Hr) as K.
  unfold kn_img in K. apply existsb_exists in K as (Kn & HK & HKb).
  destruct Kn as [| | |lo hi| | | | | |]; try discriminate HKb.
  apply andb_prop in HKb as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  pose proof (proj1 (Forall_forall _ _) (ho_know TSEGS TFIB LIM TOP SINV argH FS0 E ch R FULL model HC) _ HK)
    as (_ & _ & Hnone).
  pose proof (Hnone a ltac:(lia)) as X.
  pose proof (tfib_rom_all a ltac:(unfold pcap_img_end, YImgTop.IMG_TOP; lia)) as Hrom.
  destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [b|] eqn:Hs; [|exfalso; exact (Hrom eq_refl)].
  change tfibsegs with TSEGS. apply (AD2i.mbyte_MR_m1 sp rdraw inp Hsp Hva ch E FULL model).
  unfold mbyte. rewrite X. exact Hs.
Qed.

(* Conjuncts 8, 11 and 13 at the hand-off memory. *)
Theorem lw_handoff : amf_gi tfibsegs link_amf [] m1 /\ amf_env tfibsegs link_amf m1 /\ val_mem tfibsegs m1 LA_NUL 1 0.
Proof. exact (lw_rom_conj m1 lw_handoff_rom). Qed.
End handoff.

(* The same, from the start-up theorem's hand-off (AB1n.v HS_ok, the states tfib_startup_T1 hands main). *)
Corollary lw_startup : forall h sp rdraw brk inp fs c, valid_sp sp -> valid_argv (in_argv inp) ->
  AB1n.HS_ok h sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) fs c ->
  exists ch E R FULL model, HS_tfib h = Some ch /\ c = cfg_of TSEGS R (pc ch) FULL model /\
  amf_gi tfibsegs link_amf [] (mrestrict (AD2i.H1 sp rdraw inp ch E model) FULL) /\
  amf_env tfibsegs link_amf (mrestrict (AD2i.H1 sp rdraw inp ch E model) FULL) /\
  val_mem tfibsegs (mrestrict (AD2i.H1 sp rdraw inp ch E model) FULL) LA_NUL 1 0.
Proof.
  intros h sp rdraw brk inp fs c Hsp Hva (ch & E & R & FULL & model & Hch & Hc & HC).
  exists ch, E, R, FULL, model. split; [exact Hch|]. split; [exact Hc|].
  eapply lw_handoff; eassumption.
Qed.
