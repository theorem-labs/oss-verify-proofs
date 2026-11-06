(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD1q.v (tfib_srealizesX),
   lib/A/AB1n.v (tfib_startup_T1, HS_ok) and lib/A/AD2o.v (TFIB_T_of_partsXF), in the form of fuzz_pcap's closing side
   (proofs/libreac/fuzz_pcap/lib/A/PcapClose.v, a working branch 86b0e893fe8), for libreac/fuzz_decode's
   ASan image: one named Section hypothesis per remaining part, module paths and names changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/DecodeClose.v, with its module paths and module names changed; 1425 of its 1489 lines of code are new or changed and 431 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_leafb.v, with its module paths and module names changed; 316 of its 463 lines of code are new or changed and 1342 lines of the source are left out. *)
(* DgnDecodeCgRun: the helper lemmas the image-A caller-journal walks of fuzz_decode.asan (lib/A/Prog/*_cg.v walks)
   share: one footprint run of lib/Lib/ExecF.v carried into SRr, the runtime cells of lib/A/AsanCells.v read from the
   allocator invariant AR, a sub-range of a read range, and the small facts about the reader aview, the world's hidden
   bytes and the loaded segments that a walk step uses at every call site.

   The proofs follow the released image-A walk of check_round_trip of libreac/fuzz_decode:
     proofs/libreac/fuzz_decode/lib/A/Prog/crtA_bridge.v:27-43  decode_ms_of_regs_regs, decode_mkst_eqv_ms_of_regs;
     proofs/libreac/fuzz_decode/lib/A/Prog/crtA_walk.v:43-85    decode_fp_avoids, decode_run, decode_ms_shape,
                                                                decode_ms_reg;
     proofs/libreac/fuzz_decode/lib/A/Prog/crtA_cells.v:25-240  the byte lemmas, the cell-to-bytes lemmas,
                                                                decode_covers_visible, decode_seg_of, the tactics
                                                                decode_seg / decode_top and decode_cells_asan;
     proofs/libreac/fuzz_decode/lib/A/Prog/crtA_encw.v:69-364   decode_segs_low .. decode_frame_ext (the donor's
                                                                function-specific lemmas are not taken; decode_frame_ext
                                                                takes the frame base and size as arguments).
   decode_rd_ok_sub (a sub-range of DgnDecodeCg.decode_rd_ok) is new here.

   Segments: lib/A/AB1v.v tfibsegs, lib/A/Img0.v rsegs and lib/A/DecodeTFIB.v decodesegs0 are all the image module's
   Asan.M.loaded_segments, so they are convertible.  The walk statements are over tfibsegs; the local abbreviation `segs`
   below names it, once.  ExecF runs, ms_of_regs (lib/A/Prog/LeafCgKit.v), mrd / bytes_at (lib/Lib/Mem.v) and
   AsanCells are over rsegs, as those files state them.

   The donor's BRIDGE hypothesis is proved: decode_run applies lib/A/Prog/LeafCgFacts.v bridge_evtF_stmt_YA0n after
   the state transport of lib/Lib/CrtBridge.v evtF_eqv. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0n YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF CrtBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.

Local Abbreviation segs := tfibsegs.

(* ---- the bytes: le_byte (YG0f.v) against le8 / le4 / [Z_to_bv 8 _] (Mem.v) ---- *)

Lemma decode_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma decode_mod_pow2_mod : forall v n m, 0 <= n <= m -> (v mod 2 ^ m) mod 2 ^ n = v mod 2 ^ n.
Proof.
  intros v n m Hnm. apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec0 i n) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* Byte k of z is byte k of z mod 2^n when the byte lies below bit n. *)
Lemma decode_byte_mod : forall z n k, 0 <= k -> k + 8 <= n ->
  Z.shiftr (z mod 2 ^ n) k mod 256 = Z.shiftr z k mod 256.
Proof.
  intros z n k Hk Hn. change 256 with (2 ^ 8). apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec0 i 8) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma decode_le_byte : forall (w k : nat) z v, (k < w)%nat ->
  z mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w) ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (Z_to_le_bytes w z) k) = Some (le_byte v w k).
Proof.
  intros w k z v Hk Hm. rewrite decode_nth_le_bytes by exact Hk. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  unfold le_byte. rewrite <- Hm. symmetry. apply decode_byte_mod; lia.
Qed.

Lemma decode_wa_mod : forall v (w : nat), (w <= 8)%nat ->
  bv_unsigned (wa v) mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w).
Proof.
  intros v w Hw. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply decode_mod_pow2_mod. change (Z.of_N 64) with 64. lia.
Qed.

(* Width 8: the bytes of le8 (wa v), as asan_cells writes the word cells. *)
Lemma decode_le8_byte : forall v k, (k < 8)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (le8 (wa v)) k) = Some (le_byte v 8 k).
Proof.
  intros v k Hk. unfold le8, word_to_le_bytes.
  apply decode_le_byte; [exact Hk | apply decode_wa_mod; lia].
Qed.

(* Width 4: the bytes of le4 (wa v) (the UAR cell). *)
Lemma decode_le4_byte : forall v k, (k < 4)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (le4 (wa v)) k) = Some (le_byte v 4 k).
Proof.
  intros v k Hk. unfold le4.
  apply decode_le_byte; [exact Hk | apply decode_wa_mod; lia].
Qed.

(* Width 1: the byte [Z_to_bv 8 v] (the INITED / REPLACE / CANPOISON cells). *)
Lemma decode_le1_byte : forall v k, (k < 1)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error [Z_to_bv 8 v] k) = Some (le_byte v 1 k).
Proof.
  intros v k Hk. change [Z_to_bv 8 v] with (Z_to_le_bytes 1 v).
  apply decode_le_byte; [exact Hk | reflexivity].
Qed.

Lemma decode_opt_byte_eq : forall (x y : option byte) z,
  option_map (fun b : byte => bv_unsigned b) x = Some z ->
  option_map (fun b : byte => bv_unsigned b) y = Some z -> x = y.
Proof.
  intros [x|] [y|] z Hx Hy; cbn in Hx, Hy; try discriminate.
  injection Hx as Hx. injection Hy as Hy. f_equal. apply bv_eq. congruence.
Qed.

(* ---- the addresses: a byte inside a loaded segment is not hidden ---- *)

Lemma decode_find_none : forall (l : list Segment) addr n s,
  find_segment l addr n = None -> In s l ->
  Z.of_N (seg_base s) <= addr -> addr + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s) -> False.
Proof.
  induction l as [|s0 l IH]; intros addr n s Hf Hin H1 H2; [destruct Hin|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s0)) addr && Z.leb (addr + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%Z
    eqn:E; [discriminate|].
  destruct Hin as [<- | Hin].
  - apply andb_false_iff in E as [E | E]; apply Z.leb_gt in E; lia.
  - exact (IH addr n s Hf Hin H1 H2).
Qed.

Lemma decode_covers_lo : forall a n, decode_seg_covers a n = true -> 0 <= a.
Proof.
  intros a n Hc. unfold decode_seg_covers in Hc. apply existsb_exists in Hc as (s & _ & Hb). cbv beta in Hb.
  apply andb_true_iff in Hb as [H1 _]. apply Z.leb_le in H1.
  pose proof (N2Z.is_nonneg (seg_base s)). lia.
Qed.

Lemma decode_covers_visible : forall (hd : word -> bool) a n i,
  H_off_segments segs hd -> decode_seg_covers a n = true -> 0 <= i < n -> a + n <= 2 ^ 64 ->
  hd (Z_to_bv 64 (a + i)) = false.
Proof.
  intros hd a n i Hoff Hc Hi Ht.
  unfold decode_seg_covers in Hc. apply existsb_exists in Hc as (s & Hs & Hb). cbv beta in Hb.
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (N2Z.is_nonneg (seg_base s)) as H0.
  destruct (hd (Z_to_bv 64 (a + i))) eqn:E; [exfalso | reflexivity].
  pose proof (Hoff _ E) as E2.
  assert (U : bv_unsigned (Z_to_bv 64 (a + i)) = a + i) by (apply (wa_unsigned (a + i)); lia).
  rewrite U in E2.
  exact (decode_find_none segs (a + i) 1 s E2 Hs ltac:(lia) ltac:(lia)).
Qed.

Lemma decode_seg_of : forall a n, In (a, n) decode_asan_cell_ranges -> decode_seg_covers a n = true.
Proof. intros a n Hin. exact (proj1 (forallb_forall _ _) decode_asan_cells_in_seg (a, n) Hin). Qed.

(* decode_seg closes `decode_seg_covers a n = true` for a row (a, n) of decode_asan_cell_ranges; decode_top closes a
   closed `a + n <= 2 ^ 64`. *)
Ltac decode_seg := clear; apply decode_seg_of; unfold decode_asan_cell_ranges; cbn [In];
  repeat (first [left; reflexivity | right]).
Ltac decode_top := clear; apply Z.leb_le; reflexivity.

Section DecodeCells.
Context {rc : YM05.RunCeil}.
Variable B : asyms.

(* One constant cell at a numeral address, in a loaded segment: its bytes are bytes_at under mrd. *)
Lemma decode_cell_bytes : forall ly (hd : word -> bool) mem a v (w : nat) (bs : list byte),
  H_off_segments segs hd ->
  cell_holds B ly (aview segs hd mem) (ACell (ANum a) w (AV (ANum v))) ->
  decode_seg_covers a (Z.of_nat w) = true -> a + Z.of_nat w <= 2 ^ 64 ->
  length bs = w ->
  (forall k, (k < w)%nat -> option_map (fun b : byte => bv_unsigned b) (nth_error bs k) = Some (le_byte v w k)) ->
  bytes_at rsegs mem a bs.
Proof.
  intros ly hd mem a v w bs Hoff Hc Hcov Htop Hlen Henc.
  unfold cell_holds in Hc. cbn [aeval c_at c_w c_val] in Hc.
  unfold bytes_at.
  split; [exact (decode_covers_lo a (Z.of_nat w) Hcov)|].
  split; [rewrite Hlen; exact Htop|].
  intros i Hi. rewrite Hlen in Hi.
  assert (Hv : hd (Z_to_bv 64 (a + Z.of_nat i)) = false)
    by (apply (decode_covers_visible hd a (Z.of_nat w) (Z.of_nat i) Hoff Hcov); lia).
  assert (Erd : mrd rsegs mem (wa (a + Z.of_nat i)) = YP09.mbyte segs (mrestrict hd mem) (a + Z.of_nat i)).
  { unfold mrd, wa, YP09.mbyte, mrestrict. rewrite Hv. reflexivity. }
  rewrite Erd. apply (decode_opt_byte_eq _ _ (le_byte v w i)); [exact (Hc i Hi) | exact (Henc i Hi)].
Qed.

Lemma decode_z8 : forall ly (hd : word -> bool) mem a v,
  H_off_segments segs hd ->
  Forall (cell_holds B ly (aview segs hd mem)) (as_const B ly) ->
  In (z8 (ANum a) v) (as_const B ly) -> decode_seg_covers a 8 = true -> a + 8 <= 2 ^ 64 ->
  bytes_at rsegs mem a (le8 (wa v)).
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (decode_cell_bytes ly hd mem a v 8 (le8 (wa v)) Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           (length_le8 _) (decode_le8_byte v)).
Qed.

Lemma decode_z4 : forall ly (hd : word -> bool) mem a v,
  H_off_segments segs hd ->
  Forall (cell_holds B ly (aview segs hd mem)) (as_const B ly) ->
  In (z4 (ANum a) v) (as_const B ly) -> decode_seg_covers a 4 = true -> a + 4 <= 2 ^ 64 ->
  bytes_at rsegs mem a (le4 (wa v)).
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (decode_cell_bytes ly hd mem a v 4 (le4 (wa v)) Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           (length_le4 _) (decode_le4_byte v)).
Qed.

Lemma decode_z1 : forall ly (hd : word -> bool) mem a v,
  H_off_segments segs hd ->
  Forall (cell_holds B ly (aview segs hd mem)) (as_const B ly) ->
  In (z1 (ANum a) v) (as_const B ly) -> decode_seg_covers a 1 = true -> a + 1 <= 2 ^ 64 ->
  bytes_at rsegs mem a [Z_to_bv 8 v].
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (decode_cell_bytes ly hd mem a v 1 [Z_to_bv 8 v] Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           eq_refl (decode_le1_byte v)).
Qed.

(* The runtime cells of AsanCells.asan_cells at every AR state: decode_cells puts them in the constant cells of B,
   which ARm's am_const (YG0n.v) reads under aview; every cell lies in a loaded segment (decode_asan_cells_in_seg),
   where the world hides no byte, so aview reads the byte mrd reads. *)
Lemma decode_cells_asan :
  transport_cells B ->
  forall (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model),
    H_off_segments segs (w_H W) ->
    @AR rc segs B ly S W mem md ->
    ACells.asan_cells mem.
Proof.
  intros HC ly S W mem md Hoff HAR.
  destruct HAR as [HM _].
  assert (HK : Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly))
    by (eapply am_const; exact HM).
  (* Rows 1-17 of decode_cells are the cells of asan_cells; rows 18-19 (DESK's shadow) are not needed here. *)
  destruct (HC ly) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & _).
  unfold ACells.asan_cells.
  split; [exact (decode_z8 ly _ mem ACells.CELL_K ACells.ASAN_K Hoff HK C1 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem ACells.GOT_CELL_K ACells.CELL_K Hoff HK C2 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z1 ly _ mem ACells.INITED 1 Hoff HK C3 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z1 ly _ mem ACells.REPLACE 1 Hoff HK C4 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem ACells.GOT_REPLACE ACells.REPLACE Hoff HK C5 ltac:(decode_seg)
                   ltac:(decode_top))|].
  split; [exact (decode_z4 ly _ mem ACells.UAR 1 Hoff HK C6 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem ACells.GOT_UAR ACells.UAR Hoff HK C7 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z1 ly _ mem ACells.CANPOISON 1 Hoff HK C8 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem ACells.HIEND 0x7fffffffffff Hoff HK C9 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem ACells.GOT_HIEND ACells.HIEND Hoff HK C10 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem ACells.MIDBEG 0 Hoff HK C11 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem ACells.GOT_MIDBEG ACells.MIDBEG Hoff HK C12 ltac:(decode_seg)
                   ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem ACells.MIDEND 0 Hoff HK C13 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem ACells.GOT_MIDEND ACells.MIDEND Hoff HK C14 ltac:(decode_seg)
                   ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem ACells.REAL_MEMCPY ACells.MUSL_MEMCPY Hoff HK C15 ltac:(decode_seg)
                   ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem ACells.REAL_MEMSET ACells.MUSL_MEMSET Hoff HK C16 ltac:(decode_seg)
                   ltac:(decode_top))|].
  exact (decode_z8 ly _ mem ACells.GOT_REAL_MEMSET ACells.REAL_MEMSET Hoff HK C17 ltac:(decode_seg)
           ltac:(decode_top)).
Qed.
End DecodeCells.

(* ---- the run state: LeafCgKit's ms_of_regs against cgif's mkst ---- *)

Section DecodeShape.
Context {fx : YKK.FPState}.

(* LeafCgKit's run state carries `mkR` of the register values, which is mkR_of of the map. *)
Lemma decode_ms_of_regs_regs : forall pc (regs : bvmap 5 word) (mem : word -> option byte),
  ms_regs (@LCK.ms_of_regs fx pc regs mem) = mkR_of regs.
Proof.
  intros pc regs mem. unfold LCK.ms_of_regs, mkR_of, YKK.getr. cbn.
  first [reflexivity | f_equal].
Qed.

(* cgif's configuration state at a pc of image A, and the state decode's footprint runs start from. *)
Lemma decode_mkst_eqv_ms_of_regs : forall pc (regs : bvmap 5 word) (mem : word -> option byte),
  ms_eqv (@YKK.mkst fx regs (LCK.w64 pc) mem (YKK.seg_rom rsegs)) (@LCK.ms_of_regs fx pc regs mem).
Proof.
  intros pc regs mem.
  pose proof (@mkst_eqv_mkR_of fx regs (LCK.w64 pc) mem (YKK.seg_rom rsegs)) as H.
  unfold ms_eqv in H |- *. rewrite (decode_ms_of_regs_regs pc regs mem).
  unfold LCK.ms_of_regs. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in H |- *.
  exact H.
Qed.
End DecodeShape.

(* ---- one footprint run carried into SRr ---- *)

Section DecodeWalk.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.

(* The footprint the walk gives every run: all visible bytes; it avoids the world's hidden bytes by construction. *)
Lemma decode_fp_avoids : forall (W : world segs),
  LCK.fp_avoids (@w_H segs W) (LCK.RNG_W (world segs) (@w_H segs) W).
Proof.
  intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* A footprint run from cgif's configuration at pc: the run is the one of decode's state ms_of_regs; the walk
   continues from every state the transported run can reach. *)
Lemma decode_run : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (pc : Z)
    (P : machine_state -> Prop) (Q : world segs -> config -> Prop),
  ExecF.evtF rsegs (LCK.RNG_W (world segs) (@w_H segs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr segs W (mkCfg ms' md') Q) ->
  SRr segs W (@cfg_at fx segs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K.
  unfold cfg_at.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W (@YKK.mkst fx regs (w64 pc) mem (YKK.seg_rom segs)) md
           (LCK.RNG_W (world segs) (@w_H segs) W) (fun ms => exists ms0, P ms0 /\ ms_eqv ms0 ms) Q).
  - apply (evtF_eqv rsegs _ P (@LCK.ms_of_regs fx pc regs mem)).
    + apply ms_eqv_sym. exact (decode_mkst_eqv_ms_of_regs pc regs mem).
    + exact Hrun.
  - apply decode_fp_avoids.
  - exact K.
Qed.

(* A state ms_eqv to decode's MS form with cgif's float state is cgif's mkst state of its own register map. *)
Lemma decode_ms_shape : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte) (ms' : machine_state),
  ms_eqv (MS R (@YKK.fp_regs fx) pc (@YKK.fp_csr fx) None m (YKK.seg_rom segs)) ms' ->
  ms' = @YKK.mkst fx (ms_regs ms') pc m (YKK.seg_rom segs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

(* ... and its registers are R's (x1 .. x31). *)
Lemma decode_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> is_x0 r = false ->
  YKK.getr (ms_regs ms') r = YKK.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _) Hr. cbn [MS ms_regs] in HR.
  rewrite !getr_nonzero by exact Hr. symmetry. apply HR. exact Hr.
Qed.
End DecodeWalk.

(* ---- the reader aview, the hidden bytes and the loaded segments ---- *)

Section DecodeView.
Context {rc : YM05.RunCeil}.

(* Every loaded segment lies below kLowMemEnd (YImgTop.segs_in_asan, IMG_LO_val, IMG_TOP_val). *)
Lemma decode_segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr).
  pose proof YImgTop.segs_in_asan as Hall. unfold YImgTop.segs_in in Hall. rewrite forallb_forall in Hall.
  pose proof (Hall sg Hin) as Hb. apply andb_true_iff in Hb as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. unfold YImgTop.seg_lo, YImgTop.seg_hi in Hlo, Hhi.
  pose proof YImgTop.IMG_LO_val as E1. pose proof YImgTop.IMG_TOP_val as E2. unfold kLowMemEnd. lia.
Qed.

Lemma decode_aview_vis : forall (W : world segs) mem a v,
  aview segs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (@w_Hoff segs W _ E) as F.
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H.
  unfold YKK.seg_rom, memory_read in H. cbn [Z.of_N] in H. rewrite F in H. discriminate H.
Qed.

Lemma decode_aview_mrd : forall (W : world segs) mem a, w_H W (Z_to_bv 64 a) = false ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (mrd rsegs mem (wa a)).
Proof. intros W mem a H. unfold aview, YP09.mbyte, mrestrict, mrd, wa. rewrite H. reflexivity. Qed.

Lemma decode_aview_some : forall (W : world segs) mem a v, aview segs (w_H W) mem a = Some v ->
  w_H W (Z_to_bv 64 a) = false /\ exists b : byte, mrd rsegs mem (wa a) = Some b /\ bv_unsigned b = v.
Proof.
  intros W mem a v H. pose proof (decode_aview_vis W mem a v H) as Hv. split; [exact Hv|].
  rewrite (decode_aview_mrd W mem a Hv) in H.
  destruct (mrd rsegs mem (wa a)) as [b|] eqn:E; [|discriminate H]. exists b. split; [reflexivity|].
  injection H as H. exact H.
Qed.

Lemma decode_present_eq : forall (W : world segs) m m' a,
  apresent (w_H W) m a -> apresent (w_H W) m' a -> aview segs (w_H W) m' a = aview segs (w_H W) m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros W m m' a (Hh & b & Hb) (_ & b' & Hb') E.
  rewrite (decode_aview_mrd W m' a Hh), (decode_aview_mrd W m a Hh) in E. unfold mrd, wa in E.
  rewrite Hb, Hb' in E. cbn in E. injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma decode_rw_cells_ext : forall m m' A cs,
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wa (A + i)) = m (wa (A + i))) ->
  rw_cells rsegs m A cs -> rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs E [[Hwf (H0 & Hl & Hb)] (W0 & W1 & Hw)].
  pose proof (cells_bytes_length cs Hwf) as Lc.
  split; [split; [exact Hwf|]|].
  - split; [exact H0|]. split; [exact Hl|]. intros i Hi. rewrite <- (Hb i Hi). unfold mrd.
    rewrite (E (Z.of_nat i)) by lia. reflexivity.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. specialize (Hw i Hi). unfold wview in *.
    rewrite (E i Hi). exact Hw.
Qed.

Lemma decode_req_size : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

(* RNG_W W holds on a range of bytes the world does not hide. *)
Lemma decode_rng : forall (W : world segs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall b, lo <= b < lo + len -> w_H W (Z_to_bv 64 b) = false) ->
  rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof.
  intros W lo len H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hbj. unfold LCK.RNG_W, LCK.range_avoids, LCK.woff. intros k Hk.
  rewrite (unsigned_lit b) by lia. apply H. lia.
Qed.

(* A byte of a loaded segment is never hidden (YK04.v H_off_segments). *)
Lemma decode_vis_seg : forall (W : world segs) a,
  (exists sg, In sg segs /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) ->
  w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W a (sg & Hin & Hr). destruct (w_H W (Z_to_bv 64 a)) eqn:E; [exfalso|reflexivity].
  pose proof (@w_Hoff segs W _ E) as F.
  assert (Ha : 0 <= a < kLowMemEnd) by (apply decode_segs_low; exists sg; split; [exact Hin | exact Hr]).
  rewrite (unsigned_lit a) in F by (unfold kLowMemEnd in Ha; lia).
  exact (decode_find_none segs a 1 sg F Hin ltac:(lia) ltac:(lia)).
Qed.

(* The shadow hull a block gives (shadow_hull_vis) is not hidden. *)
Lemma decode_vis_hull : forall (W : world segs) mem x n s,
  shadow_hull_vis (aview segs (w_H W) mem) x n ->
  YG0f.shadow_addr x / 8 * 8 <= s < YG0f.shadow_addr (x + n - 1) / 8 * 8 + 8 ->
  w_H W (Z_to_bv 64 s) = false.
Proof.
  intros W mem x n s H Hs. specialize (H s Hs).
  destruct (aview segs (w_H W) mem s) as [v|] eqn:E; [|exfalso; exact (H eq_refl)].
  exact (decode_aview_vis W mem s v E).
Qed.

Lemma decode_byte_signed : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  rewrite Z.mod_small by lia. lia.
Qed.

(* AsanCells' addressable (lib/A/AsanCells.v) from cgif's range_addressable (YG0v.v) over a range of application
   memory. *)
Lemma decode_addressable : forall (W : world segs) mem p n,
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n -> 0 <= n ->
  4096 <= p /\ (p + n <= kLowShadowBeg \/ kHighMemBeg <= p /\ p + n <= ASAN_CEIL) ->
  ACells.addressable mem p n.
Proof.
  intros W mem p n HA Hn Happ. pose proof ASAN_CEIL_range as [CR _].
  split; [lia|]. split; [exact Hn|]. split; [unfold ACells.APPMEM_END, kLowShadowBeg, kHighMemBeg in *; lia|].
  intros i Hi. split.
  - unfold ACells.app_mem, ACells.LOWMEM_END, ACells.HIGHMEM_BEG, ACells.APPMEM_END, kLowShadowBeg, kHighMemBeg in *.
    lia.
  - destruct (HA (p + i) ltac:(lia)) as (s & Hs & Hok).
    destruct (decode_aview_some W mem _ s Hs) as (_ & b & Hb & Eb).
    exists b. split.
    + replace (ACells.shadow_addr (p + i)) with (shadow_of_addr SHADOW_OFF (p + i))
        by (unfold ACells.shadow_addr, shadow_of_addr, ACells.ASAN_K, SHADOW_OFF; lia).
      exact Hb.
    + pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
      unfold saddr_ok in Hok. unfold ACells.shadow_ok.
      rewrite decode_byte_signed by lia. lia.
Qed.

(* cgif's view of the caller's memory is decode's mrd of the restricted overlay. *)
Lemma decode_rd_mrd : forall (H : word -> bool) (m : word -> option byte) (a : Z),
  aview segs H m a = option_map (fun b : byte => bv_unsigned b) (mrd rsegs (mrestrict H m) (wa a)).
Proof. reflexivity. Qed.

Lemma decode_le4 : forall v, le4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof.
  intros v. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z_to_le_bytes_mod. lia.
Qed.

(* A frame of cells at [base, base + sz) is kept by every memory that agrees with the old one on its bytes. *)
Lemma decode_frame_ext : forall (base sz : Z) (cs : list cell) (m m' : word -> option byte),
  Z.of_nat (cells_size cs) <= sz ->
  (forall i, 0 <= i < sz -> m' (wa (base + i)) = m (wa (base + i))) ->
  rw_cells rsegs m base cs -> rw_cells rsegs m' base cs.
Proof.
  intros base sz cs m m' Hsz E H. eapply decode_rw_cells_ext; [|exact H].
  intros i Hi. apply E. lia.
Qed.

Lemma decode_in_rom_img : forall a, in_rom segs a -> in_img segs a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.

(* A range decode_seg_covers accepts lies in a loaded segment. *)
Lemma decode_covers_img : forall a n x, decode_seg_covers a n = true -> a <= x < a + n ->
  exists sg, In sg segs /\ Z.of_N (seg_base sg) <= x < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
  intros a n x H Hx. unfold decode_seg_covers in H. apply existsb_exists in H as (sg & Hin & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hin | lia].
Qed.

Lemma decode_shadow_addr_eq : forall a, ACells.shadow_addr a = YG0f.shadow_addr a.
Proof. intros a. unfold ACells.shadow_addr, YG0f.shadow_addr, ACells.ASAN_K, SHADOW_OFF. lia. Qed.

(* RNG_W W holds on the 8-aligned shadow cover of a block range whose shadow the block law makes visible. *)
Lemma decode_rng_hull : forall (W : world segs) mem x n, 0 <= x -> 0 < n -> x + n <= 2 ^ 48 ->
  shadow_hull_vis (aview segs (w_H W) mem) x n ->
  rng (LCK.RNG_W (world segs) (@w_H segs) W) (ACells.shadow_addr x / 8 * 8)
    (ACells.shadow_addr (x + n - 1) / 8 * 8 + 8 - ACells.shadow_addr x / 8 * 8).
Proof.
  intros W mem x n H0 Hn H1 H. rewrite !decode_shadow_addr_eq.
  assert (B1 : 0 <= YG0f.shadow_addr x / 8 * 8) by (unfold YG0f.shadow_addr, SHADOW_OFF; lia).
  assert (B2 : YG0f.shadow_addr x / 8 * 8 <= YG0f.shadow_addr (x + n - 1) / 8 * 8)
    by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; [lia|];
        unfold YG0f.shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (B3 : YG0f.shadow_addr (x + n - 1) / 8 * 8 + 8 <= 2 ^ 64) by (unfold YG0f.shadow_addr, SHADOW_OFF; lia).
  apply decode_rng; [exact B1 | lia |]. intros s Hs. apply (decode_vis_hull W mem x n s H). lia.
Qed.

Lemma decode_present_vis : forall (W : world segs) m a, apresent (w_H W) m a -> aview segs (w_H W) m a <> None.
Proof.
  intros W m a (Hh & b & Hb). rewrite (decode_aview_mrd W m a Hh). unfold mrd, wa. rewrite Hb. discriminate.
Qed.

(* A range one read-only segment holds is read-only image data (in_rom), decided on the segment list. *)
Lemma decode_rom_range : forall b n a,
  existsb (fun sg : Segment => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? b) &&
                               (b + n <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool segs = true ->
  b <= a < b + n -> in_rom segs a.
Proof.
  intros b n a H Ha. apply existsb_exists in H as (sg & Hin & Hb).
  apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [Hw H1].
  apply negb_true_iff in Hw. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hin|]. split; [exact Hw | lia].
Qed.

(* The rom_view-type agreement on a read-only byte (DgnDecodeCg.decode_rom_view_rd's form) is decode's: mrd of the
   overlay is the image byte. *)
Lemma decode_ro_mrd : forall (W : world segs) mem a,
  in_rom segs a ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (YKK.seg_rom segs (Z_to_bv 64 a)) ->
  mrd rsegs mem (wa a) = PropExec.seg_rom rsegs (wa a).
Proof.
  intros W mem a Hrom E.
  assert (Hh : w_H W (Z_to_bv 64 a) = false)
    by (apply decode_vis_seg; destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
  rewrite (decode_aview_mrd W mem a Hh) in E.
  change (YKK.seg_rom segs (Z_to_bv 64 a)) with (PropExec.seg_rom rsegs (wa a)) in E.
  destruct (mrd rsegs mem (wa a)) as [b1|]; destruct (PropExec.seg_rom rsegs (wa a)) as [b2|];
    cbn [option_map] in E; try discriminate E.
  - injection E as E. f_equal. apply bv_eq. exact E.
  - reflexivity.
Qed.

(* A sub-range of a read range is a read range (DgnDecodeCg.decode_rd_ok): each conjunct restricts. *)
Lemma decode_rd_ok_sub : forall (W : world segs) (memc : word -> option byte) (q n q' n' : Z),
  decode_rd_ok W memc q n -> q <= q' -> q' + n' <= q + n -> 0 <= n' -> decode_rd_ok W memc q' n'.
Proof.
  intros W memc q n q' n' (Hv & Ha & Hh & Hm & H0 & H63) H1 H2 H3.
  split; [intros a Ha'; apply Hv; lia|].
  split; [exact (range_addressable_sub _ _ q n q' n' Ha H1 H2)|].
  split.
  - intros s Hs. apply Hh.
    assert (A1 : YG0f.shadow_addr q / 8 * 8 <= YG0f.shadow_addr q' / 8 * 8)
      by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; [lia|];
          unfold YG0f.shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
    assert (A2 : YG0f.shadow_addr (q' + n' - 1) / 8 * 8 <= YG0f.shadow_addr (q + n - 1) / 8 * 8)
      by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; [lia|];
          unfold YG0f.shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
    lia.
  - split; [unfold amem_range in *; lia|]. split; lia.
Qed.
End DecodeView.

Print Assumptions decode_run.
Print Assumptions decode_cells_asan.
Print Assumptions decode_rd_ok_sub.
