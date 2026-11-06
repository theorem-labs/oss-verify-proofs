(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_leafb.v (origin/ossv/recipes 88154566652a) for reac-repacer/fuzz_uci's image A: module paths and names changed, the cell rows are this unit's AsanCells rows, and the read-only-image helper is dropped. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths and module names changed; 271 of its 440 lines of code are new or changed and 352 lines of the source are left out. *)
(* DecodeFevt: the kit a caller-journal walk of fuzz_decode.asan (lib/A/Prog/*_cg.v) uses to run footprint
   contracts (lib/Lib/ExecF.v evtF) from a cg premise list:
   - decode_cells_asan: AsanCells.asan_cells of the memory from DgnDecodeCg.decode_cells and AR;
   - decode_run: a footprint run from cfg_at, carried into SRr (the run's final state register-equivalent to an
     mkst state, the memory grown, the model same_but_materialized);
   - the memory facts a walk reads its premises with: garr8 of visible bytes as bytes_at / rw_cells, aview
     range_addressable and a heap block as AsanCells.addressable, raw bytes equal from equal views of present
     bytes, cells and bytes carried to a memory equal on their range, ExecF.rng of visible ranges, stk of present
     bytes. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0n YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0f YG0v YG0n YG0d YI04 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame Cells Step ExecF PropExec Regs6ss MState.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit LeafCgGlue LeafCgFacts DgnTransportImg.
Import ListNotations.
Open Scope Z_scope.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LFrame := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Frame.
Module LCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module LStep := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Step.
Module AImg0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Img0.
Module FC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The image's segment list under its three names: the statements' tfibsegs (lib/A/AB1v.v), the footprint runs'
   rsegs (lib/A/Img0.v) and the listing's decodesegs0 (lib/A/DecodeTFIB.v) are the one list. *)
Lemma decode_segs_eq : tfibsegs = AImg0.rsegs.
Proof. reflexivity. Qed.

(* Every byte of the image lies below the low shadow (lib/A/Prog/DgnDecodeImg.v dgndec_segs_low). *)
Lemma decode_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. exact DgnTransportImg.transport_segs_low. Qed.

Lemma decode_seg_rom_high : forall a : word, kLowMemEnd <= bv_unsigned a -> PropExec.seg_rom AImg0.rsegs a = None.
Proof.
  intros a Ha. apply LeafCgGlue.seg_rom_out_img. intros Him.
  pose proof (decode_segs_low (bv_unsigned a) Him). lia.
Qed.

(* ---- the runtime cells (crtA_cells.v) ---- *)

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
  bv_unsigned (LMem.wa v) mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w).
Proof.
  intros v w Hw. unfold LMem.wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply decode_mod_pow2_mod. change (Z.of_N 64) with 64. lia.
Qed.

Lemma decode_le8_byte : forall v k, (k < 8)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (LMem.le8 (LMem.wa v)) k) = Some (le_byte v 8 k).
Proof.
  intros v k Hk. unfold LMem.le8, word_to_le_bytes.
  apply decode_le_byte; [exact Hk | apply decode_wa_mod; lia].
Qed.

Lemma decode_le4_byte : forall v k, (k < 4)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (LMem.le4 (LMem.wa v)) k) = Some (le_byte v 4 k).
Proof.
  intros v k Hk. unfold LMem.le4.
  apply decode_le_byte; [exact Hk | apply decode_wa_mod; lia].
Qed.

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
  H_off_segments tfibsegs hd -> decode_seg_covers a n = true -> 0 <= i < n -> a + n <= 2 ^ 64 ->
  hd (Z_to_bv 64 (a + i)) = false.
Proof.
  intros hd a n i Hoff Hc Hi Ht.
  unfold decode_seg_covers in Hc. apply existsb_exists in Hc as (s & Hs & Hb). cbv beta in Hb.
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (N2Z.is_nonneg (seg_base s)) as H0.
  destruct (hd (Z_to_bv 64 (a + i))) eqn:E; [exfalso | reflexivity].
  pose proof (Hoff _ E) as E2.
  assert (U : bv_unsigned (Z_to_bv 64 (a + i)) = a + i) by (apply (LMem.wa_unsigned (a + i)); lia).
  rewrite U in E2.
  exact (decode_find_none tfibsegs (a + i) 1 s E2 Hs ltac:(lia) ltac:(lia)).
Qed.

Lemma decode_seg_of : forall a n, In (a, n) decode_asan_cell_ranges -> decode_seg_covers a n = true.
Proof. intros a n Hin. exact (proj1 (forallb_forall _ _) decode_asan_cells_in_seg (a, n) Hin). Qed.

Ltac decode_seg := clear; apply decode_seg_of; unfold decode_asan_cell_ranges; cbn [In];
  repeat (first [left; reflexivity | right]).
Ltac decode_top := clear; apply Z.leb_le; reflexivity.

Section Cells.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma decode_cell_bytes : forall ly (hd : word -> bool) mem a v (w : nat) (bs : list byte),
  H_off_segments tfibsegs hd ->
  cell_holds B ly (aview tfibsegs hd mem) (ACell (ANum a) w (AV (ANum v))) ->
  decode_seg_covers a (Z.of_nat w) = true -> a + Z.of_nat w <= 2 ^ 64 ->
  length bs = w ->
  (forall k, (k < w)%nat -> option_map (fun b : byte => bv_unsigned b) (nth_error bs k) = Some (le_byte v w k)) ->
  LMem.bytes_at AImg0.rsegs mem a bs.
Proof.
  intros ly hd mem a v w bs Hoff Hc Hcov Htop Hlen Henc.
  unfold cell_holds in Hc. cbn [aeval c_at c_w c_val] in Hc.
  unfold LMem.bytes_at.
  split; [exact (decode_covers_lo a (Z.of_nat w) Hcov)|].
  split; [rewrite Hlen; exact Htop|].
  intros i Hi. rewrite Hlen in Hi.
  assert (Hv : hd (Z_to_bv 64 (a + Z.of_nat i)) = false)
    by (apply (decode_covers_visible hd a (Z.of_nat w) (Z.of_nat i) Hoff Hcov); lia).
  assert (Erd : LMem.mrd AImg0.rsegs mem (LMem.wa (a + Z.of_nat i)) =
                mbyte tfibsegs (mrestrict hd mem) (a + Z.of_nat i)).
  { unfold LMem.mrd, LMem.wa, mbyte, mrestrict. rewrite Hv. reflexivity. }
  rewrite Erd. apply (decode_opt_byte_eq _ _ (le_byte v w i)); [exact (Hc i Hi) | exact (Henc i Hi)].
Qed.

Lemma decode_z8 : forall ly (hd : word -> bool) mem a v,
  H_off_segments tfibsegs hd ->
  Forall (cell_holds B ly (aview tfibsegs hd mem)) (as_const B ly) ->
  In (z8 (ANum a) v) (as_const B ly) -> decode_seg_covers a 8 = true -> a + 8 <= 2 ^ 64 ->
  LMem.bytes_at AImg0.rsegs mem a (LMem.le8 (LMem.wa v)).
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (decode_cell_bytes ly hd mem a v 8 (LMem.le8 (LMem.wa v)) Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           (LMem.length_le8 _) (decode_le8_byte v)).
Qed.

Lemma decode_z4 : forall ly (hd : word -> bool) mem a v,
  H_off_segments tfibsegs hd ->
  Forall (cell_holds B ly (aview tfibsegs hd mem)) (as_const B ly) ->
  In (z4 (ANum a) v) (as_const B ly) -> decode_seg_covers a 4 = true -> a + 4 <= 2 ^ 64 ->
  LMem.bytes_at AImg0.rsegs mem a (LMem.le4 (LMem.wa v)).
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (decode_cell_bytes ly hd mem a v 4 (LMem.le4 (LMem.wa v)) Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           (LMem.length_le4 _) (decode_le4_byte v)).
Qed.

Lemma decode_z1 : forall ly (hd : word -> bool) mem a v,
  H_off_segments tfibsegs hd ->
  Forall (cell_holds B ly (aview tfibsegs hd mem)) (as_const B ly) ->
  In (z1 (ANum a) v) (as_const B ly) -> decode_seg_covers a 1 = true -> a + 1 <= 2 ^ 64 ->
  LMem.bytes_at AImg0.rsegs mem a [Z_to_bv 8 v].
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (decode_cell_bytes ly hd mem a v 1 [Z_to_bv 8 v] Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           eq_refl (decode_le1_byte v)).
Qed.

(* The first seventeen rows of decode_cells are AsanCells.asan_cells, in its order. *)
Lemma decode_cells_asan :
  transport_cells B ->
  forall (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte) (md : Model),
    @AR rc tfibsegs B ly S W mem md -> FC.asan_cells mem.
Proof.
  intros HC ly S W mem md HAR.
  pose proof (w_Hoff W) as Hoff.
  destruct HAR as [HM _].
  assert (HK : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly))
    by (eapply am_const; exact HM).
  destruct (HC ly) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & _).
  unfold FC.asan_cells.
  split; [exact (decode_z8 ly _ mem FC.CELL_K FC.ASAN_K Hoff HK C1 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem FC.GOT_CELL_K FC.CELL_K Hoff HK C2 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z1 ly _ mem FC.INITED 1 Hoff HK C3 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z1 ly _ mem FC.REPLACE 1 Hoff HK C4 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem FC.GOT_REPLACE FC.REPLACE Hoff HK C5 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z4 ly _ mem FC.UAR 1 Hoff HK C6 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem FC.GOT_UAR FC.UAR Hoff HK C7 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z1 ly _ mem FC.CANPOISON 1 Hoff HK C8 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem FC.HIEND 0x7fffffffffff Hoff HK C9 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem FC.GOT_HIEND FC.HIEND Hoff HK C10 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem FC.MIDBEG 0 Hoff HK C11 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem FC.GOT_MIDBEG FC.MIDBEG Hoff HK C12 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem FC.MIDEND 0 Hoff HK C13 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem FC.GOT_MIDEND FC.MIDEND Hoff HK C14 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem FC.REAL_MEMCPY FC.MUSL_MEMCPY Hoff HK C15 ltac:(decode_seg) ltac:(decode_top))|].
  split; [exact (decode_z8 ly _ mem FC.REAL_MEMSET FC.MUSL_MEMSET Hoff HK C16 ltac:(decode_seg) ltac:(decode_top))|].
  exact (decode_z8 ly _ mem FC.GOT_REAL_MEMSET FC.REAL_MEMSET Hoff HK C17 ltac:(decode_seg) ltac:(decode_top)).
Qed.

(* Every cell row lies in the image, where the world hides no byte: its bytes are footprint bytes. *)
Lemma decode_cell_visible : forall (W : world tfibsegs) a n i, In (a, n) decode_asan_cell_ranges -> 0 <= i < n ->
  w_H W (Z_to_bv 64 (a + i)) = false.
Proof.
  intros W a n i Hin Hi. apply (decode_covers_visible (w_H W) a n i (w_Hoff W) (decode_seg_of a n Hin) Hi).
  unfold decode_asan_cell_ranges in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E | Hin]; [injection E as <- <-; unfold FC.CELL_K, FC.GOT_CELL_K, FC.INITED, FC.REPLACE,
    FC.GOT_REPLACE, FC.UAR, FC.GOT_UAR, FC.CANPOISON, FC.HIEND, FC.GOT_HIEND, FC.MIDBEG, FC.GOT_MIDBEG, FC.MIDEND,
    FC.GOT_MIDEND, FC.REAL_MEMCPY, FC.REAL_MEMSET, FC.GOT_REAL_MEMSET; lia|]).
  destruct Hin.
Qed.
End Cells.

(* ---- the run (crtA_walk.v crtA_run) ---- *)

Section Run.
Context {fx : YK11.FPState}.

(* The footprint a walk gives every run: all visible bytes; it avoids the hidden bytes by its definition. *)
Lemma decode_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (w_H W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof.
  intros W a n Ha. unfold LCK.RNG_W in Ha. rewrite MState.Z_to_bv_bv_unsigned in Ha. exact Ha.
Qed.

(* A footprint run from cfg_at pc regs mem md: the walk goes on from every final state register-equivalent to a
   state the run reaches, with the run's memory grown from mem and any same_but_materialized model. *)
Lemma decode_run : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF AImg0.rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms1 ms2 md', P ms1 -> Regs6ss.ms_eqv ms1 ms2 -> YK1b.mem_grows mem (ms_mem ms1) ->
     same_but_materialized md md' -> SRr tfibsegs W (mkCfg ms2 md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q HR K.
  pose proof (LeafCgGlue.evtF_eqv AImg0.rsegs _ P _ _ HR (LeafCgGlue.ms_of_regs_eqv pc regs mem)) as HR'.
  unfold cfg_at.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W (YK11.mkst regs (w64 pc) mem (YK11.seg_rom AImg0.rsegs)) md _ _ Q HR').
  - exact (decode_fp_avoids W).
  - intros ms2 md' (ms1 & HP & HE & HG) Hs. exact (K ms1 ms2 md' HP HE HG Hs).
Qed.

(* A final state of a run in decode's MS form is an mkst state at the walk's float state. *)
Lemma decode_eqv_mkst : forall (R : bvmap 5 word) pc (m : word -> option byte) ms,
  Regs6ss.ms_eqv (MState.MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom AImg0.rsegs)) ms ->
  exists R', ms = @YK11.mkst fx R' pc m (YK11.seg_rom AImg0.rsegs) /\ Regs6ss.xregs_eqv R R'.
Proof.
  intros R pc m ms HE. destruct (LeafCgGlue.eqv_MS_mkst _ _ _ _ _ _ _ HE) as (R' & -> & HX).
  exists R'. split; [reflexivity | exact HX].
Qed.

Lemma decode_getr_xeqv : forall R R', Regs6ss.xregs_eqv R R' -> forall r, YK11.getr R' r = YK11.getr R r.
Proof. exact LeafCgGlue.getr_xeqv. Qed.
End Run.

(* ---- memory ---- *)

Section Mem.
Context {fx : YK11.FPState}.

(* Two present bytes with the same view are the same byte (crtA_w_tail.v). *)
Lemma decode_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  apresent H m a -> apresent H' m' a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

(* rw_cells / bytes_at are properties of the bytes of their range only (crtA_w_head.v). *)
Lemma decode_rw_cells_eq : forall (m m' : word -> option byte) A cs,
  LStep.rw_cells AImg0.rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (LCells.cells_size cs) -> m' (LMem.wa (A + i)) = m (LMem.wa (A + i))) ->
  LStep.rw_cells AImg0.rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf [H0 [H1 Hb]]] [W0 [W1 Hw]]] E.
  pose proof (LCells.cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|] |].
  - split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite <- (Hb i Hi). unfold LMem.mrd. rewrite (E (Z.of_nat i)); [reflexivity|]. rewrite L in Hi. lia.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    unfold wview. rewrite (E i Hi). exact (Hw i Hi).
Qed.

Lemma decode_bytes_at_eq : forall (m m' : word -> option byte) A bs,
  LMem.bytes_at AImg0.rsegs m A bs ->
  (forall i, (i < length bs)%nat -> m' (LMem.wa (A + Z.of_nat i)) = m (LMem.wa (A + Z.of_nat i))) ->
  LMem.bytes_at AImg0.rsegs m' A bs.
Proof.
  intros m m' A bs (H0 & H1 & Hb) E. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (Hb i Hi). unfold LMem.mrd. rewrite (E i Hi). reflexivity.
Qed.

Lemma decode_addressable_eq : forall (m m' : word -> option byte) p n,
  FC.addressable m p n ->
  (forall i, 0 <= i < n -> m' (LMem.wa (FC.shadow_addr (p + i))) = m (LMem.wa (FC.shadow_addr (p + i)))) ->
  FC.addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & HA) E. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (HA i Hi) as (Happ & b & Hb & Hs). split; [exact Happ|].
  exists b. split; [|exact Hs]. unfold LMem.mrd in *. rewrite (E i Hi). exact Hb.
Qed.

(* A visible byte: the image view's byte of the restricted memory is the footprint view's byte. *)
Lemma decode_mbyte_vis : forall (H : word -> bool) (m : word -> option byte) a, H (Z_to_bv 64 a) = false ->
  mbyte tfibsegs (mrestrict H m) a = LMem.mrd AImg0.rsegs m (LMem.wa a).
Proof. intros H m a Ha. unfold mbyte, mrestrict, LMem.mrd, LMem.wa. rewrite Ha. reflexivity. Qed.

Lemma decode_nth_map_bz : forall (l : list byte) j, (j < length l)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
  intros l j Hj. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  apply map_nth.
Qed.

Lemma decode_le_byte1 : forall b : byte, Z_to_bv 8 (le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. unfold le_byte. cbn [Z.of_nat].
  change (2 ^ (8 * 1)) with 256. rewrite Z.shiftr_0_r.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* garr8 of visible bytes is bytes_at, and back. *)
Lemma decode_garr8_bytes : forall (H : word -> bool) (m : word -> option byte) A (l : list byte),
  0 <= A -> A + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall j, (j < length l)%nat -> H (Z_to_bv 64 (A + Z.of_nat j)) = false) ->
  garr8 tfibsegs (mrestrict H m) A (map (fun b : byte => bv_unsigned b) l) ->
  LMem.bytes_at AImg0.rsegs m A l.
Proof.
  intros H m A l H0 H1 Hv Hg. split; [exact H0|]. split; [exact H1|].
  intros i Hi. assert (Hi' : (i < length (map (fun b : byte => bv_unsigned b) l))%nat) by (rewrite length_map; exact Hi).
  destruct (Hg i Hi') as [Hval _]. specialize (Hval 0%nat ltac:(lia)).
  rewrite Nat2Z.inj_0, Z.add_0_r in Hval. rewrite decode_mbyte_vis in Hval by exact (Hv i Hi).
  rewrite Hval, decode_nth_map_bz by exact Hi. rewrite decode_le_byte1.
  symmetry. apply nth_error_nth'. exact Hi.
Qed.

Lemma decode_bytes_garr8 : forall (H : word -> bool) (m : word -> option byte) A (l : list byte),
  (forall j, (j < length l)%nat -> H (Z_to_bv 64 (A + Z.of_nat j)) = false) ->
  LMem.bytes_at AImg0.rsegs m A l ->
  garr8 tfibsegs (mrestrict H m) A (map (fun b : byte => bv_unsigned b) l).
Proof.
  intros H m A l Hv (H0 & H1 & Hb) j Hj. rewrite length_map in Hj.
  rewrite decode_nth_map_bz by exact Hj. split.
  - intros k Hk. assert (k = 0%nat) by lia. subst k.
    rewrite Nat2Z.inj_0, Z.add_0_r, decode_mbyte_vis by exact (Hv j Hj).
    rewrite (Hb j Hj), decode_le_byte1. apply nth_error_nth'. exact Hj.
  - apply bv_unsigned_in_range.
Qed.

(* A byte the memory holds is writable in the footprint view. *)
Lemma decode_wview_some : forall (m : word -> option byte) (a : word) b, m a = Some b -> wview AImg0.rsegs m a <> None.
Proof. intros m a b Hb. unfold wview. rewrite Hb. discriminate. Qed.

(* rw_cells from garr8 of present bytes. *)
Lemma decode_rw_of_garr8 : forall (H : word -> bool) (m : word -> option byte) A cs,
  LCells.cells_wf cs -> 0 <= A -> A + Z.of_nat (LCells.cells_size cs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (LCells.cells_size cs) -> apresent H m (A + i)) ->
  garr8 tfibsegs (mrestrict H m) A (map (fun b : byte => bv_unsigned b) (LCells.cells_bytes cs)) ->
  LStep.rw_cells AImg0.rsegs m A cs.
Proof.
  intros H m A cs Hwf H0 H1 Hp Hg. pose proof (LCells.cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|] |].
  - apply (decode_garr8_bytes H m A); [exact H0 | rewrite L; exact H1 | | exact Hg].
    intros j Hj. rewrite L in Hj. exact (proj1 (Hp (Z.of_nat j) ltac:(lia))).
  - split; [exact H0|]. split; [exact H1|]. intros i Hi.
    destruct (Hp i Hi) as [_ [b Hb]]. exact (decode_wview_some m _ b Hb).
Qed.

(* A visible shadow byte: aview reads a value there only through the memory (the shadow lies above the image). *)
Lemma decode_aview_high : forall (H : word -> bool) (m : word -> option byte) a v,
  kLowMemEnd <= a < 2 ^ 64 -> aview tfibsegs H m a = Some v ->
  H (Z_to_bv 64 a) = false /\ exists b, m (Z_to_bv 64 a) = Some b /\ bv_unsigned b = v.
Proof.
  intros H m a v Ha E. unfold aview, mbyte, mrestrict in E.
  assert (Hr : YK11.seg_rom tfibsegs (Z_to_bv 64 a) = None).
  { change (YK11.seg_rom tfibsegs) with (PropExec.seg_rom AImg0.rsegs). apply decode_seg_rom_high.
    assert (U : bv_unsigned (Z_to_bv 64 a) = a) by (apply MState.unsigned_lit; split; [unfold kLowMemEnd in Ha|]; lia).
    rewrite U. exact (proj1 Ha). }
  destruct (H (Z_to_bv 64 a)) eqn:Eh.
  - rewrite Hr in E. discriminate E.
  - split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
    + cbn in E. injection E as E. exists b. split; [reflexivity | exact E].
    + rewrite Hr in E. discriminate E.
Qed.

Lemma decode_signed_small : forall b : byte, 0 <= bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. unfold bv_signed, bv_swrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma decode_shadow_eq : forall x, shadow_of_addr SHADOW_OFF x = FC.shadow_addr x.
Proof. intros x. unfold shadow_of_addr, FC.shadow_addr, SHADOW_OFF, FC.ASAN_K. lia. Qed.

Lemma decode_shadow_high : forall x, 0 <= x < 2 ^ 47 -> kLowMemEnd <= FC.shadow_addr x < 2 ^ 64.
Proof. intros x Hx. unfold FC.shadow_addr, FC.ASAN_K, kLowMemEnd. Z.div_mod_to_equations. lia. Qed.

(* range_addressable at the image view of application bytes is AsanCells.addressable, and its shadow bytes are
   visible. *)
Lemma decode_addressable_of : forall (H : word -> bool) (m : word -> option byte) q n,
  range_addressable (aview tfibsegs H m) SHADOW_OFF q n -> amem_range q n -> 0 <= q -> 0 <= n ->
  FC.addressable m q n /\ (forall i, 0 <= i < n -> H (Z_to_bv 64 (FC.shadow_addr (q + i))) = false).
Proof.
  intros H m q n HR Ham H0 Hn.
  assert (Hq : forall i, 0 <= i < n -> FC.app_mem (q + i) /\ 0 <= q + i < 2 ^ 47).
  { intros i Hi. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
    unfold FC.app_mem, FC.LOWMEM_END, FC.HIGHMEM_BEG, FC.APPMEM_END. lia. }
  assert (Hs : forall i, 0 <= i < n -> exists b, H (Z_to_bv 64 (FC.shadow_addr (q + i))) = false /\
             m (Z_to_bv 64 (FC.shadow_addr (q + i))) = Some b /\ FC.shadow_ok (q + i) (bv_signed b)).
  { intros i Hi. destruct (HR (q + i) ltac:(lia)) as (s & Es & Hok).
    rewrite decode_shadow_eq in Es.
    destruct (decode_aview_high H m _ s (decode_shadow_high (q + i) (proj2 (Hq i Hi))) Es) as (Hh & b & Hb & Ev).
    exists b. split; [exact Hh|]. split; [exact Hb|].
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
    unfold saddr_ok in Hok. unfold FC.shadow_ok.
    rewrite decode_signed_small by lia. lia. }
  split.
  - split; [exact H0|]. split; [exact Hn|].
    split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; unfold FC.APPMEM_END; lia|].
    intros i Hi. split; [exact (proj1 (Hq i Hi))|].
    destruct (Hs i Hi) as (b & Hh & Hb & Hok). exists b. split; [|exact Hok].
    unfold LMem.mrd, LMem.wa. rewrite Hb. reflexivity.
  - intros i Hi. destruct (Hs i Hi) as (b & Hh & _). exact Hh.
Qed.

(* A heap block's bytes are addressable: its shadow (AR_shadow_law block_shadow) marks every byte of
   [p, p + n) usable. *)
Lemma decode_block_range_addressable : forall (rd : Z -> option Z) p n q len,
  block_shadow rd SHADOW_OFF p (req_size n) -> 0 <= n -> p <= q -> 0 <= len -> q + len <= p + n ->
  range_addressable rd SHADOW_OFF q len.
Proof.
  intros rd p n q len (Hp8 & Hn0 & HB) Hn Hq Hl Hql x Hx.
  assert (Hreq : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  set (i := (x - p) / 8).
  assert (Hi : 0 <= i < (req_size n + 7) / 8) by (unfold i; Z.div_mod_to_equations; lia).
  specialize (HB i Hi).
  assert (Ex : shadow_of_addr SHADOW_OFF p + i = shadow_of_addr SHADOW_OFF x).
  { unfold shadow_of_addr, i. Z.div_mod_to_equations. lia. }
  rewrite Ex in HB. eexists. split; [exact HB|].
  unfold saddr_ok. destruct (Z.ltb_spec i (req_size n / 8)) as [Hlt|Hge]; [left; reflexivity|].
  right. unfold i in *. Z.div_mod_to_equations. lia.
Qed.

(* A range of visible bytes is in the walk's footprint (crtA_w_head.v crtA_rng_vis). *)
Lemma decode_rng_vis : forall (W : world tfibsegs) a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (a + i)) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) a n.
Proof.
  intros W a n H0 H1 Hv. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hj. unfold LCK.RNG_W, LCK.range_avoids. intros kk Hk. unfold LCK.woff.
  assert (Ub : bv_unsigned (Z_to_bv 64 b) = b) by (apply MState.unsigned_lit; lia).
  rewrite Ub. replace (b + Z.of_nat kk) with (a + (b + Z.of_nat kk - a)) by lia. apply Hv. lia.
Qed.

(* Present bytes form a stack range in the footprint view (crtA_w_head.v crtA_stk_present). *)
Lemma decode_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> LFrame.stk AImg0.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold LMem.wa. split.
  - exact (decode_wview_some m _ b Hb).
  - exists b. unfold LMem.mrd. rewrite Hb. reflexivity.
Qed.
End Mem.
