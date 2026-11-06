(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths, module names and numbers changed; 693 of its 784 lines of code are new or changed and 939 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/maybe_online_cgW.v, with its module paths and module names changed; 1846 of its 1962 lines of code are new or changed and 668 lines of the source are left out. *)
(* io_recv: Theorem transport_io_recv_cg_holds : the statement transport_io_recv_cg_holds_stmt of
   lib/A/Prog/io_recv_cg.v, the machine walk of io_recv on fuzz_transport.asan at 0x834c4 (168 bytes, frame 32).

   The walk is a G-form caller-journal walk: it holds the caller's journal ajournal_gx G_HARNESS 0 []
   (lib/A/W_journalG.v) from the entry to the return, and the runs are the symbolic runs of lib/A/Prog/PaShadow.v
   taken over that journal (lib/A/Prog/TransportGRunA.v paj_run_x). The stores into g_rx_fail and g_rx_times are
   allowed by the run's write right awr_ok_x (bytes of G); m_rx and m_tick are G-form callees composed in the same
   journal, and __asan_memcpy is applied through lib/A/Prog/TransportGCg.v gx_intrin_at.

   The code forms the address of each global from an auipc high part: the listing names the loads (PLdHi, the object
   atom) but the two stores and the second load of g_rx are raw words whose address is the high part plus an
   immediate. The walk's symbolic state carries them as the three aliases of ir_alias, each the listing's own
   relation between the high part and the object (ir_vals_img, decided on the image).

   The world across the two callees. A G-form callee's post keeps the caller's blocks and frames outside its written
   range and the image bytes OUTSIDE G, and gives the world relation at its own world. TF lies outside G
   (trans_tf_off_g) and outside every written range (iorecv_apart), so the walk carries TF's bytes and placement to
   the copy through one acall_kept_g over the bytes ir_eo (io_recv's two globals and m_rx's mrx_wr, which holds
   m_tick's). The bytes of g_rx, which the code reads again after the call, are bytes of G: they are read back through
   the model, since m_rx_m and m_tick_m change no world byte outside ir_wo (the offsets of m_rx_cg.v mrx_wr); ir_keep
   carries that, ir_wo_mrx turns an offset of ir_wo into an address of mrx_wr, and ir_G_kept reads it at the walk's
   view. The paths: g_rx_fail <> 0, g_rx = 0 and g_rx_times = 0 return with no call; on the others the code calls
   m_tick (n = 0) or m_rx (n <> 0), on both sides of the bltu that chooses n = min (g_rx_len, cap), then
   __asan_memcpy (bp, g_rx, n). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
m_lost_cg m_rx_cg m_tick_cg check_state_data_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TCb TImg TWorldLemmas TIoRecv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_recv_seg_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TIR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TIoRecv.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.

(* ------------------------------------------------------------------ *)
(* The walk's state and its kept facts                                 *)
(* ------------------------------------------------------------------ *)

Section irw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The listing's objects are the four globals; each high part plus the code's immediate is its global. *)
Lemma ir_vals_img :
  VAL (A_OBJ 31) = TA_g_rx_fail /\ VAL (A_OBJ 32) = TA_g_rx /\ VAL (A_OBJ 33) = TA_g_rx_times /\
  VAL (A_OBJ 34) = TA_g_rx_len /\ VAL (A_HI 65) - 1240 = TA_g_rx_fail /\ VAL (A_HI 66) + 1200 = TA_g_rx /\
  VAL (A_HI 67) - 1248 = TA_g_rx_times /\ BASE + AF_io_recv = TI.ti_io_recv timg_A.
Proof. vm_compute. repeat split. Qed.

Lemma ir_inG_row : forall o b n a, In (o, b, n) TMAP_A -> b <= a < b + n -> inG TG.G_HARNESS a.
Proof.
intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The walk's valuation: the 32 registers at the entry, the shadow base and the four loaded values of Bw. *)
Definition ir_vals (Bw : list byte) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.OFF_g_rx_fail 4); Z_to_bv 64 (TW.u_at Bw TW.OFF_g_rx 8);
   Z_to_bv 64 (TW.u_at Bw TW.OFF_g_rx_times 4); Z_to_bv 64 (TW.u_at Bw TW.OFF_g_rx_len 8)].
Definition ir_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (ir_vals Bw)).

Lemma ir_agree : forall regs Bw, env_agree 32 (Ereg regs (ir_vals Bw)) (ir_E regs Bw).
Proof. intros regs Bw. split; [intros n Hn; unfold ir_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* The entry state: the frame below sp, the four globals holding the world's bytes, the three aliases. *)
Lemma ir_entry : forall (W : world segs) regs mem Bw,
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  (forall a, spZ regs - IORECV_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (ir_E regs Bw) ss_ir
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_io_recv)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem Bw Htw Hpres Hsp Hsp16.
  destruct ir_vals_img as (V31 & V32 & V33 & V34 & VH65 & VH66 & VH67 & _).
  set (E := ir_E regs Bw).
  assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, ir_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (EHI : forall j, (j < 278)%nat -> ew E (A_HI j) = Z_to_bv 64 (VAL (A_HI j)))
    by (intros j Hj; unfold E, ir_E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (B31 : base_val E (Some (A_OBJ 31)) = TA_g_rx_fail)
    by (apply VB; [rewrite (EOB 31%nat ltac:(lia)), V31; reflexivity | unfold TA_g_rx_fail; lia]).
  assert (B32 : base_val E (Some (A_OBJ 32)) = TA_g_rx)
    by (apply VB; [rewrite (EOB 32%nat ltac:(lia)), V32; reflexivity | unfold TA_g_rx; lia]).
  assert (B33 : base_val E (Some (A_OBJ 33)) = TA_g_rx_times)
    by (apply VB; [rewrite (EOB 33%nat ltac:(lia)), V33; reflexivity | unfold TA_g_rx_times; lia]).
  assert (B34 : base_val E (Some (A_OBJ 34)) = TA_g_rx_len)
    by (apply VB; [rewrite (EOB 34%nat ltac:(lia)), V34; reflexivity | unfold TA_g_rx_len; lia]).
  assert (E2 : ew E 2 = YK11.getr regs 2%bv) by (unfold E, ir_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (B2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (ir_vals Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, ir_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36.
  cbn [Nat.add nth ir_vals] in E32, E33, E34, E35, E36.
  pose proof (TWL.u_at_range Bw TW.OFF_g_rx_fail 4) as R33. pose proof (TWL.u_at_range Bw TW.OFF_g_rx 8) as R34.
  pose proof (TWL.u_at_range Bw TW.OFF_g_rx_times 4) as R35.
  pose proof (TWL.u_at_range Bw TW.OFF_g_rx_len 8) as R36.
  change (8 * Z.of_nat 4) with 32 in R33, R35. change (8 * Z.of_nat 8) with 64 in R34, R36.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_ir.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold ir_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [|apply Forall_cons; [|apply Forall_nil]]]]].
    + unfold stack_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. unfold IORECV_FRAME in *.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
    + unfold ir_fail_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B31.
      split; [unfold TA_g_rx_fail; lia|]. split; [unfold TA_g_rx_fail; lia|].
      split.
      { intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_g_rx_fail + o) G_HARNESS_rw).
        apply (ir_inG_row _ _ _ _ TMAP_A_g_rx_fail). unfold TW.SZ_g_rx_fail. lia. }
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TA_g_rx_fail 0 4 (SOff 33 0) (TW.u_at Bw TW.OFF_g_rx_fail 4));
        [apply DEN; [exact E33 | lia] | exact R33 | lia |].
      pose proof (tw_read_val segs _ TMAP_A Bw TW.OFF_g_rx_fail TA_g_rx_fail TW.SZ_g_rx_fail 0 4 TMAP_A_ok Htw
        TMAP_A_g_rx_fail ltac:(lia) ltac:(unfold TW.SZ_g_rx_fail; lia)) as Hv.
      rewrite !Z.add_0_r in Hv. exact Hv.
    + unfold ir_rx_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B32.
      split; [unfold TA_g_rx; lia|]. split; [unfold TA_g_rx; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TA_g_rx 0 8 (SOff 34 0) (TW.u_at Bw TW.OFF_g_rx 8));
        [apply DEN; [exact E34 | lia] | exact R34 | lia |].
      pose proof (tw_read_val segs _ TMAP_A Bw TW.OFF_g_rx TA_g_rx TW.SZ_g_rx 0 8 TMAP_A_ok Htw
        TMAP_A_g_rx ltac:(lia) ltac:(unfold TW.SZ_g_rx; lia)) as Hv.
      rewrite !Z.add_0_r in Hv. exact Hv.
    + unfold ir_times_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
      split; [unfold TA_g_rx_times; lia|]. split; [unfold TA_g_rx_times; lia|].
      split.
      { intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_g_rx_times + o) G_HARNESS_rw).
        apply (ir_inG_row _ _ _ _ TMAP_A_g_rx_times). unfold TW.SZ_g_rx_times. lia. }
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TA_g_rx_times 0 4 (SOff 35 0) (TW.u_at Bw TW.OFF_g_rx_times 4));
        [apply DEN; [exact E35 | lia] | exact R35 | lia |].
      pose proof (tw_read_val segs _ TMAP_A Bw TW.OFF_g_rx_times TA_g_rx_times TW.SZ_g_rx_times 0 4 TMAP_A_ok Htw
        TMAP_A_g_rx_times ltac:(lia) ltac:(unfold TW.SZ_g_rx_times; lia)) as Hv.
      rewrite !Z.add_0_r in Hv. exact Hv.
    + unfold ir_len_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B34.
      split; [unfold TA_g_rx_len; lia|]. split; [unfold TA_g_rx_len; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TA_g_rx_len 0 8 (SOff 36 0) (TW.u_at Bw TW.OFF_g_rx_len 8));
        [apply DEN; [exact E36 | lia] | exact R36 | lia |].
      pose proof (tw_read_val segs _ TMAP_A Bw TW.OFF_g_rx_len TA_g_rx_len TW.SZ_g_rx_len 0 8 TMAP_A_ok Htw
        TMAP_A_g_rx_len ltac:(lia) ltac:(unfold TW.SZ_g_rx_len; lia)) as Hv.
      rewrite !Z.add_0_r in Hv. exact Hv.
  - unfold ir_regions, stack_region, ir_fail_region, ir_rx_region, ir_times_region, ir_len_region.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2, B31, B32, B33, B34.
    unfold IORECV_FRAME, TA_g_rx_fail, TA_g_rx, TA_g_rx_times, TA_g_rx_len. repeat split; lia.
  - unfold ir_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    assert (H65 : VAL (A_HI 65) = TA_g_rx_fail + 1240) by lia.
    assert (H66 : VAL (A_HI 66) = TA_g_rx - 1200) by lia.
    assert (H67 : VAL (A_HI 67) = TA_g_rx_times + 1248) by lia.
    unfold ir_alias. cbn [alias_ok sv_denot].
    rewrite (EHI 65%nat ltac:(lia)), (EHI 66%nat ltac:(lia)), (EHI 67%nat ltac:(lia)),
      (EOB 31%nat ltac:(lia)), (EOB 32%nat ltac:(lia)), (EOB 33%nat ltac:(lia)), H65, H66, H67, V31, V32, V33.
    rewrite Usp, E32, E33, E35.
    unfold TA_g_rx_fail, TA_g_rx, TA_g_rx_times in *.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | f_equal; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* What the walk keeps                                                 *)
(* ------------------------------------------------------------------ *)

(* the bytes of G the code itself may write *)
Definition ir_gw (a : Z) : Prop :=
  TA_g_rx_fail <= a < TA_g_rx_fail + 4 \/ TA_g_rx_times <= a < TA_g_rx_times + 4.

Lemma ir_gw_wr : forall Bw bp cap a, ir_gw a -> iorecv_wr Bw bp cap a.
Proof.
intros Bw bp cap a [H | H]; unfold iorecv_wr, twa_fld; [left | right; left];
  unfold TW.SZ_g_rx_fail, TW.SZ_g_rx_times; lia.
Qed.

Lemma ir_gw_inG : forall a, ir_gw a -> inG TG.G_HARNESS a.
Proof.
intros a [H | H].
- apply (ir_inG_row _ _ _ _ TMAP_A_g_rx_fail). unfold TW.SZ_g_rx_fail. lia.
- apply (ir_inG_row _ _ _ _ TMAP_A_g_rx_times). unfold TW.SZ_g_rx_times. lia.
Qed.

(* from the entry memory memc to a memory m of the walk's runs: every byte outside the frame and the two globals'
   bytes kept, presence grows *)
Definition ir_KA (W : world segs) (memc m : word -> option byte) (sp : Z) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - IORECV_FRAME <= a < sp) -> ~ ir_gw a ->
     aview segs (w_H W) m a = aview segs (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).

Lemma ir_KA_refl : forall W memc sp, ir_KA W memc memc sp.
Proof. intros W memc sp. split; [intros; reflexivity | intros a Ha; exact Ha]. Qed.

Lemma ir_KA_step : forall (E : env) (rs : smem) (W : world segs) memc m m' sp,
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi ->
     (sp - IORECV_FRAME <= a < sp) \/ ir_gw a) ->
  ir_KA W memc m sp ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  ir_KA W memc m' sp.
Proof.
intros E rs W memc m m' sp Hw [K1 K2] Hfr Hg. split.
- intros a Ha H1 H2.
  rewrite (kept_of_frame E rs (w_H W) m m' (fun x => (sp - IORECV_FRAME <= x < sp) \/ ir_gw x) Hfr Hw a Ha
    (fun X => match X with or_introl X1 => H1 X1 | or_intror X2 => H2 X2 end)).
  exact (K1 a Ha H1 H2).
- intros a Ha. exact (apresent_grows _ _ _ a Hg (K2 a Ha)).
Qed.

(* the call's kept fact across one run of the walk before a call, for any written range Eo holding ir_gw *)
Lemma ir_kept_step : forall lyc Sc (W : world segs) memc mdc m m' (regs : bvmap 5 word) (Eo : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - IORECV_STK -> (forall a, ir_gw a -> Eo a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W m (spZ regs - IORECV_STK) (spZ regs) Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IORECV_FRAME <= a < spZ regs) -> ~ ir_gw a ->
     aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W m' (spZ regs - IORECV_STK) (spZ regs) Eo.
Proof.
intros lyc Sc W memc mdc m m' regs Eo LAWS HAR Hce HE HK Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (SK : IORECV_STK = 8384) by reflexivity. assert (SF : IORECV_FRAME = 32) by reflexivity.
assert (GLO : forall a, ir_gw a -> a < kLowMemEnd)
  by (intros a [Ha|Ha]; unfold TA_g_rx_fail, TA_g_rx_times, kLowMemEnd in *; lia).
apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc m m'
  (spZ regs - IORECV_STK) (spZ regs) Eo
  (fun a => (spZ regs - IORECV_FRAME <= a < spZ regs) \/ ir_gw a) HAR HK).
- intros a Ha Hn. apply Hkp; [exact Ha | intros X; apply Hn; left; exact X | intros X; apply Hn; right; exact X].
- exact Hgr.
- intros a [X | X] Hc; [lia | pose proof (GLO a X); unfold kLowMemEnd in *; lia].
- intros b0 m0 i Hb Hi [X | X]; [| exact (HE _ X)].
  exfalso. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HAR Hb) as (_ & H4096 & Hbc & _). lia.
- intros a [X | X] Hi HnG _ _.
  + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  + exact (HnG (ir_gw_inG a X)).
- intros cid pos a Hin Hr [X | X]; [| exact (HE _ X)].
  exfalso.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

(* Two worlds: a region whose bytes and writable window the call kept. *)
Lemma ir_region_kept : forall (E : env) (H H' : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview segs H' m2 a = aview segs H m a) ->
  (forall a, b + wlo <= a < b + whi -> writable_at segs (mrestrict H m) a -> writable_at segs (mrestrict H' m2) a) ->
  region_kept segs E (mrestrict H m) (mrestrict H' m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H' m m2 n b lo hi wlo whi cs Hn Hav Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- apply Hw. exact Ha.
Qed.

(* the kept fact of the walk across one step that changes only bytes of Zs *)
Lemma ir_KA_upd : forall (W : world segs) memc m m' sp,
  ir_KA W memc m sp ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((sp - IORECV_FRAME <= a < sp) \/ ir_gw a) ->
     aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  ir_KA W memc m' sp.
Proof.
intros W memc m m' sp [K1 K2] Hs Hg. split.
- intros a Ha H1 H2. rewrite (Hs a Ha ltac:(intros [X|X]; [exact (H1 X) | exact (H2 X)])). exact (K1 a Ha H1 H2).
- intros a Ha. exact (Hg a (K2 a Ha)).
Qed.

Lemma ir_gw_dec : forall a, ir_gw a \/ ~ ir_gw a.
Proof. intros a. unfold ir_gw. lia. Qed.

(* A 4-byte chunk of a run's region, read as the value it holds. *)
Lemma ir_chunk_val4 : forall (E : env) (m : word -> option byte) base (e : sv) v,
  YP09.chunk_ok segs E m base (YP09.mkChunk 0 (YP09.CVal 4 e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  YI04.val_mem segs m base 4 v.
Proof.
intros E m base e v Hc He Hv k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm. rewrite Z.add_0_r in Hm. rewrite Hm.
injection Hb as <-. rewrite He. f_equal. unfold YP09.byte_of_word.
rewrite unsigned_lit_small by lia. rewrite (le_byte_small v 4 k) by (cbn; lia). reflexivity.
Qed.

(* A value in memory, read through the walk's view. *)
Lemma ir_aview_of_val : forall (H : word -> bool) (m : word -> option byte) a (n : nat) v,
  YI04.val_mem segs (mrestrict H m) a n v ->
  forall j, (j < n)%nat -> aview segs H m (a + Z.of_nat j) = Some (le_byte v n j).
Proof.
intros H m a n v Hv j Hj. unfold aview. rewrite (Hv j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold le_byte.
pose proof (Z.mod_pos_bound (Z.shiftr (v mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat j)) 256 ltac:(lia)).
unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

(* The world relation after the walk's own runs: nothing of G changed. *)
Lemma ir_tw_none : forall (W : world segs) memc m Bq sp,
  tw_at TMAP_A (aview segs (w_H W) memc) Bq -> ir_KA W memc m sp ->
  alloc_ceiling <= sp - IORECV_FRAME ->
  (forall a, ir_gw a -> aview segs (w_H W) m a = aview segs (w_H W) memc a) ->
  tw_at TMAP_A (aview segs (w_H W) m) Bq.
Proof.
intros W memc m Bq sp Htw [KA _] Hce Hgw. apply (tw_kept TMAP_A (aview segs (w_H W) memc)); [exact Htw|].
intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
pose proof asan_consts as (C1 & _).
destruct (ir_gw_dec x) as [Hg | Hg]; [exact (Hgw x Hg) | apply KA; [lia | unfold IORECV_FRAME in *; lia | exact Hg]].
Qed.

(* ... after a store of v at one of the two globals the code writes, the other one unchanged. *)
Lemma ir_tw_fail : forall (W : world segs) memc m Bq sp,
  tw_at TMAP_A (aview segs (w_H W) memc) Bq -> ir_KA W memc m sp ->
  alloc_ceiling <= sp - IORECV_FRAME ->
  YI04.val_mem segs (mrestrict (w_H W) m) TA_g_rx_fail 4 0 ->
  (forall a, TA_g_rx_times <= a < TA_g_rx_times + 4 -> aview segs (w_H W) m a = aview segs (w_H W) memc a) ->
  tw_at TMAP_A (aview segs (w_H W) m) (TW.set_g_rx_fail Bq 0).
Proof.
intros W memc m Bq sp Htw [KA _] Hce Hv Hti.
pose proof asan_consts as (C1 & _).
unfold TW.set_g_rx_fail. rewrite <- (Z.add_0_r TW.OFF_g_rx_fail).
apply (tw_write TMAP_A (aview segs (w_H W) memc) (aview segs (w_H W) m) Bq TW.OFF_g_rx_fail TA_g_rx_fail
  TW.SZ_g_rx_fail 0 4 0 TMAP_A_ok Htw TMAP_A_g_rx_fail).
- lia.
- unfold TW.SZ_g_rx_fail; lia.
- intros j Hj. rewrite Z.add_0_r. exact (ir_aview_of_val (w_H W) m TA_g_rx_fail 4 0 Hv j Hj).
- intros x Hx Hn. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  destruct (Z_lt_le_dec x TA_g_rx_times) as [L1|L1]; [|destruct (Z_lt_le_dec x (TA_g_rx_times + 4)) as [L2|L2]].
  + apply KA; [lia | unfold IORECV_FRAME in *; lia | unfold ir_gw; lia].
  + apply Hti. lia.
  + apply KA; [lia | unfold IORECV_FRAME in *; lia | unfold ir_gw; lia].
Qed.

Lemma ir_tw_times : forall (W : world segs) memc m Bq sp v,
  tw_at TMAP_A (aview segs (w_H W) memc) Bq -> ir_KA W memc m sp ->
  alloc_ceiling <= sp - IORECV_FRAME ->
  YI04.val_mem segs (mrestrict (w_H W) m) TA_g_rx_times 4 v ->
  (forall a, TA_g_rx_fail <= a < TA_g_rx_fail + 4 -> aview segs (w_H W) m a = aview segs (w_H W) memc a) ->
  tw_at TMAP_A (aview segs (w_H W) m) (TW.set_g_rx_times Bq v).
Proof.
intros W memc m Bq sp v Htw [KA _] Hce Hv Hfi.
pose proof asan_consts as (C1 & _).
unfold TW.set_g_rx_times. rewrite <- (Z.add_0_r TW.OFF_g_rx_times).
apply (tw_write TMAP_A (aview segs (w_H W) memc) (aview segs (w_H W) m) Bq TW.OFF_g_rx_times TA_g_rx_times
  TW.SZ_g_rx_times 0 4 v TMAP_A_ok Htw TMAP_A_g_rx_times).
- lia.
- unfold TW.SZ_g_rx_times; lia.
- intros j Hj. rewrite Z.add_0_r. exact (ir_aview_of_val (w_H W) m TA_g_rx_times 4 v Hv j Hj).
- intros x Hx Hn. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  destruct (Z_lt_le_dec x TA_g_rx_fail) as [L1|L1]; [|destruct (Z_lt_le_dec x (TA_g_rx_fail + 4)) as [L2|L2]].
  + apply KA; [lia | unfold IORECV_FRAME in *; lia | unfold ir_gw; lia].
  + apply Hfi. lia.
  + apply KA; [lia | unfold IORECV_FRAME in *; lia | unfold ir_gw; lia].
Qed.

Lemma ir_nth_firstn : forall (A : Type) (l : list A) i j d, (i < j)%nat -> nth i (firstn j l) d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros i j d H.
- rewrite firstn_nil. reflexivity.
- destruct j as [|j]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma ir_nth_zs : forall (l : list byte) j, (j < length l)%nat -> nth j (TW.zs l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
unfold TW.zs. intros l. induction l as [|x l IH]; intros j H; cbn [length] in H; [lia|].
destruct j as [|j]; [reflexivity|]. cbn [map nth]. apply IH. lia.
Qed.

(* The cap bytes at bp: visible, so some list X is there; its first length got bytes are got when got's bytes are
   there. *)
Lemma ir_buf_X : forall (W : world segs) m bp cap (got : list byte),
  0 <= bp -> 0 <= cap -> bp + cap <= 2 ^ 63 ->
  (forall a, bp <= a < bp + cap -> ~ in_img segs a) ->
  (forall a, bp <= a < bp + cap -> aview segs (w_H W) m a <> None) ->
  (length got <= Z.to_nat cap)%nat ->
  garr8 segs (mrestrict (w_H W) m) bp (TW.zs got) ->
  exists X : list byte, length X = Z.to_nat cap /\ garr8 segs (mrestrict (w_H W) m) bp (TW.zs X) /\
    firstn (length got) X = got.
Proof.
intros W m bp cap got Hbp Hcap Hhi Himg Hvis Hlen Hgot.
destruct (garr8_of_present segs (mrestrict (w_H W) m) bp (Z.to_nat cap)) as (l & Hl & Hg).
{ intros a Ha. rewrite Z2Nat.id in Ha by lia.
  destruct (apresent_of_aview segs (w_H W) m a ltac:(lia) (Himg a Ha) (Hvis a Ha)) as [Hh [b Hb]].
  exists b. unfold mrestrict. rewrite Hh. exact Hb. }
pose proof (garr8_bytes_ok segs _ _ _ Hg) as Hok.
exists (TW.bs l). assert (Hzs : TW.zs (TW.bs l) = l).
{ unfold TW.zs, TW.bs. rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
  intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bytes_ok in Hok.
  rewrite Forall_forall in Hok. specialize (Hok x Hx). unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia. }
split; [unfold TW.bs; rewrite length_map; exact Hl|]. split; [rewrite Hzs; exact Hg|].
apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)).
- rewrite length_firstn. unfold TW.bs. rewrite length_map. lia.
- intros j Hj. rewrite length_firstn in Hj. unfold TW.bs in Hj. rewrite length_map in Hj.
  rewrite ir_nth_firstn by lia.
  pose proof (garr8_mbyte segs _ _ _ j Hg ltac:(lia)) as M1.
  pose proof (garr8_mbyte segs _ _ _ j Hgot ltac:(unfold TW.zs; rewrite length_map; lia)) as M2.
  assert (M3 : Z_to_bv 8 (nth j l 0) = Z_to_bv 8 (nth j (TW.zs got) 0)) by congruence. clear M1 M2.
  change (nth j (TW.bs l) (Z_to_bv 8 0)) with (nth j (map (Z_to_bv 8) l) (Z_to_bv 8 0)).
  rewrite (map_nth (Z_to_bv 8) l 0 j). rewrite M3, (ir_nth_zs got j ltac:(lia)). apply Z_to_bv_bv_unsigned.
Qed.

(* The post at the return, from the pieces each path gives. *)
Lemma ir_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W W2 : world segs) memc k regs bp cap Bw Bw' r got
    ly2 S2 regsF mF mdF,
  AR_laws segs B ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mF mdF k ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mF (spZ regs - IORECV_STK) (spZ regs) (iorecv_wr Bw bp cap) ->
  mo_le MT Sc S2 0 ->
  YK11.getr regsF 10 = w64 r ->
  tw_at TMAP_A (aview segs (w_H W2) mF) Bw' -> TW.g_fail_next Bw' <= 1 ->
  (exists X : list byte, length X = Z.to_nat cap /\ garr8 segs (mrestrict (w_H W2) mF) bp (TW.zs X) /\
     firstn (length got) X = got) ->
  forall mat, transport_io_recv_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bp cap Bw Bw' r got W2
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W W2 memc k regs bp cap Bw Bw' r got ly2 S2 regsF mF mdF
  LAWS Hra HJF HP RF1 Hfr Hperm HK HMO H10 HTW HGF HX mat.
unfold transport_io_recv_post, transport_cg_post.
exists ly2, S2, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
split. { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [unfold IORECV_EV; lia|].
split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJF|].
split; [exact HP|]. split; [exact Hfr|]. split; [exact Hperm|]. split; [exact HK|]. split; [exact HMO|].
split; [exact H10|]. split; [exact HTW|]. split; [exact HGF | exact HX].
Qed.

(* ------------------------------------------------------------------ *)
(* The callees' facts                                                  *)
(* ------------------------------------------------------------------ *)

Ltac ir_mo_case H :=
  first
  [ left; ir_offs; unfold TA_M, TW.SZ_M in *; lia
  | right; ir_offs; unfold TA_OW, TW.SZ_OW in *; lia
  | let ii := fresh "ii" in let Hii := fresh "Hii" in let Hr := fresh "Hr" in
    destruct H as (ii & Hii & Hr); right; ir_offs; unfold TA_OW, TW.SZ_OW in *; lia ].

(* m_rx's written range lies in M's and OW's payloads *)
Lemma ir_mrx_MO : forall a, mrx_wr a -> (TA_M <= a < TA_M + TW.SZ_M) \/ (TA_OW <= a < TA_OW + TW.SZ_OW).
Proof.
intros a H. unfold mrx_wr, twa_fld in H.
repeat (destruct H as [H|H]; [ir_mo_case H |]). ir_mo_case H.
Qed.

Lemma ir_mrx_inG : forall a, mrx_wr a -> inG TG.G_HARNESS a.
Proof.
intros a H. destruct (ir_mrx_MO a H) as [Hm | Ho].
- apply (ir_inG_row _ _ _ _ TMAP_A_M). exact Hm.
- apply (ir_inG_row _ _ _ _ TMAP_A_OW). exact Ho.
Qed.

(* m_tick's written range lies in m_rx's *)
Lemma ir_mtick_mrx : forall Bq a, mtick_wr Bq a -> mrx_wr a.
Proof.
intros Bq a [_ H]. unfold mlost_wr, mset_wr in H. unfold mrx_wr.
destruct H as [H | [H | (_ & [(Hi & H) | [H | H]])]].
- do 9 right. left. exact H.
- do 12 right. left. exact H.
- do 14 right. left. exists (TW.OW_n Bq). split; [exact Hi | exact H].
- do 13 right. left. exact H.
- do 2 right. left. exact H.
Qed.

(* a byte of g_rx is not one m_rx writes *)
Lemma ir_rx_not_mrx : forall a, TA_g_rx <= a < TA_g_rx + 8 -> ~ mrx_wr a.
Proof.
intros a Ha H. destruct (ir_mrx_MO a H) as [Hm | Ho]; unfold TA_M, TA_OW, TA_g_rx, TW.SZ_M, TW.SZ_OW in *; lia.
Qed.

(* The bytes of G the walk carries as written up to the copy: its own two globals and m_rx's (m_tick's lie in
   m_rx's). *)
Definition ir_eo (a : Z) : Prop := ir_gw a \/ mrx_wr a.

Lemma ir_eo_inG : forall a, ir_eo a -> inG TG.G_HARNESS a.
Proof. intros a [H | H]; [exact (ir_gw_inG a H) | exact (ir_mrx_inG a H)]. Qed.

Lemma ir_eo_wr : forall Bw bp cap a, ir_eo a -> iorecv_wr Bw bp cap a.
Proof.
intros Bw bp cap a [H | H]; [exact (ir_gw_wr Bw bp cap a H) | unfold iorecv_wr; right; right; left; exact H].
Qed.

(* the call state's layout is the journal's start layout, at every state of the journal *)
Lemma ir_ly_eq : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  (forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) /\
  ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly.
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
destruct HJi as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Eslo & Eshi & _).
split; [intros cid pos; unfold frame_addr; rewrite EF; reflexivity | split; [exact Eslo | exact Eshi]].
Qed.

(* the journal's window is present at every state of the journal *)
Lemma ir_jpres : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k (_ & HXO & (memS & HJi & _) & _) a Ha.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
apply Hpres. lia.
Qed.

(* the caller's write right at another state of the same journal *)
Lemma ir_awr_move : forall STK sp0 FP bl0 lyc Sc ly2 S2 own a,
  awr_byte STK sp0 FP bl0 (ablocks B lyc Sc) lyc own a ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  awr_byte STK sp0 FP bl0 (ablocks B ly2 S2) ly2 own a.
Proof.
intros STK sp0 FP bl0 lyc Sc ly2 S2 own a H Hp Hf.
assert (Hin : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hp) Hbm)).
destruct H as [H | [(HF & b & n & Hb & Hr) | [(b & n & Hb & Hn & Hr) | (cid & pos & Hc & Hr)]]].
- left. exact H.
- right; left. split; [exact HF | exists b, n; split; [exact (Hin _ Hb) | exact Hr]].
- right; right; left. exists b, n. split; [exact (Hin _ Hb) | split; [exact Hn | exact Hr]].
- right; right; right. exists cid, pos. split; [exact Hc|]. rewrite !Hf. exact Hr.
Qed.

(* a placement at a later memory of the walk's own runs before a call *)
Lemma ir_src_run : forall lyc Sc (W : world segs) memc m q n sp,
  trans_src_ok B lyc Sc W memc q n ->
  ir_KA W memc m sp -> alloc_ceiling <= sp - IORECV_FRAME -> sp <= 2 ^ 47 ->
  (forall a, q <= a < q + n -> 0 <= a < 2 ^ 64 /\ ~ (sp - IORECV_FRAME <= a < sp) /\ ~ ir_gw a) ->
  trans_src_ok B lyc Sc W m q n.
Proof.
intros lyc Sc W memc m q n sp Hs [KA _] Hce H47 Hr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (trans_src_ok_view B lyc Sc W W memc m q n Hs).
- intros a Ha. destruct (Hr a Ha) as (H0 & H1 & H2). exact (KA a H0 H1 H2).
- intros s Hs'. apply KA; [unfold kLowMemEnd, kHighShadowEnd in *; lia | unfold IORECV_FRAME, kHighShadowEnd in *; lia |].
  unfold ir_gw, TA_g_rx_fail, TA_g_rx_times, kLowMemEnd in *. lia.
Qed.

(* A byte of a caller's frame, or of its shadow, is not one of ir_eo (bytes of G). *)
Lemma ir_frame_not_eo : forall lyc Sc (W : world segs) memc mdc cid pos a,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> In (cid, pos) (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
  ~ ir_eo a.
Proof.
intros lyc Sc W memc mdc cid pos a LAWS HAR Hin Hr He.
pose proof (ir_eo_inG a He) as HG.
pose proof (inG_G_HARNESS_hull a HG) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
- exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia) (trans_g_img a HG)).
- destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & _).
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold shadow_addr, SHADOW_OFF in Hr. lia.
Qed.

(* the call's kept fact at a state of the walk's own runs, from ir_KA *)
Lemma ir_kept_of_KA : forall lyc Sc (W : world segs) memc mdc m (regs : bvmap 5 word) (Eo : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - IORECV_STK ->
  (forall a, spZ regs - IORECV_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  (forall a, ir_gw a -> Eo a) -> ir_KA W memc m (spZ regs) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W m (spZ regs - IORECV_STK) (spZ regs) Eo.
Proof.
intros lyc Sc W memc mdc m regs Eo LAWS HAR Hce Hwin HE [KA GA].
apply (ir_kept_step lyc Sc W memc mdc memc m regs Eo LAWS HAR Hce HE).
- apply dk_kept_refl_g. exact Hwin.
- intros a Ha H1 H2. exact (KA a Ha H1 H2).
- exact GA.
Qed.

(* one run after a call (at the callee's world W2) that changes only the frame *)
Lemma ir_kept_run_w : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) m m' (regs : bvmap 5 word)
    (Eo : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - IORECV_STK ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 m (spZ regs - IORECV_STK) (spZ regs) Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IORECV_FRAME <= a < spZ regs) ->
     aview segs (w_H W2) m' a = aview segs (w_H W2) m a) ->
  (forall a, apresent (w_H W2) m a -> apresent (w_H W2) m' a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 m' (spZ regs - IORECV_STK) (spZ regs) Eo.
Proof.
intros lyc Sc W memc mdc W2 m m' regs Eo LAWS HAR Hce HK Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (SK : IORECV_STK = 8384) by reflexivity. assert (SF : IORECV_FRAME = 32) by reflexivity.
apply (ir_kept_step_w B LAWS TG.G_HARNESS lyc Sc W memc mdc W2 m m' (spZ regs - IORECV_STK) (spZ regs) Eo
  (fun a => spZ regs - IORECV_FRAME <= a < spZ regs) HAR HK).
- intros a Ha Hn. exact (Hkp a Ha Hn).
- exact Hgr.
- intros a X Hc. lia.
- intros b0 m0 i Hb Hi X. exfalso.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HAR Hb) as (_ & H4096 & Hbc & _). lia.
- intros a X Hi _ _ _. pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
- intros cid pos a Hin Hr X. exfalso.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

(* the call's kept fact across __asan_memcpy (its written bytes: the first n bytes of the buffer and its stack
   scratch below sp - 32), at the callee's world W2 *)
Lemma ir_kept_cpy : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) m m' (regs : bvmap 5 word) bp cap n
    (Eo : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - IORECV_STK -> decode_in_fake lyc Sc bp cap -> 0 <= n <= cap ->
  (forall a, bp <= a < bp + n -> Eo a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 m (spZ regs - IORECV_STK) (spZ regs) Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (bp <= a < bp + n) ->
     ~ (spZ regs - IORECV_FRAME - ESTACK <= a < spZ regs - IORECV_FRAME) ->
     aview segs (w_H W2) m' a = aview segs (w_H W2) m a) ->
  (forall a, apresent (w_H W2) m a -> apresent (w_H W2) m' a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 m' (spZ regs - IORECV_STK) (spZ regs) Eo.
Proof.
intros lyc Sc W memc mdc W2 m m' regs bp cap n Eo LAWS HAR Hce (cid0 & pos0 & Hin0 & F1 & F2) Hn BW HK Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (SK : IORECV_STK = 8384) by reflexivity. assert (SF : IORECV_FRAME = 32) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid0 pos0 HAR Hin0) as (G4096 & Gce & _).
apply (ir_kept_step_w B LAWS TG.G_HARNESS lyc Sc W memc mdc W2 m m' (spZ regs - IORECV_STK) (spZ regs) Eo
  (fun a => (bp <= a < bp + n) \/ (spZ regs - IORECV_FRAME - ESTACK <= a < spZ regs - IORECV_FRAME)) HAR HK).
- intros a Ha Hz. apply Hkp; [exact Ha | intros X; apply Hz; left; exact X | intros X; apply Hz; right; exact X].
- exact Hgr.
- intros a [X | X] Hc; lia.
- intros b0 m0 i Hb Hi [X | X]; [exact (BW _ X) |].
  exfalso. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HAR Hb) as (_ & H4096 & Hbc & _). lia.
- intros a [X | X] Hi HnG _ _.
  + exact (frm_img segs B LAWS lyc Sc W memc mdc cid0 pos0 a HAR Hin0 ltac:(lia) Hi).
  + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
- intros cid pos a Hin Hr [X | X]; [exact (BW _ X) |].
  exfalso.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the run's regions                                           *)
(* ------------------------------------------------------------------ *)

(* A 4-byte chunk at offset 0 of a region, read as the value its expression denotes (any sign). *)
Lemma ir_rd4 : forall (E : env) (m : word -> option byte) n b lo hi wlo whi cs e v,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk 0 (YP09.CVal 4 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  YI04.val_mem segs m b 4 v.
Proof.
intros E m n b lo hi wlo whi cs e v Hr Hb Hin He.
pose proof (field_of_region_any E m n b cs lo hi wlo whi 0 4%N e Hr Hb Hin ltac:(lia)) as Hv.
rewrite Z.add_0_r, He, Z_to_bv_unsigned in Hv. change (N.to_nat 4) with 4%nat in Hv.
assert (EQ : bv_wrap 64 v mod 2 ^ (8 * Z.of_N 4) mod 2 ^ (8 * Z.of_nat 4) = v mod 2 ^ (8 * Z.of_nat 4)).
{ change (8 * Z.of_N 4) with 32. change (8 * Z.of_nat 4) with 32. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 32 * 2 ^ 32). rewrite Z.mod_mod by lia.
  rewrite (Z.mod_eq v (2 ^ 32 * 2 ^ 32)) by lia.
  set (M := 2 ^ 32).
  replace (v - M * M * (v / (M * M))) with (v + (- (M * (v / (M * M)))) * M) by ring.
  apply Z_mod_plus_full. }
intros j Hj. rewrite (Hv j Hj). do 2 f_equal. unfold YO0f.le_byte. rewrite <- EQ. reflexivity.
Qed.

(* Two memories holding the same 4-byte value agree on its bytes. *)
Lemma ir_same4 : forall (H H' : word -> bool) (m m' : word -> option byte) b v,
  YI04.val_mem segs (mrestrict H m) b 4 v -> YI04.val_mem segs (mrestrict H' m') b 4 v ->
  forall a, b <= a < b + 4 -> aview segs H m a = aview segs H' m' a.
Proof.
intros H H' m m' b v H1 H2 a Ha. replace a with (b + Z.of_nat (Z.to_nat (a - b))) by lia.
rewrite (ir_aview_of_val H m b 4 v H1 (Z.to_nat (a - b)) ltac:(lia)).
rewrite (ir_aview_of_val H' m' b 4 v H2 (Z.to_nat (a - b)) ltac:(lia)).
reflexivity.
Qed.

(* the store of g_rx_times - 1 at 0x83518 *)
Lemma ir_dec_denot : forall E u, ew E 35 = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 35 0)) (SLit (-1))) = Z_to_bv 64 (bv_swrap 32 u - 1).
Proof.
intros E u H R.
change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 35 0)) (SLit (-1)))) with
  (alu64 ALU_ADD (sv_denot E (SExt true 32 (SOff 35 0))) (sv_denot E (SLit (-1)))).
rewrite (ir_sext32 E 35 u H R). change (sv_denot E (SLit (-1))) with (Z_to_bv 64 (-1)).
rewrite zalu64_sound. apply Z_to_bv64_eq_mod. cbv [zalu64 zalu_raw zcanon M64].
rewrite Z.mod_mod by lia. rewrite <- Zplus_mod. f_equal; try lia.
Qed.

(* the world relation kept when every byte of G is *)
Lemma ir_tw_G : forall (rd rd' : Z -> option Z) Bq, tw_at TMAP_A rd Bq ->
  (forall a, inG TG.G_HARNESS a -> rd' a = rd a) -> tw_at TMAP_A rd' Bq.
Proof.
intros rd rd' Bq H Hk. apply (tw_kept TMAP_A rd); [exact H|].
intros x (o & b & n & Hin & Hx). apply Hk. exact (ir_inG_row o b n x Hin Hx).
Qed.

(* the walk's valuation below atom 32 at a later environment *)
Lemma ir_agree2 : forall regs Bw E, (forall n, (n < 32)%nat -> ew E n = ew (ir_E regs Bw) n) ->
  ed E = ed (ir_E regs Bw) -> env_agree 32 (Ereg regs (ir_vals Bw)) E.
Proof.
intros regs Bw E H1 H2. split.
- intros n Hn. rewrite (H1 n Hn). unfold ir_E. apply Eimg_low. unfold A_TEXT. lia.
- rewrite H2. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Byte lists                                                          *)
(* ------------------------------------------------------------------ *)

Lemma ir_nth_skipn : forall (A : Type) (l : list A) o j d, nth j (skipn o l) d = nth (o + j) l d.
Proof.
intros A l o. revert l. induction o as [|o IH]; intros l j d; [reflexivity|].
destruct l as [|x l]; [destruct j; reflexivity | exact (IH l j d)].
Qed.

Lemma ir_map_skipn : forall (A C : Type) (g : A -> C) (l : list A) o, map g (skipn o l) = skipn o (map g l).
Proof.
intros A C g l o. revert l. induction o as [|o IH]; intros l; [reflexivity|].
destruct l as [|x l]; [reflexivity | exact (IH l)].
Qed.

Lemma ir_map_firstn : forall (A C : Type) (g : A -> C) (l : list A) o, map g (firstn o l) = firstn o (map g l).
Proof.
intros A C g l o. revert l. induction o as [|o IH]; intros l; [reflexivity|].
destruct l as [|x l]; [reflexivity | cbn [firstn map]; f_equal; exact (IH l)].
Qed.

(* k bytes of L from index o, read at d of another memory that agrees with them *)
Lemma ir_garr8_at : forall (H H' : word -> bool) (m m' : word -> option byte) x d (L : list Z) o k,
  garr8 segs (mrestrict H m) x L ->
  (forall j, (j < k)%nat -> (o + j < length L)%nat ->
     aview segs H' m' (d + Z.of_nat j) = aview segs H m (x + Z.of_nat (o + j))) ->
  garr8 segs (mrestrict H' m') d (firstn k (skipn o L)).
Proof.
intros H H' m m' x d L o k HG Hv j Hj. rewrite length_firstn, length_skipn in Hj.
rewrite (ir_nth_firstn Z (skipn o L) j k 0) by lia. rewrite ir_nth_skipn.
destruct (HG (o + j)%nat ltac:(lia)) as [Hm Hr]. split; [|exact Hr].
intros k0 Hk0. assert (k0 = 0%nat) by lia. subst k0. specialize (Hm 0%nat ltac:(lia)).
change (Z.of_nat 0) with 0 in Hm |- *. rewrite Z.add_0_r in Hm. rewrite Z.add_0_r.
pose proof (Hv j ltac:(lia) ltac:(lia)) as E. unfold aview in E. rewrite Hm in E. cbn [option_map] in E.
lazymatch type of E with option_map _ ?t = _ =>
  destruct t as [b'|] eqn:Eb; cbn [option_map] in E; [|discriminate E] end.
f_equal. apply bv_eq. congruence.
Qed.

Lemma ir_amem_sub : forall p n p' n', amem_range p n -> p <= p' -> p' + n' <= p + n -> amem_range p' n'.
Proof. intros p n p' n' H H1 H2. unfold amem_range in *. lia. Qed.

Lemma ir_disj : forall d x n, (forall a, d <= a < d + n -> ~ (x <= a < x + n)) -> 0 <= n ->
  d + n <= x \/ x + n <= d.
Proof.
intros d x n H Hn.
destruct (Z_le_gt_dec (d + n) x) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (x + n) d) as [L2|L2]; [right; exact L2|].
exfalso. destruct (Z_le_gt_dec d x) as [L3|L3]; [apply (H x); lia | apply (H d); lia].
Qed.

Lemma ir_vis_chain : forall (x y z w : option Z), w <> None -> x = y -> y = z -> z = w -> x <> None.
Proof. intros x y z w Hw H1 H2 H3. rewrite H1, H2, H3. exact Hw. Qed.

(* ------------------------------------------------------------------ *)
(* The facts of the call steps                                         *)
(* ------------------------------------------------------------------ *)

(* m_rx's frame at the call: the part of TF from p on, at the call memory and at m_rx's window *)
Lemma ir_tframe_rx : forall lyc Sc (W : world segs) memc mdc m (regs regsT : bvmap 5 word) f p Bw bp cap,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  trans_tframe_at B lyc Sc W memc regs IORECV_STK (Some f) -> iorecv_apart (Some f) Bw bp cap ->
  ir_KA W memc m (spZ regs) -> alloc_ceiling <= spZ regs - IORECV_FRAME -> spZ regs <= 2 ^ 47 ->
  0 <= p - TI.tf_addr f < Z.of_nat (length (TI.tf_bytes f)) ->
  spZ regsT = spZ regs - IORECV_FRAME ->
  trans_tframe_at B lyc Sc W m regsT MRX_STK
    (Some (TI.TFrame p (skipn (Z.to_nat (p - TI.tf_addr f)) (TI.tf_bytes f)))).
Proof.
intros lyc Sc W memc mdc m regs regsT f p Bw bp cap LAWS HAR Htf Hap KA Hce H47 Hoff Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (SK : IORECV_STK = 8384) by reflexivity. assert (SF : IORECV_FRAME = 32) by reflexivity.
assert (SMR : MRX_STK = 8352) by reflexivity.
unfold trans_tframe_at in Htf |- *. destruct Htf as (Ha0 & HG & Hs & Hwo).
cbn [TI.tf_addr TI.tf_bytes]. rewrite length_skipn.
assert (Hl : Z.of_nat (length (TI.tf_bytes f) - Z.to_nat (p - TI.tf_addr f)) =
  Z.of_nat (length (TI.tf_bytes f)) - (p - TI.tf_addr f)) by lia.
rewrite Hl.
pose proof (trans_src_ok_place B LAWS lyc Sc W memc mdc _ _ HAR Hs ltac:(lia)) as Hpl.
assert (Hin : forall a, TI.tf_addr f <= a < TI.tf_addr f + Z.of_nat (length (TI.tf_bytes f)) ->
  0 <= a < 2 ^ 64 /\ ~ (spZ regs - IORECV_FRAME <= a < spZ regs) /\ ~ ir_gw a).
{ intros a Ha. split; [lia|]. split; [unfold decode_off_win in Hwo; lia|].
  intros X. exact (Hap a (ir_gw_wr Bw bp cap a X) f eq_refl Ha). }
split; [lia|]. split; [|split].
- change (map DSpec.bz (skipn (Z.to_nat (p - TI.tf_addr f)) (TI.tf_bytes f))) with
    (map (fun b : byte => bv_unsigned b) (skipn (Z.to_nat (p - TI.tf_addr f)) (TI.tf_bytes f))).
  change (map DSpec.bz (TI.tf_bytes f)) with (map (fun b : byte => bv_unsigned b) (TI.tf_bytes f)) in HG.
  rewrite ir_map_skipn.
  rewrite <- (firstn_all (skipn (Z.to_nat (p - TI.tf_addr f)) (map (fun b : byte => bv_unsigned b) (TI.tf_bytes f)))).
  apply (ir_garr8_at (w_H W) (w_H W) memc m (TI.tf_addr f) p _ _ _ HG).
  intros j Hj1 Hj2. rewrite length_map in Hj2.
  replace (TI.tf_addr f + Z.of_nat (Z.to_nat (p - TI.tf_addr f) + j)) with (p + Z.of_nat j) by lia.
  destruct KA as [KA1 _]. destruct (Hin (p + Z.of_nat j) ltac:(lia)) as (H1 & H2 & H3). exact (KA1 _ H1 H2 H3).
- assert (Hs' : trans_src_ok B lyc Sc W memc p (Z.of_nat (length (TI.tf_bytes f)) - (p - TI.tf_addr f)))
    by (apply (trans_src_ok_sub B lyc Sc W memc _ _ p _ Hs); lia).
  apply (ir_src_run lyc Sc W memc m p _ (spZ regs) Hs' KA Hce H47).
  intros a Ha. apply Hin. lia.
- unfold decode_off_win in *. rewrite Hsp. lia.
Qed.

(* the copy's destination at the call memory mT: amem_range, its shadow, and the buffer's bytes kept *)
Lemma ir_dest : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) mT bp cap n (regs : bvmap 5 word),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  decode_in_fake lyc Sc bp cap -> decode_rd_ok W memc bp cap -> 0 <= n <= cap ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mT (spZ regs - IORECV_STK) (spZ regs) ir_eo ->
  amem_range bp n /\ range_addressable (aview segs (w_H W2) mT) SHADOW_OFF bp n /\
  (0 < n -> shadow_hull_vis (aview segs (w_H W2) mT) bp n) /\
  (forall a, bp <= a < bp + cap -> aview segs (w_H W2) mT a = aview segs (w_H W) memc a).
Proof.
intros lyc Sc W memc mdc W2 mT bp cap n regs LAWS HAR Hfake Hrd Hn HK.
pose proof Hfake as (cid0 & pos0 & Hin0 & F1 & F2).
destruct HK as (_ & _ & _ & K4 & _).
assert (KB : forall a, bp <= a < bp + cap -> aview segs (w_H W2) mT a = aview segs (w_H W) memc a).
{ intros a Ha.
  assert (Hr : in_zr a (frame_rng lyc (cid0, pos0)) \/
               in_zr a (shadow_addr (frame_addr lyc cid0 pos0), fs_frame_bytes cid0 / 8))
    by (left; unfold in_zr, frame_rng; cbn [fst snd]; lia).
  exact (K4 cid0 pos0 a Hin0 Hr (ir_frame_not_eo lyc Sc W memc mdc cid0 pos0 a LAWS HAR Hin0 Hr)). }
assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
  in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
  aview segs (w_H W2) mT s = aview segs (w_H W) memc s)
  by (intros cid pos s Hin Hs;
      exact (K4 cid pos s Hin (or_intror Hs) (ir_frame_not_eo lyc Sc W memc mdc cid pos s LAWS HAR Hin (or_intror Hs)))).
pose proof Hrd as (_ & _ & _ & Ham & _).
split; [exact (ir_amem_sub bp cap bp n Ham ltac:(lia) ltac:(lia)) |].
destruct (Z_lt_le_dec 0 n) as [Hp | Hz].
- assert (Hfk : decode_in_fake lyc Sc bp n) by (exists cid0, pos0; split; [exact Hin0 | lia]).
  pose proof (decode_rd_ok_fake_kept B LAWS lyc Sc W W2 memc mT mdc bp n HAR Hfk
    (trans_rd_ok_sub W memc bp cap bp n Hrd ltac:(lia) ltac:(lia) ltac:(lia)) Hp
    (fun a Ha => KB a ltac:(lia)) KS) as (_ & Hra & Hhu & _).
  split; [exact Hra | split; [intros _; exact Hhu | exact KB]].
- split; [intros x Hx; lia | split; [intros Hp; lia | exact KB]].
Qed.

(* the copy's source for n <> 0: n bytes of TF at x, carried from the entry to the call memory mT *)
Lemma ir_src : forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mT mdT (regs regsT : bvmap 5 word)
    f x n bp cap Bw,
  AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mT mdT ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mT (spZ regs - IORECV_STK) (spZ regs) ir_eo ->
  trans_tframe_at B lyc Sc W memc regs IORECV_STK (Some f) -> trans_tf_off_g (Some f) ->
  iorecv_apart (Some f) Bw bp cap ->
  TI.tf_addr f <= x -> 0 < n -> x + n <= TI.tf_addr f + Z.of_nat (length (TI.tf_bytes f)) -> n <= cap ->
  spZ regsT = spZ regs - IORECV_FRAME ->
  (0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W2 regsT mT x n /\ (bp + n <= x \/ x + n <= bp) /\ amem_range x n /\
   range_addressable (aview segs (w_H W2) mT) SHADOW_OFF x n /\
   (0 < n -> shadow_hull_vis (aview segs (w_H W2) mT) x n)) /\
  (forall a, x <= a < x + n -> aview segs (w_H W2) mT a = aview segs (w_H W) memc a).
Proof.
intros lyc Sc W memc mdc ly2 S2 W2 mT mdT regs regsT f x n bp cap Bw LAWS HRU HRE HAR HART Hperm Hfr Hfa Elo Ehi
  HK Htf Hoffg Hapart Hx Hn Hxn Hcap Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (SK : IORECV_STK = 8384) by reflexivity. assert (SF : IORECV_FRAME = 32) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
unfold trans_tframe_at in Htf. destruct Htf as (Ha0 & _ & Hs & Hwo).
assert (Hs' : trans_src_ok B lyc Sc W memc x n)
  by (apply (trans_src_ok_sub B lyc Sc W memc _ _ x n Hs); lia).
assert (HnE : forall a, x <= a < x + n -> ~ ir_eo a)
  by (intros a Ha He; exact (Hapart a (ir_eo_wr Bw bp cap a He) f eq_refl ltac:(lia))).
assert (HGK : forall a, x <= a < x + n -> inG TG.G_HARNESS a ->
  aview segs (w_H W2) mT a = aview segs (w_H W) memc a)
  by (intros a Ha Hg; exfalso; exact (Hoffg f eq_refl a ltac:(lia) Hg)).
assert (HnEs : forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ ir_eo a).
{ intros a Ha He. pose proof (inG_G_HARNESS_hull a (ir_eo_inG a He)) as Hh.
  unfold TG.G_HARNESS_HI in Hh. unfold kLowMemEnd in Ha. lia. }
assert (Hoff' : x + n <= spZ regs - IORECV_STK \/ spZ regs <= x) by (unfold decode_off_win in Hwo; lia).
destruct (ir_src_acall B LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mT mdT (spZ regs - IORECV_STK) (spZ regs) ir_eo x n
  HAR HART Hperm Hfr Hfa Elo Ehi HK HGK HnE HnEs Hoff' Hs' Hn) as (Hs2 & KV).
pose proof (trans_src_ok_rd B LAWS ly2 S2 W2 mT mdT x n HART Hs2 Hn) as (Hv & Hra & Hhu & Ham & H0 & H63).
split; [|exact KV].
split; [exact H0 |]. split; [exact H63 |]. split.
{ intros a Ha. split; [exact (Hv a Ha) | rewrite Hsp; unfold decode_off_win in Hwo; lia]. }
split.
{ apply ir_disj; [|lia]. intros a Ha Hb.
  assert (Hw : iorecv_wr Bw bp cap a) by (unfold iorecv_wr; do 4 right; lia).
  apply (Hapart a Hw f eq_refl). lia. }
split; [exact Ham |]. split; [exact Hra | intros _; exact Hhu].
Qed.

(* the copy's source for n = 0: g_rx, not 0, lies in TF's range *)
Lemma ir_src0 : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) mT (regs regsT : bvmap 5 word) TF Bw bp,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  trans_tframe_at B lyc Sc W memc regs IORECV_STK TF -> iorecv_rx_in TF Bw -> TW.g_rx Bw <> 0 ->
  0 <= TW.g_rx Bw /\ TW.g_rx Bw + 0 <= 2 ^ 63 /\ src_ok segs W2 regsT mT (TW.g_rx Bw) 0 /\
  (bp + 0 <= TW.g_rx Bw \/ TW.g_rx Bw + 0 <= bp) /\ amem_range (TW.g_rx Bw) 0 /\
  range_addressable (aview segs (w_H W2) mT) SHADOW_OFF (TW.g_rx Bw) 0 /\
  (0 < 0 -> shadow_hull_vis (aview segs (w_H W2) mT) (TW.g_rx Bw) 0).
Proof.
intros lyc Sc W memc mdc W2 mT regs regsT TF Bw bp LAWS HAR Htf Hrx Hne.
destruct (TC.frame_from TF (TW.g_rx Bw)) as [fr|] eqn:Efr; [| exfalso; exact (Hrx Hne Efr)].
destruct (ir_frame_from_some _ _ _ Efr) as (f & -> & Hoff & _).
unfold trans_tframe_at in Htf. destruct Htf as (Ha0 & _ & Hs & _).
destruct (ir_src_ok_amem B LAWS lyc Sc W memc mdc _ _ HAR Hs) as (H0 & H63 & Ham).
assert (B2a : 0 <= TW.g_rx Bw <= 2 ^ 63) by lia.
assert (B2b : amem_range (TW.g_rx Bw) 0) by (apply (ir_amem_sub _ _ _ _ Ham); lia).
split; [lia|]. split; [lia|]. split; [intros a Ha; lia|]. split; [lia|]. split; [exact B2b|].
split; [intros y Hy; lia | intros H; lia].
Qed.

(* The post's X after a copy of n <> 0 bytes from TF: the cap bytes visible, got's bytes at bp. *)
Lemma ir_X : forall (W W2 : world segs) memc mT m3 mF bp cap n off (f : TI.tframe) r (got : list byte),
  0 <= bp -> 0 <= cap -> bp + cap <= 2 ^ 63 -> 0 <= n <= cap -> 0 <= off ->
  off + n <= Z.of_nat (length (TI.tf_bytes f)) ->
  (forall a, bp <= a < bp + cap -> ~ in_img segs a) ->
  (forall a, bp <= a < bp + cap -> aview segs (w_H W) memc a <> None) ->
  garr8 segs (mrestrict (w_H W) memc) (TI.tf_addr f) (map DSpec.bz (TI.tf_bytes f)) ->
  (forall a, bp <= a < bp + cap -> aview segs (w_H W2) mT a = aview segs (w_H W) memc a) ->
  (forall i, 0 <= i < n ->
     aview segs (w_H W2) mT (TI.tf_addr f + off + i) = aview segs (w_H W) memc (TI.tf_addr f + off + i)) ->
  (forall i, 0 <= i < n -> aview segs (w_H W2) m3 (bp + i) = aview segs (w_H W2) mT (TI.tf_addr f + off + i)) ->
  (forall a, bp + n <= a < bp + cap -> aview segs (w_H W2) m3 a = aview segs (w_H W2) mT a) ->
  (forall a, bp <= a < bp + cap -> aview segs (w_H W2) mF a = aview segs (w_H W2) m3 a) ->
  got = (if 0 <? r then TW.sub (TI.tf_bytes f) off (Z.to_nat n) else []) ->
  exists X : list byte, length X = Z.to_nat cap /\ garr8 segs (mrestrict (w_H W2) mF) bp (TW.zs X) /\
    firstn (length got) X = got.
Proof.
intros W W2 memc mT m3 mF bp cap n off f r got Hbp Hcap Hbe Hn Hoff Hon Himg Hvis HG KB KS Hcpy Hrest HF Hgot.
change (map DSpec.bz (TI.tf_bytes f)) with (map (fun b : byte => bv_unsigned b) (TI.tf_bytes f)) in HG.
assert (Hsrc : forall i, 0 <= i < n -> aview segs (w_H W) memc (TI.tf_addr f + off + i) <> None).
{ intros i Hi.
  pose proof (garr8_mbyte segs _ _ _ (Z.to_nat (off + i)) HG ltac:(rewrite length_map; lia)) as M.
  rewrite Z2Nat.id in M by lia. unfold aview.
  replace (TI.tf_addr f + off + i) with (TI.tf_addr f + (off + i)) by lia. rewrite M. cbn [option_map]. discriminate. }
assert (VF : forall a, bp <= a < bp + cap -> aview segs (w_H W2) mF a <> None).
{ intros a Ha. rewrite (HF a Ha). destruct (Z_lt_le_dec a (bp + n)) as [L|L].
  - replace a with (bp + (a - bp)) by lia. rewrite (Hcpy (a - bp) ltac:(lia)), (KS (a - bp) ltac:(lia)).
    apply Hsrc. lia.
  - rewrite (Hrest a ltac:(lia)), (KB a Ha). exact (Hvis a Ha). }
apply (ir_buf_X W2 mF bp cap got Hbp Hcap Hbe Himg VF).
- rewrite Hgot. destruct (0 <? r); [|cbn [length]; lia].
  pose proof (TWL.length_sub_le (TI.tf_bytes f) off (Z.to_nat n)). lia.
- rewrite Hgot. destruct (0 <? r); [|apply garr8_nil].
  unfold TW.sub, TW.zs. rewrite ir_map_firstn, ir_map_skipn.
  apply (ir_garr8_at (w_H W) (w_H W2) memc mF (TI.tf_addr f) bp _ _ _ HG).
  intros j Hj1 Hj2. rewrite length_map in Hj2.
  rewrite (HF (bp + Z.of_nat j) ltac:(lia)), (Hcpy (Z.of_nat j) ltac:(lia)), (KS (Z.of_nat j) ltac:(lia)).
  f_equal. lia.
Qed.

(* The post at a return with no call (got = []): the world relation at mF, nothing else written. *)
Lemma ir_close0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs bp cap Bw Bw' r
    regsF mF mdF,
  AR_laws segs B -> ameter_laws MT -> @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - IORECV_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - IORECV_STK ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mF mdF k ->
  decode_in_fake lyc Sc bp cap -> decode_rd_ok W memc bp cap -> decode_off_win regs IORECV_STK bp cap ->
  (forall x, bp <= x < bp + cap -> ~ inG TG.G_HARNESS x) -> 0 <= cap ->
  ir_KA W memc mF (spZ regs) ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 -> YK11.getr regsF 10 = w64 r ->
  tw_at TMAP_A (aview segs (w_H W) mF) Bw' -> TW.g_fail_next Bw' <= 1 ->
  forall mat, transport_io_recv_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bp cap Bw Bw' r [] W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bp cap Bw Bw' r regsF mF mdF
  LAWS MTL HAR Hwin Hce Hra HJF Hfake Hrd Hoff HnG Hcap KA HP RF1 RF10 HTW HGF mat.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (SK : IORECV_STK = 8384) by reflexivity. assert (SF : IORECV_FRAME = 32) by reflexivity.
apply (ir_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W W memc k regs bp cap Bw Bw' r [] lyc Sc regsF mF mdF
  LAWS Hra HJF HP RF1 eq_refl (Permutation_refl _)).
- exact (ir_kept_of_KA lyc Sc W memc mdc mF regs (iorecv_wr Bw bp cap) LAWS HAR Hce Hwin (ir_gw_wr Bw bp cap) KA).
- exact (mo_le_refl MT MTL Sc).
- exact RF10.
- exact HTW.
- exact HGF.
- destruct Hrd as (Hv & _ & _ & _ & Hbp & Hbe).
  destruct Hfake as (cid & pos & Hin & F1 & F2).
  pose proof KA as [KA1 _].
  apply (ir_buf_X W mF bp cap [] Hbp Hcap Hbe).
  + intros a Ha. exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia)).
  + intros a Ha. unfold decode_off_win in Hoff.
    rewrite (KA1 a ltac:(lia) ltac:(lia) ltac:(intros X; exact (HnG a Ha (ir_gw_inG a X)))). exact (Hv a Ha).
  + cbn [length]. lia.
  + apply garr8_nil.
Qed.

(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ir_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | _ => fail "ir_reg: HS is not st_ok_pi or st_ok of a restricted state"
  end.

(* The windows a run wrote, each inside the bytes of the goal: the windows of the state's regions, computed. *)
Ltac ir_win :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as <- <- <-; cbn [base_val] in Hx; cbv beta; unfold ir_gw; lia |]);
  destruct Hin.

(* The write rights of a run: the frame below sp (inside the caller's window), regions with no writable byte, and
   the two globals io_recv stores (bytes of G). *)
Ltac ir_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia
            | left; split; [unfold awr_byte; left; lia | lia]
            | right; left; apply ir_gw_inG; unfold ir_gw; lia ] |]);
  apply awr_ok_x_nil.

(* After a run before a call: the model generalized, ir_KA carried to the run's last memory, the old machine states
   dropped, the current one named ms. *)
Ltac ir_after KA HS :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt;
    try clear m0 end;
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let KW := fresh "KW" in
    pose proof (fun Hw => ir_KA_step Ex rsx _ _ _ _ _ Hw KA HFr HG) as KW;
    lazymatch type of KW with ?A -> _ =>
      let Hw := fresh "Hw" in assert (Hw : A) by ir_win; specialize (KW Hw); clear Hw end;
    clear KA HFr HG; rename KW into KA end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  repeat match goal with old : machine_state |- _ => clear old end;
  lazymatch type of HS with context [restrict _ ?m] => try rename m into ms end.

(* After a run after a call: the model generalized, the bytes outside the frame [sp - 32, sp) kept (KR), presence
   grown (GR), the current machine state named ms. *)
Ltac ir_after2 HS sp KR GR :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt;
    try clear m0 end;
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict ?Hh ?mo) (mrestrict _ ?mn), HG : mem_grows _ _ |- _ =>
    assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - IORECV_FRAME <= a < sp) ->
      aview segs Hh mn a = aview segs Hh mo a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn;
          apply (kept_of_frame Ex rsx Hh mo mn (fun y => sp - IORECV_FRAME <= y < sp) HFr);
          [ir_win | exact Ha | exact Hn]);
    assert (GR : forall a, apresent Hh mo a -> apresent Hh mn a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (apresent_grows _ _ _ a HG Ha));
    clear HFr HG end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  lazymatch type of HS with context [restrict _ ?m] => try rename m into ms end.

(* The walk. *)
Lemma ir_holds : @transport_io_recv_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_io_recv_cg_holds_stmt.
intros HCELLS HROU HRNE LAWS MTL HGX HMRX HMTK HCPY.
unfold transport_io_recv_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bp cap r got TF Bw Bw'
  HJ Hra Hra4 Hgp Htp H11 H12 Hsp16 Hlo Hhi Hcap Hfake Htwr Hrd Hoff HnG Htf Hoffg Hapart Hrxin Hrom Htw Hgfn Hm Hev.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
destruct (ir_ly_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (FAc & SLc & SHc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (SK : IORECV_STK = 8384) by reflexivity. assert (SF : IORECV_FRAME = 32) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity. assert (SMR : MRX_STK = 8352) by reflexivity.
assert (SMT : MTICK_STK = 16) by reflexivity.
assert (HBASE : BASE = 0x834c4 - 8800) by (vm_compute; reflexivity).
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - IORECV_STK) by lia.
assert (Hwin : forall a, spZ regs - IORECV_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (Hm16 : (spZ regs - 32 - sp0) mod 16 = 0).
{ replace (spZ regs - 32 - sp0) with (spZ regs - sp0 + (-2) * 16) by lia.
  rewrite Z_mod_plus_full, Zminus_mod, Hsp16, Hsp0a. reflexivity. }
assert (Hsp32 : (spZ regs - 32) mod 16 = 0).
{ replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
assert (HLB : Z.of_nat (length Bw) = TW.W_LEN)
  by (rewrite (tw_len _ _ _ Htw), Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]).
pose proof Hrd as (Hvis & _ & _ & Hamr & Hbp0 & Hbpe).
assert (Himg : forall a, bp <= a < bp + cap -> ~ in_img segs a).
{ intros a Ha. pose proof Hfake as (cid & pos & Hin & F1 & F2).
  exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia)). }
(* The valuation of the walk and its atoms. *)
set (E0 := ir_E regs Bw).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ir_E; apply Eimg_env).
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E0 n = YK11.getr regs q)
  by (intros n q Hn; unfold E0, ir_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 5)%nat -> ew E0 (32 + j) = nth j (ir_vals Bw) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, ir_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth ir_vals] in E33, E34, E35, E36. clear EX.
pose proof (TWL.u_at_range Bw TW.OFF_g_rx_fail 4) as R33. pose proof (TWL.u_at_range Bw TW.OFF_g_rx 8) as R34.
pose proof (TWL.u_at_range Bw TW.OFF_g_rx_times 4) as R35. pose proof (TWL.u_at_range Bw TW.OFF_g_rx_len 8) as R36.
change (8 * Z.of_nat 4) with 32 in R33, R35. change (8 * Z.of_nat 8) with 64 in R34, R36.
assert (R34' : 0 <= TW.g_rx Bw < 2 ^ 64) by exact R34.
assert (R36' : 0 <= TW.g_rx_len Bw < 2 ^ 64) by exact R36.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U272 : bv_unsigned (ew E0 272) = TA_g_rx_fail)
  by (unfold E0, ir_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U273 : bv_unsigned (ew E0 273) = TA_g_rx)
  by (unfold E0, ir_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U274 : bv_unsigned (ew E0 274) = TA_g_rx_times)
  by (unfold E0, ir_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (E11 : ew E0 11 = w64 bp) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E0 12 = w64 cap) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
(* g_rx_fail's and g_rx_times' bytes at the entry *)
pose proof (tw_read_val segs _ TMAP_A Bw TW.OFF_g_rx_fail TA_g_rx_fail TW.SZ_g_rx_fail 0 4 TMAP_A_ok Htw
  TMAP_A_g_rx_fail ltac:(lia) ltac:(unfold TW.SZ_g_rx_fail; lia)) as VF0.
pose proof (tw_read_val segs _ TMAP_A Bw TW.OFF_g_rx_times TA_g_rx_times TW.SZ_g_rx_times 0 4 TMAP_A_ok Htw
  TMAP_A_g_rx_times ltac:(lia) ltac:(unfold TW.SZ_g_rx_times; lia)) as VT0.
rewrite !Z.add_0_r in VF0, VT0.
(* The entry state. *)
pose proof (ir_entry W regs memc Bw Htw ltac:(intros a Ha; apply Hpres0; lia) Hsp Hsp16) as HS.
fold E0 in HS.
assert (SHOK : sh_ok segs IR_Bx IR_SH E0 (mrestrict (w_H W) memc)) by (unfold sh_ok, IR_SH; apply Forall_nil).
pose proof (ir_KA_refl W memc (spZ regs)) as KA.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_io_recv)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, 0x834c4 .. 0x834e0: the frame, the four saves, the load of g_rx_fail, `beqz`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ir_awr. }
ir_after KA HS.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
2: {
  (* g_rx_fail <> 0: the store of 0 at g_rx_fail, a0 = -EIO, return. *)
  rewrite (ir_br_eq32 E0 33 _ E33 R33) in Hc.
  change (bv_swrap 32 (TW.u_at Bw TW.OFF_g_rx_fail 4)) with (TW.g_rx_fail Bw) in Hc.
  assert (Hf : TC.truth (TW.g_rx_fail Bw) = true) by (unfold TC.truth; rewrite Hc; reflexivity).
  destruct (ir_m_fail TF Bw cap Bw' r got Hf Hm) as (-> & -> & ->). clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ir_awr. }
  ir_after KA HS.
  ir_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  ir_reg HS (Z_to_bv 5 10) (w64 (- TC.EIO)) RF10 ltac:(apply bv_eq; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms))
    by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (ir_vals Bw) HS);
        [exact (ir_agree regs Bw) | vm_compute; reflexivity]).
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
  cbn [ms_mem restrict] in RG1, RG3.
  pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ 0 RG1 U272 (or_introl eq_refl) eq_refl) as VF.
  pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.u_at Bw TW.OFF_g_rx_times 4) RG3 U274 (or_introl eq_refl)
    ltac:(cbn [sv_denot]; rewrite E35, unsigned_lit_small, Z.add_0_r by lia; reflexivity)) as VT.
  assert (HTF : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) (TW.set_g_rx_fail Bw 0)).
  { apply (ir_tw_fail W memc (ms_mem ms) Bw (spZ regs) Htw KA ltac:(lia) VF).
    intros a Ha. exact (ir_same4 (w_H W) (w_H W) (ms_mem ms) memc TA_g_rx_times _ VT VT0 a Ha). }
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  apply (ir_close0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bp cap Bw _ _ (ms_regs ms) (ms_mem ms) _
    LAWS MTL HAR Hwin Hce Hra HJ Hfake Hrd Hoff HnG ltac:(lia) KA HPF RF1 RF10 HTF).
  rewrite (ir_fail_gfn Bw HLB). exact Hgfn. }
(* g_rx_fail = 0 *)
rewrite (ir_br_eq32 E0 33 _ E33 R33) in Hc.
change (bv_swrap 32 (TW.u_at Bw TW.OFF_g_rx_fail 4)) with (TW.g_rx_fail Bw) in Hc.
assert (Hf0 : TC.truth (TW.g_rx_fail Bw) = false) by (unfold TC.truth; rewrite Hc; reflexivity). clear Hc.
(* run 2, 0x834f0 .. 0x834f8: s2, the load of g_rx, `beqz`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ir_awr. }
ir_after KA HS.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
1: {
  (* g_rx = 0: a0 = 0, return. *)
  rewrite (ir_br_eq64 E0 34 _ E34 R34) in Hc. change (TW.u_at Bw TW.OFF_g_rx 8) with (TW.g_rx Bw) in Hc.
  destruct (ir_m_zero TF Bw cap Bw' r got Hf0 ltac:(rewrite Hc; reflexivity) Hm) as (-> & -> & ->). clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ir_awr. }
  ir_after KA HS.
  ir_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  ir_reg HS (Z_to_bv 5 10) (w64 0) RF10 ltac:(apply bv_eq; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms))
    by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (ir_vals Bw) HS);
        [exact (ir_agree regs Bw) | vm_compute; reflexivity]).
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
  cbn [ms_mem restrict] in RG1, RG3.
  pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.u_at Bw TW.OFF_g_rx_fail 4) RG1 U272 (or_introl eq_refl)
    ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity)) as VF.
  pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.u_at Bw TW.OFF_g_rx_times 4) RG3 U274 (or_introl eq_refl)
    ltac:(cbn [sv_denot]; rewrite E35, unsigned_lit_small, Z.add_0_r by lia; reflexivity)) as VT.
  assert (HTF : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) Bw).
  { apply (ir_tw_none W memc (ms_mem ms) Bw (spZ regs) Htw KA ltac:(lia)).
    intros a [Ha | Ha].
    - exact (ir_same4 (w_H W) (w_H W) (ms_mem ms) memc TA_g_rx_fail _ VF VF0 a Ha).
    - exact (ir_same4 (w_H W) (w_H W) (ms_mem ms) memc TA_g_rx_times _ VT VT0 a Ha). }
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  exact (ir_close0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bp cap Bw Bw _ (ms_regs ms) (ms_mem ms) _
    LAWS MTL HAR Hwin Hce Hra HJ Hfake Hrd Hoff HnG ltac:(lia) KA HPF RF1 RF10 HTF Hgfn mat'). }
rewrite (ir_br_eq64 E0 34 _ E34 R34) in Hc. change (TW.u_at Bw TW.OFF_g_rx 8) with (TW.g_rx Bw) in Hc.
rename Hc into Hrx0.
assert (Hrx0' : TW.g_rx Bw <> 0) by (apply Z.eqb_neq; exact Hrx0).
(* run 3, 0x834fc .. 0x83508: s0 = bp, the load of g_rx_times, `beqz`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ir_awr. }
ir_after KA HS.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
1: {
  (* g_rx_times = 0: a0 = 0, return. *)
  rewrite (ir_br_eq32 E0 35 _ E35 R35) in Hc.
  change (bv_swrap 32 (TW.u_at Bw TW.OFF_g_rx_times 4)) with (TW.g_rx_times Bw) in Hc.
  destruct (ir_m_zero TF Bw cap Bw' r got Hf0 ltac:(rewrite Hrx0, Hc; reflexivity) Hm) as (-> & -> & ->).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ir_awr. }
  ir_after KA HS.
  ir_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  ir_reg HS (Z_to_bv 5 10) (w64 0) RF10 ltac:(apply bv_eq; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms))
    by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (ir_vals Bw) HS);
        [exact (ir_agree regs Bw) | vm_compute; reflexivity]).
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
  cbn [ms_mem restrict] in RG1, RG3.
  pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.u_at Bw TW.OFF_g_rx_fail 4) RG1 U272 (or_introl eq_refl)
    ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity)) as VF.
  pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.u_at Bw TW.OFF_g_rx_times 4) RG3 U274 (or_introl eq_refl)
    ltac:(cbn [sv_denot]; rewrite E35, unsigned_lit_small, Z.add_0_r by lia; reflexivity)) as VT.
  assert (HTF : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) Bw).
  { apply (ir_tw_none W memc (ms_mem ms) Bw (spZ regs) Htw KA ltac:(lia)).
    intros a [Ha | Ha].
    - exact (ir_same4 (w_H W) (w_H W) (ms_mem ms) memc TA_g_rx_fail _ VF VF0 a Ha).
    - exact (ir_same4 (w_H W) (w_H W) (ms_mem ms) memc TA_g_rx_times _ VT VT0 a Ha). }
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  exact (ir_close0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bp cap Bw Bw _ (ms_regs ms) (ms_mem ms) _
    LAWS MTL HAR Hwin Hce Hra HJ Hfake Hrd Hoff HnG ltac:(lia) KA HPF RF1 RF10 HTF Hgfn mat'). }
rewrite (ir_br_eq32 E0 35 _ E35 R35) in Hc.
change (bv_swrap 32 (TW.u_at Bw TW.OFF_g_rx_times 4)) with (TW.g_rx_times Bw) in Hc.
rename Hc into Ht0.
(* run 4, 0x8350c .. 0x83520: the load of g_rx_len, the store of g_rx_times - 1, `bltu`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ir_awr. }
ir_after KA HS.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* g_rx_len < cap: n = g_rx_len *)
rewrite (ir_br_ltu E0 36 12 _ cap E36 E12 R36 ltac:(lia)) in Hc.
change (TW.u_at Bw TW.OFF_g_rx_len 8) with (TW.g_rx_len Bw) in Hc. rename Hc into Hlt.
(* run 5, 0x83524: `beqz` on n. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ir_awr. }
ir_after KA HS.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
+ (* n = 0: m_tick, then the copy of 0 bytes. *)
rewrite (ir_br_eq64 E0 36 _ E36 R36) in Hc. change (TW.u_at Bw TW.OFF_g_rx_len 8) with (TW.g_rx_len Bw) in Hc.
apply Z.eqb_eq in Hc. rename Hc into Hn0.
destruct (ir_m_main TF Bw cap Bw' r got (TW.g_rx_len Bw) HLB Hf0 Hrx0 Ht0 ltac:(rewrite Hlt; reflexivity) Hm)
  as ([(_ & u & Etk) | (Hnz & _)] & (bytes & _ & Hr & Hgot)); [| exfalso; exact (Hnz Hn0)].
destruct u.
assert (Hr0 : r = 0) by (rewrite Hr, Hn0; reflexivity).
assert (Hg0 : got = []) by (rewrite Hgot, Hr0; reflexivity).
clear Hr Hgot. subst r got.
pose proof (ir_w1_length Bw HLB) as HL1.
pose proof (ir_mtick_keep (iorecv_w1 Bw) HL1 _ _ _ (ir_keep_refl _) Etk) as HK1m.
(* run 6, 0x8353c: `jal m_tick`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ir_awr. }
ir_after KA HS.
pose proof (st_ok_region_nth E0 _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_region_nth E0 _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
cbn [ms_mem restrict] in RG1, RG3.
pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.u_at Bw TW.OFF_g_rx_fail 4) RG1 U272 (or_introl eq_refl)
  ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity)) as VF.
pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.g_rx_times Bw - 1) RG3 U274 (or_introl eq_refl)
  (ir_dec_denot E0 _ E35 R35)) as VT.
assert (Htw1 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) (iorecv_w1 Bw)).
{ apply (ir_tw_times W memc (ms_mem ms) Bw (spZ regs) (TW.g_rx_times Bw - 1) Htw KA ltac:(lia) VT).
  intros a Ha. exact (ir_same4 (w_H W) (w_H W) (ms_mem ms) memc TA_g_rx_fail _ VF VF0 a Ha). }
clear RG1 RG3 VF VT.
pmkst HS.
ir_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 8924)) R1 ltac:(apply codeptr_val; exact HEI).
ir_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 32)) R2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ir_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ir_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = spZ regs - 32)
  by (rewrite R2; apply unsigned_lit_small; lia).
assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 32) by exact ESP. clear ESP.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_m_tick) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HMTK fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) _ k (ms_regs ms) (iorecv_w1 Bw) Bw' HJ).
  - rewrite R1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - change (4096 <= bv_unsigned (YK11.getr (ms_regs ms) (1%bv : bv 5))). rewrite R1, unsigned_lit_small; lia.
  - exact R3.
  - exact R4.
  - rewrite Hsp1. exact Hsp32.
  - rewrite Hsp1. lia.
  - rewrite Hsp1. lia.
  - exact Htw1.
  - exact Etk.
  - rewrite (proj2 iorecv_ev_eq). unfold IORECV_EV in Hev. lia. }
intros W2 c2 HWle HQ.
unfold transport_mtick_post, transport_cg_post in HQ.
destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e & -> & He & HJ2 & HP2 & Hfr2 & Hperm2 & HKc & HMO2 & HTW2).
assert (e = 0) by (rewrite (proj2 iorecv_ev_eq) in He; lia). subst e. rewrite Z.add_0_r in HJ2.
rewrite R1. rewrite Hsp1 in HKc.
destruct (ir_ly_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (FA2 & SL2 & SH2).
(* the running kept fact, merged with m_tick's *)
assert (HKX : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - IORECV_STK) (spZ regs) ir_eo).
{ eapply dk_kept_trans_g with (W1 := W) (memX := ms_mem ms) (slo' := spZ regs - 32 - MTICK_STK)
    (shi' := spZ regs - 32) (Eo' := ir_eo).
  - exact Hce.
  - lia.
  - exact (ir_kept_of_KA lyc Sc W memc mdc (ms_mem ms) regs ir_eo LAWS HAR Hce Hwin (fun a X => or_introl X) KA).
  - eapply acall_kept_g_weaken; [|exact HKc]. intros a X. right. exact (ir_mtick_mrx _ a X).
  - lia.
  - lia.
  - intros a X. exact X. }
(* the state after the call: the frame and g_rx kept *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0%nat; 2%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (ir_region_kept E0 (w_H W) (w_H W2) (ms_mem ms) mem2 2%nat (spZ regs)); [exact Usp | |].
    + intros a Ha. destruct HKc as (K1 & _). apply K1; lia.
    + intros a Ha _. apply (apresent_writable segs). destruct HKc as (_ & _ & _ & _ & K5 & _).
      apply K5; [lia | lia | exact (ir_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a ltac:(lia))].
  - apply (ir_region_kept E0 (w_H W) (w_H W2) (ms_mem ms) mem2 273%nat TA_g_rx); [exact U273 | |].
    + intros a Ha. exact (ir_G_kept _ _ (iorecv_w1 Bw) Bw' a Htw1 HTW2 HK1m
        (ir_inG_row _ _ _ a TMAP_A_g_rx ltac:(unfold TW.SZ_g_rx; lia)) (ir_rx_not_mrx a ltac:(lia))).
    + intros a Ha. lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regs2) CLOB)) in HS.
assert (HEJ1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros q Hq; apply ew_havoc_old; exact Hq).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E1lo by lia; exact Usp).
assert (SHOK1 : sh_ok segs IR_Bx IR_SH E1 (mrestrict (w_H W2) mem2)) by (unfold sh_ok, IR_SH; apply Forall_nil).
clear dependent ms.
(* run 7, 0x83540 .. 0x8354c: the load of g_rx again, a0 = bp, a2 = n = 0, `jal __asan_memcpy`. *)
paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
{ ir_awr. }
ir_after2 HS (spZ regs) KR GR.
pose proof (ir_kept_run_w lyc Sc W memc mdc W2 mem2 (ms_mem ms) regs ir_eo LAWS HAR Hce HKX KR GR) as HKT.
pmkst HS.
ir_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 8940)) R1 ltac:(apply codeptr_val; exact HEJ1).
ir_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 32)) R2 ltac:(cbn [sv_denot]; rewrite Usp1; f_equal; lia).
ir_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ir_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
ir_reg HS (Z_to_bv 5 10) (w64 bp) R10
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ir_reg HS (Z_to_bv 5 11) (w64 (TW.g_rx Bw)) R11
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
ir_reg HS (Z_to_bv 5 12) (w64 0) Q12
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite E36, unsigned_lit_small, Z.add_0_r by lia;
        change (TW.u_at Bw TW.OFF_g_rx_len 8) with (TW.g_rx_len Bw); rewrite Hn0; reflexivity).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = spZ regs - 32)
  by (rewrite R2; apply unsigned_lit_small; lia).
assert (Hsp2 : spZ (ms_regs ms) = spZ regs - 32) by exact ESP. clear ESP.
destruct (ir_dest lyc Sc W memc mdc W2 (ms_mem ms) bp cap 0 regs LAWS HAR Hfake Hrd ltac:(lia) HKT)
  as (Dam & Dra & Dhu & KB).
pose proof (ir_src0 lyc Sc W memc mdc W2 (ms_mem ms) regs (ms_regs ms) TF Bw bp LAWS HAR Htf Hrxin Hrx0') as Hsrc.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OCpy (transport_sigma TS___asan_memcpy)
    (HCPY fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own ly2 S2 _ k
    bp (TW.g_rx Bw) 0 (spZ regs - 32 - sp0) (Z_to_bv 64 (BASE + 8940)) HGX G_HARNESS_rw HJ2 R10 R11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite Hsp2. lia.
  - exact Hm16.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|]. intros a Ha. lia.
  - exact Dam.
  - exact Dra.
  - exact Dhu.
  - exact Hsrc. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hcpy3 & Heff3 & Hgr3).
jafter_call_keep_hi HS 2048%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat; 1%nat] HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 2%nat (spZ regs)); [exact Usp1 | | exact Hgr3].
    intros a Ha. apply Heff3; [lia | lia | lia].
  - apply (region_kept_aview _ _ _ _ 273%nat TA_g_rx); [rewrite E1lo by lia; exact U273 | | exact Hgr3].
    intros a Ha. apply Heff3; [unfold TA_g_rx in *; lia | lia | unfold TA_g_rx in *; lia]. }
specialize (HS3 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
set (E2 := havoc E1 2048 (map (YK11.getr regs3) CLOB)) in HS.
assert (HEJ2 : img_env VAL A_LIM E2) by (apply img_env_havoc_hi; [exact HEJ1 | cbv; lia]).
assert (E2lo : forall n, (n < 2048)%nat -> ew E2 n = ew E1 n) by (intros q Hq; apply ew_havoc_old; exact Hq).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite E2lo by lia; exact Usp1).
assert (SHOK2 : sh_ok segs IR_Bx IR_SH E2 (mrestrict (w_H W2) mem3)) by (unfold sh_ok, IR_SH; apply Forall_nil).
assert (HK3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem3 (spZ regs - IORECV_STK) (spZ regs)
  (iorecv_wr Bw bp cap)).
{ apply (ir_kept_cpy lyc Sc W memc mdc W2 (ms_mem ms) mem3 regs bp cap 0 (iorecv_wr Bw bp cap)
    LAWS HAR Hce Hfake ltac:(lia)).
  - intros a Ha. lia.
  - eapply acall_kept_g_weaken; [|exact HKT]. intros a X. exact (ir_eo_wr Bw bp cap a X).
  - intros a Ha H1 H2. apply Heff3; [exact Ha | exact H1 | lia].
  - exact Hgr3. }
set (mT := ms_mem ms) in *. clearbody mT. clear dependent ms.
(* run 8, 0x83550 .. 0x83568: a0 = sext.w 0, the reloads, `ret`. *)
paj_run_tok RUN HS HJ3 SHOK2 YC4b.Bspan.
{ ir_awr. }
ir_after2 HS (spZ regs) KR3 GR3.
pose proof (ir_kept_run_w lyc Sc W memc mdc W2 mem3 (ms_mem ms) regs (iorecv_wr Bw bp cap) LAWS HAR Hce HK3 KR3 GR3)
  as HKF.
ir_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
  ltac:(cbn [sv_denot]; rewrite E2lo, E1lo by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
ir_reg HS (Z_to_bv 5 10) (w64 0) RF10
  ltac:(refine (eq_trans (ir_sextw E2 (SOff 36 0) 0 _) _);
        [cbn [sv_denot]; rewrite E2lo, E1lo by lia; rewrite E36, unsigned_lit_small, Z.add_0_r by lia;
         change (TW.u_at Bw TW.OFF_g_rx_len 8) with (TW.g_rx_len Bw); rewrite Hn0; reflexivity
        | reflexivity]).
assert (HPF : aregs_preserved regs (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) E2 _ ms regs (ir_vals Bw) HS).
  - apply ir_agree2; [intros q Hq; rewrite E2lo, E1lo by lia; reflexivity | reflexivity].
  - vm_compute. reflexivity. }
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
apply (ir_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W W2 memc k regs bp cap Bw Bw' 0 [] ly2 S2 (ms_regs ms)
  (ms_mem ms) _ LAWS Hra HJ3 HPF RF1 Hfr2 Hperm2 HKF HMO2 RF10).
* apply (ir_tw_G (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)) Bw' HTW2). intros a Ha.
  pose proof (inG_G_HARNESS_hull a Ha) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  rewrite (KR3 a ltac:(lia) ltac:(lia)).
  transitivity (aview segs (w_H W2) mT a); [exact (Heff3 a ltac:(lia) ltac:(lia) ltac:(lia)) |].
  exact (KR a ltac:(lia) ltac:(lia)).
* rewrite (ir_gfn_keep _ _ HL1 HK1m), (ir_w1_gfn Bw HLB). exact Hgfn.
* apply (ir_buf_X W2 (ms_mem ms) bp cap [] Hbp0 ltac:(lia) Hbpe Himg).
  -- intros a Ha. unfold decode_off_win in Hoff.
     exact (ir_vis_chain _ _ _ _ (Hvis a Ha) (KR3 a ltac:(lia) ltac:(lia))
       (Heff3 a ltac:(lia) ltac:(lia) ltac:(lia)) (KB a Ha)).
  -- cbn [length]. lia.
  -- apply garr8_nil.
+ (* n <> 0: m_rx (g_rx, n), then the copy of n bytes from TF. *)
rewrite (ir_br_eq64 E0 36 _ E36 R36) in Hc. change (TW.u_at Bw TW.OFF_g_rx_len 8) with (TW.g_rx_len Bw) in Hc.
apply Z.eqb_neq in Hc. rename Hc into Hn0.
destruct (ir_m_main TF Bw cap Bw' r got (TW.g_rx_len Bw) HLB Hf0 Hrx0 Ht0 ltac:(rewrite Hlt; reflexivity) Hm)
  as ([(Hz & _) | (_ & rr & Erx)] & (bytes & Hrd' & Hr & Hgot)); [exfalso; exact (Hn0 Hz) |].
assert (HnC : 0 <= TW.g_rx_len Bw <= cap) by (apply Z.ltb_lt in Hlt; lia).
pose proof (ir_w1_length Bw HLB) as HL1.
pose proof (ir_mrx_keep (iorecv_w1 Bw) HL1 _ _ _ _ _ _ (ir_keep_refl _) Erx) as HK1m.
assert (Hgrx : TW.g_rx Bw' = TW.g_rx Bw) by (rewrite (ir_grx_keep _ _ HL1 HK1m); exact (ir_w1_rx Bw HLB)).
rewrite Hgrx in Hrd'.
destruct (ir_frame_read_some TF (TW.g_rx Bw) (TW.g_rx_len Bw) bytes Hrd' Hn0) as (f & -> & Of0 & _ & Ofn & Ebytes).
destruct (TC.frame_from (Some f) (TW.g_rx Bw)) as [fr|] eqn:Efr;
  [| try rewrite Efr in Erx; unfold TC.m_rx_m in Erx; discriminate Erx].
try rewrite Efr in Erx.
destruct (ir_frame_from_some _ _ _ Efr) as (f' & Ef' & _ & Efr').
assert (f' = f) by congruence. subst f'. subst fr.
pose proof Htf as Htf'. unfold trans_tframe_at in Htf'. destruct Htf' as (Ha0 & HGf & Hsf & Hwf).
pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc _ _ HAR Hsf ltac:(lia)) as (_ & _ & _ & _ & Htf0 & Htf63).
(* run 6, 0x83528 .. 0x8352c: a1 = n, `jal m_rx`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ir_awr. }
ir_after KA HS.
pose proof (st_ok_region_nth E0 _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_region_nth E0 _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
cbn [ms_mem restrict] in RG1, RG3.
pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.u_at Bw TW.OFF_g_rx_fail 4) RG1 U272 (or_introl eq_refl)
  ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity)) as VF.
pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.g_rx_times Bw - 1) RG3 U274 (or_introl eq_refl)
  (ir_dec_denot E0 _ E35 R35)) as VT.
assert (Htw1 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) (iorecv_w1 Bw)).
{ apply (ir_tw_times W memc (ms_mem ms) Bw (spZ regs) (TW.g_rx_times Bw - 1) Htw KA ltac:(lia) VT).
  intros a Ha. exact (ir_same4 (w_H W) (w_H W) (ms_mem ms) memc TA_g_rx_fail _ VF VF0 a Ha). }
clear RG1 RG3 VF VT.
pmkst HS.
ir_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 8908)) R1 ltac:(apply codeptr_val; exact HEI).
ir_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 32)) R2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ir_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ir_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
ir_reg HS (Z_to_bv 5 10) (w64 (TW.g_rx Bw)) R10
  ltac:(cbn [sv_denot]; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
ir_reg HS (Z_to_bv 5 11) (w64 (TW.g_rx_len Bw)) R11
  ltac:(cbn [sv_denot]; rewrite E36, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = spZ regs - 32)
  by (rewrite R2; apply unsigned_lit_small; lia).
assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 32) by exact ESP. clear ESP.
pose proof (ir_tframe_rx lyc Sc W memc mdc (ms_mem ms) regs (ms_regs ms) f (TW.g_rx Bw) Bw bp cap LAWS HAR Htf Hapart
  KA ltac:(lia) ltac:(lia) ltac:(lia) Hsp1) as HTF1.
assert (Hrom1 : trans_rom_view_rd W (ms_mem ms)).
{ intros a Ha. pose proof KA as [KA1 _]. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  rewrite (KA1 a ltac:(lia) ltac:(lia) ltac:(unfold ir_gw, TA_g_rx_fail, TA_g_rx_times; lia)). exact (Hrom a Ha). }
assert (Happ : mrx_apart (TI.TFrame (TW.g_rx Bw) (skipn (Z.to_nat (TW.g_rx Bw - TI.tf_addr f)) (TI.tf_bytes f)))).
{ intros x Hx. cbn [TI.tf_addr TI.tf_bytes]. rewrite length_skipn. intros Hin.
  apply (Hapart x (or_intror (or_intror (or_introl Hx))) f eq_refl). lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_m_rx) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HMRX fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) _ k (ms_regs ms)
    (TI.TFrame (TW.g_rx Bw) (skipn (Z.to_nat (TW.g_rx Bw - TI.tf_addr f)) (TI.tf_bytes f))) (TW.g_rx_len Bw) rr
    (iorecv_w1 Bw) Bw' HJ).
  - rewrite R1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - change (4096 <= bv_unsigned (YK11.getr (ms_regs ms) (1%bv : bv 5))). rewrite R1, unsigned_lit_small; lia.
  - exact R3.
  - exact R4.
  - exact R10.
  - exact R11.
  - rewrite Hsp1. exact Hsp32.
  - rewrite Hsp1. lia.
  - rewrite Hsp1. lia.
  - exact HTF1.
  - cbn [TI.tf_addr]. lia.
  - exact Happ.
  - exact Hrom1.
  - exact Htw1.
  - exact Erx.
  - rewrite (proj1 iorecv_ev_eq). unfold IORECV_EV in Hev. lia. }
intros W2 c2 HWle HQ.
unfold transport_mrx_post, transport_cg_post in HQ.
destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e & -> & He & HJ2 & HP2 & Hfr2 & Hperm2 & HKc & HMO2 & _ & HTW2).
assert (e = 0) by (rewrite (proj1 iorecv_ev_eq) in He; lia). subst e. rewrite Z.add_0_r in HJ2.
rewrite R1. rewrite Hsp1 in HKc.
destruct (ir_ly_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (FA2 & SL2 & SH2).
assert (HFA : forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos)
  by (intros cid pos; rewrite FA2, FAc; reflexivity).
assert (HSL : ly_stk_lo ly2 = ly_stk_lo lyc) by lia. assert (HSH : ly_stk_hi ly2 = ly_stk_hi lyc) by lia.
(* the running kept fact, merged with m_rx's *)
assert (HKX : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - IORECV_STK) (spZ regs) ir_eo).
{ eapply dk_kept_trans_g with (W1 := W) (memX := ms_mem ms) (slo' := spZ regs - 32 - MRX_STK)
    (shi' := spZ regs - 32) (Eo' := ir_eo).
  - exact Hce.
  - lia.
  - exact (ir_kept_of_KA lyc Sc W memc mdc (ms_mem ms) regs ir_eo LAWS HAR Hce Hwin (fun a X => or_introl X) KA).
  - eapply acall_kept_g_weaken; [|exact HKc]. intros a X. right. exact X.
  - lia.
  - lia.
  - intros a X. exact X. }
(* the state after the call: the frame and g_rx kept *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0%nat; 2%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (ir_region_kept E0 (w_H W) (w_H W2) (ms_mem ms) mem2 2%nat (spZ regs)); [exact Usp | |].
    + intros a Ha. destruct HKc as (K1 & _). apply K1; lia.
    + intros a Ha _. apply (apresent_writable segs). destruct HKc as (_ & _ & _ & _ & K5 & _).
      apply K5; [lia | lia | exact (ir_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a ltac:(lia))].
  - apply (ir_region_kept E0 (w_H W) (w_H W2) (ms_mem ms) mem2 273%nat TA_g_rx); [exact U273 | |].
    + intros a Ha. exact (ir_G_kept _ _ (iorecv_w1 Bw) Bw' a Htw1 HTW2 HK1m
        (ir_inG_row _ _ _ a TMAP_A_g_rx ltac:(unfold TW.SZ_g_rx; lia)) (ir_rx_not_mrx a ltac:(lia))).
    + intros a Ha. lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regs2) CLOB)) in HS.
assert (HEJ1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros q Hq; apply ew_havoc_old; exact Hq).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E1lo by lia; exact Usp).
assert (SHOK1 : sh_ok segs IR_Bx IR_SH E1 (mrestrict (w_H W2) mem2)) by (unfold sh_ok, IR_SH; apply Forall_nil).
clear dependent ms.
(* run 7, 0x83530 .. 0x8354c: `j`, the load of g_rx again, a0 = bp, a2 = n, `jal __asan_memcpy`. *)
paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
{ ir_awr. }
ir_after2 HS (spZ regs) KR GR.
pose proof (ir_kept_run_w lyc Sc W memc mdc W2 mem2 (ms_mem ms) regs ir_eo LAWS HAR Hce HKX KR GR) as HKT.
pmkst HS.
ir_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 8940)) R1 ltac:(apply codeptr_val; exact HEJ1).
ir_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 32)) R2 ltac:(cbn [sv_denot]; rewrite Usp1; f_equal; lia).
ir_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ir_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
ir_reg HS (Z_to_bv 5 10) (w64 bp) R10
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ir_reg HS (Z_to_bv 5 11) (w64 (TW.g_rx Bw)) R11
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
ir_reg HS (Z_to_bv 5 12) (w64 (TW.g_rx_len Bw)) Q12
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite E36, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = spZ regs - 32)
  by (rewrite R2; apply unsigned_lit_small; lia).
assert (Hsp2 : spZ (ms_regs ms) = spZ regs - 32) by exact ESP. clear ESP.
destruct (ir_dest lyc Sc W memc mdc W2 (ms_mem ms) bp cap (TW.g_rx_len Bw) regs LAWS HAR Hfake Hrd HnC HKT)
  as (Dam & Dra & Dhu & KB).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HART.
destruct (ir_src lyc Sc W memc mdc ly2 S2 W2 (ms_mem ms) _ regs (ms_regs ms) f (TW.g_rx Bw) (TW.g_rx_len Bw) bp cap Bw
  LAWS HROU HRNE HAR HART Hperm2 Hfr2 HFA HSL HSH HKT Htf Hoffg Hapart ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  Hsp2) as (Hsrc & KS).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OCpy (transport_sigma TS___asan_memcpy)
    (HCPY fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own ly2 S2 _ k
    bp (TW.g_rx Bw) (TW.g_rx_len Bw) (spZ regs - 32 - sp0) (Z_to_bv 64 (BASE + 8940)) HGX G_HARNESS_rw HJ2 R10 R11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite Hsp2. lia.
  - exact Hm16.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|].
    intros a Ha. left. destruct (Htwr a ltac:(lia)) as [(Hw & _ & _ & _) | HGa]; [| exfalso; exact (HnG a ltac:(lia) HGa)].
    split; [exact (ir_awr_move STK sp0 FP _ lyc Sc ly2 S2 own a Hw Hperm2 HFA) |].
    rewrite Hsp2. unfold decode_off_win in Hoff. lia.
  - exact Dam.
  - exact Dra.
  - exact Dhu.
  - exact Hsrc. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hcpy3 & Heff3 & Hgr3).
jafter_call_keep_hi HS 2048%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat; 1%nat] HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 2%nat (spZ regs)); [exact Usp1 | | exact Hgr3].
    intros a Ha. apply Heff3; [lia | unfold decode_off_win in Hoff; lia | lia].
  - apply (region_kept_aview _ _ _ _ 273%nat TA_g_rx); [rewrite E1lo by lia; exact U273 | | exact Hgr3].
    intros a Ha. apply Heff3; [unfold TA_g_rx in *; lia | |unfold TA_g_rx in *; lia].
    intros X. exact (HnG a ltac:(lia) (ir_inG_row _ _ _ a TMAP_A_g_rx ltac:(unfold TW.SZ_g_rx; lia))). }
specialize (HS3 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
set (E2 := havoc E1 2048 (map (YK11.getr regs3) CLOB)) in HS.
assert (HEJ2 : img_env VAL A_LIM E2) by (apply img_env_havoc_hi; [exact HEJ1 | cbv; lia]).
assert (E2lo : forall n, (n < 2048)%nat -> ew E2 n = ew E1 n) by (intros q Hq; apply ew_havoc_old; exact Hq).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite E2lo by lia; exact Usp1).
assert (SHOK2 : sh_ok segs IR_Bx IR_SH E2 (mrestrict (w_H W2) mem3)) by (unfold sh_ok, IR_SH; apply Forall_nil).
assert (HK3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem3 (spZ regs - IORECV_STK) (spZ regs)
  (iorecv_wr Bw bp cap)).
{ apply (ir_kept_cpy lyc Sc W memc mdc W2 (ms_mem ms) mem3 regs bp cap (TW.g_rx_len Bw) (iorecv_wr Bw bp cap)
    LAWS HAR Hce Hfake HnC).
  - intros a Ha. unfold iorecv_wr. do 4 right. lia.
  - eapply acall_kept_g_weaken; [|exact HKT]. intros a X. exact (ir_eo_wr Bw bp cap a X).
  - intros a Ha H1 H2. apply Heff3; [exact Ha | exact H1 | lia].
  - exact Hgr3. }
set (mT := ms_mem ms) in *. clearbody mT. clear dependent ms.
(* run 8, 0x83550 .. 0x83568: a0 = sext.w n, the reloads, `ret`. *)
paj_run_tok RUN HS HJ3 SHOK2 YC4b.Bspan.
{ ir_awr. }
ir_after2 HS (spZ regs) KR3 GR3.
pose proof (ir_kept_run_w lyc Sc W memc mdc W2 mem3 (ms_mem ms) regs (iorecv_wr Bw bp cap) LAWS HAR Hce HK3 KR3 GR3)
  as HKF.
ir_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
  ltac:(cbn [sv_denot]; rewrite E2lo, E1lo by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
ir_reg HS (Z_to_bv 5 10) (w64 r) RF10
  ltac:(rewrite Hr; refine (ir_sextw E2 (SOff 36 0) (TW.g_rx_len Bw) _); cbn [sv_denot];
        rewrite E2lo, E1lo by lia; rewrite E36, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
assert (HPF : aregs_preserved regs (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) E2 _ ms regs (ir_vals Bw) HS).
  - apply ir_agree2; [intros q Hq; rewrite E2lo, E1lo by lia; reflexivity | reflexivity].
  - vm_compute. reflexivity. }
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
apply (ir_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W W2 memc k regs bp cap Bw Bw' r got ly2 S2 (ms_regs ms)
  (ms_mem ms) _ LAWS Hra HJ3 HPF RF1 Hfr2 Hperm2 HKF HMO2 RF10).
* apply (ir_tw_G (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)) Bw' HTW2). intros a Ha.
  pose proof (inG_G_HARNESS_hull a Ha) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  rewrite (KR3 a ltac:(lia) ltac:(lia)).
  transitivity (aview segs (w_H W2) mT a);
    [exact (Heff3 a ltac:(lia) ltac:(intros X; exact (HnG a ltac:(lia) Ha)) ltac:(lia)) |].
  exact (KR a ltac:(lia) ltac:(lia)).
* rewrite (ir_gfn_keep _ _ HL1 HK1m), (ir_w1_gfn Bw HLB). exact Hgfn.
* apply (ir_X W W2 memc mT mem3 (ms_mem ms) bp cap (TW.g_rx_len Bw) (TW.g_rx Bw - TI.tf_addr f) f r got
    Hbp0 ltac:(lia) Hbpe HnC ltac:(lia) ltac:(lia) Himg Hvis HGf KB).
  -- intros i Hi. replace (TI.tf_addr f + (TW.g_rx Bw - TI.tf_addr f) + i) with (TW.g_rx Bw + i) by lia.
     apply KS. lia.
  -- intros i Hi. replace (TI.tf_addr f + (TW.g_rx Bw - TI.tf_addr f) + i) with (TW.g_rx Bw + i) by lia.
     apply Hcpy3. lia.
  -- intros a Ha. apply Heff3; [lia | lia | unfold decode_off_win in Hoff; lia].
  -- intros a Ha. apply KR3; [lia | unfold decode_off_win in Hoff; lia].
  -- rewrite Hgot, Ebytes. reflexivity.
- (* g_rx_len >= cap: n = cap *)
rewrite (ir_br_ltu E0 36 12 _ cap E36 E12 R36 ltac:(lia)) in Hc.
change (TW.u_at Bw TW.OFF_g_rx_len 8) with (TW.g_rx_len Bw) in Hc. rename Hc into Hge.
(* run 5, 0x83520 .. 0x83524: s1 = cap, `beqz` on n. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ir_awr. }
ir_after KA HS.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
+ (* n = cap = 0: m_tick, then the copy of 0 bytes. *)
rewrite (ir_br_eq64 E0 12 cap E12 ltac:(lia)) in Hc.
apply Z.eqb_eq in Hc. rename Hc into Hn0.
destruct (ir_m_main TF Bw cap Bw' r got cap HLB Hf0 Hrx0 Ht0 ltac:(rewrite Hge; reflexivity) Hm)
  as ([(_ & u & Etk) | (Hnz & _)] & (bytes & _ & Hr & Hgot)); [| exfalso; exact (Hnz Hn0)].
destruct u.
assert (Hr0 : r = 0) by (rewrite Hr, Hn0; reflexivity).
assert (Hg0 : got = []) by (rewrite Hgot, Hr0; reflexivity).
clear Hr Hgot. subst r got.
pose proof (ir_w1_length Bw HLB) as HL1.
pose proof (ir_mtick_keep (iorecv_w1 Bw) HL1 _ _ _ (ir_keep_refl _) Etk) as HK1m.
(* run 6, 0x8353c: `jal m_tick`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ir_awr. }
ir_after KA HS.
pose proof (st_ok_region_nth E0 _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_region_nth E0 _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
cbn [ms_mem restrict] in RG1, RG3.
pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.u_at Bw TW.OFF_g_rx_fail 4) RG1 U272 (or_introl eq_refl)
  ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity)) as VF.
pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.g_rx_times Bw - 1) RG3 U274 (or_introl eq_refl)
  (ir_dec_denot E0 _ E35 R35)) as VT.
assert (Htw1 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) (iorecv_w1 Bw)).
{ apply (ir_tw_times W memc (ms_mem ms) Bw (spZ regs) (TW.g_rx_times Bw - 1) Htw KA ltac:(lia) VT).
  intros a Ha. exact (ir_same4 (w_H W) (w_H W) (ms_mem ms) memc TA_g_rx_fail _ VF VF0 a Ha). }
clear RG1 RG3 VF VT.
pmkst HS.
ir_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 8924)) R1 ltac:(apply codeptr_val; exact HEI).
ir_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 32)) R2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ir_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ir_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = spZ regs - 32)
  by (rewrite R2; apply unsigned_lit_small; lia).
assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 32) by exact ESP. clear ESP.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_m_tick) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HMTK fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) _ k (ms_regs ms) (iorecv_w1 Bw) Bw' HJ).
  - rewrite R1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - change (4096 <= bv_unsigned (YK11.getr (ms_regs ms) (1%bv : bv 5))). rewrite R1, unsigned_lit_small; lia.
  - exact R3.
  - exact R4.
  - rewrite Hsp1. exact Hsp32.
  - rewrite Hsp1. lia.
  - rewrite Hsp1. lia.
  - exact Htw1.
  - exact Etk.
  - rewrite (proj2 iorecv_ev_eq). unfold IORECV_EV in Hev. lia. }
intros W2 c2 HWle HQ.
unfold transport_mtick_post, transport_cg_post in HQ.
destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e & -> & He & HJ2 & HP2 & Hfr2 & Hperm2 & HKc & HMO2 & HTW2).
assert (e = 0) by (rewrite (proj2 iorecv_ev_eq) in He; lia). subst e. rewrite Z.add_0_r in HJ2.
rewrite R1. rewrite Hsp1 in HKc.
(* the running kept fact, merged with m_tick's *)
assert (HKX : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - IORECV_STK) (spZ regs) ir_eo).
{ eapply dk_kept_trans_g with (W1 := W) (memX := ms_mem ms) (slo' := spZ regs - 32 - MTICK_STK)
    (shi' := spZ regs - 32) (Eo' := ir_eo).
  - exact Hce.
  - lia.
  - exact (ir_kept_of_KA lyc Sc W memc mdc (ms_mem ms) regs ir_eo LAWS HAR Hce Hwin (fun a X => or_introl X) KA).
  - eapply acall_kept_g_weaken; [|exact HKc]. intros a X. right. exact (ir_mtick_mrx _ a X).
  - lia.
  - lia.
  - intros a X. exact X. }
(* the state after the call: the frame and g_rx kept *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0%nat; 2%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (ir_region_kept E0 (w_H W) (w_H W2) (ms_mem ms) mem2 2%nat (spZ regs)); [exact Usp | |].
    + intros a Ha. destruct HKc as (K1 & _). apply K1; lia.
    + intros a Ha _. apply (apresent_writable segs). destruct HKc as (_ & _ & _ & _ & K5 & _).
      apply K5; [lia | lia | exact (ir_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a ltac:(lia))].
  - apply (ir_region_kept E0 (w_H W) (w_H W2) (ms_mem ms) mem2 273%nat TA_g_rx); [exact U273 | |].
    + intros a Ha. exact (ir_G_kept _ _ (iorecv_w1 Bw) Bw' a Htw1 HTW2 HK1m
        (ir_inG_row _ _ _ a TMAP_A_g_rx ltac:(unfold TW.SZ_g_rx; lia)) (ir_rx_not_mrx a ltac:(lia))).
    + intros a Ha. lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regs2) CLOB)) in HS.
assert (HEJ1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros q Hq; apply ew_havoc_old; exact Hq).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E1lo by lia; exact Usp).
assert (SHOK1 : sh_ok segs IR_Bx IR_SH E1 (mrestrict (w_H W2) mem2)) by (unfold sh_ok, IR_SH; apply Forall_nil).
clear dependent ms.
(* run 7, 0x83540 .. 0x8354c: the load of g_rx again, a0 = bp, a2 = n = 0, `jal __asan_memcpy`. *)
paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
{ ir_awr. }
ir_after2 HS (spZ regs) KR GR.
pose proof (ir_kept_run_w lyc Sc W memc mdc W2 mem2 (ms_mem ms) regs ir_eo LAWS HAR Hce HKX KR GR) as HKT.
pmkst HS.
ir_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 8940)) R1 ltac:(apply codeptr_val; exact HEJ1).
ir_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 32)) R2 ltac:(cbn [sv_denot]; rewrite Usp1; f_equal; lia).
ir_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ir_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
ir_reg HS (Z_to_bv 5 10) (w64 bp) R10
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ir_reg HS (Z_to_bv 5 11) (w64 (TW.g_rx Bw)) R11
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
ir_reg HS (Z_to_bv 5 12) (w64 0) Q12
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned, Hn0; reflexivity).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = spZ regs - 32)
  by (rewrite R2; apply unsigned_lit_small; lia).
assert (Hsp2 : spZ (ms_regs ms) = spZ regs - 32) by exact ESP. clear ESP.
destruct (ir_dest lyc Sc W memc mdc W2 (ms_mem ms) bp cap 0 regs LAWS HAR Hfake Hrd ltac:(lia) HKT)
  as (Dam & Dra & Dhu & KB).
pose proof (ir_src0 lyc Sc W memc mdc W2 (ms_mem ms) regs (ms_regs ms) TF Bw bp LAWS HAR Htf Hrxin Hrx0') as Hsrc.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OCpy (transport_sigma TS___asan_memcpy)
    (HCPY fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own ly2 S2 _ k
    bp (TW.g_rx Bw) 0 (spZ regs - 32 - sp0) (Z_to_bv 64 (BASE + 8940)) HGX G_HARNESS_rw HJ2 R10 R11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite Hsp2. lia.
  - exact Hm16.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|]. intros a Ha. lia.
  - exact Dam.
  - exact Dra.
  - exact Dhu.
  - exact Hsrc. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hcpy3 & Heff3 & Hgr3).
jafter_call_keep_hi HS 2048%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat; 1%nat] HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 2%nat (spZ regs)); [exact Usp1 | | exact Hgr3].
    intros a Ha. apply Heff3; [lia | lia | lia].
  - apply (region_kept_aview _ _ _ _ 273%nat TA_g_rx); [rewrite E1lo by lia; exact U273 | | exact Hgr3].
    intros a Ha. apply Heff3; [unfold TA_g_rx in *; lia | lia | unfold TA_g_rx in *; lia]. }
specialize (HS3 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
set (E2 := havoc E1 2048 (map (YK11.getr regs3) CLOB)) in HS.
assert (HEJ2 : img_env VAL A_LIM E2) by (apply img_env_havoc_hi; [exact HEJ1 | cbv; lia]).
assert (E2lo : forall n, (n < 2048)%nat -> ew E2 n = ew E1 n) by (intros q Hq; apply ew_havoc_old; exact Hq).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite E2lo by lia; exact Usp1).
assert (SHOK2 : sh_ok segs IR_Bx IR_SH E2 (mrestrict (w_H W2) mem3)) by (unfold sh_ok, IR_SH; apply Forall_nil).
assert (HK3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem3 (spZ regs - IORECV_STK) (spZ regs)
  (iorecv_wr Bw bp cap)).
{ apply (ir_kept_cpy lyc Sc W memc mdc W2 (ms_mem ms) mem3 regs bp cap 0 (iorecv_wr Bw bp cap)
    LAWS HAR Hce Hfake ltac:(lia)).
  - intros a Ha. lia.
  - eapply acall_kept_g_weaken; [|exact HKT]. intros a X. exact (ir_eo_wr Bw bp cap a X).
  - intros a Ha H1 H2. apply Heff3; [exact Ha | exact H1 | lia].
  - exact Hgr3. }
set (mT := ms_mem ms) in *. clearbody mT. clear dependent ms.
(* run 8, 0x83550 .. 0x83568: a0 = sext.w 0, the reloads, `ret`. *)
paj_run_tok RUN HS HJ3 SHOK2 YC4b.Bspan.
{ ir_awr. }
ir_after2 HS (spZ regs) KR3 GR3.
pose proof (ir_kept_run_w lyc Sc W memc mdc W2 mem3 (ms_mem ms) regs (iorecv_wr Bw bp cap) LAWS HAR Hce HK3 KR3 GR3)
  as HKF.
ir_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
  ltac:(cbn [sv_denot]; rewrite E2lo, E1lo by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
ir_reg HS (Z_to_bv 5 10) (w64 0) RF10
  ltac:(refine (eq_trans (ir_sextw E2 (SOff 12 0) 0 _) _);
        [cbn [sv_denot]; rewrite E2lo, E1lo by lia; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned, Hn0; reflexivity
        | reflexivity]).
assert (HPF : aregs_preserved regs (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) E2 _ ms regs (ir_vals Bw) HS).
  - apply ir_agree2; [intros q Hq; rewrite E2lo, E1lo by lia; reflexivity | reflexivity].
  - vm_compute. reflexivity. }
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
apply (ir_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W W2 memc k regs bp cap Bw Bw' 0 [] ly2 S2 (ms_regs ms)
  (ms_mem ms) _ LAWS Hra HJ3 HPF RF1 Hfr2 Hperm2 HKF HMO2 RF10).
* apply (ir_tw_G (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)) Bw' HTW2). intros a Ha.
  pose proof (inG_G_HARNESS_hull a Ha) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  rewrite (KR3 a ltac:(lia) ltac:(lia)).
  transitivity (aview segs (w_H W2) mT a); [exact (Heff3 a ltac:(lia) ltac:(lia) ltac:(lia)) |].
  exact (KR a ltac:(lia) ltac:(lia)).
* rewrite (ir_gfn_keep _ _ HL1 HK1m), (ir_w1_gfn Bw HLB). exact Hgfn.
* apply (ir_buf_X W2 (ms_mem ms) bp cap [] Hbp0 ltac:(lia) Hbpe Himg).
  -- intros a Ha. unfold decode_off_win in Hoff.
     exact (ir_vis_chain _ _ _ _ (Hvis a Ha) (KR3 a ltac:(lia) ltac:(lia))
       (Heff3 a ltac:(lia) ltac:(lia) ltac:(lia)) (KB a Ha)).
  -- cbn [length]. lia.
  -- apply garr8_nil.
+ (* n = cap <> 0: m_rx (g_rx, cap), then the copy of cap bytes from TF. *)
rewrite (ir_br_eq64 E0 12 cap E12 ltac:(lia)) in Hc.
apply Z.eqb_neq in Hc. rename Hc into Hn0.
destruct (ir_m_main TF Bw cap Bw' r got cap HLB Hf0 Hrx0 Ht0 ltac:(rewrite Hge; reflexivity) Hm)
  as ([(Hz & _) | (_ & rr & Erx)] & (bytes & Hrd' & Hr & Hgot)); [exfalso; exact (Hn0 Hz) |].
assert (HnC : 0 <= cap <= cap) by lia.
pose proof (ir_w1_length Bw HLB) as HL1.
pose proof (ir_mrx_keep (iorecv_w1 Bw) HL1 _ _ _ _ _ _ (ir_keep_refl _) Erx) as HK1m.
assert (Hgrx : TW.g_rx Bw' = TW.g_rx Bw) by (rewrite (ir_grx_keep _ _ HL1 HK1m); exact (ir_w1_rx Bw HLB)).
rewrite Hgrx in Hrd'.
destruct (ir_frame_read_some TF (TW.g_rx Bw) cap bytes Hrd' Hn0) as (f & -> & Of0 & _ & Ofn & Ebytes).
destruct (TC.frame_from (Some f) (TW.g_rx Bw)) as [fr|] eqn:Efr;
  [| try rewrite Efr in Erx; unfold TC.m_rx_m in Erx; discriminate Erx].
try rewrite Efr in Erx.
destruct (ir_frame_from_some _ _ _ Efr) as (f' & Ef' & _ & Efr').
assert (f' = f) by congruence. subst f'. subst fr.
pose proof Htf as Htf'. unfold trans_tframe_at in Htf'. destruct Htf' as (Ha0 & HGf & Hsf & Hwf).
pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc _ _ HAR Hsf ltac:(lia)) as (_ & _ & _ & _ & Htf0 & Htf63).
(* run 6, 0x83528 .. 0x8352c: a1 = n, `jal m_rx`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ir_awr. }
ir_after KA HS.
pose proof (st_ok_region_nth E0 _ (restrict (w_H W) ms) 1 _ HS eq_refl) as RG1.
pose proof (st_ok_region_nth E0 _ (restrict (w_H W) ms) 3 _ HS eq_refl) as RG3.
cbn [ms_mem restrict] in RG1, RG3.
pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.u_at Bw TW.OFF_g_rx_fail 4) RG1 U272 (or_introl eq_refl)
  ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity)) as VF.
pose proof (ir_rd4 E0 _ _ _ _ _ _ _ _ _ (TW.g_rx_times Bw - 1) RG3 U274 (or_introl eq_refl)
  (ir_dec_denot E0 _ E35 R35)) as VT.
assert (Htw1 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) (iorecv_w1 Bw)).
{ apply (ir_tw_times W memc (ms_mem ms) Bw (spZ regs) (TW.g_rx_times Bw - 1) Htw KA ltac:(lia) VT).
  intros a Ha. exact (ir_same4 (w_H W) (w_H W) (ms_mem ms) memc TA_g_rx_fail _ VF VF0 a Ha). }
clear RG1 RG3 VF VT.
pmkst HS.
ir_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 8908)) R1 ltac:(apply codeptr_val; exact HEI).
ir_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 32)) R2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ir_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ir_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
ir_reg HS (Z_to_bv 5 10) (w64 (TW.g_rx Bw)) R10
  ltac:(cbn [sv_denot]; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
ir_reg HS (Z_to_bv 5 11) (w64 cap) R11
  ltac:(cbn [sv_denot]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = spZ regs - 32)
  by (rewrite R2; apply unsigned_lit_small; lia).
assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 32) by exact ESP. clear ESP.
pose proof (ir_tframe_rx lyc Sc W memc mdc (ms_mem ms) regs (ms_regs ms) f (TW.g_rx Bw) Bw bp cap LAWS HAR Htf Hapart
  KA ltac:(lia) ltac:(lia) ltac:(lia) Hsp1) as HTF1.
assert (Hrom1 : trans_rom_view_rd W (ms_mem ms)).
{ intros a Ha. pose proof KA as [KA1 _]. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  rewrite (KA1 a ltac:(lia) ltac:(lia) ltac:(unfold ir_gw, TA_g_rx_fail, TA_g_rx_times; lia)). exact (Hrom a Ha). }
assert (Happ : mrx_apart (TI.TFrame (TW.g_rx Bw) (skipn (Z.to_nat (TW.g_rx Bw - TI.tf_addr f)) (TI.tf_bytes f)))).
{ intros x Hx. cbn [TI.tf_addr TI.tf_bytes]. rewrite length_skipn. intros Hin.
  apply (Hapart x (or_intror (or_intror (or_introl Hx))) f eq_refl). lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_m_rx) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HMRX fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) _ k (ms_regs ms)
    (TI.TFrame (TW.g_rx Bw) (skipn (Z.to_nat (TW.g_rx Bw - TI.tf_addr f)) (TI.tf_bytes f))) cap rr
    (iorecv_w1 Bw) Bw' HJ).
  - rewrite R1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - change (4096 <= bv_unsigned (YK11.getr (ms_regs ms) (1%bv : bv 5))). rewrite R1, unsigned_lit_small; lia.
  - exact R3.
  - exact R4.
  - exact R10.
  - exact R11.
  - rewrite Hsp1. exact Hsp32.
  - rewrite Hsp1. lia.
  - rewrite Hsp1. lia.
  - exact HTF1.
  - cbn [TI.tf_addr]. lia.
  - exact Happ.
  - exact Hrom1.
  - exact Htw1.
  - exact Erx.
  - rewrite (proj1 iorecv_ev_eq). unfold IORECV_EV in Hev. lia. }
intros W2 c2 HWle HQ.
unfold transport_mrx_post, transport_cg_post in HQ.
destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e & -> & He & HJ2 & HP2 & Hfr2 & Hperm2 & HKc & HMO2 & _ & HTW2).
assert (e = 0) by (rewrite (proj1 iorecv_ev_eq) in He; lia). subst e. rewrite Z.add_0_r in HJ2.
rewrite R1. rewrite Hsp1 in HKc.
destruct (ir_ly_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (FA2 & SL2 & SH2).
assert (HFA : forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos)
  by (intros cid pos; rewrite FA2, FAc; reflexivity).
assert (HSL : ly_stk_lo ly2 = ly_stk_lo lyc) by lia. assert (HSH : ly_stk_hi ly2 = ly_stk_hi lyc) by lia.
(* the running kept fact, merged with m_rx's *)
assert (HKX : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - IORECV_STK) (spZ regs) ir_eo).
{ eapply dk_kept_trans_g with (W1 := W) (memX := ms_mem ms) (slo' := spZ regs - 32 - MRX_STK)
    (shi' := spZ regs - 32) (Eo' := ir_eo).
  - exact Hce.
  - lia.
  - exact (ir_kept_of_KA lyc Sc W memc mdc (ms_mem ms) regs ir_eo LAWS HAR Hce Hwin (fun a X => or_introl X) KA).
  - eapply acall_kept_g_weaken; [|exact HKc]. intros a X. right. exact X.
  - lia.
  - lia.
  - intros a X. exact X. }
(* the state after the call: the frame and g_rx kept *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0%nat; 2%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (ir_region_kept E0 (w_H W) (w_H W2) (ms_mem ms) mem2 2%nat (spZ regs)); [exact Usp | |].
    + intros a Ha. destruct HKc as (K1 & _). apply K1; lia.
    + intros a Ha _. apply (apresent_writable segs). destruct HKc as (_ & _ & _ & _ & K5 & _).
      apply K5; [lia | lia | exact (ir_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a ltac:(lia))].
  - apply (ir_region_kept E0 (w_H W) (w_H W2) (ms_mem ms) mem2 273%nat TA_g_rx); [exact U273 | |].
    + intros a Ha. exact (ir_G_kept _ _ (iorecv_w1 Bw) Bw' a Htw1 HTW2 HK1m
        (ir_inG_row _ _ _ a TMAP_A_g_rx ltac:(unfold TW.SZ_g_rx; lia)) (ir_rx_not_mrx a ltac:(lia))).
    + intros a Ha. lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regs2) CLOB)) in HS.
assert (HEJ1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros q Hq; apply ew_havoc_old; exact Hq).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E1lo by lia; exact Usp).
assert (SHOK1 : sh_ok segs IR_Bx IR_SH E1 (mrestrict (w_H W2) mem2)) by (unfold sh_ok, IR_SH; apply Forall_nil).
clear dependent ms.
(* run 7, 0x83530 .. 0x8354c: `j`, the load of g_rx again, a0 = bp, a2 = n, `jal __asan_memcpy`. *)
paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
{ ir_awr. }
ir_after2 HS (spZ regs) KR GR.
pose proof (ir_kept_run_w lyc Sc W memc mdc W2 mem2 (ms_mem ms) regs ir_eo LAWS HAR Hce HKX KR GR) as HKT.
pmkst HS.
ir_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 8940)) R1 ltac:(apply codeptr_val; exact HEJ1).
ir_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 32)) R2 ltac:(cbn [sv_denot]; rewrite Usp1; f_equal; lia).
ir_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ir_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
ir_reg HS (Z_to_bv 5 10) (w64 bp) R10
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ir_reg HS (Z_to_bv 5 11) (w64 (TW.g_rx Bw)) R11
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
ir_reg HS (Z_to_bv 5 12) (w64 cap) Q12
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = spZ regs - 32)
  by (rewrite R2; apply unsigned_lit_small; lia).
assert (Hsp2 : spZ (ms_regs ms) = spZ regs - 32) by exact ESP. clear ESP.
destruct (ir_dest lyc Sc W memc mdc W2 (ms_mem ms) bp cap cap regs LAWS HAR Hfake Hrd HnC HKT)
  as (Dam & Dra & Dhu & KB).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HART.
destruct (ir_src lyc Sc W memc mdc ly2 S2 W2 (ms_mem ms) _ regs (ms_regs ms) f (TW.g_rx Bw) cap bp cap Bw
  LAWS HROU HRNE HAR HART Hperm2 Hfr2 HFA HSL HSH HKT Htf Hoffg Hapart ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  Hsp2) as (Hsrc & KS).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OCpy (transport_sigma TS___asan_memcpy)
    (HCPY fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own ly2 S2 _ k
    bp (TW.g_rx Bw) cap (spZ regs - 32 - sp0) (Z_to_bv 64 (BASE + 8940)) HGX G_HARNESS_rw HJ2 R10 R11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite Hsp2. lia.
  - exact Hm16.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|].
    intros a Ha. left. destruct (Htwr a ltac:(lia)) as [(Hw & _ & _ & _) | HGa]; [| exfalso; exact (HnG a ltac:(lia) HGa)].
    split; [exact (ir_awr_move STK sp0 FP _ lyc Sc ly2 S2 own a Hw Hperm2 HFA) |].
    rewrite Hsp2. unfold decode_off_win in Hoff. lia.
  - exact Dam.
  - exact Dra.
  - exact Dhu.
  - exact Hsrc. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hcpy3 & Heff3 & Hgr3).
jafter_call_keep_hi HS 2048%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat; 1%nat] HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 2%nat (spZ regs)); [exact Usp1 | | exact Hgr3].
    intros a Ha. apply Heff3; [lia | unfold decode_off_win in Hoff; lia | lia].
  - apply (region_kept_aview _ _ _ _ 273%nat TA_g_rx); [rewrite E1lo by lia; exact U273 | | exact Hgr3].
    intros a Ha. apply Heff3; [unfold TA_g_rx in *; lia | |unfold TA_g_rx in *; lia].
    intros X. exact (HnG a ltac:(lia) (ir_inG_row _ _ _ a TMAP_A_g_rx ltac:(unfold TW.SZ_g_rx; lia))). }
specialize (HS3 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
set (E2 := havoc E1 2048 (map (YK11.getr regs3) CLOB)) in HS.
assert (HEJ2 : img_env VAL A_LIM E2) by (apply img_env_havoc_hi; [exact HEJ1 | cbv; lia]).
assert (E2lo : forall n, (n < 2048)%nat -> ew E2 n = ew E1 n) by (intros q Hq; apply ew_havoc_old; exact Hq).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite E2lo by lia; exact Usp1).
assert (SHOK2 : sh_ok segs IR_Bx IR_SH E2 (mrestrict (w_H W2) mem3)) by (unfold sh_ok, IR_SH; apply Forall_nil).
assert (HK3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem3 (spZ regs - IORECV_STK) (spZ regs)
  (iorecv_wr Bw bp cap)).
{ apply (ir_kept_cpy lyc Sc W memc mdc W2 (ms_mem ms) mem3 regs bp cap cap (iorecv_wr Bw bp cap)
    LAWS HAR Hce Hfake HnC).
  - intros a Ha. unfold iorecv_wr. do 4 right. lia.
  - eapply acall_kept_g_weaken; [|exact HKT]. intros a X. exact (ir_eo_wr Bw bp cap a X).
  - intros a Ha H1 H2. apply Heff3; [exact Ha | exact H1 | lia].
  - exact Hgr3. }
set (mT := ms_mem ms) in *. clearbody mT. clear dependent ms.
(* run 8, 0x83550 .. 0x83568: a0 = sext.w n, the reloads, `ret`. *)
paj_run_tok RUN HS HJ3 SHOK2 YC4b.Bspan.
{ ir_awr. }
ir_after2 HS (spZ regs) KR3 GR3.
pose proof (ir_kept_run_w lyc Sc W memc mdc W2 mem3 (ms_mem ms) regs (iorecv_wr Bw bp cap) LAWS HAR Hce HK3 KR3 GR3)
  as HKF.
ir_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
  ltac:(cbn [sv_denot]; rewrite E2lo, E1lo by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
ir_reg HS (Z_to_bv 5 10) (w64 r) RF10
  ltac:(rewrite Hr; refine (ir_sextw E2 (SOff 12 0) cap _); cbn [sv_denot];
        rewrite E2lo, E1lo by lia; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HPF : aregs_preserved regs (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) E2 _ ms regs (ir_vals Bw) HS).
  - apply ir_agree2; [intros q Hq; rewrite E2lo, E1lo by lia; reflexivity | reflexivity].
  - vm_compute. reflexivity. }
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
apply (ir_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W W2 memc k regs bp cap Bw Bw' r got ly2 S2 (ms_regs ms)
  (ms_mem ms) _ LAWS Hra HJ3 HPF RF1 Hfr2 Hperm2 HKF HMO2 RF10).
* apply (ir_tw_G (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)) Bw' HTW2). intros a Ha.
  pose proof (inG_G_HARNESS_hull a Ha) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  rewrite (KR3 a ltac:(lia) ltac:(lia)).
  transitivity (aview segs (w_H W2) mT a);
    [exact (Heff3 a ltac:(lia) ltac:(intros X; exact (HnG a ltac:(lia) Ha)) ltac:(lia)) |].
  exact (KR a ltac:(lia) ltac:(lia)).
* rewrite (ir_gfn_keep _ _ HL1 HK1m), (ir_w1_gfn Bw HLB). exact Hgfn.
* apply (ir_X W W2 memc mT mem3 (ms_mem ms) bp cap cap (TW.g_rx Bw - TI.tf_addr f) f r got
    Hbp0 ltac:(lia) Hbpe HnC ltac:(lia) ltac:(lia) Himg Hvis HGf KB).
  -- intros i Hi. replace (TI.tf_addr f + (TW.g_rx Bw - TI.tf_addr f) + i) with (TW.g_rx Bw + i) by lia.
     apply KS. lia.
  -- intros i Hi. replace (TI.tf_addr f + (TW.g_rx Bw - TI.tf_addr f) + i) with (TW.g_rx Bw + i) by lia.
     apply Hcpy3. lia.
  -- intros a Ha. lia.
  -- intros a Ha. apply KR3; [lia | unfold decode_off_win in Hoff; lia].
  -- rewrite Hgot, Ebytes. reflexivity.
Qed.

End irw.

(* The statement of lib/A/Prog/io_recv_cg.v. *)
Theorem transport_io_recv_cg_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  @transport_io_recv_cg_holds_stmt fx rc B MT.
Proof. exact (@ir_holds fx rc B MT). Qed.
Print Assumptions transport_io_recv_cg_holds.
