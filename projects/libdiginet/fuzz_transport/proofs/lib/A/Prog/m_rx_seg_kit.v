(* m_rx_seg_kit: the shared pieces of the image-A walk of m_rx (statement lib/A/Prog/m_rx_cg.v, entry 0x8488c =
   transport_sigma TS_m_rx, 1716 bytes, frame 144), split in segments m_rx_seg_*.v and closed in m_rx_cgW.v.

   The walk holds an INNER G journal, started at m_rx's entry (sp1 = the entry sp, window MRX_STK, no footprint, no
   frame of its own, start state the call state lyc Sc W memc mdc):
     ajournal_gx G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc mem2 md2 0.
   Every run of a segment and every callee runs against it (the callees take it as their caller's journal). The top
   file composes it with the caller's journal (W_journalG.v ajournal_gx_sub) and reads acall_kept_g off it
   (mrx_kept_g_of_inner).

   A segment starts at a CUT: a pc inside m_rx and the facts mrx_at gives there, and ends at other cuts, whose
   continuations (mrx_K) are its premises, or at the return (mrx_ipost). The cuts (pc = 0x8488c + offset):
     EPI  0x8496c  the epilogue, a0 = r, the world is the model's last world;
     TICK 0x84e1c  `jal m_tick`, then a0 = 1 and the epilogue;
     MO   0x84e18  `jal m_maybe_online`, then TICK;          WAKE 0x84e00  `jal m_wake`, then TICK;
     LOST 0x84c80  `jal m_lost` (a0 = why), then TICK;
     E0L  0x84de8  `jal m_lost` (a0 = 3, cmd e0), then E0W;   E0W  0x84dec  M.state reloaded, auto_wake, m_wake;
     MAC  0x84abc  the frame's header read, before the three MAC compares;
     DESK 0x84b08  the desk test;   BODY 0x84b70  the S_CLOSED test, M.last_rx, the switch;
     HOST 0x84bbc  host_offset (cmd e1);   ANNT 0x84da8  the announce tail (desk_named, e0 / e1);
     DATA 0x84c88  cmd DATA.
   The cuts before the first G-form callee (MAC .. DATA) are at the call state itself (ly2 = lyc, S2 = Sc) and
   carry the frame's bytes, their shadow facts and the read-only view (mrx_frs). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP0m YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportImg TransportGRwA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  m_lost_cg m_wake_cg m_maybe_online_cg m_tick_cg desk_named_cg check_state_data_cg m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- the cut pcs ---- *)
Definition MRX_PC (off : Z) : Z := transport_sigma TS_m_rx + off.
Definition OFF_EPI : Z := 0xe0.
Definition OFF_MAC : Z := 0x230.
Definition OFF_DESK : Z := 0x27c.
Definition OFF_BODY : Z := 0x2e4.
Definition OFF_HOST : Z := 0x330.
Definition OFF_LOST : Z := 0x3f4.
Definition OFF_DATA : Z := 0x3fc.
Definition OFF_ANNT : Z := 0x51c.
Definition OFF_E0L : Z := 0x55c.
Definition OFF_E0W : Z := 0x560.
Definition OFF_WAKE : Z := 0x574.
Definition OFF_MO : Z := 0x58c.
Definition OFF_TICK : Z := 0x590.
Lemma mrx_pc_val : transport_sigma TS_m_rx = 0x8488c.
Proof. reflexivity. Qed.

(* The 13 registers the prologue saves (0x84890 - 0x848c0), with their offsets from sp1 - 144: ra at 136, s0 .. s11
   at 128 .. 40. The epilogue (0x8496c - 0x8499c) loads them back. *)
Definition MRX_SAVES : list (Z * Z) :=
  [(1, 136); (8, 128); (9, 120); (18, 112); (19, 104); (20, 96); (21, 88); (22, 80); (23, 72); (24, 64);
   (25, 56); (26, 48); (27, 40)].

(* A frame byte of the received frame, as the model reads it (DgnSpec.v byte_at of zs). *)
Definition mfb (fr : TI.tframe) (k : Z) : Z := DSpec.byte_at (TW.zs (TI.tf_bytes fr)) k.
Definition mlen (fr : TI.tframe) : Z := Z.of_nat (length (TI.tf_bytes fr)).

(* The header facts spec_read_frame's SPEC_OK case gives (DgnSpec.v :243-250): 30 <= n <= length, the ethertype,
   16 <= numbytes <= n - 14. *)
Definition mrx_hdr (fr : TI.tframe) (n : Z) : Prop :=
  30 <= n <= mlen fr /\
  DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 12 = DSpec.SPEC_ETHERTYPE /\
  16 <= DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 14 <= n - 14.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The 13 saved slots hold the entry registers. *)
Definition mrx_saved (Wc : world segs) (mem : word -> option byte) (sp1 : Z) (regs0 : bvmap 5 word) : Prop :=
  Forall (fun ro => rdword (aview segs (w_H Wc) mem) (sp1 - MRX_FRAME + snd ro) =
                    Some (bv_unsigned (YK11.getr regs0 (Z_to_bv 5 (fst ro))))) MRX_SAVES.

(* What the return leaves, at the inner journal: the inner journal at the return, the callee-saved registers of the
   entry, the side-stack frames and blocks of the call state, no meter charge, a0 = r and the world relation at the
   model's world Bw'. *)
Definition mrx_ipost (sp1 : Z) (regs0 : bvmap 5 word) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (mdc : Model) (Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs0 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal_gx TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 0 /\
    aregs_preserved regs0 regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ mo_le MT Sc S2 0 /\
    YK11.getr regs2 10 = w64 r /\ tw_at TMAP_A (aview segs (w_H W2) mem2) Bw'.

(* A cut: the machine at pc with the inner journal at (ly2, S2), the common facts, and the cut's own facts R (of the
   current world Wc, the model's world Bwc, the state, the registers and the memory). *)
Definition mrx_at (sp1 : Z) (regs0 : bvmap 5 word) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (mdc : Model) (pc : Z)
    (R : world segs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop)
    (Wc : world segs) (Bwc : list byte) (c : config) : Prop :=
  exists ly2 S2 regs2 mem2 md2,
    c = mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 pc) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal_gx TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc mem2 md2 0 /\
    frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ mo_le MT Sc S2 0 /\
    YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) /\
    YK11.getr regs2 3 = YK11.getr regs0 3 /\ YK11.getr regs2 4 = YK11.getr regs0 4 /\
    mrx_saved Wc mem2 sp1 regs0 /\
    tw_at TMAP_A (aview segs (w_H Wc) mem2) Bwc /\
    R Wc Bwc ly2 S2 regs2 mem2.

(* The continuation of a cut: from every machine the cut describes, the run reaches the return. *)
Definition mrx_K (sp1 : Z) (regs0 : bvmap 5 word) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (mdc : Model) (Bw' : list byte) (r : Z) (pc : Z)
    (R : world segs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
  forall Wc Bwc c, mrx_at sp1 regs0 lyc Sc W memc mdc pc R Wc Bwc c ->
    SRr segs Wc c (mrx_ipost sp1 regs0 lyc Sc W memc mdc Bw' r).

(* The frame's bytes, their placement facts at the current memory and the read-only view (the cuts before the first
   G-form callee). *)
Definition mrx_frs (fr : TI.tframe) (Wc : world segs) (mem : word -> option byte) : Prop :=
  garr8 segs (mrestrict (w_H Wc) mem) (TI.tf_addr fr) (map DSpec.bz (TI.tf_bytes fr)) /\
  decode_rd_ok Wc mem (TI.tf_addr fr) (mlen fr) /\
  trans_rom_view_rd Wc mem.

(* An 8-byte stack slot at sp1 - 144 + o holding the frame byte k (the spills at 0x84a94 - 0x84a9c and 0x84b08). *)
Definition mrx_spill (Wc : world segs) (mem : word -> option byte) (sp1 o : Z) (fr : TI.tframe) (k : Z) : Prop :=
  rdword (aview segs (w_H Wc) mem) (sp1 - MRX_FRAME + o) = Some (mfb fr k).

(* ---- the cuts' own facts ---- *)

(* EPI: the epilogue with a0 = r at the model's last world. *)
Definition R_EPI (Bw' : list byte) (r : Z) : world segs -> list byte -> alayout -> astate -> bvmap 5 word ->
    (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 => Bwc = Bw' /\ YK11.getr regs2 10 = w64 r.

(* TICK: m_tick from Bwc gives Bw'; the result is 1. *)
Definition R_TICK (Bw' : list byte) (r : Z) : world segs -> list byte -> alayout -> astate -> bvmap 5 word ->
    (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 => TC.m_tick_m Bwc = Some (Bw', tt) /\ r = 1.

(* MO: m_maybe_online, then m_tick. *)
Definition R_MO (Bw' : list byte) (r : Z) : world segs -> list byte -> alayout -> astate -> bvmap 5 word ->
    (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists B3,
    TC.m_maybe_online_m Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* WAKE: m_wake (its result ignored), then m_tick. *)
Definition R_WAKE (Bw' : list byte) (r : Z) : world segs -> list byte -> alayout -> astate -> bvmap 5 word ->
    (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists B3 rw,
    TC.m_wake_m Bwc = Some (B3, rw) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* LOST: a0 = why, m_lost why, then m_tick. *)
Definition R_LOST (Bw' : list byte) (r : Z) : world segs -> list byte -> alayout -> astate -> bvmap 5 word ->
    (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists why B3,
    YK11.getr regs2 10 = w64 why /\ - 2 ^ 31 <= why < 2 ^ 31 /\
    TC.m_lost_m Bwc why = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* E0W (cmd e0, after its m_lost): s3 = &M; mrx_e0w, then m_tick. *)
Definition R_E0W (Bw' : list byte) (r : Z) : world segs -> list byte -> alayout -> astate -> bvmap 5 word ->
    (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists B3,
    YK11.getr regs2 19 = w64 TA_M /\
    EPI.mrx_e0w Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* E0L (cmd e0, M.state was S_ONLINE): s3 = &M, a0 = 3 (R_DESK_OFFLINE); m_lost 3, mrx_e0w, then m_tick. *)
Definition R_E0L (Bw' : list byte) (r : Z) : world segs -> list byte -> alayout -> astate -> bvmap 5 word ->
    (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists B6 B3,
    YK11.getr regs2 19 = w64 TA_M /\ YK11.getr regs2 10 = w64 3 /\
    TC.m_lost_m Bwc 3 = Some (B6, tt) /\ EPI.mrx_e0w B6 = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\
    r = 1.

(* The registers every cut from MAC on carries (the header bytes the code keeps): s0 = fa (MAC, DESK, BODY), s2 = the
   shadow base, s4 = numbytes, s5 = byte 20, s6 = byte 22, s7 = byte 26, s8 = byte 27, s9 = cmd (byte 28),
   s10 = byte 23, s11 = byte 19; the spills: sp + 16 = byte 25, sp + 24 = byte 24, sp + 32 = byte 21. *)
Definition mrx_hregs (fr : TI.tframe) (Wc : world segs) (sp1 : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
  YK11.getr regs2 18 = w64 SHADOW_OFF /\
  YK11.getr regs2 21 = w64 (mfb fr 20) /\ YK11.getr regs2 22 = w64 (mfb fr 22) /\
  YK11.getr regs2 23 = w64 (mfb fr 26) /\ YK11.getr regs2 24 = w64 (mfb fr 27) /\
  YK11.getr regs2 25 = w64 (mfb fr 28) /\ YK11.getr regs2 26 = w64 (mfb fr 23) /\
  YK11.getr regs2 27 = w64 (mfb fr 19) /\
  mrx_spill Wc mem2 sp1 16 fr 25 /\ mrx_spill Wc mem2 sp1 24 fr 24 /\ mrx_spill Wc mem2 sp1 32 fr 21.

(* MAC: the header read (s0 = fa, s3 = byte 18, s4 = numbytes); the model from mrx_top. *)
Definition R_MAC (fr : TI.tframe) (n : Z) (sp1 : Z) (lyc : alayout) (Sc : astate) (Bw' : list byte) (r : Z) :
    world segs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    ly2 = lyc /\ S2 = Sc /\ mrx_frs fr Wc mem2 /\ mrx_hdr fr n /\
    YK11.getr regs2 8 = w64 (TI.tf_addr fr) /\ YK11.getr regs2 19 = w64 (mfb fr 18) /\
    YK11.getr regs2 20 = w64 (DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 14) /\
    mrx_hregs fr Wc sp1 regs2 mem2 /\
    EPI.mrx_top timg_A fr Bwc = Some (Bw', r).

(* DESK: as MAC, and s1 = fa + 6 (the source MAC); the model from mrx_desk_m. *)
Definition R_DESK (fr : TI.tframe) (n : Z) (sp1 : Z) (lyc : alayout) (Sc : astate) (Bw' : list byte) (r : Z) :
    world segs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    ly2 = lyc /\ S2 = Sc /\ mrx_frs fr Wc mem2 /\ mrx_hdr fr n /\
    YK11.getr regs2 8 = w64 (TI.tf_addr fr) /\ YK11.getr regs2 9 = w64 (TI.tf_addr fr + 6) /\
    YK11.getr regs2 19 = w64 (mfb fr 18) /\
    YK11.getr regs2 20 = w64 (DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 14) /\
    mrx_hregs fr Wc sp1 regs2 mem2 /\
    EPI.mrx_desk_m timg_A fr Bwc = Some (Bw', r).

(* BODY: as DESK with s3 = &M and byte 18 spilled at sp + 8; the model from mrx_k. *)
Definition R_BODY (fr : TI.tframe) (n : Z) (sp1 : Z) (lyc : alayout) (Sc : astate) (Bw' : list byte) (r : Z) :
    world segs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    ly2 = lyc /\ S2 = Sc /\ mrx_frs fr Wc mem2 /\ mrx_hdr fr n /\
    YK11.getr regs2 8 = w64 (TI.tf_addr fr) /\ YK11.getr regs2 9 = w64 (TI.tf_addr fr + 6) /\
    YK11.getr regs2 19 = w64 TA_M /\
    YK11.getr regs2 20 = w64 (DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 14) /\
    mrx_hregs fr Wc sp1 regs2 mem2 /\ mrx_spill Wc mem2 sp1 8 fr 18 /\
    EPI.mrx_k timg_A fr Bwc = Some (Bw', r).

(* DATA (cmd 0, after M.last_rx): a0 = g_now, s0 = fa + 30, s3 = &M, s4 = body_len; the model from mrx_data, then
   m_tick. *)
Definition R_DATA (fr : TI.tframe) (n : Z) (sp1 : Z) (lyc : alayout) (Sc : astate) (Bw' : list byte) (r : Z) :
    world segs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    ly2 = lyc /\ S2 = Sc /\ mrx_frs fr Wc mem2 /\ mrx_hdr fr n /\ mfb fr 28 = 0 /\
    YK11.getr regs2 10 = w64 (TW.g_now Bwc) /\
    YK11.getr regs2 8 = w64 (TI.tf_addr fr + 30) /\ YK11.getr regs2 19 = w64 TA_M /\
    YK11.getr regs2 20 = w64 (EPI.mrx_blen fr) /\
    mrx_hregs fr Wc sp1 regs2 mem2 /\ mrx_spill Wc mem2 sp1 8 fr 18 /\
    exists B3, EPI.mrx_data fr Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* HOST (cmd e1, body_len >= 33, after M.last_rx): s0 = fa + 30, s3 = &M, s4 = -1, s7 = M.state; the model from
   mrx_ann, then m_tick. *)
Definition R_HOST (fr : TI.tframe) (n : Z) (sp1 : Z) (lyc : alayout) (Sc : astate) (Bw' : list byte) (r : Z) :
    world segs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    ly2 = lyc /\ S2 = Sc /\ mrx_frs fr Wc mem2 /\ mrx_hdr fr n /\
    mfb fr 28 = TC.SPEC_CMD_E1 /\ TC.SPEC_ANN_MIN <= EPI.mrx_blen fr /\
    YK11.getr regs2 8 = w64 (TI.tf_addr fr + 30) /\ YK11.getr regs2 19 = w64 TA_M /\
    YK11.getr regs2 20 = w64 (-1) /\ YK11.getr regs2 23 = w64 (TW.M_state Bwc) /\
    YK11.getr regs2 25 = w64 (mfb fr 28) /\
    exists B3, EPI.mrx_ann timg_A fr Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* ANNT (cmd e0 / e1, body_len >= 33, after host_offset gave off): s0 = fa + 30, s3 = &M, s4 = off, s7 = M.state,
   s9 = cmd; the model from mrx_ann_tail off, then m_tick. *)
Definition R_ANNT (fr : TI.tframe) (n : Z) (sp1 : Z) (lyc : alayout) (Sc : astate) (Bw' : list byte) (r : Z) :
    world segs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists off,
    ly2 = lyc /\ S2 = Sc /\ mrx_frs fr Wc mem2 /\ mrx_hdr fr n /\
    (mfb fr 28 = TC.SPEC_CMD_E0 \/ mfb fr 28 = TC.SPEC_CMD_E1) /\ TC.SPEC_ANN_MIN <= EPI.mrx_blen fr /\
    -1 <= off <= 9 /\ (mfb fr 28 = TC.SPEC_CMD_E0 -> off = -1) /\
    YK11.getr regs2 8 = w64 (TI.tf_addr fr + 30) /\ YK11.getr regs2 19 = w64 TA_M /\
    YK11.getr regs2 20 = w64 off /\ YK11.getr regs2 23 = w64 (TW.M_state Bwc) /\
    YK11.getr regs2 25 = w64 (mfb fr 28) /\
    exists B3, EPI.mrx_ann_tail timg_A fr Bwc off = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* ---- the static facts every segment may use ---- *)

(* The facts of the entry that no step changes: the entry registers, the stack window, the frame's placement, the
   allocator's event count, and the start state's AR. *)
Definition mrx_static (sp1 : Z) (regs0 : bvmap 5 word) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (mdc : Model) (fr : TI.tframe) (n : Z) : Prop :=
  spZ regs0 = sp1 /\ sp1 mod 16 = 0 /\ alloc_ceiling + MRX_STK <= sp1 /\ 2 ^ 46 <= sp1 - MRX_STK /\ sp1 <= 2 ^ 47 /\
  YK0s.ret_ok (YK11.getr regs0 1) /\ 4096 <= raZ regs0 /\
  YK11.getr regs0 3 = w64 (as_gp B) /\ YK11.getr regs0 4 = w64 (as_tp B) /\
  YK11.getr regs0 10 = w64 (TI.tf_addr fr) /\ YK11.getr regs0 11 = w64 n /\
  0 < TI.tf_addr fr /\ TI.tf_addr fr + n < 2 ^ 64 /\
  trans_src_ok B lyc Sc W memc (TI.tf_addr fr) (mlen fr) /\
  (TI.tf_addr fr + mlen fr <= sp1 - MRX_STK \/ sp1 <= TI.tf_addr fr) /\
  mrx_apart fr /\
  st_nev Sc <= EV_MAX /\
  @AR rc segs B lyc Sc W memc mdc.

(* The walk from m_rx's entry (the head segment's statement): the inner journal at its start, the frame's bytes and
   the read-only view at the entry memory, the world relation and the model call. *)
Definition mrx_K_entry (sp1 : Z) (regs0 : bvmap 5 word) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (mdc : Model) (fr : TI.tframe) (n : Z) (Bw Bw' : list byte) (r : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 ->
  garr8 segs (mrestrict (w_H W) memc) (TI.tf_addr fr) (map DSpec.bz (TI.tf_bytes fr)) ->
  trans_rom_view_rd W memc ->
  tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
  TC.m_rx_m timg_A (Some fr) Bw n = Some (Bw', r) ->
  SRr segs W (@cfg_at fx segs (transport_sigma TS_m_rx) regs0 memc mdc)
    (mrx_ipost sp1 regs0 lyc Sc W memc mdc Bw' r).

End k.

(* ---- bytes, world writes, chunks ---- *)

(* Byte j < w (w <= 8) of a 64-bit word holding v is byte j of the w-byte little-endian v. *)
Lemma mrx_bow : forall v (w j : nat), (j < w)%nat -> (w <= 8)%nat ->
  bv_unsigned (YP09.byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v w j.
Proof.
intros v w j Hj Hw. unfold YP09.byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64). change 256 with (2 ^ 8).
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* A view that is rdF on the bytes P marks and rd0 elsewhere (m_lost_cgW.v's form). *)
Definition mrx_in (lo n x : Z) : bool := (lo <=? x) && (x <? lo + n).
Definition mrx_mix (P : Z -> bool) (rdF rd0 : Z -> option Z) : Z -> option Z :=
  fun x => if P x then rdF x else rd0 x.

Lemma mrx_in_true : forall lo n x, lo <= x < lo + n -> mrx_in lo n x = true.
Proof. intros lo n x H. unfold mrx_in. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma mrx_in_false' : forall lo n x, ~ (lo <= x < lo + n) -> mrx_in lo n x = false.
Proof.
intros lo n x H. unfold mrx_in. destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + n)); cbn [andb];
  first [reflexivity | exfalso; lia].
Qed.
Lemma mrx_in_false : forall lo n x, mrx_in lo n x = false -> ~ (lo <= x < lo + n).
Proof. intros lo n x H Hx. rewrite (mrx_in_true lo n x Hx) in H. discriminate H. Qed.

Lemma mrx_tw_start : forall rdF rd0 Bw, tw_at TMAP_A rd0 Bw -> tw_at TMAP_A (mrx_mix (fun _ => false) rdF rd0) Bw.
Proof. intros rdF rd0 Bw H. apply (tw_kept TMAP_A rd0 _ Bw H). intros x _. reflexivity. Qed.

(* One store of m bytes of v at the world offset ko = o + k of the row (o, b, n). *)
Lemma mrx_tw_step : forall rdF rd0 P Bw o b n k ko (m : nat) v,
  tw_at TMAP_A (mrx_mix P rdF rd0) Bw -> In (o, b, n) TMAP_A -> ko = o + k -> 0 <= k -> k + Z.of_nat m <= n ->
  (forall j, (j < m)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  tw_at TMAP_A (mrx_mix (fun x => P x || mrx_in (b + k) (Z.of_nat m) x) rdF rd0) (TW.upd Bw ko (TW.put m v)).
Proof.
intros rdF rd0 P Bw o b n k ko m v H Hin Hko Hk Hkn HV. subst ko.
apply (tw_write TMAP_A (mrx_mix P rdF rd0) (mrx_mix (fun x => P x || mrx_in (b + k) (Z.of_nat m) x) rdF rd0)
  Bw o b n k m v TMAP_A_ok H Hin Hk Hkn).
- intros j Hj. unfold mrx_mix. cbv beta.
  rewrite (mrx_in_true (b + k) (Z.of_nat m) (b + k + Z.of_nat j)) by lia. rewrite orb_true_r. exact (HV j Hj).
- intros x Hx Hn. unfold mrx_mix. cbv beta.
  rewrite (mrx_in_false' (b + k) (Z.of_nat m) x) by lia. rewrite orb_false_r. reflexivity.
Qed.

(* A span of the bytes src written at the world offset ko = o + k of the row (o, b, n) (__asan_memcpy's form). *)
Lemma mrx_tw_span : forall rdF rd0 P Bw o b n k ko (src : list byte),
  tw_at TMAP_A (mrx_mix P rdF rd0) Bw -> In (o, b, n) TMAP_A -> ko = o + k -> 0 <= k ->
  k + Z.of_nat (length src) <= n ->
  (forall i, 0 <= i < Z.of_nat (length src) ->
     rdF (b + k + i) = Some (bv_unsigned (nth (Z.to_nat i) src (Z_to_bv 8 0)))) ->
  tw_at TMAP_A (mrx_mix (fun x => P x || mrx_in (b + k) (Z.of_nat (length src)) x) rdF rd0) (TW.upd Bw ko src).
Proof.
intros rdF rd0 P Bw o b n k ko src H Hin Hko Hk Hkn HV. subst ko.
apply (tw_fill TMAP_A (mrx_mix P rdF rd0)
  (mrx_mix (fun x => P x || mrx_in (b + k) (Z.of_nat (length src)) x) rdF rd0) Bw o b n k src TMAP_A_ok H Hin Hk Hkn).
- intros i Hi. unfold mrx_mix. cbv beta.
  rewrite (mrx_in_true (b + k) (Z.of_nat (length src)) (b + k + i)) by lia. rewrite orb_true_r. exact (HV i Hi).
- intros x Hx Hn. unfold mrx_mix. cbv beta.
  rewrite (mrx_in_false' (b + k) (Z.of_nat (length src)) x) by lia. rewrite orb_false_r. reflexivity.
Qed.

Lemma mrx_tw_end : forall rdF rd0 P Bw, tw_at TMAP_A (mrx_mix P rdF rd0) Bw ->
  (forall x, tw_in TMAP_A x -> P x = false -> rdF x = rd0 x) -> tw_at TMAP_A rdF Bw.
Proof.
intros rdF rd0 P Bw H Hk. apply (tw_kept TMAP_A (mrx_mix P rdF rd0) rdF Bw H).
intros x Hx. unfold mrx_mix. destruct (P x) eqn:E; [reflexivity | exact (Hk x Hx E)].
Qed.

Ltac mrx_unP HP :=
  cbv beta in HP;
  repeat match type of HP with
  | orb _ _ = false =>
      let Hq := fresh "Hq" in apply orb_false_iff in HP; destruct HP as [HP Hq]; apply mrx_in_false in Hq
  end.

(* The rdword of 8 bytes kept byte by byte. *)
Lemma mrx_rdword_kept : forall (rd rd' : Z -> option Z) a v,
  rdword rd a = Some v -> (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = Some v.
Proof.
intros rd rd' a v H K. unfold rdword in *.
rewrite <- (Z.add_0_r a) at 1. rewrite (K 0) by lia. rewrite (K 1) by lia. rewrite (K 2) by lia.
rewrite (K 3) by lia. rewrite (K 4) by lia. rewrite (K 5) by lia. rewrite (K 6) by lia. rewrite (K 7) by lia.
rewrite Z.add_0_r. exact H.
Qed.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.
Local Abbreviation segs := tfibsegs.

(* The w bytes (w <= 8) of a chunk of value v, read through the view. *)
Lemma mrx_chunk_rd : forall (E : env) (H : word -> bool) (mm : word -> option byte) (base off : Z) (w : N) (e : sv) (v : Z),
  YP09.chunk_ok segs E (mrestrict H mm) base (YP09.mkChunk off (CVal w e)) -> sv_denot E e = Z_to_bv 64 v ->
  (N.to_nat w <= 8)%nat ->
  forall j, (j < N.to_nat w)%nat -> aview segs H mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v (N.to_nat w) j).
Proof.
intros E H mm base off w e v HC He Hw j Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC (Z.of_nat j) ltac:(lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview segs H mm (base + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H mm) (base + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply mrx_bow; lia.
Qed.

(* The saved slots, and a spill slot, kept when their bytes are. *)
Lemma mrx_saved_kept : forall (Wc Wc' : world segs) mem mem' sp1 regs0,
  @mrx_saved Wc mem sp1 regs0 ->
  (forall a, sp1 - 104 <= a < sp1 -> aview segs (w_H Wc') mem' a = aview segs (w_H Wc) mem a) ->
  @mrx_saved Wc' mem' sp1 regs0.
Proof.
intros Wc Wc' mem mem' sp1 regs0 H K. unfold mrx_saved in *.
rewrite Forall_forall in *. intros ro Hro. specialize (H ro Hro).
apply (mrx_rdword_kept _ _ _ _ H). intros i Hi. apply K.
unfold MRX_SAVES in Hro. unfold MRX_FRAME.
repeat (destruct Hro as [Hro | Hro]; [subst ro; cbn [snd]; lia |]). destruct Hro.
Qed.

Lemma mrx_spill_kept : forall (Wc Wc' : world segs) mem mem' sp1 o fr k,
  @mrx_spill Wc mem sp1 o fr k ->
  (forall a, sp1 - MRX_FRAME + o <= a < sp1 - MRX_FRAME + o + 8 -> aview segs (w_H Wc') mem' a = aview segs (w_H Wc) mem a) ->
  @mrx_spill Wc' mem' sp1 o fr k.
Proof.
intros Wc Wc' mem mem' sp1 o fr k H K. unfold mrx_spill in *.
apply (mrx_rdword_kept _ _ _ _ H). intros i Hi. apply K. lia.
Qed.

(* The cut from its parts (a run's end, or a callee's return). *)
Lemma mrx_at_intro : forall sp1 regs0 lyc Sc (W : world segs) memc mdc pc R (Wc : world segs) Bwc ly2 S2 regs2 mem2 md2,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc mem2 md2 0 ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> mo_le MT Sc S2 0 ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regs2 3 = YK11.getr regs0 3 -> YK11.getr regs2 4 = YK11.getr regs0 4 ->
  @mrx_saved Wc mem2 sp1 regs0 ->
  tw_at TMAP_A (aview segs (w_H Wc) mem2) Bwc ->
  R Wc Bwc ly2 S2 regs2 mem2 ->
  @mrx_at fx rc B MT sp1 regs0 lyc Sc W memc mdc pc R Wc Bwc
    (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 pc) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros. exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

(* The bcmp wrapper called from a G journal (YCbq.v aj_bcmp_at through TransportGCg.v gx_call_leaf). *)
Lemma mrx_bcmp_gx : forall pc, abcmp_realizes segs B pc ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (o : Z) raw,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  YK11.getr regsT 10 = w64 x -> YK11.getr regsT 11 = w64 y -> YK11.getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) -> YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n ->
  (forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  amem_range x n -> amem_range y n ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 pc) memT (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
      c2 = mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
      @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
      aregs_preserved regsT regs2 /\
      (YK11.getr regs2 10 = w64 0 <->
         forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
         aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
      (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw
  HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
apply (gx_call_leaf segs B TG.G_HARNESS STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k _ raw
  (fun regs2 mem2 md2 =>
     aregs_preserved regsT regs2 /\
     (YK11.getr regs2 10 = w64 0 <->
        forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
        aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)) HJ).
intros memS HJi.
eapply SRr_mono.
{ exact (aj_bcmp_at segs B LAWS transport_segs_low pc AM W regsT memT STK sp0 FP ly S W0 memS md own lyc Sc mdc k
    x y n o raw HJi Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy
    Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & Hc & HJ2 & HP & Hv & Hcmp & Hfr & Hgr).
split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|].
split; [exact HP|]. split; [rewrite Hv; exact Hcmp|]. split; [exact Hfr | exact Hgr].
Qed.

End l.

(* ---- the model ---- *)

(* n < 30: spec_read_frame's SPEC_E_SHORT, the world unchanged and 0. *)
Lemma mrx_m_short : forall I fr Bw n, 0 <= n < 30 -> n <= mlen fr ->
  TC.m_rx_m I (Some fr) Bw n = Some (Bw, 0).
Proof.
intros I fr Bw n Hn Hl.
assert (E1 : (n <? 0) || (Z.of_nat (length (TI.tf_bytes fr)) <? n) = false)
  by (apply orb_false_iff; unfold mlen in Hl; split; apply Z.ltb_ge; lia).
unfold TC.m_rx_m. cbv zeta. rewrite E1. unfold DSpec.spec_read_frame.
replace (n <? DSpec.SPEC_BODY_AT) with true by (symmetry; apply Z.ltb_lt; unfold DSpec.SPEC_BODY_AT; lia).
reflexivity.
Qed.

(* The model's range of n. *)
Lemma mrx_m_n : forall I fr Bw n Bw' r, TC.m_rx_m I (Some fr) Bw n = Some (Bw', r) -> 0 <= n <= mlen fr.
Proof.
intros I fr Bw n Bw' r H. unfold TC.m_rx_m in H. cbv zeta in H.
destruct ((n <? 0) || (Z.of_nat (length (TI.tf_bytes fr)) <? n)) eqn:E; [discriminate H|].
apply orb_false_iff in E as [E1 E2]. apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. unfold mlen. lia.
Qed.
