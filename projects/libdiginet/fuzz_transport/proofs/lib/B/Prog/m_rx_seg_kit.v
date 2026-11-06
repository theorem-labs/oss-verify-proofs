(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 902 of its 1078 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SlostHead.v, with its module names and numbers changed; 1131 of its 1216 lines of code are new or changed and 993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_annt.v; 727 of its 836 lines of code are new or changed and 1107 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_calls.v, with its module paths, module names and numbers changed; 491 of its 582 lines of code are new or changed and 745 lines of the source are left out. *)
(* m_rx_seg_kit: the shared pieces of the image-B walk of m_rx (statement lib/B/Prog/m_rx_cg.v, entry 0x84c1c =
   transportb_sigma TB_m_rx, 1060 bytes, frame 112), split in segments m_rx_seg_*.v and closed in m_rx_cgW.v.

   The walk holds an INNER G journal, started at m_rx's entry (sp1 = the entry sp, window MRX_STK, no footprint, no
   frame of its own, start state the call state lyc Sc W memc mdc):
     ajournal_gx G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc mem2 md2 0.
   Every run of a segment and every callee runs against it (the callees take it as their caller's journal). The top
   file composes it with the caller's journal (W_journalG.v ajournal_gx_sub) and reads acall_kept_g off it
   (m_rx_seg_glue.v mrx_kept_g_of_inner). The design is image A's (lib/A/Prog/m_rx_seg_kit.v); the cuts and their
   facts are image B's code (lib/B/Prog/DgnTransportBList.v AF_m_rx 0x397c).

   A segment starts at a CUT, a pc inside m_rx and the facts mrx_at gives there, and ends at other cuts, whose
   continuations (mrx_K) are its premises, or at the return (mrx_ipost). The cuts (pc = 0x84c1c + offset):
     SRF  +0x024  `jal spec_read_frame` (a0 = fa, a1 = n, a2 = sp), at the call state (ly2 = lyc, S2 = Sc);
     EPI  +0x030  the epilogue, a0 = r, the world the model's last world;
     MAC  +0x048  spec_read_frame gave SPEC_OK: the three MAC compares;
     DESK +0x098  the desk test (bcmp with M.desk, or the cmd test, the OUI bcmp and __asan_memcpy into M.desk);
     BODY +0x100  the S_CLOSED test, M.last_rx, the switch, cmd e3 inline;
     HOST +0x144  cmd e1 with body_len >= 33: `jal host_offset`, s0 = its result, then ANNT;
     ACK  +0x160  cmd ACK;
     SET  +0x1cc  `mv a0, zero; jal m_set` (a1 = why), then TICK (the inlined m_lost of cmd e3 and of a foreign e1);
     DATA +0x1d8  cmd DATA;
     ANNT +0x314  cmd e0 / e1 (s0 = off): OW.desk, OW.desk_off, `jal desk_named`, OW.desk_p, OW.desk_body;
     E0   +0x350  cmd e0 after the desk fields;   E1   +0x390  cmd e1 after the desk fields;
     E0L  +0x36c  `mv a0, zero; jal m_set` (a1 = 3), then `lw a0, 12(s1)` (M.state) -> E0W;
     E0W  +0x378  a0 = M.state: S_IDLE and g_cfg.auto_wake give m_wake;
     WAKE +0x388  `jal m_wake`, then TICK;   MO +0x3a0 `jal m_maybe_online` (its return address is TICK);
     TICK +0x3a4  `jal m_tick`, a0 = 1, `j` to the epilogue.
   The cuts from MAC on carry the frame (its bytes, their placement at the current state, the read-only view), the
   struct spec_read_frame filled at sp1 - 112 and spec_read_frame's SPEC_OK (mrx_cur). Their model facts are
   lib/U/Prog/T/m_rx.v's cut of TCb.v m_rx_m (the ubsan image calls spec_read_frame and host_offset as image B does):
   mr_f, mr_k, mr_ack, mr_data, mr_ann, mr_ann2, mr_e0, mr_e1; lib/Prog/T/m_rx_epi.v mrx_e0w; and mrxb_mac /
   mrxb_desk below (the MAC compares and the desk test, mr_unfold's head). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg m_wake_cg m_maybe_online_cg m_tick_cg spec_read_frame_cg host_offset_cg desk_named_cg check_state_data_cg
  m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require m_rx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module UMR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.m_rx.
Module AK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_kit.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- the cut pcs ---- *)
Definition MRX_PC (off : Z) : Z := transportb_sigma TB_m_rx + off.
Definition OFF_SRF : Z := 0x24.
Definition OFF_EPI : Z := 0x30.
Definition OFF_MAC : Z := 0x48.
Definition OFF_DESK : Z := 0x98.
Definition OFF_BODY : Z := 0x100.
Definition OFF_HOST : Z := 0x144.
Definition OFF_ACK : Z := 0x160.
Definition OFF_SET : Z := 0x1cc.
Definition OFF_DATA : Z := 0x1d8.
Definition OFF_ANNT : Z := 0x314.
Definition OFF_E0 : Z := 0x350.
Definition OFF_E0L : Z := 0x36c.
Definition OFF_E0W : Z := 0x378.
Definition OFF_WAKE : Z := 0x388.
Definition OFF_E1 : Z := 0x390.
Definition OFF_MO : Z := 0x3a0.
Definition OFF_TICK : Z := 0x3a4.
Lemma mrx_pc_val : transportb_sigma TB_m_rx = 0x84c1c.
Proof. reflexivity. Qed.

(* The listing's base: the text object's value plus m_rx's slot offset is the entry. *)
Section base. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mrx_base : @pa_val _ transportb_listing PI_transportb A_TEXT + AF_m_rx = transportb_sigma TB_m_rx.
Proof. vm_compute. reflexivity. Qed.
Lemma mrx_pcv : forall off, MRX_PC off = @pa_val _ transportb_listing PI_transportb A_TEXT + (AF_m_rx + off).
Proof. intros off. unfold MRX_PC. rewrite <- mrx_base. ring. Qed.
Lemma mrx_bval : @pa_val _ transportb_listing PI_transportb A_TEXT = 0x84c1c - 0x397c.
Proof. rewrite <- mrx_pc_val, <- mrx_base. unfold AF_m_rx. ring. Qed.
End base.

(* The 4 registers the prologue saves (0x84c20 - 0x84c2c), with their offsets from sp1 - 112: ra at 104, s0 at 96,
   s1 at 88, s2 at 80. The epilogue (0x84c4c - 0x84c58) loads them back. *)
Definition MRX_SAVES : list (Z * Z) := [(1, 104); (8, 96); (9, 88); (18, 80)].

(* The frame's length (A's kit, image-free). *)
Abbreviation mlen := AK.mlen.

(* spec_read_frame's parse of the n bytes of the frame (lib/U/Prog/T/m_rx.v mr_f; spec_read_frame_cg.v srf_f). *)
Abbreviation mrx_f := UMR.mr_f.

(* spec_read_frame's SPEC_OK at n: the model's range of n and the code. *)
Definition mrx_ok (fr : TI.tframe) (n : Z) : Prop :=
  0 <= n <= mlen fr /\ DSpec.sf_code (mrx_f fr n) = DSpec.SPEC_OK.

(* ---- the model ---- *)

(* The MAC fields of the frame at the parse's offsets. *)
Definition mrxb_src (fr : TI.tframe) (n : Z) : list byte := TW.sub (TI.tf_bytes fr) (DSpec.sf_src (mrx_f fr n)) 6.
Definition mrxb_dst (fr : TI.tframe) (n : Z) : list byte := TW.sub (TI.tf_bytes fr) (DSpec.sf_dst (mrx_f fr n)) 6.

(* :288-297, once the frame is from not-HOST to HOST or broadcast. *)
Definition mrxb_desk (I : TI.timg) (fr : TI.tframe) (n : Z) (B : list byte) : option (list byte * Z) :=
  let fc := DSpec.sf_cmd (mrx_f fr n) in
  if TC.truth (TW.M_desk_known B) then
    if TC.beq_bytes (mrxb_src fr n) (TW.M_desk B) then UMR.mr_k I fr n B else Some (B, 0)
  else if negb ((fc =? TC.SPEC_CMD_E0) || (fc =? TC.SPEC_CMD_E1)) then Some (B, 0)
  else if negb (TC.beq_bytes (firstn 3 (mrxb_src fr n)) TC.SPEC_OUI) then Some (B, 0)
  else UMR.mr_k I fr n (TW.set_M_desk_known (TW.set_M_desk B (mrxb_src fr n)) 1).

(* :285-297, after spec_read_frame's SPEC_OK. *)
Definition mrxb_mac (I : TI.timg) (fr : TI.tframe) (n : Z) (B : list byte) : option (list byte * Z) :=
  if TC.beq_bytes (mrxb_src fr n) TC.HOST ||
     (negb (TC.beq_bytes (mrxb_dst fr n) TC.HOST) && negb (TC.beq_bytes (mrxb_dst fr n) TC.SPEC_BCAST))
  then Some (B, 0)
  else mrxb_desk I fr n B.

(* m_rx_m at SPEC_OK is mrxb_mac; at another code it is (B, 0). *)
Lemma mrxb_top : forall I fr B n, mrx_ok fr n -> TC.m_rx_m I (Some fr) B n = mrxb_mac I fr n B.
Proof.
intros I fr B n (Hn & Hok). rewrite UMR.mr_unfold.
assert (E1 : (n <? 0) || (Z.of_nat (length (TI.tf_bytes fr)) <? n) = false)
  by (apply orb_false_iff; unfold mlen, AK.mlen in Hn; split; apply Z.ltb_ge; lia).
rewrite E1. rewrite Hok. cbn [Z.eqb negb]. unfold mrxb_mac, mrxb_desk, mrxb_src, mrxb_dst. reflexivity.
Qed.

Lemma mrxb_err : forall I fr B n, 0 <= n <= mlen fr -> DSpec.sf_code (mrx_f fr n) <> DSpec.SPEC_OK ->
  TC.m_rx_m I (Some fr) B n = Some (B, 0).
Proof.
intros I fr B n Hn Hc. rewrite UMR.mr_unfold.
assert (E1 : (n <? 0) || (Z.of_nat (length (TI.tf_bytes fr)) <? n) = false)
  by (apply orb_false_iff; unfold mlen, AK.mlen in Hn; split; apply Z.ltb_ge; lia).
rewrite E1. replace (DSpec.sf_code (mrx_f fr n) =? DSpec.SPEC_OK) with false by (symmetry; apply Z.eqb_neq; exact Hc).
reflexivity.
Qed.

(* spec_read_frame's fields at SPEC_OK (lib/U/Prog/T/m_rx.v mr_srf_ok). *)
Lemma mrx_ok_fields : forall fr n, mrx_ok fr n ->
  DSpec.sf_dst (mrx_f fr n) = 0 /\ DSpec.sf_src (mrx_f fr n) = 6 /\ DSpec.sf_body (mrx_f fr n) = 30 /\ 30 <= n /\
  0 <= DSpec.sf_body_len (mrx_f fr n) /\ 30 + DSpec.sf_body_len (mrx_f fr n) <= n /\
  0 <= DSpec.sf_cmd (mrx_f fr n) < 256 /\ 0 <= DSpec.sf_retry (mrx_f fr n) < 2 ^ 16 /\
  0 <= DSpec.sf_send (mrx_f fr n) < 2 ^ 32 /\ 0 <= DSpec.sf_ack (mrx_f fr n) < 2 ^ 32.
Proof. intros fr n (_ & Hok). exact (UMR.mr_srf_ok (TI.tf_bytes fr) n Hok). Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The callee-saved registers m_rx never writes (s3 .. s11 = x19 .. x27) hold the entry's values. *)
Definition mrx_hi (regs0 regs2 : bvmap 5 word) : Prop :=
  forall q, 19 <= q <= 27 -> YK11.getr regs2 (Z_to_bv 5 q) = YK11.getr regs0 (Z_to_bv 5 q).

(* The 4 saved slots hold the entry registers. *)
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
    ajournal_gx TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 0 /\
    aregs_preserved regs0 regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ mo_le MT Sc S2 0 /\
    YK11.getr regs2 10 = w64 r /\ tw_at TMAP_B (aview segs (w_H W2) mem2) Bw'.

(* A cut: the machine at pc with the inner journal at (ly2, S2), the common facts, and the cut's own facts R (of the
   current world Wc, the model's world Bwc, the state, the registers and the memory). *)
Definition mrx_at (sp1 : Z) (regs0 : bvmap 5 word) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (mdc : Model) (pc : Z)
    (R : world segs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop)
    (Wc : world segs) (Bwc : list byte) (c : config) : Prop :=
  exists ly2 S2 regs2 mem2 md2,
    c = mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 pc) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal_gx TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc mem2 md2 0 /\
    frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ mo_le MT Sc S2 0 /\
    YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) /\
    YK11.getr regs2 3 = YK11.getr regs0 3 /\ YK11.getr regs2 4 = YK11.getr regs0 4 /\
    mrx_hi regs0 regs2 /\
    mrx_saved Wc mem2 sp1 regs0 /\
    tw_at TMAP_B (aview segs (w_H Wc) mem2) Bwc /\
    R Wc Bwc ly2 S2 regs2 mem2.

(* The continuation of a cut: from every machine the cut describes, the run reaches the return. *)
Definition mrx_K (sp1 : Z) (regs0 : bvmap 5 word) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (mdc : Model) (Bw' : list byte) (r : Z) (pc : Z)
    (R : world segs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
  forall Wc Bwc c, mrx_at sp1 regs0 lyc Sc W memc mdc pc R Wc Bwc c ->
    SRr segs Wc c (mrx_ipost sp1 regs0 lyc Sc W memc mdc Bw' r).

(* The frame's bytes, their placement at the state (ly2, S2) and memory mem, and the read-only view. *)
Definition mrx_frs (fr : TI.tframe) (ly2 : alayout) (S2 : astate) (Wc : world segs) (mem : word -> option byte) : Prop :=
  garr8 segs (mrestrict (w_H Wc) mem) (TI.tf_addr fr) (map DSpec.bz (TI.tf_bytes fr)) /\
  trans_src_ok B ly2 S2 Wc mem (TI.tf_addr fr) (mlen fr) /\
  trans_rom_view_rd Wc mem.

(* The struct f spec_read_frame filled at sp1 - 112: its 80 bytes (spec_read_frame_cg.v transport_srf_post). *)
Definition mrx_sf (Wc : world segs) (mem : word -> option byte) (sp1 : Z) (fr : TI.tframe) (n : Z) : Prop :=
  garr8 segs (mrestrict (w_H Wc) mem) (sp1 - MRX_FRAME) (TW.zs (TCt.sf_bytes (TI.tf_addr fr) (mrx_f fr n))).

(* What every cut from MAC on carries of the frame: SPEC_OK, the frame and the struct. *)
Definition mrx_cur (fr : TI.tframe) (n sp1 : Z) (ly2 : alayout) (S2 : astate) (Wc : world segs)
    (mem : word -> option byte) : Prop :=
  mrx_ok fr n /\ mrx_frs fr ly2 S2 Wc mem /\ mrx_sf Wc mem sp1 fr n.

(* ---- the cuts' own facts ---- *)

Definition mrx_R : Type := world segs -> list byte -> alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Prop.

(* EPI: the epilogue with a0 = r at the model's last world. *)
Definition R_EPI (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 => Bwc = Bw' /\ YK11.getr regs2 10 = w64 r.

(* TICK: m_tick from Bwc gives Bw'; the result is 1. *)
Definition R_TICK (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 => TC.m_tick_m Bwc = Some (Bw', tt) /\ r = 1.

(* MO: m_maybe_online, then m_tick. *)
Definition R_MO (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists B3,
    TC.m_maybe_online_m Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* WAKE: m_wake (its result ignored), then m_tick. *)
Definition R_WAKE (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists B3 rw,
    TC.m_wake_m Bwc = Some (B3, rw) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* SET: a1 = why; m_set S_IDLE why (a0 = 0 is set at the cut's own `mv a0, zero`), then m_tick. The two stores of
   the inlined m_lost are made before the cut. *)
Definition R_SET (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists why B3,
    YK11.getr regs2 11 = w64 why /\ - 2 ^ 31 <= why < 2 ^ 31 /\
    TC.m_set_m Bwc TC.S_IDLE why = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* E0W (cmd e0, after its m_lost or with M.state not S_ONLINE): a0 = M.state; mrx_e0w, then m_tick. *)
Definition R_E0W (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists B3,
    YK11.getr regs2 10 = w64 (TW.M_state Bwc) /\
    EPI.mrx_e0w Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* E0L (cmd e0, M.state was S_ONLINE, after the inlined m_lost's two stores): s1 = &M, a1 = 3 (R_DESK_OFFLINE);
   m_set S_IDLE 3, mrx_e0w, then m_tick. *)
Definition R_E0L (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists B6 B3,
    YK11.getr regs2 9 = w64 TB_M /\ YK11.getr regs2 11 = w64 3 /\
    TC.m_set_m Bwc TC.S_IDLE 3 = Some (B6, tt) /\ EPI.mrx_e0w B6 = Some (B3, tt) /\
    TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* E0 (cmd e0, after OW.desk_p / OW.desk_body): s1 = &M; mr_e0, then m_tick. *)
Definition R_E0 (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists B3,
    YK11.getr regs2 9 = w64 TB_M /\
    UMR.mr_e0 Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* E1 (cmd e1, after OW.desk_p / OW.desk_body): s0 = off (host_offset's result), s1 = &M, s2 = &OW; mr_e1 off, then
   m_tick. *)
Definition R_E1 (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists off B3,
    -1 <= off < 10 /\
    YK11.getr regs2 8 = w64 off /\ YK11.getr regs2 9 = w64 TB_M /\ YK11.getr regs2 18 = w64 TB_OW /\
    UMR.mr_e1 off Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* SRF: the call of spec_read_frame, at the call state: a0 = fa, a1 = n, a2 = sp, s2 = the shadow base; the frame's
   bytes, its placement and the read-only view at the current memory; the model call. *)
Definition R_SRF (fr : TI.tframe) (n : Z) (sp1 : Z) (lyc : alayout) (Sc : astate) (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    ly2 = lyc /\ S2 = Sc /\ mrx_frs fr lyc Sc Wc mem2 /\
    YK11.getr regs2 10 = w64 (TI.tf_addr fr) /\ YK11.getr regs2 11 = w64 n /\
    YK11.getr regs2 12 = Z_to_bv 64 (sp1 - MRX_FRAME) /\ YK11.getr regs2 18 = w64 SHADOW_OFF /\
    TC.m_rx_m timg_B (Some fr) Bwc n = Some (Bw', r).

(* MAC: SPEC_OK, s2 = the shadow base; the model from mrxb_mac. *)
Definition R_MAC (fr : TI.tframe) (n : Z) (sp1 : Z) (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    mrx_cur fr n sp1 ly2 S2 Wc mem2 /\ YK11.getr regs2 18 = w64 SHADOW_OFF /\
    mrxb_mac timg_B fr n Bwc = Some (Bw', r).

(* DESK: as MAC, and s0 = fa + 6 (f.src); the model from mrxb_desk. *)
Definition R_DESK (fr : TI.tframe) (n : Z) (sp1 : Z) (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    mrx_cur fr n sp1 ly2 S2 Wc mem2 /\
    YK11.getr regs2 8 = w64 (TI.tf_addr fr + 6) /\ YK11.getr regs2 18 = w64 SHADOW_OFF /\
    mrxb_desk timg_B fr n Bwc = Some (Bw', r).

(* BODY: s1 = &M, s2 = the shadow base; the model from mr_k. *)
Definition R_BODY (fr : TI.tframe) (n : Z) (sp1 : Z) (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    mrx_cur fr n sp1 ly2 S2 Wc mem2 /\
    YK11.getr regs2 9 = w64 TB_M /\ YK11.getr regs2 18 = w64 SHADOW_OFF /\
    UMR.mr_k timg_B fr n Bwc = Some (Bw', r).

(* ACK (after M.last_rx): cmd ACK, a0 = M.state, s1 = &M; mr_ack, then m_tick. *)
Definition R_ACK (fr : TI.tframe) (n : Z) (sp1 : Z) (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    mrx_cur fr n sp1 ly2 S2 Wc mem2 /\ DSpec.sf_cmd (mrx_f fr n) = TC.SPEC_CMD_ACK /\
    YK11.getr regs2 10 = w64 (TW.M_state Bwc) /\ YK11.getr regs2 9 = w64 TB_M /\
    exists B3, UMR.mr_ack fr n Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* DATA (after M.last_rx): cmd DATA, a1 = g_now, s1 = &M, s2 = the shadow base; mr_data, then m_tick. *)
Definition R_DATA (fr : TI.tframe) (n : Z) (sp1 : Z) (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    mrx_cur fr n sp1 ly2 S2 Wc mem2 /\ DSpec.sf_cmd (mrx_f fr n) = TC.SPEC_CMD_DATA /\
    YK11.getr regs2 11 = w64 (TW.g_now Bwc) /\ YK11.getr regs2 9 = w64 TB_M /\
    YK11.getr regs2 18 = w64 SHADOW_OFF /\
    exists B3, UMR.mr_data fr n Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* HOST (after M.last_rx): cmd e1, body_len >= 33, s1 = &M; mr_ann, then m_tick. *)
Definition R_HOST (fr : TI.tframe) (n : Z) (sp1 : Z) (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    mrx_cur fr n sp1 ly2 S2 Wc mem2 /\ DSpec.sf_cmd (mrx_f fr n) = TC.SPEC_CMD_E1 /\
    TC.SPEC_ANN_MIN <= DSpec.sf_body_len (mrx_f fr n) /\ YK11.getr regs2 9 = w64 TB_M /\
    exists B3, UMR.mr_ann timg_B fr n Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* ANNT (after M.last_rx and, for e1, host_offset): cmd e0 / e1, body_len >= 33, s0 = off (-1 for e0), s1 = &M;
   mr_ann2 off, then m_tick. *)
Definition R_ANNT (fr : TI.tframe) (n : Z) (sp1 : Z) (Bw' : list byte) (r : Z) : mrx_R :=
  fun Wc Bwc ly2 S2 regs2 mem2 => exists off,
    mrx_cur fr n sp1 ly2 S2 Wc mem2 /\
    (DSpec.sf_cmd (mrx_f fr n) = TC.SPEC_CMD_E0 \/ DSpec.sf_cmd (mrx_f fr n) = TC.SPEC_CMD_E1) /\
    TC.SPEC_ANN_MIN <= DSpec.sf_body_len (mrx_f fr n) /\
    -1 <= off < 10 /\ (DSpec.sf_cmd (mrx_f fr n) = TC.SPEC_CMD_E0 -> off = -1) /\
    YK11.getr regs2 8 = w64 off /\ YK11.getr regs2 9 = w64 TB_M /\
    exists B3, UMR.mr_ann2 timg_B fr n off Bwc = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

(* ---- the static facts every segment may use ---- *)

(* The facts of the entry that no step changes: the entry registers, the stack window, the frame's placement, the
   allocator's event count, and the start state's AR. *)
Definition mrx_static (sp1 : Z) (regs0 : bvmap 5 word) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (mdc : Model) (fr : TI.tframe) (n : Z) : Prop :=
  spZ regs0 = sp1 /\ sp1 mod 16 = 0 /\ alloc_ceiling + MRX_STK <= sp1 /\ 2 ^ 46 <= sp1 - MRX_STK /\ sp1 <= 2 ^ 47 /\
  YK0s.ret_ok (YK11.getr regs0 1) /\ 4096 <= raZ regs0 /\
  YK11.getr regs0 3 = w64 (as_gp B) /\ YK11.getr regs0 4 = w64 (as_tp B) /\
  YK11.getr regs0 10 = w64 (TI.tf_addr fr) /\ YK11.getr regs0 11 = w64 n /\
  0 < TI.tf_addr fr /\ TI.tf_addr fr + n < 2 ^ 64 /\ TI.tf_addr fr + mlen fr < 2 ^ 64 /\
  trans_src_ok B lyc Sc W memc (TI.tf_addr fr) (mlen fr) /\
  (TI.tf_addr fr + mlen fr <= sp1 - MRX_STK \/ sp1 <= TI.tf_addr fr) /\
  mrx_apart fr /\
  st_nev Sc <= EV_MAX /\
  @AR rc segs B lyc Sc W memc mdc.

(* The walk from m_rx's entry (the head segment's statement): the inner journal at its start, the frame's bytes and
   the read-only view at the entry memory, the world relation and the model call. *)
Definition mrx_K_entry (sp1 : Z) (regs0 : bvmap 5 word) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (mdc : Model) (fr : TI.tframe) (n : Z) (Bw Bw' : list byte) (r : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 ->
  garr8 segs (mrestrict (w_H W) memc) (TI.tf_addr fr) (map DSpec.bz (TI.tf_bytes fr)) ->
  trans_rom_view_rd W memc ->
  tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
  TC.m_rx_m timg_B (Some fr) Bw n = Some (Bw', r) ->
  SRr segs W (@cfg_at fx segs (transportb_sigma TB_m_rx) regs0 memc mdc)
    (mrx_ipost sp1 regs0 lyc Sc W memc mdc Bw' r).

End k.

(* ---- bytes, world writes ---- *)

(* A view that is rdF on the bytes P marks and rd0 elsewhere (A's kit mrx_mix, image-free). *)
Abbreviation mrx_mix := AK.mrx_mix.
Abbreviation mrx_in := AK.mrx_in.

Lemma mrx_tw_start : forall rdF rd0 Bw, tw_at TMAP_B rd0 Bw -> tw_at TMAP_B (mrx_mix (fun _ => false) rdF rd0) Bw.
Proof. intros rdF rd0 Bw H. apply (tw_kept TMAP_B rd0 _ Bw H). intros x _. reflexivity. Qed.

(* One store of m bytes of v at the world offset ko = o + k of the row (o, b, n). *)
Lemma mrx_tw_step : forall rdF rd0 P Bw o b n k ko (m : nat) v,
  tw_at TMAP_B (mrx_mix P rdF rd0) Bw -> In (o, b, n) TMAP_B -> ko = o + k -> 0 <= k -> k + Z.of_nat m <= n ->
  (forall j, (j < m)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  tw_at TMAP_B (mrx_mix (fun x => P x || mrx_in (b + k) (Z.of_nat m) x) rdF rd0) (TW.upd Bw ko (TW.put m v)).
Proof.
intros rdF rd0 P Bw o b n k ko m v H Hin Hko Hk Hkn HV. subst ko.
apply (tw_write TMAP_B (mrx_mix P rdF rd0) (mrx_mix (fun x => P x || mrx_in (b + k) (Z.of_nat m) x) rdF rd0)
  Bw o b n k m v TMAP_B_ok H Hin Hk Hkn).
- intros j Hj. unfold AK.mrx_mix. cbv beta.
  rewrite (AK.mrx_in_true (b + k) (Z.of_nat m) (b + k + Z.of_nat j)) by lia. rewrite orb_true_r. exact (HV j Hj).
- intros x Hx Hn. unfold AK.mrx_mix. cbv beta.
  rewrite (AK.mrx_in_false' (b + k) (Z.of_nat m) x) by lia. rewrite orb_false_r. reflexivity.
Qed.

(* A span of the bytes src written at the world offset ko = o + k of the row (o, b, n) (__asan_memcpy's form). *)
Lemma mrx_tw_span : forall rdF rd0 P Bw o b n k ko (src : list byte),
  tw_at TMAP_B (mrx_mix P rdF rd0) Bw -> In (o, b, n) TMAP_B -> ko = o + k -> 0 <= k ->
  k + Z.of_nat (length src) <= n ->
  (forall i, 0 <= i < Z.of_nat (length src) ->
     rdF (b + k + i) = Some (bv_unsigned (nth (Z.to_nat i) src (Z_to_bv 8 0)))) ->
  tw_at TMAP_B (mrx_mix (fun x => P x || mrx_in (b + k) (Z.of_nat (length src)) x) rdF rd0) (TW.upd Bw ko src).
Proof.
intros rdF rd0 P Bw o b n k ko src H Hin Hko Hk Hkn HV. subst ko.
apply (tw_fill TMAP_B (mrx_mix P rdF rd0)
  (mrx_mix (fun x => P x || mrx_in (b + k) (Z.of_nat (length src)) x) rdF rd0) Bw o b n k src TMAP_B_ok H Hin Hk Hkn).
- intros i Hi. unfold AK.mrx_mix. cbv beta.
  rewrite (AK.mrx_in_true (b + k) (Z.of_nat (length src)) (b + k + i)) by lia. rewrite orb_true_r. exact (HV i Hi).
- intros x Hx Hn. unfold AK.mrx_mix. cbv beta.
  rewrite (AK.mrx_in_false' (b + k) (Z.of_nat (length src)) x) by lia. rewrite orb_false_r. reflexivity.
Qed.

Lemma mrx_tw_end : forall rdF rd0 P Bw, tw_at TMAP_B (mrx_mix P rdF rd0) Bw ->
  (forall x, tw_in TMAP_B x -> P x = false -> rdF x = rd0 x) -> tw_at TMAP_B rdF Bw.
Proof.
intros rdF rd0 P Bw H Hk. apply (tw_kept TMAP_B (mrx_mix P rdF rd0) rdF Bw H).
intros x Hx. unfold AK.mrx_mix. destruct (P x) eqn:E; [reflexivity | exact (Hk x Hx E)].
Qed.

Ltac mrx_unP HP :=
  cbv beta in HP;
  repeat match type of HP with
  | orb _ _ = false =>
      let Hq := fresh "Hq" in apply orb_false_iff in HP; destruct HP as [HP Hq]; apply AK.mrx_in_false in Hq
  end.

(* nth through firstn, skipn and TW.zs. *)
Lemma mrx_nth_firstn : forall (A : Type) (l : list A) w k d, (k < w)%nat -> nth k (firstn w l) d = nth k l d.
Proof.
intros A l. induction l as [|x l IH]; intros w k d Hk.
- destruct w as [|w]; [lia|]. destruct k; reflexivity.
- destruct w as [|w]; [lia|]. destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma mrx_nth_skipn : forall (A : Type) (l : list A) o k d, nth k (skipn o l) d = nth (o + k) l d.
Proof.
intros A l o. revert l. induction o as [|o IH]; intros l k d; [reflexivity|].
destruct l as [|x l]; [destruct k; reflexivity | cbn [skipn]; apply IH].
Qed.
Lemma mrx_nth_zs : forall (l : list byte) j, (j < length l)%nat ->
  nth j (TW.zs l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
intros l j Hj. unfold TW.zs.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). apply map_nth.
Qed.
Lemma mrx_le_byte1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small x 256) by lia. apply Z.mod_small. lia.
Qed.

(* The w bytes at offset o of a garr8 array of a byte list l whose bytes there are put w v: the w-byte value v. *)
Lemma mrx_garr8_val : forall (sg : list Segment) (mm : word -> option byte) (base : Z) (l : list byte) (o w : nat) (v : Z),
  garr8 sg mm base (TW.zs l) -> (o + w <= length l)%nat -> firstn w (skipn o l) = TW.put w v ->
  val_mem sg mm (base + Z.of_nat o) w v.
Proof.
intros sg mm base l o w v HG Hlen Hsub k Hk.
assert (Hj : (o + k < length (TW.zs l))%nat) by (unfold TW.zs; rewrite length_map; lia).
destruct (HG (o + k)%nat Hj) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
replace (base + Z.of_nat (o + k) + Z.of_nat 0) with (base + Z.of_nat o + Z.of_nat k) in Hv by lia.
rewrite Hv. do 2 f_equal.
assert (Hn : nth (o + k) l (Z_to_bv 8 0) = nth k (TW.put w v) (Z_to_bv 8 0)).
{ rewrite <- Hsub. rewrite (mrx_nth_firstn _ _ w k _ Hk). rewrite mrx_nth_skipn. reflexivity. }
rewrite (mrx_nth_zs l (o + k) ltac:(lia)), Hn, (tw_le_byte_put w v k (Z_to_bv 8 0) Hk).
apply mrx_le_byte1. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* The struct's fields, as the code loads them: the 8 bytes at 8 (dst), 16 (src), 48 (body), 56 (body_len); the 2
   bytes at 30 (retry); the 4 bytes at 32 (send) and 36 (ack); the byte at 40 (cmd). *)
Section sf. Context {sg : list Segment}.
Variable mm : word -> option byte.
Variable base fa : Z.
Variable f : DSpec.spec_frame.
Hypothesis HG : garr8 sg mm base (TW.zs (TCt.sf_bytes fa f)).

Local Ltac sf_field o w :=
  change (base + _) with (base + Z.of_nat o);
  apply (mrx_garr8_val sg mm base (TCt.sf_bytes fa f) o w _ HG);
  [ change (length (TCt.sf_bytes fa f)) with 80%nat; lia | reflexivity ].

Lemma mrx_sf_dst : val_mem sg mm (base + 8) 8 (TCt.sf_ptr fa f (DSpec.sf_dst f)).
Proof. sf_field 8%nat 8%nat. Qed.
Lemma mrx_sf_src : val_mem sg mm (base + 16) 8 (TCt.sf_ptr fa f (DSpec.sf_src f)).
Proof. sf_field 16%nat 8%nat. Qed.
Lemma mrx_sf_retry : val_mem sg mm (base + 30) 2 (DSpec.sf_retry f).
Proof. sf_field 30%nat 2%nat. Qed.
Lemma mrx_sf_send : val_mem sg mm (base + 32) 4 (DSpec.sf_send f).
Proof. sf_field 32%nat 4%nat. Qed.
Lemma mrx_sf_ack : val_mem sg mm (base + 36) 4 (DSpec.sf_ack f).
Proof. sf_field 36%nat 4%nat. Qed.
Lemma mrx_sf_cmd : val_mem sg mm (base + 40) 1 (DSpec.sf_cmd f).
Proof. sf_field 40%nat 1%nat. Qed.
Lemma mrx_sf_body : val_mem sg mm (base + 48) 8 (TCt.sf_ptr fa f (DSpec.sf_body f)).
Proof. sf_field 48%nat 8%nat. Qed.
Lemma mrx_sf_blen : val_mem sg mm (base + 56) 8 (DSpec.sf_body_len f).
Proof. sf_field 56%nat 8%nat. Qed.

End sf.

(* A pointer field of the struct at SPEC_OK. *)
Lemma mrx_sf_ptr : forall fr n off, mrx_ok fr n -> TCt.sf_ptr (TI.tf_addr fr) (mrx_f fr n) off = TI.tf_addr fr + off.
Proof. intros fr n off (_ & Hok). unfold TCt.sf_ptr. rewrite Hok. reflexivity. Qed.

(* An option of a pair, inverted by name (never `injection` on a world-carrying option at a use site). *)
Lemma mrx_some_inv : forall (X Y : Type) (x x' : X) (y y' : Y), Some (x, y) = Some (x', y') -> x = x' /\ y = y'.
Proof. intros X Y x x' y y' H. injection H as -> ->. split; reflexivity. Qed.

(* The bytes the walk and its callees may store (m_rx_cg.v mrx_wr) are bytes of G. *)
Lemma mrx_row : forall o b n A w a, In (o, b, n) TMAP_B -> o <= A -> A + w <= o + n -> twb_fld o b A w a ->
  inG TG.G_HARNESS_B a.
Proof.
intros o b n A w a Hin H1 H2 Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr, twb_fld in *; cbn [fst snd]; lia].
Qed.

Lemma mrx_wr_G : forall a, mrx_wr a -> inG TG.G_HARNESS_B a.
Proof.
intros a H. unfold mrx_wr in H.
repeat (destruct H as [H | H];
  [ try (destruct H as (i & Hi & H));
    first [ refine (mrx_row _ _ _ _ _ _ TMAP_B_M _ _ H) | refine (mrx_row _ _ _ _ _ _ TMAP_B_OW _ _ H) ];
    first [ apply Z.leb_le; reflexivity
          | unfold TW.A_OW_t_state, TW.OW_t_ESZ, TW.OFF_OW, TW.SZ_OW, TC.TRANS_MAX in *; lia ] |]).
destruct H as (k & Hk & H). refine (mrx_row _ _ _ _ _ _ TMAP_B_OW _ _ H);
  unfold TC.A_OW_dn_body, TW.OFF_OW, TW.SZ_OW, TW.OW_dn_N in *; lia.
Qed.

(* ... and so below the shadow band and above the read-only bytes (G's hull is [0x5ded00, 0x5f2e10)). *)
Lemma mrx_wr_hull : forall a, mrx_wr a -> TG.G_HARNESS_B_LO <= a < TG.G_HARNESS_B_HI.
Proof. intros a H. exact (inG_G_HARNESS_hull a (mrx_wr_G a H)). Qed.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
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
rewrite Hb2. cbn [option_map]. f_equal. apply AK.mrx_bow; lia.
Qed.

(* The saved slots kept when their bytes are ([sp1 - 32, sp1)). *)
Lemma mrx_saved_kept : forall (Wc Wc' : world segs) mem mem' sp1 regs0,
  @mrx_saved Wc mem sp1 regs0 ->
  (forall a, sp1 - 32 <= a < sp1 -> aview segs (w_H Wc') mem' a = aview segs (w_H Wc) mem a) ->
  @mrx_saved Wc' mem' sp1 regs0.
Proof.
intros Wc Wc' mem mem' sp1 regs0 H K. unfold mrx_saved in *.
rewrite Forall_forall in *. intros ro Hro. specialize (H ro Hro).
apply (AK.mrx_rdword_kept _ _ _ _ H). intros i Hi. apply K.
unfold MRX_SAVES in Hro. unfold MRX_FRAME.
repeat (destruct Hro as [Hro | Hro]; [subst ro; cbn [snd]; lia |]). destruct Hro.
Qed.

(* The struct kept when its bytes are ([sp1 - 112, sp1 - 32)). *)
Lemma mrx_sf_kept : forall (Wc Wc' : world segs) mem mem' sp1 fr n,
  @mrx_sf Wc mem sp1 fr n ->
  (forall a, sp1 - MRX_FRAME <= a < sp1 - MRX_FRAME + 80 -> aview segs (w_H Wc') mem' a = aview segs (w_H Wc) mem a) ->
  @mrx_sf Wc' mem' sp1 fr n.
Proof.
intros Wc Wc' mem mem' sp1 fr n H K. unfold mrx_sf in *.
apply (garr8_frame segs _ _ _ _ H). intros a Ha. apply (mbyte_of_aview segs). apply K.
unfold TW.zs in Ha. rewrite length_map in Ha. rewrite (spec_read_frame_cg.srf_size_bytes) in Ha. unfold SRF_SIZE in Ha.
lia.
Qed.

(* The cut from its parts (a run's end, or a callee's return). *)
Lemma mrx_at_intro : forall sp1 regs0 lyc Sc (W : world segs) memc mdc pc R (Wc : world segs) Bwc ly2 S2 regs2 mem2 md2,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc mem2 md2 0 ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> mo_le MT Sc S2 0 ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regs2 3 = YK11.getr regs0 3 -> YK11.getr regs2 4 = YK11.getr regs0 4 ->
  mrx_hi regs0 regs2 ->
  @mrx_saved Wc mem2 sp1 regs0 ->
  tw_at TMAP_B (aview segs (w_H Wc) mem2) Bwc ->
  R Wc Bwc ly2 S2 regs2 mem2 ->
  @mrx_at fx rc B MT sp1 regs0 lyc Sc W memc mdc pc R Wc Bwc
    (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 pc) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros. exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

(* The bcmp wrapper called from a G journal (YCbq.v aj_bcmp_at through TransportGCg.v gx_call_leaf). *)
Lemma mrx_bcmp_gx : forall pc, abcmp_realizes segs B pc ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (o : Z) raw,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
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
      @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
      aregs_preserved regsT regs2 /\
      (YK11.getr regs2 10 = w64 0 <->
         forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
         aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
      (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw
  HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
apply (gx_call_leaf segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k _ raw
  (fun regs2 mem2 md2 =>
     aregs_preserved regsT regs2 /\
     (YK11.getr regs2 10 = w64 0 <->
        forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
        aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)) HJ).
intros memS HJi.
eapply SRr_mono.
{ exact (aj_bcmp_at segs B LAWS transportb_segs_low pc AM W regsT memT STK sp0 FP ly S W0 memS md own lyc Sc mdc k
    x y n o raw HJi Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy
    Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & Hc & HJ2 & HP & Hv & Hcmp & Hfr & Hgr).
split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|].
split; [exact HP|]. split; [rewrite Hv; exact Hcmp|]. split; [exact Hfr | exact Hgr].
Qed.

Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The premises every callee's contract takes of the machine at a `jal`'s target (return address BASE + k, sp =
   sp1 - 112). *)
Lemma mrx_pre : forall (sp1 : Z) (regsT : bvmap 5 word) (k : Z),
  sp1 mod 16 = 0 -> alloc_ceiling + MRX_STK <= sp1 -> sp1 <= 2 ^ 47 ->
  0 <= k < 2 ^ 40 -> k mod 2 = 0 ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + k) ->
  YK11.getr regsT 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK0s.ret_ok (YK11.getr regsT 1) /\ 4096 <= raZ regsT /\ spZ regsT = sp1 - MRX_FRAME /\
  spZ regsT mod 16 = 0 /\ sp1 - MRX_STK <= spZ regsT - HOFF_STK /\ spZ regsT <= sp1.
Proof.
intros sp1 regsT k Hsp16 Hceil H47 Hk Hk2 R1 R2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MRX_STK = MRX_FRAME + HOFF_STK) by reflexivity.
assert (FH : HOFF_STK = 80 + 2 * ESTACK) by reflexivity.
assert (EST : 0 <= ESTACK) by (unfold ESTACK; lia).
unfold MRX_FRAME in *.
assert (HB : BASE = 0x84c1c - 0x397c) by exact mrx_bval.
assert (HS2 : spZ regsT = sp1 - 112).
{ change (spZ regsT) with (bv_unsigned (YK11.getr regsT 2)).
  rewrite R2. apply unsigned_lit_small. lia. }
split; [rewrite R1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | exact Hk2]|].
split.
{ change (raZ regsT) with (bv_unsigned (YK11.getr regsT 1)).
  rewrite R1, unsigned_lit_small by lia. lia. }
split; [exact HS2|].
split; [rewrite HS2; replace (sp1 - 112) with (sp1 + (-7) * 16) by lia;
        rewrite Z_mod_plus_full; exact Hsp16|].
split; [rewrite HS2; lia | rewrite HS2; lia].
Qed.

(* What the next cut takes of the state after a callee's return: the saved slots (they lie above the callee's
   stack window and outside its written range), sp / gp / tp (callee-saved), and the frames, blocks and meter
   composed with the cut's. *)
Lemma mrx_next : forall (sp1 : Z) (regs0 : bvmap 5 word) lyc Sc (Wc W2 : world segs) memA mem3
    (regsT regs3 : bvmap 5 word) S2 S3 ly2 ly3 (FSTK : Z),
  0 <= FSTK -> FSTK <= MRX_STK - MRX_FRAME ->
  spZ regsT = sp1 - MRX_FRAME ->
  @mrx_saved Wc memA sp1 regs0 ->
  (forall a, sp1 - 32 <= a < sp1 -> aview segs (w_H W2) mem3 a = aview segs (w_H Wc) memA a) ->
  aregs_preserved regsT regs3 ->
  YK11.getr regsT 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regsT 3 = YK11.getr regs0 3 -> YK11.getr regsT 4 = YK11.getr regs0 4 ->
  mrx_hi regs0 regsT ->
  frames S2 = frames Sc -> frames S3 = frames S2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  mo_le MT Sc S2 0 -> mo_le MT S2 S3 0 ->
  @mrx_saved W2 mem3 sp1 regs0 /\
  YK11.getr regs3 2 = Z_to_bv 64 (sp1 - MRX_FRAME) /\
  YK11.getr regs3 3 = YK11.getr regs0 3 /\ YK11.getr regs3 4 = YK11.getr regs0 4 /\
  mrx_hi regs0 regs3 /\
  frames S3 = frames Sc /\ Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) /\ mo_le MT Sc S3 0.
Proof.
intros sp1 regs0 lyc Sc Wc W2 memA mem3 regsT regs3 S2 S3 ly2 ly3 FSTK HF0 HF1 HSP HSV K1 HP R2 R3 R4 RH F2 F3 P2 P3
  M2 M3.
split; [exact (mrx_saved_kept Wc W2 memA mem3 sp1 regs0 HSV K1)|].
split; [rewrite <- R2; exact (HP 2 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R3; exact (HP 3 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R4; exact (HP 4 ltac:(unfold acallee_saved; lia))|].
split; [intros q Hq; rewrite <- (RH q Hq); exact (HP q ltac:(unfold acallee_saved; lia))|].
split; [exact (eq_trans F3 F2)|].
split; [exact (Permutation_trans P3 P2)|].
exact (mle_station MT Sc S2 S3 0 0 MTL M2 M3).
Qed.

(* The frame facts at a later memory: the frame's bytes, the shadow band and the read-only bytes as they were (the
   placements read no memory: DgnTransportBCg.v trans_src_ok_view). *)
Lemma mrx_frs_view : forall fr ly2 S2 (Wc Wc' : world segs) mem mem',
  mrx_frs B fr ly2 S2 Wc mem ->
  (forall a, TI.tf_addr fr <= a < TI.tf_addr fr + mlen fr -> aview segs (w_H Wc') mem' a = aview segs (w_H Wc) mem a) ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H Wc') mem' s = aview segs (w_H Wc) mem s) ->
  (forall a, trans_in_ro_rd a -> aview segs (w_H Wc') mem' a = aview segs (w_H Wc) mem a) ->
  mrx_frs B fr ly2 S2 Wc' mem'.
Proof.
intros fr ly2 S2 Wc Wc' mem mem' (Hg & Hs & Hr) K1 K2 K3.
split; [|split].
- apply (garr8_frame segs _ _ _ _ Hg). intros a Ha. apply (mbyte_of_aview segs). apply K1.
  rewrite length_map in Ha. unfold AK.mlen. exact Ha.
- exact (trans_src_ok_view B ly2 S2 Wc Wc' mem mem' _ _ Hs K1 K2).
- intros a Ha. rewrite (K3 a Ha). exact (Hr a Ha).
Qed.

(* A run that changes only bytes of mrx_wr (the walk's own stores into M and OW) keeps the frame facts: the frame is
   apart from mrx_wr (mrx_apart), and mrx_wr lies in G, below the shadow band and above the read-only bytes. *)
Lemma mrx_frs_wr : forall fr ly2 S2 (Wc : world segs) mem mem',
  mrx_frs B fr ly2 S2 Wc mem -> mrx_apart fr -> 0 <= TI.tf_addr fr -> TI.tf_addr fr + mlen fr < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mrx_wr a -> aview segs (w_H Wc) mem' a = aview segs (w_H Wc) mem a) ->
  mrx_frs B fr ly2 S2 Wc mem'.
Proof.
intros fr ly2 S2 Wc mem mem' HF HAP H0 H64 K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfa : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + mlen fr -> 0 <= a < 2 ^ 64) by (intros a Ha; lia).
apply (mrx_frs_view fr ly2 S2 Wc Wc mem mem' HF).
- intros a Ha. apply K; [exact (Hfa a Ha)|]. intros Hw. exact (HAP a Hw Ha).
- intros s Hs'. apply K; [lia|]. intros Hw. pose proof (inG_G_HARNESS_hull s (mrx_wr_G s Hw)) as Gh.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Gh. lia.
- intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Rb. apply K; [lia|]. intros Hw.
  pose proof (inG_G_HARNESS_hull a (mrx_wr_G a Hw)) as Gh. unfold TG.G_HARNESS_B_LO in Gh. lia.
Qed.

End l.

(* ---- the model's range ---- *)
Abbreviation mrx_m_n := AK.mrx_m_n.
