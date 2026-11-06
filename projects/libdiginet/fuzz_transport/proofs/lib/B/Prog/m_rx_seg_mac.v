(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 757 of its 844 lines of code are new or changed and 943 lines of the source are left out. *)
(* m_rx_seg_mac: the segment MAC of the image-B walk of m_rx (statement lib/B/Prog/m_rx_cg.v, kit
   lib/B/Prog/m_rx_seg_kit.v), Lemma mrx_seg_mac: from the cut MAC (0x84c64, spec_read_frame gave SPEC_OK) to the cuts
   DESK (0x84cb4) and EPI (0x84c4c), through the three MAC compares (fuzz_transport.c:285-287; model mrxb_mac).
     +0x048 - +0x05c  s0 = f.src (the 8-byte load at sp + 16: fa + 6); a1 = HOST (object 6, 0x20fe0); a2 = 6; a0 = s0;
                      bcmp (fa + 6, HOST, 6), return address +0x060;
     +0x060           beqz a0: a0 = 0 (src = HOST) goes to the epilogue +0x030 with a0 = 0;
     +0x064 - +0x078  s1 = f.dst (the 8-byte load at sp + 8: fa); bcmp (fa, HOST, 6), return address +0x07c;
     +0x07c           beqz a0: a0 = 0 (dst = HOST) goes to DESK +0x098;
     +0x080 - +0x090  bcmp (fa, SPEC_BCAST (object 17, 0x21020), 6), return address +0x094;
     +0x094           bnez a0: a0 <> 0 goes to +0x02c (a0 = 0) and the epilogue; a0 = 0 (dst = SPEC_BCAST) goes on to
                      DESK.
   Each run is a symbolic run (TransportGRunB.v paj_run_x / paj_run_to_x) from a fresh state at the segment start or at
   a call's return address, whose one region is read-only: the struct's two pointer fields f.dst and f.src at sp + 8
   and sp + 16 (atom 32 = fa; their values fa + sf_dst = fa and fa + sf_src = fa + 6 at SPEC_OK, from the struct's
   garr8 by the kit's mrx_sf_dst / mrx_sf_src). So no run writes memory. Each call is the kit's mrx_bcmp_gx on the
   inner journal: the frame ranges [fa + 6, + 6) and [fa, + 6) are sub-ranges of the frame (n >= 30 at SPEC_OK), read
   ranges by the frame's trans_src_ok at the current state (DgnTransportBCg.v trans_src_ok_rd); HOST and SPEC_BCAST
   are TRANS_RO_RD bytes read through trans_rom_view_rd, and their aligned groups of 8 shadow bytes are constant cells
   of the record (transport_cells: HOST, DESK, SPEC_BCAST; trans_mrx_cells: SCALE's, HOST's, DESK's and SPEC_BCAST's
   guard bytes). A result 0 is exactly the model's beq_bytes (garr8 of the frame bytes; the image's HOST and
   SPEC_BCAST bytes are TCb's, decided by vm_compute). A call changes no byte outside its stack window
   [sp1 - 112 - 2 * ESTACK, sp1 - 112) and keeps the callee-saved registers, so the frame facts, the struct, the saved
   slots, the world relation and s2 hold at each successor cut. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_kit m_rx_seg_mac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRunB TransportGFrameB CanKit
YC1g YC1h m_rx_seg_kit.
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
Module AM := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_mac.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* A fresh state at offset pc of the listing: atoms 0 .. 31 the registers, 32 = fa; one read-only region, the
   struct's f.dst (sp + 8, value fa) and f.src (sp + 16, value fa + 6). *)
Definition MAC_RG : YP09.region :=
  YP09.mkRegion (Some 2%nat) 8 24 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 32 6))].
Definition mac_ss (pc : Z) : sstate := mkSS pc sr_atoms [MAC_RG] None (mkFacts [] [] []).
Definition MAC_SH : list shent := [].
Definition MAC_Bx : sv := SLit 0.
Definition mac_E {rc : YM05.RunCeil} (regs : bvmap 5 word) (fa : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 fa]).
(* The callee-saved registers run 1 keeps (all but s0), and run 2 (all but s1). *)
Definition MAC_KEEP1 : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition MAC_KEEP2 : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac mac_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mac_reg: no match for" T; fail
  end.

(* The write rights of a run whose one region is read-only. *)
Ltac mac_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* The closed bounds of a shadow hull hypothesis lo <= s < hi, computed. *)
Ltac mac_hull Hs :=
  lazymatch type of Hs with ?lo <= ?s < ?hi =>
    let lo' := eval vm_compute in lo in let hi' := eval vm_compute in hi in change (lo' <= s < hi') in Hs end.

(* ------------------------------------------------------------------ *)
(* Bytes, the model                                                    *)
(* ------------------------------------------------------------------ *)

(* The j-th byte of a garr8 array under the view. *)
Lemma mac_garr_view : forall (Wx : world tfibsegs) mem p (bs : list byte) j,
  garr8 tfibsegs (mrestrict (w_H Wx) mem) p (map DSpec.bz bs) -> (j < length bs)%nat ->
  aview tfibsegs (w_H Wx) mem (p + Z.of_nat j) = Some (bv_unsigned (nth j bs (Z_to_bv 8 0))).
Proof.
  intros Wx mem p bs j HG Hj.
  assert (Hj' : (j < length (map DSpec.bz bs))%nat) by (rewrite length_map; exact Hj).
  pose proof (garr8_mbyte tfibsegs _ p _ j HG Hj') as Hm.
  rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) in Hm by exact Hj'. rewrite map_nth in Hm.
  unfold aview. rewrite Hm. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold DSpec.bz.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* HOST's and SPEC_BCAST's six bytes in image B (fuzz_transport.c:109, spec.h:69; TCb.v HOST, SPEC_BCAST), decided
   over the loaded segments. *)
Lemma mac_host_rom : forall i, 0 <= i < 6 ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (TRANS_HOST + i)))
  = Some (bv_unsigned (nth (Z.to_nat i) TC.HOST (Z_to_bv 8 0))).
Proof.
  intros i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.
Lemma mac_bcast_rom : forall i, 0 <= i < 6 ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (TRANS_SPEC_BCAST + i)))
  = Some (bv_unsigned (nth (Z.to_nat i) TC.SPEC_BCAST (Z_to_bv 8 0))).
Proof.
  intros i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.

(* HOST and SPEC_BCAST lie in TRANS_RO_RD (their registered globals' payloads). *)
Lemma mac_host_ro : forall i, 0 <= i < 6 -> trans_in_ro_rd (TRANS_HOST + i).
Proof.
  intros i Hi. unfold trans_in_ro_rd, TRANS_RO_RD. apply Exists_exists. exists (TRANS_HOST, 6). split.
  - apply in_or_app. right. unfold TRANS_RO_GLOBALS. right. left. reflexivity.
  - unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma mac_bcast_ro : forall i, 0 <= i < 6 -> trans_in_ro_rd (TRANS_SPEC_BCAST + i).
Proof.
  intros i Hi. unfold trans_in_ro_rd, TRANS_RO_RD. apply Exists_exists. exists (TRANS_SPEC_BCAST, 6). split.
  - apply in_or_app. right. unfold TRANS_RO_GLOBALS. right. right. right. left. reflexivity.
  - unfold in_zr. cbn [fst snd]. lia.
Qed.

(* A one-byte constant cell of the record B, read at an AR state of image B (image A's m_rx_seg_mac.v mac_const1). *)
Lemma mac_const1 : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s = Some v.
Proof.
  intros rc B ly S W mem md a v s HAR Hin Hv <-.
  destruct HAR as (Mx & _).
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) _ Hin) as Hc.
  unfold cell_holds in Hc. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hc.
  specialize (Hc 0%nat ltac:(lia)). rewrite (AM.mac_le1 v Hv) in Hc.
  replace a with (a + Z.of_nat 0) by lia. exact Hc.
Qed.
Lemma mac_const1_nn : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s <> None.
Proof.
  intros rc B ly S W mem md a v s H1 H2 H3 H4. rewrite (mac_const1 B ly S W mem md a v s H1 H2 H3 H4). discriminate.
Qed.

(* The four cases of mrxb_mac (the three compares). *)
Lemma mac_m_src : forall I fr0 n0 Bx B' r0, TC.beq_bytes (mrxb_src fr0 n0) TC.HOST = true ->
  mrxb_mac I fr0 n0 Bx = Some (B', r0) -> B' = Bx /\ r0 = 0.
Proof.
  intros I fr0 n0 Bx B' r0 E1 H. unfold mrxb_mac in H. rewrite E1 in H. cbn [orb] in H.
  destruct (mrx_some_inv _ _ _ _ _ _ H) as [Ea Eb]. split; [exact (eq_sym Ea) | exact (eq_sym Eb)].
Qed.
Lemma mac_m_dsth : forall I fr0 n0 Bx B' r0, TC.beq_bytes (mrxb_src fr0 n0) TC.HOST = false ->
  TC.beq_bytes (mrxb_dst fr0 n0) TC.HOST = true ->
  mrxb_mac I fr0 n0 Bx = Some (B', r0) -> mrxb_desk I fr0 n0 Bx = Some (B', r0).
Proof.
  intros I fr0 n0 Bx B' r0 E1 E2 H. unfold mrxb_mac in H. rewrite E1, E2 in H. cbn [orb andb negb] in H. exact H.
Qed.
Lemma mac_m_bc_no : forall I fr0 n0 Bx B' r0, TC.beq_bytes (mrxb_src fr0 n0) TC.HOST = false ->
  TC.beq_bytes (mrxb_dst fr0 n0) TC.HOST = false -> TC.beq_bytes (mrxb_dst fr0 n0) TC.SPEC_BCAST = false ->
  mrxb_mac I fr0 n0 Bx = Some (B', r0) -> B' = Bx /\ r0 = 0.
Proof.
  intros I fr0 n0 Bx B' r0 E1 E2 E3 H. unfold mrxb_mac in H. rewrite E1, E2, E3 in H. cbn [orb andb negb] in H.
  destruct (mrx_some_inv _ _ _ _ _ _ H) as [Ea Eb]. split; [exact (eq_sym Ea) | exact (eq_sym Eb)].
Qed.
Lemma mac_m_bc_yes : forall I fr0 n0 Bx B' r0, TC.beq_bytes (mrxb_src fr0 n0) TC.HOST = false ->
  TC.beq_bytes (mrxb_dst fr0 n0) TC.HOST = false -> TC.beq_bytes (mrxb_dst fr0 n0) TC.SPEC_BCAST = true ->
  mrxb_mac I fr0 n0 Bx = Some (B', r0) -> mrxb_desk I fr0 n0 Bx = Some (B', r0).
Proof.
  intros I fr0 n0 Bx B' r0 E1 E2 E3 H. unfold mrxb_mac in H. rewrite E1, E2, E3 in H. cbn [orb andb negb] in H.
  exact H.
Qed.

(* The MAC fields of the frame at SPEC_OK: bytes 6 .. 11 (src) and 0 .. 5 (dst). *)
Lemma mac_src_eq : forall fr0 n0, mrx_ok fr0 n0 -> mrxb_src fr0 n0 = TW.sub (TI.tf_bytes fr0) 6 6.
Proof.
  intros fr0 n0 Hok. destruct (mrx_ok_fields fr0 n0 Hok) as (_ & Fs & _). unfold mrxb_src. rewrite Fs. reflexivity.
Qed.
Lemma mac_dst_eq : forall fr0 n0, mrx_ok fr0 n0 -> mrxb_dst fr0 n0 = TW.sub (TI.tf_bytes fr0) 0 6.
Proof.
  intros fr0 n0 Hok. destruct (mrx_ok_fields fr0 n0 Hok) as (Fd & _). unfold mrxb_dst. rewrite Fd. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HMRX : trans_mrx_cells B.
Hypothesis HRO : trans_ro_rd_unowned B.
Hypothesis HNE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS_B.
Hypothesis HGNE : gx_noerrno B TG.G_HARNESS_B.
Hypothesis HSRF : forall fx' : YK11.FPState, @transport_spec_read_frame_cg fx' rc B MT (transportb_sigma TB_spec_read_frame).
Hypothesis HBCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc tfibsegs B (transportb_sigma TB___interceptor_trampoline_bcmp).
Hypothesis HMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (transportb_sigma TB___asan_memcpy).
Hypothesis HHOFF : forall fx' : YK11.FPState, @transport_host_offset_cg fx' rc B MT (transportb_sigma TB_host_offset).
Hypothesis HMSET : forall fx' : YK11.FPState, @transport_m_set_cg fx' rc B MT (transportb_sigma TB_m_set).
Hypothesis HDN : forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transportb_sigma TB_desk_named).
Hypothesis HMW : forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transportb_sigma TB_m_wake).
Hypothesis HMO : forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transportb_sigma TB_m_maybe_online).
Hypothesis HMT : forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transportb_sigma TB_m_tick).
Variable sp1 : Z.
Variable regs0 : bvmap 5 word.
Variable lyc : alayout.
Variable Sc : astate.
Variable W : world tfibsegs.
Variable memc : word -> option byte.
Variable mdc : Model.
Variable fr : TI.tframe.
Variable n : Z.
Variable Bw' : list byte.
Variable r : Z.
Hypothesis HST : mrx_static B sp1 regs0 lyc Sc W memc mdc fr n.
Local Notation K := (@mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).

Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Local Abbreviation IPOST := (@mrx_ipost fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Local Abbreviation fa := (TI.tf_addr fr).

(* The image objects and the pcs: object 6 is HOST, object 17 SPEC_BCAST; the segment's pcs (offsets from the
   listing's base, m_rx at 0x397c = 14716): MAC +0x048 = 14788, EPI +0x030 = 14764, DESK +0x098 = 14868. *)
Lemma mac_vals : VAL (A_OBJ 6) = TRANS_HOST /\ VAL (A_OBJ 17) = TRANS_SPEC_BCAST /\
  BASE + 14788 = MRX_PC OFF_MAC /\ BASE + 14764 = MRX_PC OFF_EPI /\ BASE + 14868 = MRX_PC OFF_DESK.
Proof. vm_compute. repeat split. Qed.

(* ---- valuations ---- *)

Lemma mac_E32 : forall regs v, ew (mac_E regs v) 32 = w64 v.
Proof. intros regs v. unfold mac_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.

Lemma mac_den : forall regs v c, 0 <= v < 2 ^ 64 -> sv_denot (mac_E regs v) (SOff 32 c) = w64 (v + c).
Proof.
  intros regs v c Hv. cbn [sv_denot]. rewrite mac_E32. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma mac_den0 : forall regs v, 0 <= v < 2 ^ 64 -> sv_denot (mac_E regs v) (SOff 32 0) = w64 v.
Proof. intros regs v Hv. rewrite (mac_den regs v 0 Hv), Z.add_0_r. reflexivity. Qed.

Lemma mac_sv_reg : forall regs v k (q : bv 5) x, Z.of_nat k = bv_unsigned q -> YK11.getr regs q = w64 x ->
  0 <= x < 2 ^ 64 -> sv_denot (mac_E regs v) (SOff k 0) = w64 x.
Proof.
  intros regs v k q x Hk Hq Hx. cbn [sv_denot]. unfold mac_E. rewrite (ew_Eimg_Ereg_nat regs _ k q Hk), Hq.
  unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma mac_sv_obj : forall regs v k x, (A_TEXT <= k < A_LIM)%nat -> VAL k = x -> 0 <= x < 2 ^ 64 ->
  sv_denot (mac_E regs v) (SOff k 0) = w64 x.
Proof.
  intros regs v k x Hk Hv Hr. cbn [sv_denot]. unfold mac_E. rewrite Eimg_img by exact Hk. rewrite Hv.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma mac_sv_a0 : forall regs v, sv_denot (mac_E regs v) (SOff 10 0) = YK11.getr regs (Z_to_bv 5 10).
Proof.
  intros regs v. cbn [sv_denot]. unfold mac_E. rewrite (ew_Eimg_Ereg_nat regs _ 10 (Z_to_bv 5 10) eq_refl).
  rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma mac_agree : forall regs v, env_agree 32 (Ereg regs [w64 v]) (mac_E regs v).
Proof. intros regs v. split; [intros k Hk; unfold mac_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma mac_img : forall regs v, img_env VAL A_LIM (mac_E regs v).
Proof. intros regs v. unfold mac_E. apply Eimg_env. Qed.

(* The two branches on a0 (beqz / bnez). *)
Lemma mac_br_eq : forall regs v,
  branch_taken BC_EQ (sv_denot (mac_E regs v) (SOff 10 0)) (sv_denot (mac_E regs v) (SLit 0)) = true <->
  YK11.getr regs 10 = w64 0.
Proof. intros regs v. cbn [branch_taken]. rewrite mac_sv_a0. cbn [sv_denot]. exact (AM.mac_eqb0 _). Qed.
Lemma mac_br_ne : forall regs v,
  branch_taken BC_NE (sv_denot (mac_E regs v) (SOff 10 0)) (sv_denot (mac_E regs v) (SLit 0)) = true <->
  YK11.getr regs 10 <> w64 0.
Proof.
  intros regs v. cbn [branch_taken]. rewrite mac_sv_a0. cbn [sv_denot]. rewrite negb_true_iff.
  pose proof (AM.mac_eqb0 (YK11.getr regs (Z_to_bv 5 10))) as Q.
  destruct (bv_eqb (YK11.getr regs (Z_to_bv 5 10)) (Z_to_bv 64 0)).
  - split; [discriminate | intros N; exfalso; apply N; exact (proj1 Q eq_refl)].
  - split; [intros _ Z0; apply Q in Z0; discriminate Z0 | reflexivity].
Qed.
Lemma mac_br_eq_f : forall regs v,
  branch_taken BC_EQ (sv_denot (mac_E regs v) (SOff 10 0)) (sv_denot (mac_E regs v) (SLit 0)) = false ->
  YK11.getr regs 10 <> w64 0.
Proof. intros regs v H E. apply (proj2 (mac_br_eq regs v)) in E. rewrite E in H. discriminate H. Qed.
Lemma mac_br_ne_f : forall regs v,
  branch_taken BC_NE (sv_denot (mac_E regs v) (SOff 10 0)) (sv_denot (mac_E regs v) (SLit 0)) = false ->
  YK11.getr regs 10 = w64 0.
Proof.
  intros regs v H. destruct (bv_eqb (YK11.getr regs 10) (Z_to_bv 64 0)) eqn:Q.
  - exact (proj1 (AM.mac_eqb0 _) Q).
  - exfalso. assert (N : YK11.getr regs 10 <> w64 0) by (intros Z0; apply (proj2 (AM.mac_eqb0 _)) in Z0; congruence).
    apply (proj2 (mac_br_ne regs v)) in N. rewrite N in H. discriminate H.
Qed.

(* The fresh state at offset pc, from a machine at BASE + pc whose sp is p, with the struct's two pointer fields. *)
Lemma mac_entry : forall (H : word -> bool) regs mem pc v p,
  spZ regs = p -> 0 <= p -> p + 24 <= 2 ^ 64 -> 0 <= v -> v + 6 < 2 ^ 64 ->
  val_mem segs (mrestrict H mem) (p + 8) 8 v -> val_mem segs (mrestrict H mem) (p + 16) 8 (v + 6) ->
  st_ok_pi segs VAL (mac_E regs v) (mac_ss pc)
    (restrict H (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros H regs mem pc v p Hsp Hp0 Hp1 Hv0 Hv1 V8 V16.
  assert (U2 : bv_unsigned (ew (mac_E regs v) 2) = p)
    by (unfold mac_E; rewrite (ew_Eimg_Ereg_nat regs [w64 v] 2 2%bv eq_refl); exact Hsp).
  rewrite restrict_mkst_fx. unfold mac_ss.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - unfold mac_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold MAC_RG, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val segs _ _ p 8 8 (SOff 32 0) v);
        [exact (mac_den0 regs v ltac:(lia)) | cbn; lia | cbn; lia | exact V8].
    + apply (chunk_ok_val segs _ _ p 16 8 (SOff 32 6) (v + 6));
        [exact (mac_den regs v 6 ltac:(lia)) | cbn; lia | cbn; lia | exact V16].
  - exact (conj I I).
  - exact (conj I (conj I I)).
Qed.

(* The static facts. *)
Lemma mac_geo : 2 ^ 46 <= sp1 - MRX_STK /\ sp1 <= 2 ^ 47 /\ MRX_STK = 8384 /\ MRX_FRAME = 112 /\ ESTACK = 4096 /\
  0 < fa /\ fa + mlen fr < 2 ^ 64 /\ (fa + mlen fr <= sp1 - MRX_STK \/ sp1 <= fa).
Proof.
  pose proof HST as (_ & _ & _ & H46 & H47 & _ & _ & _ & _ & _ & _ & Hfa0 & _ & Hfam & _ & Hpl & _).
  split; [exact H46|]. split; [exact H47|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hfa0|]. split; [exact Hfam | exact Hpl].
Qed.

Section cut.
Variable Wc : world segs.
Variable Bwc : list byte.
Variable ly2 : alayout.
Variable S2 : astate.
Variable regs2 : bvmap 5 word.
Variable mem2 : word -> option byte.
Hypothesis KE : K (MRX_PC OFF_EPI) (R_EPI Bw' r).
Hypothesis KD : K (MRX_PC OFF_DESK) (R_DESK B fr n sp1 Bw' r).
Hypothesis HFR : frames S2 = frames Sc.
Hypothesis HPM : Permutation (ablocks B ly2 S2) (ablocks B lyc Sc).
Hypothesis HMO2 : mo_le MT Sc S2 0.
Hypothesis H2 : YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME).
Hypothesis H3 : YK11.getr regs2 3 = YK11.getr regs0 3.
Hypothesis H4 : YK11.getr regs2 4 = YK11.getr regs0 4.
Hypothesis HHI : mrx_hi regs0 regs2.
Hypothesis HSV : mrx_saved Wc mem2 sp1 regs0.
Hypothesis HTW : tw_at TMAP_B (aview segs (w_H Wc) mem2) Bwc.
Hypothesis HCUR : mrx_cur B fr n sp1 ly2 S2 Wc mem2.
Hypothesis H18 : YK11.getr regs2 18 = w64 SHADOW_OFF.
Hypothesis HM : mrxb_mac timg_B fr n Bwc = Some (Bw', r).

(* The inner journal at the cut's state and the memory m. *)
Local Abbreviation MJ m md :=
  (@W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc
     m md 0).

(* The stack window below the frame: the only bytes a call may change. *)
Definition mac_win (a : Z) : Prop := sp1 - MRX_STK <= a < sp1 - MRX_FRAME.
(* The view at m is the cut's outside that window. *)
Definition mac_KV (m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ mac_win a -> aview segs (w_H Wc) m a = aview segs (w_H Wc) mem2 a.
(* The callee-saved registers but s0 and s1 are the cut's; then s0 = fa + 6; then s1 = fa. *)
Definition mac_rgA (regs : bvmap 5 word) : Prop :=
  forall q, acallee_saved q -> q <> 8 -> q <> 9 -> YK11.getr regs (Z_to_bv 5 q) = YK11.getr regs2 (Z_to_bv 5 q).
Definition mac_rg1 (regs : bvmap 5 word) : Prop :=
  mac_rgA regs /\ YK11.getr regs (Z_to_bv 5 8) = w64 (fa + 6).
Definition mac_rg2 (regs : bvmap 5 word) : Prop :=
  mac_rg1 regs /\ YK11.getr regs (Z_to_bv 5 9) = w64 fa.

Ltac mac_lia := unfold mac_win, TRANS_HOST, TRANS_SPEC_BCAST in *; lia.

Lemma mac_rgA_pres : forall r1 r2, mac_rgA r1 -> aregs_preserved r1 r2 -> mac_rgA r2.
Proof. intros r1 r2 RG HP q Hq H8 H9. rewrite (HP q Hq). exact (RG q Hq H8 H9). Qed.
Lemma mac_rg1_pres : forall r1 r2, mac_rg1 r1 -> aregs_preserved r1 r2 -> mac_rg1 r2.
Proof.
  intros r1 r2 (RG & R8) HP. split; [exact (mac_rgA_pres r1 r2 RG HP)|].
  rewrite (HP 8 ltac:(unfold acallee_saved; lia)). exact R8.
Qed.
Lemma mac_rg2_pres : forall r1 r2, mac_rg2 r1 -> aregs_preserved r1 r2 -> mac_rg2 r2.
Proof.
  intros r1 r2 (RG & R9) HP. split; [exact (mac_rg1_pres r1 r2 RG HP)|].
  rewrite (HP 9 ltac:(unfold acallee_saved; lia)). exact R9.
Qed.
Lemma mac_rg1_A : forall r1, mac_rg1 r1 -> mac_rgA r1.
Proof. intros r1 (RG & _). exact RG. Qed.

(* The registers the cuts take, from mac_rgA. *)
Lemma mac_rgA_regs : forall regs, mac_rgA regs ->
  YK11.getr regs 2 = Z_to_bv 64 (sp1 - MRX_FRAME) /\ YK11.getr regs 3 = YK11.getr regs0 3 /\
  YK11.getr regs 4 = YK11.getr regs0 4 /\ mrx_hi regs0 regs /\ YK11.getr regs 18 = w64 SHADOW_OFF.
Proof.
  intros regs RG.
  split; [exact (eq_trans (RG 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) H2)|].
  split; [exact (eq_trans (RG 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) H3)|].
  split; [exact (eq_trans (RG 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) H4)|].
  split; [|exact (eq_trans (RG 18 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) H18)].
  intros q Hq. rewrite (RG q ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)). exact (HHI q Hq).
Qed.

(* n >= 30 at SPEC_OK, and n <= the frame's length. *)
Lemma mac_n : 30 <= n /\ n <= mlen fr.
Proof.
  pose proof HCUR as (Hok & _ & _). pose proof Hok as ((_ & Hn) & _).
  destruct (mrx_ok_fields fr n Hok) as (_ & _ & _ & H30 & _). split; [exact H30 | exact Hn].
Qed.

(* ---- what the view keeps ---- *)

Lemma mac_frs_kept : forall m, mac_KV m -> mrx_frs B fr ly2 S2 Wc m.
Proof.
  intros m KV. pose proof HCUR as (_ & HFRS & _).
  pose proof mac_geo as (SP1 & SP2 & STK & FRM & EST & F0 & F64 & FP).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (mrx_frs_view B fr ly2 S2 Wc Wc mem2 m HFRS).
  - intros a Ha. apply KV; mac_lia.
  - intros s Hs. apply KV; unfold kLowMemEnd, kHighShadowEnd in *; mac_lia.
  - intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Hl. apply KV; mac_lia.
Qed.

Lemma mac_sf_at : forall m, mac_KV m -> mrx_sf Wc m sp1 fr n.
Proof.
  intros m KV. pose proof HCUR as (_ & _ & HSF). pose proof mac_geo as (SP1 & SP2 & STK & FRM & EST & _).
  apply (mrx_sf_kept Wc Wc mem2 m sp1 fr n HSF). intros a Ha. apply KV; mac_lia.
Qed.

Lemma mac_saved : forall m, mac_KV m -> mrx_saved Wc m sp1 regs0.
Proof.
  intros m KV. pose proof mac_geo as (SP1 & SP2 & STK & FRM & EST & _).
  apply (mrx_saved_kept Wc Wc mem2 m sp1 regs0 HSV). intros a Ha. apply KV; mac_lia.
Qed.

Lemma mac_tw : forall m, mac_KV m -> tw_at TMAP_B (aview segs (w_H Wc) m) Bwc.
Proof.
  intros m KV. pose proof mac_geo as (SP1 & SP2 & STK & FRM & EST & _).
  apply (tw_kept TMAP_B (aview segs (w_H Wc) mem2)); [exact HTW|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KV; mac_lia.
Qed.

Lemma mac_cur : forall m, mac_KV m -> mrx_cur B fr n sp1 ly2 S2 Wc m.
Proof.
  intros m KV. pose proof HCUR as (Hok & _ & _).
  split; [exact Hok|]. split; [exact (mac_frs_kept m KV) | exact (mac_sf_at m KV)].
Qed.

(* The struct's f.dst and f.src at sp1 - 112 + 8 and + 16: fa and fa + 6. *)
Lemma mac_sfv : forall m, mac_KV m ->
  val_mem segs (mrestrict (w_H Wc) m) (sp1 - MRX_FRAME + 8) 8 fa /\
  val_mem segs (mrestrict (w_H Wc) m) (sp1 - MRX_FRAME + 16) 8 (fa + 6).
Proof.
  intros m KV. pose proof (mac_sf_at m KV) as HSF. unfold mrx_sf in HSF.
  pose proof HCUR as (Hok & _ & _).
  destruct (mrx_ok_fields fr n Hok) as (Fd & Fs & _).
  pose proof (mrx_sf_dst _ _ _ _ HSF) as V8. pose proof (mrx_sf_src _ _ _ _ HSF) as V16.
  rewrite (mrx_sf_ptr fr n _ Hok), Fd, Z.add_0_r in V8.
  rewrite (mrx_sf_ptr fr n _ Hok), Fs in V16.
  split; [exact V8 | exact V16].
Qed.

(* The fresh state at a pc of the segment. *)
Lemma mac_entry_at : forall regs m pc, mac_rgA regs -> mac_KV m ->
  st_ok_pi segs VAL (mac_E regs fa) (mac_ss pc)
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) m (YK11.seg_rom segs))).
Proof.
  intros regs m pc RG KV.
  pose proof mac_geo as (SP1 & SP2 & STK & FRM & EST & F0 & F64 & FP). pose proof mac_n as (N30 & NL).
  pose proof (mac_rgA_regs regs RG) as (R2 & _).
  assert (HSP : spZ regs = sp1 - MRX_FRAME)
    by (unfold spZ; rewrite R2; apply unsigned_lit_small; rewrite FRM; lia).
  destruct (mac_sfv m KV) as (V8 & V16).
  apply (mac_entry (w_H Wc) regs m pc fa (sp1 - MRX_FRAME) HSP); [lia | lia | lia | lia | exact V8 | exact V16].
Qed.

(* ---- the bytes the compares read ---- *)

Lemma mac_frame_view : forall m, mac_KV m -> forall j, 0 <= j < mlen fr ->
  aview segs (w_H Wc) m (fa + j) = Some (bv_unsigned (nth (Z.to_nat j) (TI.tf_bytes fr) (Z_to_bv 8 0))).
Proof.
  intros m KV j Hj. pose proof (mac_frs_kept m KV) as (G & _ & _).
  replace (fa + j) with (fa + Z.of_nat (Z.to_nat j)) by lia.
  apply (mac_garr_view Wc m fa (TI.tf_bytes fr) (Z.to_nat j) G). unfold AK.mlen in Hj. lia.
Qed.

Lemma mac_host_view : forall m, mac_KV m -> forall i, 0 <= i < 6 ->
  aview segs (w_H Wc) m (TRANS_HOST + i) = Some (bv_unsigned (nth (Z.to_nat i) TC.HOST (Z_to_bv 8 0))).
Proof.
  intros m KV i Hi. pose proof (mac_frs_kept m KV) as (_ & _ & ROM).
  rewrite (ROM _ (mac_host_ro i Hi)). exact (mac_host_rom i Hi).
Qed.

Lemma mac_bcast_view : forall m, mac_KV m -> forall i, 0 <= i < 6 ->
  aview segs (w_H Wc) m (TRANS_SPEC_BCAST + i) = Some (bv_unsigned (nth (Z.to_nat i) TC.SPEC_BCAST (Z_to_bv 8 0))).
Proof.
  intros m KV i Hi. pose proof (mac_frs_kept m KV) as (_ & _ & ROM).
  rewrite (ROM _ (mac_bcast_ro i Hi)). exact (mac_bcast_rom i Hi).
Qed.

(* The compare of [x, + 6) (x = fa + k) with [y, + 6) holding l is the model's beq_bytes. *)
Lemma mac_cmp : forall m x y k (l : list byte), mac_KV m -> x = fa + k -> 0 <= k -> k + 6 <= mlen fr ->
  length l = 6%nat ->
  (forall i, 0 <= i < 6 -> aview segs (w_H Wc) m (y + i) = Some (bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0)))) ->
  ((forall i, 0 <= i < 6 -> aview segs (w_H Wc) m (x + i) = aview segs (w_H Wc) m (y + i)) <->
   TC.beq_bytes (TW.sub (TI.tf_bytes fr) k 6) l = true).
Proof.
  intros m x y k l KV -> Hk Hk6 Hl HY.
  assert (LS : length (TW.sub (TI.tf_bytes fr) k 6) = 6%nat)
    by (apply TWL.length_sub; unfold AK.mlen in Hk6; lia).
  assert (FV : forall i, 0 <= i < 6 ->
    aview segs (w_H Wc) m (fa + k + i) = Some (bv_unsigned (nth (Z.to_nat i) (TW.sub (TI.tf_bytes fr) k 6) (Z_to_bv 8 0)))).
  { intros i Hi. replace (fa + k + i) with (fa + (k + i)) by lia.
    rewrite (mac_frame_view m KV (k + i) ltac:(lia)).
    rewrite (tw_nth_sub (TI.tf_bytes fr) k 6 (Z.to_nat i) (Z_to_bv 8 0)) by (unfold AK.mlen in Hk6; lia).
    do 3 f_equal. lia. }
  rewrite UMR.mr_beq_iff, (AM.mac_zs6 _ _ LS Hl).
  split; intros H i Hi.
  - specialize (H i Hi). rewrite (FV i Hi), (HY i Hi) in H. injection H as H. exact H.
  - rewrite (FV i Hi), (HY i Hi). f_equal. exact (H i Hi).
Qed.

(* ---- the ranges the compares read, as read ranges ---- *)

Lemma mac_rd_frame : forall m md x k, MJ m md -> mac_KV m -> x = fa + k -> 0 <= k -> k + 6 <= mlen fr ->
  decode_rd_ok Wc m x 6.
Proof.
  intros m md x k HJ KV -> Hk Hk6. pose proof (mac_frs_kept m KV) as (_ & HS & _). pose proof mac_n as (N30 & NL).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof (trans_src_ok_rd B LAWS ly2 S2 Wc m md fa (mlen fr) HAR HS ltac:(lia)) as RD.
  exact (trans_rd_ok_sub Wc m fa (mlen fr) (fa + k) 6 RD ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma mac_rd_host : forall m md, MJ m md -> mac_KV m -> decode_rd_ok Wc m TRANS_HOST 6.
Proof.
  intros m md HJ KV.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  destruct (HCELLS ly2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RH & _).
  destruct HMRX as (_ & _ & HC). destruct (HC ly2) as (S32 & S40 & S48 & S56 & RH8 & RH16 & RH24 & _).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. replace a with (TRANS_HOST + (a - TRANS_HOST)) by lia.
    rewrite (mac_host_view m KV (a - TRANS_HOST) ltac:(lia)). discriminate.
  - intros x Hx. exists 6. split.
    + eapply (mac_const1 B ly2 S2 Wc m md); [exact HAR | exact RH | lia |].
      unfold BCells.shadow_addr, BCells.ASAN_K, TRANS_HOST, shadow_of_addr, SHADOW_OFF in *.
      Z.div_mod_to_equations. lia.
    + unfold saddr_ok, TRANS_HOST in *. right. Z.div_mod_to_equations. lia.
  - intros s' Hs. mac_hull Hs.
    assert (Hc : s' = 0x7fffc1f8 \/ s' = 0x7fffc1f9 \/ s' = 0x7fffc1fa \/ s' = 0x7fffc1fb \/ s' = 0x7fffc1fc \/
                 s' = 0x7fffc1fd \/ s' = 0x7fffc1fe \/ s' = 0x7fffc1ff) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ eapply mac_const1_nn; [exact HAR | exact S32 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact S40 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact S48 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact S56 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RH | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RH8 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RH16 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RH24 | lia | reflexivity] ].
  - unfold amem_range, kLowMemEnd, TRANS_HOST. lia.
  - unfold TRANS_HOST. lia.
  - unfold TRANS_HOST. lia.
Qed.

Lemma mac_rd_bcast : forall m md, MJ m md -> mac_KV m -> decode_rd_ok Wc m TRANS_SPEC_BCAST 6.
Proof.
  intros m md HJ KV.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  destruct (HCELLS ly2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RD & RB & _).
  destruct HMRX as (_ & _ & HC).
  destruct (HC ly2) as (_ & _ & _ & _ & _ & _ & _ & RD8 & RD16 & RD24 & RB8 & RB16 & RB24 & _).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. replace a with (TRANS_SPEC_BCAST + (a - TRANS_SPEC_BCAST)) by lia.
    rewrite (mac_bcast_view m KV (a - TRANS_SPEC_BCAST) ltac:(lia)). discriminate.
  - intros x Hx. exists 6. split.
    + eapply (mac_const1 B ly2 S2 Wc m md); [exact HAR | exact RB | lia |].
      unfold BCells.shadow_addr, BCells.ASAN_K, TRANS_SPEC_BCAST, shadow_of_addr, SHADOW_OFF in *.
      Z.div_mod_to_equations. lia.
    + unfold saddr_ok, TRANS_SPEC_BCAST in *. right. Z.div_mod_to_equations. lia.
  - intros s' Hs. mac_hull Hs.
    assert (Hc : s' = 0x7fffc200 \/ s' = 0x7fffc201 \/ s' = 0x7fffc202 \/ s' = 0x7fffc203 \/ s' = 0x7fffc204 \/
                 s' = 0x7fffc205 \/ s' = 0x7fffc206 \/ s' = 0x7fffc207) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ eapply mac_const1_nn; [exact HAR | exact RD | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RD8 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RD16 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RD24 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RB | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RB8 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RB16 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RB24 | lia | reflexivity] ].
  - unfold amem_range, kLowMemEnd, TRANS_SPEC_BCAST. lia.
  - unfold TRANS_SPEC_BCAST. lia.
  - unfold TRANS_SPEC_BCAST. lia.
Qed.

(* ---- a read-only run's memory ---- *)

Lemma mac_KV_ext : forall m m', mac_KV m -> (forall x, m' x = m x) -> mac_KV m'.
Proof.
  intros m m' KV E a Ha Hw. rewrite <- (KV a Ha Hw). unfold aview, YP09.mbyte, mrestrict. rewrite E. reflexivity.
Qed.

(* The memory after a run of the segment (its one region is read-only) is the memory before it. *)
Lemma mac_ro_mem : forall E (m m' : word -> option byte), frame_of E [MAC_RG] m m' -> forall x, m' x = m x.
Proof. intros E m m' HF. exact (frame_of_ro E [MAC_RG] m m' eq_refl HF). Qed.

(* ---- the exits ---- *)

Lemma mac_exit_epi : forall regs m md, MJ m md -> mac_rgA regs -> mac_KV m ->
  YK11.getr regs 10 = w64 0 -> Bw' = Bwc -> r = 0 ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (MRX_PC OFF_EPI)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md HJ RG KV R10 EB Er.
  pose proof (mac_rgA_regs regs RG) as (R2 & R3 & R4 & RHI & _).
  apply (KE Wc Bwc).
  apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_EPI) (R_EPI Bw' r) Wc Bwc ly2 S2 regs m md HJ
    HFR HPM HMO2 R2 R3 R4 RHI (mac_saved m KV) (mac_tw m KV)).
  unfold R_EPI. split; [exact (eq_sym EB) | rewrite Er; exact R10].
Qed.

Lemma mac_exit_desk : forall regs m md, MJ m md -> mac_rg1 regs -> mac_KV m ->
  mrxb_desk timg_B fr n Bwc = Some (Bw', r) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (MRX_PC OFF_DESK)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md HJ (RG & R8) KV HD.
  pose proof (mac_rgA_regs regs RG) as (R2 & R3 & R4 & RHI & R18).
  apply (KD Wc Bwc).
  apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_DESK) (R_DESK B fr n sp1 Bw' r) Wc Bwc ly2 S2
    regs m md HJ HFR HPM HMO2 R2 R3 R4 RHI (mac_saved m KV) (mac_tw m KV)).
  unfold R_DESK. split; [exact (mac_cur m KV)|]. split; [exact R8|]. split; [exact R18 | exact HD].
Qed.

(* ---- one call of the bcmp wrapper (the kit's mrx_bcmp_gx) ---- *)

Lemma mac_bcmp : forall (P : bvmap 5 word -> Prop),
  (forall r1 r2, P r1 -> aregs_preserved r1 r2 -> P r2) -> (forall r1, P r1 -> mac_rgA r1) ->
  forall (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model) (x y : Z) (raw : word)
    (Q : world segs -> config -> Prop),
  MJ memT mdT -> P regsT -> mac_KV memT ->
  YK11.getr regsT 10 = w64 x -> YK11.getr regsT 11 = w64 y -> YK11.getr regsT 12 = w64 6 ->
  decode_rd_ok Wc memT x 6 -> decode_rd_ok Wc memT y 6 ->
  (x + 6 <= sp1 - MRX_STK \/ sp1 <= x) -> (y + 6 <= sp1 - MRX_STK \/ sp1 <= y) ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall regs3 mem3 md3, MJ mem3 md3 -> P regs3 -> mac_KV mem3 ->
     (YK11.getr regs3 10 = w64 0 <->
        forall i, 0 <= i < 6 -> aview segs (w_H Wc) memT (x + i) = aview segs (w_H Wc) memT (y + i)) ->
     SRr segs Wc (mkCfg (@YK11.mkst fx regs3 raw mem3 (YK11.seg_rom segs)) md3) Q) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) memT
    (YK11.seg_rom segs)) mdT) Q.
Proof.
  intros P HPP HPA regsT memT mdT x y raw Q HJ HP KV R10 R11 R12 RDX RDY OFX OFY R1 HRAW KK.
  pose proof (mac_rgA_regs regsT (HPA regsT HP)) as (R2 & R3 & R4 & _).
  pose proof mac_geo as (SP1 & SP2 & STK & FRM & EST & _).
  pose proof RDX as (HvX & HraX & HhX & HmX & H0X & H63X).
  pose proof RDY as (HvY & HraY & HhY & HmY & H0Y & H63Y).
  pose proof HST as (_ & _ & _ & _ & _ & _ & _ & Hg0 & Ht0 & _).
  assert (HspT : spZ regsT = sp1 + -112)
    by (unfold spZ; rewrite R2; rewrite unsigned_lit_small; [rewrite FRM; lia | rewrite FRM; lia]).
  assert (R3' : YK11.getr regsT 3 = w64 (as_gp B)) by (rewrite <- Hg0; exact R3).
  assert (R4' : YK11.getr regsT 4 = w64 (as_tp B)) by (rewrite <- Ht0; exact R4).
  assert (SX : src_ok segs Wc regsT memT x 6)
    by (intros a Ha; split; [exact (HvX a Ha) | rewrite HspT; lia]).
  assert (SY : src_ok segs Wc regsT memT y 6)
    by (intros a Ha; split; [exact (HvY a Ha) | rewrite HspT; lia]).
  assert (BX : forall a, x <= a < x + 6 -> ~ (sp1 + -112 - 2 * ESTACK <= a < sp1 + -112)) by (intros a Ha; lia).
  assert (BY : forall a, y <= a < y + 6 -> ~ (sp1 + -112 - 2 * ESTACK <= a < sp1 + -112)) by (intros a Ha; lia).
  eapply SRr_bind.
  { exact (mrx_bcmp_gx B LAWS _ (HBCMP fx) Wc regsT memT MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 mdT 0 x y 6 (-112)
      raw HJ R10 R11 R12 ltac:(lia) H0X H63X H0Y H63Y HspT eq_refl ltac:(lia) ltac:(lia)
      R3' R4' R1 HRAW SX SY BX BY HmX HmY HraX (fun _ => HhX) HraY (fun _ => HhY)). }
  cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hiff & Hview & _).
  apply (KK regs3 mem3 md3 HJ3 (HPP regsT regs3 HP HP3)); [|exact Hiff].
  intros a Ha Hw. rewrite (Hview a Ha ltac:(unfold mac_win in Hw; lia)). exact (KV a Ha Hw).
Qed.

(* ---- the phases ---- *)

(* After the third call (+0x094, bnez a0): a0 <> 0 goes to +0x02c (a0 = 0) and the epilogue; a0 = 0 to DESK. *)
Lemma mac_p3 : forall regs m md, MJ m md -> mac_rg1 regs -> mac_KV m ->
  TC.beq_bytes (mrxb_src fr n) TC.HOST = false -> TC.beq_bytes (mrxb_dst fr n) TC.HOST = false ->
  (YK11.getr regs 10 = w64 0 <-> TC.beq_bytes (mrxb_dst fr n) TC.SPEC_BCAST = true) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14864)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md HJ RG KV E1 E2 IFF.
  destruct mac_vals as (_ & _ & _ & PEPI & PDESK).
  pose proof (mac_img regs fa) as HEI. pose proof (mac_agree regs fa) as AG.
  pose proof (mac_entry_at regs m 14864 (mac_rg1_A regs RG) KV) as HS.
  assert (SHOK : sh_ok segs MAC_Bx MAC_SH (mac_E regs fa) (mrestrict (w_H Wc) m))
    by (unfold sh_ok, MAC_SH; apply Forall_nil).
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUNTO.
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUN.
  pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* a0 <> 0: dst is not SPEC_BCAST; +0x02c a0 = 0, then the epilogue *)
    apply (proj1 (mac_br_ne regs fa)) in Hc.
    assert (E3 : TC.beq_bytes (mrxb_dst fr n) TC.SPEC_BCAST = false).
    { destruct (TC.beq_bytes (mrxb_dst fr n) TC.SPEC_BCAST) eqn:E3; [|reflexivity].
      exfalso. apply Hc. apply IFF. reflexivity. }
    destruct (mac_m_bc_no _ _ _ _ _ _ E1 E2 E3 HM) as [EB Er].
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14764.
    { mac_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    pose proof (mac_ro_mem _ _ _ HF) as Hm1.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (mac_E regs fa) _ ms regs [w64 fa] HS AG);
          vm_compute; reflexivity).
    mac_reg HS (Z_to_bv 5 10) (w64 0) R10 ltac:(reflexivity).
    pmkst HS. rewrite PEPI.
    exact (mac_exit_epi (ms_regs ms) (ms_mem ms) md' HJ (mac_rgA_pres _ _ (mac_rg1_A regs RG) HP)
      (mac_KV_ext m _ KV Hm1) R10 EB Er).
  - (* a0 = 0: dst is SPEC_BCAST; DESK *)
    apply mac_br_ne_f in Hc.
    assert (E3 : TC.beq_bytes (mrxb_dst fr n) TC.SPEC_BCAST = true) by (apply IFF; exact Hc).
    pose proof (mac_m_bc_yes _ _ _ _ _ _ E1 E2 E3 HM) as HD.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14868.
    { mac_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    pose proof (mac_ro_mem _ _ _ HF) as Hm1.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (mac_E regs fa) _ ms regs [w64 fa] HS AG);
          vm_compute; reflexivity).
    pmkst HS. rewrite PDESK.
    exact (mac_exit_desk (ms_regs ms) (ms_mem ms) md' HJ (mac_rg1_pres _ _ RG HP) (mac_KV_ext m _ KV Hm1) HD).
Qed.

(* After the second call (+0x07c, beqz a0): a0 = 0 goes to DESK; else the third call (+0x080 - +0x090). *)
Lemma mac_p2 : forall regs m md, MJ m md -> mac_rg2 regs -> mac_KV m ->
  TC.beq_bytes (mrxb_src fr n) TC.HOST = false ->
  (YK11.getr regs 10 = w64 0 <-> TC.beq_bytes (mrxb_dst fr n) TC.HOST = true) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14840)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md HJ RG KV E1 IFF.
  destruct mac_vals as (V6 & V17 & _ & PEPI & PDESK).
  pose proof mac_geo as (SP1 & SP2 & STK & FRM & EST & F0 & F64 & FP). pose proof mac_n as (N30 & NL).
  pose proof HCUR as (Hok & _ & _).
  pose proof RG as ((RGA & S0) & S1).
  pose proof (mac_img regs fa) as HEI. pose proof (mac_agree regs fa) as AG.
  pose proof (mac_entry_at regs m 14840 RGA KV) as HS.
  assert (SHOK : sh_ok segs MAC_Bx MAC_SH (mac_E regs fa) (mrestrict (w_H Wc) m))
    by (unfold sh_ok, MAC_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* a0 = 0: dst is HOST; DESK *)
    apply (proj1 (mac_br_eq regs fa)) in Hc.
    pose proof (mac_m_dsth _ _ _ _ _ _ E1 (proj1 IFF Hc) HM) as HD.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14868.
    { mac_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    pose proof (mac_ro_mem _ _ _ HF) as Hm1.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (mac_E regs fa) _ ms regs [w64 fa] HS AG);
          vm_compute; reflexivity).
    pmkst HS. rewrite PDESK.
    exact (mac_exit_desk (ms_regs ms) (ms_mem ms) md' HJ (mac_rg1_pres _ _ (proj1 RG) HP) (mac_KV_ext m _ KV Hm1) HD).
  - (* a0 <> 0: dst is not HOST; a1 = SPEC_BCAST, a2 = 6, a0 = s1 = fa, `jal bcmp` *)
    apply mac_br_eq_f in Hc.
    assert (E2 : TC.beq_bytes (mrxb_dst fr n) TC.HOST = false).
    { destruct (TC.beq_bytes (mrxb_dst fr n) TC.HOST) eqn:E2; [|reflexivity].
      exfalso. apply Hc. apply IFF. reflexivity. }
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mac_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    pose proof (mac_ro_mem _ _ _ HF) as Hm1.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (mac_E regs fa) _ ms regs [w64 fa] HS AG);
          vm_compute; reflexivity).
    pose proof (mac_KV_ext m _ KV Hm1) as KV1.
    mac_reg HS (Z_to_bv 5 10) (w64 fa) Ra0 ltac:(apply (mac_sv_reg regs fa 9 (Z_to_bv 5 9) fa eq_refl S1); lia).
    mac_reg HS (Z_to_bv 5 11) (w64 TRANS_SPEC_BCAST) Ra1
      ltac:(apply (mac_sv_obj regs fa (A_OBJ 17) TRANS_SPEC_BCAST);
            [unfold A_OBJ, A_TEXT, A_LIM; lia | exact V17 | unfold TRANS_SPEC_BCAST; lia]).
    mac_reg HS (Z_to_bv 5 12) (w64 6) Ra2 ltac:(reflexivity).
    mac_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14864)) Rra ltac:(apply codeptr_val; exact HEI).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) mm
        rom) mdx) Q) end.
    apply (mac_bcmp mac_rg1 mac_rg1_pres mac_rg1_A (ms_regs ms) (ms_mem ms) md' fa TRANS_SPEC_BCAST
      (Z_to_bv 64 (BASE + 14864)) _ HJ (mac_rg1_pres _ _ (proj1 RG) HP) KV1 Ra0 Ra1 Ra2
      (mac_rd_frame (ms_mem ms) md' fa 0 HJ KV1 ltac:(lia) ltac:(lia) ltac:(lia)) (mac_rd_bcast _ _ HJ KV1)
      ltac:(lia) ltac:(left; unfold TRANS_SPEC_BCAST; lia) Rra
      (ret_ok_codeptr_v (PI := PI_transportb) 14864 ltac:(lia) eq_refl)).
    intros regs3 mem3 md3 HJ3 RG3 KV3 IFF3.
    apply (mac_p3 regs3 mem3 md3 HJ3 RG3 KV3 E1 E2).
    rewrite (mac_dst_eq fr n Hok).
    exact (iff_trans IFF3 (mac_cmp (ms_mem ms) fa TRANS_SPEC_BCAST 0 TC.SPEC_BCAST KV1 ltac:(lia) ltac:(lia) ltac:(lia)
      eq_refl (mac_bcast_view (ms_mem ms) KV1))).
Qed.

(* After the first call (+0x060, beqz a0): a0 = 0 goes to the epilogue with a0 = 0; else the second call
   (+0x064 - +0x078: s1 = f.dst = fa, a1 = HOST, a2 = 6, a0 = s1). *)
Lemma mac_p1 : forall regs m md, MJ m md -> mac_rg1 regs -> mac_KV m ->
  (YK11.getr regs 10 = w64 0 <-> TC.beq_bytes (mrxb_src fr n) TC.HOST = true) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14812)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md HJ RG KV IFF.
  destruct mac_vals as (V6 & V17 & _ & PEPI & PDESK).
  pose proof mac_geo as (SP1 & SP2 & STK & FRM & EST & F0 & F64 & FP). pose proof mac_n as (N30 & NL).
  pose proof HCUR as (Hok & _ & _).
  pose proof RG as (RGA & S0).
  pose proof (mac_img regs fa) as HEI. pose proof (mac_agree regs fa) as AG.
  pose proof (mac_entry_at regs m 14812 RGA KV) as HS.
  assert (SHOK : sh_ok segs MAC_Bx MAC_SH (mac_E regs fa) (mrestrict (w_H Wc) m))
    by (unfold sh_ok, MAC_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* a0 = 0: src is HOST; the epilogue with a0 = 0 *)
    apply (proj1 (mac_br_eq regs fa)) in Hc.
    destruct (mac_m_src _ _ _ _ _ _ (proj1 IFF Hc) HM) as [EB Er].
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14764.
    { mac_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    pose proof (mac_ro_mem _ _ _ HF) as Hm1.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (mac_E regs fa) _ ms regs [w64 fa] HS AG);
          vm_compute; reflexivity).
    mac_reg HS (Z_to_bv 5 10) (w64 0) Ra0 ltac:(rewrite mac_sv_a0; exact Hc).
    pmkst HS. rewrite PEPI.
    exact (mac_exit_epi (ms_regs ms) (ms_mem ms) md' HJ (mac_rgA_pres _ _ RGA HP) (mac_KV_ext m _ KV Hm1) Ra0 EB Er).
  - (* a0 <> 0: src is not HOST; s1 = fa, a0 = s1, a1 = HOST, a2 = 6, `jal bcmp` *)
    apply mac_br_eq_f in Hc.
    assert (E1 : TC.beq_bytes (mrxb_src fr n) TC.HOST = false).
    { destruct (TC.beq_bytes (mrxb_src fr n) TC.HOST) eqn:E1; [|reflexivity].
      exfalso. apply Hc. apply IFF. reflexivity. }
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mac_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    pose proof (mac_ro_mem _ _ _ HF) as Hm1.
    pose proof (regs_kept_of_st_ok segs (mac_E regs fa) _ _ regs [w64 fa] MAC_KEEP2 HS AG
      ltac:(vm_compute; reflexivity)) as KP.
    pose proof (mac_KV_ext m _ KV Hm1) as KV1.
    mac_reg HS (Z_to_bv 5 9) (w64 fa) Rs1 ltac:(apply mac_den0; lia).
    mac_reg HS (Z_to_bv 5 10) (w64 fa) Ra0 ltac:(apply mac_den0; lia).
    mac_reg HS (Z_to_bv 5 11) (w64 TRANS_HOST) Ra1
      ltac:(apply (mac_sv_obj regs fa (A_OBJ 6) TRANS_HOST);
            [unfold A_OBJ, A_TEXT, A_LIM; lia | exact V6 | unfold TRANS_HOST; lia]).
    mac_reg HS (Z_to_bv 5 12) (w64 6) Ra2 ltac:(reflexivity).
    mac_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14840)) Rra ltac:(apply codeptr_val; exact HEI).
    assert (RG2 : mac_rg2 (ms_regs ms)).
    { split; [split|].
      - intros q Hq H8 H9. refine (eq_trans (KP (Z_to_bv 5 q) _) (RGA q Hq H8 H9)).
        unfold MAC_KEEP2. apply in_map. unfold acallee_saved in Hq. cbn [In]. lia.
      - refine (eq_trans (KP (Z_to_bv 5 8) _) S0). unfold MAC_KEEP2. apply in_map. cbn [In]. lia.
      - exact Rs1. }
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) mm
        rom) mdx) Q) end.
    apply (mac_bcmp mac_rg2 mac_rg2_pres (fun r1 H => mac_rg1_A r1 (proj1 H)) (ms_regs ms) (ms_mem ms) md' fa TRANS_HOST
      (Z_to_bv 64 (BASE + 14840)) _ HJ RG2 KV1 Ra0 Ra1 Ra2
      (mac_rd_frame (ms_mem ms) md' fa 0 HJ KV1 ltac:(lia) ltac:(lia) ltac:(lia)) (mac_rd_host _ _ HJ KV1)
      ltac:(lia) ltac:(left; unfold TRANS_HOST; lia) Rra
      (ret_ok_codeptr_v (PI := PI_transportb) 14840 ltac:(lia) eq_refl)).
    intros regs3 mem3 md3 HJ3 RG3 KV3 IFF3.
    apply (mac_p2 regs3 mem3 md3 HJ3 RG3 KV3 E1).
    rewrite (mac_dst_eq fr n Hok).
    exact (iff_trans IFF3 (mac_cmp (ms_mem ms) fa TRANS_HOST 0 TC.HOST KV1 ltac:(lia) ltac:(lia) ltac:(lia)
      eq_refl (mac_host_view (ms_mem ms) KV1))).
Qed.

(* From the cut MAC: run 1 (+0x048 - +0x05c: s0 = f.src = fa + 6, a1 = HOST, a2 = 6, a0 = s0, `jal bcmp`), the first
   call, then mac_p1. *)
Lemma mac_walk : forall md2, MJ mem2 md2 ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (MRX_PC OFF_MAC)) mem2 (YK11.seg_rom segs)) md2) IPOST.
Proof using All.
  intros md2 HJ.
  destruct mac_vals as (V6 & V17 & PMAC & PEPI & PDESK).
  pose proof mac_geo as (SP1 & SP2 & STK & FRM & EST & F0 & F64 & FP). pose proof mac_n as (N30 & NL).
  pose proof HCUR as (Hok & _ & _).
  assert (RGA : mac_rgA regs2) by (intros q _ _ _; reflexivity).
  assert (KV0 : mac_KV mem2) by (intros a _ _; reflexivity).
  rewrite <- PMAC.
  pose proof (mac_img regs2 fa) as HEI. pose proof (mac_agree regs2 fa) as AG.
  pose proof (mac_entry_at regs2 mem2 14788 RGA KV0) as HS.
  assert (SHOK : sh_ok segs MAC_Bx MAC_SH (mac_E regs2 fa) (mrestrict (w_H Wc) mem2))
    by (unfold sh_ok, MAC_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
    HGX 0 []) as RUN.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mac_awr. }
  set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
  pose proof (mac_ro_mem _ _ _ HF) as Hm1.
  pose proof (regs_kept_of_st_ok segs (mac_E regs2 fa) _ _ regs2 [w64 fa] MAC_KEEP1 HS AG
    ltac:(vm_compute; reflexivity)) as KP.
  pose proof (mac_KV_ext mem2 _ KV0 Hm1) as KV1.
  mac_reg HS (Z_to_bv 5 8) (w64 (fa + 6)) Rs0 ltac:(apply mac_den; lia).
  mac_reg HS (Z_to_bv 5 10) (w64 (fa + 6)) Ra0 ltac:(apply mac_den; lia).
  mac_reg HS (Z_to_bv 5 11) (w64 TRANS_HOST) Ra1
    ltac:(apply (mac_sv_obj regs2 fa (A_OBJ 6) TRANS_HOST);
          [unfold A_OBJ, A_TEXT, A_LIM; lia | exact V6 | unfold TRANS_HOST; lia]).
  mac_reg HS (Z_to_bv 5 12) (w64 6) Ra2 ltac:(reflexivity).
  mac_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14812)) Rra ltac:(apply codeptr_val; exact HEI).
  assert (RG1 : mac_rg1 (ms_regs ms)).
  { split; [|exact Rs0].
    intros q Hq H8 H9. apply (KP (Z_to_bv 5 q)). unfold MAC_KEEP1. apply in_map. unfold acallee_saved in Hq.
    cbn [In]. lia. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) mm rom)
      mdx) Q) end.
  apply (mac_bcmp mac_rg1 mac_rg1_pres mac_rg1_A (ms_regs ms) (ms_mem ms) md1 (fa + 6) TRANS_HOST
    (Z_to_bv 64 (BASE + 14812)) _ HJ RG1 KV1 Ra0 Ra1 Ra2
    (mac_rd_frame (ms_mem ms) md1 (fa + 6) 6 HJ KV1 eq_refl ltac:(lia) ltac:(lia)) (mac_rd_host _ _ HJ KV1)
    ltac:(lia) ltac:(left; unfold TRANS_HOST; lia) Rra
    (ret_ok_codeptr_v (PI := PI_transportb) 14812 ltac:(lia) eq_refl)).
  intros regs3 mem3 md3 HJ3 RG3 KV3 IFF3.
  apply (mac_p1 regs3 mem3 md3 HJ3 RG3 KV3).
  rewrite (mac_src_eq fr n Hok).
  exact (iff_trans IFF3 (mac_cmp (ms_mem ms) (fa + 6) TRANS_HOST 6 TC.HOST KV1 eq_refl ltac:(lia) ltac:(lia)
    eq_refl (mac_host_view (ms_mem ms) KV1))).
Qed.

End cut.

(* The segment MAC: from the cut MAC to the cuts EPI and DESK. *)
Lemma mrx_seg_mac : K (MRX_PC OFF_EPI) (R_EPI Bw' r) -> K (MRX_PC OFF_DESK) (R_DESK B fr n sp1 Bw' r) ->
  K (MRX_PC OFF_MAC) (R_MAC B fr n sp1 Bw' r).
Proof using All.
  intros KE KD Wc Bwc c HAT.
  destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HFR & HPM & HMO2 & HSP & HGP & HTP & HHI & HSV & HTW & HR).
  destruct HR as (HCUR & H18 & HM).
  exact (mac_walk Wc Bwc ly2 S2 regs2 mem2 KE KD HFR HPM HMO2 HSP HGP HTP HHI HSV HTW HCUR H18 HM md2 HJ).
Qed.

End seg.
