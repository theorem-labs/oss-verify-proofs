(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module paths and module names changed; 496 of its 563 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SrxBDeskKit.v, with its module paths and module names changed; 902 of its 992 lines of code are new or changed and 473 lines of the source are left out. *)
(* SrxBLearn: Theorem srxb_learn_ok : forall fx rc B MT, @srxb_learn_stmt fx rc B MT (lib/B/Prog/SrxBCut.v), the
   learn piece of the walk of diginet_session_rx on fuzz_transport.asan-ubsan (0x87784 = transportb_sigma
   TB_diginet_session_rx), from the learn cut (+0x330, 0x87ab4) to the release cut (+0x1e0), the ignored cut
   (+0x1d4) and the closed cut (+0x374). The code is image A's (lib/A/Prog/SrxLearn.v) 12 bytes later and the proof
   is that file's at image B's names. The runs are the position-abstract token runs of lib/B/Prog/TransportGRunB.v
   paj_run_x / paj_run_to_x, inside the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []):
     run 1  +0x330 .. +0x338  a0 = the 1-byte load of h.cmd at f + 30 (fr_cmd b, cell 30 of frame_f_bytes; inside
                              the own frame, so the compiler emits no shadow check), a0 & 0xfe, a1 = 0xe0;
     +0x33c                   `bne a0, a1`: not an announce (the model's cmd test of :284) runs through +0x394
                              (a0 = 0) and `j` to the release cut, with the world Bw;
     run 2  +0x340 .. +0x344  the 8-byte store of a2 (the shadow byte's address of s + 116) at s1 + 24 and a0 =
                              s7 = f + 6, up to the leaf call;
     +0x348                   diginet_mac_is_digidesign (lib/B/Prog/diginet_mac_is_digidesign_cg.v read through
                              DgnTransportBCg.v transport_leaf_at, its post turned into the journal by
                              DgnTransportBLeafb.v decode_leafb_journal, inside the G journal by TransportGCg.v
                              gx_call_leaf): its result is 1 exactly when oui_of (fr_src b);
     +0x34c                   `beq a0, zero`: not Digidesign runs through +0x418 .. +0x428 (the checked access at
                              s + 18184, whose shadow byte is 0) to the ignored cut with a0 = 0;
     run 3  +0x350 .. +0x358  a0 = s + 120, a2 = 6, a1 = f + 6, up to the memcpy call;
     +0x35c                   __asan_memcpy (YG0d.v aintrin_realizes through TransportGCg.v gx_intrin_at; the
                              destination is a range of g_s, a byte of G, writable by TransportGRwB.v
                              G_HARNESS_B_rw): g_s.desk_mac = fr_src b (the model's set_S_desk_mac);
     run 4  +0x360 .. +0x370  a0 = the 8-byte load of the slot at s1 + 24, the checked 1-byte load of the shadow
                              byte it holds (0 by trans_srx_cells, so `bne` is not taken), a0 = 1 and the 4-byte
                              store at s + 116 (the model's set_S_desk_known), falling into the closed cut with the
                              world srx_learn Bw b.
   The error paths of this range are unreached: __asan_report_store4 at +0x508 (0x87c8c; the block at +0x4f8 is not
   entered, the shadow byte of s + 116 being 0) and __asan_report_load8 at +0x430 (0x87bb4; the shadow byte of
   s + 18184 is 0). The range has no UBSan trap branch. Every byte the piece changes lies in the callees' stack
   windows below the realigned sp, in the slot s1 + 24 of its own machine frame, or in g_s's desk_mac and desk_known
   (bytes of G and rows of srx_wr b), so SrxBDeskKit.v srxbdk_move carries every fact of the learn cut to each of the
   three cuts. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  DgnTransportBLeafb DgnTransportBCgRun LeafCgKit AsanKA diginet_mac_is_digidesign_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_mac_is_digidesign_cg m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import CanKit SrxBCut SrxBDeskKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.DgnTransportBLeafb.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module LKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module LMDc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_mac_is_digidesign_c.
Module LMD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_mac_is_digidesign_cg.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module MLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.m_set_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The pcs inside the piece: the cmd test (+0x33c), the test of the leaf's result (+0x34c), the slot's reload
   (+0x360) and the ignored path of :287-289 (+0x418). *)
Definition SRXBL_C1 : Z := AF_diginet_session_rx + 0x33c.
Definition SRXBL_C2 : Z := AF_diginet_session_rx + 0x34c.
Definition SRXBL_C3 : Z := AF_diginet_session_rx + 0x360.
Lemma srxbl_pcs : SRXB_LEARN = 26644 /\ SRXBL_C1 = 26656 /\ SRXBL_C2 = 26672 /\ SRXBL_C3 = 26692 /\
  SRXB_REL = 26308 /\ SRXB_IGN = 26296 /\ SRXB_CLOSED = 26712.
Proof. repeat split; reflexivity. Qed.

(* runs 1 and 2: h.cmd at f + 30 (atom 34) and the slot at s1 + 24. *)
Definition srxbl_rg_cmd : YP09.region :=
  YP09.mkRegion (Some 22%nat) 30 31 0 0 [YP09.mkChunk 30 (YP09.CVal 1 (SOff 33 0))].
Definition srxbl_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
Definition srxbl_facts1 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF 4096 (2 ^ 47) 5); (33%nat, mkAF 0 255 0)] [] [].
Definition ss_srxbl1 : sstate := mkSS SRXB_LEARN sr_atoms [srxbl_rg_cmd; srxbl_rg_slot] None srxbl_facts1.
(* the state at +0x34c, after the leaf: the shadow entry of g_s.stats.rx_ignored's group *)
Definition srxbl_facts2 : facts :=
  mkFacts [(21%nat, mkAF (SRX_S + 18152) (SRX_S + 18152) 3); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_srxbl2 : sstate := mkSS SRXBL_C2 sr_atoms [] None srxbl_facts2.
Definition SRXBL_SH2 : list shent := [mkSHE 21 32 40].
(* run 4: the slot read back (its 8 bytes hold the shadow byte's address of s + 116), the shadow entry of
   [s + 112, s + 128) and g_s.desk_known at s8 (atom 24), written by the `sw` of :291. *)
Definition srxbl_sv_sh : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 116) (SLit 3)) (SOff 27 0).
Definition srxbl_rg_slot2 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (YP09.CVal 8 srxbl_sv_sh)].
Definition srxbl_rg_dk : YP09.region := YP09.mkRegion (Some 24%nat) 0 4 0 4 [].
Definition srxbl_facts3 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF SRX_S SRX_S 6);
           (24%nat, mkAF (SRX_S + 116) (SRX_S + 116) 2); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_srxbl3 : sstate := mkSS SRXBL_C3 sr_atoms [srxbl_rg_slot2; srxbl_rg_dk] None srxbl_facts3.
Definition SRXBL_SH3 : list shent := [mkSHE 20 112 128].
Definition SRXBL_Bx : sv := SOff 27 0.
Definition SRXBL_B0 : Z * Z := (0, 0).

(* `andi a0, a0, 254` on a byte: the model's test of :284 (cmd = DIGINET_CMD_ANNOUNCE or
   DIGINET_CMD_ANNOUNCE_SESSION). *)
Lemma srxbl_land254 : forall c, 0 <= c < 256 -> Z.land c 254 = 2 * (c / 2).
Proof.
intros c Hc.
assert (E1 : 254 = Z.ldiff (Z.ones 8) (Z.ones 1)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
change (2 ^ 1) with 2. lia.
Qed.

Lemma srxbl_cmd_test : forall c, 0 <= c < 256 ->
  (Z.land c 254 = 224 <-> ((c =? TS0.DIGINET_CMD_ANNOUNCE) || (c =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = true).
Proof.
intros c Hc. rewrite (srxbl_land254 c Hc).
assert (D : c = 2 * (c / 2) + c mod 2) by (pose proof (Z.div_mod c 2 ltac:(lia)); lia).
pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as M.
assert (EA : TS0.DIGINET_CMD_ANNOUNCE = 224) by reflexivity.
assert (EB : TS0.DIGINET_CMD_ANNOUNCE_SESSION = 225) by reflexivity.
rewrite EA, EB, orb_true_iff, !Z.eqb_eq. lia.
Qed.

(* The byte-wise value of a 4-byte store of 1 (the model's set_S_desk_known at 1). *)
Lemma srxbl_aview_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v -> forall j, (j < n)%nat ->
    aview tfibsegs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v HV j Hj. pose proof (HV j Hj) as H0.
unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* The two stores of :290-291 keep g_fail_next (a global of its own). *)
Lemma srxbl_fn : forall Bw b, length Bw = Z.to_nat TW.W_LEN -> DSpec.fr_code b = 0 ->
  TW.g_fail_next (srx_learn Bw b) = TW.g_fail_next Bw.
Proof.
intros Bw b HL H0.
assert (Hs : length (DSpec.fr_src b) = 6%nat).
{ unfold DSpec.fr_src. rewrite length_firstn, length_skipn.
  pose proof (srxbdk_code0_len b H0) as Hb. lia. }
assert (LZ : Z.of_nat (length Bw) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
assert (L1 : Z.of_nat (length (TW.upd Bw TW.A_S_desk_mac (DSpec.fr_src b))) = TW.W_LEN).
{ rewrite (TWL.length_upd Bw (DSpec.fr_src b) TW.A_S_desk_mac
    ltac:(unfold TW.A_S_desk_mac, TW.OFF_g_s; lia)
    ltac:(rewrite Hs, LZ; unfold TW.A_S_desk_mac, TW.OFF_g_s, TW.W_LEN; lia)). exact LZ. }
unfold srx_learn, TW.set_S_desk_known, TW.set_S_desk_mac, TW.g_fail_next.
rewrite (TWL.u_at_upd_out (TW.upd Bw TW.A_S_desk_mac (DSpec.fr_src b)) (TW.put 4 1)
  TW.A_S_desk_known TW.OFF_g_fail_next 1
  ltac:(unfold TW.A_S_desk_known, TW.OFF_g_s; lia) ltac:(unfold TW.OFF_g_fail_next; lia)
  ltac:(rewrite TWL.length_put; unfold TW.A_S_desk_known, TW.OFF_g_s, TW.OFF_g_fail_next; lia)
  ltac:(rewrite TWL.length_put, L1; unfold TW.A_S_desk_known, TW.OFF_g_s, TW.W_LEN; lia)).
rewrite (TWL.u_at_upd_out Bw (DSpec.fr_src b) TW.A_S_desk_mac TW.OFF_g_fail_next 1
  ltac:(unfold TW.A_S_desk_mac, TW.OFF_g_s; lia) ltac:(unfold TW.OFF_g_fail_next; lia)
  ltac:(rewrite Hs; unfold TW.A_S_desk_mac, TW.OFF_g_s, TW.OFF_g_fail_next; lia)
  ltac:(rewrite Hs, LZ; unfold TW.A_S_desk_mac, TW.OFF_g_s, TW.W_LEN; lia)).
reflexivity.
Qed.

Lemma srxbl_eqb_lit : forall v w, 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
intros v w Hv Hw. unfold bv_eqb. rewrite (unsigned_lit_small v Hv), (unsigned_lit_small w Hw). reflexivity.
Qed.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma srxbl_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* The walk's valuations: the registers, the shadow base (atom 32) and h.cmd (atom 34). *)
Definition srxbl_E (regs2 : bvmap 5 word) (b : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 [w64 SHADOW_OFF; Z_to_bv 64 (DSpec.fr_cmd b)]).
Definition srxbl_E0 (regs2 : bvmap 5 word) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 [w64 SHADOW_OFF]).

Lemma srxbl_ew : forall regs2 b n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (srxbl_E regs2 b) n = YK11.getr regs2 rr.
Proof. intros regs2 b n rr Hn. unfold srxbl_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma srxbl_ew0 : forall regs2 n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (srxbl_E0 regs2) n = YK11.getr regs2 rr.
Proof. intros regs2 n rr Hn. unfold srxbl_E0. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma srxbl_ew33 : forall regs2 b, ew (srxbl_E regs2 b) 33 = Z_to_bv 64 (DSpec.fr_cmd b).
Proof.
intros regs2 b. unfold srxbl_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 1).
Qed.
Lemma srxbl_env : forall regs2 b, img_env VAL A_LIM (srxbl_E regs2 b).
Proof. intros regs2 b. unfold srxbl_E. apply Eimg_env. Qed.
Lemma srxbl_env0 : forall regs2, img_env VAL A_LIM (srxbl_E0 regs2).
Proof. intros regs2. unfold srxbl_E0. apply Eimg_env. Qed.

(* The state of runs 1 and 2, at +0x330. *)
Lemma srxbl_entry1 : forall (W : world segs) regs2 mem buf b fj F sp1,
  DSpec.fr_code b = 0 -> srxb_fbytes W mem F buf b fj ->
  YK11.getr regs2 9 = w64 sp1 -> YK11.getr regs2 22 = w64 (F + SRX_F) ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 4096 <= F -> F + SRXB_FBYTES <= sp1 -> F mod 64 = 0 ->
  (forall a, sp1 + 24 <= a < sp1 + 32 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (srxbl_E regs2 b) ss_srxbl1
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SRXB_LEARN)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SRXBL_Bx (@nil shent) (srxbl_E regs2 b) (mrestrict (w_H W) mem).
Proof.
intros W regs2 mem buf b fj F sp1 H0 HFB R9 R22 Hsp Hsp32 HF4 HFc HF64 Hpres.
assert (Hfbs : SRXB_FBYTES = 128) by reflexivity.
assert (Hsf : SRX_F = 32) by reflexivity.
destruct HFB as (Hfj & HFG).
assert (HLen : length (frame_f_bytes buf b fj) = 64%nat) by exact (srxbdk_fbytes_len buf b fj H0 Hfj).
assert (Hcr : 0 <= DSpec.fr_cmd b < 256) by exact (DSpec.at8_range b 28).
assert (U9 : bv_unsigned (ew (srxbl_E regs2 b) 9) = sp1)
  by (rewrite (srxbl_ew regs2 b 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew (srxbl_E regs2 b) 22) = F + SRX_F)
  by (rewrite (srxbl_ew regs2 b 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (srxbl_E regs2 b) 33) = DSpec.fr_cmd b)
  by (rewrite (srxbl_ew33 regs2 b); apply unsigned_lit_small; lia).
split; [|constructor].
rewrite restrict_mkst_fx. unfold ss_srxbl1.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold srxbl_rg_cmd, srxbl_rg_slot, region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ (F + SRX_F) 30 1 (SOff 33 0) (DSpec.fr_cmd b));
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    rewrite <- (srxbdk_fcmd buf b fj H0 Hfj).
    exact (proj1 (HFG 30%nat ltac:(lia))).
  + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
- apply pairwise_disjoint_of_extents.
  unfold srxbl_rg_cmd, srxbl_rg_slot, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U22. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold srxbl_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U22, U33.
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
  pose proof (Z.div_mod F 64 ltac:(lia)) as D64. rewrite HF64, Z.add_0_r in D64.
  replace (F + SRX_F) with ((2 * (F / 64)) * 32 + 32) by (rewrite Hsf; lia).
  rewrite Z.add_mod, Z_mod_mult by lia. reflexivity.
Qed.

(* The state at +0x34c, after the leaf call. *)
Lemma srxbl_entry2 : forall ly S (W : world segs) regs3 mem md,
  trans_srx_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs3 21 = w64 (SRX_S + 18152) -> YK11.getr regs3 27 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (srxbl_E0 regs3) ss_srxbl2
    (restrict (w_H W) (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + SRXBL_C2)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SRXBL_Bx SRXBL_SH2 (srxbl_E0 regs3) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs3 mem md HSC HAR R21 R27.
assert (CS : SRX_S = 6157888) by reflexivity.
assert (U21 : bv_unsigned (ew (srxbl_E0 regs3) 21) = SRX_S + 18152)
  by (rewrite (srxbl_ew0 regs3 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew (srxbl_E0 regs3) 27) = SHADOW_OFF)
  by (rewrite (srxbl_ew0 regs3 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_srxbl2.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  + unfold srxbl_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U21, U27.
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- assert (UB : U (srxbl_E0 regs3) SRXBL_Bx = SHADOW_OFF).
  { unfold U, SRXBL_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia. }
  unfold sh_ok, SRXBL_SH2. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ SRXBL_Bx 21 (SRX_S + 18184) 8 (SRX_S + 18152) 32 40
    (srxbdk_gs_ra B ly S W mem md (SRX_S + 18184) 8 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) UB).
  + unfold U. cbn [sv_denot]. rewrite U21, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The state of run 4, at +0x360: the slot holds the shadow byte's address of s + 116. *)
Lemma srxbl_entry3 : forall ly S (W : world segs) regs4 mem md sp1,
  trans_srx_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs4 9 = w64 sp1 -> YK11.getr regs4 20 = w64 SRX_S -> YK11.getr regs4 24 = w64 (SRX_S + 116) ->
  YK11.getr regs4 27 = w64 SHADOW_OFF -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 24) 8 (SHADOW_OFF + (SRX_S + 116) / 8) ->
  st_ok_pi segs VAL (srxbl_E0 regs4) ss_srxbl3
    (restrict (w_H W) (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + SRXBL_C3)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SRXBL_Bx SRXBL_SH3 (srxbl_E0 regs4) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs4 mem md sp1 HSC HAR R9 R20 R24 R27 Hsp Hsp32 HVAL.
assert (CS : SRX_S = 6157888) by reflexivity.
assert (DSH : (SRX_S + 116) / 8 = 769750) by (vm_compute; reflexivity).
assert (U9 : bv_unsigned (ew (srxbl_E0 regs4) 9) = sp1)
  by (rewrite (srxbl_ew0 regs4 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (srxbl_E0 regs4) 20) = SRX_S)
  by (rewrite (srxbl_ew0 regs4 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew (srxbl_E0 regs4) 27) = SHADOW_OFF)
  by (rewrite (srxbl_ew0 regs4 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U24 : bv_unsigned (ew (srxbl_E0 regs4) 24) = SRX_S + 116)
  by (rewrite (srxbl_ew0 regs4 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (DEN : sv_denot (srxbl_E0 regs4) srxbl_sv_sh = Z_to_bv 64 (SHADOW_OFF + (SRX_S + 116) / 8)).
{ unfold srxbl_sv_sh.
  exact (srxbdk_denot_shadow (srxbl_E0 regs4) 20%nat 27%nat SRX_S 116 SHADOW_OFF
    ltac:(rewrite (srxbl_ew0 regs4 20%nat 20%bv eq_refl); exact R20)
    ltac:(rewrite (srxbl_ew0 regs4 27%nat 27%bv eq_refl); exact R27)
    ltac:(lia) ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)). }
split.
- rewrite restrict_mkst_fx. unfold ss_srxbl3.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold srxbl_rg_slot2, srxbl_rg_dk, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ sp1 24 8 srxbl_sv_sh (SHADOW_OFF + (SRX_S + 116) / 8));
        [exact DEN | cbn; unfold SHADOW_OFF; lia | cbn; lia | exact HVAL].
    * rewrite U24. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (SRX_S + 116 + o) G_HARNESS_B_rw).
      apply srxbdk_inG. unfold TW.SZ_g_s. lia.
  + apply pairwise_disjoint_of_extents.
    unfold srxbl_rg_slot2, srxbl_rg_dk, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U24. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + unfold srxbl_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U20, U24, U27.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- assert (UB : U (srxbl_E0 regs4) SRXBL_Bx = SHADOW_OFF).
  { unfold U, SRXBL_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia. }
  unfold sh_ok, SRXBL_SH3. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ SRXBL_Bx 20 (SRX_S + 112) 16 SRX_S 112 128
    (srxbdk_gs_ra B ly S W mem md (SRX_S + 112) 16 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) UB).
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* `andi a0, a0, 254` on the byte h.cmd. *)
Lemma srxbl_denot_and254 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 254)) = Z_to_bv 64 (Z.land v 254).
Proof.
intros E n v Hn Hv.
assert (HB : 0 <= Z.land v 254 <= 254).
{ rewrite (srxbl_land254 v Hv). pose proof (Z.div_mod v 2 ltac:(lia)).
  pose proof (Z.mod_pos_bound v 2 ltac:(lia)). lia. }
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v 0 Hn) by lia.
rewrite Z.add_0_r, (zcanon_id 254) by (unfold M64; lia).
apply zcanon_id. unfold M64. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The piece                                                           *)
(* ------------------------------------------------------------------ *)

Lemma srxbl_holds : @srxb_learn_stmt fx rc B MT.
Proof.
unfold srxb_learn_stmt. intros INV REL IGN CLOSED.
unfold srxb_learn_at. intros HLAWS HCALLS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HRD HRDF HFB Htw H0 HMAC HK0 HREGS.
pose proof HLAWS as (HPCS & HCELLS & HSC & HROU & HRNE & HROR & HRON & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HCALLS as (_ & _ & _ & LEAFC & AMEMCPY & _).
pose proof HFIX as (_ & _ & _ & Hgp & Htp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfn & Hm & _ & _
  & _ & _ & Hinv & _).
destruct (srxbdk_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F HFIX)
  as (HAR & Hce0 & Hlo & Hhi & Hsp0a & H47 & Hsp16 & (Hs1a & Hs1b) & Hs1m & HF4 & HF64 & HFc & HFe).
pose proof HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
pose proof HREGS as ((((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22) & R23) & R24 & R12).
pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hstk : SRX_STK = 9184) by reflexivity.
assert (Hfbs : SRXB_FBYTES = 128) by reflexivity.
assert (Hsf : SRX_F = 32) by reflexivity.
assert (Hffs : FRAME_F_SIZE = 64) by reflexivity.
assert (CS : SRX_S = 6157888) by reflexivity.
assert (DSH : (SRX_S + 116) / 8 = 769750) by (vm_compute; reflexivity).
assert (Hs6 : length (DSpec.fr_src b) = 6%nat).
{ unfold DSpec.fr_src. rewrite length_firstn, length_skipn.
  pose proof (srxbdk_code0_len b H0) as Hb. lia. }
assert (Hcr : 0 <= DSpec.fr_cmd b < 256) by exact (DSpec.at8_range b 28).
assert (HWL : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw).
assert (Hin2 : In (SRX_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFa2 : frame_addr ly2 SRX_CID pos = F) by (rewrite HFe; unfold frame_addr; rewrite HlyF; reflexivity).
assert (Hfs1 : fs_frame_bytes SRX_CID = SRXB_FBYTES) by exact srxb_fbytes_eq.
assert (NGF : forall a, F <= a < F + SRXB_FBYTES -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  refine (frm_img segs B LAWS ly2 S2 W2 mem2 md2 SRX_CID pos a HAR2 Hin2 _ Hi).
  rewrite HFa2, Hfs1. exact Ha. }
assert (HFce : F + SRXB_FBYTES <= YM05.alloc_ceiling) by exact HFc.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* run 1, +0x330 .. +0x338: h.cmd, its mask and the constant 0xe0 *)
destruct (srxbl_entry1 W2 regs2 mem2 buf b fj F sp1 H0 HFB R9 R22 ltac:(lia) Hs1m HF4 ltac:(lia) HF64
  ltac:(intros a Ha; exact (srxbl_jpres STK sp0 FP ly S W0 mem0 md0 _ ly2 S2 W2 mem2 md2 (k + e) HJ2 a ltac:(lia))))
  as [HS SHOK].
assert (HEI : img_env VAL A_LIM (srxbl_E regs2 b)) by apply srxbl_env.
pose proof HJ2 as HJ.
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (srxbl_E regs2 b) n = YK11.getr regs2 rr)
  by (intros n rr Hn; exact (srxbl_ew regs2 b n rr Hn)).
assert (U9e : bv_unsigned (ew (srxbl_E regs2 b) 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
paj_run_to_tok RUNTO HS HJ SHOK SRXBL_B0 SRXBL_C1.
{ srxbdk_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9e in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  apply awr_ok_x_nil. }
srxbdk_kreg HS EE regs2 (2%bv : bv 5) 2%nat R2 X2.
srxbdk_kreg HS EE regs2 (3%bv : bv 5) 3%nat R3 X3.
srxbdk_kreg HS EE regs2 (4%bv : bv 5) 4%nat R4 X4.
srxbdk_kreg HS EE regs2 (8%bv : bv 5) 8%nat R8 X8.
srxbdk_kreg HS EE regs2 (9%bv : bv 5) 9%nat R9 X9.
srxbdk_kreg HS EE regs2 (12%bv : bv 5) 12%nat R12 X12.
srxbdk_kreg HS EE regs2 (18%bv : bv 5) 18%nat R18 X18.
srxbdk_kreg HS EE regs2 (19%bv : bv 5) 19%nat R19 X19.
srxbdk_kreg HS EE regs2 (20%bv : bv 5) 20%nat R20 X20.
srxbdk_kreg HS EE regs2 (21%bv : bv 5) 21%nat R21 X21.
srxbdk_kreg HS EE regs2 (22%bv : bv 5) 22%nat R22 X22.
srxbdk_kreg HS EE regs2 (23%bv : bv 5) 23%nat R23 X23.
srxbdk_kreg HS EE regs2 (24%bv : bv 5) 24%nat R24 X24.
srxbdk_kreg HS EE regs2 (25%bv : bv 5) 25%nat R25 X25.
srxbdk_kreg HS EE regs2 (26%bv : bv 5) 26%nat R26 X26.
srxbdk_kreg HS EE regs2 (27%bv : bv 5) 27%nat R27 X27.
assert (D10 : sv_denot (srxbl_E regs2 b) (SAlu ALU_AND (SOff 33 0) (SLit 254)) =
  Z_to_bv 64 (Z.land (DSpec.fr_cmd b) 254))
  by exact (srxbl_denot_and254 (srxbl_E regs2 b) 33%nat (DSpec.fr_cmd b) (srxbl_ew33 regs2 b) Hcr).
assert (KD1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 24 <= a < sp1 + 32) ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn.
  refine (kept_of_frame (srxbl_E regs2 b) (ss_mem ss_srxbl1) (w_H W2) mem2 (ms_mem ms)
    (fun x => sp1 + 24 <= x < sp1 + 32) HFr _ a Ha Hn).
  intros bb wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9e in Hx; lia |]).
  destruct Hin. }
assert (GR1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG. rename ms into msA.
assert (HtwA : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msA)) Bw).
{ apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KD1; lia. }
destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e (ms_mem msA) _ (fun a : Z => sp1 + 24 <= a < sp1 + 32)
  HLAWS HFIX HCUR HRD HRDF HFB H0 HJ ltac:(intros a HZ; cbv beta in HZ; left; lia)
  ltac:(intros a Ha Hn; exact (KD1 a Ha Hn)) GR1) as (CURA & RDA & RDFA & FBA).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARA.
(* +0x33c: `bne a0, a1` on (h.cmd & 0xfe) *)
psrr_branch_tok RUN BR HS SHOK SRXBL_B0.
- (* not an announce: through +0x394 to the release cut, with the world Bw *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (srxbl_E regs2 b) (SLit 224)) with (Z_to_bv 64 224) in Hc.
  rewrite (srxbl_eqb_lit (Z.land (DSpec.fr_cmd b) 254) 224) in Hc;
    [| pose proof (srxbl_land254 (DSpec.fr_cmd b) Hcr); pose proof (Z.div_mod (DSpec.fr_cmd b) 2 ltac:(lia)); lia
     | lia].
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (HCMD : ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) ||
                  (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = false).
  { destruct (((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) ||
               (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)))%bool eqn:EQ; [|reflexivity].
    exfalso. exact (Hc (proj2 (srxbl_cmd_test (DSpec.fr_cmd b) Hcr) EQ)). }
  pose proof (srxb_m_nocmd timg_B TF Bw b now H0 HMAC HK0 HCMD) as HMD.
  rewrite Hm in HMD. destruct (srxb_some_inv Bw' Bw r DLib.DIGINET_OK HMD) as [EBw Er].
  paj_run_to_tok RUNTO HS HJ SHOK SRXBL_B0 SRXB_REL.
  { srxbdk_awr_rs.
    apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9e in Ha;
      left; split; [unfold awr_byte; left; lia | lia] |].
    apply awr_ok_x_nil. }
  srxbdk_kreg HS EE regs2 (2%bv : bv 5) 2%nat R2 Y2.
  srxbdk_kreg HS EE regs2 (3%bv : bv 5) 3%nat R3 Y3.
  srxbdk_kreg HS EE regs2 (4%bv : bv 5) 4%nat R4 Y4.
  srxbdk_kreg HS EE regs2 (8%bv : bv 5) 8%nat R8 Y8.
  srxbdk_kreg HS EE regs2 (9%bv : bv 5) 9%nat R9 Y9.
  srxbdk_kreg HS EE regs2 (18%bv : bv 5) 18%nat R18 Y18.
  srxbdk_kreg HS EE regs2 (19%bv : bv 5) 19%nat R19 Y19.
  srxbdk_kreg HS EE regs2 (20%bv : bv 5) 20%nat R20 Y20.
  srxbdk_kreg HS EE regs2 (21%bv : bv 5) 21%nat R21 Y21.
  srxbdk_kreg HS EE regs2 (22%bv : bv 5) 22%nat R22 Y22.
  srxbdk_kreg HS EE regs2 (25%bv : bv 5) 25%nat R25 Y25.
  srxbdk_kreg HS EE regs2 (26%bv : bv 5) 26%nat R26 Y26.
  srxbdk_kreg HS EE regs2 (27%bv : bv 5) 27%nat R27 Y27.
  srxbdk_reg HS (10%bv : bv 5) (w64 0) Y10 ltac:(cbn [sv_denot]; reflexivity).
  assert (KD2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 24 <= a < sp1 + 32) ->
    aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) (ms_mem msA) a).
  { intros a Ha Hn.
    refine (kept_of_frame (srxbl_E regs2 b) (ss_mem ss_srxbl1) (w_H W2) (ms_mem msA) (ms_mem ms)
      (fun x => sp1 + 24 <= x < sp1 + 32) HFr _ a Ha Hn).
    intros bb wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9e in Hx; lia |]).
    destruct Hin. }
  assert (GR2 : forall a, apresent (w_H W2) (ms_mem msA) a -> apresent (w_H W2) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG. rename ms into msB.
  assert (HtwB : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msB)) Bw).
  { apply (tw_kept TMAP_B (aview segs (w_H W2) (ms_mem msA))); [exact HtwA|].
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KD2; lia. }
  destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 (ms_mem msA) _ e (ms_mem msB) _ (fun a : Z => sp1 + 24 <= a < sp1 + 32)
    HLAWS HFIX CURA RDA RDFA FBA H0 HJ ltac:(intros a HZ; cbv beta in HZ; left; lia)
    ltac:(intros a Ha Hn; exact (KD2 a Ha Hn)) GR2) as (CURB & RDB & RDFB & FBB).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_REL)) mm rom) mdx) Q) end.
  apply (REL HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw'
    pos sp1 F ly2 S2 W2 (ms_mem msB) _ e (ms_regs msB) HFIX CURB).
  + rewrite EBw. exact HtwB.
  + rewrite EBw. exact Hfn.
  + unfold srxb_regs_rel, srxb_regs_base, srxb_regs_core.
    refine (conj (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y19 (conj Y20 (conj Y25 (conj Y26 Y27)))))))))) (conj Y21 Y22)) _).
    * exact Y3.
    * exact Y4.
    * rewrite Y10, Er. reflexivity.
- (* an announce: the slot, then the leaf diginet_mac_is_digidesign *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (srxbl_E regs2 b) (SLit 224)) with (Z_to_bv 64 224) in Hc.
  rewrite (srxbl_eqb_lit (Z.land (DSpec.fr_cmd b) 254) 224) in Hc;
    [| pose proof (srxbl_land254 (DSpec.fr_cmd b) Hcr); pose proof (Z.div_mod (DSpec.fr_cmd b) 2 ltac:(lia)); lia
     | lia].
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (HCMD : ((DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE) ||
                  (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION)) = true)
    by exact (proj1 (srxbl_cmd_test (DSpec.fr_cmd b) Hcr) Hc).
  paj_run_tok RUN HS HJ SHOK SRXBL_B0.
  { srxbdk_awr_rs.
    apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9e in Ha;
      left; split; [unfold awr_byte; left; lia | lia] |].
    apply awr_ok_x_nil. }
  srxbdk_kreg HS EE regs2 (2%bv : bv 5) 2%nat R2 Y2.
  srxbdk_kreg HS EE regs2 (3%bv : bv 5) 3%nat R3 Y3.
  srxbdk_kreg HS EE regs2 (4%bv : bv 5) 4%nat R4 Y4.
  srxbdk_kreg HS EE regs2 (8%bv : bv 5) 8%nat R8 Y8.
  srxbdk_kreg HS EE regs2 (9%bv : bv 5) 9%nat R9 Y9.
  srxbdk_kreg HS EE regs2 (18%bv : bv 5) 18%nat R18 Y18.
  srxbdk_kreg HS EE regs2 (19%bv : bv 5) 19%nat R19 Y19.
  srxbdk_kreg HS EE regs2 (20%bv : bv 5) 20%nat R20 Y20.
  srxbdk_kreg HS EE regs2 (21%bv : bv 5) 21%nat R21 Y21.
  srxbdk_kreg HS EE regs2 (22%bv : bv 5) 22%nat R22 Y22.
  srxbdk_kreg HS EE regs2 (23%bv : bv 5) 23%nat R23 Y23.
  srxbdk_kreg HS EE regs2 (24%bv : bv 5) 24%nat R24 Y24.
  srxbdk_kreg HS EE regs2 (25%bv : bv 5) 25%nat R25 Y25.
  srxbdk_kreg HS EE regs2 (26%bv : bv 5) 26%nat R26 Y26.
  srxbdk_kreg HS EE regs2 (27%bv : bv 5) 27%nat R27 Y27.
  srxbdk_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 26672)) Y1 ltac:(apply codeptr_val; exact HEI).
  srxbdk_reg HS (10%bv : bv 5) (w64 (F + SRX_F + 6)) Y10
    ltac:(cbn [sv_denot]; rewrite (EE 23%nat 23%bv eq_refl), R23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  (* the slot now holds the shadow byte's address of s + 116 *)
  srxbdk_region HS 1%nat HRsl.
  assert (HVAL : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (sp1 + 24) 8
    (SHADOW_OFF + (SRX_S + 116) / 8)).
  { exact (can_field_of_region (srxbl_E regs2 b) _ 9%nat sp1 _ 24 32 24 32 24 8%N (SOff 12 0)
      (SHADOW_OFF + (SRX_S + 116) / 8) HRsl U9e ltac:(srxbdk_in)
      ltac:(cbn [sv_denot]; rewrite (EE 12%nat 12%bv eq_refl), R12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(cbn; unfold SHADOW_OFF; lia) ltac:(cbn; lia)). }
  clear HRsl.
  assert (KGy : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 24 <= a < sp1 + 32) ->
    aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) (ms_mem msA) a).
  { intros a Ha Hn.
    refine (kept_of_frame (srxbl_E regs2 b) (ss_mem ss_srxbl1) (w_H W2) (ms_mem msA) (ms_mem ms)
      (fun x => sp1 + 24 <= x < sp1 + 32) HFr _ a Ha Hn).
    intros bb wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9e in Hx; lia |]).
    destruct Hin. }
  assert (GR2 : forall a, apresent (w_H W2) (ms_mem msA) a -> apresent (w_H W2) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG. rename ms into msB.
  assert (HtwB : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msB)) Bw).
  { apply (tw_kept TMAP_B (aview segs (w_H W2) (ms_mem msA))); [exact HtwA|].
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KGy; lia. }
  destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 (ms_mem msA) _ e (ms_mem msB) _ (fun a : Z => sp1 + 24 <= a < sp1 + 32)
    HLAWS HFIX CURA RDA RDFA FBA H0 HJ ltac:(intros a HZ; cbv beta in HZ; left; lia)
    ltac:(intros a Ha Hn; exact (KGy a Ha Hn)) GR2) as (CURB & RDB & RDFB & FBB).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARB.
  (* the leaf call at +0x348 *)
  assert (Hsp1b : spZ (ms_regs msB) = sp0 + (sp1 - sp0))
    by (unfold spZ; rewrite Y2; rewrite unsigned_lit_small by lia; lia).
  assert (Hmod16 : (sp1 - sp0) mod 16 = 0).
  { pose proof (Z.div_mod sp1 32 ltac:(lia)) as D32. rewrite Hs1m, Z.add_0_r in D32.
    pose proof (Z.div_mod sp0 16 ltac:(lia)) as D16. rewrite Hsp0a, Z.add_0_r in D16.
    replace (sp1 - sp0) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
  assert (HFRM : LMDc.DIGINET_MAC_IS_DIGIDESIGN_FRAME = 16) by reflexivity.
  destruct RDFB as (RDFv & RDFa & RDFh & RDFm & RDF0 & RDF63).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 LMDc.DIGINET_MAC_IS_DIGIDESIGN) mm rom) mdx) Q) end.
  eapply SRr_bind.
  { eapply (gx_call_leaf (fx := fx) (rc := rc) (SK := tfib_sink_head) segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0
      ((SRX_CID, pos) :: own) ly2 S2 W2 (ms_mem msB) _ (k + e) _ (YK11.getr (ms_regs msB) 1) _ HJ).
    intros memS HJS.
    eapply (LB.decode_leafb_journal (fx := fx) (SK := tfib_sink_head) B LAWS W2 (ms_regs msB) (ms_mem msB) STK sp0
      FP ly S W0 memS md0 ((SRX_CID, pos) :: own) ly2 S2 _ (k + e) (sp1 - sp0) LMDc.DIGINET_MAC_IS_DIGIDESIGN
      (Some (if DSpec.oui_of (DSpec.fr_src b) then 1 else 0)) [] (fun _ => True) HJS).
    - exact Hsp1b.
    - exact Hmod16.
    - lia.
    - lia.
    - rewrite Y1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
    - rewrite Y3. exact Hgp.
    - rewrite Y4. exact Htp.
    - intros a Ha. unfold LB.LCK.in_wr in Ha. inversion Ha.
    - intros HPRE.
      pose proof (LEAFC fx) as LF.
      unfold transport_leaf_at, LMD.transport_diginet_mac_is_digidesign_cg in LF.
      specialize (LF ly2 S2 W2 (ms_regs msB) (ms_mem msB) _ (F + SRX_F + 6) (DSpec.fr_src b) (sp0 - STK) HPRE Y10).
      cbv zeta in LF.
      assert (SPU : bv_unsigned (YK11.getr (ms_regs msB) (Z_to_bv 5 2)) = sp1).
      { change (YK11.getr (ms_regs msB) (Z_to_bv 5 2)) with (YK11.getr (ms_regs msB) (2%bv : bv 5)).
        rewrite Y2. apply unsigned_lit_small. lia. }
      apply LF; clear LF.
      + lia.
      + rewrite Hs6. lia.
      + apply (LB.decode_leafb_bytes_garr8 W2 (ms_mem msB) (F + SRX_F + 6) (DSpec.fr_src b));
          [exact (srxbdk_fsrc_garr8 W2 (ms_mem msB) F buf b fj H0 FBB) | lia | rewrite Hs6; lia].
      + rewrite SPU. eapply (LB.decode_leafb_stk_journal B); [exact HJS | lia | lia].
      + rewrite SPU. lia.
      + unfold LKA.off_stk. rewrite SPU. left. lia.
      + rewrite SPU. apply LB.decode_leafb_app_stack. lia.
      + rewrite SPU. apply LB.decode_leafb_app_stack. lia.
      + exact (LB.decode_leafb_asan_cells B HCELLS ly2 S2 W2 (ms_mem msB) _ (proj1 HJS)).
      + unfold LKA.off_stk. rewrite SPU. left. unfold ACells.GOT_CELL_K. lia.
      + unfold LKA.off_stk. rewrite SPU. left. unfold ACells.CELL_K. lia.
      + apply (LB.decode_leafb_addressable W2 (ms_mem msB) (F + SRX_F + 6) 3
          (fun x Hx => RDFa x ltac:(lia))); [lia | lia | unfold ACells.APPMEM_END; lia |].
        intros i Hi. unfold ACells.app_mem, ACells.LOWMEM_END, ACells.HIGHMEM_BEG, ACells.APPMEM_END.
        unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in RDFm.
        destruct RDFm as [Hmr | Hmr]; [left | right]; lia.
      + rewrite SPU. eapply (LB.decode_leafb_rng_journal B); [exact HJS | lia | lia].
      + exact (proj1 (LB.decode_leafb_rng_cells W2)).
      + exact (proj2 (LB.decode_leafb_rng_cells W2)).
      + apply (LB.decode_leafb_rng W2); [lia | lia |].
        intros a Ha. pose proof (RDFv a ltac:(lia)) as Hv.
        destruct (aview segs (w_H W2) (ms_mem msB) a) as [z|] eqn:Ez; [|contradiction].
        exact (LB.decode_leafb_aview_vis W2 (ms_mem msB) a z Ez).
      + exact (LB.decode_leafb_rng_shadow W2 (ms_mem msB) (F + SRX_F + 6) 3
          (fun x Hx => RDFa x ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)). }
  cbv beta. intros Wq cq _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hres3 & Heff3 & Hpres3 & _).
  assert (HRES : YK11.getr regs3 10 = w64 (if DSpec.oui_of (DSpec.fr_src b) then 1 else 0))
    by (apply Hres3; reflexivity).
  (* what the leaf kept: every byte outside its ESTACK window below sp1 *)
  assert (KD3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1) ->
    aview segs (w_H W2) mem3 a = aview segs (w_H W2) (ms_mem msB) a).
  { intros a Ha Hn. apply Heff3; [exact Ha | rewrite Hsp1b; lia |].
    intros HW. unfold LB.LCK.in_wr in HW. inversion HW. }
  assert (HtwC : tw_at TMAP_B (aview segs (w_H W2) mem3) Bw).
  { apply (tw_kept TMAP_B (aview segs (w_H W2) (ms_mem msB))); [exact HtwB|].
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KD3; lia. }
  assert (HVAL3 : val_mem segs (mrestrict (w_H W2) mem3) (sp1 + 24) 8 (SHADOW_OFF + (SRX_S + 116) / 8))
    by (apply (srxbdk_val_mem_move W2 (ms_mem msB) mem3 _ _ _ HVAL); intros x Hx; apply KD3; lia).
  destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 (ms_mem msB) _ e mem3 md3 (fun a : Z => sp1 - ESTACK <= a < sp1)
    HLAWS HFIX CURB RDB (conj RDFv (conj RDFa (conj RDFh (conj RDFm (conj RDF0 RDF63))))) FBB H0 HJ3
    ltac:(intros a HZ; cbv beta in HZ; left; lia) ltac:(intros a Ha Hn; exact (KD3 a Ha Hn)) Hpres3)
    as (CURC & RDC & RDFC & FBC).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARC.
  assert (HPRES : aregs_preserved (ms_regs msB) regs3) by exact HP3.
  assert (Z2 : YK11.getr regs3 2 = w64 sp1)
    by (transitivity (YK11.getr (ms_regs msB) 2); [exact (HPRES 2 ltac:(unfold acallee_saved; lia)) | exact Y2]).
  assert (Z3 : YK11.getr regs3 3 = YK11.getr regs 3)
    by (transitivity (YK11.getr (ms_regs msB) 3); [exact (HPRES 3 ltac:(unfold acallee_saved; lia)) | exact Y3]).
  assert (Z4 : YK11.getr regs3 4 = YK11.getr regs 4)
    by (transitivity (YK11.getr (ms_regs msB) 4); [exact (HPRES 4 ltac:(unfold acallee_saved; lia)) | exact Y4]).
  assert (Z8 : YK11.getr regs3 8 = w64 (spZ regs))
    by (transitivity (YK11.getr (ms_regs msB) 8); [exact (HPRES 8 ltac:(unfold acallee_saved; lia)) | exact Y8]).
  assert (Z9 : YK11.getr regs3 9 = w64 sp1)
    by (transitivity (YK11.getr (ms_regs msB) 9); [exact (HPRES 9 ltac:(unfold acallee_saved; lia)) | exact Y9]).
  assert (Z18 : YK11.getr regs3 18 = w64 F)
    by (transitivity (YK11.getr (ms_regs msB) 18); [exact (HPRES 18 ltac:(unfold acallee_saved; lia)) | exact Y18]).
  assert (Z19 : YK11.getr regs3 19 = w64 now)
    by (transitivity (YK11.getr (ms_regs msB) 19); [exact (HPRES 19 ltac:(unfold acallee_saved; lia)) | exact Y19]).
  assert (Z20 : YK11.getr regs3 20 = w64 SRX_S)
    by (transitivity (YK11.getr (ms_regs msB) 20); [exact (HPRES 20 ltac:(unfold acallee_saved; lia)) | exact Y20]).
  assert (Z21 : YK11.getr regs3 21 = w64 (SRX_S + 18152))
    by (transitivity (YK11.getr (ms_regs msB) 21); [exact (HPRES 21 ltac:(unfold acallee_saved; lia)) | exact Y21]).
  assert (Z22 : YK11.getr regs3 22 = w64 (F + SRX_F))
    by (transitivity (YK11.getr (ms_regs msB) 22); [exact (HPRES 22 ltac:(unfold acallee_saved; lia)) | exact Y22]).
  assert (Z23 : YK11.getr regs3 23 = w64 (F + SRX_F + 6))
    by (transitivity (YK11.getr (ms_regs msB) 23); [exact (HPRES 23 ltac:(unfold acallee_saved; lia)) | exact Y23]).
  assert (Z24 : YK11.getr regs3 24 = w64 (SRX_S + 116))
    by (transitivity (YK11.getr (ms_regs msB) 24); [exact (HPRES 24 ltac:(unfold acallee_saved; lia)) | exact Y24]).
  assert (Z25 : YK11.getr regs3 25 = w64 (SHADOW_OFF + F / 8))
    by (transitivity (YK11.getr (ms_regs msB) 25); [exact (HPRES 25 ltac:(unfold acallee_saved; lia)) | exact Y25]).
  assert (Z26 : YK11.getr regs3 26 = w64 F)
    by (transitivity (YK11.getr (ms_regs msB) 26); [exact (HPRES 26 ltac:(unfold acallee_saved; lia)) | exact Y26]).
  assert (Z27 : YK11.getr regs3 27 = w64 SHADOW_OFF)
    by (transitivity (YK11.getr (ms_regs msB) 27); [exact (HPRES 27 ltac:(unfold acallee_saved; lia)) | exact Y27]).
  (* +0x34c: `beq a0, zero` on the leaf's result *)
  destruct (srxbl_entry2 ly2 S2 W2 regs3 mem3 md3 HSC HARC Z21 Z27) as [HS2 SHOK2].
  clear HS SHOK HEI. rename HS2 into HS. rename SHOK2 into SHOK.
  assert (HEI : img_env VAL A_LIM (srxbl_E0 regs3)) by apply srxbl_env0.
  assert (EE3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (srxbl_E0 regs3) n = YK11.getr regs3 rr)
    by (intros n rr Hn; exact (srxbl_ew0 regs3 n rr Hn)).
  assert (D10b : sv_denot (srxbl_E0 regs3) (SOff 10 0) =
    Z_to_bv 64 (if DSpec.oui_of (DSpec.fr_src b) then 1 else 0))
    by (cbn [sv_denot]; rewrite (EE3 10%nat 10%bv eq_refl), HRES, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg ?pcx ?mm ?rom) ?mdx) ?Q =>
    replace pcx with (Z_to_bv 64 (BASE + SRXBL_C2)) by (symmetry; exact Y1) end.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* not Digidesign: +0x418 .. +0x428 to the ignored cut *)
    cbn [branch_taken] in Hc0. rewrite D10b in Hc0.
    change (sv_denot (srxbl_E0 regs3) (SLit 0)) with (Z_to_bv 64 0) in Hc0.
    assert (HOUI : DSpec.oui_of (DSpec.fr_src b) = false).
    { destruct (DSpec.oui_of (DSpec.fr_src b)); [|reflexivity].
      rewrite (srxbl_eqb_lit 1 0) in Hc0 by lia. discriminate Hc0. }
    pose proof (srxb_m_oui timg_B TF Bw b now H0 HMAC HK0 HCMD HOUI) as HMD.
    rewrite Hm in HMD.
    destruct (srxb_some_inv Bw' (srx_ign Bw) r DLib.DIGINET_OK HMD) as [EBw Er].
    paj_run_to_tok RUNTO HS HJ3 SHOK YC4b.Bspan SRXB_IGN.
    { srxbdk_awr_rs. apply awr_ok_x_nil. }
    srxbdk_kreg HS EE3 regs3 (2%bv : bv 5) 2%nat Z2 V2.
    srxbdk_kreg HS EE3 regs3 (3%bv : bv 5) 3%nat Z3 V3.
    srxbdk_kreg HS EE3 regs3 (4%bv : bv 5) 4%nat Z4 V4.
    srxbdk_kreg HS EE3 regs3 (8%bv : bv 5) 8%nat Z8 V8.
    srxbdk_kreg HS EE3 regs3 (9%bv : bv 5) 9%nat Z9 V9.
    srxbdk_kreg HS EE3 regs3 (18%bv : bv 5) 18%nat Z18 V18.
    srxbdk_kreg HS EE3 regs3 (19%bv : bv 5) 19%nat Z19 V19.
    srxbdk_kreg HS EE3 regs3 (20%bv : bv 5) 20%nat Z20 V20.
    srxbdk_kreg HS EE3 regs3 (21%bv : bv 5) 21%nat Z21 V21.
    srxbdk_kreg HS EE3 regs3 (22%bv : bv 5) 22%nat Z22 V22.
    srxbdk_kreg HS EE3 regs3 (25%bv : bv 5) 25%nat Z25 V25.
    srxbdk_kreg HS EE3 regs3 (26%bv : bv 5) 26%nat Z26 V26.
    srxbdk_kreg HS EE3 regs3 (27%bv : bv 5) 27%nat Z27 V27.
    srxbdk_reg HS (10%bv : bv 5) (w64 0) V10 ltac:(cbn [sv_denot]; reflexivity).
    srxbdk_reg HS (11%bv : bv 5) (w64 SRXB_RXIGN) V11
      ltac:(rewrite denot_lit_U; f_equal;
            rewrite (U_atom_off (srxbl_E0 regs3) 21%nat (SRX_S + 18152) 32
              ltac:(rewrite (EE3 21%nat 21%bv eq_refl); exact Z21)) by lia;
            unfold SRXB_RXIGN; lia).
    assert (KGz : (forall a, aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem3 a) /\
      (forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem ms) a)).
    { apply (srxbdk_kept_run W2 _ _ mem3 (ms_mem ms) HFr); [|exact HG].
      intros x Hx. destruct Hx as (rr & Hr & Hb). vm_compute in Hr.
      repeat (destruct Hr as [Hr | Hr];
        [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]).
      destruct Hr. }
    destruct KGz as [KD4 GR4].
    clear HF HFr HG. rename ms into msD.
    assert (HtwD : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msD)) Bw)
      by (apply (tw_kept TMAP_B (aview segs (w_H W2) mem3)); [exact HtwC | intros x _; exact (KD4 x)]).
    destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw'
      pos sp1 F ly2 S2 W2 mem3 md3 e (ms_mem msD) _ (fun _ : Z => False)
      HLAWS HFIX CURC RDC RDFC FBC H0 HJ3 ltac:(intros a HZ; destruct HZ)
      ltac:(intros a _ _; exact (KD4 a)) GR4) as (CURD & RDD & RDFD & FBD).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_IGN)) mm rom) mdx) Q) end.
    apply (IGN HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' Bw
      pos sp1 F ly2 S2 W2 (ms_mem msD) _ e (ms_regs msD) HFIX CURD HtwD Hfn EBw).
    unfold srxb_regs_ign, srxb_regs_base, srxb_regs_core.
    refine (conj (conj (conj V2 (conj V3 (conj V4 (conj V8 (conj V9 (conj V18 (conj V19 (conj V20 (conj V25
      (conj V26 V27)))))))))) (conj V21 V22)) (conj _ V11)).
    rewrite V10, Er. reflexivity.
  + (* Digidesign: run 3, the memcpy, run 4, to the closed cut *)
    cbn [branch_taken] in Hc0. rewrite D10b in Hc0.
    change (sv_denot (srxbl_E0 regs3) (SLit 0)) with (Z_to_bv 64 0) in Hc0.
    assert (HOUI : DSpec.oui_of (DSpec.fr_src b) = true).
    { destruct (DSpec.oui_of (DSpec.fr_src b)); [reflexivity|].
      rewrite (srxbl_eqb_lit 0 0) in Hc0 by lia. discriminate Hc0. }
    (* run 3, +0x350 .. +0x358: a0 = s + 120, a2 = 6, a1 = f + 6, up to the memcpy call *)
    paj_run_tok RUN HS HJ3 SHOK YC4b.Bspan.
    { srxbdk_awr_rs. apply awr_ok_x_nil. }
    srxbdk_kreg HS EE3 regs3 (2%bv : bv 5) 2%nat Z2 V2.
    srxbdk_kreg HS EE3 regs3 (3%bv : bv 5) 3%nat Z3 V3.
    srxbdk_kreg HS EE3 regs3 (4%bv : bv 5) 4%nat Z4 V4.
    srxbdk_kreg HS EE3 regs3 (8%bv : bv 5) 8%nat Z8 V8.
    srxbdk_kreg HS EE3 regs3 (9%bv : bv 5) 9%nat Z9 V9.
    srxbdk_kreg HS EE3 regs3 (18%bv : bv 5) 18%nat Z18 V18.
    srxbdk_kreg HS EE3 regs3 (19%bv : bv 5) 19%nat Z19 V19.
    srxbdk_kreg HS EE3 regs3 (20%bv : bv 5) 20%nat Z20 V20.
    srxbdk_kreg HS EE3 regs3 (21%bv : bv 5) 21%nat Z21 V21.
    srxbdk_kreg HS EE3 regs3 (22%bv : bv 5) 22%nat Z22 V22.
    srxbdk_kreg HS EE3 regs3 (24%bv : bv 5) 24%nat Z24 V24.
    srxbdk_kreg HS EE3 regs3 (25%bv : bv 5) 25%nat Z25 V25.
    srxbdk_kreg HS EE3 regs3 (26%bv : bv 5) 26%nat Z26 V26.
    srxbdk_kreg HS EE3 regs3 (27%bv : bv 5) 27%nat Z27 V27.
    srxbdk_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 26692)) V1 ltac:(apply codeptr_val; exact HEI).
    srxbdk_reg HS (10%bv : bv 5) (w64 (SRX_S + 120)) V10
      ltac:(rewrite denot_lit_U; f_equal;
            rewrite (U_atom_off (srxbl_E0 regs3) 20%nat SRX_S 120
              ltac:(rewrite (EE3 20%nat 20%bv eq_refl); exact Z20)) by lia; reflexivity).
    srxbdk_reg HS (11%bv : bv 5) (w64 (F + SRX_F + 6)) V11
      ltac:(cbn [sv_denot]; rewrite (EE3 23%nat 23%bv eq_refl), Z23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    srxbdk_reg HS (12%bv : bv 5) (w64 6) V12 ltac:(cbn [sv_denot]; reflexivity).
    assert (KGc : (forall a, aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem3 a) /\
      (forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem ms) a)).
    { apply (srxbdk_kept_run W2 _ _ mem3 (ms_mem ms) HFr); [|exact HG].
      intros x Hx. destruct Hx as (rr & Hr & Hb). vm_compute in Hr.
      repeat (destruct Hr as [Hr | Hr];
        [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia |]).
      destruct Hr. }
    destruct KGc as [KDc GRc].
    clear HF HFr HG. rename ms into msC.
    assert (HtwE : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msC)) Bw)
      by (apply (tw_kept TMAP_B (aview segs (w_H W2) mem3)); [exact HtwC | intros x _; exact (KDc x)]).
    assert (HVALc : val_mem segs (mrestrict (w_H W2) (ms_mem msC)) (sp1 + 24) 8 (SHADOW_OFF + (SRX_S + 116) / 8))
      by (apply (srxbdk_val_mem_move W2 mem3 (ms_mem msC) _ _ _ HVAL3); intros x _; exact (KDc x)).
    destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw'
      pos sp1 F ly2 S2 W2 mem3 md3 e (ms_mem msC) _ (fun _ : Z => False)
      HLAWS HFIX CURC RDC RDFC FBC H0 HJ3 ltac:(intros a HZ; destruct HZ)
      ltac:(intros a _ _; exact (KDc a)) GRc) as (CURE & RDE & RDFE & FBE).
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARE.
    destruct RDFE as (RDFv2 & RDFa2 & RDFh2 & RDFm2 & RDF02 & RDF632).
    (* the memcpy at +0x35c: g_s.desk_mac := the six bytes at f + 6 *)
    assert (Hsp1c : spZ (ms_regs msC) = sp0 + (sp1 - sp0))
      by (unfold spZ; rewrite V2; rewrite unsigned_lit_small by lia; lia).
    assert (HDISJ : SRX_S + 120 + 6 <= F + SRX_F + 6 \/ F + SRX_F + 6 + 6 <= SRX_S + 120).
    { destruct (Z_le_dec (SRX_S + 126) (F + SRX_F + 6)) as [HA|HA]; [left; lia|].
      destruct (Z_le_dec (F + SRX_F + 12) (SRX_S + 120)) as [HB'|HB']; [right; lia|].
      exfalso. set (a := Z.max (SRX_S + 120) (F + SRX_F + 6)).
      assert (Ha1 : SRX_S + 120 <= a < SRX_S + 126) by (unfold a; lia).
      assert (Ha2 : F + SRX_F + 6 <= a < F + SRX_F + 12) by (unfold a; lia).
      exact (NGF a ltac:(lia) (srxbdk_inG a ltac:(unfold TW.SZ_g_s; lia))). }
    assert (D1 : (SRX_S + 120) / 64 * 64 = SRX_S + 64) by (vm_compute; reflexivity).
    assert (D2 : (SRX_S + 120 + 6 - 1) / 64 * 64 = SRX_S + 64) by (vm_compute; reflexivity).
    destruct (decode_zshadow_ra B ly2 S2 W2 (ms_mem msC) _ SRX_S (SRX_S + TW.SZ_g_s) (SRX_S + 120) 6 HARE
      (proj1 HSC) ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as [RAd HULLd].
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q) end.
    eapply SRr_bind.
    { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OCpy (transportb_sigma TB___asan_memcpy)
        (AMEMCPY fx) TG.G_HARNESS_B W2 (ms_regs msC) (ms_mem msC) STK sp0 FP ly S W0 mem0 md0
        ((SRX_CID, pos) :: own) ly2 S2 _ (k + e) (SRX_S + 120) (F + SRX_F + 6) 6 (sp1 - sp0)
        (Z_to_bv 64 (BASE + 26692)) HGX G_HARNESS_B_rw HJ3 V10 V11 V12).
      - lia.
      - lia.
      - lia.
      - exact Hsp1c.
      - exact Hmod16.
      - lia.
      - lia.
      - rewrite V3. exact Hgp.
      - rewrite V4. exact Htp.
      - exact V1.
      - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
      - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ3|].
        intros a Ha. right. apply srxbdk_inG. unfold TW.SZ_g_s. lia.
      - left. unfold kLowMemEnd. lia.
      - exact RAd.
      - intros _. exact HULLd.
      - cbn iota. split; [lia|]. split; [lia|]. split.
        { intros a Ha. split; [apply RDFv2; lia|]. rewrite Hsp1c. lia. }
        split; [exact HDISJ|]. split.
        { unfold amem_range in RDFm2 |- *. destruct RDFm2 as [Hmr | Hmr]; [left | right]; lia. }
        split.
        { exact (range_addressable_sub _ _ (F + SRX_F) FRAME_F_SIZE (F + SRX_F + 6) 6 RDFa2 ltac:(lia) ltac:(lia)). }
        intros _. exact (trans_hull_sub _ (F + SRX_F) FRAME_F_SIZE (F + SRX_F + 6) 6 RDFh2 ltac:(lia) ltac:(lia)). }
    cbv beta. intros Wq cq _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & H10d & Hcpy & Heff4 & Hpres4).
    (* what the memcpy kept, and the bytes it wrote *)
    assert (KD5 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1) -> ~ (SRX_S + 120 <= a < SRX_S + 126) ->
      aview segs (w_H W2) mem4 a = aview segs (w_H W2) (ms_mem msC) a).
    { intros a Ha Hn1 Hn2. apply Heff4; [exact Ha | intros X; apply Hn2; lia | lia]. }
    assert (HtwF : tw_at TMAP_B (aview segs (w_H W2) mem4) (TW.set_S_desk_mac Bw (DSpec.fr_src b))).
    { unfold TW.set_S_desk_mac, TW.A_S_desk_mac.
      apply (tw_fill TMAP_B (aview segs (w_H W2) (ms_mem msC)) _ Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 120
        (DSpec.fr_src b) TMAP_B_ok HtwE TMAP_B_g_s ltac:(lia) ltac:(rewrite Hs6; unfold TW.SZ_g_s; lia)).
      - intros i Hi. rewrite Hs6 in Hi.
        change (TB_g_s + 120 + i) with (SRX_S + 120 + i). rewrite (Hcpy i Hi).
        replace (F + SRX_F + 6 + i) with (F + SRX_F + Z.of_nat (6 + Z.to_nat i)) by lia.
        destruct FBE as (Hfj4 & HFG4).
        rewrite (srxbdk_view_garr8 W2 (ms_mem msC) (F + SRX_F) _ (6 + Z.to_nat i) HFG4
          ltac:(rewrite (srxbdk_fbytes_len buf b fj H0 Hfj4); lia)).
        rewrite (srxbdk_fsrc buf b fj (Z.to_nat i) H0 ltac:(lia)). reflexivity.
      - intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
        apply KD5; [lia | lia | intros X; apply Hn; rewrite Hs6; unfold SRX_S in X; lia]. }
    assert (HVALd : val_mem segs (mrestrict (w_H W2) mem4) (sp1 + 24) 8 (SHADOW_OFF + (SRX_S + 116) / 8))
      by (apply (srxbdk_val_mem_move W2 (ms_mem msC) mem4 _ _ _ HVALc); intros x Hx; apply KD5; lia).
    destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw'
      pos sp1 F ly2 S2 W2 (ms_mem msC) _ e mem4 md4
      (fun a : Z => (sp1 - ESTACK <= a < sp1) \/ (SRX_S + 120 <= a < SRX_S + 126))
      HLAWS HFIX CURE RDE (conj RDFv2 (conj RDFa2 (conj RDFh2 (conj RDFm2 (conj RDF02 RDF632))))) FBE H0 HJ4
      ltac:(intros a HZ; cbv beta in HZ; destruct HZ as [HZ | HZ];
            [left; lia
            | right; split; [right; left; unfold MLC.twb_fld, TW.A_S_desk_mac, TW.OFF_g_s, TB_g_s, TS0.DIGINET_MAC_LEN;
                             unfold SRX_S, TB_g_s in HZ; lia
                            | apply srxbdk_inG; unfold TW.SZ_g_s; lia]])
      ltac:(intros a Ha Hn; apply KD5; [exact Ha | intros X; apply Hn; left; exact X
                                       | intros X; apply Hn; right; exact X]) Hpres4)
      as (CURF & RDF & RDFF & FBF).
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HARF.
    assert (HPRES4 : aregs_preserved (ms_regs msC) regs4) by exact HP4.
    assert (U9r : YK11.getr regs4 9 = w64 sp1)
      by (transitivity (YK11.getr (ms_regs msC) 9); [exact (HPRES4 9 ltac:(unfold acallee_saved; lia)) | exact V9]).
    assert (U20r : YK11.getr regs4 20 = w64 SRX_S)
      by (transitivity (YK11.getr (ms_regs msC) 20); [exact (HPRES4 20 ltac:(unfold acallee_saved; lia)) | exact V20]).
    assert (U27r : YK11.getr regs4 27 = w64 SHADOW_OFF)
      by (transitivity (YK11.getr (ms_regs msC) 27); [exact (HPRES4 27 ltac:(unfold acallee_saved; lia)) | exact V27]).
    assert (U24r : YK11.getr regs4 24 = w64 (SRX_S + 116))
      by (transitivity (YK11.getr (ms_regs msC) 24); [exact (HPRES4 24 ltac:(unfold acallee_saved; lia)) | exact V24]).
    (* run 4, +0x360 .. +0x370: the slot read back, its shadow byte checked, desk_known := 1 *)
    destruct (srxbl_entry3 ly2 S2 W2 regs4 mem4 md4 sp1 HSC HARF U9r U20r U24r U27r ltac:(lia) Hs1m HVALd)
      as [HS4 SHOK4].
    clear HS SHOK HEI. rename HS4 into HS. rename SHOK4 into SHOK.
    assert (HEI : img_env VAL A_LIM (srxbl_E0 regs4)) by apply srxbl_env0.
    assert (EE4 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (srxbl_E0 regs4) n = YK11.getr regs4 rr)
      by (intros n rr Hn; exact (srxbl_ew0 regs4 n rr Hn)).
    assert (U24e : bv_unsigned (ew (srxbl_E0 regs4) 24) = SRX_S + 116)
      by (rewrite (EE4 24%nat 24%bv eq_refl), U24r; apply unsigned_lit_small; lia).
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg ?pcx ?mm ?rom) ?mdx) ?Q =>
      replace pcx with (Z_to_bv 64 (BASE + SRXBL_C3)) by reflexivity end.
    paj_run_to_tok RUNTO HS HJ4 SHOK YC4b.Bspan SRXB_CLOSED.
    { srxbdk_awr_rs.
      apply awr_ok_x_cons;
      [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
      apply awr_ok_x_cons_g;
      [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U24e in Ha;
        apply srxbdk_inG; unfold TW.SZ_g_s; lia |].
      apply awr_ok_x_nil. }
    lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E5 := EF) in * end.
    assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew (srxbl_E0 regs4) n)
      by (intros n Hn; unfold E5; repeat rewrite ew_ewset_other by lia; reflexivity).
    (* desk_known's four bytes now hold 1 *)
    srxbdk_region HS 1%nat HRdk.
    assert (U24f : bv_unsigned (ew E5 24) = SRX_S + 116) by (rewrite E5lo by lia; exact U24e).
    assert (ZD : forall j, (j < 4)%nat ->
      aview segs (w_H W2) (ms_mem ms) (SRX_S + 116 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)).
    { apply (srxbl_aview_of_val (w_H W2) (ms_mem ms) (SRX_S + 116) 4 1).
      rewrite <- (Z.add_0_r (SRX_S + 116)) at 1.
      exact (can_field_of_region E5 _ 24 (SRX_S + 116) _ 0 4 0 4 0 4%N (SLit 1) 1 HRdk U24f ltac:(srxbdk_in)
        eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
    clear HRdk.
    assert (KD6 : forall a, 0 <= a < 2 ^ 64 -> ~ (SRX_S + 116 <= a < SRX_S + 120) ->
      aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem4 a).
    { intros a Ha Hn.
      refine (kept_of_frame _ _ (w_H W2) mem4 (ms_mem ms) (fun x => SRX_S + 116 <= x < SRX_S + 120) HFr _ a Ha Hn).
      intros bb wlo whi x Hin Hx.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U24e in Hx; lia |]).
      destruct Hin. }
    assert (GR6 : forall a, apresent (w_H W2) mem4 a -> apresent (w_H W2) (ms_mem ms) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    (* the registers at the closed cut: kept by the memcpy (callee-saved) and by run 4 (it writes a0 only) *)
    assert (EE5 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E5 n = YK11.getr regs4 rr).
    { intros n rr Hn. assert (Hn32 : (n < 32)%nat).
      { pose proof (bv_unsigned_in_range 5 rr) as Hrg. unfold bv_modulus in Hrg.
        change (2 ^ Z.of_N 5) with 32 in Hrg. lia. }
      rewrite (E5lo n ltac:(lia)). exact (EE4 n rr Hn). }
    assert (P2 : YK11.getr regs4 2 = w64 sp1)
      by (transitivity (YK11.getr (ms_regs msC) 2); [exact (HPRES4 2 ltac:(unfold acallee_saved; lia)) | exact V2]).
    assert (P3 : YK11.getr regs4 3 = YK11.getr regs 3)
      by (transitivity (YK11.getr (ms_regs msC) 3); [exact (HPRES4 3 ltac:(unfold acallee_saved; lia)) | exact V3]).
    assert (P4 : YK11.getr regs4 4 = YK11.getr regs 4)
      by (transitivity (YK11.getr (ms_regs msC) 4); [exact (HPRES4 4 ltac:(unfold acallee_saved; lia)) | exact V4]).
    assert (P8 : YK11.getr regs4 8 = w64 (spZ regs))
      by (transitivity (YK11.getr (ms_regs msC) 8); [exact (HPRES4 8 ltac:(unfold acallee_saved; lia)) | exact V8]).
    assert (P18 : YK11.getr regs4 18 = w64 F)
      by (transitivity (YK11.getr (ms_regs msC) 18); [exact (HPRES4 18 ltac:(unfold acallee_saved; lia)) | exact V18]).
    assert (P19 : YK11.getr regs4 19 = w64 now)
      by (transitivity (YK11.getr (ms_regs msC) 19); [exact (HPRES4 19 ltac:(unfold acallee_saved; lia)) | exact V19]).
    assert (P21 : YK11.getr regs4 21 = w64 (SRX_S + 18152))
      by (transitivity (YK11.getr (ms_regs msC) 21); [exact (HPRES4 21 ltac:(unfold acallee_saved; lia)) | exact V21]).
    assert (P22 : YK11.getr regs4 22 = w64 (F + SRX_F))
      by (transitivity (YK11.getr (ms_regs msC) 22); [exact (HPRES4 22 ltac:(unfold acallee_saved; lia)) | exact V22]).
    assert (P25 : YK11.getr regs4 25 = w64 (SHADOW_OFF + F / 8))
      by (transitivity (YK11.getr (ms_regs msC) 25); [exact (HPRES4 25 ltac:(unfold acallee_saved; lia)) | exact V25]).
    assert (P26 : YK11.getr regs4 26 = w64 F)
      by (transitivity (YK11.getr (ms_regs msC) 26); [exact (HPRES4 26 ltac:(unfold acallee_saved; lia)) | exact V26]).
    srxbdk_kreg HS EE5 regs4 (2%bv : bv 5) 2%nat P2 Q2.
    srxbdk_kreg HS EE5 regs4 (3%bv : bv 5) 3%nat P3 Q3.
    srxbdk_kreg HS EE5 regs4 (4%bv : bv 5) 4%nat P4 Q4.
    srxbdk_kreg HS EE5 regs4 (8%bv : bv 5) 8%nat P8 Q8.
    srxbdk_kreg HS EE5 regs4 (9%bv : bv 5) 9%nat U9r Q9.
    srxbdk_kreg HS EE5 regs4 (18%bv : bv 5) 18%nat P18 Q18.
    srxbdk_kreg HS EE5 regs4 (19%bv : bv 5) 19%nat P19 Q19.
    srxbdk_kreg HS EE5 regs4 (20%bv : bv 5) 20%nat U20r Q20.
    srxbdk_kreg HS EE5 regs4 (21%bv : bv 5) 21%nat P21 Q21.
    srxbdk_kreg HS EE5 regs4 (22%bv : bv 5) 22%nat P22 Q22.
    srxbdk_kreg HS EE5 regs4 (25%bv : bv 5) 25%nat P25 Q25.
    srxbdk_kreg HS EE5 regs4 (26%bv : bv 5) 26%nat P26 Q26.
    srxbdk_kreg HS EE5 regs4 (27%bv : bv 5) 27%nat U27r Q27.
    (* the world srx_learn Bw b: desk_known := 1 on top of desk_mac := fr_src b *)
    assert (HtwG : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms)) (srx_learn Bw b)).
    { unfold srx_learn, TW.set_S_desk_known, TW.A_S_desk_known.
      apply (tw_write TMAP_B (aview segs (w_H W2) mem4) _ (TW.set_S_desk_mac Bw (DSpec.fr_src b))
        TW.OFF_g_s TB_g_s TW.SZ_g_s 116 4 1 TMAP_B_ok HtwF TMAP_B_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      - intros j Hj. change (TB_g_s + 116 + Z.of_nat j) with (SRX_S + 116 + Z.of_nat j). exact (ZD j Hj).
      - intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
        apply KD6; [lia | intros X; apply Hn; unfold SRX_S in X; lia]. }
    clear HF HFr HG. rename ms into msD.
    destruct (srxbdk_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw'
      pos sp1 F ly2 S2 W2 mem4 md4 e (ms_mem msD) _ (fun a : Z => SRX_S + 116 <= a < SRX_S + 120)
      HLAWS HFIX CURF RDF RDFF FBF H0 HJ4
      ltac:(intros a HZ; cbv beta in HZ; right; split;
            [right; right; left; unfold MLC.twb_fld, TW.A_S_desk_known, TW.OFF_g_s, TB_g_s;
             unfold SRX_S, TB_g_s in HZ; lia
            | apply srxbdk_inG; unfold TW.SZ_g_s; lia])
      ltac:(intros a Ha Hn; exact (KD6 a Ha Hn)) GR6) as (CURG & RDG & RDFG & FBG).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_CLOSED)) mm rom) mdx) Q) end.
    apply (CLOSED HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw'
      (srx_learn Bw b) pos sp1 F ly2 S2 W2 (ms_mem msD) _ e (ms_regs msD) HFIX CURG RDG RDFG FBG HtwG).
    * rewrite (srxbl_fn Bw b HWL H0). exact Hfn.
    * exact (proj1 INV Bw b HWL Hinv).
    * split; [exact H0|]. split; [exact HMAC|]. right.
      split; [exact HK0|]. split; [exact HCMD|]. split; [exact HOUI | reflexivity].
    * unfold srxb_regs_base, srxb_regs_core.
      exact (conj (conj Q2 (conj Q3 (conj Q4 (conj Q8 (conj Q9 (conj Q18 (conj Q19 (conj Q20 (conj Q25
        (conj Q26 Q27)))))))))) (conj Q21 Q22)).
Qed.

End l.

(* The learn piece of the image-B walk of diginet_session_rx (SrxBCut.v srxb_learn_stmt), at every machine, run
   ceiling, record and meter. *)
Theorem srxb_learn_ok : forall fx rc B MT, @srxb_learn_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@srxbl_holds fx rc B MT). Qed.
