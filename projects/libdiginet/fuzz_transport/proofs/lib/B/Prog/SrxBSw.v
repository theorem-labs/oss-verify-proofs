(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 1137 of its 1231 lines of code are new or changed and 465 lines of the source are left out. *)
(* SrxBSw: the switch piece of the image-B walk of diginet_session_rx (fuzz_transport.asan-ubsan 0x87784; the cuts are
   those of lib/B/Prog/SrxBCut.v), Theorem srxb_sw_ok : srxb_sw_stmt. It starts at the closed cut (+0x374) and ends in
   the cuts the switch reaches. The code of the range is image A's (lib/A/Prog/SrxSw.v) at image B's pcs, and has no
   UBSan trap of its own. The runs are the position-abstract runs of lib/B/Prog/TransportGRunB.v paj_run_x /
   paj_run_to_x over the caller's G journal:
     run A  +0x374 .. +0x38c  a0 = s + 112, the check of the 4-byte load of g_s.state (its shadow byte read 0: the shadow
                              entry of [s + 112, s + 120)), a1 = the sign-extended state, a0 = 3, up to `bne a1, a0`;
     +0x390                   S_CLOSED: +0x394 .. +0x398 (a0 = 0, `j` to the release cut: srxb_rel_at, the model's world
                              is Bx by srxb_acc_closed); any other state: on to +0x39c (srxb_acc_open);
     run B  +0x39c .. +0x3d4  the checked load and store of stats.rx_frames + 1 and the checked store of now at
                              last_rx_us (shadow entries of [s + 18152, s + 18160) and [s + 176, s + 184)), a2 = h.cmd (the
                              byte at f + 30: fr_cmd b, cell 30 of frame_f_bytes), a3 = 223; the memory then relates to
                              srx_w1 Bx now (srxbs_tw_w1), and the facts every cut carries are moved to that memory (no
                              byte outside G changed: srxbs_cur_g, srxbs_rd_g);
     +0x3d8 .. +0x444         the switch of :298-316, from a state with no region (srxbs_tail): `bge 223, cmd`, `beq cmd,
                              0`, `bne cmd, 0xa0`, `bgeu cmd - 0xe0, 2`, `bne cmd, 0xe3` and the DISCONNECT test of :310
                              (`addiw a1, a1, -1`, `bltu 1, a1`) lead to the arm cuts srxb_ann_at (+0x3e8), srxb_ack_at
                              (+0x408), srxb_data_at (+0x48c) and srxb_lost_at (+0x448, image B's inlined session_lost),
                              to the tick cut (+0x4c0, the world srx_w1 Bx now: srxb_sw_stay), or to the ignored arm;
     run D  +0x4a0 .. +0x4bc  the checked increment of stats.rx_ignored (shadow entry of [s + 18184, s + 18192)), then the
                              tick cut (the world srx_ign (srx_w1 Bx now): srxb_sw_other) (srxbs_ign).
   The error paths of the range (__asan_report_load4 at +0x4f4 through +0x4e8, __asan_report_load8 at +0x538,
   __asan_report_store8 at +0x53c, __asan_report_load8 at +0x540) are not reached: each `bne` before them tests a shadow
   byte of g_s's payload, which the run reads as 0 from its shadow entry (trans_srx_cells: g_s's payload has shadow 0),
   so each branch falls through. A run whose start state has no writable byte leaves the memory as it was
   (srxbs_mem_eq). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality Classical_Prop.
From Stdlib Require Znumtheory.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YK00 YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_rx_cg SrxBCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_parse_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YK00 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK00.
Module YO0f := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YO0f.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module PParse := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* s11, the shadow base, is the base of every shadow entry. *)
Definition SRXBS_Bx : sv := SOff 27 0.

(* run A, +0x374 .. +0x390: g_s.state (atom 32, its 4 bytes) read through s4 = s (atom 20). *)
Definition SRXBS_RST : YP09.region :=
  YP09.mkRegion (Some 20%nat) 112 116 0 0 [YP09.mkChunk 112 (YP09.CVal 4 (SOff 32 0))].
Definition srxbs_factsA : facts :=
  mkFacts [(20%nat, mkAF SRX_S SRX_S 6); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_srxbsA : sstate := mkSS SRXB_CLOSED sr_atoms [SRXBS_RST] None srxbs_factsA.
Definition SRXBS_SHA : list shent := [mkSHE 20 112 120].

(* run B, +0x39c .. +0x3d8: stats.rx_frames (atom 32) through s5 = s + 18152 (atom 21), last_rx_us through s4, and
   h.cmd (atom 33) through s6 = f (atom 22). *)
Definition SRXBS_C2 : Z := AF_diginet_session_rx + 0x39c.
Definition SRXBS_RFR : YP09.region :=
  YP09.mkRegion (Some 21%nat) 0 8 0 8 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 32 0))].
Definition SRXBS_RLAST : YP09.region := YP09.mkRegion (Some 20%nat) 176 184 176 184 [].
Definition SRXBS_RCMD : YP09.region :=
  YP09.mkRegion (Some 22%nat) 30 31 0 0 [YP09.mkChunk 30 (YP09.CVal 1 (SOff 33 0))].
Definition srxbs_factsB : facts :=
  mkFacts [(20%nat, mkAF SRX_S SRX_S 6); (21%nat, mkAF (SRX_S + 18152) (SRX_S + 18152) 3);
           (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 255 0)] [] [].
Definition ss_srxbsB : sstate := mkSS SRXBS_C2 sr_atoms [SRXBS_RFR; SRXBS_RLAST; SRXBS_RCMD] None srxbs_factsB.
Definition SRXBS_SHB : list shent := [mkSHE 21 0 8; mkSHE 20 176 184].

(* the switch, +0x3d8 .. : no region (a1 = the state, a2 = h.cmd, a3 = 223 in registers). *)
Definition SRXBS_C3 : Z := AF_diginet_session_rx + 0x3d8.
Definition ss_srxbsC : sstate := mkSS SRXBS_C3 sr_atoms [] None (mkFacts [] [] []).

(* run D, +0x4a0 .. +0x4c0: stats.rx_ignored (atom 32) through s5. *)
Definition SRXBS_C4 : Z := AF_diginet_session_rx + 0x4a0.
Definition SRXBS_RIGN : YP09.region :=
  YP09.mkRegion (Some 21%nat) 32 40 32 40 [YP09.mkChunk 32 (YP09.CVal 8 (SOff 32 0))].
Definition srxbs_factsD : facts :=
  mkFacts [(21%nat, mkAF (SRX_S + 18152) (SRX_S + 18152) 3); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_srxbsD : sstate := mkSS SRXBS_C4 sr_atoms [SRXBS_RIGN] None srxbs_factsD.
Definition SRXBS_SHD : list shent := [mkSHE 21 32 40].

(* ------------------------------------------------------------------ *)
(* The model's worlds and paths (no machine)                           *)
(* ------------------------------------------------------------------ *)

Lemma srxbs_w1_eq : forall Bx now, srx_w1 Bx now =
  TW.upd (TW.upd Bx (TW.OFF_g_s + 18152) (TW.put 8 (TS0.u64 (TW.u_at Bx (TW.OFF_g_s + 18152) 8 + 1))))
    (TW.OFF_g_s + 176) (TW.put 8 now).
Proof. intros Bx now. reflexivity. Qed.

Lemma srxbs_ign_eq : forall Bs, srx_ign Bs =
  TW.upd Bs (TW.OFF_g_s + 18184) (TW.put 8 (TS0.u64 (TW.u_at Bs (TW.OFF_g_s + 18184) 8 + 1))).
Proof. intros Bs. reflexivity. Qed.

Lemma srxbs_len_upd8 : forall (Bx : list byte) k v, length Bx = Z.to_nat TW.W_LEN -> 0 <= k -> k + 8 <= TW.W_LEN ->
  length (TW.upd Bx k (TW.put 8 v)) = Z.to_nat TW.W_LEN.
Proof.
intros Bx k v HL Hk Hk8.
assert (LZ : Z.of_nat (length Bx) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
rewrite TWL.length_upd_put; [exact HL | exact Hk | rewrite LZ; exact Hk8].
Qed.

(* A store of 8 bytes misses a field that lies apart from it. *)
Lemma srxbs_u_out8 : forall (Bx : list byte) k v k' (n : nat), length Bx = Z.to_nat TW.W_LEN ->
  0 <= k -> k + 8 <= TW.W_LEN -> 0 <= k' -> (k' + Z.of_nat n <= k \/ k + 8 <= k') ->
  TW.u_at (TW.upd Bx k (TW.put 8 v)) k' n = TW.u_at Bx k' n.
Proof.
intros Bx k v k' n HL Hk Hk8 Hk' Hd.
assert (LZ : Z.of_nat (length Bx) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
apply TWL.u_at_upd_out; [exact Hk | exact Hk' | | rewrite TWL.length_put, LZ; exact Hk8].
rewrite TWL.length_put. destruct Hd as [Hd | Hd]; [left; exact Hd | right; exact Hd].
Qed.

Lemma srxbs_len_w1 : forall Bx now, length Bx = Z.to_nat TW.W_LEN -> length (srx_w1 Bx now) = Z.to_nat TW.W_LEN.
Proof.
intros Bx now HL. rewrite srxbs_w1_eq.
apply srxbs_len_upd8; [apply srxbs_len_upd8; [exact HL | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_s, TW.W_LEN; lia] |
  unfold TW.OFF_g_s; lia | unfold TW.OFF_g_s, TW.W_LEN; lia].
Qed.

Lemma srxbs_len_ign : forall Bs, length Bs = Z.to_nat TW.W_LEN -> length (srx_ign Bs) = Z.to_nat TW.W_LEN.
Proof.
intros Bs HL. rewrite srxbs_ign_eq. apply srxbs_len_upd8; [exact HL | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* The two stores of :296-297 keep g_s.state and g_fail_next. *)
Lemma srxbs_w1_state : forall Bx now, length Bx = Z.to_nat TW.W_LEN -> TW.S_state (srx_w1 Bx now) = TW.S_state Bx.
Proof.
intros Bx now HL. rewrite srxbs_w1_eq. unfold TW.S_state, TW.s32_at, TW.A_S_state.
assert (L1 := srxbs_len_upd8 Bx (TW.OFF_g_s + 18152) (TS0.u64 (TW.u_at Bx (TW.OFF_g_s + 18152) 8 + 1)) HL
  ltac:(unfold TW.OFF_g_s; lia) ltac:(unfold TW.OFF_g_s, TW.W_LEN; lia)).
rewrite (srxbs_u_out8 _ _ _ _ _ L1); [| unfold TW.OFF_g_s; lia | unfold TW.OFF_g_s, TW.W_LEN; lia | unfold TW.OFF_g_s; lia |].
2: { left. unfold TW.OFF_g_s. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
rewrite (srxbs_u_out8 _ _ _ _ _ HL); [reflexivity | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_s, TW.W_LEN; lia
  | unfold TW.OFF_g_s; lia |].
left. unfold TW.OFF_g_s. cbn [Z.of_nat Pos.of_succ_nat]. lia.
Qed.

Lemma srxbs_w1_gfn : forall Bx now, length Bx = Z.to_nat TW.W_LEN -> TW.g_fail_next (srx_w1 Bx now) = TW.g_fail_next Bx.
Proof.
intros Bx now HL. rewrite srxbs_w1_eq. unfold TW.g_fail_next.
assert (L1 := srxbs_len_upd8 Bx (TW.OFF_g_s + 18152) (TS0.u64 (TW.u_at Bx (TW.OFF_g_s + 18152) 8 + 1)) HL
  ltac:(unfold TW.OFF_g_s; lia) ltac:(unfold TW.OFF_g_s, TW.W_LEN; lia)).
rewrite (srxbs_u_out8 _ _ _ _ _ L1); [| unfold TW.OFF_g_s; lia | unfold TW.OFF_g_s, TW.W_LEN; lia
  | unfold TW.OFF_g_fail_next; lia | right; unfold TW.OFF_g_s, TW.OFF_g_fail_next; lia].
rewrite (srxbs_u_out8 _ _ _ _ _ HL); [reflexivity | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_s, TW.W_LEN; lia
  | unfold TW.OFF_g_fail_next; lia | right; unfold TW.OFF_g_s, TW.OFF_g_fail_next; lia].
Qed.

Lemma srxbs_ign_gfn : forall Bs, length Bs = Z.to_nat TW.W_LEN -> TW.g_fail_next (srx_ign Bs) = TW.g_fail_next Bs.
Proof.
intros Bs HL. rewrite srxbs_ign_eq. unfold TW.g_fail_next.
rewrite (srxbs_u_out8 _ _ _ _ _ HL); [reflexivity | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_s, TW.W_LEN; lia
  | unfold TW.OFF_g_fail_next; lia | right; unfold TW.OFF_g_s, TW.OFF_g_fail_next; lia].
Qed.

(* The accepted path: the state not CLOSED gives srxb_after at srx_w1 Bx now; CLOSED gives the world Bx and 0. *)
Lemma srxbs_m_open : forall TF Bw b now Bw' r Bx,
  TSS.diginet_session_rx_m timg_B TF Bw b now = Some (Bw', r) -> srxb_pre_acc Bw b Bx ->
  TW.S_state Bx <> TS0.DIGINET_S_CLOSED -> srxb_after timg_B TF (srx_w1 Bx now) b now = Some (Bw', r).
Proof.
intros TF Bw b now Bw' r Bx Hm Hp Hs.
rewrite (srxb_m_acc timg_B TF Bw b now Bx Hp), (srxb_acc_open timg_B TF Bx b now Hs) in Hm. exact Hm.
Qed.

Lemma srxbs_m_closed : forall TF Bw b now Bw' r Bx,
  TSS.diginet_session_rx_m timg_B TF Bw b now = Some (Bw', r) -> srxb_pre_acc Bw b Bx ->
  TW.S_state Bx = TS0.DIGINET_S_CLOSED -> Bw' = Bx /\ r = 0.
Proof.
intros TF Bw b now Bw' r Bx Hm Hp Hs.
rewrite (srxb_m_acc timg_B TF Bw b now Bx Hp), (srxb_acc_closed timg_B TF Bx b now Hs) in Hm.
destruct (srxb_some_inv _ _ _ _ Hm) as [E1 E2]. split; [symmetry; exact E1 | rewrite <- E2; reflexivity].
Qed.

(* diginet_session_tick_m at the world the switch leaves. *)
Lemma srxbs_m_tick : forall I F Bs b now B2 Bw' r, srxb_after I F Bs b now = Some (Bw', r) ->
  srx_sw I F Bs b now = Some (B2, tt) -> TSS.diginet_session_tick_m I F B2 now = Some (Bw', r).
Proof. intros I F Bs b now B2 Bw' r H Hs. unfold srxb_after in H. rewrite Hs in H. exact H. Qed.

Lemma srxbs_cmd_range : forall b, 0 <= DSpec.fr_cmd b < 256.
Proof.
intros b. unfold DSpec.fr_cmd, DSpec.at8, DSpec.bz.
pose proof (bv_unsigned_in_range 8 (nth 28 b (DSpec.b8 0))) as R. unfold bv_modulus in R.
change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

(* The 64 bytes diginet_frame_parse leaves at f (fr_code b = 0): byte 30 is h.cmd. *)
Lemma srxbs_fbytes_cmd : forall buf b fj, DSpec.fr_code b = 0 -> length fj = 64%nat ->
  length (frame_f_bytes buf b fj) = 64%nat /\ nth 30 (frame_f_bytes buf b fj) 0 = DSpec.fr_cmd b.
Proof.
intros buf b fj Hc Hfj.
assert (Hlen : (30 <= length b)%nat).
{ revert Hc. unfold DSpec.fr_code. destruct (length b <? 30)%nat eqn:E; [discriminate|]. intros _.
  apply Nat.ltb_ge in E. exact E. }
assert (L1 : length (DSpec.fr_dst b) = 6%nat) by (unfold DSpec.fr_dst; apply firstn_length_le; lia).
assert (L2 : length (DSpec.fr_src b) = 6%nat) by (unfold DSpec.fr_src; apply firstn_length_le; rewrite length_skipn; lia).
assert (L3 : length (firstn 2 (skipn 14 fj)) = 2%nat) by (apply firstn_length_le; rewrite length_skipn; lia).
assert (L5 : length (skipn 59 fj) = 5%nat) by (rewrite length_skipn; lia).
assert (EC : frame_f_cells buf b fj = PParse.parse_cells buf b fj) by (unfold frame_f_cells; rewrite Hc; reflexivity).
unfold frame_f_bytes. rewrite EC. split.
- rewrite length_map, LC.cells_bytes_length; [reflexivity|].
  unfold PParse.parse_cells. cbn [LC.cells_wf LC.cell_wf].
  repeat split; first [exact L1 | exact L2 | exact L3 | exact L5].
- unfold PParse.parse_cells. cbn [LC.cells_bytes LC.cbytes]. unfold LMem.le2, LMem.le4.
  rewrite !map_app.
  repeat (rewrite app_nth2 by (rewrite length_map;
            first [rewrite L1 | rewrite L2 | rewrite L3 | rewrite LMem.length_Z_to_le_bytes]; lia);
          rewrite length_map; first [rewrite L1 | rewrite L2 | rewrite L3 | rewrite LMem.length_Z_to_le_bytes];
          cbn [Nat.sub]).
  cbn [map app nth]. unfold DSpec.b8, DSpec.fr_cmd, DSpec.at8, DSpec.bz. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Branch conditions                                                   *)
(* ------------------------------------------------------------------ *)

Lemma srxbs_sext : forall E Bx, ew E 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_state Bx).
Proof.
intros E Bx H. pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 112) 4) as R. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma srxbs_state_range : forall Bx, - 2 ^ 31 <= TW.S_state Bx < 2 ^ 31.
Proof. intros Bx. unfold TW.S_state. apply TWL.s32_range. Qed.

(* +0x390, `bne a1, a0` with a1 the sign-extended state and a0 = 3. *)
Lemma srxbs_br_state : forall E Bx, ew E 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4) ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff 32 0))) (sv_denot E (SLit 3)) = negb (TW.S_state Bx =? 3).
Proof.
intros E Bx H. cbn [branch_taken]. rewrite (srxbs_sext E Bx H). cbn [sv_denot]. unfold bv_eqb.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (srxbs_state_range Bx) as R.
rewrite (Z.mod_small 3 (2 ^ 64)) by lia. f_equal.
destruct (Z.eqb_spec (TW.S_state Bx) 3) as [Heq | Hne].
- rewrite Heq. rewrite (Z.mod_small 3 (2 ^ 64)) by lia. apply Z.eqb_refl.
- apply Z.eqb_neq. intros HH. apply Hne.
  destruct (Z_lt_le_dec (TW.S_state Bx) 0) as [Hneg | Hpos].
  + rewrite <- (Z.mod_unique (TW.S_state Bx) (2 ^ 64) (-1) (TW.S_state Bx + 2 ^ 64)) in HH by lia. lia.
  + rewrite (Z.mod_small (TW.S_state Bx) (2 ^ 64)) in HH by lia. exact HH.
Qed.

(* +0x3d8, `bge a3, a2` with a3 = 223 and a2 = h.cmd. *)
Lemma srxbs_br_ge : forall E c, ew E 13 = w64 223 -> ew E 12 = w64 c -> 0 <= c < 256 ->
  branch_taken BC_GE (sv_denot E (SOff 13 0)) (sv_denot E (SOff 12 0)) = negb (223 <? c).
Proof.
intros E c H13 H12 Hc. cbn [branch_taken sv_denot]. rewrite H13, H12. unfold w64.
rewrite (unsigned_lit_small 223), (unsigned_lit_small c) by lia. rewrite !Z.add_0_r.
unfold bv_lts. rewrite !YK00.bv_signed_small by lia. reflexivity.
Qed.

(* `beq a2, zero` and `bne a2, k` with a2 = h.cmd. *)
Lemma srxbs_br_eq : forall E c k, ew E 12 = w64 c -> 0 <= c < 256 -> 0 <= k < 256 ->
  branch_taken BC_EQ (sv_denot E (SOff 12 0)) (sv_denot E (SLit k)) = (c =? k).
Proof.
intros E c k H12 Hc Hk. cbn [branch_taken sv_denot]. rewrite H12. unfold w64, bv_eqb.
rewrite (unsigned_lit_small c) by lia. rewrite Z.add_0_r. rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma srxbs_br_ne : forall E c k, ew E 12 = w64 c -> 0 <= c < 256 -> 0 <= k < 256 ->
  branch_taken BC_NE (sv_denot E (SOff 12 0)) (sv_denot E (SLit k)) = negb (c =? k).
Proof.
intros E c k H12 Hc Hk. cbn [branch_taken sv_denot]. rewrite H12. unfold w64, bv_eqb.
rewrite (unsigned_lit_small c) by lia. rewrite Z.add_0_r. rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

(* +0x3e4, `bgeu a0, a3` with a0 = h.cmd - 224 (h.cmd > 223) and a3 = 2. *)
Lemma srxbs_br_geu : forall E c, ew E 12 = w64 c -> 223 < c < 256 ->
  branch_taken BC_GEU (sv_denot E (SOff 12 (-224))) (sv_denot E (SLit 2)) = negb (c - 224 <? 2).
Proof.
intros E c H12 Hc. cbn [branch_taken sv_denot]. rewrite H12. unfold w64, bv_ltu.
rewrite (unsigned_lit_small c) by lia. rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

(* +0x444, `bltu a0, a1` with a0 = 1 and a1 = the state - 1 (`addiw`): not taken exactly for WAKING (1) and ONLINE
   (2). *)
Lemma srxbs_br_ltu : forall E s, ew E 11 = w64 s -> - 2 ^ 31 <= s < 2 ^ 31 ->
  branch_taken BC_LTU (sv_denot E (SLit 1)) (sv_denot E (SAluw ALU_ADD (SOff 11 0) (SLit (-1))))
  = negb ((s =? 2) || (s =? 1)).
Proof.
intros E s H11 Hs. rewrite branch_ltu_U.
assert (U1 : U E (SLit 1) = 1) by reflexivity.
assert (Ua : U E (SOff 11 0) mod 2 ^ 32 = s mod 2 ^ 32).
{ unfold U. cbn [sv_denot]. rewrite H11. unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Zmod_mod.
  rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | lia | exists (2 ^ 32); reflexivity]. }
assert (Ub : U E (SLit (-1)) mod 2 ^ 32 = 2 ^ 32 - 1) by reflexivity.
rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw]. rewrite Ua, Ub, U1.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
change (bv_modulus 64) with (2 ^ 64).
pose proof (Z.div_mod s (2 ^ 32) ltac:(lia)) as D1. pose proof (Z.mod_pos_bound s (2 ^ 32) ltac:(lia)) as M1.
match goal with |- (1 <? (?y mod 2 ^ 32 - 2 ^ 31) mod 2 ^ 64) = _ =>
  pose proof (Z.div_mod y (2 ^ 32) ltac:(lia)) as D2; pose proof (Z.mod_pos_bound y (2 ^ 32) ltac:(lia)) as M2;
  pose proof (Z.div_mod (y mod 2 ^ 32 - 2 ^ 31) (2 ^ 64) ltac:(lia)) as D3;
  pose proof (Z.mod_pos_bound (y mod 2 ^ 32 - 2 ^ 31) (2 ^ 64) ltac:(lia)) as M3;
  destruct (Z.ltb_spec 1 ((y mod 2 ^ 32 - 2 ^ 31) mod 2 ^ 64)) end;
destruct (Z.eqb_spec s 2); destruct (Z.eqb_spec s 1); cbn [orb negb]; first [reflexivity | exfalso; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* Byte facts                                                          *)
(* ------------------------------------------------------------------ *)

(* A stored value read back byte by byte through the view. *)
Lemma srxbs_val_aview : forall (H : word -> bool) mem a (n : nat) v k,
  val_mem tfibsegs (mrestrict H mem) a n v -> (k < n)%nat ->
  aview tfibsegs H mem (a + Z.of_nat k) = Some (YO0f.le_byte v n k).
Proof.
intros H mem a n v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* A chunk of w bytes of the value e reads, byte k, the k-th little-endian byte of e. *)
Lemma srxbs_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* The stored 8-byte values of run B and run D: an atom plus 1, and an atom. *)
Lemma srxbs_inc8 : forall E (n : nat) y, ew E n = Z_to_bv 64 y -> 0 <= y < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SOff n 1)) mod 2 ^ (8 * Z.of_N 8) = TS0.u64 (y + 1).
Proof.
intros E n y H Hy. cbn [sv_denot]. rewrite H, (unsigned_lit_small y) by lia. rewrite Z_to_bv_unsigned.
unfold bv_wrap, TS0.u64. change (bv_modulus 64) with (2 ^ 64). change (8 * Z.of_N 8) with 64. rewrite Zmod_mod.
reflexivity.
Qed.

Lemma srxbs_atom8 : forall E (n : nat) y, ew E n = Z_to_bv 64 y -> 0 <= y < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SOff n 0)) mod 2 ^ (8 * Z.of_N 8) = y.
Proof.
intros E n y H Hy. cbn [sv_denot]. rewrite H, (unsigned_lit_small y) by lia. rewrite Z.add_0_r.
rewrite (unsigned_lit_small y) by lia. change (8 * Z.of_N 8) with 64. apply Z.mod_small. exact Hy.
Qed.

(* The memory after a run whose start state has no writable byte is the memory before it. *)
Lemma srxbs_mem_eq : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  (forall a, ~ in_wrange E rs a) -> m' = m.
Proof. intros E rs m m' HF Hn. apply functional_extensionality. intros x. apply HF. apply Hn. Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma srxbs_inG : forall a, SRX_S <= a < SRX_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, SRX_S in *; cbn [fst snd]; lia].
Qed.

(* The two stores of :296-297, read through tw_write. *)
Lemma srxbs_tw_w1 : forall (rd rd' : Z -> option Z) Bx now,
  tw_at TMAP_B rd Bx ->
  (forall j, (j < 8)%nat ->
     rd' (SRX_S + 18152 + Z.of_nat j) = Some (YO0f.le_byte (TS0.u64 (TW.u_at Bx (TW.OFF_g_s + 18152) 8 + 1)) 8 j)) ->
  (forall j, (j < 8)%nat -> rd' (SRX_S + 176 + Z.of_nat j) = Some (YO0f.le_byte now 8 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (SRX_S + 18152 <= x < SRX_S + 18160) -> ~ (SRX_S + 176 <= x < SRX_S + 184) ->
     rd' x = rd x) ->
  tw_at TMAP_B rd' (srx_w1 Bx now).
Proof.
intros rd rd' Bx now Hat HF HL HO.
assert (CS : SRX_S = TB_g_s) by reflexivity.
set (rdm := fun x => if ((SRX_S + 176 <=? x) && (x <? SRX_S + 184))%bool then rd x else rd' x).
assert (H1 : tw_at TMAP_B rdm
  (TW.upd Bx (TW.OFF_g_s + 18152) (TW.put 8 (TS0.u64 (TW.u_at Bx (TW.OFF_g_s + 18152) 8 + 1))))).
{ apply (tw_write TMAP_B rd rdm Bx TW.OFF_g_s TB_g_s TW.SZ_g_s 18152 8 _ TMAP_B_ok Hat TMAP_B_g_s);
    [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. unfold rdm. rewrite <- CS.
    assert (Hb : ((SRX_S + 176 <=? SRX_S + 18152 + Z.of_nat j) && (SRX_S + 18152 + Z.of_nat j <? SRX_S + 184))%bool
      = false) by (apply andb_false_iff; right; apply Z.ltb_ge; lia).
    rewrite Hb. exact (HF j Hj).
  - intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
    destruct ((SRX_S + 176 <=? x) && (x <? SRX_S + 184))%bool eqn:Eb; [reflexivity|].
    apply andb_false_iff in Eb.
    apply HO; [exact Hx | lia |].
    destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia. }
rewrite srxbs_w1_eq.
apply (tw_write TMAP_B rdm rd' _ TW.OFF_g_s TB_g_s TW.SZ_g_s 176 8 now TMAP_B_ok H1 TMAP_B_g_s);
  [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. rewrite <- CS. exact (HL j Hj).
- intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
  destruct ((SRX_S + 176 <=? x) && (x <? SRX_S + 184))%bool eqn:Eb; [|reflexivity].
  apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  exfalso. apply Hn. lia.
Qed.

(* The store of :314, read through tw_write. *)
Lemma srxbs_tw_ign : forall (rd rd' : Z -> option Z) Bs,
  tw_at TMAP_B rd Bs ->
  (forall j, (j < 8)%nat ->
     rd' (SRX_S + 18184 + Z.of_nat j) = Some (YO0f.le_byte (TS0.u64 (TW.u_at Bs (TW.OFF_g_s + 18184) 8 + 1)) 8 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (SRX_S + 18184 <= x < SRX_S + 18192) -> rd' x = rd x) ->
  tw_at TMAP_B rd' (srx_ign Bs).
Proof.
intros rd rd' Bs Hat HN HO. rewrite srxbs_ign_eq.
apply (tw_write TMAP_B rd rd' Bs TW.OFF_g_s TB_g_s TW.SZ_g_s 18184 8 _ TMAP_B_ok Hat TMAP_B_g_s);
  [lia | unfold TW.SZ_g_s; lia | exact HN |].
intros x Hx Hn. apply HO; [exact Hx | unfold SRX_S; lia].
Qed.

(* The registers srxb_regs_base names, kept by a run that writes no callee-saved register. *)
Lemma srxbs_regs_pres : forall regs regs2 regs3 now sp1 F,
  srxb_regs_base regs regs2 now sp1 F -> aregs_preserved regs2 regs3 -> srxb_regs_base regs regs3 now sp1 F.
Proof.
intros regs regs2 regs3 now sp1 F ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22) HP.
split; [split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]] | split].
- exact (eq_trans (HP 2 ltac:(hnf; lia)) R2).
- exact (eq_trans (HP 3 ltac:(hnf; lia)) R3).
- exact (eq_trans (HP 4 ltac:(hnf; lia)) R4).
- exact (eq_trans (HP 8 ltac:(hnf; lia)) R8).
- exact (eq_trans (HP 9 ltac:(hnf; lia)) R9).
- exact (eq_trans (HP 18 ltac:(hnf; lia)) R18).
- exact (eq_trans (HP 19 ltac:(hnf; lia)) R19).
- exact (eq_trans (HP 20 ltac:(hnf; lia)) R20).
- exact (eq_trans (HP 25 ltac:(hnf; lia)) R25).
- exact (eq_trans (HP 26 ltac:(hnf; lia)) R26).
- exact (eq_trans (HP 27 ltac:(hnf; lia)) R27).
- exact (eq_trans (HP 21 ltac:(hnf; lia)) R21).
- exact (eq_trans (HP 22 ltac:(hnf; lia)) R22).
Qed.

(* ------------------------------------------------------------------ *)
(* Tactics of the runs                                                 *)
(* ------------------------------------------------------------------ *)

(* After a run: the model the run left generalized. *)
Ltac srxbs_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end.
(* The write rights of a run whose regions have no writable byte. *)
Ltac srxbs_awr_nil :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.
(* No byte lies in a window of regions with no writable byte. *)
Ltac srxbs_nowin :=
  let a := fresh "a" in let r0 := fresh "r0" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r0 & Hin & Hr);
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r0 l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia |]);
  destruct Hin.
(* After a run with no writable byte: the model generalized, and HmE (the run's start memory is the cut's memory)
   moved to the run's last memory. *)
Ltac srxbs_step_mem HmE :=
  srxbs_md;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => clear HFr end;
  lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end;
  lazymatch goal with HF : frame_of _ _ ?m0 ?m1 |- _ =>
    let Hm' := fresh "HmE" in pose proof (eq_trans (srxbs_mem_eq _ _ _ _ HF ltac:(srxbs_nowin)) HmE) as Hm';
    clear HmE HF; rename Hm' into HmE end.
(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac srxbs_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* The pc of the goal's machine state, at a named offset. *)
Ltac srxbs_pc pc :=
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst ?f ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst f rg (Z_to_bv 64 (@pa_val _ transportb_listing PI_transportb A_TEXT + pc))
      mm rom) mdx) Q) end.

Section sw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Local Abbreviation srxbs_cfg pc regs2 mem2 md2 :=
  (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + pc)) mem2 (YK11.seg_rom segs)) md2).

Lemma srxbs_agree : forall regs extra,
  env_agree 32 (Ereg regs extra) (Eimg (PI := PI_transportb) (Ereg regs extra)).
Proof. intros regs extra. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* At a cut reached by a run with no writable byte: the machine state named, the callee-saved registers kept (HP),
   the memory the cut's, the pc named. *)
Ltac srxbs_leaf HS HJ HmE regs2 extra E0 pc HP :=
  srxbs_step_mem HmE; pmkst HS;
  lazymatch type of HS with context [restrict ?Hh ?m] =>
    assert (HP : aregs_preserved regs2 (ms_regs m))
      by (apply (aregs_preserved_of_st_ok tfibsegs Hh E0 _ m regs2 extra HS);
          [apply srxbs_agree | vm_compute; reflexivity]);
    rewrite HmE in HJ |- *
  end;
  srxbs_pc pc.

(* ------------------------------------------------------------------ *)
(* What a store into G keeps                                           *)
(* ------------------------------------------------------------------ *)

(* g_s's payload is addressable at every AR state (the record's zero shadow of g_s). *)
Lemma srxbs_ra : forall ly S (W : world segs) mem md, trans_srx_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF SRX_S TW.SZ_g_s.
Proof.
intros ly S W mem md (HZ & _) HAR x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : SRX_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= SRX_S + TW.SZ_g_s)
  by (unfold SRX_S, TB_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md SRX_S (SRX_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The own frame holds no byte of G. *)
Lemma srxbs_frame_ng : forall ly2 S2 (W2 : world segs) mem2 md2 lyc pos F,
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  In (SRX_CID, pos) (frames S2) -> ly_F ly2 = ly_F lyc -> F = frame_addr lyc SRX_CID pos ->
  forall a, F <= a < F + SRXB_FBYTES -> ~ inG TG.G_HARNESS_B a.
Proof.
intros ly2 S2 W2 mem2 md2 lyc pos F LAWS HG HAR Hin ELF EF a Ha Hg.
assert (EF2 : frame_addr ly2 SRX_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 SRX_CID pos a HAR Hin);
  [rewrite EF2; change (fs_frame_bytes SRX_CID) with 128; unfold SRXB_FBYTES in Ha; lia |].
exact (proj1 (HG a Hg)).
Qed.

Lemma srxbs_fg_apart : forall F, (forall a, F <= a < F + SRXB_FBYTES -> ~ inG TG.G_HARNESS_B a) ->
  F + SRXB_FBYTES <= SRX_S \/ SRX_S + TW.SZ_g_s <= F.
Proof.
intros F HN.
destruct (Z_le_gt_dec (F + SRXB_FBYTES) SRX_S) as [h|h]; [left; exact h|].
destruct (Z_le_gt_dec (SRX_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
exfalso. destruct (Z_le_gt_dec F SRX_S) as [h3|h3].
- apply (HN SRX_S); [lia | apply srxbs_inG; unfold TW.SZ_g_s; lia].
- apply (HN F); [unfold SRXB_FBYTES; lia | apply srxbs_inG; lia].
Qed.

(* acall_kept_g carried across a step that changes bytes of G only. *)
Lemma srxbs_kept_g : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) memX memY slo shi (Eo Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B -> @AR rc segs B lyc Sc W memc mdc ->
  (forall a, Zs a -> inG TG.G_HARNESS_B a) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) memY a = aview segs (w_H W2) memX a) ->
  (forall a, apresent (w_H W2) memX a -> apresent (w_H W2) memY a) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 memY slo shi Eo.
Proof.
intros lyc Sc W memc mdc W2 memX memY slo shi Eo Zs LAWS HG HAR HZ HK Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 memX memY slo shi Eo Zs HAR HK
  Hkp Hgr).
- intros a Ha Hc. exfalso. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HG (HZ a Ha)) as Hl.
  unfold kLowMemEnd in Hl. lia.
- intros b m i Hb Hi Ha. exfalso. destruct (HG _ (HZ _ Ha)) as [Hi' _].
  exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HAR Hb ltac:(lia) Hi').
- intros a Ha _ HnG _ _. exact (HnG (HZ a Ha)).
- intros cid pos a Hin Hr Ha. exfalso. pose proof (HZ a Ha) as Hg. destruct (HG _ Hg) as [Hi _].
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HG Hg) as Hl.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & _ & _).
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
  + exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr Hi).
  + pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
Qed.

(* decode_rd_ok carried across a step that changes bytes of G only: a byte of G stays visible (gx_rw_vis), and no
   shadow byte is a byte of G. *)
Lemma srxbs_rd_ok_g : forall (W : world segs) m m' q n, decode_rd_ok W m q n ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  decode_rd_ok W m' q n.
Proof.
intros W m m' q n (R1 & R2 & R3 & R4 & R5 & R6) K.
assert (KS : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W) m' s = aview segs (w_H W) m s).
{ intros s Hs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). apply K; [lia|]. intros Hg.
  pose proof (inG_G_HARNESS_hull s Hg) as Gh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI, kLowMemEnd in *. lia. }
assert (Hq : q + n <= kHighMemEnd - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
unfold kHighMemEnd in Hq.
split; [|split; [|split; [|exact (conj R4 (conj R5 R6))]]].
- intros a Ha. destruct (classic (inG TG.G_HARNESS_B a)) as [Hg | Hg].
  + exact (gx_rw_vis segs TG.G_HARNESS_B a G_HARNESS_B_rw Hg (w_H W) m').
  + rewrite (K a ltac:(lia) Hg). exact (R1 a Ha).
- intros x Hx. destruct (R2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite KS; [exact Hs|]. unfold shadow_of_addr, kLowMemEnd, kHighShadowEnd, SHADOW_OFF.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
- intros s Hs. rewrite KS; [exact (R3 s Hs)|]. unfold shadow_addr, SHADOW_OFF in Hs.
  unfold kLowMemEnd, kHighShadowEnd.
  pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
  pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + q / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147450880 + q / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.

Lemma srxbs_src_ok_g : forall lyc Sc (W : world segs) m m' q n, trans_src_ok B lyc Sc W m q n ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  trans_src_ok B lyc Sc W m' q n.
Proof.
intros lyc Sc W m m' q n [Hb | (HL & Hrd)] K; [left; exact Hb|].
right. split; [exact HL | exact (srxbs_rd_ok_g W m m' q n Hrd K)].
Qed.

Lemma srxbs_garr8_keep : forall (W : world segs) m m' q (l : list Z), garr8 segs (mrestrict (w_H W) m) q l ->
  (forall a, q <= a < q + Z.of_nat (length l) -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  garr8 segs (mrestrict (w_H W) m') q l.
Proof.
intros W m m' q l H K. apply (garr8_frame segs _ _ q l H). intros a Ha. apply (mbyte_of_aview segs). exact (K a Ha).
Qed.

(* A placed range lies below 2 ^ 47. *)
Lemma srxbs_place : forall ly2 S2 (W2 : world segs) mem2 md2 q n, AR_laws segs B -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  trans_src_ok B ly2 S2 W2 mem2 q n -> 0 < n -> 0 <= q /\ q + n <= 2 ^ 47.
Proof.
intros ly2 S2 W2 mem2 md2 q n LAWS HAR Hs Hn. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (trans_src_ok_place B LAWS ly2 S2 W2 mem2 md2 q n HAR Hs Hn) as [P | P]; lia.
Qed.

(* The reads srxb_rd names, carried across a step that changes bytes of G only (the bytes at buf and TF lie outside
   G, the read-only bytes below it, and a range's placement survives: srxbs_src_ok_g). *)
Lemma srxbs_rd_g : forall ly2 S2 (W2 : world segs) mem2 md2 m' regs buf b TF Bw,
  AR_laws segs B -> @AR rc segs B ly2 S2 W2 mem2 md2 -> srx_buf_off_g buf b -> trans_tf_off_g TF ->
  srxb_rd B ly2 S2 W2 mem2 regs buf b TF Bw ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> aview segs (w_H W2) m' a = aview segs (w_H W2) mem2 a) ->
  srxb_rd B ly2 S2 W2 m' regs buf b TF Bw.
Proof.
intros ly2 S2 W2 mem2 md2 m' regs buf b TF Bw LAWS HAR Hboff Htfg (Hg8 & Hsrc & HTF & Hrom & Hnd) K.
split; [|split; [|split; [|split]]].
- apply (srxbs_garr8_keep W2 mem2 m' buf (TW.zs b) Hg8). intros a Ha. unfold TW.zs in Ha. rewrite length_map in Ha.
  destruct (srxbs_place ly2 S2 W2 mem2 md2 buf (Z.of_nat (length b)) LAWS HAR Hsrc ltac:(lia)) as [P1 P2].
  apply K; [lia | apply Hboff; lia].
- exact (srxbs_src_ok_g ly2 S2 W2 mem2 m' buf _ Hsrc K).
- destruct TF as [fr|]; [|exact I].
  destruct HTF as (Ha0 & Hg & Hs & Hw).
  split; [exact Ha0|]. split; [|split; [exact (srxbs_src_ok_g ly2 S2 W2 mem2 m' _ _ Hs K) | exact Hw]].
  apply (srxbs_garr8_keep W2 mem2 m' _ _ Hg). intros a Ha. rewrite length_map in Ha.
  destruct (srxbs_place ly2 S2 W2 mem2 md2 _ _ LAWS HAR Hs ltac:(lia)) as [P1 P2].
  apply K; [lia | apply (Htfg fr eq_refl); lia].
- intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Rb. rewrite K; [exact (Hrom a Ha) | lia |].
  intros Hg. pose proof (inG_G_HARNESS_hull a Hg) as Gh. unfold TG.G_HARNESS_B_LO in Gh. lia.
- intros H1 H2 H3 H4 H5 H6 H7 H8. destruct (Hnd H1 H2 H3 H4 H5 H6 H7 H8) as [Hs Hw].
  split; [exact (srxbs_src_ok_g ly2 S2 W2 mem2 m' _ _ Hs K) | exact Hw].
Qed.

(* f's 64 bytes, carried across a step that changes bytes of G only. *)
Lemma srxbs_fbytes_g : forall (W2 : world segs) mem2 m' F buf b fj, srxb_fbytes W2 mem2 F buf b fj ->
  DSpec.fr_code b = 0 -> (forall a, F <= a < F + SRXB_FBYTES -> ~ inG TG.G_HARNESS_B a) ->
  0 <= F -> F + SRXB_FBYTES <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> aview segs (w_H W2) m' a = aview segs (w_H W2) mem2 a) ->
  srxb_fbytes W2 m' F buf b fj.
Proof.
intros W2 mem2 m' F buf b fj (Hl & Hg) Hc HN HF0 HFc K. split; [exact Hl|].
apply (srxbs_garr8_keep W2 mem2 m' _ _ Hg). intros a Ha.
rewrite (proj1 (srxbs_fbytes_cmd buf b fj Hc Hl)) in Ha.
apply K; [unfold SRX_F, SRXB_FBYTES in *; lia | apply HN; unfold SRX_F, SRXB_FBYTES in *; lia].
Qed.

(* What every cut carries, at a later memory of the same state whose bytes outside G are those of the cut's memory. *)
Lemma srxbs_cur_g : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F
    ly2 S2 (W2 : world segs) mem2 md2 e m3 md3,
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B ->
  srxb_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
  srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((SRX_CID, pos) :: own) ly2 S2 W2 m3 md3 (k + e) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> aview segs (w_H W2) m3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) m3 a) ->
  srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 m3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 e
  m3 md3 LAWS HG HFIX (HJ & He & Hfr & Hperm & HlyF & Hmo & HK & Hsv & HFL) HJ3 K Gr.
pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _).
pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & EF & HF0 & _ & HFc & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (H104 : 104 <= SRX_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HsG : forall a, spZ regs - 104 <= a < spZ regs -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. pose proof (inG_G_HARNESS_hull a Hg) as Gh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Gh. lia. }
assert (Hin2 : In (SRX_CID, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof (srxbs_frame_ng ly2 S2 W2 mem2 md2 lyc pos F LAWS HG HAR2 Hin2 HlyF EF) as HNF.
unfold SRXB_FBYTES in *.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj Hmo (conj _ (conj _ _)))))))).
- exact (srxbs_kept_g lyc Sc W memc mdc W2 mem2 m3 _ _ _ (inG TG.G_HARNESS_B) LAWS HG HARc (fun a Ha => Ha) HK K Gr).
- assert (HSo : forall o, In o SRXB_SAVED -> 8 <= fst o <= 104).
  { intros o Ho. unfold SRXB_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
  rewrite Forall_forall in Hsv |- *. intros o Ho. rewrite <- (Hsv o Ho).
  pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply K; [lia | apply HsG; lia].
- rewrite <- HFL. unfold SRXB_FBYTES. apply rdword_ext. intros i Hi. apply K; [lia | apply HNF; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The entry states                                                    *)
(* ------------------------------------------------------------------ *)

Definition srxbs_EA (regs : bvmap 5 word) (Bx : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4)]).

Lemma srxbs_entryA : forall ly2 S2 (W2 : world segs) regs2 mem2 md2 Bx,
  trans_srx_cells B -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bx ->
  YK11.getr regs2 20 = w64 SRX_S -> YK11.getr regs2 27 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (srxbs_EA regs2 Bx) ss_srxbsA
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SRXB_CLOSED)) mem2 (YK11.seg_rom segs))) /\
  sh_ok segs SRXBS_Bx SRXBS_SHA (srxbs_EA regs2 Bx) (mrestrict (w_H W2) mem2).
Proof.
intros ly2 S2 W2 regs2 mem2 md2 Bx HSC HAR Htw R20 R27.
set (E := srxbs_EA regs2 Bx).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E, srxbs_EA; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4))
  by (unfold E, srxbs_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (R32 : 0 <= TW.u_at Bx (TW.OFF_g_s + 112) 4 < 2 ^ 32) by exact (TWL.u_at_range Bx _ 4).
assert (U20 : bv_unsigned (ew E 20) = SRX_S)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; unfold SRX_S, TB_g_s; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = TW.u_at Bx (TW.OFF_g_s + 112) 4)
  by (rewrite E32; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_srxbsA.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, SRXBS_RST.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
    split; [unfold SRX_S, TB_g_s; lia|]. split; [unfold SRX_S, TB_g_s; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ SRX_S 112 4 (SOff 32 0) (TW.u_at Bx (TW.OFF_g_s + 112) 4));
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | lia |].
    exact (tw_read_val segs _ TMAP_B Bx TW.OFF_g_s TB_g_s TW.SZ_g_s 112 4 TMAP_B_ok Htw TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents. unfold extent_of_region, SRXBS_RST.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold srxbs_factsA, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U27, U32.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SRX_S, TB_g_s, SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (srxbs_ra ly2 S2 W2 mem2 md2 HSC HAR) as HRA.
  assert (UB : U E SRXBS_Bx = SHADOW_OFF)
    by (unfold U, SRXBS_Bx; cbn [sv_denot]; rewrite U27, Z.add_0_r; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  unfold sh_ok, SRXBS_SHA. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W2) mem2 E SRXBS_Bx 20 SRX_S TW.SZ_g_s SRX_S 112 120 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. unfold SRX_S, TB_g_s; lia.
  + lia.
  + unfold TW.SZ_g_s. lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SRX_S, TB_g_s, SHADOW_OFF in *. lia.
Qed.

Definition srxbs_EB (regs : bvmap 5 word) (Bx b : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 18152) 8); Z_to_bv 64 (DSpec.fr_cmd b)]).

Lemma srxbs_entryB : forall ly2 S2 (W2 : world segs) regs mem md Bx b buf fj F,
  trans_srx_cells B -> @AR rc segs B ly2 S2 W2 mem md ->
  tw_at TMAP_B (aview segs (w_H W2) mem) Bx ->
  srxb_fbytes W2 mem F buf b fj -> DSpec.fr_code b = 0 ->
  (forall a, F <= a < F + SRXB_FBYTES -> ~ inG TG.G_HARNESS_B a) -> 4096 <= F -> F + SRXB_FBYTES <= 2 ^ 47 ->
  YK11.getr regs 20 = w64 SRX_S -> YK11.getr regs 21 = w64 (SRX_S + 18152) -> YK11.getr regs 22 = w64 (F + SRX_F) ->
  YK11.getr regs 27 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (srxbs_EB regs Bx b) ss_srxbsB
    (restrict (w_H W2) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SRXBS_C2)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SRXBS_Bx SRXBS_SHB (srxbs_EB regs Bx b) (mrestrict (w_H W2) mem).
Proof.
intros ly2 S2 W2 regs mem md Bx b buf fj F HSC HAR Htw (Hfl & Hfg) Hc HNF HF0 HFc R20 R21 R22 R27.
set (E := srxbs_EB regs Bx b).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, srxbs_EB; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 18152) 8))
  by (unfold E, srxbs_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (DSpec.fr_cmd b))
  by (unfold E, srxbs_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (R32 : 0 <= TW.u_at Bx (TW.OFF_g_s + 18152) 8 < 2 ^ 64) by exact (TWL.u_at_range Bx _ 8).
pose proof (srxbs_cmd_range b) as R33.
assert (U20 : bv_unsigned (ew E 20) = SRX_S)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; unfold SRX_S, TB_g_s; lia).
assert (U21 : bv_unsigned (ew E 21) = SRX_S + 18152)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold SRX_S, TB_g_s; lia).
assert (U22 : bv_unsigned (ew E 22) = F + SRX_F)
  by (rewrite (EE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; unfold SRX_F, SRXB_FBYTES in *; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = TW.u_at Bx (TW.OFF_g_s + 18152) 8)
  by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = DSpec.fr_cmd b) by (rewrite E33; apply unsigned_lit_small; lia).
destruct (srxbs_fbytes_cmd buf b fj Hc Hfl) as [FL FC].
pose proof (srxbs_fg_apart F HNF) as HFG.
split.
- rewrite restrict_mkst_fx. unfold ss_srxbsB.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [SRXBS_RFR SRXBS_RLAST SRXBS_RCMD YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U21. split; [unfold SRX_S, TB_g_s; lia|]. split; [unfold SRX_S, TB_g_s; lia|]. split.
      -- intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (SRX_S + 18152 + o) G_HARNESS_B_rw).
         apply srxbs_inG. unfold TW.SZ_g_s. lia.
      -- constructor; [|constructor].
         apply (chunk_ok_val segs E _ (SRX_S + 18152) 0 8 (SOff 32 0) (TW.u_at Bx (TW.OFF_g_s + 18152) 8));
           [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | lia |].
         replace (SRX_S + 18152 + 0) with (TB_g_s + 18152) by (unfold SRX_S; lia).
         exact (tw_read_val segs _ TMAP_B Bx TW.OFF_g_s TB_g_s TW.SZ_g_s 18152 8 TMAP_B_ok Htw TMAP_B_g_s
           ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    * rewrite U20. split; [unfold SRX_S, TB_g_s; lia|]. split; [unfold SRX_S, TB_g_s; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (SRX_S + o) G_HARNESS_B_rw).
      apply srxbs_inG. unfold TW.SZ_g_s. lia.
    * rewrite U22. split; [unfold SRX_F; lia|]. split; [unfold SRX_F, SRXB_FBYTES in *; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (F + SRX_F) 30 1 (SOff 33 0) (DSpec.fr_cmd b));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
      destruct (garr8_nthZ segs _ (F + SRX_F) (frame_f_bytes buf b fj) 30 Hfg ltac:(lia)
        ltac:(rewrite FL; cbn; lia)) as [Hv _].
      change (Z.to_nat 30) with 30%nat in Hv. rewrite FC in Hv. exact Hv.
  + apply pairwise_disjoint_of_extents.
    unfold extent_of_region, SRXBS_RFR, SRXBS_RLAST, SRXBS_RCMD.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, U21, U22.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SRX_S, TB_g_s, SRX_F, SRXB_FBYTES, TW.SZ_g_s in *.
    destruct HFG as [HFG | HFG]; repeat split; first [exact I | lia].
  + unfold srxbs_factsB, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U21, U27, U33.
    change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SRX_S, TB_g_s, SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (srxbs_ra ly2 S2 W2 mem md HSC HAR) as HRA.
  assert (UB : U E SRXBS_Bx = SHADOW_OFF)
    by (unfold U, SRXBS_Bx; cbn [sv_denot]; rewrite U27, Z.add_0_r; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  unfold sh_ok, SRXBS_SHB. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range segs (w_H W2) mem E SRXBS_Bx 21 SRX_S TW.SZ_g_s (SRX_S + 18152) 0 8 HRA UB).
    * unfold U. cbn [sv_denot]. rewrite U21, Z.add_0_r. apply unsigned_lit_small. unfold SRX_S, TB_g_s; lia.
    * lia.
    * unfold TW.SZ_g_s. lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SRX_S, TB_g_s, SHADOW_OFF in *. lia.
  + apply (shent_ok_of_range segs (w_H W2) mem E SRXBS_Bx 20 SRX_S TW.SZ_g_s SRX_S 176 184 HRA UB).
    * unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. unfold SRX_S, TB_g_s; lia.
    * lia.
    * unfold TW.SZ_g_s. lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SRX_S, TB_g_s, SHADOW_OFF in *. lia.
Qed.

Lemma srxbs_entryC : forall (W2 : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) ss_srxbsC
    (restrict (w_H W2) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SRXBS_C3)) mem (YK11.seg_rom segs))).
Proof.
intros W2 regs mem. rewrite restrict_mkst_fx. unfold ss_srxbsC.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

Definition srxbs_ED (regs : bvmap 5 word) (Bs : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at Bs (TW.OFF_g_s + 18184) 8)]).

Lemma srxbs_entryD : forall ly2 S2 (W2 : world segs) regs mem md Bs,
  trans_srx_cells B -> @AR rc segs B ly2 S2 W2 mem md ->
  tw_at TMAP_B (aview segs (w_H W2) mem) Bs ->
  YK11.getr regs 21 = w64 (SRX_S + 18152) -> YK11.getr regs 27 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (srxbs_ED regs Bs) ss_srxbsD
    (restrict (w_H W2) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SRXBS_C4)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SRXBS_Bx SRXBS_SHD (srxbs_ED regs Bs) (mrestrict (w_H W2) mem).
Proof.
intros ly2 S2 W2 regs mem md Bs HSC HAR Htw R21 R27.
set (E := srxbs_ED regs Bs).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, srxbs_ED; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at Bs (TW.OFF_g_s + 18184) 8))
  by (unfold E, srxbs_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (R32 : 0 <= TW.u_at Bs (TW.OFF_g_s + 18184) 8 < 2 ^ 64) by exact (TWL.u_at_range Bs _ 8).
assert (U21 : bv_unsigned (ew E 21) = SRX_S + 18152)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold SRX_S, TB_g_s; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = TW.u_at Bs (TW.OFF_g_s + 18184) 8)
  by (rewrite E32; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_srxbsD.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, SRXBS_RIGN.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U21.
    split; [unfold SRX_S, TB_g_s; lia|]. split; [unfold SRX_S, TB_g_s; lia|]. split.
    * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (SRX_S + 18152 + o) G_HARNESS_B_rw).
      apply srxbs_inG. unfold TW.SZ_g_s. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val segs E _ (SRX_S + 18152) 32 8 (SOff 32 0) (TW.u_at Bs (TW.OFF_g_s + 18184) 8));
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | lia |].
      replace (SRX_S + 18152 + 32) with (TB_g_s + 18184) by (unfold SRX_S; lia).
      exact (tw_read_val segs _ TMAP_B Bs TW.OFF_g_s TB_g_s TW.SZ_g_s 18184 8 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents. unfold extent_of_region, SRXBS_RIGN.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold srxbs_factsD, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U21, U27.
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SRX_S, TB_g_s, SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (srxbs_ra ly2 S2 W2 mem md HSC HAR) as HRA.
  assert (UB : U E SRXBS_Bx = SHADOW_OFF)
    by (unfold U, SRXBS_Bx; cbn [sv_denot]; rewrite U27, Z.add_0_r; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  unfold sh_ok, SRXBS_SHD. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W2) mem E SRXBS_Bx 21 SRX_S TW.SZ_g_s (SRX_S + 18152) 32 40 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U21, Z.add_0_r. apply unsigned_lit_small. unfold SRX_S, TB_g_s; lia.
  + lia.
  + unfold TW.SZ_g_s. lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SRX_S, TB_g_s, SHADOW_OFF in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The ignored arm, +0x4a0 .. +0x4bc, to the tick cut                  *)
(* ------------------------------------------------------------------ *)

(* The state at +0x4a0: the counters of :296-297 stored (the memory relates to srx_w1 Bx now), and the switch's
   ignored arm chosen. *)
Definition srxbs_ign_at : Prop :=
  srxb_laws B MT -> srxb_calls B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b : list byte)
         (TF : option TI.tframe) (Bw Bw' Bx : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srxb_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srxb_rd B ly2 S2 W2 mem2 regs buf b TF Bw ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) (srx_w1 Bx now) -> TW.g_fail_next (srx_w1 Bx now) <= 1 ->
    length Bx = Z.to_nat TW.W_LEN -> srxb_inv (srx_w1 Bx now) ->
    srxb_after timg_B TF (srx_w1 Bx now) b now = Some (Bw', r) ->
    srx_sw timg_B TF (srx_w1 Bx now) b now = Some (srx_ign (srx_w1 Bx now), tt) ->
    srxb_regs_base regs regs2 now sp1 F ->
    SRr segs W2 (srxbs_cfg SRXBS_C4 regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

Lemma srxbs_ign : @srxb_tick_at fx rc B MT -> srxbs_ign_at.
Proof.
intros TICK. unfold srxbs_ign_at.
intros HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' Bx pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HRD HTW HGF HLB HINV Haft Hsw HREGS.
pose proof HLAWS as (HPCS & HCELLS & HSC & HGU & HGNE0 & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hboff & _ & _ & _ & _ & Htfg & _).
pose proof HCUR as (HJ & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22).
set (Bs := srx_w1 Bx now) in *.
assert (HLs : length Bs = Z.to_nat TW.W_LEN) by exact (srxbs_len_w1 Bx now HLB).
destruct (srxbs_entryD ly2 S2 W2 regs2 mem2 md2 Bs HSC HAR2 HTW R21 R27) as [HS SHOK].
set (E0 := srxbs_ED regs2 Bs) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, srxbs_ED; apply Eimg_env).
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E0 n = YK11.getr regs2 r0)
  by (intros n r0 Hn; unfold E0, srxbs_ED; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E0 32 = Z_to_bv 64 (TW.u_at Bs (TW.OFF_g_s + 18184) 8))
  by (unfold E0, srxbs_ED; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (U21 : bv_unsigned (ew E0 21) = SRX_S + 18152)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold SRX_S, TB_g_s; lia).
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
(* run D, +0x4a0 .. +0x4bc: the checked increment of stats.rx_ignored *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SRXB_TICK.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U21 in Ha.
  apply srxbs_inG. unfold TW.SZ_g_s. lia. }
srxbs_md.
lazymatch type of HS with context [restrict _ ?m] => rename m into msD end.
(* run D wrote stats.rx_ignored only *)
assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (SRX_S + 18184 <= a < SRX_S + 18192) ->
  aview segs (w_H W2) (ms_mem msD) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => SRX_S + 18184 <= x < SRX_S + 18192) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U21 in Hx; lia |]).
  destruct Hin. }
assert (GD : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msD) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KG : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a ->
  aview segs (w_H W2) (ms_mem msD) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hng. apply KD; [exact Ha|]. intros X. apply Hng. apply srxbs_inG. unfold TW.SZ_g_s. lia. }
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (srxbs_chunk_val E0 (w_H W2) (ms_mem msD) _ _ _ _ _ _ 32 8 (SOff 32 1) RG0
  ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VI.
cbn [base_val] in VI. rewrite U21 in VI.
rewrite (srxbs_inc8 E0 32 _ E32 (TWL.u_at_range Bs _ 8)) in VI. change (N.to_nat 8) with 8%nat in VI.
(* the world relation at srx_ign Bs *)
assert (TWD : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msD)) (srx_ign Bs)).
{ apply (srxbs_tw_ign (aview segs (w_H W2) mem2) _ Bs HTW).
  - intros j Hj. replace (SRX_S + 18184 + Z.of_nat j) with (SRX_S + 18152 + 32 + Z.of_nat j) by lia.
    exact (srxbs_val_aview _ _ _ _ _ j VI Hj).
  - intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KD; [lia | exact Hn]. }
assert (HP : aregs_preserved regs2 (ms_regs msD))
  by (apply (aregs_preserved_of_st_ok tfibsegs (w_H W2) E0 _ msD regs2 [Z_to_bv 64 (TW.u_at Bs (TW.OFF_g_s + 18184) 8)]
        HS); [apply srxbs_agree | vm_compute; reflexivity]).
pose proof (srxbs_rd_g ly2 S2 W2 mem2 md2 (ms_mem msD) regs buf b TF Bw LAWS HAR2 Hboff Htfg HRD KG) as HRD'.
pmkst HS. srxbs_pc SRXB_TICK.
apply (TICK HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' Bs (srx_ign Bs)
  pos sp1 F ly2 S2 W2 (ms_mem msD) _ e (ms_regs msD) HFIX).
- exact (srxbs_cur_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ly2 S2 W2
    mem2 md2 e (ms_mem msD) _ LAWS HGX HFIX HCUR HJ KG GD).
- exact (proj1 (proj2 (proj2 HRD'))).
- exact (proj1 (proj2 (proj2 (proj2 HRD')))).
- exact TWD.
- rewrite (srxbs_ign_gfn Bs HLs). exact HGF.
- exact HLs.
- exact HINV.
- exact Hsw.
- exact (srxbs_m_tick _ _ _ _ _ _ _ _ Haft Hsw).
- exact (srxbs_regs_pres _ _ _ _ _ _ HREGS HP).
Qed.

(* ------------------------------------------------------------------ *)
(* The switch, +0x3d8 .. +0x444                                        *)
(* ------------------------------------------------------------------ *)

(* The state at +0x3d8: the counters of :296-297 stored (the memory relates to srx_w1 Bx now), the model's result
   srxb_after at that world, a1 = the state, a2 = h.cmd, a3 = 223. *)
Definition srxbs_open_at : Prop :=
  srxb_laws B MT -> srxb_calls B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf now r : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' Bx : list byte) (pos sp1 F : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    srxb_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
    srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
    srxb_rd B ly2 S2 W2 mem2 regs buf b TF Bw ->
    decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE -> srxb_fbytes W2 mem2 F buf b fj ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) (srx_w1 Bx now) -> TW.g_fail_next (srx_w1 Bx now) <= 1 ->
    length Bx = Z.to_nat TW.W_LEN -> srxb_inv (srx_w1 Bx now) ->
    srxb_pre_acc Bw b Bx -> TW.S_state Bx <> TS0.DIGINET_S_CLOSED ->
    srxb_after timg_B TF (srx_w1 Bx now) b now = Some (Bw', r) ->
    srxb_regs_base regs regs2 now sp1 F ->
    YK11.getr regs2 11 = w64 (TW.S_state Bx) -> YK11.getr regs2 12 = w64 (DSpec.fr_cmd b) ->
    YK11.getr regs2 13 = w64 223 ->
    SRr segs W2 (srxbs_cfg SRXBS_C3 regs2 mem2 md2)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).

Lemma srxbs_tail : @srxb_ann_at fx rc B MT -> @srxb_ack_at fx rc B MT -> @srxb_data_at fx rc B MT ->
  @srxb_lost_at fx rc B MT -> @srxb_tick_at fx rc B MT -> srxbs_ign_at -> srxbs_open_at.
Proof.
intros ANN ACK DATA LOST TICK IGN. unfold srxbs_open_at.
intros HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bx pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HRD HFRD HFB HTW HGF HLB HINV HPRE HSNC Haft HREGS H11 H12 H13.
pose proof HLAWS as (HPCS & HCELLS & HSC & HGU & HGNE0 & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HCUR as (HJ & _).
pose proof (srxbs_cmd_range b) as Rc.
pose proof (srxbs_state_range Bx) as Rs.
pose proof (srxbs_entryC W2 regs2 mem2) as HS.
set (E0 := Eimg (PI := PI_transportb) (Ereg regs2 [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E0 n = YK11.getr regs2 r0)
  by (intros n r0 Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (eq_trans (EE 11%nat 11%bv eq_refl) H11) as E11.
pose proof (eq_trans (EE 12%nat 12%bv eq_refl) H12) as E12.
pose proof (eq_trans (EE 13%nat 13%bv eq_refl) H13) as E13.
clear EE.
assert (SHOK : sh_ok segs SRXBS_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
assert (HmE : mem2 = mem2) by reflexivity.
(* +0x3d8: `bge a3, a2` *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* h.cmd <= 223 *)
  rewrite (srxbs_br_ge E0 _ E13 E12 Rc) in Hc. apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hle.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan. { srxbs_awr_nil. }
  srxbs_step_mem HmE.
  (* +0x3fc: `beq a2, zero` *)
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* DATA: the arm cut +0x48c *)
    rewrite (srxbs_br_eq E0 _ 0 E12 Rc ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. rename Hc into Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SRXB_DATA. { srxbs_awr_nil. }
    srxbs_leaf HS HJ HmE regs2 (@nil word) E0 SRXB_DATA HP.
    apply (DATA HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bx pos
      sp1 F ly2 S2 W2 mem2 _ e _ HFIX
      (srxbs_cur_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ly2 S2 W2
        mem2 md2 e mem2 _ LAWS HGX HFIX HCUR HJ (fun a _ _ => eq_refl) (fun a Ha => Ha))
      HRD HFRD HFB HTW HGF HINV HPRE HSNC Haft).
    * exact Hc0.
    * exact (srxbs_regs_pres _ _ _ _ _ _ HREGS HP).
  + rewrite (srxbs_br_eq E0 _ 0 E12 Rc ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hn0.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan. { srxbs_awr_nil. }
    srxbs_step_mem HmE.
    (* +0x404: `bne a2, 0xa0` *)
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* not ACK: the ignored arm +0x4a0 *)
      rewrite (srxbs_br_ne E0 _ 160 E12 Rc ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hn160.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SRXBS_C4. { srxbs_awr_nil. }
      srxbs_leaf HS HJ HmE regs2 (@nil word) E0 SRXBS_C4 HP.
      apply (IGN HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' Bx pos
        sp1 F ly2 S2 W2 mem2 _ e _ HFIX
        (srxbs_cur_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ly2 S2 W2
          mem2 md2 e mem2 _ LAWS HGX HFIX HCUR HJ (fun a _ _ => eq_refl) (fun a Ha => Ha))
        HRD HTW HGF HLB HINV Haft).
      -- apply srxb_sw_other;
           unfold TS0.DIGINET_CMD_ANNOUNCE, TS0.DIGINET_CMD_ANNOUNCE_SESSION, TS0.DIGINET_CMD_ACK,
             TS0.DIGINET_CMD_DATA, TS0.DIGINET_CMD_DISCONNECT;
           first [apply orb_false_iff; split; apply Z.eqb_neq; lia | apply Z.eqb_neq; lia].
      -- exact (srxbs_regs_pres _ _ _ _ _ _ HREGS HP).
    * (* ACK: the arm cut +0x408 *)
      rewrite (srxbs_br_ne E0 _ 160 E12 Rc ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into H160.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SRXB_ACK. { srxbs_awr_nil. }
      srxbs_leaf HS HJ HmE regs2 (@nil word) E0 SRXB_ACK HP.
      apply (ACK HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bx pos
        sp1 F ly2 S2 W2 mem2 _ e _ HFIX
        (srxbs_cur_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ly2 S2 W2
          mem2 md2 e mem2 _ LAWS HGX HFIX HCUR HJ (fun a _ _ => eq_refl) (fun a Ha => Ha))
        HRD HFRD HFB HTW HGF HINV HPRE HSNC Haft).
      -- exact H160.
      -- exact (srxbs_regs_pres _ _ _ _ _ _ HREGS HP).
- (* h.cmd > 223 *)
  rewrite (srxbs_br_ge E0 _ E13 E12 Rc) in Hc. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hgt.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan. { srxbs_awr_nil. }
  srxbs_step_mem HmE.
  (* +0x3e4: `bgeu a0, a3` with a0 = h.cmd - 0xe0 *)
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + rewrite (srxbs_br_geu E0 _ E12 ltac:(lia)) in Hc. apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hge2.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan. { srxbs_awr_nil. }
    srxbs_step_mem HmE.
    (* +0x438: `bne a2, 0xe3` *)
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* not DISCONNECT: the ignored arm +0x4a0 *)
      rewrite (srxbs_br_ne E0 _ 227 E12 Rc ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hn227.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SRXBS_C4. { srxbs_awr_nil. }
      srxbs_leaf HS HJ HmE regs2 (@nil word) E0 SRXBS_C4 HP.
      apply (IGN HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' Bx pos
        sp1 F ly2 S2 W2 mem2 _ e _ HFIX
        (srxbs_cur_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ly2 S2 W2
          mem2 md2 e mem2 _ LAWS HGX HFIX HCUR HJ (fun a _ _ => eq_refl) (fun a Ha => Ha))
        HRD HTW HGF HLB HINV Haft).
      -- apply srxb_sw_other;
           unfold TS0.DIGINET_CMD_ANNOUNCE, TS0.DIGINET_CMD_ANNOUNCE_SESSION, TS0.DIGINET_CMD_ACK,
             TS0.DIGINET_CMD_DATA, TS0.DIGINET_CMD_DISCONNECT;
           first [apply orb_false_iff; split; apply Z.eqb_neq; lia | apply Z.eqb_neq; lia].
      -- exact (srxbs_regs_pres _ _ _ _ _ _ HREGS HP).
    * (* DISCONNECT *)
      rewrite (srxbs_br_ne E0 _ 227 E12 Rc ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into H227.
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan. { srxbs_awr_nil. }
      srxbs_step_mem HmE.
      (* +0x444: `bltu a0, a1` with a1 = the state - 1 *)
      psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
      -- (* neither WAKING nor ONLINE: the tick cut +0x4c0, the world srx_w1 Bx now *)
         rewrite (srxbs_br_ltu E0 _ E11 Rs) in Hc. apply negb_true_iff in Hc. rename Hc into Hnw.
         paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SRXB_TICK. { srxbs_awr_nil. }
         srxbs_leaf HS HJ HmE regs2 (@nil word) E0 SRXB_TICK HP.
         assert (Hsw : srx_sw timg_B TF (srx_w1 Bx now) b now = Some (srx_w1 Bx now, tt)).
         { apply srxb_sw_stay; [exact H227 | rewrite (srxbs_w1_state Bx now HLB); exact Hnw]. }
         apply (TICK HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw'
           (srx_w1 Bx now) (srx_w1 Bx now) pos sp1 F ly2 S2 W2 mem2 _ e _ HFIX
           (srxbs_cur_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ly2 S2
             W2 mem2 md2 e mem2 _ LAWS HGX HFIX HCUR HJ (fun a _ _ => eq_refl) (fun a Ha => Ha))).
         ++ exact (proj1 (proj2 (proj2 HRD))).
         ++ exact (proj1 (proj2 (proj2 (proj2 HRD)))).
         ++ exact HTW.
         ++ exact HGF.
         ++ exact (srxbs_len_w1 Bx now HLB).
         ++ exact HINV.
         ++ exact Hsw.
         ++ exact (srxbs_m_tick _ _ _ _ _ _ _ _ Haft Hsw).
         ++ exact (srxbs_regs_pres _ _ _ _ _ _ HREGS HP).
      -- (* WAKING or ONLINE: the arm cut +0x448 (session_lost) *)
         rewrite (srxbs_br_ltu E0 _ E11 Rs) in Hc. apply negb_false_iff in Hc. rename Hc into Hw.
         paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SRXB_LOST. { srxbs_awr_nil. }
         srxbs_leaf HS HJ HmE regs2 (@nil word) E0 SRXB_LOST HP.
         apply (LOST HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bx
           pos sp1 F ly2 S2 W2 mem2 _ e _ HFIX
           (srxbs_cur_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ly2 S2
             W2 mem2 md2 e mem2 _ LAWS HGX HFIX HCUR HJ (fun a _ _ => eq_refl) (fun a Ha => Ha))
           HRD HFRD HFB HTW HGF HINV HPRE HSNC Haft).
         ++ split; [exact H227 | rewrite (srxbs_w1_state Bx now HLB); exact Hw].
         ++ exact (srxbs_regs_pres _ _ _ _ _ _ HREGS HP).
  + (* ANNOUNCE or ANNOUNCE_SESSION: the arm cut +0x3e8 *)
    rewrite (srxbs_br_geu E0 _ E12 ltac:(lia)) in Hc. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hlt2.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SRXB_ANN. { srxbs_awr_nil. }
    srxbs_leaf HS HJ HmE regs2 (@nil word) E0 SRXB_ANN HP.
    apply (ANN HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bx pos
      sp1 F ly2 S2 W2 mem2 _ e _ HFIX
      (srxbs_cur_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ly2 S2 W2
        mem2 md2 e mem2 _ LAWS HGX HFIX HCUR HJ (fun a _ _ => eq_refl) (fun a Ha => Ha))
      HRD HFRD HFB HTW HGF HINV HPRE HSNC Haft).
    * cbv beta. unfold TS0.DIGINET_CMD_ANNOUNCE, TS0.DIGINET_CMD_ANNOUNCE_SESSION.
      destruct (Z.eqb_spec (DSpec.fr_cmd b) 0xe0); [reflexivity|].
      destruct (Z.eqb_spec (DSpec.fr_cmd b) 0xe1); [reflexivity|]. exfalso. lia.
    * exact (srxbs_regs_pres _ _ _ _ _ _ HREGS HP).
Qed.

(* ------------------------------------------------------------------ *)
(* From the closed cut                                                 *)
(* ------------------------------------------------------------------ *)

Lemma srxbs_main : srxb_inv_stmt -> @srxb_rel_at fx rc B MT -> srxbs_open_at -> @srxb_closed_at fx rc B MT.
Proof.
intros INV REL OPEN. unfold srxb_closed_at.
intros HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bx pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HRD HFRD HFB HTW HGF HINV HPRE HREGS.
pose proof HLAWS as (HPCS & HCELLS & HSC & HGU & HGNE0 & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnow & _ & _ & _ & _ & Hboff & _ & _ & Hm & _ & Htfg & _).
pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & EF & HF0 & _ & HFc & _).
pose proof HCUR as (HJ & He & Hfr & Hperm & HlyF & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (Hin2 : In (SRX_CID, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof (srxbs_frame_ng ly2 S2 W2 mem2 md2 lyc pos F LAWS HGX HAR2 Hin2 HlyF EF) as HNF.
assert (HFc' : F + SRXB_FBYTES <= 2 ^ 47) by (pose proof asan_consts as (C1 & _); lia).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22).
pose proof (tw_len _ _ _ HTW) as HLB.
pose proof HPRE as (Hcode & _).
(* run A, +0x374 .. +0x390: the checked load of g_s.state *)
destruct (srxbs_entryA ly2 S2 W2 regs2 mem2 md2 Bx HSC HAR2 HTW R20 R27) as [HS SHOK].
set (E0 := srxbs_EA regs2 Bx) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, srxbs_EA; apply Eimg_env).
assert (E32 : ew E0 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4))
  by (unfold E0, srxbs_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
assert (HmE : mem2 = mem2) by reflexivity.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ srxbs_awr_nil. }
srxbs_step_mem HmE.
(* +0x390: `bne a1, a0` with a0 = 3 *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* the state is not S_CLOSED: on to +0x39c *)
  rewrite (srxbs_br_state E0 Bx E32) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hst : TW.S_state Bx <> TS0.DIGINET_S_CLOSED) by exact Hc. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SRXBS_C2.
  { srxbs_awr_nil. }
  srxbs_step_mem HmE.
  lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
  assert (HP : aregs_preserved regs2 (ms_regs msA))
    by (apply (aregs_preserved_of_st_ok tfibsegs (w_H W2) E0 _ msA regs2
          [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4)] HS); [apply srxbs_agree | vm_compute; reflexivity]).
  srxbs_reg HS (Z_to_bv 5 11) (w64 (TW.S_state Bx)) Q11 ltac:(exact (srxbs_sext E0 Bx E32)).
  pose proof (srxbs_regs_pres _ _ _ _ _ _ HREGS HP) as HREGSA.
  pose proof HREGSA as ((T2 & T3 & T4 & T8 & T9 & T18 & T19 & T20 & T25 & T26 & T27) & T21 & T22).
  pmkst HS. rewrite HmE in HJ |- *. srxbs_pc SRXBS_C2.
  set (regsA := ms_regs msA) in *. clear HS SHOK HmE. clearbody regsA. clear msA.
  (* run B, +0x39c .. +0x3d8: the counters of :296-297, h.cmd *)
  destruct (srxbs_entryB ly2 S2 W2 regsA mem2 md2 Bx b buf fj F HSC HAR2 HTW HFB Hcode HNF HF0 HFc' T20 T21 T22 T27)
    as [HS SHOK].
  set (E1 := srxbs_EB regsA Bx b) in HS, SHOK.
  assert (HEIB : img_env VAL A_LIM E1) by (unfold E1, srxbs_EB; apply Eimg_env).
  assert (EE1 : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E1 n = YK11.getr regsA r0)
    by (intros n r0 Hn; unfold E1, srxbs_EB; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (E1_32 : ew E1 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 18152) 8))
    by (unfold E1, srxbs_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 0)).
  assert (E1_33 : ew E1 33 = Z_to_bv 64 (DSpec.fr_cmd b))
    by (unfold E1, srxbs_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 1)).
  pose proof (eq_trans (EE1 19%nat 19%bv eq_refl) T19) as E1_19.
  assert (U20 : bv_unsigned (ew E1 20) = SRX_S)
    by (rewrite (EE1 20%nat 20%bv eq_refl), T20; apply unsigned_lit_small; unfold SRX_S, TB_g_s; lia).
  assert (U21 : bv_unsigned (ew E1 21) = SRX_S + 18152)
    by (rewrite (EE1 21%nat 21%bv eq_refl), T21; apply unsigned_lit_small; unfold SRX_S, TB_g_s; lia).
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_cons_g;
      [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U21 in Ha;
       apply srxbs_inG; unfold TW.SZ_g_s; lia |].
    apply awr_ok_x_cons_g;
      [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20 in Ha;
       apply srxbs_inG; unfold TW.SZ_g_s; lia |].
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_nil. }
  srxbs_md.
  lazymatch type of HS with context [restrict _ ?m] => rename m into msB end.
  (* run B wrote stats.rx_frames and last_rx_us only *)
  assert (KB : forall a, 0 <= a < 2 ^ 64 ->
    ~ (SRX_S + 18152 <= a < SRX_S + 18160 \/ SRX_S + 176 <= a < SRX_S + 184) ->
    aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn.
    apply (kept_of_frame _ _ _ _ _ (fun x => SRX_S + 18152 <= x < SRX_S + 18160 \/ SRX_S + 176 <= x < SRX_S + 184)
      HFr); [| exact Ha | exact Hn].
    intros b0 wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U20, ?U21 in Hx;
       first [left; lia | right; lia | exfalso; lia] |]).
    destruct Hin. }
  assert (GB : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  assert (KG : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a ->
    aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hng. apply KB; [exact Ha|]. intros [X | X]; apply Hng; apply srxbs_inG; unfold TW.SZ_g_s; lia. }
  (* the two stored values *)
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1.
  cbn [ms_mem restrict] in RG0, RG1.
  pose proof (srxbs_chunk_val E1 (w_H W2) (ms_mem msB) _ _ _ _ _ _ 0 8 (SOff 32 1) RG0
    ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VF.
  pose proof (srxbs_chunk_val E1 (w_H W2) (ms_mem msB) _ _ _ _ _ _ 176 8 (SOff 19 0) RG1
    ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VL.
  cbn [base_val] in VF, VL. rewrite U21 in VF. rewrite U20 in VL.
  rewrite (srxbs_inc8 E1 32 _ E1_32 (TWL.u_at_range Bx _ 8)) in VF.
  rewrite (srxbs_atom8 E1 19 now E1_19 Hnow) in VL.
  change (N.to_nat 8) with 8%nat in VF, VL.
  (* the world relation at srx_w1 Bx now *)
  assert (TWB : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msB)) (srx_w1 Bx now)).
  { apply (srxbs_tw_w1 (aview segs (w_H W2) mem2) _ Bx now HTW).
    - intros j Hj. replace (SRX_S + 18152 + Z.of_nat j) with (SRX_S + 18152 + 0 + Z.of_nat j) by lia.
      exact (srxbs_val_aview _ _ _ _ _ j VF Hj).
    - intros j Hj. exact (srxbs_val_aview _ _ _ _ _ j VL Hj).
    - intros x Hx H1 H2. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply KB; [lia | intros [X | X]; [exact (H1 X) | exact (H2 X)]]. }
  (* the registers at +0x3d8 *)
  assert (HPB : aregs_preserved regsA (ms_regs msB))
    by (apply (aregs_preserved_of_st_ok tfibsegs (w_H W2) E1 _ msB regsA
          [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 18152) 8); Z_to_bv 64 (DSpec.fr_cmd b)] HS);
        [apply srxbs_agree | vm_compute; reflexivity]).
  pose proof (srxbs_cmd_range b) as Rc.
  srxbs_reg HS (Z_to_bv 5 11) (w64 (TW.S_state Bx)) Q11'
    ltac:(cbn [sv_denot]; rewrite (EE1 11%nat (Z_to_bv 5 11) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q11).
  srxbs_reg HS (Z_to_bv 5 12) (w64 (DSpec.fr_cmd b)) Q12
    ltac:(cbn [sv_denot]; rewrite E1_33, (unsigned_lit_small (DSpec.fr_cmd b)) by lia; rewrite Z.add_0_r; reflexivity).
  srxbs_reg HS (Z_to_bv 5 13) (w64 223) Q13 ltac:(reflexivity).
  pmkst HS. srxbs_pc SRXBS_C3.
  apply (OPEN HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bx pos
    sp1 F ly2 S2 W2 (ms_mem msB) _ e (ms_regs msB) HFIX).
  + exact (srxbs_cur_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ly2 S2
      W2 mem2 md2 e (ms_mem msB) _ LAWS HGX HFIX HCUR HJ KG GB).
  + exact (srxbs_rd_g ly2 S2 W2 mem2 md2 (ms_mem msB) regs buf b TF Bw LAWS HAR2 Hboff Htfg HRD KG).
  + exact (srxbs_rd_ok_g W2 mem2 (ms_mem msB) _ _ HFRD KG).
  + exact (srxbs_fbytes_g W2 mem2 (ms_mem msB) F buf b fj HFB Hcode HNF ltac:(lia) HFc' KG).
  + exact TWB.
  + rewrite (srxbs_w1_gfn Bx now HLB). exact HGF.
  + exact HLB.
  + exact (proj1 (proj2 INV) Bx now HLB HINV).
  + exact HPRE.
  + exact Hst.
  + exact (srxbs_m_open TF Bw b now Bw' r Bx Hm HPRE Hst).
  + exact (srxbs_regs_pres _ _ _ _ _ _ HREGSA HPB).
  + exact Q11'.
  + exact Q12.
  + exact Q13.
- (* S_CLOSED: +0x394 .. +0x398, to the release cut with a0 = 0 *)
  rewrite (srxbs_br_state E0 Bx E32) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  destruct (srxbs_m_closed TF Bw b now Bw' r Bx Hm HPRE Hc) as [EB Er]. subst Bw' r. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SRXB_REL.
  { srxbs_awr_nil. }
  srxbs_leaf HS HJ HmE regs2 [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4)] E0 SRXB_REL HP.
  srxbs_reg HS (Z_to_bv 5 10) (w64 0) Q10 ltac:(reflexivity).
  apply (REL HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now 0 b TF Bw Bx pos sp1 F
    ly2 S2 W2 mem2 _ e _ HFIX).
  + exact (srxbs_cur_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now 0 b TF Bw Bx pos sp1 F ly2 S2 W2
      mem2 md2 e mem2 _ LAWS HGX HFIX HCUR HJ (fun a _ _ => eq_refl) (fun a Ha => Ha)).
  + exact HTW.
  + exact HGF.
  + exact (conj (srxbs_regs_pres _ _ _ _ _ _ HREGS HP) Q10).
Qed.

End sw.

(* The switch piece of the image-B walk of diginet_session_rx (SrxBCut.v srxb_sw_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem srxb_sw_ok : forall fx rc B MT, @srxb_sw_stmt fx rc B MT.
Proof.
intros fx rc B MT INV REL ANN ACK DATA LOST TICK.
exact (@srxbs_main fx rc B MT INV REL (@srxbs_tail fx rc B MT ANN ACK DATA LOST TICK (@srxbs_ign fx rc B MT TICK))).
Qed.
