(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module paths and module names changed; 496 of its 563 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SrxBDeskKit.v, with its module paths and module names changed; 1169 of its 1273 lines of code are new or changed and 459 lines of the source are left out. *)
(* receive (image B, ASan build), the by-poll piece: the poll cut (+0x0b8, receive_seg_cut.v recv_poll_at) from the
   call of spec_read_frame (recv_srf_at), the invariants piece (recv_inv_stmt) and the set cut (recv_set_at). Each
   phase restarts from a symbolic state built from the concrete registers (bp_entryP, bp_entry0, bp_entryR,
   bp_entryT) and runs with the image-B engine (TransportGRunB.v paj_run_x / paj_run_to_x, DgnTransportBPaLib.v
   paj_branch). Image A's twin is lib/A/Prog/receive_seg_poll.v; its image-free lemmas are used by qualified Require.

   +0x0b8 .. +0x0c0 (bp_main): `addi a0, zero, 0x5ea`, `bltu s1, a0, 8` (bp_br_ltu on n < 1514), on the fall-through
     `addi s1, zero, 0x5ea`: s1 = got = min (n, 1514) (receive_cg.v recv_got) at +0x0c4 on each side.
   +0x0c4 .. +0x0d0 (bp_got): a2 = sp, a0 = s0 = a, a1 = s1 = got, `jal spec_read_frame`: the cut file's recv_srf_at at
     len = got (continuation form; the run writes nothing, so recv_cur, recv_blk and the world relation at
     recv_w2 Bw bytes hold at the call memory: bp_cur_view, bp_blk_view, bp_tw_view). Its continuation is bp_ret at
     the return address +0x0d4, with the struct's 80 bytes TContract.sf_bytes a (srf_f bytes got) at the frame's sp.
   +0x0d4 .. +0x11c (bp_ret): the state holds the struct's send field (4 bytes at sp + 32) as atom 32 (bp_sf_send:
     the bytes put 4 (sf_send f) at offset 32; bp_srf_send, plain receive.v r_srf_send: the value is recv_send of the
     first got bytes); `slli a0, s2, 62`, `andi a1, s2, 1`, `lw a2, 32(sp)`, the 8-byte store of got at g_rx_len, the
     4-byte store of (pf & 1) + 1 at g_rx_times (bp_den_times), the 8-byte store of a at g_rx, the 4-byte stores of
     the send value at g_rx_send (bp_sext_mod) and of bit 1 of pf at g_rx_fail (bp_den_fails); s2 = that bit xor 1
     = recv_ticked pf (bp_den_ticked); the bytes of the five fields by bp_chunk_bytes, the world recv_w2c by
     bp_tw_w2c over TWorldG.v tw_write; a0 = &g_s, a1 = 0; the call of diginet_session_poll by recv_calls'
     transport_diginet_session_poll_cg at TF = Some (TFrame a bytes), w = 0: the model by bp_model (receive_cg.v
     recv_model, image A's recv_some_inv_u); trans_tframe_at by the block in the current ablocks below
     alloc_ceiling; trans_tf_off_g and poll_apart by YCbq.v blk_img and bp_poll_wr_G (every row of poll_wr is a
     field of a row of TMAP_B, or a notice store: TransportGNoticeB.v notice_wr_G); trans_rom_view_rd by bp_rom
     (acall_kept_g's image clause); iorecv_rx_in by g_rx (recv_w2c ..) = a and TCb.v frame_from_base; the invariants
     by recv_inv_stmt's second clause; poll_rx_each by recv_fix's recv_dn_each.
   The callee's transport_cg_post: e = 0; frames, Permutation and mo_le_trans; acall_kept_g by TransportGCg.v
     dk_kept_trans_g over the store run (bp_kept_run) and dk_kept_trans_nf_g over the callee (poll_wr is a row of
     recv_wr); the saved words lie above the callee's window.
   +0x120 .. +0x128: the stores of 0 at g_rx and g_rx_fail (s1, s3 kept by the callee; the world
     TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0 by bp_tw_w3), `j` to the set cut, and recv_set_at there with
     ticked = recv_ticked pf (the invariants by recv_inv_stmt's fifth clause, g_fail_next by image A's rp_gfn_w3,
     settle_m by bp_model). *)

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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import notice_cg io_send_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import spec_read_frame_cg settle_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRunB CanKit YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TOps TRunInv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require receive.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require receive.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require receive_seg_cut receive_seg_poll.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module PR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.receive.
Module UR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.receive.
Module ACUT := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.receive_seg_cut.
Module AP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.receive_seg_poll.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The pcs and the symbolic states                                  *)
(* ------------------------------------------------------------------ *)

(* +0x0c4 (got in s1), +0x0d4 (spec_read_frame's return), +0x120 (diginet_session_poll's return). *)
Definition BP_GOT : Z := AF_receive + 0xc4.
Definition BP_RS : Z := AF_receive + 0xd4.
Definition BP_RP : Z := AF_receive + 0x120.
Lemma bp_pcs : BP_GOT = 9420 /\ BP_RS = 9436 /\ BP_RP = 9512 /\ RECV_POLL = 9408 /\ RECV_SET = 9568.
Proof. repeat split; reflexivity. Qed.

(* +0x0b8: s1 = n (atom 9) below 2 ^ 16; the run stops at `bltu s1, a0` (+0x0bc). *)
Definition bp_factsP : facts := mkFacts [(9%nat, mkAF 0 65535 0)] [] [].
Definition ss_bpP : sstate := mkSS RECV_POLL sr_atoms [] None bp_factsP.
(* +0x0d4: the struct's send field (4 bytes at sp + 32) as atom 32 (read only); the five stores, at the auipc values
   of the pairs 83 (g_rx_len), 85 (g_rx_times), 84 (g_rx), 86 (g_rx_fail) and at s4 = RECV_RXS_HI (g_rx_send). *)
Definition bp_sf : YP09.region := YP09.mkRegion (Some 2%nat) 32 36 0 0 [YP09.mkChunk 32 (CVal 4 (SOff 32 0))].
Definition bp_len : YP09.region := YP09.mkRegion (Some (A_HI 83)) 0x538 0x540 0x538 0x540 [].
Definition bp_tm : YP09.region := YP09.mkRegion (Some (A_HI 85)) 0x50c 0x510 0x50c 0x510 [].
Definition bp_rx : YP09.region := YP09.mkRegion (Some (A_HI 84)) (-0x170) (-0x168) (-0x170) (-0x168) [].
Definition bp_snd : YP09.region := YP09.mkRegion (Some 20%nat) (-0x6f4) (-0x6f0) (-0x6f4) (-0x6f0) [].
Definition bp_fl : YP09.region := YP09.mkRegion (Some (A_HI 86)) 0x4e0 0x4e4 0x4e0 0x4e4 [].
Definition bp_factsR : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF RECV_RXS_HI RECV_RXS_HI 2);
           (32%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (A_HI 83, mkAF 6236040 6236040 3); (A_HI 84, mkAF 6158224 6158224 4);
           (A_HI 85, mkAF 6236052 6236052 2); (A_HI 86, mkAF 6236064 6236064 5)] [] [].
Definition ss_bpR : sstate := mkSS BP_RS sr_atoms [bp_sf; bp_len; bp_tm; bp_rx; bp_snd; bp_fl] None bp_factsR.
(* +0x120: the stores of 0 at s1 - 0x170 (g_rx) and s3 + 0x4e0 (g_rx_fail); s1, s3 kept by the callee. *)
Definition bp_rx2 : YP09.region := YP09.mkRegion (Some 9%nat) (-0x170) (-0x168) (-0x170) (-0x168) [].
Definition bp_fl2 : YP09.region := YP09.mkRegion (Some 19%nat) 0x4e0 0x4e4 0x4e0 0x4e4 [].
Definition bp_factsT : facts := mkFacts [(9%nat, mkAF 6158224 6158224 4); (19%nat, mkAF 6236064 6236064 5)] [] [].
Definition ss_bpT : sstate := mkSS BP_RP sr_atoms [bp_rx2; bp_fl2] None bp_factsT.

(* The registers from +0x0c4 to +0x0d4: what the cut keeps, s0 = a, s1 = got, s2 = the entry's a3, s4 = the PHi of
   g_rx_send. *)
Definition bp_regs (regs regs2 : bvmap 5 word) (a got : Z) : Prop :=
  recv_regs_keep regs regs2 /\
  YK11.getr regs2 8 = w64 a /\ YK11.getr regs2 9 = w64 got /\
  YK11.getr regs2 18 = YK11.getr regs 13 /\ YK11.getr regs2 20 = w64 RECV_RXS_HI.

Lemma bp_regs_pres : forall regs r1 r2 a got, bp_regs regs r1 a got -> aregs_preserved r1 r2 -> bp_regs regs r2 a got.
Proof.
  intros regs r1 r2 a got ((K2 & K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27) & K8 & K9 & K18 & K20) HP.
  refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))) (conj _ (conj _ (conj _ _)))).
  - exact (eq_trans (HP 2 ltac:(hnf; lia)) K2).
  - exact (eq_trans (HP 3 ltac:(hnf; lia)) K3).
  - exact (eq_trans (HP 4 ltac:(hnf; lia)) K4).
  - exact (eq_trans (HP 21 ltac:(hnf; lia)) K21).
  - exact (eq_trans (HP 22 ltac:(hnf; lia)) K22).
  - exact (eq_trans (HP 23 ltac:(hnf; lia)) K23).
  - exact (eq_trans (HP 24 ltac:(hnf; lia)) K24).
  - exact (eq_trans (HP 25 ltac:(hnf; lia)) K25).
  - exact (eq_trans (HP 26 ltac:(hnf; lia)) K26).
  - exact (eq_trans (HP 27 ltac:(hnf; lia)) K27).
  - exact (eq_trans (HP 8 ltac:(hnf; lia)) K8).
  - exact (eq_trans (HP 9 ltac:(hnf; lia)) K9).
  - exact (eq_trans (HP 18 ltac:(hnf; lia)) K18).
  - exact (eq_trans (HP 20 ltac:(hnf; lia)) K20).
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* Image A's lemmas on the same definitions (lib/A/Prog/receive_cg.v's recv_got, recv_send, recv_w2c and
   recv_ticked have the bodies of image B's), read at image B's names. *)
Lemma bp_got_range : forall bytes,
  0 <= recv_got bytes <= 1514 /\ recv_got bytes <= Z.of_nat (length bytes) /\
  (Z.of_nat (length bytes) < 1514 -> recv_got bytes = Z.of_nat (length bytes)) /\
  (1514 <= Z.of_nat (length bytes) -> recv_got bytes = 1514).
Proof. exact AP.rp_got_range. Qed.
Lemma bp_send_range : forall bytes, 0 <= recv_send (firstn (Z.to_nat (recv_got bytes)) bytes) < 2 ^ 32.
Proof. exact AP.rp_send_range. Qed.
Lemma bp_ticked_range : forall pf, 0 <= recv_ticked pf <= 1.
Proof. exact AP.rp_ticked_range. Qed.
Lemma bp_ticked_eq : forall pf, Z.lxor (Z.land (Z.shiftr pf 1) 1) 1 = recv_ticked pf.
Proof. exact AP.rp_ticked_eq. Qed.
Lemma bp_gfn_w2c : forall Bw bytes a pf, length Bw = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (recv_w2c Bw bytes a pf) = TW.g_fail_next Bw.
Proof. exact AP.rp_gfn_w2c. Qed.
Lemma bp_grx_w2c : forall Bw bytes a pf, length Bw = Z.to_nat TW.W_LEN -> 0 <= a < 2 ^ 64 ->
  TW.g_rx (recv_w2c Bw bytes a pf) = a.
Proof. exact AP.rp_grx_w2c. Qed.

(* The send field of the struct spec_read_frame fills from the first got bytes: the model's recv_send of them (plain
   receive.v r_srf_send). *)
Lemma bp_srf_send : forall bytes got, 0 <= got <= Z.of_nat (length bytes) ->
  DSpec.sf_send (srf_f bytes got) = recv_send (firstn (Z.to_nat got) bytes).
Proof.
  intros bytes got Hg. unfold srf_f.
  replace (DSpec.spec_read_frame (TW.zs bytes) got) with (DSpec.spec_read_frame (TW.zs bytes) (Z.of_nat (Z.to_nat got)))
    by (rewrite Z2Nat.id by lia; reflexivity).
  exact (UR.r_srf_send bytes (Z.to_nat got) ltac:(lia)).
Qed.

(* The model at the address the malloc returned, on the by-poll path. *)
Lemma bp_model : forall Bw a bytes by_poll pf Bw', a <> 0 -> by_poll <> 0 ->
  TOP.receive_m timg_B Bw a bytes by_poll pf = Some (Bw', tt) ->
  exists B2d r, TSS.diginet_session_poll_m timg_B (Some (TI.TFrame a bytes)) (recv_w2c Bw bytes a pf) 0 = Some (B2d, r) /\
    TC.settle_m (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0) (recv_ticked pf) = Some (Bw', tt).
Proof.
  intros Bw a bytes by_poll pf Bw' Ha Hb HM. rewrite recv_model in HM.
  rewrite (proj2 (Z.eqb_neq a 0) Ha), (proj2 (Z.eqb_neq by_poll 0) Hb) in HM.
  (* each scrutinee that is a model call is destructed before HM is reduced, so that the kernel never reduces a
     match on a model call *)
  destruct (TSS.diginet_session_poll_m timg_B (Some (TI.TFrame a bytes)) (recv_w2c Bw bytes a pf) 0)
    as [[B2d r]|] eqn:EP; cbv beta iota delta [negb] in HM; [|discriminate HM].
  exists B2d, r. split; [reflexivity|].
  destruct (TC.settle_m (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0) (recv_ticked pf)) as [[B4 []]|] eqn:ES;
    cbv beta iota in HM; [|discriminate HM].
  rewrite (ACUT.recv_some_inv_u B4 Bw' HM). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The worlds                                                       *)
(* ------------------------------------------------------------------ *)

(* One store of m bytes of v into a row, from the view that is rd at the bytes Pre names and rdF elsewhere. *)
Lemma bp_tw_step : forall (rd rdF : Z -> option Z) (Pre Post : Z -> bool) X o b n k (m : nat) v,
  In (o, b, n) TMAP_B -> 0 <= k -> k + Z.of_nat m <= n ->
  tw_at TMAP_B (fun x => if Pre x then rd x else rdF x) X ->
  (forall j, (j < m)%nat -> Post (b + k + Z.of_nat j) = false) ->
  (forall j, (j < m)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  (forall x, tw_in TMAP_B x -> ~ (b + k <= x < b + k + Z.of_nat m) -> Post x = Pre x) ->
  tw_at TMAP_B (fun x => if Post x then rd x else rdF x) (TW.upd X (o + k) (TW.put m v)).
Proof.
  intros rd rdF Pre Post X o b n k m v Hin Hk Hkm HX HP HV HO.
  apply (tw_write TMAP_B _ _ X o b n k m v TMAP_B_ok HX Hin Hk Hkm).
  - intros j Hj. cbv beta. rewrite (HP j Hj). exact (HV j Hj).
  - intros x Hx Hn. cbv beta. rewrite (HO x Hx Hn). reflexivity.
Qed.

Ltac bp_inb := repeat first
  [ rewrite AP.inb_false by (unfold TB_g_rx_send, TB_g_rx, TB_g_rx_len, TB_g_rx_times, TB_g_rx_fail in *; lia)
  | rewrite AP.inb_true by (unfold TB_g_rx_send, TB_g_rx, TB_g_rx_len, TB_g_rx_times, TB_g_rx_fail in *; lia)];
  cbn [orb].

(* The five by-poll stores (in any order of the code): the world handed to diginet_session_poll. *)
Lemma bp_tw_w2c : forall (rd rd' : Z -> option Z) Bw bytes a pf sv got t f,
  sv = recv_send (firstn (Z.to_nat (recv_got bytes)) bytes) -> got = recv_got bytes ->
  t = (if Z.land pf 1 =? 0 then 1 else 2) -> f = Z.land (Z.shiftr pf 1) 1 ->
  tw_at TMAP_B rd (recv_w2 Bw bytes) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_rx_send + Z.of_nat j) = Some (YO0f.le_byte sv 4 j)) ->
  (forall j, (j < 8)%nat -> rd' (TB_g_rx + Z.of_nat j) = Some (YO0f.le_byte a 8 j)) ->
  (forall j, (j < 8)%nat -> rd' (TB_g_rx_len + Z.of_nat j) = Some (YO0f.le_byte got 8 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_rx_times + Z.of_nat j) = Some (YO0f.le_byte t 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_rx_fail + Z.of_nat j) = Some (YO0f.le_byte f 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_g_rx_send <= x < TB_g_rx_send + 4) -> ~ (TB_g_rx <= x < TB_g_rx + 8) ->
     ~ (TB_g_rx_len <= x < TB_g_rx_len + 8) -> ~ (TB_g_rx_times <= x < TB_g_rx_times + 4) ->
     ~ (TB_g_rx_fail <= x < TB_g_rx_fail + 4) -> rd' x = rd x) ->
  tw_at TMAP_B rd' (recv_w2c Bw bytes a pf).
Proof.
  intros rd rd' Bw bytes a pf sv got t f Esv Egot Et Ef HX VS VR VL VT VF HO.
  set (P4 := fun x => AP.inb TB_g_rx_fail (TB_g_rx_fail + 4) x).
  set (P3 := fun x => (AP.inb TB_g_rx_times (TB_g_rx_times + 4) x || P4 x)%bool).
  set (P2 := fun x => (AP.inb TB_g_rx_len (TB_g_rx_len + 8) x || P3 x)%bool).
  set (P1 := fun x => (AP.inb TB_g_rx (TB_g_rx + 8) x || P2 x)%bool).
  set (P0 := fun x => (AP.inb TB_g_rx_send (TB_g_rx_send + 4) x || P1 x)%bool).
  assert (H0 : tw_at TMAP_B (fun x => if P0 x then rd x else rd' x) (recv_w2 Bw bytes)).
  { apply (tw_kept TMAP_B rd); [exact HX|]. intros x Hx. cbv beta.
    destruct (P0 x) eqn:E0; [reflexivity|].
    unfold P0, P1, P2, P3, P4 in E0. apply orb_false_iff in E0 as [E1 E0].
    apply orb_false_iff in E0 as [E2 E0]. apply orb_false_iff in E0 as [E3 E0].
    apply orb_false_iff in E0 as [E4 E5].
    apply HO; [exact Hx | exact (AP.inb_false_iff _ _ _ E1) | exact (AP.inb_false_iff _ _ _ E2)
      | exact (AP.inb_false_iff _ _ _ E3) | exact (AP.inb_false_iff _ _ _ E4) | exact (AP.inb_false_iff _ _ _ E5)]. }
  assert (H1 : tw_at TMAP_B (fun x => if P1 x then rd x else rd' x)
    (TW.upd (recv_w2 Bw bytes) (TW.OFF_g_rx_send + 0) (TW.put 4 sv))).
  { apply (bp_tw_step rd rd' P0 P1 _ TW.OFF_g_rx_send TB_g_rx_send TW.SZ_g_rx_send 0 4 sv TMAP_B_g_rx_send);
      [lia | unfold TW.SZ_g_rx_send; lia | exact H0 | | | ].
    - intros j Hj. unfold P1, P2, P3, P4. bp_inb. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VS j Hj).
    - intros x _ Hn. unfold P0. rewrite AP.inb_false by lia. reflexivity. }
  assert (H2 : tw_at TMAP_B (fun x => if P2 x then rd x else rd' x)
    (TW.upd (TW.upd (recv_w2 Bw bytes) (TW.OFF_g_rx_send + 0) (TW.put 4 sv)) (TW.OFF_g_rx + 0) (TW.put 8 a))).
  { apply (bp_tw_step rd rd' P1 P2 _ TW.OFF_g_rx TB_g_rx TW.SZ_g_rx 0 8 a TMAP_B_g_rx);
      [lia | unfold TW.SZ_g_rx; lia | exact H1 | | | ].
    - intros j Hj. unfold P2, P3, P4. bp_inb. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VR j Hj).
    - intros x _ Hn. unfold P1. rewrite AP.inb_false by lia. reflexivity. }
  assert (H3 : tw_at TMAP_B (fun x => if P3 x then rd x else rd' x)
    (TW.upd (TW.upd (TW.upd (recv_w2 Bw bytes) (TW.OFF_g_rx_send + 0) (TW.put 4 sv)) (TW.OFF_g_rx + 0) (TW.put 8 a))
      (TW.OFF_g_rx_len + 0) (TW.put 8 got))).
  { apply (bp_tw_step rd rd' P2 P3 _ TW.OFF_g_rx_len TB_g_rx_len TW.SZ_g_rx_len 0 8 got TMAP_B_g_rx_len);
      [lia | unfold TW.SZ_g_rx_len; lia | exact H2 | | | ].
    - intros j Hj. unfold P3, P4. bp_inb. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VL j Hj).
    - intros x _ Hn. unfold P2. rewrite AP.inb_false by lia. reflexivity. }
  assert (H4 : tw_at TMAP_B (fun x => if P4 x then rd x else rd' x)
    (TW.upd (TW.upd (TW.upd (TW.upd (recv_w2 Bw bytes) (TW.OFF_g_rx_send + 0) (TW.put 4 sv)) (TW.OFF_g_rx + 0)
      (TW.put 8 a)) (TW.OFF_g_rx_len + 0) (TW.put 8 got)) (TW.OFF_g_rx_times + 0) (TW.put 4 t))).
  { apply (bp_tw_step rd rd' P3 P4 _ TW.OFF_g_rx_times TB_g_rx_times TW.SZ_g_rx_times 0 4 t TMAP_B_g_rx_times);
      [lia | unfold TW.SZ_g_rx_times; lia | exact H3 | | | ].
    - intros j Hj. unfold P4. bp_inb. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VT j Hj).
    - intros x _ Hn. unfold P3. rewrite AP.inb_false by lia. reflexivity. }
  assert (H5 : tw_at TMAP_B (fun x => if (fun _ : Z => false) x then rd x else rd' x)
    (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (recv_w2 Bw bytes) (TW.OFF_g_rx_send + 0) (TW.put 4 sv)) (TW.OFF_g_rx + 0)
      (TW.put 8 a)) (TW.OFF_g_rx_len + 0) (TW.put 8 got)) (TW.OFF_g_rx_times + 0) (TW.put 4 t))
      (TW.OFF_g_rx_fail + 0) (TW.put 4 f))).
  { apply (bp_tw_step rd rd' P4 (fun _ => false) _ TW.OFF_g_rx_fail TB_g_rx_fail TW.SZ_g_rx_fail 0 4 f
      TMAP_B_g_rx_fail); [lia | unfold TW.SZ_g_rx_fail; lia | exact H4 | | | ].
    - intros j Hj. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VF j Hj).
    - intros x _ Hn. unfold P4. rewrite AP.inb_false by lia. reflexivity. }
  rewrite !Z.add_0_r in H5. subst sv got t f.
  apply (tw_kept TMAP_B _ rd' _ H5). intros x _. reflexivity.
Qed.

(* The two stores of 0 after the call (g_rx, then g_rx_fail). *)
Lemma bp_tw_w3 : forall (rd rd' : Z -> option Z) B2d,
  tw_at TMAP_B rd B2d ->
  (forall j, (j < 8)%nat -> rd' (TB_g_rx + Z.of_nat j) = Some (YO0f.le_byte 0 8 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_rx_fail + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_g_rx <= x < TB_g_rx + 8) -> ~ (TB_g_rx_fail <= x < TB_g_rx_fail + 4) ->
     rd' x = rd x) ->
  tw_at TMAP_B rd' (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0).
Proof.
  intros rd rd' B2d HX VR VF HO.
  set (P1 := fun x => AP.inb TB_g_rx_fail (TB_g_rx_fail + 4) x).
  set (P0 := fun x => (AP.inb TB_g_rx (TB_g_rx + 8) x || P1 x)%bool).
  assert (H0 : tw_at TMAP_B (fun x => if P0 x then rd x else rd' x) B2d).
  { apply (tw_kept TMAP_B rd); [exact HX|]. intros x Hx. cbv beta.
    destruct (P0 x) eqn:E0; [reflexivity|].
    unfold P0, P1 in E0. apply orb_false_iff in E0 as [E1 E2].
    apply HO; [exact Hx | exact (AP.inb_false_iff _ _ _ E1) | exact (AP.inb_false_iff _ _ _ E2)]. }
  assert (H1 : tw_at TMAP_B (fun x => if P1 x then rd x else rd' x) (TW.upd B2d (TW.OFF_g_rx + 0) (TW.put 8 0))).
  { apply (bp_tw_step rd rd' P0 P1 _ TW.OFF_g_rx TB_g_rx TW.SZ_g_rx 0 8 0 TMAP_B_g_rx);
      [lia | unfold TW.SZ_g_rx; lia | exact H0 | | | ].
    - intros j Hj. unfold P1. bp_inb. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VR j Hj).
    - intros x _ Hn. unfold P0. rewrite AP.inb_false by lia. reflexivity. }
  assert (H2 : tw_at TMAP_B (fun x => if (fun _ : Z => false) x then rd x else rd' x)
    (TW.upd (TW.upd B2d (TW.OFF_g_rx + 0) (TW.put 8 0)) (TW.OFF_g_rx_fail + 0) (TW.put 4 0))).
  { apply (bp_tw_step rd rd' P1 (fun _ => false) _ TW.OFF_g_rx_fail TB_g_rx_fail TW.SZ_g_rx_fail 0 4 0
      TMAP_B_g_rx_fail); [lia | unfold TW.SZ_g_rx_fail; lia | exact H1 | | | ].
    - intros j Hj. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VF j Hj).
    - intros x _ Hn. unfold P1. rewrite AP.inb_false by lia. reflexivity. }
  rewrite !Z.add_0_r in H2.
  apply (tw_kept TMAP_B _ rd' _ H2). intros x _. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The values the code forms                                        *)
(* ------------------------------------------------------------------ *)

(* `andi a1, s2, 1; addi a1, a1, 1` (g_rx_times), `slli a0, s2, 62; srli a0, a0, 63` (g_rx_fail) and
   `xori s2, a0, 1` (ticked), on s2 = the entry's a3 (atom n), whose low 32 bits are pf (plain receive.v r_twice,
   r_fails). *)
Lemma bp_den_times : forall E (n : nat) w pf, ew E n = w -> bv_unsigned w mod 2 ^ 32 = pf ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n 0) (SLit 1)) (SLit 1)) = Z_to_bv 64 (Z.land pf 1 + 1).
Proof.
  intros E n w pf H Hp. rewrite denot_lit_U. f_equal.
  rewrite !U_SAlu, U_SOff, !U_SLit, H. cbn [zalu_raw].
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  rewrite Z.add_0_r, (zcanon_id (bv_unsigned w)) by (unfold M64; lia).
  rewrite PR.r_twice, Hp.
  destruct (AP.rp_land1 pf) as [E1|E1]; rewrite E1; reflexivity.
Qed.
Lemma bp_den_fails : forall E (n : nat) w pf, ew E n = w -> bv_unsigned w mod 2 ^ 32 = pf ->
  sv_denot E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 62)) (SLit 63)) = Z_to_bv 64 (Z.land (Z.shiftr pf 1) 1).
Proof.
  intros E n w pf H Hp. rewrite denot_lit_U. f_equal.
  rewrite !U_SAlu, U_SOff, !U_SLit, H. cbn [zalu_raw].
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  rewrite Z.add_0_r, (zcanon_id (bv_unsigned w)) by (unfold M64; lia).
  change (Z.land (zcanon 62) 63) with 62. change (Z.land (zcanon 63) 63) with 63.
  pose proof (PR.r_fails w) as F. rewrite Z_to_bv_unsigned in F.
  rewrite (zcanon_wrap (Z.shiftl (bv_unsigned w) 62)). rewrite F, Hp.
  rewrite zcanon_id; [reflexivity|]. destruct (AP.rp_land1 (Z.shiftr pf 1)) as [E1|E1]; rewrite E1; unfold M64; lia.
Qed.
Lemma bp_den_ticked : forall E (n : nat) w pf, ew E n = w -> bv_unsigned w mod 2 ^ 32 = pf ->
  sv_denot E (SAlu ALU_XOR (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 62)) (SLit 63)) (SLit 1)) =
  Z_to_bv 64 (recv_ticked pf).
Proof.
  intros E n w pf H Hp. rewrite denot_lit_U. f_equal.
  rewrite U_SAlu, U_SLit. cbn [zalu_raw]. unfold U. rewrite (bp_den_fails E n w pf H Hp).
  rewrite <- bp_ticked_eq.
  destruct (AP.rp_land1 (Z.shiftr pf 1)) as [E1|E1]; rewrite E1; reflexivity.
Qed.

(* The low w bytes of a stored value, as a chunk of w bytes holds them. *)
Lemma bp_mod_den : forall E e v (w : N), sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  Z.of_N w <= 8 -> bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w) = v.
Proof.
  intros E e v w H Hv Hw. rewrite H.
  assert (Hp : 2 ^ (8 * Z.of_N w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite unsigned_lit_small by lia. apply Z.mod_small. exact Hv.
Qed.
Lemma bp_mod_lit : forall E (j : nat) v (w : N), ew E j = w64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  bv_unsigned (sv_denot E (SOff j 0)) mod 2 ^ (8 * Z.of_N w) = v.
Proof.
  intros E j v w H Hv Hw.
  assert (Hp : 2 ^ (8 * Z.of_N w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  apply (bp_mod_den E _ v w (AP.rp_den_lit E j v H ltac:(lia)) Hv Hw).
Qed.
(* A sign-extending 4-byte load of a value below 2 ^ 32, stored back as 4 bytes. *)
Lemma bp_sext_mod : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) mod 2 ^ (8 * Z.of_N 4) = v.
Proof.
  intros E n v H Hv.
  assert (D : sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 v)).
  { cbn [sv_denot]. rewrite H. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
    rewrite LMem.sext_small, LMem.signed_of_extract by lia. rewrite unsigned_lit_small by lia. reflexivity. }
  rewrite D, UR.r_swrap32_eq. change (8 * Z.of_N 4) with 32. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. change (2 ^ 32) with 4294967296 in *.
  change (2 ^ 31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

(* The branch `bltu sK, a0` on an atom below 2 ^ 63 and a literal. *)
Lemma bp_br_ltu : forall E (j : nat) n c, ew E j = w64 n -> 0 <= n < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  branch_taken BC_LTU (sv_denot E (SOff j 0)) (sv_denot E (SLit c)) = (n <? c).
Proof.
  intros E j n c H Hn Hc. rewrite (AP.rp_den_lit E j n H ltac:(lia)).
  cbn [branch_taken sv_denot]. rewrite EPI.mrxk_ltu by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The written bytes                                                *)
(* ------------------------------------------------------------------ *)

(* The five fields the code stores before the call, the two after it. *)
Definition bp_Z5 (x : Z) : Prop :=
  TB_g_rx_send <= x < TB_g_rx_send + 4 \/ TB_g_rx <= x < TB_g_rx + 8 \/ TB_g_rx_len <= x < TB_g_rx_len + 8 \/
  TB_g_rx_times <= x < TB_g_rx_times + 4 \/ TB_g_rx_fail <= x < TB_g_rx_fail + 4.
Definition bp_Z2 (x : Z) : Prop := TB_g_rx <= x < TB_g_rx + 8 \/ TB_g_rx_fail <= x < TB_g_rx_fail + 4.

Lemma bp_inG_row : forall o b n x, In (o, b, n) TMAP_B -> b <= x < b + n -> inG TG.G_HARNESS_B x.
Proof.
  intros o b n x Hin Hx. unfold inG. apply Exists_exists. exists (b, n).
  split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma bp_twb_G : forall o b n A w x, In (o, b, n) TMAP_B -> o <= A -> A + w <= o + n -> twb_fld o b A w x ->
  inG TG.G_HARNESS_B x.
Proof. intros o b n A w x Hin H1 H2 Hx. unfold twb_fld in Hx. apply (bp_inG_row o b n x Hin). lia. Qed.
Lemma bp_Z5_G : forall x, bp_Z5 x -> 0 <= x < 0x600000 /\ inG TG.G_HARNESS_B x.
Proof.
  intros x Hx.
  split; [unfold bp_Z5, TB_g_rx_send, TB_g_rx, TB_g_rx_len, TB_g_rx_times, TB_g_rx_fail in Hx; lia|].
  destruct Hx as [H | [H | [H | [H | H]]]].
  - apply (bp_inG_row _ _ _ x TMAP_B_g_rx_send). unfold TW.SZ_g_rx_send. lia.
  - apply (bp_inG_row _ _ _ x TMAP_B_g_rx). unfold TW.SZ_g_rx. lia.
  - apply (bp_inG_row _ _ _ x TMAP_B_g_rx_len). unfold TW.SZ_g_rx_len. lia.
  - apply (bp_inG_row _ _ _ x TMAP_B_g_rx_times). unfold TW.SZ_g_rx_times. lia.
  - apply (bp_inG_row _ _ _ x TMAP_B_g_rx_fail). unfold TW.SZ_g_rx_fail. lia.
Qed.
Lemma bp_Z2_G : forall x, bp_Z2 x -> 0 <= x < 0x600000 /\ inG TG.G_HARNESS_B x.
Proof. intros x Hx. apply bp_Z5_G. unfold bp_Z2, bp_Z5 in *. tauto. Qed.

(* Every byte diginet_session_poll may store (diginet_session_poll_cg.v poll_wr) is a byte of G: each row of each
   callee's written range is a field of a row of TMAP_B, or a byte notice stores (TransportGNoticeB.v
   notice_wr_G). *)
Ltac bp_bnd := first
  [ unfold TW.A_OW_t_state, TW.OW_t_ESZ, TC.TRANS_MAX, TC.A_OW_dn_body, TW.OW_dn_N, TW.A_Cmd_st, TC.CMDS_MAX,
      TW.A_S_queue_bytes, TW.S_queue_N, TW.S_queue_ESZ, TW.A_M_fly_frame, TC.SPEC_MAX_FRAME, TW.OFF_OW, TW.SZ_OW,
      TW.OFF_g_s, TW.SZ_g_s, TW.OFF_g_cmd, TW.SZ_g_cmd, TW.OFF_M, TW.SZ_M in *; lia
  | vm_compute; congruence ].
Ltac bp_rowG H := first
  [ refine (bp_twb_G _ _ _ _ _ _ TMAP_B_M _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_s _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_cmd _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_q _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_fail_next _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_raw _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_last_counter _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_nq _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_ncmd _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_rx_send _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_rx_fail _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_rx_times _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_now _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_rx _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_rx_len _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_g_cfg _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_GOT _ _ H); bp_bnd
  | refine (bp_twb_G _ _ _ _ _ _ TMAP_B_OW _ _ H); bp_bnd ].
Ltac bp_wr_split H :=
  repeat match type of H with
  | _ \/ _ => destruct H as [H | H]
  | _ /\ _ => let Hb := fresh "Hb" in destruct H as [Hb H]
  | exists _, _ => let y := fresh "y" in destruct H as [y H]
  end.

Lemma bp_poll_wr_G : forall x, poll_wr x -> inG TG.G_HARNESS_B x.
Proof.
  intros x H.
  cbv beta delta [poll_wr mtick_wr mlost_wr mset_st_wr mset_wr mrx_wr srx_wr onann_wr onack_wr ondata_wr sstate_wr
    tick_wr wake_wr maybeon_wr iosend_wr senddata_wr] in H.
  bp_wr_split H; first [exact (TransportGNoticeB.notice_wr_G _ _ _ H) | bp_rowG H].
Qed.

(* ------------------------------------------------------------------ *)
(* 6. Bytes read back, what the runs keep, the entry states            *)
(* ------------------------------------------------------------------ *)

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* A region cell of n bytes holding v, read byte by byte through the view. *)
Lemma bp_aview_of_val : forall H (m : word -> option byte) a (n : nat) v j,
  val_mem segs (mrestrict H m) a n v -> (j < n)%nat ->
  aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
  intros H m a n v j HV Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
(* The bytes a chunk of w bytes holding the value v leaves, read through the view. *)
Lemma bp_chunk_bytes : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e v,
  region_ok segs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w) = v ->
  forall j, (j < N.to_nat w)%nat ->
  aview segs H m (base_val E bopt + off + Z.of_nat j) = Some (YO0f.le_byte v (N.to_nat w) j).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e v (_ & _ & _ & Hcs) Hin Hw He j Hj.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  pose proof (val_of_chunk_any segs E _ _ off w e Hc Hw) as HV. rewrite He in HV.
  exact (bp_aview_of_val H m _ _ v j HV Hj).
Qed.

(* The send field of the struct: the 4 bytes at offset 32 of TContract.sf_bytes fa f. *)
Lemma bp_sf_send : forall (mm : word -> option byte) base fa (f : DSpec.spec_frame),
  garr8 segs mm base (TW.zs (TCt.sf_bytes fa f)) -> val_mem segs mm (base + 32) 4 (DSpec.sf_send f).
Proof.
  intros mm base fa f HG kk Hk.
  assert (Hj : (32 + kk < length (TW.zs (TCt.sf_bytes fa f)))%nat)
    by (unfold TW.zs; rewrite length_map; change (length (TCt.sf_bytes fa f)) with 80%nat; lia).
  pose proof (garr8_mbyte segs mm base _ (32 + kk) HG Hj) as Hm.
  replace (base + 32 + Z.of_nat kk) with (base + Z.of_nat (32 + kk)) by lia. rewrite Hm. do 2 f_equal.
  rewrite <- (tw_le_byte_put 4 (DSpec.sf_send f) kk (Z_to_bv 8 0) Hk).
  destruct kk as [|[|[|[|kk]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
Qed.

(* The frame's bytes, the world relation, at a memory whose view is the cut's. *)
Lemma bp_blk_view : forall (W2 : world segs) mem2 memX a bytes,
  garr8 segs (mrestrict (w_H W2) mem2) a (TW.zs bytes) -> 0 <= a -> a + Z.of_nat (length bytes) <= 2 ^ 64 ->
  (forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) memX x = aview segs (w_H W2) mem2 x) ->
  garr8 segs (mrestrict (w_H W2) memX) a (TW.zs bytes).
Proof.
  intros W2 mem2 memX a bytes HB H0 H1 KV. apply (garr8_frame segs (mrestrict (w_H W2) mem2) _ _ _ HB).
  intros x Hx. unfold TW.zs in Hx. rewrite length_map in Hx.
  apply can_mbyte_of_aview. exact (KV x ltac:(lia)).
Qed.
Lemma bp_tw_view : forall (W2 : world segs) mem2 memX Bx,
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bx ->
  (forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) memX x = aview segs (w_H W2) mem2 x) ->
  tw_at TMAP_B (aview segs (w_H W2) memX) Bx.
Proof.
  intros W2 mem2 memX Bx HT KV. apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact HT|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  exact (KV x ltac:(lia)).
Qed.

(* A run that changes only bytes of G (Zs) keeps what a call keeps, over an empty window. *)
Lemma bp_kept_run : forall lyc Sc (W : world segs) memc mdc (Wx : world segs) mX mY s (Eo Zs : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  (forall a, Zs a -> 0 <= a < 0x600000 /\ inG TG.G_HARNESS_B a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H Wx) mY a = aview segs (w_H Wx) mX a) ->
  (forall a, apresent (w_H Wx) mX a -> apresent (w_H Wx) mY a) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc Wx mX Wx mY s s Eo.
Proof.
  intros lyc Sc W memc mdc Wx mX mY s Eo Zs LAWS HAR HZ Hkp Hgr.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. apply Hkp; [lia|]. intros HZa. destruct (HZ a HZa) as [Hl _]. lia.
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hce & _).
    apply Hkp; [lia|]. intros HZa. destruct (HZ _ HZa) as [_ Hg].
    exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HAR Hb ltac:(lia) (trans_g_img _ Hg)).
  - intros a Hi HnG _ _. pose proof (transportb_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    apply Hkp; [lia|]. intros HZa. exact (HnG (proj2 (HZ a HZa))).
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
    + apply Hkp; [lia|]. intros HZa. destruct (HZ _ HZa) as [_ Hg].
      exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr (trans_g_img _ Hg)).
    + pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd.
      apply Hkp; [lia|]. intros HZa. destruct (HZ _ HZa) as [Hl _]. lia.
  - intros a Ha Hw Hp. exact (Hgr a Hp).
  - intros a Ha. lia.
Qed.

(* The read-only bytes the callees read stay the image's: acall_kept_g keeps every TRANS_RO_RD byte (an image byte
   below G, outside the owned statics and errno). *)
Lemma bp_rom : forall ly2 S2 (W2 W3 : world segs) mem2 mem3 slo shi (E : Z -> Prop),
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  acall_kept_g segs B TG.G_HARNESS_B ly2 S2 W2 mem2 W3 mem3 slo shi E ->
  trans_rom_view_rd W2 mem2 -> trans_rom_view_rd W3 mem3.
Proof.
  intros ly2 S2 W2 W3 mem2 mem3 slo shi E HRO HNE (_ & _ & K3 & _) Hrom a Ha.
  rewrite <- (Hrom a Ha). destruct (trans_ro_rd_scoped B HRO HNE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_B_LO in Gh. lia.
Qed.

(* The valuations: the 32 registers and the extra atoms (32 ..). *)
Definition bp_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transportb) (Ereg regs extra).
Lemma bp_ew : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (bp_E regs extra) n = YK11.getr regs r.
Proof. intros regs extra n r Hn. unfold bp_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma bp_ew_x : forall regs extra j, (j < 8)%nat -> ew (bp_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. unfold bp_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma bp_ew_img : forall regs extra n, (A_TEXT <= n < A_LIM)%nat -> ew (bp_E regs extra) n = Z_to_bv 64 (VAL n).
Proof. intros regs extra n Hn. unfold bp_E. apply Eimg_img. exact Hn. Qed.
Lemma bp_env_img : forall regs extra, img_env VAL A_LIM (bp_E regs extra).
Proof. intros regs extra. unfold bp_E. apply Eimg_env. Qed.
Lemma bp_agree : forall regs extra, env_agree 32 (Ereg regs extra) (bp_E regs extra).
Proof. intros regs extra. split; [intros n Hn; unfold bp_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma bp_vals : VAL (A_HI 83) = 6236040 /\ VAL (A_HI 84) = 6158224 /\ VAL (A_HI 85) = 6236052 /\
  VAL (A_HI 86) = 6236064 /\ VAL (A_OBJ 9) = POLL_S /\ BASE = 529056.
Proof. vm_compute. repeat split. Qed.
Lemma bp_uimg : forall regs extra n v, (A_TEXT <= n < A_LIM)%nat -> VAL n = v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (bp_E regs extra) n) = v.
Proof. intros regs extra n v Hn Hv Hr. rewrite bp_ew_img by exact Hn. rewrite Hv. apply unsigned_lit_small. lia. Qed.
Lemma bp_ureg : forall regs extra n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> YK11.getr regs r = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (bp_E regs extra) n) = v.
Proof. intros regs extra n r v Hn Hr Hv. rewrite (bp_ew regs extra n r Hn), Hr. apply unsigned_lit_small. lia. Qed.

Ltac bp_facts := unfold facts_ok; cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok];
  unfold afact_ok; cbn [af_lo af_hi af_al2].

(* A fresh state at a pc of the listing: the registers as atoms, no region, no fact. *)
Lemma bp_entry0 : forall (Wx : world segs) regs mem pc,
  st_ok_pi segs VAL (bp_E regs []) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros Wx regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split.
Qed.

(* +0x0b8: no region, s1 = n. *)
Lemma bp_entryP : forall (Wx : world segs) regs mem n,
  YK11.getr regs 9 = w64 n -> 0 <= n <= 65535 ->
  st_ok_pi segs VAL (bp_E regs []) ss_bpP
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + RECV_POLL)) mem (YK11.seg_rom segs))).
Proof.
  intros Wx regs mem n R9 Hn.
  pose proof (bp_ureg regs [] 9 9%bv n eq_refl R9 ltac:(lia)) as U9.
  rewrite restrict_mkst_fx. unfold ss_bpP.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold bp_factsP. bp_facts. rewrite U9. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* +0x0d4: the struct's send field (atom 32) at sp + 32, the five stores' regions. *)
Lemma bp_entryR : forall (Wx : world segs) regs mem sp sv,
  YK11.getr regs 2 = w64 (sp - RECV_FRAME) -> 2 ^ 46 + RECV_FRAME <= sp <= 2 ^ 47 -> sp mod 16 = 0 ->
  YK11.getr regs 20 = w64 RECV_RXS_HI -> 0 <= sv < 2 ^ 32 ->
  val_mem segs (mrestrict (w_H Wx) mem) (sp - RECV_FRAME + 32) 4 sv ->
  st_ok_pi segs VAL (bp_E regs [w64 sv]) ss_bpR
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + BP_RS)) mem (YK11.seg_rom segs))).
Proof.
  intros Wx regs mem sp sv R2 Hsp Hal R20 Hsv HV.
  destruct bp_vals as (V83 & V84 & V85 & V86 & _).
  assert (ERF : RECV_FRAME = 128) by reflexivity.
  pose proof (bp_ureg regs [w64 sv] 2 2%bv (sp - RECV_FRAME) eq_refl R2 ltac:(lia)) as U2.
  pose proof (bp_ureg regs [w64 sv] 20 20%bv RECV_RXS_HI eq_refl R20 ltac:(unfold RECV_RXS_HI, TB_g_rx_send; lia))
    as U20.
  pose proof (bp_uimg regs [w64 sv] (A_HI 83) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V83 ltac:(lia)) as U83.
  pose proof (bp_uimg regs [w64 sv] (A_HI 84) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V84 ltac:(lia)) as U84.
  pose proof (bp_uimg regs [w64 sv] (A_HI 85) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V85 ltac:(lia)) as U85.
  pose proof (bp_uimg regs [w64 sv] (A_HI 86) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V86 ltac:(lia)) as U86.
  assert (A32 : ew (bp_E regs [w64 sv]) 32 = w64 sv) by exact (bp_ew_x regs [w64 sv] 0 ltac:(lia)).
  assert (U32 : bv_unsigned (ew (bp_E regs [w64 sv]) 32) = sv) by (rewrite A32; unfold w64; apply unsigned_lit_small; lia).
  assert (GW : forall o b n x, In (o, b, n) TMAP_B -> b <= x < b + n -> forall m, writable_at segs m x)
    by (intros o b n x Hin Hx m; exact (gx_rw_writable segs TG.G_HARNESS_B x G_HARNESS_B_rw (bp_inG_row o b n x Hin Hx) m)).
  rewrite restrict_mkst_fx. unfold ss_bpR.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons.
    + unfold region_ok. cbn [bp_sf YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs (bp_E regs [w64 sv]) _ (sp - RECV_FRAME) 32 4 (SOff 32 0) sv).
      * cbn [sv_denot]. rewrite A32. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      * change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
      * cbn. lia.
      * exact HV.
    + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [bp_len bp_tm bp_rx bp_snd bp_fl YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks
          base_val];
        rewrite ?U20, ?U83, ?U84, ?U85, ?U86;
        (split; [unfold RECV_RXS_HI, TB_g_rx_send; lia|]); (split; [unfold RECV_RXS_HI, TB_g_rx_send; lia|]);
        (split; [|constructor]); intros o Ho.
      * apply (GW _ _ _ _ TMAP_B_g_rx_len). unfold TB_g_rx_len, TW.SZ_g_rx_len. lia.
      * apply (GW _ _ _ _ TMAP_B_g_rx_times). unfold TB_g_rx_times, TW.SZ_g_rx_times. lia.
      * apply (GW _ _ _ _ TMAP_B_g_rx). unfold TB_g_rx, TW.SZ_g_rx. lia.
      * apply (GW _ _ _ _ TMAP_B_g_rx_send). unfold RECV_RXS_HI, TB_g_rx_send, TW.SZ_g_rx_send. lia.
      * apply (GW _ _ _ _ TMAP_B_g_rx_fail). unfold TB_g_rx_fail, TW.SZ_g_rx_fail. lia.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, bp_sf, bp_len, bp_tm, bp_rx, bp_snd, bp_fl.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U20, U83, U84, U85, U86.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia | unfold RECV_RXS_HI, TB_g_rx_send; lia].
  - unfold bp_factsR. bp_facts. rewrite U2, U20, U32, U83, U84, U85, U86.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I;
      first [lia | reflexivity | (change (2 ^ 4) with 16; lia)].
Qed.

(* +0x120: the two stores of 0, at s1 - 0x170 and s3 + 0x4e0. *)
Lemma bp_entryT : forall (Wx : world segs) regs mem,
  YK11.getr regs 9 = Z_to_bv 64 6158224 -> YK11.getr regs 19 = Z_to_bv 64 6236064 ->
  st_ok_pi segs VAL (bp_E regs []) ss_bpT
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + BP_RP)) mem (YK11.seg_rom segs))).
Proof.
  intros Wx regs mem R9 R19.
  pose proof (bp_ureg regs [] 9 9%bv 6158224 eq_refl R9 ltac:(lia)) as U9.
  pose proof (bp_ureg regs [] 19 19%bv 6236064 eq_refl R19 ltac:(lia)) as U19.
  assert (GW : forall o b n x, In (o, b, n) TMAP_B -> b <= x < b + n -> forall m, writable_at segs m x)
    by (intros o b n x Hin Hx m; exact (gx_rw_writable segs TG.G_HARNESS_B x G_HARNESS_B_rw (bp_inG_row o b n x Hin Hx) m)).
  rewrite restrict_mkst_fx. unfold ss_bpT.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [bp_rx2 bp_fl2 YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite ?U9, ?U19; (split; [lia|]); (split; [lia|]); (split; [|constructor]); intros o Ho.
    + apply (GW _ _ _ _ TMAP_B_g_rx). unfold TB_g_rx, TW.SZ_g_rx. lia.
    + apply (GW _ _ _ _ TMAP_B_g_rx_fail). unfold TB_g_rx_fail, TW.SZ_g_rx_fail. lia.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, bp_rx2, bp_fl2. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; first [exact I | lia].
  - unfold bp_factsT. bp_facts. rewrite U9, U19.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.
End k.

(* ------------------------------------------------------------------ *)
(* 7. The tactics of the runs                                          *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac bp_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac bp_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac bp_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac bp_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The environment after a run: the atoms below 1024 are the entry's. *)
Ltac bp_ewv := repeat (first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by (cbv; lia)]).
Ltac bp_curE HS := lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ _ => EF
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ _ => EF end.
(* Register rd of the state HS holds the entry's atom n, the entry register rs (Q : getr regsB rs = v). *)
Ltac bp_kreg HS regsB xs n rs rd Q H :=
  lazymatch type of Q with _ = ?v =>
    bp_reg HS rd v H ltac:(cbn [sv_denot]; bp_ewv; rewrite (bp_ew regsB xs n rs eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
                          exact Q)
  end.
(* A run that writes nothing: the written ranges of its frame are empty. *)
Ltac bp_cover0 := intros ? ? ? ? Hin Hy; cbv beta;
  lazymatch type of Hin with In ?z ?l => let l' := eval vm_compute in l in change (In z l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hy; lia |]);
  try destruct Hin.
(* After such a run: the view and the present bytes at mem2, carried to the run's memory. *)
Ltac bp_kv HS W2 mem2 KV GV :=
  let m1 := lazymatch type of HS with context [restrict _ ?msn] => constr:(ms_mem msn) end in
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let KV' := fresh "KV" in let GV' := fresh "GV" in
    assert (KV' : forall x, 0 <= x < 2 ^ 64 -> aview tfibsegs (w_H W2) m1 x = aview tfibsegs (w_H W2) mem2 x)
      by (intros x Hx; refine (eq_trans _ (KV x Hx));
          apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [bp_cover0 | exact Hx | tauto]);
    assert (GV' : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) m1 x)
      by (intros x Hx; exact (apresent_grows _ _ _ x HG (GV x Hx)));
    clear KV GV; rename KV' into KV; rename GV' into GV;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac bp_md := lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mt ?m0] =>
  let md' := fresh "md" in set (md' := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md'; clear mt end.
Ltac bp_awr0 := bp_awr_rs;
  repeat (apply awr_ok_x_cons_g; [intros ? Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* 8. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (p by_poll pf T : Z)
  (bytes Bw : list byte) (ch : list (Z * Z * Z)) (a : Z) (Bw' : list byte).
Hypothesis LAWS0 : recv_laws B MT.
Hypothesis CALLS : recv_calls B MT.
Hypothesis SRF : recv_srf_at B MT.
Hypothesis INV : recv_inv_stmt.
Hypothesis SET : recv_set_at B MT.
Hypothesis HFIX : recv_fix B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch.
Hypothesis HRES : recv_res Bw bytes by_poll pf a Bw'.
Hypothesis HBP : by_poll <> 0.
Local Abbreviation POST :=
  (@transport_recv_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).
Local Abbreviation CFG pc regs2 mem2 md2 :=
  (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + pc)) mem2 (YK11.seg_rom segs)) md2).
Local Abbreviation JX ly2 S2 W2 m2 d2 :=
  (@W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m2 d2
    (k + 1)).

(* The caller's entry state and its stack window. *)
Lemma bp_hfacts : @AR rc segs B lyc Sc W memc mdc /\ alloc_ceiling <= spZ regs - RECV_STK /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hwlo & Hwhi & _).
  pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
  pose proof HJi as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  split; [exact HARc|]. split; lia.
Qed.

(* What every cut carries, at a memory whose view is the cut's and whose present bytes include the cut's. *)
Lemma bp_cur_view : forall ly2 S2 (W2 : world segs) mem2 md2 memX mdX,
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
  JX ly2 S2 W2 memX mdX ->
  (forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) memX x = aview segs (w_H W2) mem2 x) ->
  (forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) memX x) ->
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 memX mdX.
Proof.
  intros ly2 S2 W2 mem2 md2 memX mdX (HJ2 & Hfrs & Hperm & Hmo2 & HK2 & Hsv2 & Ha4096) HJ KV GV.
  pose proof LAWS0 as (_ & _ & _ & _ & _ & _ & _ & _ & LAWS & _).
  destruct bp_hfacts as (HARc & Hce & Hsp47).
  pose proof asan_consts as (AC1 & _).
  assert (ERS : RECV_STK = 16512) by reflexivity.
  refine (conj HJ (conj Hfrs (conj Hperm (conj Hmo2 (conj _ (conj _ Ha4096)))))).
  - apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 W2 memX (spZ regs - RECV_STK) (spZ regs)
      (spZ regs) (spZ regs) (recv_wr bytes) (fun _ => False) Hce ltac:(lia) HK2); [| lia | lia | tauto].
    apply (bp_kept_run B lyc Sc W memc mdc W2 mem2 memX (spZ regs) (fun _ => False) (fun _ => False) LAWS HARc).
    + intros x [].
    + intros x Hx _. exact (KV x Hx).
    + exact GV.
  - rewrite Forall_forall in Hsv2 |- *. intros o Ho. rewrite <- (Hsv2 o Ho).
    assert (Hob : 8 <= fst o <= 48).
    { unfold RECV_SAVED in Ho. cbn [In] in Ho. repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
    apply rdword_ext. intros i Hi. apply KV. lia.
Qed.

(* +0x0d4 .. the set cut: the five stores, diginet_session_poll, the two stores of 0, `j` the set cut. *)
Lemma bp_ret : forall ly2 S2 (W2 : world segs) mem2 md2 regsX,
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
  recv_blk W2 mem2 a bytes ->
  tw_at TMAP_B (aview segs (w_H W2) mem2) (recv_w2 Bw bytes) ->
  garr8 segs (mrestrict (w_H W2) mem2) (spZ regs - RECV_FRAME)
    (TW.zs (TCt.sf_bytes a (srf_f bytes (recv_got bytes)))) ->
  bp_regs regs regsX a (recv_got bytes) ->
  SRr segs W2 (CFG BP_RS regsX mem2 md2) POST.
Proof.
intros ly2 S2 W2 mem2 md2 regsX HCUR HBLK HTW HSF HREGS.
pose proof LAWS0 as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
pose proof CALLS as (CM & CCPY & CMSET & CSRF & CPOLL & CMRX & CRX & CSETL & CFREE).
pose proof HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hch & Hal & Hwlo & Hwhi & Hbp & Hpf &
  Hn & Hgarr & Hsrc & Htw0 & Hgf0 & Hmod & Hrom & Hrinv & Hdn & Q1c & Q2c & Q3c & Q4c & Q5c & Hnev & Hlive & Hmo &
  Hcost & Htrm & Htrf).
pose proof HRES as ((Ha0 & Ha64) & HM).
pose proof HREGS as ((X2 & X3 & X4 & X21 & X22 & X23 & X24 & X25 & X26 & X27) & X8 & X9 & X18 & X20).
pose proof HCUR as (HJ & Hfrs & Hperm & Hmo2 & HK2 & Hsv2 & Ha4096).
destruct bp_hfacts as (HARc & Hce & Hsp47).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
assert (ERS : RECV_STK = 16512) by reflexivity.
assert (ERF : RECV_FRAME = 128) by reflexivity.
assert (EPS : POLL_STK <= 16384) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (Hblk : In (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hblk) as (_ & _ & Hbce & _ & _).
pose proof (req_size_pos (Z.max 1 (Z.of_nat (length bytes))) ltac:(lia)) as [_ Hreq].
pose proof (bp_got_range bytes) as (Rg1 & Rg2 & Rg3 & Rg4).
pose proof (bp_send_range bytes) as Rsv.
assert (Esv : DSpec.sf_send (srf_f bytes (recv_got bytes)) = recv_send (firstn (Z.to_nat (recv_got bytes)) bytes))
  by (apply bp_srf_send; lia).
set (sv := recv_send (firstn (Z.to_nat (recv_got bytes)) bytes)) in *.
assert (HVS : val_mem segs (mrestrict (w_H W2) mem2) (spZ regs - RECV_FRAME + 32) 4 sv)
  by (rewrite <- Esv; exact (bp_sf_send _ _ _ _ HSF)).
(* run R, +0x0d4 .. `jal diginet_session_poll` (+0x11c) *)
pose proof (@bp_entryR fx rc W2 regsX mem2 (spZ regs) sv X2 ltac:(lia) Hal X20 Rsv HVS) as HS.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) (bp_E regsX [w64 sv]) (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI : img_env VAL A_LIM (bp_E regsX [w64 sv])) by apply bp_env_img.
destruct bp_vals as (V83 & V84 & V85 & V86 & V9 & VB).
pose proof (bp_ureg regsX [w64 sv] 2 2%bv _ eq_refl X2 ltac:(lia)) as U2.
pose proof (bp_ureg regsX [w64 sv] 20 20%bv _ eq_refl X20 ltac:(unfold RECV_RXS_HI, TB_g_rx_send; lia)) as U20.
pose proof (bp_uimg regsX [w64 sv] (A_HI 83) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V83 ltac:(lia)) as U83.
pose proof (bp_uimg regsX [w64 sv] (A_HI 84) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V84 ltac:(lia)) as U84.
pose proof (bp_uimg regsX [w64 sv] (A_HI 85) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V85 ltac:(lia)) as U85.
pose proof (bp_uimg regsX [w64 sv] (A_HI 86) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V86 ltac:(lia)) as U86.
change (A_HI 83) with 483%nat in U83. change (A_HI 84) with 484%nat in U84.
change (A_HI 85) with 485%nat in U85. change (A_HI 86) with 486%nat in U86.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
paj_run_tok RUN HS HJ SHOK (0, 0).
{ bp_awr_rs.
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia |].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U83 in Hx;
    apply (bp_inG_row _ _ _ x TMAP_B_g_rx_len); unfold TB_g_rx_len, TW.SZ_g_rx_len in *; lia |].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U85 in Hx;
    apply (bp_inG_row _ _ _ x TMAP_B_g_rx_times); unfold TB_g_rx_times, TW.SZ_g_rx_times in *; lia |].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U84 in Hx;
    apply (bp_inG_row _ _ _ x TMAP_B_g_rx); unfold TB_g_rx, TW.SZ_g_rx in *; lia |].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U20 in Hx;
    apply (bp_inG_row _ _ _ x TMAP_B_g_rx_send); unfold RECV_RXS_HI, TB_g_rx_send, TW.SZ_g_rx_send in *; lia |].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U86 in Hx;
    apply (bp_inG_row _ _ _ x TMAP_B_g_rx_fail); unfold TB_g_rx_fail, TW.SZ_g_rx_fail in *; lia |].
  apply awr_ok_x_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in *; clearbody md1 end.
lazymatch type of HS with context [restrict _ ?mf] => rename mf into msC end.
(* run R wrote the five fields only *)
assert (KR1 : forall x, 0 <= x < 2 ^ 64 -> ~ bp_Z5 x -> aview segs (w_H W2) (ms_mem msC) x = aview segs (w_H W2) mem2 x).
{ intros x Hx Hnz. apply (kept_of_frame _ _ _ _ _ bp_Z5 HFr); [| exact Hx | exact Hnz].
  intros b wlo whi y Hin Hy. cbv beta.
  lazymatch type of Hin with In ?z ?l => let l' := eval vm_compute in l in change (In z l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hy;
    rewrite ?U20, ?U83, ?U84, ?U85, ?U86 in Hy;
    unfold bp_Z5, RECV_RXS_HI, TB_g_rx_send, TB_g_rx, TB_g_rx_len, TB_g_rx_times, TB_g_rx_fail in Hy |- *; lia |]).
  destruct Hin. }
assert (GA1 : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem msC) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
(* the atoms the stores read, at the run's environment *)
let EF := bp_curE HS in
(assert (W8 : ew EF 8 = w64 a) by (bp_ewv; exact (eq_trans (bp_ew regsX [w64 sv] 8 8%bv eq_refl) X8));
 assert (W9 : ew EF 9 = w64 (recv_got bytes)) by (bp_ewv; exact (eq_trans (bp_ew regsX [w64 sv] 9 9%bv eq_refl) X9));
 assert (W18 : ew EF 18 = YK11.getr regs 13) by (bp_ewv; exact (eq_trans (bp_ew regsX [w64 sv] 18 18%bv eq_refl) X18));
 assert (W32 : ew EF 32 = w64 sv) by (bp_ewv; exact (bp_ew_x regsX [w64 sv] 0 ltac:(lia)));
 assert (EU20 : bv_unsigned (ew EF 20) = RECV_RXS_HI) by (bp_ewv; exact U20);
 assert (EU83 : bv_unsigned (ew EF 483) = 6236040) by (bp_ewv; exact U83);
 assert (EU84 : bv_unsigned (ew EF 484) = 6158224) by (bp_ewv; exact U84);
 assert (EU85 : bv_unsigned (ew EF 485) = 6236052) by (bp_ewv; exact U85);
 assert (EU86 : bv_unsigned (ew EF 486) = 6236064) by (bp_ewv; exact U86);
 assert (E250 : ew EF 250 = w64 POLL_S)
   by (bp_ewv; rewrite (bp_ew_img regsX [w64 sv] 250 ltac:(unfold A_TEXT, A_LIM; lia)); unfold w64; f_equal;
       vm_compute; reflexivity);
 assert (E484 : ew EF 484 = w64 6158224)
   by (bp_ewv; rewrite (bp_ew_img regsX [w64 sv] 484 ltac:(unfold A_TEXT, A_LIM; lia)); unfold w64; f_equal;
       vm_compute; reflexivity);
 assert (E486 : ew EF 486 = w64 6236064)
   by (bp_ewv; rewrite (bp_ew_img regsX [w64 sv] 486 ltac:(unfold A_TEXT, A_LIM; lia)); unfold w64; f_equal;
       vm_compute; reflexivity)).
(* the five stores' bytes *)
bp_region HS 1%nat HR1. bp_region HS 2%nat HR2. bp_region HS 3%nat HR3. bp_region HS 4%nat HR4.
bp_region HS 5%nat HR5.
assert (VL : forall j, (j < 8)%nat -> aview segs (w_H W2) (ms_mem msC) (TB_g_rx_len + Z.of_nat j) =
  Some (YO0f.le_byte (recv_got bytes) 8 j)).
{ intros j Hj. pose proof (bp_chunk_bytes _ (w_H W2) (ms_mem msC) (Some 483%nat) _ _ _ _ _ 1336 8 (SOff 9 0)
    (recv_got bytes) HR1 ltac:(bp_in) ltac:(lia) (bp_mod_lit _ 9 _ 8 W9 ltac:(lia) ltac:(lia)) j Hj) as Hc.
  cbn [base_val] in Hc. rewrite EU83 in Hc.
  replace (6236040 + 1336) with TB_g_rx_len in Hc by (unfold TB_g_rx_len; lia). exact Hc. }
assert (VT : forall j, (j < 4)%nat -> aview segs (w_H W2) (ms_mem msC) (TB_g_rx_times + Z.of_nat j) =
  Some (YO0f.le_byte (if Z.land pf 1 =? 0 then 1 else 2) 4 j)).
{ intros j Hj.
  assert (Dt : forall EX, ew EX 18 = YK11.getr regs 13 ->
    bv_unsigned (sv_denot EX (SAlu ALU_ADD (SAlu ALU_AND (SOff 18 0) (SLit 1)) (SLit 1))) mod 2 ^ (8 * Z.of_N 4) =
    (if Z.land pf 1 =? 0 then 1 else 2)).
  { intros EX HX. rewrite <- AP.rp_times_eq. apply (bp_mod_den _ _ _ 4 (bp_den_times EX 18 _ pf HX H13)); [|lia].
    destruct (AP.rp_land1 pf) as [E1|E1]; rewrite E1; cbn; lia. }
  pose proof (bp_chunk_bytes _ (w_H W2) (ms_mem msC) (Some 485%nat) _ _ _ _ _ 1292 4 _ _ HR2 ltac:(bp_in) ltac:(lia)
    (Dt _ W18) j Hj) as Hc.
  cbn [base_val] in Hc. rewrite EU85 in Hc.
  replace (6236052 + 1292) with TB_g_rx_times in Hc by (unfold TB_g_rx_times; lia). exact Hc. }
assert (VR : forall j, (j < 8)%nat -> aview segs (w_H W2) (ms_mem msC) (TB_g_rx + Z.of_nat j) =
  Some (YO0f.le_byte a 8 j)).
{ intros j Hj. pose proof (bp_chunk_bytes _ (w_H W2) (ms_mem msC) (Some 484%nat) _ _ _ _ _ (-368) 8 (SOff 8 0)
    a HR3 ltac:(bp_in) ltac:(lia) (bp_mod_lit _ 8 _ 8 W8 ltac:(lia) ltac:(lia)) j Hj) as Hc.
  cbn [base_val] in Hc. rewrite EU84 in Hc.
  replace (6158224 + -368) with TB_g_rx in Hc by (unfold TB_g_rx; lia). exact Hc. }
assert (VS : forall j, (j < 4)%nat -> aview segs (w_H W2) (ms_mem msC) (TB_g_rx_send + Z.of_nat j) =
  Some (YO0f.le_byte sv 4 j)).
{ intros j Hj. pose proof (bp_chunk_bytes _ (w_H W2) (ms_mem msC) (Some 20%nat) _ _ _ _ _ (-1780) 4
    (SExt true 32 (SOff 32 0)) sv HR4 ltac:(bp_in) ltac:(lia) (bp_sext_mod _ 32 sv W32 Rsv) j Hj) as Hc.
  cbn [base_val] in Hc. rewrite EU20 in Hc.
  replace (RECV_RXS_HI + -1780) with TB_g_rx_send in Hc by (unfold RECV_RXS_HI, TB_g_rx_send; lia). exact Hc. }
assert (VF : forall j, (j < 4)%nat -> aview segs (w_H W2) (ms_mem msC) (TB_g_rx_fail + Z.of_nat j) =
  Some (YO0f.le_byte (Z.land (Z.shiftr pf 1) 1) 4 j)).
{ intros j Hj.
  assert (Df : forall EX, ew EX 18 = YK11.getr regs 13 ->
    bv_unsigned (sv_denot EX (SAlu ALU_SRL (SAlu ALU_SLL (SOff 18 0) (SLit 62)) (SLit 63))) mod 2 ^ (8 * Z.of_N 4) =
    Z.land (Z.shiftr pf 1) 1).
  { intros EX HX. apply (bp_mod_den _ _ _ 4 (bp_den_fails EX 18 _ pf HX H13)); [|lia].
    destruct (AP.rp_land1 (Z.shiftr pf 1)) as [E1|E1]; rewrite E1; cbn; lia. }
  pose proof (bp_chunk_bytes _ (w_H W2) (ms_mem msC) (Some 486%nat) _ _ _ _ _ 1248 4 _ _ HR5 ltac:(bp_in) ltac:(lia)
    (Df _ W18) j Hj) as Hc.
  cbn [base_val] in Hc. rewrite EU86 in Hc.
  replace (6236064 + 1248) with TB_g_rx_fail in Hc by (unfold TB_g_rx_fail; lia). exact Hc. }
clear HR1 HR2 HR3 HR4 HR5.
(* the world handed to diginet_session_poll *)
assert (TWC : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msC)) (recv_w2c Bw bytes a pf)).
{ apply (bp_tw_w2c (aview segs (w_H W2) mem2) _ Bw bytes a pf _ _ _ _ eq_refl eq_refl eq_refl eq_refl HTW
    VS VR VL VT VF).
  intros x Hx N1 N2 N3 N4 N5. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KR1; [lia|]. unfold bp_Z5. tauto. }
(* the registers at the call *)
bp_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 9512)) C1 ltac:(apply codeptr_val; assumption).
bp_kreg HS regsX [w64 sv] 2%nat (2%bv : bv 5) (2%bv : bv 5) X2 C2.
bp_kreg HS regsX [w64 sv] 3%nat (3%bv : bv 5) (3%bv : bv 5) X3 C3.
bp_kreg HS regsX [w64 sv] 4%nat (4%bv : bv 5) (4%bv : bv 5) X4 C4.
bp_kreg HS regsX [w64 sv] 8%nat (8%bv : bv 5) (8%bv : bv 5) X8 C8.
bp_kreg HS regsX [w64 sv] 20%nat (20%bv : bv 5) (20%bv : bv 5) X20 C20.
bp_kreg HS regsX [w64 sv] 21%nat (21%bv : bv 5) (21%bv : bv 5) X21 C21.
bp_kreg HS regsX [w64 sv] 22%nat (22%bv : bv 5) (22%bv : bv 5) X22 C22.
bp_kreg HS regsX [w64 sv] 23%nat (23%bv : bv 5) (23%bv : bv 5) X23 C23.
bp_kreg HS regsX [w64 sv] 24%nat (24%bv : bv 5) (24%bv : bv 5) X24 C24.
bp_kreg HS regsX [w64 sv] 25%nat (25%bv : bv 5) (25%bv : bv 5) X25 C25.
bp_kreg HS regsX [w64 sv] 26%nat (26%bv : bv 5) (26%bv : bv 5) X26 C26.
bp_kreg HS regsX [w64 sv] 27%nat (27%bv : bv 5) (27%bv : bv 5) X27 C27.
bp_reg HS (18%bv : bv 5) (Z_to_bv 64 (recv_ticked pf)) C18 ltac:(exact (bp_den_ticked _ 18 _ pf W18 H13)).
bp_reg HS (9%bv : bv 5) (Z_to_bv 64 6158224) C9 ltac:(exact (AP.rp_den_lit _ 484 6158224 E484 ltac:(lia))).
bp_reg HS (19%bv : bv 5) (Z_to_bv 64 6236064) C19 ltac:(exact (AP.rp_den_lit _ 486 6236064 E486 ltac:(lia))).
bp_reg HS (10%bv : bv 5) (w64 POLL_S) C10 ltac:(exact (AP.rp_den_lit _ 250 POLL_S E250 ltac:(unfold POLL_S, TB_g_s; lia))).
bp_reg HS (11%bv : bv 5) (w64 0) C11 ltac:(reflexivity).
assert (USPC : spZ (ms_regs msC) = spZ regs - 128)
  by (unfold spZ at 1; rewrite C2; unfold w64; rewrite ERF; apply unsigned_lit_small; lia).
(* the model on this path *)
destruct (bp_model Bw a bytes by_poll pf Bw' ltac:(lia) HBP HM) as (B2d & r & HPM & HSM).
(* the frame at the call *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARC.
assert (FNG : forall x, a <= x < a + Z.max 1 (Z.of_nat (length bytes)) -> ~ inG TG.G_HARNESS_B x).
{ intros x Hx Hg. exact (blk_img segs B LAWS ly2 S2 W2 mem2 md2 a _ x HAR2 Hblk ltac:(lia) (trans_g_img x Hg)). }
assert (FN5 : forall x, a <= x < a + Z.max 1 (Z.of_nat (length bytes)) -> ~ bp_Z5 x)
  by (intros x Hx HZ; exact (FNG x Hx (proj2 (bp_Z5_G x HZ)))).
assert (HBLKC : garr8 segs (mrestrict (w_H W2) (ms_mem msC)) a (TW.zs bytes)).
{ apply (garr8_frame segs (mrestrict (w_H W2) mem2) _ _ _ HBLK). intros x Hx.
  unfold TW.zs in Hx. rewrite length_map in Hx.
  apply can_mbyte_of_aview. exact (KR1 x ltac:(lia) (FN5 x ltac:(lia))). }
assert (PTF : trans_tframe_at B ly2 S2 W2 (ms_mem msC) (ms_regs msC) POLL_STK (Some (TI.TFrame a bytes))).
{ unfold trans_tframe_at. cbn [TI.tf_addr TI.tf_bytes].
  split; [lia|]. split; [exact HBLKC|].
  split; [left; exists a, (Z.max 1 (Z.of_nat (length bytes))); split; [exact Hblk | lia]|].
  unfold decode_off_win. left. rewrite USPC. lia. }
assert (PTFG : trans_tf_off_g (Some (TI.TFrame a bytes))).
{ intros fr Efr x Hx. injection Efr as <-. cbn [TI.tf_addr TI.tf_bytes] in Hx. apply FNG. lia. }
assert (PAP : poll_apart (Some (TI.TFrame a bytes))).
{ intros x Hw fr Efr Hx. injection Efr as <-. cbn [TI.tf_addr TI.tf_bytes] in Hx.
  exact (FNG x ltac:(lia) (bp_poll_wr_G x Hw)). }
assert (PROM : trans_rom_view_rd W2 (ms_mem msC)).
{ pose proof (bp_rom B lyc Sc W W2 memc mem2 _ _ _ HRU HRE HK2 Hrom) as R2r.
  intros x Hx. pose proof (trans_ro_rd_bounds x Hx) as Hb.
  rewrite (KR1 x ltac:(lia) ltac:(unfold bp_Z5, TB_g_rx_send, TB_g_rx, TB_g_rx_len, TB_g_rx_times, TB_g_rx_fail; lia)).
  exact (R2r x Hx). }
assert (PIRX : iorecv_rx_in (Some (TI.TFrame a bytes)) (recv_w2c Bw bytes a pf)).
{ unfold iorecv_rx_in. intros _. rewrite (bp_grx_w2c Bw bytes a pf HLB ltac:(lia)).
  pose proof (TC.frame_from_base (TI.TFrame a bytes)) as E. cbn [TI.tf_addr] in E. rewrite E. discriminate. }
destruct (proj1 (proj2 INV) Bw bytes a pf HLB Hrinv) as (I1 & I2 & I4 & I5a & I5b & I4b & I2b).
assert (PRX : poll_rx_each timg_B (Some (TI.TFrame a bytes)) (poll_dn_in (Some (TI.TFrame a bytes)))
  (recv_w2c Bw bytes a pf)).
{ pose proof (Hdn a (conj Ha0 Ha64)) as Hpe. rewrite (proj2 (Z.eqb_neq by_poll 0) HBP) in Hpe. exact Hpe. }
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_diginet_session_poll) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (CPOLL fx STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem msC) md1 (k + 1) (ms_regs msC) 0 r
    (Some (TI.TFrame a bytes)) (recv_w2c Bw bytes a pf) B2d HJ).
  - rewrite C1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - unfold raZ. rewrite C1, VB. rewrite unsigned_lit_small by lia. lia.
  - exact (eq_trans C3 Hgp).
  - exact (eq_trans C4 Htp).
  - exact C10.
  - exact C11.
  - rewrite USPC. replace (spZ regs - 128) with (spZ regs + (-8) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - lia.
  - exact TWC.
  - rewrite (bp_gfn_w2c Bw bytes a pf HLB). exact Hgf0.
  - exact HPM.
  - exact PTF.
  - exact PTFG.
  - exact PROM.
  - exact PAP.
  - exact PIRX.
  - exact I1.
  - exact I2.
  - exact I2b.
  - exact I4.
  - exact I4b.
  - exact I5a.
  - exact I5b.
  - exact PRX.
  - rewrite Hfrs. exact Q1c.
  - rewrite Hfrs. exact Q2c.
  - rewrite Hfrs. exact Q3c.
  - rewrite Hfrs. exact Q4c.
  - rewrite Hfrs. exact Q5c.
  - unfold POLL_EV, RECV_EV in *. lia. }
intros W3 c3 _ HPOST.
unfold transport_poll_post, transport_cg_post in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e & -> & He & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX10 & Htw3 &
  Hgf3).
assert (He0 : e = 0) by (unfold POLL_EV in He; lia). subst e. rewrite Z.add_0_r in HJ3.
(* the registers diginet_session_poll kept *)
assert (T2 : YK11.getr regs3 2 = w64 (spZ regs - RECV_FRAME)) by exact (eq_trans (HP3 2 ltac:(hnf; lia)) C2).
assert (T3 : YK11.getr regs3 3 = YK11.getr regs 3) by exact (eq_trans (HP3 3 ltac:(hnf; lia)) C3).
assert (T4 : YK11.getr regs3 4 = YK11.getr regs 4) by exact (eq_trans (HP3 4 ltac:(hnf; lia)) C4).
assert (T8 : YK11.getr regs3 8 = w64 a) by exact (eq_trans (HP3 8 ltac:(hnf; lia)) C8).
assert (T9 : YK11.getr regs3 9 = Z_to_bv 64 6158224) by exact (eq_trans (HP3 9 ltac:(hnf; lia)) C9).
assert (T18 : YK11.getr regs3 18 = Z_to_bv 64 (recv_ticked pf)) by exact (eq_trans (HP3 18 ltac:(hnf; lia)) C18).
assert (T19 : YK11.getr regs3 19 = Z_to_bv 64 6236064) by exact (eq_trans (HP3 19 ltac:(hnf; lia)) C19).
assert (T21 : YK11.getr regs3 21 = YK11.getr regs 21) by exact (eq_trans (HP3 21 ltac:(hnf; lia)) C21).
assert (T22 : YK11.getr regs3 22 = YK11.getr regs 22) by exact (eq_trans (HP3 22 ltac:(hnf; lia)) C22).
assert (T23 : YK11.getr regs3 23 = YK11.getr regs 23) by exact (eq_trans (HP3 23 ltac:(hnf; lia)) C23).
assert (T24 : YK11.getr regs3 24 = YK11.getr regs 24) by exact (eq_trans (HP3 24 ltac:(hnf; lia)) C24).
assert (T25 : YK11.getr regs3 25 = YK11.getr regs 25) by exact (eq_trans (HP3 25 ltac:(hnf; lia)) C25).
assert (T26 : YK11.getr regs3 26 = YK11.getr regs 26) by exact (eq_trans (HP3 26 ltac:(hnf; lia)) C26).
assert (T27 : YK11.getr regs3 27 = YK11.getr regs 27) by exact (eq_trans (HP3 27 ltac:(hnf; lia)) C27).
(* what the call has kept up to diginet_session_poll's return *)
assert (ELF2 : ly_F ly2 = ly_F lyc).
{ pose proof HJ0 as (_ & _ & (memS0 & HJ0i & _) & _). pose proof HJ0i as (_ & Hlyc & _).
  pose proof HJ as (_ & _ & (memS2 & HJ2i & _) & _). pose proof HJ2i as (_ & Hly2 & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & E2 & _). pose proof Hlyc as (_ & _ & _ & _ & _ & Ec & _).
  rewrite E2, Ec. reflexivity. }
assert (K1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (ms_mem msC) (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 W2 (ms_mem msC) (spZ regs - RECV_STK)
    (spZ regs) (spZ regs) (spZ regs) (recv_wr bytes) (fun _ => False) Hce ltac:(lia) HK2); [| lia | lia | tauto].
  apply (bp_kept_run B lyc Sc W memc mdc W2 mem2 (ms_mem msC) (spZ regs) (fun _ => False) bp_Z5 LAWS HARc).
  - intros x Hx. exact (bp_Z5_G x Hx).
  - intros x Hx Hnz. exact (KR1 x Hx Hnz).
  - intros x Hx. exact (GA1 x Hx). }
assert (K2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 (ms_mem msC) W3 mem3
    (spZ regs - RECV_STK) (spZ regs) (spZ (ms_regs msC) - POLL_STK) (spZ (ms_regs msC)) (recv_wr bytes) poll_wr
    (fun _ => False) Hce ltac:(lia)).
  - intros c q. unfold frame_addr. rewrite ELF2. reflexivity.
  - intros f Hf. rewrite Hfrs. exact Hf.
  - intros bm Hbm. apply (Permutation_in _ (Permutation_sym Hperm)). right. exact Hbm.
  - intros b m i _ _ [].
  - intros cid q x _ _ [].
  - exact K1.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros x Hx. left. unfold recv_wr. do 10 right. exact Hx. }
clear HS SHOK HF HFr HG.
(* +0x120 .. +0x128: the two stores of 0, `j` to the set cut *)
rewrite C1. change (Z_to_bv 64 (BASE + 9512)) with (Z_to_bv 64 (BASE + BP_RP)).
pose proof (@bp_entryT fx rc W3 regs3 mem3 T9 T19) as HST.
assert (SHOKT : sh_ok segs (SLit 0) (@nil shent) (bp_E regs3 []) (mrestrict (w_H W3) mem3)) by constructor.
assert (HEIT : img_env VAL A_LIM (bp_E regs3 [])) by apply bp_env_img.
pose proof (bp_ureg regs3 [] 9 9%bv 6158224 eq_refl T9 ltac:(lia)) as V9'.
pose proof (bp_ureg regs3 [] 19 19%bv 6236064 eq_refl T19 ltac:(lia)) as V19.
paj_run_to_tok RUNTO HST HJ3 SHOKT (0, 0) RECV_SET.
{ bp_awr_rs.
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite V9' in Hx;
    apply (bp_inG_row _ _ _ x TMAP_B_g_rx); unfold TB_g_rx, TW.SZ_g_rx in *; lia |].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite V19 in Hx;
    apply (bp_inG_row _ _ _ x TMAP_B_g_rx_fail); unfold TB_g_rx_fail, TW.SZ_g_rx_fail in *; lia |].
  apply awr_ok_x_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdT := mdx) in *; clearbody mdT end.
lazymatch type of HST with context [restrict _ ?mf] => rename mf into msT end.
assert (KR2 : forall x, 0 <= x < 2 ^ 64 -> ~ bp_Z2 x -> aview segs (w_H W3) (ms_mem msT) x = aview segs (w_H W3) mem3 x).
{ intros x Hx Hnz. apply (kept_of_frame _ _ _ _ _ bp_Z2 HFr); [| exact Hx | exact Hnz].
  intros b wlo whi y Hin Hy. cbv beta.
  lazymatch type of Hin with In ?z ?l => let l' := eval vm_compute in l in change (In z l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hy;
    rewrite ?V9', ?V19 in Hy; unfold bp_Z2, TB_g_rx, TB_g_rx_fail in Hy |- *; lia |]).
  destruct Hin. }
assert (GA2 : forall x, apresent (w_H W3) mem3 x -> apresent (w_H W3) (ms_mem msT) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
let EF := bp_curE HST in
(assert (EV9 : bv_unsigned (ew EF 9) = 6158224) by (bp_ewv; exact V9');
 assert (EV19 : bv_unsigned (ew EF 19) = 6236064) by (bp_ewv; exact V19)).
bp_region HST 0%nat HT0. bp_region HST 1%nat HT1.
assert (VR2 : forall j, (j < 8)%nat -> aview segs (w_H W3) (ms_mem msT) (TB_g_rx + Z.of_nat j) =
  Some (YO0f.le_byte 0 8 j)).
{ intros j Hj. pose proof (bp_chunk_bytes _ (w_H W3) (ms_mem msT) (Some 9%nat) _ _ _ _ _ (-368) 8 _ 0 HT0
    ltac:(bp_in) ltac:(lia) ltac:(reflexivity) j Hj) as Hc.
  cbn [base_val] in Hc. rewrite EV9 in Hc.
  replace (6158224 + -368) with TB_g_rx in Hc by (unfold TB_g_rx; lia). exact Hc. }
assert (VF2 : forall j, (j < 4)%nat -> aview segs (w_H W3) (ms_mem msT) (TB_g_rx_fail + Z.of_nat j) =
  Some (YO0f.le_byte 0 4 j)).
{ intros j Hj. pose proof (bp_chunk_bytes _ (w_H W3) (ms_mem msT) (Some 19%nat) _ _ _ _ _ 1248 4 _ 0 HT1
    ltac:(bp_in) ltac:(lia) ltac:(reflexivity) j Hj) as Hc.
  cbn [base_val] in Hc. rewrite EV19 in Hc.
  replace (6236064 + 1248) with TB_g_rx_fail in Hc by (unfold TB_g_rx_fail; lia). exact Hc. }
clear HT0 HT1.
(* the world settle is handed *)
assert (HLB2 : length B2d = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw3).
assert (TWT : tw_at TMAP_B (aview segs (w_H W3) (ms_mem msT)) (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0)).
{ apply (bp_tw_w3 (aview segs (w_H W3) mem3) _ B2d Htw3 VR2 VF2).
  intros x Hx N1 N2. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KR2; [lia|]. unfold bp_Z2. tauto. }
assert (GFT : TW.g_fail_next (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0) <= 1)
  by (rewrite (AP.rp_gfn_w3 B2d HLB2); exact Hgf3).
pose proof (proj2 (proj2 (proj2 (proj2 INV))) Bw bytes a pf (Some (TI.TFrame a bytes)) B2d r HLB Hrinv HPM) as RINVT.
(* what every cut carries, at the set cut *)
assert (CURT : recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly3 S3 W3 (ms_mem msT) mdT).
{ refine (conj HJ3 (conj (eq_trans Hfr3 Hfrs) (conj (Permutation_trans Hperm3 Hperm) (conj _ (conj _ (conj _ Ha4096)))))).
  - rewrite <- (Z.add_0_r (mo_malloc MT (Z.max 1 (Z.of_nat (length bytes))))).
    exact (mo_le_trans MT MTL _ _ _ _ _ Hmo2 Hmo3).
  - apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 W3 (ms_mem msT) (spZ regs - RECV_STK) (spZ regs)
      (spZ regs) (spZ regs) (recv_wr bytes) (fun _ => False) Hce ltac:(lia) K2); [| lia | lia | tauto].
    apply (bp_kept_run B lyc Sc W memc mdc W3 mem3 (ms_mem msT) (spZ regs) (fun _ => False) bp_Z2 LAWS HARc).
    + intros x Hx. exact (bp_Z2_G x Hx).
    + intros x Hx Hnz. exact (KR2 x Hx Hnz).
    + intros x Hx. exact (GA2 x Hx).
  - rewrite Forall_forall in Hsv2 |- *. intros o Ho. rewrite <- (Hsv2 o Ho).
    assert (Hob : 8 <= fst o <= 48).
    { unfold RECV_SAVED in Ho. cbn [In] in Ho. repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
    apply rdword_ext. intros i Hi.
    pose proof (HK3) as (KK1 & _).
    rewrite KR2 by (try lia; intros HZ; destruct (bp_Z2_G _ HZ) as [Hl _]; lia).
    rewrite KK1 by (rewrite ?USPC; lia).
    rewrite KR1 by (try lia; intros HZ; destruct (bp_Z5_G _ HZ) as [Hl _]; lia).
    reflexivity. }
(* the registers at the set cut *)
pmkst HST.
bp_kreg HST regs3 (@nil word) 2%nat (2%bv : bv 5) (2%bv : bv 5) T2 Z2r.
bp_kreg HST regs3 (@nil word) 3%nat (3%bv : bv 5) (3%bv : bv 5) T3 Z3r.
bp_kreg HST regs3 (@nil word) 4%nat (4%bv : bv 5) (4%bv : bv 5) T4 Z4r.
bp_kreg HST regs3 (@nil word) 8%nat (8%bv : bv 5) (8%bv : bv 5) T8 Z8r.
bp_kreg HST regs3 (@nil word) 18%nat (18%bv : bv 5) (18%bv : bv 5) T18 Z18r.
bp_kreg HST regs3 (@nil word) 21%nat (21%bv : bv 5) (21%bv : bv 5) T21 Z21r.
bp_kreg HST regs3 (@nil word) 22%nat (22%bv : bv 5) (22%bv : bv 5) T22 Z22r.
bp_kreg HST regs3 (@nil word) 23%nat (23%bv : bv 5) (23%bv : bv 5) T23 Z23r.
bp_kreg HST regs3 (@nil word) 24%nat (24%bv : bv 5) (24%bv : bv 5) T24 Z24r.
bp_kreg HST regs3 (@nil word) 25%nat (25%bv : bv 5) (25%bv : bv 5) T25 Z25r.
bp_kreg HST regs3 (@nil word) 26%nat (26%bv : bv 5) (26%bv : bv 5) T26 Z26r.
bp_kreg HST regs3 (@nil word) 27%nat (27%bv : bv 5) (27%bv : bv 5) T27 Z27r.
assert (REGST : recv_regs_set regs (ms_regs msT) a (recv_ticked pf)).
{ refine (conj (conj Z2r (conj Z3r (conj Z4r (conj Z21r (conj Z22r (conj Z23r (conj Z24r (conj Z25r
    (conj Z26r Z27r))))))))) (conj Z8r Z18r)). }
exact (SET LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly3 S3
  W3 (ms_mem msT) mdT (ms_regs msT) (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0) (recv_ticked pf) HFIX CURT HRES TWT GFT
  RINVT HSM (bp_ticked_range pf) REGST).
Qed.

(* +0x0c4 .. +0x0d0: a2 = sp, a0 = a, a1 = got, `jal spec_read_frame` (recv_srf_at at len = got); its continuation
   is bp_ret at the return address. *)
Lemma bp_got : forall ly2 S2 (W2 : world segs) mem2 md2 regsG memG mdG,
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
  recv_blk W2 mem2 a bytes ->
  tw_at TMAP_B (aview segs (w_H W2) mem2) (recv_w2 Bw bytes) ->
  JX ly2 S2 W2 memG mdG ->
  (forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) memG x = aview segs (w_H W2) mem2 x) ->
  (forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) memG x) ->
  bp_regs regs regsG a (recv_got bytes) ->
  SRr segs W2 (CFG BP_GOT regsG memG mdG) POST.
Proof.
intros ly2 S2 W2 mem2 md2 regsG memG mdG HCUR HBLK HTW HJ KV GV HREGS.
pose proof LAWS0 as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
pose proof HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hch & Hal & Hwlo & Hwhi & Hbp & Hpf &
  Hn & _).
pose proof HRES as ((Ha0 & Ha64) & HM).
pose proof HREGS as ((G2 & G3 & G4 & G21 & G22 & G23 & G24 & G25 & G26 & G27) & G8 & G9 & G18 & G20).
pose proof (bp_got_range bytes) as (Rg1 & Rg2 & Rg3 & Rg4).
destruct bp_vals as (_ & _ & _ & _ & _ & VB).
pose proof (@bp_entry0 fx rc W2 regsG memG BP_GOT) as HS.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) (bp_E regsG []) (mrestrict (w_H W2) memG)) by constructor.
assert (HEI : img_env VAL A_LIM (bp_E regsG [])) by apply bp_env_img.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
paj_run_tok RUN HS HJ SHOK (0, 0).
{ bp_awr0. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in *; clearbody md1 end.
bp_kv HS W2 mem2 KV GV.
lazymatch type of HS with context [restrict _ ?mf] => rename mf into msG end.
(* the registers at the call *)
bp_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 9436)) C1 ltac:(apply codeptr_val; assumption).
bp_kreg HS regsG (@nil word) 8%nat (8%bv : bv 5) (10%bv : bv 5) G8 C10.
bp_kreg HS regsG (@nil word) 9%nat (9%bv : bv 5) (11%bv : bv 5) G9 C11.
bp_kreg HS regsG (@nil word) 2%nat (2%bv : bv 5) (12%bv : bv 5) G2 C12.
bp_kreg HS regsG (@nil word) 2%nat (2%bv : bv 5) (2%bv : bv 5) G2 C2.
bp_kreg HS regsG (@nil word) 3%nat (3%bv : bv 5) (3%bv : bv 5) G3 C3.
bp_kreg HS regsG (@nil word) 4%nat (4%bv : bv 5) (4%bv : bv 5) G4 C4.
bp_kreg HS regsG (@nil word) 8%nat (8%bv : bv 5) (8%bv : bv 5) G8 C8.
bp_kreg HS regsG (@nil word) 9%nat (9%bv : bv 5) (9%bv : bv 5) G9 C9.
bp_kreg HS regsG (@nil word) 18%nat (18%bv : bv 5) (18%bv : bv 5) G18 C18.
bp_kreg HS regsG (@nil word) 20%nat (20%bv : bv 5) (20%bv : bv 5) G20 C20.
bp_kreg HS regsG (@nil word) 21%nat (21%bv : bv 5) (21%bv : bv 5) G21 C21.
bp_kreg HS regsG (@nil word) 22%nat (22%bv : bv 5) (22%bv : bv 5) G22 C22.
bp_kreg HS regsG (@nil word) 23%nat (23%bv : bv 5) (23%bv : bv 5) G23 C23.
bp_kreg HS regsG (@nil word) 24%nat (24%bv : bv 5) (24%bv : bv 5) G24 C24.
bp_kreg HS regsG (@nil word) 25%nat (25%bv : bv 5) (25%bv : bv 5) G25 C25.
bp_kreg HS regsG (@nil word) 26%nat (26%bv : bv 5) (26%bv : bv 5) G26 C26.
bp_kreg HS regsG (@nil word) 27%nat (27%bv : bv 5) (27%bv : bv 5) G27 C27.
assert (KEEP : recv_regs_keep regs (ms_regs msG))
  by exact (conj C2 (conj C3 (conj C4 (conj C21 (conj C22 (conj C23 (conj C24 (conj C25 (conj C26 C27))))))))).
assert (KX : bp_regs regs (ms_regs msG) a (recv_got bytes)) by exact (conj KEEP (conj C8 (conj C9 (conj C18 C20)))).
(* the cut's facts at the call memory *)
assert (CURc : recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 (ms_mem msG) md1)
  by exact (bp_cur_view ly2 S2 W2 mem2 md2 (ms_mem msG) md1 HCUR HJ KV GV).
assert (BLKc : recv_blk W2 (ms_mem msG) a bytes)
  by exact (bp_blk_view W2 mem2 (ms_mem msG) a bytes HBLK ltac:(lia) ltac:(lia) KV).
assert (TWc : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msG)) (recv_w2 Bw bytes))
  by exact (bp_tw_view W2 mem2 (ms_mem msG) _ HTW KV).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_spec_read_frame) rg mm mdx) Q) end.
refine (SRF LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a
  ly2 S2 W2 (ms_mem msG) md1 (ms_regs msG) (recv_got bytes) (recv_w2 Bw bytes) POST HFIX CURc BLKc TWc KEEP
  _ _ C10 C11 C12 ltac:(lia) _).
- rewrite C1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
- unfold raZ. rewrite C1, VB. rewrite unsigned_lit_small by lia. lia.
- intros ly3 S3 W3 mem3 md3 regs3 HCUR3 HBLK3 HTW3 HP3 HSF3.
  rewrite C1. change (Z_to_bv 64 (BASE + 9436)) with (Z_to_bv 64 (BASE + BP_RS)).
  exact (bp_ret ly3 S3 W3 mem3 md3 regs3 HCUR3 HBLK3 HTW3 HSF3 (bp_regs_pres _ _ _ _ _ KX HP3)).
Qed.

(* +0x0b8 .. +0x0c0: got = min (n, 1514) in s1. *)
Lemma bp_main : forall ly2 S2 (W2 : world segs) mem2 md2 regs2,
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
  recv_blk W2 mem2 a bytes ->
  tw_at TMAP_B (aview segs (w_H W2) mem2) (recv_w2 Bw bytes) ->
  recv_regs_poll regs regs2 a bytes ->
  SRr segs W2 (CFG RECV_POLL regs2 mem2 md2) POST.
Proof.
intros ly2 S2 W2 mem2 md2 regs2 HCUR HBLK HTW HREGS.
pose proof LAWS0 as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
pose proof HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hch & Hal & Hwlo & Hwhi & Hbp & Hpf &
  Hn & _).
pose proof HREGS as ((R2 & R3 & R4 & R21 & R22 & R23 & R24 & R25 & R26 & R27) & R8 & R9 & R18 & R20).
pose proof HCUR as (HJ & _).
pose proof (bp_got_range bytes) as (Rg1 & Rg2 & Rg3 & Rg4).
pose proof (@bp_entryP fx rc W2 regs2 mem2 (Z.of_nat (length bytes)) R9 ltac:(lia)) as HS.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) (bp_E regs2 []) (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI : img_env VAL A_LIM (bp_E regs2 [])) by apply bp_env_img.
assert (A9 : ew (bp_E regs2 []) 9 = w64 (Z.of_nat (length bytes)))
  by exact (eq_trans (bp_ew regs2 [] 9 9%bv eq_refl) R9).
assert (KV : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) mem2 x = aview segs (w_H W2) mem2 x)
  by reflexivity.
assert (GV : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) mem2 x) by (intros x Hx; exact Hx).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
paj_run_to_tok RUNTO HS HJ SHOK (0, 0) BP_GOT; [bp_awr0 |].
bp_md. bp_kv HS W2 mem2 KV GV.
psrr_branch_tok RUN BR HS SHOK (0, 0);
  (let EF := bp_curE HS in
   rewrite (bp_br_ltu EF 9 (Z.of_nat (length bytes)) 1514 ltac:(bp_ewv; exact A9) ltac:(lia) ltac:(lia)) in Hc).
1: { apply Z.ltb_lt in Hc.
     paj_run_to_tok RUNTO HS HJ SHOK (0, 0) BP_GOT; [bp_awr0 |].
     bp_md. bp_kv HS W2 mem2 KV GV. pmkst HS.
     bp_reg HS (9%bv : bv 5) (w64 (recv_got bytes)) G9
       ltac:(rewrite (Rg3 Hc); lazymatch goal with |- sv_denot ?EF _ = _ =>
               exact (AP.rp_den_lit EF 9 _ ltac:(bp_ewv; exact A9) ltac:(lia)) end).
     bp_kreg HS regs2 (@nil word) 2%nat (2%bv : bv 5) (2%bv : bv 5) R2 G2.
     bp_kreg HS regs2 (@nil word) 3%nat (3%bv : bv 5) (3%bv : bv 5) R3 G3.
     bp_kreg HS regs2 (@nil word) 4%nat (4%bv : bv 5) (4%bv : bv 5) R4 G4.
     bp_kreg HS regs2 (@nil word) 8%nat (8%bv : bv 5) (8%bv : bv 5) R8 G8.
     bp_kreg HS regs2 (@nil word) 18%nat (18%bv : bv 5) (18%bv : bv 5) R18 G18.
     bp_kreg HS regs2 (@nil word) 20%nat (20%bv : bv 5) (20%bv : bv 5) R20 G20.
     bp_kreg HS regs2 (@nil word) 21%nat (21%bv : bv 5) (21%bv : bv 5) R21 G21.
     bp_kreg HS regs2 (@nil word) 22%nat (22%bv : bv 5) (22%bv : bv 5) R22 G22.
     bp_kreg HS regs2 (@nil word) 23%nat (23%bv : bv 5) (23%bv : bv 5) R23 G23.
     bp_kreg HS regs2 (@nil word) 24%nat (24%bv : bv 5) (24%bv : bv 5) R24 G24.
     bp_kreg HS regs2 (@nil word) 25%nat (25%bv : bv 5) (25%bv : bv 5) R25 G25.
     bp_kreg HS regs2 (@nil word) 26%nat (26%bv : bv 5) (26%bv : bv 5) R26 G26.
     bp_kreg HS regs2 (@nil word) 27%nat (27%bv : bv 5) (27%bv : bv 5) R27 G27.
     exact (bp_got _ _ _ _ _ _ _ _ HCUR HBLK HTW HJ KV GV
       (conj (conj G2 (conj G3 (conj G4 (conj G21 (conj G22 (conj G23 (conj G24 (conj G25 (conj G26 G27)))))))))
         (conj G8 (conj G9 (conj G18 G20))))). }
apply Z.ltb_ge in Hc.
(* +0x0c0: s1 = 1514 *)
paj_run_to_tok RUNTO HS HJ SHOK (0, 0) BP_GOT; [bp_awr0 |].
bp_md. bp_kv HS W2 mem2 KV GV. pmkst HS.
bp_reg HS (9%bv : bv 5) (w64 (recv_got bytes)) G9 ltac:(rewrite (Rg4 Hc); reflexivity).
bp_kreg HS regs2 (@nil word) 2%nat (2%bv : bv 5) (2%bv : bv 5) R2 G2.
bp_kreg HS regs2 (@nil word) 3%nat (3%bv : bv 5) (3%bv : bv 5) R3 G3.
bp_kreg HS regs2 (@nil word) 4%nat (4%bv : bv 5) (4%bv : bv 5) R4 G4.
bp_kreg HS regs2 (@nil word) 8%nat (8%bv : bv 5) (8%bv : bv 5) R8 G8.
bp_kreg HS regs2 (@nil word) 18%nat (18%bv : bv 5) (18%bv : bv 5) R18 G18.
bp_kreg HS regs2 (@nil word) 20%nat (20%bv : bv 5) (20%bv : bv 5) R20 G20.
bp_kreg HS regs2 (@nil word) 21%nat (21%bv : bv 5) (21%bv : bv 5) R21 G21.
bp_kreg HS regs2 (@nil word) 22%nat (22%bv : bv 5) (22%bv : bv 5) R22 G22.
bp_kreg HS regs2 (@nil word) 23%nat (23%bv : bv 5) (23%bv : bv 5) R23 G23.
bp_kreg HS regs2 (@nil word) 24%nat (24%bv : bv 5) (24%bv : bv 5) R24 G24.
bp_kreg HS regs2 (@nil word) 25%nat (25%bv : bv 5) (25%bv : bv 5) R25 G25.
bp_kreg HS regs2 (@nil word) 26%nat (26%bv : bv 5) (26%bv : bv 5) R26 G26.
bp_kreg HS regs2 (@nil word) 27%nat (27%bv : bv 5) (27%bv : bv 5) R27 G27.
exact (bp_got _ _ _ _ _ _ _ _ HCUR HBLK HTW HJ KV GV
  (conj (conj G2 (conj G3 (conj G4 (conj G21 (conj G22 (conj G23 (conj G24 (conj G25 (conj G26 G27)))))))))
    (conj G8 (conj G9 (conj G18 G20))))).
Qed.
End m.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma recv_poll : @recv_poll_stmt fx rc B MT.
Proof.
  intros SRF INV SET LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a
    Bw' ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HRES HBLK HTW HBP HREGS.
  exact (bp_main B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' LAWS0
    CALLS SRF INV SET HFIX HRES HBP ly2 S2 W2 mem2 md2 regs2 HCUR HBLK HTW HREGS).
Qed.
End s.
