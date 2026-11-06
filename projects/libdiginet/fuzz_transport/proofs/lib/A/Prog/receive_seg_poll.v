(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 1426 of its 1534 lines of code are new or changed and 451 lines of the source are left out. *)
(* receive (image A, ASan build), the by-poll piece: the poll cut (+0x14c, receive_seg_cut.v recv_poll_at) from the
   invariants piece (recv_inv_stmt) and the set cut (recv_set_at). Each phase restarts from a symbolic state built
   from the concrete registers (rp_entry0, rp_entryG, rp_entryF, rp_entryS, rp_entryT) and runs with the image-A
   engine (TransportGRunA.v paj_run_x / paj_run_to_x, DgnTransportPaLib.v paj_branch).

   +0x14c .. +0x158 (rp_main): a1 = got = min (n, 1514) (receive_cg.v recv_got): a run to `bltu s2, a0` (+0x154), the
     branch on n < 1514 (rp_br_n), a run to +0x15c on each side.
   +0x15c .. +0x160 (rp_atG): `bltu s2, a0` on n < 30: taken, +0x1f0 sets a0 = 0 (rp_snd_lt30); else +0x164.
   +0x164 .. +0x1ec and +0x320 .. +0x398 (rp_atF): the state holds the frame's bytes 12 .. 15 and 18 .. 21 as atoms
     (rp_entryF: the block's bytes at the cut, decode_rd_ok by DgnTransportCg.v trans_src_ok_rd, the shadow entry of
     the first 30 bytes by YCbq.v shent_ok_of_range), so the shadow token decides each checked load; the branches
     `bne` (the ethertype, rp_br_et), `bltu` (numbytes < 16, rp_br_nb) and `bgeu` (got - 14 >= numbytes, rp_br_len)
     give a0 = the send value of the first got bytes (plain receive.v rb_snd_gb as rp_send_got; rp_snd_et,
     rp_snd_nb, rp_snd_big, rp_snd_ok); on the last path +0x320 .. +0x398 form its big-endian value (rp_den_be32).
   +0x1f4 .. +0x238 (rp_send): a3 = (pf & 1) + 1 and s1 = ((s1 << 62) >> 63) xor 1 (plain receive.v r_twice,
     r_fails; rp_den_times, rp_den_fails, rp_den_ticked); the stores of g_rx_send, g_rx_len, g_rx, g_rx_times and
     g_rx_fail (their bytes by rp_chunk_bytes, the world recv_w2c by rp_tw_w2c over TWorldG.v tw_write); a0 = &g_s,
     a1 = 0; the call of diginet_session_poll by recv_calls' transport_diginet_session_poll_cg at
     TF = Some (TFrame a bytes), w = 0: the model by rp_model (receive_cg.v recv_model, recv_some_inv_u);
     trans_tframe_at by the block in the current ablocks below alloc_ceiling; trans_tf_off_g and poll_apart by YCbq.v
     blk_img and rp_poll_wr_G; trans_rom_view_rd by rp_rom (acall_kept_g's image clause); iorecv_rx_in by rp_grx_w2c
     and TCb.v frame_from_base; the invariants by recv_inv_stmt's second clause; poll_rx_each by recv_fix's
     recv_dn_each.
   The callee's transport_cg_post: e = 0; frames, Permutation and mo_le_trans; acall_kept_g by TransportGCg.v
     dk_kept_trans_g over the store runs (rp_kept_run) and dk_kept_trans_nf_g over the callee (poll_wr is in
     recv_wr); the saved words lie above the callee's window.
   +0x23c .. +0x244: the two stores of 0 (the world TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0 by rp_tw_w3), `j` to the
     set cut, and recv_set_at there with ticked = recv_ticked pf (the invariants by recv_inv_stmt's fifth clause,
     g_fail_next by rp_gfn_w3, settle_m by rp_model). *)

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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AE2y AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_inflight_settle_cg check_latest_queue_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import settle_cg diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import receive_cg receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require receive m_rx_epi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module PR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.receive.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The pcs and the symbolic states                                  *)
(* ------------------------------------------------------------------ *)

(* +0x15c (got in a1), +0x164 (n >= 30, the frame's tests), +0x1f4 (the send value in a0), +0x23c (poll's return). *)
Definition RP_GOT : Z := AF_receive + 0x15c.
Definition RP_F : Z := AF_receive + 0x164.
Definition RP_SEND : Z := AF_receive + 0x1f4.
Definition RP_RET : Z := AF_receive + 0x23c.

(* +0x14c: s2 = n (atom 18) below 2 ^ 16; the run stops at `bltu s2, a0` (+0x154). *)
Definition rp_facts0 : facts := mkFacts [(18%nat, mkAF 0 65535 0)] [] [].
Definition ss_rp0 : sstate := mkSS RECV_POLL sr_atoms [] None rp_facts0.
(* +0x15c: a1 = got (atom 11); the run stops at `bltu s2, a0` (+0x160, n < 30). *)
Definition rp_factsG : facts := mkFacts [(18%nat, mkAF 0 65535 0); (11%nat, mkAF 0 1514 0)] [] [].
Definition ss_rpG : sstate := mkSS RP_GOT sr_atoms [] None rp_factsG.
(* +0x164: the frame's bytes 12 .. 15 and 18 .. 21 as atoms 32 .. 39 (read only), s0 = a (atom 8), s5 = the shadow
   base (atom 21); the shadow entry of the frame's first 30 bytes. *)
Definition rp_frame : YP09.region := YP09.mkRegion (Some 8%nat) 12 22 0 0
  [YP09.mkChunk 12 (CVal 1 (SOff 32 0)); YP09.mkChunk 13 (CVal 1 (SOff 33 0));
   YP09.mkChunk 14 (CVal 1 (SOff 34 0)); YP09.mkChunk 15 (CVal 1 (SOff 35 0));
   YP09.mkChunk 18 (CVal 1 (SOff 36 0)); YP09.mkChunk 19 (CVal 1 (SOff 37 0));
   YP09.mkChunk 20 (CVal 1 (SOff 38 0)); YP09.mkChunk 21 (CVal 1 (SOff 39 0))].
Definition rp_factsF : facts :=
  mkFacts [(8%nat, mkAF 4096 (2 ^ 47 - 31) 0); (11%nat, mkAF 30 1514 0); (18%nat, mkAF 30 65535 0);
           (21%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
           (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0)] [] [].
Definition ss_rpF : sstate := mkSS RP_F sr_atoms [rp_frame] None rp_factsF.
Definition RP_SHF : list shent := [mkSHE 8 0 30].
Definition RP_BX : sv := SOff 21 0.
(* The empty shadow-token span, for the runs with no instrumented access. *)
Definition RP_B0 : Z * Z := (0, 0).
(* +0x1f4: the five stores of g_rx_send (at a2 = atom 12 - 0x530), g_rx_len, g_rx, g_rx_times, g_rx_fail (at the auipc
   values of the pairs 85, 84, 86, 87). *)
Definition rp_snd : YP09.region := YP09.mkRegion (Some 12%nat) (-0x530) (-0x52c) (-0x530) (-0x52c) [].
Definition rp_len : YP09.region := YP09.mkRegion (Some (A_HI 85)) 0x66c 0x674 0x66c 0x674 [].
Definition rp_rx : YP09.region := YP09.mkRegion (Some (A_HI 84)) (-0x30) (-0x28) (-0x30) (-0x28) [].
Definition rp_tm : YP09.region := YP09.mkRegion (Some (A_HI 86)) 0x648 0x64c 0x648 0x64c [].
Definition rp_fl : YP09.region := YP09.mkRegion (Some (A_HI 87)) 0x620 0x624 0x620 0x624 [].
Definition rp_factsS : facts :=
  mkFacts [(12%nat, mkAF RECV_RXS_HI RECV_RXS_HI 4); (A_HI 84, mkAF 6158800 6158800 4);
           (A_HI 85, mkAF 6236628 6236628 2); (A_HI 86, mkAF 6236632 6236632 3);
           (A_HI 87, mkAF 6236640 6236640 5)] [] [].
Definition ss_rpS : sstate := mkSS RP_SEND sr_atoms [rp_snd; rp_len; rp_rx; rp_tm; rp_fl] None rp_factsS.
(* +0x23c: the stores of 0 at s2 - 0x30 (g_rx) and s3 + 0x620 (g_rx_fail); s2, s3 kept by the callee. *)
Definition rp_rx2 : YP09.region := YP09.mkRegion (Some 18%nat) (-0x30) (-0x28) (-0x30) (-0x28) [].
Definition rp_fl2 : YP09.region := YP09.mkRegion (Some 19%nat) 0x620 0x624 0x620 0x624 [].
Definition rp_factsT : facts := mkFacts [(18%nat, mkAF 6158800 6158800 4); (19%nat, mkAF 6236640 6236640 5)] [] [].
Definition ss_rpT : sstate := mkSS RP_RET sr_atoms [rp_rx2; rp_fl2] None rp_factsT.

(* ------------------------------------------------------------------ *)
(* 2. The model                                                        *)
(* ------------------------------------------------------------------ *)

Lemma rp_send_eq : forall b, recv_send b = PR.rb_snd b.
Proof. intros b. reflexivity. Qed.
Lemma rp_got_range : forall bytes,
  0 <= recv_got bytes <= 1514 /\ recv_got bytes <= Z.of_nat (length bytes) /\
  (Z.of_nat (length bytes) < 1514 -> recv_got bytes = Z.of_nat (length bytes)) /\
  (1514 <= Z.of_nat (length bytes) -> recv_got bytes = 1514).
Proof.
  intros bytes. unfold recv_got, TC.SPEC_MAX_FRAME.
  destruct (Z.ltb_spec 1514 (Z.of_nat (length bytes))); lia.
Qed.
(* The send value of the first got bytes, as the code tests it (plain receive.v rb_snd_gb). *)
Lemma rp_send_got : forall bytes,
  recv_send (firstn (Z.to_nat (recv_got bytes)) bytes) =
  if Z.of_nat (length bytes) <? 30 then 0 else if negb (DSpec.be16 bytes 12 =? 34911) then 0
  else if (DSpec.be16 bytes 14 <? 16) || (recv_got bytes - 14 <? DSpec.be16 bytes 14) then 0
  else DSpec.be32 bytes 18.
Proof. intros bytes. rewrite rp_send_eq. exact (PR.rb_snd_gb bytes (recv_got bytes) eq_refl). Qed.
Lemma rp_be16 : forall l i, DSpec.be16 l i = DSpec.at8 l i * 2 ^ 8 + DSpec.at8 l (S i).
Proof. intros l i. reflexivity. Qed.
Lemma rp_be32 : forall l i, DSpec.be32 l i =
  DSpec.at8 l i * 2 ^ 24 + DSpec.at8 l (S i) * 2 ^ 16 + DSpec.at8 l (S (S i)) * 2 ^ 8 + DSpec.at8 l (S (S (S i))).
Proof. intros l i. reflexivity. Qed.
Lemma rp_at8_range : forall l i, 0 <= DSpec.at8 l i < 256.
Proof.
  intros l i. unfold DSpec.at8, DSpec.bz. pose proof (bv_unsigned_in_range 8 (nth i l (DSpec.b8 0))) as H.
  unfold bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.
Lemma rp_send_range : forall bytes, 0 <= recv_send (firstn (Z.to_nat (recv_got bytes)) bytes) < 2 ^ 32.
Proof.
  intros bytes. rewrite rp_send_got.
  destruct (Z.of_nat (length bytes) <? 30); [lia|].
  destruct (negb (DSpec.be16 bytes 12 =? 34911)); [lia|].
  destruct ((DSpec.be16 bytes 14 <? 16) || (recv_got bytes - 14 <? DSpec.be16 bytes 14))%bool; [lia|].
  rewrite rp_be32.
  pose proof (rp_at8_range bytes 18). pose proof (rp_at8_range bytes 19).
  pose proof (rp_at8_range bytes 20). pose proof (rp_at8_range bytes 21). lia.
Qed.

(* The poll flags (plain receive.v r_twice, r_fails, r_ticked). *)
Lemma rp_land1 : forall x, Z.land x 1 = 0 \/ Z.land x 1 = 1.
Proof. exact PR.r_land1. Qed.
Lemma rp_ticked_eq : forall pf, Z.lxor (Z.land (Z.shiftr pf 1) 1) 1 = recv_ticked pf.
Proof.
  intros pf. unfold recv_ticked. destruct (rp_land1 (Z.shiftr pf 1)) as [E|E]; rewrite E; reflexivity.
Qed.
Lemma rp_ticked_range : forall pf, 0 <= recv_ticked pf <= 1.
Proof. intros pf. unfold recv_ticked. destruct (Z.land (Z.shiftr pf 1) 1 =? 0); lia. Qed.
Lemma rp_times_eq : forall pf, Z.land pf 1 + 1 = (if Z.land pf 1 =? 0 then 1 else 2).
Proof. intros pf. destruct (rp_land1 pf) as [E|E]; rewrite E; reflexivity. Qed.

(* The model at the address the malloc returned, on the by-poll path. *)
Lemma rp_model : forall Bw a bytes by_poll pf Bw', a <> 0 -> by_poll <> 0 ->
  TOP.receive_m timg_A Bw a bytes by_poll pf = Some (Bw', tt) ->
  exists B2d r, TSS.diginet_session_poll_m timg_A (Some (TI.TFrame a bytes)) (recv_w2c Bw bytes a pf) 0 = Some (B2d, r) /\
    TC.settle_m (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0) (recv_ticked pf) = Some (Bw', tt).
Proof.
  intros Bw a bytes by_poll pf Bw' Ha Hb HM. rewrite recv_model in HM.
  rewrite (proj2 (Z.eqb_neq a 0) Ha), (proj2 (Z.eqb_neq by_poll 0) Hb) in HM.
  (* each scrutinee that is a model call is destructed before HM is reduced, so that the kernel never reduces a
     match on a model call *)
  destruct (TSS.diginet_session_poll_m timg_A (Some (TI.TFrame a bytes)) (recv_w2c Bw bytes a pf) 0)
    as [[B2d r]|] eqn:EP; cbv beta iota delta [negb] in HM; [|discriminate HM].
  exists B2d, r. split; [reflexivity|].
  destruct (TC.settle_m (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0) (recv_ticked pf)) as [[B4 []]|] eqn:ES;
    cbv beta iota in HM; [|discriminate HM].
  rewrite (recv_some_inv_u B4 Bw' HM). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The worlds                                                       *)
(* ------------------------------------------------------------------ *)

Lemma rp_len_upd : forall X k v, Z.of_nat (length X) = TW.W_LEN -> 0 <= k -> k + Z.of_nat (length v) <= TW.W_LEN ->
  Z.of_nat (length (TW.upd X k v)) = TW.W_LEN.
Proof. intros X k v HL Hk Hv. rewrite TWL.length_upd by lia. exact HL. Qed.
Lemma rp_gfn_upd : forall X k v, Z.of_nat (length X) = TW.W_LEN -> 0 <= k -> k + Z.of_nat (length v) <= TW.W_LEN ->
  (k + Z.of_nat (length v) <= TW.OFF_g_fail_next \/ TW.OFF_g_fail_next + 1 <= k) ->
  TW.g_fail_next (TW.upd X k v) = TW.g_fail_next X.
Proof.
  intros X k v HL Hk Hv Hd. unfold TW.g_fail_next.
  apply TWL.u_at_upd_out; [exact Hk | unfold TW.OFF_g_fail_next; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia].
Qed.
Lemma rp_grx_upd : forall X k v, Z.of_nat (length X) = TW.W_LEN -> 0 <= k -> k + Z.of_nat (length v) <= TW.W_LEN ->
  (k + Z.of_nat (length v) <= TW.OFF_g_rx \/ TW.OFF_g_rx + 8 <= k) ->
  TW.g_rx (TW.upd X k v) = TW.g_rx X.
Proof.
  intros X k v HL Hk Hv Hd. unfold TW.g_rx.
  apply TWL.u_at_upd_out; [exact Hk | unfold TW.OFF_g_rx; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia].
Qed.

Ltac rp_lenv := rewrite ?TWL.length_put, ?repeat_length;
  unfold TW.A_OW_desk_off, TW.A_M_fail, TW.OFF_OW, TW.OFF_GOT, TW.SZ_OW, TW.SZ_GOT, TW.OFF_M, TW.OFF_g_rx_send,
    TW.OFF_g_rx, TW.OFF_g_rx_len, TW.OFF_g_rx_times, TW.OFF_g_rx_fail, TW.W_LEN, TW.OFF_g_fail_next; lia.
Ltac rp_len HL := repeat (apply rp_len_upd; [| rp_lenv | rp_lenv]); exact HL.

Lemma rp_w2c_eq : forall Bw bytes a pf,
  recv_w2c Bw bytes a pf =
  TW.set_g_rx_fail (TW.set_g_rx_times (TW.set_g_rx_len (TW.set_g_rx (TW.set_g_rx_send (TW.set_g_rx_send
    (TW.set_M_fail (TW.set_OW_desk_off (TW.upd (TW.upd Bw TW.OFF_OW (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_OW)))
         TW.OFF_GOT (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_GOT))) (-1))
       (TW.g_fail_next (TW.set_OW_desk_off (TW.upd (TW.upd Bw TW.OFF_OW (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_OW)))
         TW.OFF_GOT (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_GOT))) (-1))))
    (recv_send bytes)) (recv_send (firstn (Z.to_nat (recv_got bytes)) bytes))) a) (recv_got bytes))
    (if Z.land pf 1 =? 0 then 1 else 2)) (Z.land (Z.shiftr pf 1) 1).
Proof. intros. reflexivity. Qed.

(* The code stores no byte of g_fail_next, and op_begin_m keeps it. *)
Lemma rp_gfn_w2c : forall Bw bytes a pf, length Bw = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (recv_w2c Bw bytes a pf) = TW.g_fail_next Bw.
Proof.
  intros Bw bytes a pf HL0.
  assert (HL : Z.of_nat (length Bw) = TW.W_LEN) by (rewrite HL0; unfold TW.W_LEN; lia).
  rewrite rp_w2c_eq.
  unfold TW.set_g_rx_fail, TW.set_g_rx_times, TW.set_g_rx_len, TW.set_g_rx, TW.set_g_rx_send, TW.set_M_fail,
    TW.set_OW_desk_off.
  repeat (rewrite rp_gfn_upd; [| rp_len HL | rp_lenv | rp_lenv | rp_lenv]).
  reflexivity.
Qed.
Lemma rp_grx_w2c : forall Bw bytes a pf, length Bw = Z.to_nat TW.W_LEN -> 0 <= a < 2 ^ 64 ->
  TW.g_rx (recv_w2c Bw bytes a pf) = a.
Proof.
  intros Bw bytes a pf HL0 Ha.
  assert (HL : Z.of_nat (length Bw) = TW.W_LEN) by (rewrite HL0; unfold TW.W_LEN; lia).
  rewrite rp_w2c_eq. unfold TW.set_g_rx_fail, TW.set_g_rx_times, TW.set_g_rx_len.
  repeat (rewrite rp_grx_upd; [| rp_len HL | rp_lenv | rp_lenv | rp_lenv]).
  unfold TW.g_rx, TW.set_g_rx. rewrite TWL.u_at_upd_put; [| unfold TW.OFF_g_rx; lia |].
  - change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). apply Z.mod_small. exact Ha.
  - unfold TW.set_g_rx_send, TW.set_M_fail, TW.set_OW_desk_off.
    match goal with |- _ <= Z.of_nat (length ?X) =>
      assert (LX : Z.of_nat (length X) = TW.W_LEN) by rp_len HL; rewrite LX end.
    unfold TW.OFF_g_rx, TW.W_LEN. lia.
Qed.
Lemma rp_gfn_w3 : forall B2d, length B2d = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0) = TW.g_fail_next B2d.
Proof.
  intros B2d HL0.
  assert (HL : Z.of_nat (length B2d) = TW.W_LEN) by (rewrite HL0; unfold TW.W_LEN; lia).
  unfold TW.set_g_rx_fail, TW.set_g_rx.
  repeat (rewrite rp_gfn_upd; [| rp_len HL | rp_lenv | rp_lenv | rp_lenv]).
  reflexivity.
Qed.

(* A boolean range test. *)
Definition inb (lo hi x : Z) : bool := ((lo <=? x) && (x <? hi))%bool.
Lemma inb_false : forall lo hi x, x < lo \/ hi <= x -> inb lo hi x = false.
Proof. intros lo hi x H. unfold inb. destruct (Z.leb_spec lo x), (Z.ltb_spec x hi); cbn; lia || reflexivity. Qed.
Lemma inb_true : forall lo hi x, lo <= x < hi -> inb lo hi x = true.
Proof. intros lo hi x H. unfold inb. destruct (Z.leb_spec lo x), (Z.ltb_spec x hi); cbn; lia || reflexivity. Qed.
Lemma inb_false_iff : forall lo hi x, inb lo hi x = false -> ~ (lo <= x < hi).
Proof. intros lo hi x H Hx. rewrite (inb_true lo hi x Hx) in H. discriminate H. Qed.

(* One store of m bytes of v into a row, from the view that is rd at the bytes Pre names and rdF elsewhere. *)
Lemma rp_tw_step : forall (rd rdF : Z -> option Z) (Pre Post : Z -> bool) X o b n k (m : nat) v,
  In (o, b, n) TMAP_A -> 0 <= k -> k + Z.of_nat m <= n ->
  tw_at TMAP_A (fun x => if Pre x then rd x else rdF x) X ->
  (forall j, (j < m)%nat -> Post (b + k + Z.of_nat j) = false) ->
  (forall j, (j < m)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  (forall x, tw_in TMAP_A x -> ~ (b + k <= x < b + k + Z.of_nat m) -> Post x = Pre x) ->
  tw_at TMAP_A (fun x => if Post x then rd x else rdF x) (TW.upd X (o + k) (TW.put m v)).
Proof.
  intros rd rdF Pre Post X o b n k m v Hin Hk Hkm HX HP HV HO.
  apply (tw_write TMAP_A _ _ X o b n k m v TMAP_A_ok HX Hin Hk Hkm).
  - intros j Hj. cbv beta. rewrite (HP j Hj). exact (HV j Hj).
  - intros x Hx Hn. cbv beta. rewrite (HO x Hx Hn). reflexivity.
Qed.

Ltac rp_inb := repeat first [rewrite inb_false by (unfold TA_g_rx_send, TA_g_rx, TA_g_rx_len, TA_g_rx_times, TA_g_rx_fail in *; lia)
  | rewrite inb_true by (unfold TA_g_rx_send, TA_g_rx, TA_g_rx_len, TA_g_rx_times, TA_g_rx_fail in *; lia)];
  cbn [orb].

(* The four by-poll stores and g_rx_send's (in any order of the code): the world handed to diginet_session_poll. *)
Lemma rp_tw_w2c : forall (rd rd' : Z -> option Z) Bw bytes a pf sv got t f,
  sv = recv_send (firstn (Z.to_nat (recv_got bytes)) bytes) -> got = recv_got bytes ->
  t = (if Z.land pf 1 =? 0 then 1 else 2) -> f = Z.land (Z.shiftr pf 1) 1 ->
  tw_at TMAP_A rd (recv_w2 Bw bytes) ->
  (forall j, (j < 4)%nat -> rd' (TA_g_rx_send + Z.of_nat j) = Some (YO0f.le_byte sv 4 j)) ->
  (forall j, (j < 8)%nat -> rd' (TA_g_rx + Z.of_nat j) = Some (YO0f.le_byte a 8 j)) ->
  (forall j, (j < 8)%nat -> rd' (TA_g_rx_len + Z.of_nat j) = Some (YO0f.le_byte got 8 j)) ->
  (forall j, (j < 4)%nat -> rd' (TA_g_rx_times + Z.of_nat j) = Some (YO0f.le_byte t 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TA_g_rx_fail + Z.of_nat j) = Some (YO0f.le_byte f 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_g_rx_send <= x < TA_g_rx_send + 4) -> ~ (TA_g_rx <= x < TA_g_rx + 8) ->
     ~ (TA_g_rx_len <= x < TA_g_rx_len + 8) -> ~ (TA_g_rx_times <= x < TA_g_rx_times + 4) ->
     ~ (TA_g_rx_fail <= x < TA_g_rx_fail + 4) -> rd' x = rd x) ->
  tw_at TMAP_A rd' (recv_w2c Bw bytes a pf).
Proof.
  intros rd rd' Bw bytes a pf sv got t f Esv Egot Et Ef HX VS VR VL VT VF HO.
  set (P4 := fun x => inb TA_g_rx_fail (TA_g_rx_fail + 4) x).
  set (P3 := fun x => (inb TA_g_rx_times (TA_g_rx_times + 4) x || P4 x)%bool).
  set (P2 := fun x => (inb TA_g_rx_len (TA_g_rx_len + 8) x || P3 x)%bool).
  set (P1 := fun x => (inb TA_g_rx (TA_g_rx + 8) x || P2 x)%bool).
  set (P0 := fun x => (inb TA_g_rx_send (TA_g_rx_send + 4) x || P1 x)%bool).
  assert (H0 : tw_at TMAP_A (fun x => if P0 x then rd x else rd' x) (recv_w2 Bw bytes)).
  { apply (tw_kept TMAP_A rd); [exact HX|]. intros x Hx. cbv beta.
    destruct (P0 x) eqn:E0; [reflexivity|].
    unfold P0, P1, P2, P3, P4 in E0. apply orb_false_iff in E0 as [E1 E0].
    apply orb_false_iff in E0 as [E2 E0]. apply orb_false_iff in E0 as [E3 E0].
    apply orb_false_iff in E0 as [E4 E5].
    apply HO; [exact Hx | exact (inb_false_iff _ _ _ E1) | exact (inb_false_iff _ _ _ E2)
      | exact (inb_false_iff _ _ _ E3) | exact (inb_false_iff _ _ _ E4) | exact (inb_false_iff _ _ _ E5)]. }
  assert (H1 : tw_at TMAP_A (fun x => if P1 x then rd x else rd' x)
    (TW.upd (recv_w2 Bw bytes) (TW.OFF_g_rx_send + 0) (TW.put 4 sv))).
  { apply (rp_tw_step rd rd' P0 P1 _ TW.OFF_g_rx_send TA_g_rx_send TW.SZ_g_rx_send 0 4 sv TMAP_A_g_rx_send);
      [lia | unfold TW.SZ_g_rx_send; lia | exact H0 | | | ].
    - intros j Hj. unfold P1, P2, P3, P4. rp_inb. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VS j Hj).
    - intros x _ Hn. unfold P0. rewrite inb_false by lia. reflexivity. }
  assert (H2 : tw_at TMAP_A (fun x => if P2 x then rd x else rd' x)
    (TW.upd (TW.upd (recv_w2 Bw bytes) (TW.OFF_g_rx_send + 0) (TW.put 4 sv)) (TW.OFF_g_rx + 0) (TW.put 8 a))).
  { apply (rp_tw_step rd rd' P1 P2 _ TW.OFF_g_rx TA_g_rx TW.SZ_g_rx 0 8 a TMAP_A_g_rx);
      [lia | unfold TW.SZ_g_rx; lia | exact H1 | | | ].
    - intros j Hj. unfold P2, P3, P4. rp_inb. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VR j Hj).
    - intros x _ Hn. unfold P1. rewrite inb_false by lia. reflexivity. }
  assert (H3 : tw_at TMAP_A (fun x => if P3 x then rd x else rd' x)
    (TW.upd (TW.upd (TW.upd (recv_w2 Bw bytes) (TW.OFF_g_rx_send + 0) (TW.put 4 sv)) (TW.OFF_g_rx + 0) (TW.put 8 a))
      (TW.OFF_g_rx_len + 0) (TW.put 8 got))).
  { apply (rp_tw_step rd rd' P2 P3 _ TW.OFF_g_rx_len TA_g_rx_len TW.SZ_g_rx_len 0 8 got TMAP_A_g_rx_len);
      [lia | unfold TW.SZ_g_rx_len; lia | exact H2 | | | ].
    - intros j Hj. unfold P3, P4. rp_inb. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VL j Hj).
    - intros x _ Hn. unfold P2. rewrite inb_false by lia. reflexivity. }
  assert (H4 : tw_at TMAP_A (fun x => if P4 x then rd x else rd' x)
    (TW.upd (TW.upd (TW.upd (TW.upd (recv_w2 Bw bytes) (TW.OFF_g_rx_send + 0) (TW.put 4 sv)) (TW.OFF_g_rx + 0)
      (TW.put 8 a)) (TW.OFF_g_rx_len + 0) (TW.put 8 got)) (TW.OFF_g_rx_times + 0) (TW.put 4 t))).
  { apply (rp_tw_step rd rd' P3 P4 _ TW.OFF_g_rx_times TA_g_rx_times TW.SZ_g_rx_times 0 4 t TMAP_A_g_rx_times);
      [lia | unfold TW.SZ_g_rx_times; lia | exact H3 | | | ].
    - intros j Hj. unfold P4. rp_inb. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VT j Hj).
    - intros x _ Hn. unfold P3. rewrite inb_false by lia. reflexivity. }
  assert (H5 : tw_at TMAP_A (fun x => if (fun _ : Z => false) x then rd x else rd' x)
    (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (recv_w2 Bw bytes) (TW.OFF_g_rx_send + 0) (TW.put 4 sv)) (TW.OFF_g_rx + 0)
      (TW.put 8 a)) (TW.OFF_g_rx_len + 0) (TW.put 8 got)) (TW.OFF_g_rx_times + 0) (TW.put 4 t))
      (TW.OFF_g_rx_fail + 0) (TW.put 4 f))).
  { apply (rp_tw_step rd rd' P4 (fun _ => false) _ TW.OFF_g_rx_fail TA_g_rx_fail TW.SZ_g_rx_fail 0 4 f
      TMAP_A_g_rx_fail); [lia | unfold TW.SZ_g_rx_fail; lia | exact H4 | | | ].
    - intros j Hj. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VF j Hj).
    - intros x _ Hn. unfold P4. rewrite inb_false by lia. reflexivity. }
  rewrite !Z.add_0_r in H5. subst sv got t f.
  apply (tw_kept TMAP_A _ rd' _ H5). intros x _. reflexivity.
Qed.

(* The two stores of 0 after the call (g_rx, then g_rx_fail). *)
Lemma rp_tw_w3 : forall (rd rd' : Z -> option Z) B2d,
  tw_at TMAP_A rd B2d ->
  (forall j, (j < 8)%nat -> rd' (TA_g_rx + Z.of_nat j) = Some (YO0f.le_byte 0 8 j)) ->
  (forall j, (j < 4)%nat -> rd' (TA_g_rx_fail + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_g_rx <= x < TA_g_rx + 8) -> ~ (TA_g_rx_fail <= x < TA_g_rx_fail + 4) ->
     rd' x = rd x) ->
  tw_at TMAP_A rd' (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0).
Proof.
  intros rd rd' B2d HX VR VF HO.
  set (P1 := fun x => inb TA_g_rx_fail (TA_g_rx_fail + 4) x).
  set (P0 := fun x => (inb TA_g_rx (TA_g_rx + 8) x || P1 x)%bool).
  assert (H0 : tw_at TMAP_A (fun x => if P0 x then rd x else rd' x) B2d).
  { apply (tw_kept TMAP_A rd); [exact HX|]. intros x Hx. cbv beta.
    destruct (P0 x) eqn:E0; [reflexivity|].
    unfold P0, P1 in E0. apply orb_false_iff in E0 as [E1 E2].
    apply HO; [exact Hx | exact (inb_false_iff _ _ _ E1) | exact (inb_false_iff _ _ _ E2)]. }
  assert (H1 : tw_at TMAP_A (fun x => if P1 x then rd x else rd' x) (TW.upd B2d (TW.OFF_g_rx + 0) (TW.put 8 0))).
  { apply (rp_tw_step rd rd' P0 P1 _ TW.OFF_g_rx TA_g_rx TW.SZ_g_rx 0 8 0 TMAP_A_g_rx);
      [lia | unfold TW.SZ_g_rx; lia | exact H0 | | | ].
    - intros j Hj. unfold P1. rp_inb. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VR j Hj).
    - intros x _ Hn. unfold P0. rewrite inb_false by lia. reflexivity. }
  assert (H2 : tw_at TMAP_A (fun x => if (fun _ : Z => false) x then rd x else rd' x)
    (TW.upd (TW.upd B2d (TW.OFF_g_rx + 0) (TW.put 8 0)) (TW.OFF_g_rx_fail + 0) (TW.put 4 0))).
  { apply (rp_tw_step rd rd' P1 (fun _ => false) _ TW.OFF_g_rx_fail TA_g_rx_fail TW.SZ_g_rx_fail 0 4 0
      TMAP_A_g_rx_fail); [lia | unfold TW.SZ_g_rx_fail; lia | exact H1 | | | ].
    - intros j Hj. reflexivity.
    - intros j Hj. rewrite Z.add_0_r. exact (VF j Hj).
    - intros x _ Hn. unfold P1. rewrite inb_false by lia. reflexivity. }
  rewrite !Z.add_0_r in H2.
  apply (tw_kept TMAP_A _ rd' _ H2). intros x _. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The values the code forms                                        *)
(* ------------------------------------------------------------------ *)

Lemma rp_lor_mul : forall x y k, 0 <= k -> 0 <= y < 2 ^ k -> Z.lor (x * 2 ^ k) y = x * 2 ^ k + y.
Proof.
  intros x y k Hk Hy. symmetry. apply Z.add_nocarry_lor.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec i k) as [Hl|Hl].
  - replace (x * 2 ^ k) with (Z.shiftl x k) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    rewrite Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r x (i - k)) by lia. reflexivity.
  - rewrite <- (Z.mod_small y (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

Lemma rp_den_lit : forall E (j : nat) (v : Z), ew E j = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff j 0) = Z_to_bv 64 v.
Proof.
  intros E j v H Hv. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
  reflexivity.
Qed.
Lemma rp_den_sll : forall E e v k, sv_denot E e = Z_to_bv 64 v -> 0 <= v -> 0 <= k < 64 -> v * 2 ^ k < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SLL e (SLit k)) = Z_to_bv 64 (v * 2 ^ k).
Proof.
  intros E e v k H Hv Hk Hm. cbn [sv_denot alu64 alu]. rewrite H.
  apply bv_eq. rewrite bv_shiftl_unsigned, bv_and_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  assert (Hv2 : v < 2 ^ 64) by (pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); nia).
  rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite (Z.mod_small k (2 ^ 64)) by lia.
  rewrite (Z.mod_small 63 (2 ^ 64)) by lia.
  assert (Ek : Z.land k 63 = k).
  { change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  rewrite Ek, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma rp_den_or : forall E e1 e2 v1 v2, sv_denot E e1 = Z_to_bv 64 v1 -> sv_denot E e2 = Z_to_bv 64 v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> sv_denot E (SAlu ALU_OR e1 e2) = Z_to_bv 64 (Z.lor v1 v2).
Proof.
  intros E e1 e2 v1 v2 H1 H2 R1 R2. cbn [sv_denot alu64 alu]. rewrite H1, H2.
  apply bv_eq. rewrite bv_or_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite (Z.mod_small v1), (Z.mod_small v2) by lia.
  symmetry. rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.
(* `slli x, 8; or y`: a big-endian 16-bit field. *)
Lemma rp_den_be16 : forall E (j k : nat) x y, ew E j = w64 x -> ew E k = w64 y -> 0 <= x < 256 -> 0 <= y < 256 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff j 0) (SLit 8)) (SOff k 0)) = Z_to_bv 64 (x * 2 ^ 8 + y).
Proof.
  intros E j k x y Hj Hk Rx Ry.
  rewrite (rp_den_or E _ _ (x * 2 ^ 8) y); [| apply rp_den_sll; [apply rp_den_lit; [exact Hj | lia] | lia | lia | lia]
    | apply rp_den_lit; [exact Hk | lia] | lia | lia].
  rewrite rp_lor_mul by lia. reflexivity.
Qed.
(* The 32-bit big-endian send value of the loads at a + 18 .. a + 21 (+0x37c .. +0x394). *)
Lemma rp_den_be32 : forall E w x y z, ew E 36 = w64 w -> ew E 37 = w64 x -> ew E 38 = w64 y -> ew E 39 = w64 z ->
  0 <= w < 256 -> 0 <= x < 256 -> 0 <= y < 256 -> 0 <= z < 256 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 16)) (SAlu ALU_SLL (SOff 36 0) (SLit 24)))
    (SAlu ALU_OR (SAlu ALU_SLL (SOff 38 0) (SLit 8)) (SOff 39 0))) =
  Z_to_bv 64 (w * 2 ^ 24 + x * 2 ^ 16 + y * 2 ^ 8 + z).
Proof.
  intros E w x y z Hw Hx Hy Hz Rw Rx Ry Rz.
  assert (D1 : sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 16)) (SAlu ALU_SLL (SOff 36 0) (SLit 24))) =
    Z_to_bv 64 ((w * 2 ^ 8 + x) * 2 ^ 16)).
  { rewrite (rp_den_or E _ _ (x * 2 ^ 16) (w * 2 ^ 24));
      [| apply rp_den_sll; [apply rp_den_lit; [exact Hx | lia] | lia | lia | lia]
       | apply rp_den_sll; [apply rp_den_lit; [exact Hw | lia] | lia | lia | lia] | lia | lia].
    f_equal. rewrite Z.lor_comm.
    replace (w * 2 ^ 24) with ((w * 2 ^ 8) * 2 ^ 16) by ring.
    rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite <- Z.shiftl_lor. rewrite !Z.shiftl_mul_pow2 by lia.
    rewrite rp_lor_mul by lia. reflexivity. }
  rewrite (rp_den_or E _ _ ((w * 2 ^ 8 + x) * 2 ^ 16) (y * 2 ^ 8 + z)); [| exact D1 | | lia | lia].
  - rewrite rp_lor_mul by lia. f_equal. ring.
  - apply rp_den_be16; [exact Hy | exact Hz | lia | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The written bytes                                                *)
(* ------------------------------------------------------------------ *)

(* The five fields the code stores before the call, the two after it. *)
Definition rp_Z5 (x : Z) : Prop :=
  TA_g_rx_send <= x < TA_g_rx_send + 4 \/ TA_g_rx <= x < TA_g_rx + 8 \/ TA_g_rx_len <= x < TA_g_rx_len + 8 \/
  TA_g_rx_times <= x < TA_g_rx_times + 4 \/ TA_g_rx_fail <= x < TA_g_rx_fail + 4.
Definition rp_Z2 (x : Z) : Prop := TA_g_rx <= x < TA_g_rx + 8 \/ TA_g_rx_fail <= x < TA_g_rx_fail + 4.

Lemma rp_inG_row : forall o b n x, In (o, b, n) TMAP_A -> b <= x < b + n -> inG TG.G_HARNESS x.
Proof.
  intros o b n x Hin Hx. unfold inG. apply Exists_exists. exists (b, n).
  split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma rp_twa_G : forall o b n A w x, In (o, b, n) TMAP_A -> o <= A -> A + w <= o + n -> twa_fld o b A w x ->
  inG TG.G_HARNESS x.
Proof. intros o b n A w x Hin H1 H2 Hx. unfold twa_fld in Hx. apply (rp_inG_row o b n x Hin). lia. Qed.
Lemma rp_Z5_G : forall x, rp_Z5 x -> 0 <= x < 0x600000 /\ inG TG.G_HARNESS x.
Proof.
  intros x Hx.
  split; [unfold rp_Z5, TA_g_rx_send, TA_g_rx, TA_g_rx_len, TA_g_rx_times, TA_g_rx_fail in Hx; lia|].
  destruct Hx as [H | [H | [H | [H | H]]]].
  - apply (rp_inG_row _ _ _ x TMAP_A_g_rx_send). unfold TW.SZ_g_rx_send. lia.
  - apply (rp_inG_row _ _ _ x TMAP_A_g_rx). unfold TW.SZ_g_rx. lia.
  - apply (rp_inG_row _ _ _ x TMAP_A_g_rx_len). unfold TW.SZ_g_rx_len. lia.
  - apply (rp_inG_row _ _ _ x TMAP_A_g_rx_times). unfold TW.SZ_g_rx_times. lia.
  - apply (rp_inG_row _ _ _ x TMAP_A_g_rx_fail). unfold TW.SZ_g_rx_fail. lia.
Qed.
Lemma rp_Z2_G : forall x, rp_Z2 x -> 0 <= x < 0x600000 /\ inG TG.G_HARNESS x.
Proof. intros x Hx. apply rp_Z5_G. unfold rp_Z2, rp_Z5 in *. tauto. Qed.

(* Every byte diginet_session_poll may store (diginet_session_poll_cg.v poll_wr) is a byte of G: each row of each
   callee's written range is a field of a row of TMAP_A, or a byte notice stores (TransportGNotice.v notice_wr_G). *)
Ltac rp_bnd := first
  [ unfold TW.A_OW_t_state, TW.OW_t_ESZ, TC.TRANS_MAX, TC.A_OW_dn_body, TW.OW_dn_N, TW.A_Cmd_st, TC.CMDS_MAX,
      TW.A_S_queue_bytes, TW.S_queue_N, TW.S_queue_ESZ, TW.A_M_fly_frame, TC.SPEC_MAX_FRAME, TW.OFF_OW, TW.SZ_OW,
      TW.OFF_g_s, TW.SZ_g_s, TW.OFF_g_cmd, TW.SZ_g_cmd, TW.OFF_M, TW.SZ_M in *; lia
  | vm_compute; congruence ].
Ltac rp_rowG H := first
  [ refine (rp_twa_G _ _ _ _ _ _ TMAP_A_M _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_s _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_cmd _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_q _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_fail_next _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_raw _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_last_counter _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_nq _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_ncmd _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_rx_send _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_rx_fail _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_rx_times _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_now _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_rx _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_rx_len _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_g_cfg _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_GOT _ _ H); rp_bnd
  | refine (rp_twa_G _ _ _ _ _ _ TMAP_A_OW _ _ H); rp_bnd ].
Ltac rp_wr_split H :=
  repeat match type of H with
  | _ \/ _ => destruct H as [H | H]
  | _ /\ _ => let Hb := fresh "Hb" in destruct H as [Hb H]
  | exists _, _ => let y := fresh "y" in destruct H as [y H]
  end.

Lemma rp_poll_wr_G : forall x, poll_wr x -> inG TG.G_HARNESS x.
Proof.
  intros x H.
  cbv beta delta [poll_wr mtick_wr srx_wr onann_wr onack_wr ondata_wr tick_wr wake_wr maybeon_wr slost_wr
    senddata_wr iosend_wr mlost_wr mset_wr mrx_wr] in H.
  rp_wr_split H; first [exact (TransportGNotice.notice_wr_G _ _ _ H) | rp_rowG H].
Qed.

(* ------------------------------------------------------------------ *)
(* 6. What the runs keep, the entry states                             *)
(* ------------------------------------------------------------------ *)

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* A run that changes only bytes of G (Zs) keeps what a call keeps, over an empty window. *)
Lemma rp_kept_run : forall lyc Sc (W : world segs) memc mdc (Wx : world segs) mX mY s (Eo Zs : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  (forall a, Zs a -> 0 <= a < 0x600000 /\ inG TG.G_HARNESS a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H Wx) mY a = aview segs (w_H Wx) mX a) ->
  (forall a, apresent (w_H Wx) mX a -> apresent (w_H Wx) mY a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc Wx mX Wx mY s s Eo.
Proof.
  intros lyc Sc W memc mdc Wx mX mY s Eo Zs LAWS HAR HZ Hkp Hgr.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. apply Hkp; [lia|]. intros HZa. destruct (HZ a HZa) as [Hl _]. lia.
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hce & _).
    apply Hkp; [lia|]. intros HZa. destruct (HZ _ HZa) as [_ Hg].
    exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HAR Hb ltac:(lia) (trans_g_img _ Hg)).
  - intros a Hi HnG _ _. pose proof (transport_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    apply Hkp; [lia|]. intros HZa. exact (HnG (proj2 (HZ a HZa))).
  - intros cid pos a Hin Hr Hn. destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
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
Lemma rp_rom : forall lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (E : Z -> Prop),
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  trans_rom_view_rd W memc -> trans_rom_view_rd W2 mem2.
Proof.
  intros lyc Sc W memc W2 mem2 slo shi E HRU HRE (_ & _ & K3 & _) Hrom a Ha.
  rewrite <- (Hrom a Ha).
  destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_LO in Gh. lia.
Qed.


(* A frame byte, as the model reads it (DgnSpec.v at8), at the block. *)
Lemma rp_fb : forall (mm : word -> option byte) a bytes (k : nat), garr8 segs mm a (TW.zs bytes) ->
  (k < length bytes)%nat -> val_mem segs mm (a + Z.of_nat k) 1 (DSpec.at8 bytes k).
Proof.
  intros mm a bytes k Hg Hk.
  assert (Hlt : (Z.to_nat (Z.of_nat k) < length (TW.zs bytes))%nat)
    by (unfold TW.zs; rewrite length_map, Nat2Z.id; exact Hk).
  destruct (garr8_nthZ segs mm a (TW.zs bytes) (Z.of_nat k) Hg ltac:(lia) Hlt) as [Hv _].
  rewrite Nat2Z.id in Hv.
  replace (DSpec.at8 bytes k) with (nth k (TW.zs bytes) 0); [exact Hv|].
  unfold DSpec.at8, DSpec.bz, TW.zs.
  rewrite (nth_indep _ 0 (bv_unsigned (DSpec.b8 0))) by (rewrite length_map; exact Hk).
  rewrite map_nth. reflexivity.
Qed.
Lemma rp_frame_chunk : forall (E : env) (mm : word -> option byte) a bytes (c : Z) (j : nat),
  garr8 segs mm a (TW.zs bytes) -> 0 <= c -> (Z.to_nat c < length bytes)%nat ->
  ew E j = w64 (DSpec.at8 bytes (Z.to_nat c)) ->
  YP09.chunk_ok segs E mm a (YP09.mkChunk c (CVal 1 (SOff j 0))).
Proof.
  intros E mm a bytes c j Hg Hc Hl He. pose proof (rp_at8_range bytes (Z.to_nat c)) as R.
  apply (chunk_ok_val segs E mm a c 1 (SOff j 0) (DSpec.at8 bytes (Z.to_nat c))).
  - cbn [sv_denot]. rewrite He. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  - cbn. lia.
  - cbn [N.to_nat]. pose proof (rp_fb mm a bytes (Z.to_nat c) Hg Hl) as H. rewrite Z2Nat.id in H by lia. exact H.
Qed.

(* The valuations: the 32 registers and the extra atoms (32 ..). *)
Definition rp_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transport) (Ereg regs extra).
Lemma rp_ew : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (rp_E regs extra) n = YK11.getr regs r.
Proof. intros regs extra n r Hn. unfold rp_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma rp_ew_x : forall regs extra j, (j < 8)%nat -> ew (rp_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. unfold rp_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma rp_ew_img : forall regs extra n, (A_TEXT <= n < A_LIM)%nat -> ew (rp_E regs extra) n = Z_to_bv 64 (VAL n).
Proof. intros regs extra n Hn. unfold rp_E. apply Eimg_img. exact Hn. Qed.
Lemma rp_env_img : forall regs extra, img_env VAL A_LIM (rp_E regs extra).
Proof. intros regs extra. unfold rp_E. apply Eimg_env. Qed.
Lemma rp_agree : forall regs extra, env_agree 32 (Ereg regs extra) (rp_E regs extra).
Proof. intros regs extra. split; [intros n Hn; unfold rp_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma rp_vals : VAL (A_HI 84) = 6158800 /\ VAL (A_HI 85) = 6236628 /\ VAL (A_HI 86) = 6236632 /\
  VAL (A_HI 87) = 6236640 /\ VAL (A_OBJ 9) = POLL_S /\ BASE = 528996.
Proof. vm_compute. repeat split. Qed.
Lemma rp_uimg : forall regs extra n v, (A_TEXT <= n < A_LIM)%nat -> VAL n = v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (rp_E regs extra) n) = v.
Proof. intros regs extra n v Hn Hv Hr. rewrite rp_ew_img by exact Hn. rewrite Hv. apply unsigned_lit_small. lia. Qed.
Lemma rp_ureg : forall regs extra n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> YK11.getr regs r = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (rp_E regs extra) n) = v.
Proof. intros regs extra n r v Hn Hr Hv. rewrite (rp_ew regs extra n r Hn), Hr. apply unsigned_lit_small. lia. Qed.

Ltac rp_facts := unfold facts_ok; cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok];
  unfold afact_ok; cbn [af_lo af_hi af_al2].

(* +0x14c: no region, s2 = n. *)
Lemma rp_entry0 : forall (W : world segs) regs mem n,
  YK11.getr regs 18 = w64 n -> 0 <= n <= 65535 ->
  st_ok_pi segs VAL (rp_E regs []) ss_rp0
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + RECV_POLL)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem n R18 Hn.
  pose proof (rp_ureg regs [] 18 18%bv n eq_refl R18 ltac:(lia)) as U18.
  rewrite restrict_mkst_fx. unfold ss_rp0.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold rp_facts0. rp_facts. rewrite U18. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* +0x15c: no region, s2 = n, a1 = got. *)
Lemma rp_entryG : forall (W : world segs) regs mem n got,
  YK11.getr regs 18 = w64 n -> 0 <= n <= 65535 -> YK11.getr regs 11 = w64 got -> 0 <= got <= 1514 ->
  st_ok_pi segs VAL (rp_E regs []) ss_rpG
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + RP_GOT)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem n got R18 Hn R11 Hg.
  pose proof (rp_ureg regs [] 18 18%bv n eq_refl R18 ltac:(lia)) as U18.
  pose proof (rp_ureg regs [] 11 11%bv got eq_refl R11 ltac:(lia)) as U11.
  rewrite restrict_mkst_fx. unfold ss_rpG.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold rp_factsG. rp_facts. rewrite U18, U11. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The frame bytes the phase-F atoms hold. *)
Definition rp_fvals (bytes : list byte) : list word :=
  [w64 (DSpec.at8 bytes 12); w64 (DSpec.at8 bytes 13); w64 (DSpec.at8 bytes 14); w64 (DSpec.at8 bytes 15);
   w64 (DSpec.at8 bytes 18); w64 (DSpec.at8 bytes 19); w64 (DSpec.at8 bytes 20); w64 (DSpec.at8 bytes 21)].

(* +0x164 (n >= 30): the frame region and the shadow entry of its first 30 bytes. *)
Lemma rp_entryF : forall (W : world segs) regs mem a bytes got,
  YK11.getr regs 8 = w64 a -> YK11.getr regs 11 = w64 got -> YK11.getr regs 18 = w64 (Z.of_nat (length bytes)) ->
  YK11.getr regs 21 = w64 SHADOW_OFF ->
  30 <= Z.of_nat (length bytes) <= 65535 -> 30 <= got <= 1514 -> 4096 <= a -> a + 31 <= 2 ^ 47 ->
  garr8 segs (mrestrict (w_H W) mem) a (TW.zs bytes) ->
  decode_rd_ok W mem a (Z.of_nat (length bytes)) ->
  st_ok_pi segs VAL (rp_E regs (rp_fvals bytes)) ss_rpF
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + RP_F)) mem (YK11.seg_rom segs))) /\
  sh_ok segs RP_BX RP_SHF (rp_E regs (rp_fvals bytes)) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem a bytes got R8 R11 R18 R21 Hn Hg Ha4 Ha47 Hgarr HRD.
  pose proof HRD as (_ & HRA & _ & Hmr & _ & _).
  set (E := rp_E regs (rp_fvals bytes)).
  pose proof (rp_ureg regs (rp_fvals bytes) 8 8%bv a eq_refl R8 ltac:(lia)) as U8. fold E in U8.
  pose proof (rp_ureg regs (rp_fvals bytes) 11 11%bv got eq_refl R11 ltac:(lia)) as U11. fold E in U11.
  pose proof (rp_ureg regs (rp_fvals bytes) 18 18%bv _ eq_refl R18 ltac:(lia)) as U18. fold E in U18.
  pose proof (rp_ureg regs (rp_fvals bytes) 21 21%bv SHADOW_OFF eq_refl R21 ltac:(unfold SHADOW_OFF; lia)) as U21.
  fold E in U21.
  assert (EX : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (rp_fvals bytes) (Z_to_bv 64 0))
    by (intros j Hj; exact (rp_ew_x regs (rp_fvals bytes) j Hj)).
  pose proof (EX 0%nat ltac:(lia)) as A32. pose proof (EX 1%nat ltac:(lia)) as A33.
  pose proof (EX 2%nat ltac:(lia)) as A34. pose proof (EX 3%nat ltac:(lia)) as A35.
  pose proof (EX 4%nat ltac:(lia)) as A36. pose proof (EX 5%nat ltac:(lia)) as A37.
  pose proof (EX 6%nat ltac:(lia)) as A38. pose proof (EX 7%nat ltac:(lia)) as A39.
  cbn [Nat.add nth rp_fvals] in A32, A33, A34, A35, A36, A37, A38, A39.
  split.
  - rewrite restrict_mkst_fx. unfold ss_rpF.
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold rp_frame, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
        first [ exact (rp_frame_chunk E _ a bytes 12 32 Hgarr ltac:(lia) ltac:(cbn; lia) A32)
              | exact (rp_frame_chunk E _ a bytes 13 33 Hgarr ltac:(lia) ltac:(cbn; lia) A33)
              | exact (rp_frame_chunk E _ a bytes 14 34 Hgarr ltac:(lia) ltac:(cbn; lia) A34)
              | exact (rp_frame_chunk E _ a bytes 15 35 Hgarr ltac:(lia) ltac:(cbn; lia) A35)
              | exact (rp_frame_chunk E _ a bytes 18 36 Hgarr ltac:(lia) ltac:(cbn; lia) A36)
              | exact (rp_frame_chunk E _ a bytes 19 37 Hgarr ltac:(lia) ltac:(cbn; lia) A37)
              | exact (rp_frame_chunk E _ a bytes 20 38 Hgarr ltac:(lia) ltac:(cbn; lia) A38)
              | exact (rp_frame_chunk E _ a bytes 21 39 Hgarr ltac:(lia) ltac:(cbn; lia) A39) ].
    + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
    + unfold rp_factsF. rp_facts. rewrite U8, U11, U18, U21.
      rewrite A32, A33, A34, A35, A36, A37, A38, A39. unfold w64.
      pose proof (rp_at8_range bytes 12). pose proof (rp_at8_range bytes 13). pose proof (rp_at8_range bytes 14).
      pose proof (rp_at8_range bytes 15). pose proof (rp_at8_range bytes 18). pose proof (rp_at8_range bytes 19).
      pose proof (rp_at8_range bytes 20). pose proof (rp_at8_range bytes 21).
      rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold SHADOW_OFF; lia].
  - unfold sh_ok, RP_SHF. constructor; [|constructor].
    apply (shent_ok_of_range segs (w_H W) mem E RP_BX 8 a (Z.of_nat (length bytes)) a 0 30 HRA).
    + unfold U, RP_BX. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U21.
    + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U8.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx.
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr. unfold SHADOW_OFF; lia.
Qed.

(* +0x1f4: the five stores' regions, at a2 = atom 12 and the auipc values of the pairs 85, 84, 86, 87. *)
Lemma rp_entryS : forall (W : world segs) regs mem,
  YK11.getr regs 12 = w64 RECV_RXS_HI ->
  st_ok_pi segs VAL (rp_E regs []) ss_rpS
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + RP_SEND)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem R12.
  destruct rp_vals as (V84 & V85 & V86 & V87 & _).
  pose proof (rp_ureg regs [] 12 12%bv RECV_RXS_HI eq_refl R12 ltac:(unfold RECV_RXS_HI, TA_g_rx_send; lia)) as U12.
  pose proof (rp_uimg regs [] (A_HI 84) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V84 ltac:(lia)) as U84.
  pose proof (rp_uimg regs [] (A_HI 85) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V85 ltac:(lia)) as U85.
  pose proof (rp_uimg regs [] (A_HI 86) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V86 ltac:(lia)) as U86.
  pose proof (rp_uimg regs [] (A_HI 87) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V87 ltac:(lia)) as U87.
  assert (GW : forall o b n x, In (o, b, n) TMAP_A -> b <= x < b + n -> forall m, writable_at segs m x)
    by (intros o b n x Hin Hx m; exact (gx_rw_writable segs TG.G_HARNESS x G_HARNESS_rw (rp_inG_row o b n x Hin Hx) m)).
  rewrite restrict_mkst_fx. unfold ss_rpS.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [rp_snd rp_len rp_rx rp_tm rp_fl YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks
        base_val];
      rewrite ?U12, ?U84, ?U85, ?U86, ?U87;
      (split; [unfold RECV_RXS_HI, TA_g_rx_send; lia|]); (split; [unfold RECV_RXS_HI, TA_g_rx_send; lia|]);
      (split; [|constructor]); intros o Ho.
    + apply (GW _ _ _ _ TMAP_A_g_rx_send). unfold RECV_RXS_HI, TA_g_rx_send, TW.SZ_g_rx_send. lia.
    + apply (GW _ _ _ _ TMAP_A_g_rx_len). unfold TA_g_rx_len, TW.SZ_g_rx_len. lia.
    + apply (GW _ _ _ _ TMAP_A_g_rx). unfold TA_g_rx, TW.SZ_g_rx. lia.
    + apply (GW _ _ _ _ TMAP_A_g_rx_times). unfold TA_g_rx_times, TW.SZ_g_rx_times. lia.
    + apply (GW _ _ _ _ TMAP_A_g_rx_fail). unfold TA_g_rx_fail, TW.SZ_g_rx_fail. lia.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, rp_snd, rp_len, rp_rx, rp_tm, rp_fl.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U12, U84, U85, U86, U87.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | unfold RECV_RXS_HI, TA_g_rx_send; lia].
  - unfold rp_factsS. rp_facts. rewrite U12, U84, U85, U86, U87.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

(* +0x23c: the two stores of 0, at s2 - 0x30 and s3 + 0x620. *)
Lemma rp_entryT : forall (W : world segs) regs mem,
  YK11.getr regs 18 = Z_to_bv 64 6158800 -> YK11.getr regs 19 = Z_to_bv 64 6236640 ->
  st_ok_pi segs VAL (rp_E regs []) ss_rpT
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + RP_RET)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem R18 R19.
  pose proof (rp_ureg regs [] 18 18%bv 6158800 eq_refl R18 ltac:(lia)) as U18.
  pose proof (rp_ureg regs [] 19 19%bv 6236640 eq_refl R19 ltac:(lia)) as U19.
  assert (GW : forall o b n x, In (o, b, n) TMAP_A -> b <= x < b + n -> forall m, writable_at segs m x)
    by (intros o b n x Hin Hx m; exact (gx_rw_writable segs TG.G_HARNESS x G_HARNESS_rw (rp_inG_row o b n x Hin Hx) m)).
  rewrite restrict_mkst_fx. unfold ss_rpT.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [rp_rx2 rp_fl2 YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite ?U18, ?U19; (split; [lia|]); (split; [lia|]); (split; [|constructor]); intros o Ho.
    + apply (GW _ _ _ _ TMAP_A_g_rx). unfold TA_g_rx, TW.SZ_g_rx. lia.
    + apply (GW _ _ _ _ TMAP_A_g_rx_fail). unfold TA_g_rx_fail, TW.SZ_g_rx_fail. lia.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, rp_rx2, rp_fl2. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U18, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; first [exact I | lia].
  - unfold rp_factsT. rp_facts. rewrite U18, U19.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.
End k.

(* ------------------------------------------------------------------ *)
(* 7. The poll flags the code forms, a chunk read back                 *)
(* ------------------------------------------------------------------ *)

(* `andi a3, s1, 1; addi a3, a3, 1` (g_rx_times), `slli s1, s1, 62; srli a0, s1, 63` (g_rx_fail) and `xori s1, a0, 1`
   (ticked), on s1 = the entry's a3, whose low 32 bits are pf (plain receive.v r_twice, r_fails, r_ticked). *)
Lemma rp_den_times : forall E w pf, ew E 9 = w -> bv_unsigned w mod 2 ^ 32 = pf ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 9 0) (SLit 1)) (SLit 1)) = Z_to_bv 64 (Z.land pf 1 + 1).
Proof.
  intros E w pf H Hp. rewrite denot_lit_U. f_equal.
  rewrite !U_SAlu, U_SOff, !U_SLit, H. cbn [zalu_raw].
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  rewrite Z.add_0_r, (zcanon_id (bv_unsigned w)) by (unfold M64; lia).
  rewrite PR.r_twice, Hp.
  destruct (rp_land1 pf) as [E1|E1]; rewrite E1; reflexivity.
Qed.
Lemma rp_den_fails : forall E w pf, ew E 9 = w -> bv_unsigned w mod 2 ^ 32 = pf ->
  sv_denot E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 9 0) (SLit 62)) (SLit 63)) = Z_to_bv 64 (Z.land (Z.shiftr pf 1) 1).
Proof.
  intros E w pf H Hp. rewrite denot_lit_U. f_equal.
  rewrite !U_SAlu, U_SOff, !U_SLit, H. cbn [zalu_raw].
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  rewrite Z.add_0_r, (zcanon_id (bv_unsigned w)) by (unfold M64; lia).
  change (Z.land (zcanon 62) 63) with 62. change (Z.land (zcanon 63) 63) with 63.
  pose proof (PR.r_fails w) as F. rewrite Z_to_bv_unsigned in F.
  rewrite (zcanon_wrap (Z.shiftl (bv_unsigned w) 62)). rewrite F, Hp.
  rewrite zcanon_id; [reflexivity|]. destruct (rp_land1 (Z.shiftr pf 1)) as [E1|E1]; rewrite E1; unfold M64; lia.
Qed.
Lemma rp_den_ticked : forall E w pf, ew E 9 = w -> bv_unsigned w mod 2 ^ 32 = pf ->
  sv_denot E (SAlu ALU_XOR (SAlu ALU_SRL (SAlu ALU_SLL (SOff 9 0) (SLit 62)) (SLit 63)) (SLit 1)) =
  Z_to_bv 64 (recv_ticked pf).
Proof.
  intros E w pf H Hp. rewrite denot_lit_U. f_equal.
  rewrite U_SAlu, U_SLit. cbn [zalu_raw]. unfold U. rewrite (rp_den_fails E w pf H Hp).
  rewrite <- rp_ticked_eq.
  destruct (rp_land1 (Z.shiftr pf 1)) as [E1|E1]; rewrite E1; reflexivity.
Qed.
(* a1 - 14 (got - 14 >= 16). *)
Lemma rp_den_m14 : forall E got, ew E 11 = w64 got -> 14 <= got < 2 ^ 64 ->
  sv_denot E (SOff 11 (-14)) = Z_to_bv 64 (got - 14).
Proof.
  intros E got H Hg. rewrite denot_lit_U. f_equal. rewrite U_SOff, H. unfold w64.
  rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* A region cell of n bytes holding v, read byte by byte through the view. *)
Lemma rp_aview_of_val : forall H (m : word -> option byte) a (n : nat) v j,
  val_mem tfibsegs (mrestrict H m) a n v -> (j < n)%nat ->
  aview tfibsegs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
  intros H m a n v j HV Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma rp_vm_w : forall (m : word -> option byte) a (w : N) v, Z.of_N w <= 8 ->
  val_mem tfibsegs m a (N.to_nat w) (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) ->
  val_mem tfibsegs m a (N.to_nat w) v.
Proof.
  intros m a w v Hw H.
  assert (Hd : (2 ^ (8 * Z.of_N w) | 2 ^ 64)).
  { exists (2 ^ (64 - 8 * Z.of_N w)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (E : (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) mod 2 ^ (8 * Z.of_N w) = v mod 2 ^ (8 * Z.of_N w)).
  { rewrite Zmod_mod, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    apply Z.mod_mod_divide; try exact Hd; try (apply Z.pow_nonzero; lia); try (apply Z.pow_pos_nonneg; lia). }
  intros k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite N_nat_Z, E. reflexivity.
Qed.
(* The bytes a chunk of w bytes holding the value v leaves, read through the view. *)
Lemma rp_chunk_bytes : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e v,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < N.to_nat w)%nat ->
  aview tfibsegs H m (base_val E bopt + off + Z.of_nat j) = Some (YO0f.le_byte v (N.to_nat w) j).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e v (_ & _ & _ & Hcs) Hin Hw He j Hj.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  pose proof (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw) as HV. rewrite He in HV.
  exact (rp_aview_of_val H m _ _ v j (rp_vm_w _ _ w v Hw HV) Hj).
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac rp_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac rp_region HS i HR :=
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
Ltac rp_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac rp_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
Ltac rp_kreg HS regsX n r Q H :=
  lazymatch type of Q with _ = ?v =>
    rp_reg HS r v H ltac:(cbn [sv_denot]; rewrite (rp_ew regsX [] n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q)
  end.

(* The send value on each path of the frame's tests (rp_send_got). *)
Lemma rp_be16_range : forall l i, 0 <= DSpec.be16 l i < 65536.
Proof. intros l i. rewrite rp_be16. pose proof (rp_at8_range l i). pose proof (rp_at8_range l (S i)). lia. Qed.
Lemma rp_snd_lt30 : forall bytes, Z.of_nat (length bytes) < 30 ->
  recv_send (firstn (Z.to_nat (recv_got bytes)) bytes) = 0.
Proof. intros bytes H. rewrite rp_send_got, (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma rp_snd_et : forall bytes, 30 <= Z.of_nat (length bytes) -> DSpec.be16 bytes 12 <> 34911 ->
  recv_send (firstn (Z.to_nat (recv_got bytes)) bytes) = 0.
Proof.
  intros bytes H E. rewrite rp_send_got, (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) E). reflexivity.
Qed.
Lemma rp_snd_nb : forall bytes, 30 <= Z.of_nat (length bytes) -> DSpec.be16 bytes 12 = 34911 ->
  DSpec.be16 bytes 14 < 16 -> recv_send (firstn (Z.to_nat (recv_got bytes)) bytes) = 0.
Proof.
  intros bytes H E N.
  rewrite rp_send_got, (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_eq _ _) E), (proj2 (Z.ltb_lt _ _) N). reflexivity.
Qed.
Lemma rp_snd_big : forall bytes, 30 <= Z.of_nat (length bytes) -> DSpec.be16 bytes 12 = 34911 ->
  16 <= DSpec.be16 bytes 14 -> recv_got bytes - 14 < DSpec.be16 bytes 14 ->
  recv_send (firstn (Z.to_nat (recv_got bytes)) bytes) = 0.
Proof.
  intros bytes H E N G.
  rewrite rp_send_got, (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_eq _ _) E), (proj2 (Z.ltb_ge _ _) N),
    (proj2 (Z.ltb_lt _ _) G).
  reflexivity.
Qed.
Lemma rp_snd_ok : forall bytes, 30 <= Z.of_nat (length bytes) -> DSpec.be16 bytes 12 = 34911 ->
  16 <= DSpec.be16 bytes 14 -> DSpec.be16 bytes 14 <= recv_got bytes - 14 ->
  recv_send (firstn (Z.to_nat (recv_got bytes)) bytes) = DSpec.be32 bytes 18.
Proof.
  intros bytes H E N G.
  rewrite rp_send_got, (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_eq _ _) E), (proj2 (Z.ltb_ge _ _) N),
    (proj2 (Z.ltb_ge _ _) G).
  reflexivity.
Qed.

(* The branches the code takes, at an environment whose atoms hold n (18), got (11) and the frame's bytes (32 ..). *)
Lemma rp_br_n : forall E n c, ew E 18 = w64 n -> 0 <= n < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  branch_taken BC_LTU (sv_denot E (SOff 18 0)) (sv_denot E (SLit c)) = (n <? c).
Proof.
  intros E n c H Hn Hc. rewrite (rp_den_lit E 18 n H ltac:(lia)).
  cbn [branch_taken sv_denot]. rewrite EPI.mrxk_ltu by lia. reflexivity.
Qed.
Lemma rp_br_et : forall E bytes, ew E 32 = w64 (DSpec.at8 bytes 12) -> ew E 33 = w64 (DSpec.at8 bytes 13) ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff 32 0) (SLit 8)) (SOff 33 0)))
    (sv_denot E (SLit 34911)) = negb (DSpec.be16 bytes 12 =? 34911).
Proof.
  intros E bytes H32 H33.
  rewrite (rp_den_be16 E 32 33 _ _ H32 H33 (rp_at8_range _ _) (rp_at8_range _ _)), <- rp_be16.
  cbn [branch_taken sv_denot]. rewrite EPI.mrxk_eqb by (pose proof (rp_be16_range bytes 12); lia). reflexivity.
Qed.
Lemma rp_br_nb : forall E bytes, ew E 34 = w64 (DSpec.at8 bytes 14) -> ew E 35 = w64 (DSpec.at8 bytes 15) ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 35 0)))
    (sv_denot E (SLit 16)) = (DSpec.be16 bytes 14 <? 16).
Proof.
  intros E bytes H34 H35.
  rewrite (rp_den_be16 E 34 35 _ _ H34 H35 (rp_at8_range _ _) (rp_at8_range _ _)), <- rp_be16.
  cbn [branch_taken sv_denot]. rewrite EPI.mrxk_ltu by (pose proof (rp_be16_range bytes 14); lia). reflexivity.
Qed.
Lemma rp_br_len : forall E bytes got, ew E 11 = w64 got -> 14 <= got < 2 ^ 63 ->
  ew E 34 = w64 (DSpec.at8 bytes 14) -> ew E 35 = w64 (DSpec.at8 bytes 15) ->
  branch_taken BC_GEU (sv_denot E (SOff 11 (-14)))
    (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 35 0))) =
  negb (got - 14 <? DSpec.be16 bytes 14).
Proof.
  intros E bytes got H11 Hg H34 H35.
  rewrite (rp_den_m14 E got H11 ltac:(lia)).
  rewrite (rp_den_be16 E 34 35 _ _ H34 H35 (rp_at8_range _ _) (rp_at8_range _ _)), <- rp_be16.
  cbn [branch_taken]. rewrite EPI.mrxk_ltu by (pose proof (rp_be16_range bytes 14); lia). reflexivity.
Qed.

(* The environment after a run: the atoms below 1024 are the entry's. *)
Ltac rp_ewv := repeat (rewrite ew_ewset_other by lia).
Ltac rp_curE HS := lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ _ => EF
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ _ => EF end.
(* A register the symbolic state HS holds as its own atom n, at the entry registers regsB (and extra atoms xs). *)
Ltac rp_kregE HS regsB xs n r Q H :=
  lazymatch type of Q with _ = ?v =>
    rp_reg HS r v H ltac:(cbn [sv_denot]; rp_ewv; rewrite (rp_ew regsB xs n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
                          exact Q)
  end.
(* The callee-saved registers HS holds as their own atoms. *)
Ltac rp_pres HS regsB xs H :=
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict ?Hh ?msx) =>
    assert (H : aregs_preserved regsB (ms_regs msx)) by
      (apply (aregs_preserved_of_st_ok tfibsegs Hh EF _ msx regsB xs HS);
       [ apply (env_agree_trans _ _ (rp_E regsB xs) _ (rp_agree regsB xs));
         split; [intros ? ?; rp_ewv; reflexivity | reflexivity]
       | vm_compute; reflexivity ])
  end.
(* A run that writes nothing: the written ranges of its frame are empty. *)
Ltac rp_cover0 := intros ? ? ? ? Hin Hy; cbv beta;
  lazymatch type of Hin with In ?z ?l => let l' := eval vm_compute in l in change (In z l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hy; lia |]);
  try destruct Hin.
(* After such a run: the view and the present bytes at mem2, carried to the run's memory. *)
Ltac rp_kv HS W2 mem2 KV GV :=
  let m1 := lazymatch type of HS with context [restrict _ ?msn] => constr:(ms_mem msn) end in
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let KV' := fresh "KV" in let GV' := fresh "GV" in
    assert (KV' : forall x, 0 <= x < 2 ^ 64 -> aview tfibsegs (w_H W2) m1 x = aview tfibsegs (w_H W2) mem2 x)
      by (intros x Hx; refine (eq_trans _ (KV x Hx));
          apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [rp_cover0 | exact Hx | tauto]);
    assert (GV' : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) m1 x)
      by (intros x Hx; exact (apresent_grows _ _ _ x HG (GV x Hx)));
    clear KV GV; rename KV' into KV; rename GV' into GV;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac rp_md := lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mt ?m0] =>
  let md' := fresh "md" in set (md' := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md'; clear mt end.
Ltac rp_awr0 := rp_awr_rs;
  repeat (apply awr_ok_x_cons_g; [intros ? Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* 8. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (p by_poll pf T : Z)
  (bytes Bw : list byte) (ch : list (Z * Z * Z)) (a : Z) (Bw' : list byte).
Hypothesis LAWS0 : recv_laws B MT.
Hypothesis CALLS : recv_calls B MT.
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
  (@W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m2 d2
    (k + 1)).

(* +0x1f4 .. the set cut: the five stores, diginet_session_poll, the two stores of 0, `j` the set cut. *)
Lemma rp_send : forall ly2 S2 (W2 : world segs) mem2 md2 regs2 regsX memX mdX,
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
  recv_blk W2 mem2 a bytes ->
  tw_at TMAP_A (aview segs (w_H W2) mem2) (recv_w2 Bw bytes) ->
  recv_regs_poll regs regs2 by_poll a bytes ->
  JX ly2 S2 W2 memX mdX ->
  (forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) memX x = aview segs (w_H W2) mem2 x) ->
  (forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) memX x) ->
  aregs_preserved regs2 regsX ->
  YK11.getr regsX 10 = w64 (recv_send (firstn (Z.to_nat (recv_got bytes)) bytes)) ->
  YK11.getr regsX 11 = w64 (recv_got bytes) -> YK11.getr regsX 12 = w64 RECV_RXS_HI ->
  SRr segs W2 (CFG RP_SEND regsX memX mdX) POST.
Proof.
intros ly2 S2 W2 mem2 md2 regs2 regsX memX mdX HCUR HBLK HTW HREGS HJ KDX GRX HPX X10 X11 X12.
pose proof LAWS0 as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
pose proof CALLS as (CM & CCPY & CMSET & CPOLL & CMRX & CRX & CSETL & CFREE).
pose proof HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hch & Hal & Hwlo & Hwhi & Hbp & Hpf &
  Hn & Hgarr & Hsrc & Htw0 & Hgf0 & Hmod & Hrom & Hrinv & Hdn & Q1c & Q2c & Q3c & Q4c & Q5c & Hnev & Hlive & Hmo &
  Hcost & Htrm & Htrf).
pose proof HRES as ((Ha0 & Ha64) & HM).
pose proof HREGS as (((R2 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27) & R8 & R9 & R18 & R19 & R21) & R12).
pose proof HCUR as (HJ2 & Hfrs & Hperm & Hmo2 & HK2 & Hsv2 & Ha4096).
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
pose proof HJi as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
assert (ERS : RECV_STK = 16448) by reflexivity.
assert (EPS : POLL_STK = 9344) by reflexivity.
assert (ERF : RECV_FRAME = 64) by reflexivity.
assert (Hce : alloc_ceiling <= spZ regs - RECV_STK) by lia.
assert (Hsp47 : spZ regs <= 2 ^ 47) by lia.
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARX.
assert (Hblk : In (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 memX mdX _ _ HARX Hblk) as (_ & _ & Hbce & _ & _).
pose proof (req_size_pos (Z.max 1 (Z.of_nat (length bytes))) ltac:(lia)) as [_ Hreq].
pose proof (rp_send_range bytes) as Rsv.
pose proof (rp_got_range bytes) as (Rg1 & Rg2 & Rg3 & Rg4).
(* the registers the run reads *)
assert (P2 : YK11.getr regsX 2 = w64 (spZ regs - RECV_FRAME)) by exact (eq_trans (HPX 2 ltac:(hnf; lia)) R2).
assert (P3 : YK11.getr regsX 3 = w64 (as_gp B)) by exact (eq_trans (eq_trans (HPX 3 ltac:(hnf; lia)) R3) Hgp).
assert (P4 : YK11.getr regsX 4 = w64 (as_tp B)) by exact (eq_trans (eq_trans (HPX 4 ltac:(hnf; lia)) R4) Htp).
assert (P8 : YK11.getr regsX 8 = w64 a) by exact (eq_trans (HPX 8 ltac:(hnf; lia)) R8).
assert (P9 : YK11.getr regsX 9 = YK11.getr regs 13) by exact (eq_trans (HPX 9 ltac:(hnf; lia)) R9).
assert (P22 : YK11.getr regsX 22 = YK11.getr regs 22) by exact (eq_trans (HPX 22 ltac:(hnf; lia)) R22).
assert (P23 : YK11.getr regsX 23 = YK11.getr regs 23) by exact (eq_trans (HPX 23 ltac:(hnf; lia)) R23).
assert (P24 : YK11.getr regsX 24 = YK11.getr regs 24) by exact (eq_trans (HPX 24 ltac:(hnf; lia)) R24).
assert (P25 : YK11.getr regsX 25 = YK11.getr regs 25) by exact (eq_trans (HPX 25 ltac:(hnf; lia)) R25).
assert (P26 : YK11.getr regsX 26 = YK11.getr regs 26) by exact (eq_trans (HPX 26 ltac:(hnf; lia)) R26).
assert (P27 : YK11.getr regsX 27 = YK11.getr regs 27) by exact (eq_trans (HPX 27 ltac:(hnf; lia)) R27).
(* run S, +0x1f4 .. `jal diginet_session_poll` (+0x238) *)
pose proof (@rp_entryS fx rc W2 regsX memX X12) as HS.
assert (SHOK : sh_ok segs RP_BX (@nil shent) (rp_E regsX []) (mrestrict (w_H W2) memX)) by constructor.
assert (HEI : img_env VAL A_LIM (rp_E regsX [])) by apply rp_env_img.
destruct rp_vals as (V84 & V85 & V86 & V87 & V9 & VB).
pose proof (rp_ureg regsX [] 12 12%bv RECV_RXS_HI eq_refl X12 ltac:(unfold RECV_RXS_HI, TA_g_rx_send; lia)) as U12.
pose proof (rp_uimg regsX [] (A_HI 84) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V84 ltac:(lia)) as U84.
pose proof (rp_uimg regsX [] (A_HI 85) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V85 ltac:(lia)) as U85.
pose proof (rp_uimg regsX [] (A_HI 86) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V86 ltac:(lia)) as U86.
pose proof (rp_uimg regsX [] (A_HI 87) _ ltac:(unfold A_HI, A_TEXT, A_LIM; lia) V87 ltac:(lia)) as U87.
change (A_HI 84) with 484%nat in U84. change (A_HI 85) with 485%nat in U85.
change (A_HI 86) with 486%nat in U86. change (A_HI 87) with 487%nat in U87.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_tok RUN HS HJ SHOK RP_B0.
{ rp_awr_rs.
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U12 in Hx;
    apply (rp_inG_row _ _ _ x TMAP_A_g_rx_send); unfold RECV_RXS_HI, TA_g_rx_send, TW.SZ_g_rx_send in *; lia |].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U85 in Hx;
    apply (rp_inG_row _ _ _ x TMAP_A_g_rx_len); unfold TA_g_rx_len, TW.SZ_g_rx_len in *; lia |].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U84 in Hx;
    apply (rp_inG_row _ _ _ x TMAP_A_g_rx); unfold TA_g_rx, TW.SZ_g_rx in *; lia |].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U86 in Hx;
    apply (rp_inG_row _ _ _ x TMAP_A_g_rx_times); unfold TA_g_rx_times, TW.SZ_g_rx_times in *; lia |].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U87 in Hx;
    apply (rp_inG_row _ _ _ x TMAP_A_g_rx_fail); unfold TA_g_rx_fail, TW.SZ_g_rx_fail in *; lia |].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy mdX) mat mdX) in *. clearbody md1. clear mat.
lazymatch type of HS with
| OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?mf) => rename mf into msC
end.
(* run S wrote the five fields only *)
assert (KR1 : forall x, 0 <= x < 2 ^ 64 -> ~ rp_Z5 x -> aview segs (w_H W2) (ms_mem msC) x = aview segs (w_H W2) memX x).
{ intros x Hx Hnz. apply (kept_of_frame _ _ _ _ _ rp_Z5 HFr); [| exact Hx | exact Hnz].
  intros b wlo whi y Hin Hy. cbv beta.
  lazymatch type of Hin with In ?z ?l => let l' := eval vm_compute in l in change (In z l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hy;
    rewrite ?U12, ?U84, ?U85, ?U86, ?U87 in Hy;
    unfold rp_Z5, RECV_RXS_HI, TA_g_rx_send, TA_g_rx, TA_g_rx_len, TA_g_rx_times, TA_g_rx_fail in Hy |- *; lia |]).
  destruct Hin. }
assert (GA1 : forall x, apresent (w_H W2) memX x -> apresent (w_H W2) (ms_mem msC) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
(* the five stores' bytes *)
rp_region HS 0%nat HR0. rp_region HS 1%nat HR1. rp_region HS 2%nat HR2. rp_region HS 3%nat HR3.
rp_region HS 4%nat HR4.
assert (W9 : ew (rp_E regsX []) 9 = YK11.getr regs 13) by exact (eq_trans (rp_ew regsX [] 9 9%bv eq_refl) P9).
assert (D10 : sv_denot (rp_E regsX []) (SOff 10 0) = Z_to_bv 64 (recv_send (firstn (Z.to_nat (recv_got bytes)) bytes)))
  by (apply rp_den_lit; [exact (eq_trans (rp_ew regsX [] 10 10%bv eq_refl) X10) | lia]).
assert (D11 : sv_denot (rp_E regsX []) (SOff 11 0) = Z_to_bv 64 (recv_got bytes))
  by (apply rp_den_lit; [exact (eq_trans (rp_ew regsX [] 11 11%bv eq_refl) X11) | lia]).
assert (D8 : sv_denot (rp_E regsX []) (SOff 8 0) = Z_to_bv 64 a)
  by (apply rp_den_lit; [exact (eq_trans (rp_ew regsX [] 8 8%bv eq_refl) P8) | lia]).
pose proof (rp_den_times (rp_E regsX []) _ pf W9 H13) as Dt.
pose proof (rp_den_fails (rp_E regsX []) _ pf W9 H13) as Df.
assert (VS : forall j, (j < 4)%nat -> aview segs (w_H W2) (ms_mem msC) (TA_g_rx_send + Z.of_nat j) =
  Some (YO0f.le_byte (recv_send (firstn (Z.to_nat (recv_got bytes)) bytes)) 4 j)).
{ intros j Hj. pose proof (rp_chunk_bytes _ (w_H W2) (ms_mem msC) (Some 12%nat) (-1328) (-1324) (-1328) (-1324) _
    (-1328) 4 (SOff 10 0) _ HR0 ltac:(rp_in) ltac:(lia) D10 j Hj) as Hc.
  cbn [base_val] in Hc. rewrite U12 in Hc.
  replace (RECV_RXS_HI + -1328) with TA_g_rx_send in Hc by (unfold RECV_RXS_HI, TA_g_rx_send; lia). exact Hc. }
assert (VL : forall j, (j < 8)%nat -> aview segs (w_H W2) (ms_mem msC) (TA_g_rx_len + Z.of_nat j) =
  Some (YO0f.le_byte (recv_got bytes) 8 j)).
{ intros j Hj. pose proof (rp_chunk_bytes _ (w_H W2) (ms_mem msC) (Some 485%nat) 1644 1652 1644 1652 _
    1644 8 (SOff 11 0) _ HR1 ltac:(rp_in) ltac:(lia) D11 j Hj) as Hc.
  cbn [base_val] in Hc. rewrite U85 in Hc.
  replace (6236628 + 1644) with TA_g_rx_len in Hc by (unfold TA_g_rx_len; lia). exact Hc. }
assert (VR : forall j, (j < 8)%nat -> aview segs (w_H W2) (ms_mem msC) (TA_g_rx + Z.of_nat j) =
  Some (YO0f.le_byte a 8 j)).
{ intros j Hj. pose proof (rp_chunk_bytes _ (w_H W2) (ms_mem msC) (Some 484%nat) (-48) (-40) (-48) (-40) _
    (-48) 8 (SOff 8 0) _ HR2 ltac:(rp_in) ltac:(lia) D8 j Hj) as Hc.
  cbn [base_val] in Hc. rewrite U84 in Hc.
  replace (6158800 + -48) with TA_g_rx in Hc by (unfold TA_g_rx; lia). exact Hc. }
assert (VT : forall j, (j < 4)%nat -> aview segs (w_H W2) (ms_mem msC) (TA_g_rx_times + Z.of_nat j) =
  Some (YO0f.le_byte (if Z.land pf 1 =? 0 then 1 else 2) 4 j)).
{ intros j Hj. pose proof (rp_chunk_bytes _ (w_H W2) (ms_mem msC) (Some 486%nat) 1608 1612 1608 1612 _
    1608 4 _ _ HR3 ltac:(rp_in) ltac:(lia) Dt j Hj) as Hc.
  cbn [base_val] in Hc. rewrite U86, rp_times_eq in Hc.
  replace (6236632 + 1608) with TA_g_rx_times in Hc by (unfold TA_g_rx_times; lia). exact Hc. }
assert (VF : forall j, (j < 4)%nat -> aview segs (w_H W2) (ms_mem msC) (TA_g_rx_fail + Z.of_nat j) =
  Some (YO0f.le_byte (Z.land (Z.shiftr pf 1) 1) 4 j)).
{ intros j Hj. pose proof (rp_chunk_bytes _ (w_H W2) (ms_mem msC) (Some 487%nat) 1568 1572 1568 1572 _
    1568 4 _ _ HR4 ltac:(rp_in) ltac:(lia) Df j Hj) as Hc.
  cbn [base_val] in Hc. rewrite U87 in Hc.
  replace (6236640 + 1568) with TA_g_rx_fail in Hc by (unfold TA_g_rx_fail; lia). exact Hc. }
clear HR0 HR1 HR2 HR3 HR4.
(* the world handed to diginet_session_poll *)
assert (TWX : tw_at TMAP_A (aview segs (w_H W2) memX) (recv_w2 Bw bytes))
  by (apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact HTW | intros x Hx; pose proof (TMAP_A_hull x Hx) as Hh;
      unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh; exact (KDX x ltac:(lia))]).
assert (TWC : tw_at TMAP_A (aview segs (w_H W2) (ms_mem msC)) (recv_w2c Bw bytes a pf)).
{ apply (rp_tw_w2c (aview segs (w_H W2) memX) _ Bw bytes a pf _ _ _ _ eq_refl eq_refl eq_refl eq_refl TWX
    VS VR VL VT VF).
  intros x Hx N1 N2 N3 N4 N5. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR1; [lia|]. unfold rp_Z5. tauto. }
(* the registers at the call *)
rp_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 10152)) C1 ltac:(apply codeptr_val; exact HEI).
rp_kreg HS regsX 2%nat (2%bv : bv 5) P2 C2. rp_kreg HS regsX 3%nat (3%bv : bv 5) P3 C3.
rp_kreg HS regsX 4%nat (4%bv : bv 5) P4 C4. rp_kreg HS regsX 8%nat (8%bv : bv 5) P8 C8.
rp_reg HS (9%bv : bv 5) (Z_to_bv 64 (recv_ticked pf)) C9 ltac:(exact (rp_den_ticked _ _ pf W9 H13)).
assert (E250 : ew (rp_E regsX []) 250 = w64 POLL_S)
  by (rewrite (rp_ew_img regsX [] 250 ltac:(unfold A_TEXT, A_LIM; lia)); unfold w64; f_equal; vm_compute; reflexivity).
assert (E484 : ew (rp_E regsX []) 484 = w64 6158800)
  by (rewrite (rp_ew_img regsX [] 484 ltac:(unfold A_TEXT, A_LIM; lia)); unfold w64; f_equal; vm_compute; reflexivity).
assert (E487 : ew (rp_E regsX []) 487 = w64 6236640)
  by (rewrite (rp_ew_img regsX [] 487 ltac:(unfold A_TEXT, A_LIM; lia)); unfold w64; f_equal; vm_compute; reflexivity).
rp_reg HS (10%bv : bv 5) (w64 POLL_S) C10 ltac:(exact (rp_den_lit _ 250 POLL_S E250 ltac:(unfold POLL_S, TA_g_s; lia))).
rp_reg HS (11%bv : bv 5) (w64 0) C11 ltac:(reflexivity).
rp_reg HS (18%bv : bv 5) (Z_to_bv 64 6158800) C18 ltac:(exact (rp_den_lit _ 484 6158800 E484 ltac:(lia))).
rp_reg HS (19%bv : bv 5) (Z_to_bv 64 6236640) C19 ltac:(exact (rp_den_lit _ 487 6236640 E487 ltac:(lia))).
rp_kreg HS regsX 22%nat (22%bv : bv 5) P22 C22. rp_kreg HS regsX 23%nat (23%bv : bv 5) P23 C23.
rp_kreg HS regsX 24%nat (24%bv : bv 5) P24 C24. rp_kreg HS regsX 25%nat (25%bv : bv 5) P25 C25.
rp_kreg HS regsX 26%nat (26%bv : bv 5) P26 C26. rp_kreg HS regsX 27%nat (27%bv : bv 5) P27 C27.
assert (USPC : spZ (ms_regs msC) = spZ regs - 64)
  by (unfold spZ at 1; rewrite C2; unfold w64; rewrite ERF; apply unsigned_lit_small; lia).
(* the model on this path *)
destruct (rp_model Bw a bytes by_poll pf Bw' ltac:(lia) HBP HM) as (B2d & r & HPM & HSM).
(* the frame at the call *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARC.
assert (FNG : forall x, a <= x < a + Z.max 1 (Z.of_nat (length bytes)) -> ~ inG TG.G_HARNESS x).
{ intros x Hx Hg. exact (blk_img segs B LAWS ly2 S2 W2 memX mdX a _ x HARX Hblk ltac:(lia) (trans_g_img x Hg)). }
assert (FN5 : forall x, a <= x < a + Z.max 1 (Z.of_nat (length bytes)) -> ~ rp_Z5 x)
  by (intros x Hx HZ; exact (FNG x Hx (proj2 (rp_Z5_G x HZ)))).
assert (HBLKC : garr8 segs (mrestrict (w_H W2) (ms_mem msC)) a (TW.zs bytes)).
{ apply (garr8_frame segs (mrestrict (w_H W2) mem2) _ _ _ HBLK). intros x Hx.
  unfold TW.zs in Hx. rewrite length_map in Hx.
  apply can_mbyte_of_aview. rewrite (KR1 x ltac:(lia) (FN5 x ltac:(lia))). exact (KDX x ltac:(lia)). }
assert (PTF : trans_tframe_at B ly2 S2 W2 (ms_mem msC) (ms_regs msC) POLL_STK (Some (TI.TFrame a bytes))).
{ unfold trans_tframe_at. cbn [TI.tf_addr TI.tf_bytes].
  split; [lia|]. split; [exact HBLKC|].
  split; [left; exists a, (Z.max 1 (Z.of_nat (length bytes))); split; [exact Hblk | lia]|].
  unfold decode_off_win. left. rewrite USPC. lia. }
assert (PTFG : trans_tf_off_g (Some (TI.TFrame a bytes))).
{ intros fr Efr x Hx. injection Efr as <-. cbn [TI.tf_addr TI.tf_bytes] in Hx. apply FNG. lia. }
assert (PAP : poll_apart (Some (TI.TFrame a bytes))).
{ intros x Hw fr Efr Hx. injection Efr as <-. cbn [TI.tf_addr TI.tf_bytes] in Hx.
  exact (FNG x ltac:(lia) (rp_poll_wr_G x Hw)). }
assert (PROM : trans_rom_view_rd W2 (ms_mem msC)).
{ pose proof (rp_rom B lyc Sc W memc W2 mem2 _ _ _ HRU HRE HK2 Hrom) as R2r.
  intros x Hx. pose proof (trans_ro_rd_bounds x Hx) as Hb.
  rewrite (KR1 x ltac:(lia) ltac:(unfold rp_Z5, TA_g_rx_send, TA_g_rx, TA_g_rx_len, TA_g_rx_times, TA_g_rx_fail; lia)).
  rewrite KDX by lia. exact (R2r x Hx). }
assert (PIRX : iorecv_rx_in (Some (TI.TFrame a bytes)) (recv_w2c Bw bytes a pf)).
{ unfold iorecv_rx_in. intros _. rewrite (rp_grx_w2c Bw bytes a pf HLB ltac:(lia)).
  pose proof (TC.frame_from_base (TI.TFrame a bytes)) as E. cbn [TI.tf_addr] in E. rewrite E. discriminate. }
destruct (proj1 (proj2 INV) Bw bytes a pf HLB Hrinv) as (I1 & I2 & I4 & I5a & I5b & I4b & I2b).
assert (PRX : poll_rx_each timg_A (Some (TI.TFrame a bytes)) (poll_dn_in (Some (TI.TFrame a bytes)))
  (recv_w2c Bw bytes a pf)).
{ pose proof (Hdn a (conj Ha0 Ha64)) as Hpe. rewrite (proj2 (Z.eqb_neq by_poll 0) HBP) in Hpe. exact Hpe. }
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_diginet_session_poll) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (CPOLL fx STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem msC) md1 (k + 1) (ms_regs msC) 0 r
    (Some (TI.TFrame a bytes)) (recv_w2c Bw bytes a pf) B2d HJ).
  - rewrite C1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - unfold raZ. rewrite C1, VB. rewrite unsigned_lit_small by lia. lia.
  - exact C3.
  - exact C4.
  - exact C10.
  - exact C11.
  - rewrite USPC. replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - lia.
  - exact TWC.
  - rewrite (rp_gfn_w2c Bw bytes a pf HLB). exact Hgf0.
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
assert (T3 : YK11.getr regs3 3 = YK11.getr regs 3)
  by exact (eq_trans (eq_trans (HP3 3 ltac:(hnf; lia)) C3) (eq_sym Hgp)).
assert (T4 : YK11.getr regs3 4 = YK11.getr regs 4)
  by exact (eq_trans (eq_trans (HP3 4 ltac:(hnf; lia)) C4) (eq_sym Htp)).
assert (T8 : YK11.getr regs3 8 = w64 a) by exact (eq_trans (HP3 8 ltac:(hnf; lia)) C8).
assert (T9 : YK11.getr regs3 9 = Z_to_bv 64 (recv_ticked pf)) by exact (eq_trans (HP3 9 ltac:(hnf; lia)) C9).
assert (T18 : YK11.getr regs3 18 = Z_to_bv 64 6158800) by exact (eq_trans (HP3 18 ltac:(hnf; lia)) C18).
assert (T19 : YK11.getr regs3 19 = Z_to_bv 64 6236640) by exact (eq_trans (HP3 19 ltac:(hnf; lia)) C19).
assert (T22 : YK11.getr regs3 22 = YK11.getr regs 22) by exact (eq_trans (HP3 22 ltac:(hnf; lia)) C22).
assert (T23 : YK11.getr regs3 23 = YK11.getr regs 23) by exact (eq_trans (HP3 23 ltac:(hnf; lia)) C23).
assert (T24 : YK11.getr regs3 24 = YK11.getr regs 24) by exact (eq_trans (HP3 24 ltac:(hnf; lia)) C24).
assert (T25 : YK11.getr regs3 25 = YK11.getr regs 25) by exact (eq_trans (HP3 25 ltac:(hnf; lia)) C25).
assert (T26 : YK11.getr regs3 26 = YK11.getr regs 26) by exact (eq_trans (HP3 26 ltac:(hnf; lia)) C26).
assert (T27 : YK11.getr regs3 27 = YK11.getr regs 27) by exact (eq_trans (HP3 27 ltac:(hnf; lia)) C27).
(* what the call has kept up to diginet_session_poll's return *)
assert (ELF2 : ly_F ly2 = ly_F lyc).
{ pose proof HJ2 as (_ & _ & (memS2 & HJ2i & _) & _). pose proof HJ2i as (_ & Hly2 & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & E2 & _). pose proof Hlyc as (_ & _ & _ & _ & _ & Ec & _).
  rewrite E2, Ec. reflexivity. }
assert (K1 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem msC) (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 W2 (ms_mem msC) (spZ regs - RECV_STK) (spZ regs)
    (spZ regs) (spZ regs) (recv_wr bytes) (fun _ => False) Hce ltac:(lia) HK2); [| lia | lia | tauto].
  apply (rp_kept_run B lyc Sc W memc mdc W2 mem2 (ms_mem msC) (spZ regs) (fun _ => False) rp_Z5 LAWS HARc).
  - intros x Hx. exact (rp_Z5_G x Hx).
  - intros x Hx Hnz. rewrite (KR1 x Hx Hnz). exact (KDX x Hx).
  - intros x Hx. exact (GA1 x (GRX x Hx)). }
assert (K2 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 (ms_mem msC) W3 mem3 (spZ regs - RECV_STK)
    (spZ regs) (spZ (ms_regs msC) - POLL_STK) (spZ (ms_regs msC)) (recv_wr bytes) poll_wr (fun _ => False)
    Hce ltac:(lia)).
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
(* +0x23c .. +0x244: the two stores of 0, `j` to the set cut *)
rewrite C1. change (Z_to_bv 64 (BASE + 10152)) with (Z_to_bv 64 (BASE + RP_RET)).
pose proof (@rp_entryT fx rc W3 regs3 mem3 T18 T19) as HST.
assert (SHOKT : sh_ok segs RP_BX (@nil shent) (rp_E regs3 []) (mrestrict (w_H W3) mem3)) by constructor.
assert (HEIT : img_env VAL A_LIM (rp_E regs3 [])) by apply rp_env_img.
pose proof (rp_ureg regs3 [] 18 18%bv 6158800 eq_refl T18 ltac:(lia)) as V18.
pose proof (rp_ureg regs3 [] 19 19%bv 6236640 eq_refl T19 ltac:(lia)) as V19.
paj_run_to_tok RUNTO HST HJ3 SHOKT RP_B0 RECV_SET.
{ rp_awr_rs.
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite V18 in Hx;
    apply (rp_inG_row _ _ _ x TMAP_A_g_rx); unfold TA_g_rx, TW.SZ_g_rx in *; lia |].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite V19 in Hx;
    apply (rp_inG_row _ _ _ x TMAP_A_g_rx_fail); unfold TA_g_rx_fail, TW.SZ_g_rx_fail in *; lia |].
  apply awr_ok_x_nil. }
set (mdT := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdT. clear mat.
lazymatch type of HST with context [restrict _ ?mf] => rename mf into msT end.
assert (KR2 : forall x, 0 <= x < 2 ^ 64 -> ~ rp_Z2 x -> aview segs (w_H W3) (ms_mem msT) x = aview segs (w_H W3) mem3 x).
{ intros x Hx Hnz. apply (kept_of_frame _ _ _ _ _ rp_Z2 HFr); [| exact Hx | exact Hnz].
  intros b wlo whi y Hin Hy. cbv beta.
  lazymatch type of Hin with In ?z ?l => let l' := eval vm_compute in l in change (In z l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hy;
    rewrite ?V18, ?V19 in Hy; unfold rp_Z2, TA_g_rx, TA_g_rx_fail in Hy |- *; lia |]).
  destruct Hin. }
assert (GA2 : forall x, apresent (w_H W3) mem3 x -> apresent (w_H W3) (ms_mem msT) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
rp_region HST 0%nat HT0. rp_region HST 1%nat HT1.
assert (VR2 : forall j, (j < 8)%nat -> aview segs (w_H W3) (ms_mem msT) (TA_g_rx + Z.of_nat j) =
  Some (YO0f.le_byte 0 8 j)).
{ intros j Hj. pose proof (rp_chunk_bytes _ (w_H W3) (ms_mem msT) (Some 18%nat) (-48) (-40) (-48) (-40) _
    (-48) 8 _ 0 HT0 ltac:(rp_in) ltac:(lia) ltac:(reflexivity) j Hj) as Hc.
  cbn [base_val] in Hc. rewrite V18 in Hc.
  replace (6158800 + -48) with TA_g_rx in Hc by (unfold TA_g_rx; lia). exact Hc. }
assert (VF2 : forall j, (j < 4)%nat -> aview segs (w_H W3) (ms_mem msT) (TA_g_rx_fail + Z.of_nat j) =
  Some (YO0f.le_byte 0 4 j)).
{ intros j Hj. pose proof (rp_chunk_bytes _ (w_H W3) (ms_mem msT) (Some 19%nat) 1568 1572 1568 1572 _
    1568 4 _ 0 HT1 ltac:(rp_in) ltac:(lia) ltac:(reflexivity) j Hj) as Hc.
  cbn [base_val] in Hc. rewrite V19 in Hc.
  replace (6236640 + 1568) with TA_g_rx_fail in Hc by (unfold TA_g_rx_fail; lia). exact Hc. }
clear HT0 HT1.
(* the world settle is handed *)
assert (HLB2 : length B2d = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw3).
assert (TWT : tw_at TMAP_A (aview segs (w_H W3) (ms_mem msT)) (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0)).
{ apply (rp_tw_w3 (aview segs (w_H W3) mem3) _ B2d Htw3 VR2 VF2).
  intros x Hx N1 N2. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR2; [lia|]. unfold rp_Z2. tauto. }
assert (GFT : TW.g_fail_next (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0) <= 1)
  by (rewrite (rp_gfn_w3 B2d HLB2); exact Hgf3).
pose proof (proj2 (proj2 (proj2 (proj2 INV))) Bw bytes a pf (Some (TI.TFrame a bytes)) B2d r HLB Hrinv HPM) as RINVT.
(* what every cut carries, at the set cut *)
assert (CURT : recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly3 S3 W3 (ms_mem msT) mdT).
{ refine (conj HJ3 (conj (eq_trans Hfr3 Hfrs) (conj (Permutation_trans Hperm3 Hperm) (conj _ (conj _ (conj _ Ha4096)))))).
  - rewrite <- (Z.add_0_r (mo_malloc MT (Z.max 1 (Z.of_nat (length bytes))))).
    exact (mo_le_trans MT MTL _ _ _ _ _ Hmo2 Hmo3).
  - apply (dk_kept_trans_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 W3 (ms_mem msT) (spZ regs - RECV_STK) (spZ regs)
      (spZ regs) (spZ regs) (recv_wr bytes) (fun _ => False) Hce ltac:(lia) K2); [| lia | lia | tauto].
    apply (rp_kept_run B lyc Sc W memc mdc W3 mem3 (ms_mem msT) (spZ regs) (fun _ => False) rp_Z2 LAWS HARc).
    + intros x Hx. exact (rp_Z2_G x Hx).
    + intros x Hx Hnz. exact (KR2 x Hx Hnz).
    + intros x Hx. exact (GA2 x Hx).
  - rewrite Forall_forall in Hsv2 |- *. intros o Ho. rewrite <- (Hsv2 o Ho).
    assert (Hob : 8 <= fst o <= 56).
    { unfold RECV_SAVED in Ho. cbn [In] in Ho. repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
    apply rdword_ext. intros i Hi.
    pose proof (HK3) as (KK1 & _).
    rewrite KR2 by (try lia; intros HZ; destruct (rp_Z2_G _ HZ) as [Hl _]; lia).
    rewrite KK1 by (rewrite ?USPC; lia).
    rewrite KR1 by (try lia; intros HZ; destruct (rp_Z5_G _ HZ) as [Hl _]; lia).
    apply KDX. lia. }
(* the registers at the set cut *)
pmkst HST.
rp_kreg HST regs3 2%nat (2%bv : bv 5) T2 Z2r. rp_kreg HST regs3 3%nat (3%bv : bv 5) T3 Z3r.
rp_kreg HST regs3 4%nat (4%bv : bv 5) T4 Z4r. rp_kreg HST regs3 8%nat (8%bv : bv 5) T8 Z8r.
rp_kreg HST regs3 9%nat (9%bv : bv 5) T9 Z9r.
rp_kreg HST regs3 22%nat (22%bv : bv 5) T22 Z22r. rp_kreg HST regs3 23%nat (23%bv : bv 5) T23 Z23r.
rp_kreg HST regs3 24%nat (24%bv : bv 5) T24 Z24r. rp_kreg HST regs3 25%nat (25%bv : bv 5) T25 Z25r.
rp_kreg HST regs3 26%nat (26%bv : bv 5) T26 Z26r. rp_kreg HST regs3 27%nat (27%bv : bv 5) T27 Z27r.
assert (REGST : recv_regs_set regs (ms_regs msT) a (recv_ticked pf)).
{ refine (conj (conj Z2r (conj Z3r (conj Z4r (conj Z22r (conj Z23r (conj Z24r (conj Z25r (conj Z26r Z27r))))))))
    (conj Z8r Z9r)). }
exact (SET LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly3 S3
  W3 (ms_mem msT) mdT (ms_regs msT) (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0) (recv_ticked pf) HFIX CURT HRES TWT GFT
  RINVT HSM (rp_ticked_range pf) REGST).
Qed.

(* From a phase's last run to the send cut: a0 = the send value (by SVt), a1 = got, a2 = RECV_RXS_HI (X10, X11,
   X12), the callee-saved registers kept (HPX). *)
Ltac rp_toSend RUNTO HS HJ SHOK regsB xs F11 F12 W2 mem2 KV GV SVt :=
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan RP_SEND; [rp_awr0 |];
  rp_md; rp_kv HS W2 mem2 KV GV; pmkst HS;
  let X10 := fresh "X10" in let X11 := fresh "X11" in let X12 := fresh "X12" in let HPX := fresh "HPX" in
  rp_reg HS (10%bv : bv 5) (w64 (recv_send (firstn (Z.to_nat (recv_got bytes)) bytes))) X10 SVt;
  rp_kregE HS regsB xs 11%nat (11%bv : bv 5) F11 X11;
  rp_kregE HS regsB xs 12%nat (12%bv : bv 5) F12 X12;
  rp_pres HS regsB xs HPX.

(* +0x164 .. +0x1f4 and +0x320 .. +0x398 (n >= 30): the ethertype, numbytes and length tests on the first got bytes,
   the send value in a0. *)
Lemma rp_atF : forall ly2 S2 (W2 : world segs) mem2 md2 regs2 regsF memF mdF,
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
  recv_blk W2 mem2 a bytes ->
  tw_at TMAP_A (aview segs (w_H W2) mem2) (recv_w2 Bw bytes) ->
  recv_regs_poll regs regs2 by_poll a bytes ->
  JX ly2 S2 W2 memF mdF ->
  (forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) memF x = aview segs (w_H W2) mem2 x) ->
  (forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) memF x) ->
  aregs_preserved regs2 regsF ->
  YK11.getr regsF 11 = w64 (recv_got bytes) -> YK11.getr regsF 12 = w64 RECV_RXS_HI ->
  30 <= Z.of_nat (length bytes) ->
  SRr segs W2 (CFG RP_F regsF memF mdF) POST.
Proof.
intros ly2 S2 W2 mem2 md2 regs2 regsF memF mdF HCUR HBLK HTW HREGS HJ KV GV HPF F11 F12 H30.
pose proof LAWS0 as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
pose proof HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hch & Hal & Hwlo & Hwhi & Hbp & Hpf &
  Hn & Hgarr & Hsrc & Htw0 & Hgf0 & Hmod & Hrom & Hrinv & Hdn & Q1c & Q2c & Q3c & Q4c & Q5c & Hnev & Hlive & Hmo &
  Hcost & Htrm & Htrf).
pose proof HREGS as (((R2 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27) & R8 & R9 & R18 & R19 & R21) & R12).
pose proof HCUR as (HJ2 & Hfrs & Hperm & Hmo2 & HK2 & Hsv2 & Ha4096).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof (rp_got_range bytes) as (Rg1 & Rg2 & Rg3 & Rg4).
assert (Hgot30 : 30 <= recv_got bytes).
{ destruct (Z_lt_le_dec (Z.of_nat (length bytes)) 1514) as [Hl | Hl]; [rewrite (Rg3 Hl) | rewrite (Rg4 Hl)]; lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARF.
assert (Hblk : In (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 memF mdF _ _ HARF Hblk) as (_ & _ & Hbce & _ & _).
pose proof (req_size_pos (Z.max 1 (Z.of_nat (length bytes))) ltac:(lia)) as [_ Hreq].
assert (F8 : YK11.getr regsF 8 = w64 a) by exact (eq_trans (HPF 8 ltac:(hnf; lia)) R8).
assert (F18 : YK11.getr regsF 18 = w64 (Z.of_nat (length bytes)))
  by exact (eq_trans (HPF 18 ltac:(hnf; lia)) R18).
assert (F21 : YK11.getr regsF 21 = w64 SHADOW_OFF) by exact (eq_trans (HPF 21 ltac:(hnf; lia)) R21).
assert (HBLKF : garr8 segs (mrestrict (w_H W2) memF) a (TW.zs bytes)).
{ apply (garr8_frame segs (mrestrict (w_H W2) mem2) _ _ _ HBLK). intros x Hx.
  unfold TW.zs in Hx. rewrite length_map in Hx.
  apply can_mbyte_of_aview. exact (KV x ltac:(lia)). }
assert (HRD : decode_rd_ok W2 memF a (Z.of_nat (length bytes))).
{ apply (trans_src_ok_rd B LAWS ly2 S2 W2 memF mdF a _ HARF); [|lia].
  left. exists a, (Z.max 1 (Z.of_nat (length bytes))). split; [exact Hblk | lia]. }
destruct (@rp_entryF fx rc W2 regsF memF a bytes (recv_got bytes) F8 F11 F18 F21 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) HBLKF HRD) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (rp_E regsF (rp_fvals bytes))) by apply rp_env_img.
pose proof (rp_ew_x regsF (rp_fvals bytes) 0 ltac:(lia)) as A32.
pose proof (rp_ew_x regsF (rp_fvals bytes) 1 ltac:(lia)) as A33.
pose proof (rp_ew_x regsF (rp_fvals bytes) 2 ltac:(lia)) as A34.
pose proof (rp_ew_x regsF (rp_fvals bytes) 3 ltac:(lia)) as A35.
pose proof (rp_ew_x regsF (rp_fvals bytes) 4 ltac:(lia)) as A36.
pose proof (rp_ew_x regsF (rp_fvals bytes) 5 ltac:(lia)) as A37.
pose proof (rp_ew_x regsF (rp_fvals bytes) 6 ltac:(lia)) as A38.
pose proof (rp_ew_x regsF (rp_fvals bytes) 7 ltac:(lia)) as A39.
cbn [Nat.add nth rp_fvals] in A32, A33, A34, A35, A36, A37, A38, A39.
assert (A11 : ew (rp_E regsF (rp_fvals bytes)) 11 = w64 (recv_got bytes))
  by exact (eq_trans (rp_ew regsF (rp_fvals bytes) 11 11%bv eq_refl) F11).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
(* run 1, +0x164 .. +0x1a4: the checked loads at a + 12, a + 13; `bne` on the ethertype *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan RP_SEND; [rp_awr0 |].
rp_md. rp_kv HS W2 mem2 KV GV.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan;
  (let EF := rp_curE HS in rewrite (rp_br_et EF bytes ltac:(rp_ewv; exact A32) ltac:(rp_ewv; exact A33)) in Hc).
1: { apply negb_true_iff, Z.eqb_neq in Hc. pose proof (rp_snd_et bytes H30 Hc) as SV.
     rp_toSend RUNTO HS HJ SHOK regsF (rp_fvals bytes) F11 F12 W2 mem2 KV GV ltac:(rewrite SV; reflexivity).
     exact (rp_send _ _ _ _ _ _ _ _ _ HCUR HBLK HTW HREGS HJ KV GV (aregs_preserved_trans _ _ _ HPF HPX) X10 X11 X12). }
apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HET.
(* run 2, +0x1a8 .. +0x1e4: the checked loads at a + 14, a + 15; `bltu` on numbytes < 16 *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan RP_SEND; [rp_awr0 |].
rp_md. rp_kv HS W2 mem2 KV GV.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan;
  (let EF := rp_curE HS in rewrite (rp_br_nb EF bytes ltac:(rp_ewv; exact A34) ltac:(rp_ewv; exact A35)) in Hc).
1: { apply Z.ltb_lt in Hc. pose proof (rp_snd_nb bytes H30 HET Hc) as SV.
     rp_toSend RUNTO HS HJ SHOK regsF (rp_fvals bytes) F11 F12 W2 mem2 KV GV ltac:(rewrite SV; reflexivity).
     exact (rp_send _ _ _ _ _ _ _ _ _ HCUR HBLK HTW HREGS HJ KV GV (aregs_preserved_trans _ _ _ HPF HPX) X10 X11 X12). }
apply Z.ltb_ge in Hc. rename Hc into HNB.
(* run 3, +0x1e8 .. +0x1ec: `bgeu` on got - 14 >= numbytes *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan RP_SEND; [rp_awr0 |].
rp_md. rp_kv HS W2 mem2 KV GV.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan;
  (let EF := rp_curE HS in
   rewrite (rp_br_len EF bytes (recv_got bytes) ltac:(rp_ewv; exact A11) ltac:(lia) ltac:(rp_ewv; exact A34)
     ltac:(rp_ewv; exact A35)) in Hc).
1: { apply negb_true_iff, Z.ltb_ge in Hc. pose proof (rp_snd_ok bytes H30 HET HNB Hc) as SV.
     (* +0x320 .. +0x398: the checked loads at a + 18 .. a + 21, the big-endian send value *)
     rp_toSend RUNTO HS HJ SHOK regsF (rp_fvals bytes) F11 F12 W2 mem2 KV GV
       ltac:(rewrite SV, rp_be32;
             lazymatch goal with |- sv_denot ?EF _ = _ =>
               exact (rp_den_be32 EF _ _ _ _ ltac:(rp_ewv; exact A36) ltac:(rp_ewv; exact A37)
                 ltac:(rp_ewv; exact A38) ltac:(rp_ewv; exact A39) (rp_at8_range _ _) (rp_at8_range _ _)
                 (rp_at8_range _ _) (rp_at8_range _ _)) end).
     exact (rp_send _ _ _ _ _ _ _ _ _ HCUR HBLK HTW HREGS HJ KV GV (aregs_preserved_trans _ _ _ HPF HPX) X10 X11 X12). }
apply negb_false_iff, Z.ltb_lt in Hc. pose proof (rp_snd_big bytes H30 HET HNB Hc) as SV.
rp_toSend RUNTO HS HJ SHOK regsF (rp_fvals bytes) F11 F12 W2 mem2 KV GV ltac:(rewrite SV; reflexivity).
exact (rp_send _ _ _ _ _ _ _ _ _ HCUR HBLK HTW HREGS HJ KV GV (aregs_preserved_trans _ _ _ HPF HPX) X10 X11 X12).
Qed.

(* +0x15c .. +0x160: `bltu` on n < 30 (got < 30): the send value 0, else the frame's tests. *)
Lemma rp_atG : forall ly2 S2 (W2 : world segs) mem2 md2 regs2 regsG memG mdG,
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
  recv_blk W2 mem2 a bytes ->
  tw_at TMAP_A (aview segs (w_H W2) mem2) (recv_w2 Bw bytes) ->
  recv_regs_poll regs regs2 by_poll a bytes ->
  JX ly2 S2 W2 memG mdG ->
  (forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) memG x = aview segs (w_H W2) mem2 x) ->
  (forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) memG x) ->
  aregs_preserved regs2 regsG ->
  YK11.getr regsG 11 = w64 (recv_got bytes) -> YK11.getr regsG 12 = w64 RECV_RXS_HI ->
  SRr segs W2 (CFG RP_GOT regsG memG mdG) POST.
Proof.
intros ly2 S2 W2 mem2 md2 regs2 regsG memG mdG HCUR HBLK HTW HREGS HJ KV GV HPG F11 F12.
pose proof LAWS0 as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
pose proof HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hch & Hal & Hwlo & Hwhi & Hbp & Hpf &
  Hn & _).
pose proof HREGS as (((R2 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27) & R8 & R9 & R18 & R19 & R21) & R12).
pose proof (rp_got_range bytes) as (Rg1 & Rg2 & Rg3 & Rg4).
assert (G18 : YK11.getr regsG 18 = w64 (Z.of_nat (length bytes)))
  by exact (eq_trans (HPG 18 ltac:(hnf; lia)) R18).
pose proof (@rp_entryG fx rc W2 regsG memG (Z.of_nat (length bytes)) (recv_got bytes) G18 ltac:(lia) F11 ltac:(lia))
  as HS.
assert (SHOK : sh_ok segs RP_BX (@nil shent) (rp_E regsG []) (mrestrict (w_H W2) memG)) by constructor.
assert (HEI : img_env VAL A_LIM (rp_E regsG [])) by apply rp_env_img.
assert (A18 : ew (rp_E regsG []) 18 = w64 (Z.of_nat (length bytes)))
  by exact (eq_trans (rp_ew regsG [] 18 18%bv eq_refl) G18).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
paj_run_to_tok RUNTO HS HJ SHOK RP_B0 RP_F; [rp_awr0 |].
rp_md. rp_kv HS W2 mem2 KV GV.
psrr_branch_tok RUN BR HS SHOK RP_B0;
  (let EF := rp_curE HS in
   rewrite (rp_br_n EF (Z.of_nat (length bytes)) 30 ltac:(rp_ewv; exact A18) ltac:(lia) ltac:(lia)) in Hc).
1: { apply Z.ltb_lt in Hc. pose proof (rp_snd_lt30 bytes Hc) as SV.
     (* +0x1f0: a0 = 0 *)
     paj_run_to_tok RUNTO HS HJ SHOK RP_B0 RP_SEND; [rp_awr0 |].
     rp_md. rp_kv HS W2 mem2 KV GV. pmkst HS.
     rp_reg HS (10%bv : bv 5) (w64 (recv_send (firstn (Z.to_nat (recv_got bytes)) bytes))) X10
       ltac:(rewrite SV; reflexivity).
     rp_kregE HS regsG (@nil word) 11%nat (11%bv : bv 5) F11 X11.
     rp_kregE HS regsG (@nil word) 12%nat (12%bv : bv 5) F12 X12.
     rp_pres HS regsG (@nil word) HPX.
     exact (rp_send _ _ _ _ _ _ _ _ _ HCUR HBLK HTW HREGS HJ KV GV (aregs_preserved_trans _ _ _ HPG HPX) X10 X11 X12). }
apply Z.ltb_ge in Hc.
paj_run_to_tok RUNTO HS HJ SHOK RP_B0 RP_F; [rp_awr0 |].
rp_md. rp_kv HS W2 mem2 KV GV. pmkst HS.
rp_kregE HS regsG (@nil word) 11%nat (11%bv : bv 5) F11 Y11.
rp_kregE HS regsG (@nil word) 12%nat (12%bv : bv 5) F12 Y12.
rp_pres HS regsG (@nil word) HPY.
exact (rp_atF _ _ _ _ _ _ _ _ _ HCUR HBLK HTW HREGS HJ KV GV (aregs_preserved_trans _ _ _ HPG HPY) Y11 Y12 Hc).
Qed.

(* +0x14c .. +0x158: got = min (n, 1514) in a1. *)
Lemma rp_main : forall ly2 S2 (W2 : world segs) mem2 md2 regs2,
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
  recv_blk W2 mem2 a bytes ->
  tw_at TMAP_A (aview segs (w_H W2) mem2) (recv_w2 Bw bytes) ->
  recv_regs_poll regs regs2 by_poll a bytes ->
  SRr segs W2 (CFG RECV_POLL regs2 mem2 md2) POST.
Proof.
intros ly2 S2 W2 mem2 md2 regs2 HCUR HBLK HTW HREGS.
pose proof LAWS0 as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
pose proof HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hch & Hal & Hwlo & Hwhi & Hbp & Hpf &
  Hn & _).
pose proof HREGS as (((R2 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27) & R8 & R9 & R18 & R19 & R21) & R12).
pose proof HCUR as (HJ & _).
pose proof (rp_got_range bytes) as (Rg1 & Rg2 & Rg3 & Rg4).
pose proof (@rp_entry0 fx rc W2 regs2 mem2 (Z.of_nat (length bytes)) R18 ltac:(lia)) as HS.
assert (SHOK : sh_ok segs RP_BX (@nil shent) (rp_E regs2 []) (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI : img_env VAL A_LIM (rp_E regs2 [])) by apply rp_env_img.
assert (A18 : ew (rp_E regs2 []) 18 = w64 (Z.of_nat (length bytes)))
  by exact (eq_trans (rp_ew regs2 [] 18 18%bv eq_refl) R18).
assert (KV : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) mem2 x = aview segs (w_H W2) mem2 x)
  by reflexivity.
assert (GV : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) mem2 x) by (intros x Hx; exact Hx).
assert (HP0 : aregs_preserved regs2 regs2) by (intros r _; reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
paj_run_to_tok RUNTO HS HJ SHOK RP_B0 RP_GOT; [rp_awr0 |].
rp_md. rp_kv HS W2 mem2 KV GV.
psrr_branch_tok RUN BR HS SHOK RP_B0;
  (let EF := rp_curE HS in
   rewrite (rp_br_n EF (Z.of_nat (length bytes)) 1514 ltac:(rp_ewv; exact A18) ltac:(lia) ltac:(lia)) in Hc).
1: { apply Z.ltb_lt in Hc.
     paj_run_to_tok RUNTO HS HJ SHOK RP_B0 RP_GOT; [rp_awr0 |].
     rp_md. rp_kv HS W2 mem2 KV GV. pmkst HS.
     rp_reg HS (11%bv : bv 5) (w64 (recv_got bytes)) G11
       ltac:(rewrite (Rg3 Hc); lazymatch goal with |- sv_denot ?EF _ = _ =>
               exact (rp_den_lit EF 18 _ ltac:(rp_ewv; exact A18) ltac:(lia)) end).
     rp_kregE HS regs2 (@nil word) 12%nat (12%bv : bv 5) R12 G12.
     rp_pres HS regs2 (@nil word) HPG.
     exact (rp_atG _ _ _ _ _ _ _ _ _ HCUR HBLK HTW HREGS HJ KV GV HPG G11 G12). }
apply Z.ltb_ge in Hc.
(* +0x158: a1 = 1514 *)
paj_run_to_tok RUNTO HS HJ SHOK RP_B0 RP_GOT; [rp_awr0 |].
rp_md. rp_kv HS W2 mem2 KV GV. pmkst HS.
rp_reg HS (11%bv : bv 5) (w64 (recv_got bytes)) G11 ltac:(rewrite (Rg4 Hc); reflexivity).
rp_kregE HS regs2 (@nil word) 12%nat (12%bv : bv 5) R12 G12.
rp_pres HS regs2 (@nil word) HPG.
exact (rp_atG _ _ _ _ _ _ _ _ _ HCUR HBLK HTW HREGS HJ KV GV HPG G11 G12).
Qed.
End m.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma recv_poll : @recv_poll_stmt fx rc B MT.
Proof.
  intros INV SET LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a
    Bw' ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HRES HBLK HTW HBP HREGS.
  exact (rp_main B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' LAWS0
    CALLS INV SET HFIX HRES HBP ly2 S2 W2 mem2 md2 regs2 HCUR HBLK HTW HREGS).
Qed.
End s.
