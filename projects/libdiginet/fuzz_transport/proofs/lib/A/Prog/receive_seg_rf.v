(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module names changed; 790 of its 890 lines of code are new or changed and 930 lines of the source are left out. *)
(* receive_seg_rf: Lemma recv_rf : recv_rf_stmt (lib/A/Prog/receive_seg_cut.v), the rf piece of the image-A ASan walk
   of receive (fuzz_transport.asan 0x837d0 = transport_sigma TS_receive, statement lib/A/Prog/receive_cg.v), from the
   rf cut RECV_RF (+0x0ac, 0x8387c) to the poll cut RECV_POLL (+0x14c, by_poll <> 0) or the mrx cut RECV_MRX (+0x248,
   by_poll = 0). The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 []) at k + 1
   events; the runs are lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x. The code (spec_read_frame inlined,
   fuzz_transport.c:1002-1003):
     +0x0ac            `bltu s2, a2` with a2 = 30 (recv_regs_rf): n < 30 goes to +0x13c;
     +0x0b0 .. +0x0f0  the instrumented checks and 1-byte loads at a + 12, a + 13 (s0 = a, s5 = the shadow base); the
                       big-endian ethertype <> 0x885f goes to +0x13c;
     +0x0f4 .. +0x138  the checks and loads at a + 14, a + 15: numbytes < 16 goes to +0x13c; n - 14 >= numbytes
                       (unsigned) goes to +0x2a4, else falls to +0x13c;
     +0x2a4 .. +0x31c  the checks and loads at a + 18 .. a + 21, a0 = the big-endian send value, `j` +0x140;
     +0x13c            a0 = 0;
     +0x140 .. +0x144  a2 = the PHi of g_rx_send (A_OBJ 83's high part, RECV_RXS_HI), `sw a0, -0x530(a2)`;
     +0x148            `beqz s3`: by_poll = 0 goes to +0x248 (RECV_MRX), else falls to +0x14c (RECV_POLL).
   Every check is decided by the run's shadow entry of the frame's first 30 bytes (rf_entryL, when n >= 30): they are
   bytes of the block (a, max (n, 1)) of recv_cur's blocks, usable by AR_shadow_law's block shadow (YCbq.v
   range_addressable_of_block), so no error path (+0x3a4 ..) is reached. The loaded bytes are the frame's
   (recv_blk), and the code's tests decide receive_cg.v recv_send bytes through the plain walk's lemmas
   (lib/Prog/T/receive.v rb_snd_short, rb_snd_eth, rb_snd_len, rb_snd_ok). The store at +0x144 is a byte of G
   (awr_ok_x_cons_g); TWorldG.v tw_write of put 4 (recv_send bytes) at g_rx_send gives the world relation at
   recv_w2 Bw bytes. What the call kept (acall_kept_g over recv_wr bytes) is carried by TransportGFrame.v
   dk_kept_step_gw (the four bytes of g_rx_send are in recv_wr bytes and in G), the saved words and the frame's
   bytes are outside them (rf_cur_step). Pieces of the proof: rf_store (from +0x140 with a0 = recv_send bytes to
   the two cuts), rf_join (the facts carried to the memory of a run that wrote nothing), recv_rf (the tests). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit TransportGFrame.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require receive m_rx_epi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module RPL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.receive.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* g_rx_send's four bytes, the only bytes the piece stores. *)
Definition rf_rxs (x : Z) : Prop := TA_g_rx_send <= x < TA_g_rx_send + 4.
(* The registers the piece never writes and the cuts read: sp, gp, tp, s0 .. s3, s5 .. s11. *)
Definition rf_keepl : list Z := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27].

(* A state with no region (the short frame, the branch at +0x148). *)
Definition rf_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
(* The state at +0x140: g_rx_send's four bytes, based at the PHi atom of A_OBJ 83 (A_HI 83 = atom 483, a2 after
   +0x140), writable; the atom's value is RECV_RXS_HI (the fact the token engine's window check reads). *)
Definition rf_rxs_region : YP09.region := YP09.mkRegion (Some 483%nat) (-1328) (-1324) (-1328) (-1324) [].
Definition rf_ssS : sstate :=
  mkSS (RECV_RF + 148) sr_atoms [rf_rxs_region] None (mkFacts [(483%nat, mkAF RECV_RXS_HI RECV_RXS_HI 0)] [] []).
(* The state at the rf cut when n >= 30: the frame's eight loaded bytes as atoms 32 .. 39, based at s0 = a (read
   only); the shadow entry of the frame's first 30 bytes; the shadow base is s5. *)
Definition rf_frame : YP09.region := YP09.mkRegion (Some 8%nat) 12 22 0 0
  [YP09.mkChunk 12 (CVal 1 (SOff 32 0)); YP09.mkChunk 13 (CVal 1 (SOff 33 0));
   YP09.mkChunk 14 (CVal 1 (SOff 34 0)); YP09.mkChunk 15 (CVal 1 (SOff 35 0));
   YP09.mkChunk 18 (CVal 1 (SOff 36 0)); YP09.mkChunk 19 (CVal 1 (SOff 37 0));
   YP09.mkChunk 20 (CVal 1 (SOff 38 0)); YP09.mkChunk 21 (CVal 1 (SOff 39 0))].
Definition rf_facts : facts :=
  mkFacts [(8%nat, mkAF 0 (2 ^ 47 - 31) 0); (21%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
           (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0)] [] [].
Definition rf_ssL : sstate := mkSS RECV_RF sr_atoms [rf_frame] None rf_facts.
Definition RF_SH : list shent := [mkSHE 8 0 30].
Definition RF_Bx : sv := SOff 21 0.

(* Byte c of the frame, as the block holds it (recv_blk's garr8 of TW.zs bytes). *)
Definition rfb (bytes : list byte) (c : Z) : Z := nth (Z.to_nat c) (TW.zs bytes) 0.
Definition rf_vals (bytes : list byte) : list word :=
  [w64 (rfb bytes 12); w64 (rfb bytes 13); w64 (rfb bytes 14); w64 (rfb bytes 15);
   w64 (rfb bytes 18); w64 (rfb bytes 19); w64 (rfb bytes 20); w64 (rfb bytes 21)].

(* ------------------------------------------------------------------ *)
(* Facts of the model and of the bytes                                 *)
(* ------------------------------------------------------------------ *)

Lemma rf_rxs_G : forall x, rf_rxs x -> inG TG.G_HARNESS x.
Proof.
intros x Hx. unfold inG. apply Exists_exists. exists (TA_g_rx_send, TW.SZ_g_rx_send). split.
- exact (TMAP_A_in_G _ _ _ TMAP_A_g_rx_send).
- unfold in_zr, rf_rxs, TW.SZ_g_rx_send in *. cbn [fst snd]. lia.
Qed.

Lemma rf_rxs_wr : forall bytes x, rf_rxs x -> recv_wr bytes x.
Proof. intros bytes x Hx. unfold recv_wr. right; right; right; left. unfold twa_fld, rf_rxs, TW.SZ_g_rx_send in *. lia. Qed.

Lemma rf_req_ge : forall x, x <= req_size x.
Proof. intros x. unfold req_size. destruct (Z.eqb_spec x 0); lia. Qed.

Lemma rfb_at8 : forall bytes c, rfb bytes c = DSpec.at8 bytes (Z.to_nat c).
Proof.
intros bytes c. unfold rfb, TW.zs, DSpec.at8, DSpec.bz.
transitivity (nth (Z.to_nat c) (map bv_unsigned bytes) (bv_unsigned (DSpec.b8 0))); [reflexivity | apply map_nth].
Qed.

Lemma rfb_range : forall bytes c, 0 <= rfb bytes c < 256.
Proof. intros bytes c. rewrite rfb_at8. apply RPL.r_at8_range. Qed.

Lemma rf_be16 : forall bytes, DSpec.be16 bytes 12 = rfb bytes 12 * 2 ^ 8 + rfb bytes 13 /\
  DSpec.be16 bytes 14 = rfb bytes 14 * 2 ^ 8 + rfb bytes 15.
Proof. intros bytes. rewrite !rfb_at8. split; reflexivity. Qed.

Lemma rf_be32 : forall bytes,
  DSpec.be32 bytes 18 = rfb bytes 18 * 2 ^ 24 + rfb bytes 19 * 2 ^ 16 + rfb bytes 20 * 2 ^ 8 + rfb bytes 21.
Proof. intros bytes. rewrite !rfb_at8. reflexivity. Qed.

(* receive_cg.v's recv_send is the plain walk's rb_snd. *)
Lemma rf_send_eq : forall b, recv_send b = RPL.rb_snd b.
Proof. reflexivity. Qed.

Lemma rf_send_range : forall b, 0 <= recv_send b < 2 ^ 32.
Proof.
intros b. unfold recv_send. destruct (DSpec.fr_code b =? 0); [|lia].
unfold DSpec.fr_send, DSpec.be32.
pose proof (RPL.r_at8_range b 18). pose proof (RPL.r_at8_range b 19).
pose proof (RPL.r_at8_range b 20). pose proof (RPL.r_at8_range b 21). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Denotations of the code's values                                    *)
(* ------------------------------------------------------------------ *)

Lemma rf_lor_add : forall x y k, 0 <= k -> x mod 2 ^ k = 0 -> 0 <= y < 2 ^ k -> Z.lor x y = x + y.
Proof.
intros x y k Hk Hx Hy. symmetry. apply Z.add_nocarry_lor.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec i k) as [Hl|Hl].
- rewrite <- (Z.mod_pow2_bits_low x k i) by lia. rewrite Hx, Z.bits_0. reflexivity.
- rewrite <- (Z.mod_small y (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

Lemma rf_den_atom : forall E j x, ew E j = w64 x -> 0 <= x < 2 ^ 64 -> sv_denot E (SOff j 0) = Z_to_bv 64 x.
Proof.
intros E j x H R. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by lia.
rewrite Z.add_0_r. reflexivity.
Qed.

Lemma rf_den_sll : forall E e x s, sv_denot E e = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= s < 64 ->
  x * 2 ^ s < 2 ^ 64 -> sv_denot E (SAlu ALU_SLL e (SLit s)) = Z_to_bv 64 (x * 2 ^ s).
Proof.
intros E e x s He Hx Hs Hxs.
cbn [sv_denot alu64 alu]. rewrite He. apply bv_eq.
rewrite bv_shiftl_unsigned, bv_and_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small x (2 ^ 64)) by lia. rewrite (Z.mod_small s (2 ^ 64)) by lia.
rewrite (Z.mod_small 63 (2 ^ 64)) by lia.
replace (Z.land s 63) with s
  by (symmetry; change 63 with (Z.ones 6); rewrite Z.land_ones by lia; apply Z.mod_small; change (2 ^ 6) with 64; lia).
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma rf_den_or_add : forall E e1 e2 x1 x2 k, sv_denot E e1 = Z_to_bv 64 x1 -> sv_denot E e2 = Z_to_bv 64 x2 ->
  0 <= k -> 0 <= x1 -> x1 mod 2 ^ k = 0 -> 0 <= x2 < 2 ^ k -> x1 + x2 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_OR e1 e2) = Z_to_bv 64 (x1 + x2).
Proof.
intros E e1 e2 x1 x2 k H1 H2 Hk Hx1 Hm Hx2 Hs.
cbn [sv_denot alu64 alu]. rewrite H1, H2. apply bv_eq.
rewrite bv_or_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small x1 (2 ^ 64)) by lia. rewrite (Z.mod_small x2 (2 ^ 64)) by lia.
rewrite (Z.mod_small (x1 + x2) (2 ^ 64)) by lia.
exact (rf_lor_add x1 x2 k Hk Hm Hx2).
Qed.

(* The same with the low part first. *)
Lemma rf_den_or_add' : forall E e1 e2 x1 x2 k, sv_denot E e1 = Z_to_bv 64 x1 -> sv_denot E e2 = Z_to_bv 64 x2 ->
  0 <= k -> 0 <= x1 -> x1 mod 2 ^ k = 0 -> 0 <= x2 < 2 ^ k -> x1 + x2 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_OR e2 e1) = Z_to_bv 64 (x1 + x2).
Proof.
intros E e1 e2 x1 x2 k H1 H2 Hk Hx1 Hm Hx2 Hs.
cbn [sv_denot alu64 alu]. rewrite H1, H2. apply bv_eq.
rewrite bv_or_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small x1 (2 ^ 64)) by lia. rewrite (Z.mod_small x2 (2 ^ 64)) by lia.
rewrite (Z.mod_small (x1 + x2) (2 ^ 64)) by lia.
rewrite Z.lor_comm. exact (rf_lor_add x1 x2 k Hk Hm Hx2).
Qed.

(* Byte k of a value read modulo a larger power of two. *)
Lemma rf_byte_mod : forall x N k, 0 <= k -> k + 8 <= N -> Z.shiftr (x mod 2 ^ N) k mod 256 = Z.shiftr x k mod 256.
Proof.
intros x N k Hk HkN. change 256 with (2 ^ 8). apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8) as [H8|H8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* A chunk of a region, read byte by byte through the view. *)
Lemma rf_field : forall E H (m : word -> option byte) n bb cs lo hi wlo whi od (w : N) e x,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = bb -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 x ->
  Z.of_N w <= 8 ->
  forall j, (j < N.to_nat w)%nat ->
    aview tfibsegs H m (bb + od + Z.of_nat j) = Some (YO0f.le_byte x (N.to_nat w) j).
Proof.
intros E H m n bb cs lo hi wlo whi od w e x (_ & _ & _ & Hcs) Hn Hc He Hw j Hj.
pose proof (N_nat_Z w) as Hnw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck (Z.of_nat j) ltac:(unfold YP09.c_len; cbn [YP09.cv_len YP09.c_val]; lia)) as (b & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. rewrite He in Hb1. injection Hb1 as <-.
unfold aview. rewrite Hb2. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2 ^ 64). unfold YO0f.le_byte.
rewrite (rf_byte_mod x 64 (8 * Z.of_nat j)) by lia.
rewrite (rf_byte_mod x (8 * Z.of_nat (N.to_nat w)) (8 * Z.of_nat j)) by lia.
reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Tactics                                                             *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac rf_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
Ltac rf_in := cbn [rf_keepl In]; repeat (first [left; reflexivity | right]).
(* The windows a run wrote, each closed by tac. *)
Ltac rf_win Hin Hx tac :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.
(* A run from a state whose regions have no writable byte wrote nothing. *)
Ltac rf_nowin :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx; rf_win Hin Hx ltac:(lia).
(* The write right of a run whose regions have no writable byte. *)
Ltac rf_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.
(* The write right of the run at +0x140: g_rx_send's four bytes, bytes of G. *)
Ltac rf_awr_rxs U :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U in Ha; apply rf_rxs_G;
    unfold rf_rxs, RECV_RXS_HI in *; lia |];
  apply awr_ok_x_nil.
(* The model of the goal after a run, named. *)
Ltac rf_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "md" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end.
(* After a run from a state with no writable byte: the view as at mb, the presence grown. *)
Ltac rf_kd HFr HG KDo GRo KDn GRn mb :=
  lazymatch type of HFr with frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?mo) (mrestrict (w_H ?Wx) ?mn) =>
    assert (KDn : forall x, 0 <= x < 2 ^ 64 -> aview tfibsegs (w_H Wx) mn x = aview tfibsegs (w_H Wx) mb x)
      by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; refine (eq_trans _ (KDo x Hx));
          apply (kept_of_frame Ex rsx (w_H Wx) mo mn (fun _ => False) HFr); [rf_nowin | exact Hx | intros []]);
    assert (GRn : forall x, apresent (w_H Wx) mb x -> apresent (w_H Wx) mn x)
      by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; exact (apresent_grows _ _ _ x HG (GRo x Hx)))
  end.
(* The kept registers: their symbolic values are their atoms, whose values are those of regs2. *)
Ltac rf_srget :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [rf_keepl In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity |]); destruct Hr.
Ltac rf_ewlo Elo EE :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [rf_keepl In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [rewrite Elo by lia; apply EE; reflexivity |]); destruct Hr.
Ltac rf_ew0 EE :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [rf_keepl In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [apply EE; reflexivity |]); destruct Hr.

(* ------------------------------------------------------------------ *)
(* The registers at the cuts                                           *)
(* ------------------------------------------------------------------ *)

Lemma rf_opb_of : forall regs regs2 regsF by_poll a bytes,
  recv_regs_opb regs regs2 by_poll a bytes ->
  (forall r, In r rf_keepl -> YK11.getr regsF (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)) ->
  recv_regs_opb regs regsF by_poll a bytes.
Proof.
intros regs regs2 regsF by_poll a bytes ((Q2 & Q3 & Q4 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27) & Q8 & Q9 & Q18 & Q19 & Q21) HK.
refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))) (conj _ (conj _ (conj _ (conj _ _))))).
- exact (eq_trans (HK 2 ltac:(rf_in)) Q2).
- exact (eq_trans (HK 3 ltac:(rf_in)) Q3).
- exact (eq_trans (HK 4 ltac:(rf_in)) Q4).
- exact (eq_trans (HK 22 ltac:(rf_in)) Q22).
- exact (eq_trans (HK 23 ltac:(rf_in)) Q23).
- exact (eq_trans (HK 24 ltac:(rf_in)) Q24).
- exact (eq_trans (HK 25 ltac:(rf_in)) Q25).
- exact (eq_trans (HK 26 ltac:(rf_in)) Q26).
- exact (eq_trans (HK 27 ltac:(rf_in)) Q27).
- exact (eq_trans (HK 8 ltac:(rf_in)) Q8).
- exact (eq_trans (HK 9 ltac:(rf_in)) Q9).
- exact (eq_trans (HK 18 ltac:(rf_in)) Q18).
- exact (eq_trans (HK 19 ltac:(rf_in)) Q19).
- exact (eq_trans (HK 21 ltac:(rf_in)) Q21).
Qed.

Lemma rf_mrx_of : forall regs regs2 regsF by_poll a bytes,
  recv_regs_opb regs regs2 by_poll a bytes ->
  (forall r, In r rf_keepl -> YK11.getr regsF (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)) ->
  recv_regs_mrx regs regsF a bytes.
Proof.
intros regs regs2 regsF by_poll a bytes HO HK.
destruct (rf_opb_of regs regs2 regsF by_poll a bytes HO HK) as (HKP & Q8 & _ & Q18 & _).
exact (conj HKP (conj Q8 Q18)).
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The machine state of a goal moved to the cut pc's name. *)
Ltac rf_pc pc :=
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + pc)) mm rom) mdx) Q) end.

Definition rf_E0 (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).
Definition rf_EL (regs : bvmap 5 word) (bytes : list byte) : env :=
  Eimg (PI := PI_transport) (Ereg regs (rf_vals bytes)).

Lemma rf_u483 : forall regs extra, bv_unsigned (ew (Eimg (PI := PI_transport) (Ereg regs extra)) 483) = RECV_RXS_HI.
Proof. intros regs extra. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). vm_compute. reflexivity. Qed.

(* A state with no region, at any pc. *)
Lemma rf_entry0 : forall (Wx : world segs) regs mem pc,
  st_ok_pi segs VAL (rf_E0 regs) (rf_ss0 pc)
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros Wx regs mem pc. rewrite restrict_mkst_fx. unfold rf_ss0.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The state at +0x140 with g_rx_send's region. *)
Lemma rf_entryS : forall (Wx : world segs) regs mem,
  st_ok_pi segs VAL (rf_E0 regs) rf_ssS
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (RECV_RF + 148))) mem (YK11.seg_rom segs))).
Proof.
intros Wx regs mem. rewrite restrict_mkst_fx. unfold rf_ssS.
assert (U : bv_unsigned (ew (rf_E0 regs) 483) = RECV_RXS_HI) by exact (rf_u483 regs []).
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold rf_rxs_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U. unfold RECV_RXS_HI.
  split; [unfold TA_g_rx_send; lia|]. split; [unfold TA_g_rx_send; lia|]. split; [|constructor].
  intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_g_rx_send + 1328 + o) G_HARNESS_rw).
  apply rf_rxs_G. unfold rf_rxs. lia.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U, Z.pow_0_r, Z.mod_1_r.
  repeat split; first [exact I | lia].
Qed.

(* One byte of the frame region. *)
Lemma rf_frame_chunk : forall (E : env) (mm : word -> option byte) (a : Z) (bytes : list byte) (c : Z) (j : nat),
  garr8 segs mm a (TW.zs bytes) -> 0 <= c -> c < Z.of_nat (length bytes) -> ew E j = w64 (rfb bytes c) ->
  YP09.chunk_ok segs E mm a (YP09.mkChunk c (CVal 1 (SOff j 0))).
Proof.
intros E mm a bytes c j Hg Hc Hl He.
assert (Hlt : (Z.to_nat c < length (TW.zs bytes))%nat) by (unfold TW.zs; rewrite length_map; lia).
destruct (garr8_nthZ segs mm a (TW.zs bytes) c Hg Hc Hlt) as [Hv Hr].
apply (chunk_ok_val segs E mm a c 1 (SOff j 0) (rfb bytes c)).
- apply rf_den_atom; [exact He | unfold rfb; lia].
- change (2 ^ (8 * Z.of_N 1)) with 256. unfold rfb. lia.
- cbn. lia.
- cbn [N.to_nat]. exact Hv.
Qed.

(* The state at the rf cut when n >= 30, with the frame region and the shadow entry of its first 30 bytes. *)
Lemma rf_entryL : forall (Wx : world segs) regs mem (a : Z) (bytes : list byte),
  YK11.getr regs 8 = w64 a -> YK11.getr regs 21 = w64 SHADOW_OFF ->
  30 <= Z.of_nat (length bytes) ->
  garr8 segs (mrestrict (w_H Wx) mem) a (TW.zs bytes) ->
  range_addressable (aview segs (w_H Wx) mem) SHADOW_OFF a 30 ->
  0 <= a -> amem_range a 30 ->
  st_ok_pi segs VAL (rf_EL regs bytes) rf_ssL
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + RECV_RF)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs RF_Bx RF_SH (rf_EL regs bytes) (mrestrict (w_H Wx) mem).
Proof.
intros Wx regs mem a bytes H8 H21 Hn Hg HRA Ha0 Hmr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfa : 0 <= a <= 2 ^ 47 - 31) by (unfold amem_range in Hmr; lia).
set (E := rf_EL regs bytes).
assert (E8 : ew E 8 = w64 a)
  by (unfold E, rf_EL; rewrite (can_ew_Eimg_Ereg_nat regs _ 8 (Z_to_bv 5 8) eq_refl); exact H8).
assert (U8 : bv_unsigned (ew E 8) = a) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
assert (E21 : ew E 21 = w64 SHADOW_OFF)
  by (unfold E, rf_EL; rewrite (can_ew_Eimg_Ereg_nat regs _ 21 (Z_to_bv 5 21) eq_refl); exact H21).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (rewrite E21; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (EXB : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (rf_vals bytes) (Z_to_bv 64 0))
  by (intros j Hj; unfold E, rf_EL; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EXB 0%nat ltac:(lia)) as A32. pose proof (EXB 1%nat ltac:(lia)) as A33.
pose proof (EXB 2%nat ltac:(lia)) as A34. pose proof (EXB 3%nat ltac:(lia)) as A35.
pose proof (EXB 4%nat ltac:(lia)) as A36. pose proof (EXB 5%nat ltac:(lia)) as A37.
pose proof (EXB 6%nat ltac:(lia)) as A38. pose proof (EXB 7%nat ltac:(lia)) as A39.
cbn [Nat.add nth rf_vals] in A32, A33, A34, A35, A36, A37, A38, A39.
pose proof (rfb_range bytes 12) as R12. pose proof (rfb_range bytes 13) as R13.
pose proof (rfb_range bytes 14) as R14. pose proof (rfb_range bytes 15) as R15.
pose proof (rfb_range bytes 18) as R18. pose proof (rfb_range bytes 19) as R19.
pose proof (rfb_range bytes 20) as R20. pose proof (rfb_range bytes 21) as R21.
split.
- rewrite restrict_mkst_fx. unfold rf_ssL.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold rf_frame, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
      first [ exact (rf_frame_chunk E _ a bytes 12 32 Hg ltac:(lia) ltac:(lia) A32)
            | exact (rf_frame_chunk E _ a bytes 13 33 Hg ltac:(lia) ltac:(lia) A33)
            | exact (rf_frame_chunk E _ a bytes 14 34 Hg ltac:(lia) ltac:(lia) A34)
            | exact (rf_frame_chunk E _ a bytes 15 35 Hg ltac:(lia) ltac:(lia) A35)
            | exact (rf_frame_chunk E _ a bytes 18 36 Hg ltac:(lia) ltac:(lia) A36)
            | exact (rf_frame_chunk E _ a bytes 19 37 Hg ltac:(lia) ltac:(lia) A37)
            | exact (rf_frame_chunk E _ a bytes 20 38 Hg ltac:(lia) ltac:(lia) A38)
            | exact (rf_frame_chunk E _ a bytes 21 39 Hg ltac:(lia) ltac:(lia) A39) ].
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split; exact I.
  + unfold rf_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U8, U21, A32, A33, A34, A35, A36, A37, A38, A39.
    unfold w64. rewrite !unsigned_lit_small by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold SHADOW_OFF; lia].
- unfold sh_ok, RF_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H Wx) mem E RF_Bx 8 a 30 a 0 30 HRA).
  + unfold U, RF_Bx. cbn [sv_denot]. rewrite E21, Z.add_0_r, Z_to_bv_bv_unsigned.
    unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
  + unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r, Z_to_bv_bv_unsigned.
    unfold w64. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Hmr. unfold SHADOW_OFF. lia.
Qed.

(* The value of a kept register at the machine state of a symbolic state: its atom's. *)
Lemma rf_keep_regs : forall (L : list Z) (E : env) ss (Hh : word -> bool) ms (regs2 : bvmap 5 word),
  st_ok_pi segs VAL E ss (restrict Hh ms) ->
  (forall r, In r L -> sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0) ->
  (forall r, In r L -> ew E (Z.to_nat r) = YK11.getr regs2 (Z_to_bv 5 r)) ->
  forall r, In r L -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r).
Proof.
intros L E ss Hh ms regs2 HS HR HE r Hr.
rewrite (st_ok_pi_restrict_reg Hh E ss ms (Z_to_bv 5 r) HS), (HR r Hr).
cbn [sv_denot]. rewrite (HE r Hr), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(* ------------------------------------------------------------------ *)
(* The cut facts carried across a step                                 *)
(* ------------------------------------------------------------------ *)

(* A step that changes at most g_rx_send's four bytes keeps recv_cur (TransportGFrame.v dk_kept_step_gw: those bytes
   are in recv_wr bytes and in G; the saved words lie above the allocation ceiling) and the frame's bytes (a block
   byte is not an image byte). *)
Lemma rf_cur_step : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (p by_poll pf T : Z) (bytes Bw : list byte) ch (a : Z) ly2 S2 (W2 : world segs) mX mdX mY mdY,
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS ->
  recv_fix B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mX mdX ->
  recv_blk W2 mX a bytes ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mY mdY (k + 1) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ rf_rxs x -> aview segs (w_H W2) mY x = aview segs (w_H W2) mX x) ->
  (forall x, apresent (w_H W2) mX x -> apresent (w_H W2) mY x) ->
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mY mdY /\
  recv_blk W2 mY a bytes.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a ly2 S2 W2 mX mdX mY mdY
  LAWS HGX HFIX HCUR HBLK HJY KD GR.
pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
pose proof HCUR as (HJX & Hfrs & Hperm & HMO & HK & HSV & H4096).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HAR.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX) as HAR2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (RSv : 0 <= RECV_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (CT : TA_g_rx_send = 6181856) by reflexivity.
split.
- refine (conj HJY (conj Hfrs (conj Hperm (conj HMO (conj _ (conj _ H4096)))))).
  + apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W2 mX mY
      (spZ regs - RECV_STK) (spZ regs) (recv_wr bytes) rf_rxs HAR HK KD GR).
    * intros x Hx Hc. exfalso. unfold rf_rxs in Hx. lia.
    * intros b m i _ _ Hx. exact (rf_rxs_wr bytes _ Hx).
    * intros x Hx _ HnG _ _. exact (HnG (rf_rxs_G x Hx)).
    * intros cid pos x _ _ Hx. exact (rf_rxs_wr bytes x Hx).
  + apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HSV o Ho) as Hv.
    assert (Hob : 8 <= fst o <= 56).
    { unfold RECV_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [Ho|Ho]; [subst o; cbn [fst]; lia|]). destruct Ho. }
    rewrite <- Hv. apply rdword_ext. intros i Hi. apply KD; [lia | unfold rf_rxs; lia].
- assert (Hin2 : In (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B ly2 S2))
    by exact (Permutation_in _ (Permutation_sym Hperm) (or_introl eq_refl)).
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mX mdX _ _ HAR2 Hin2) as (_ & Hb4096 & Hbc & _).
  pose proof (rf_req_ge (Z.max 1 (Z.of_nat (length bytes)))) as Hq.
  unfold recv_blk in *. apply (garr8_frame segs (mrestrict (w_H W2) mX) _ _ _ HBLK).
  intros x Hx. apply can_mbyte_of_aview. unfold TW.zs in Hx. rewrite length_map in Hx.
  apply KD; [lia|].
  intros Hr. apply (blk_img segs B LAWS ly2 S2 W2 mX mdX a (Z.max 1 (Z.of_nat (length bytes))) x HAR2 Hin2
    ltac:(lia)).
  destruct (HGX x (rf_rxs_G x Hr)) as [Hi _]. exact Hi.
Qed.

(* ------------------------------------------------------------------ *)
(* +0x140 .. +0x148: the store of the send value, `beqz s3`, the cuts   *)
(* ------------------------------------------------------------------ *)

Lemma rf_store : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (p by_poll pf T : Z) (bytes Bw : list byte) ch (a : Z) (Bw' : list byte)
    ly2 S2 (W2 : world segs) (mF : word -> option byte) (mdF : Model) (regs3 : bvmap 5 word),
  @recv_poll_at fx rc B MT -> @recv_mrx_at fx rc B MT -> recv_laws B MT -> recv_calls B MT ->
  recv_fix B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mF mdF ->
  recv_res Bw bytes by_poll pf a Bw' -> recv_blk W2 mF a bytes ->
  tw_at TMAP_A (aview segs (w_H W2) mF) (recv_w1 Bw) ->
  recv_regs_opb regs regs3 by_poll a bytes -> YK11.getr regs3 10 = w64 (recv_send bytes) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + (RECV_RF + 148))) mF (YK11.seg_rom segs)) mdF)
    (@transport_recv_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2 S2 W2 mF mdF regs3
  HPOLL HMRX HL HC HFIX HCUR HRES HBLK HTW HREGS H10.
pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & LAWS & MTL & HGX & HGNE).
pose proof HCUR as (HJ & _).
pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbp & _).
pose proof (rf_send_range bytes) as RSV.
pose proof (rf_entryS W2 regs3 mF) as HS.
set (E0 := rf_E0 regs3) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, rf_E0; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 21 0) (@nil shent) E0 (mrestrict (w_H W2) mF)) by constructor.
assert (U483 : bv_unsigned (ew E0 483) = RECV_RXS_HI) by (unfold E0, rf_E0; apply rf_u483).
assert (EE0 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E0 nn = YK11.getr regs3 rr)
  by (intros nn rr Hnn; unfold E0, rf_E0; apply can_ew_Eimg_Ereg_nat; exact Hnn).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
(* run 1, +0x140 .. +0x144: a2 = the PHi of g_rx_send, `sw a0, -0x530(a2)`; it stops at `beqz s3` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ rf_awr_rxs U483. }
rf_md.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into ms1 end.
assert (K1 : forall x, 0 <= x < 2 ^ 64 -> ~ rf_rxs x ->
  aview segs (w_H W2) (ms_mem ms1) x = aview segs (w_H W2) mF x).
{ intros x Hx Hn. apply (kept_of_frame _ _ _ _ _ rf_rxs HFr); [| exact Hx | exact Hn].
  intros b wlo whi y Hin Hy. rf_win Hin Hy ltac:(rewrite ?U483 in Hy; unfold rf_rxs, RECV_RXS_HI in *; lia). }
assert (G1 : forall x, apresent (w_H W2) mF x -> apresent (w_H W2) (ms_mem ms1) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in HS end.
assert (E1lo : forall nn, (nn < 1024)%nat -> ew E1 nn = ew E0 nn)
  by (intros nn Hnn; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (U483b : bv_unsigned (ew E1 483) = RECV_RXS_HI) by (rewrite E1lo by lia; exact U483).
(* the stored bytes, read back from the region *)
pose proof (st_ok_pi_region_nth E1 _ (restrict (w_H W2) ms1) 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (D10 : sv_denot E1 (SOff 10 0) = Z_to_bv 64 (recv_send bytes)).
{ apply rf_den_atom; [|lia]. rewrite (E1lo 10%nat ltac:(lia)), (EE0 10%nat (Z_to_bv 5 10) eq_refl). exact H10. }
pose proof (rf_field _ _ _ _ _ _ _ _ _ _ (-1328) 4 (SOff 10 0) (recv_send bytes) RG0 U483b
  ltac:(cbn [In]; left; reflexivity) D10 ltac:(cbn; lia)) as VS.
clear RG0.
(* the registers at +0x148 *)
assert (KR1 : forall r, In r rf_keepl -> YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs3 (Z_to_bv 5 r)).
{ apply (rf_keep_regs rf_keepl E1 _ (w_H W2) ms1 regs3 HS); [rf_srget | rf_ewlo E1lo EE0]. }
rf_reg HS (Z_to_bv 5 12) (w64 RECV_RXS_HI) Ya2 ltac:(cbn [sv_denot]; rewrite U483b, Z.add_0_r; reflexivity).
(* the facts at the memory after the store; the machine state named *)
pmkst HS.
clear HS SHOK HEI.
set (m1 := ms_mem ms1) in *.
destruct (rf_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a ly2 S2 W2
  mF mdF m1 _ LAWS HGX HFIX HCUR HBLK HJ K1 G1) as [CUR1 BLK1].
assert (TW1 : tw_at TMAP_A (aview segs (w_H W2) m1) (recv_w2 Bw bytes)).
{ unfold recv_w2, TW.set_g_rx_send.
  replace TW.OFF_g_rx_send with (TW.OFF_g_rx_send + 0) by lia.
  apply (tw_write TMAP_A (aview segs (w_H W2) mF) (aview segs (w_H W2) m1) (recv_w1 Bw) TW.OFF_g_rx_send
    TA_g_rx_send TW.SZ_g_rx_send 0 4 (recv_send bytes) TMAP_A_ok HTW TMAP_A_g_rx_send ltac:(lia)
    ltac:(unfold TW.SZ_g_rx_send; lia)).
  - intros j Hj. pose proof (VS j Hj) as V.
    replace (RECV_RXS_HI + -1328) with (TA_g_rx_send + 0) in V by (unfold RECV_RXS_HI; lia). exact V.
  - intros x Hx Hn. apply K1.
    + pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. lia.
    + intros Hr. apply Hn. unfold rf_rxs in Hr. lia. }
(* +0x148: `beqz s3`, from a state with no region *)
rf_pc (RECV_RF + 156).
pose proof (rf_entry0 W2 (ms_regs ms1) m1 (RECV_RF + 156)) as HS.
set (E2 := rf_E0 (ms_regs ms1)) in HS.
assert (HEI : img_env VAL A_LIM E2) by (unfold E2, rf_E0; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 21 0) (@nil shent) E2 (mrestrict (w_H W2) m1)) by constructor.
assert (EE2 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E2 nn = YK11.getr (ms_regs ms1) rr)
  by (intros nn rr Hnn; unfold E2, rf_E0; apply can_ew_Eimg_Ereg_nat; exact Hnn).
pose proof HREGS as (_ & _ & _ & _ & Q19 & _).
assert (Y19 : YK11.getr (ms_regs ms1) (Z_to_bv 5 19) = w64 by_poll) by exact (eq_trans (KR1 19 ltac:(rf_in)) Q19).
assert (D19 : sv_denot E2 (SOff 19 0) = Z_to_bv 64 by_poll).
{ cbn [sv_denot]. rewrite (EE2 19%nat (Z_to_bv 5 19) eq_refl), Y19. unfold w64.
  rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (KDb : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) m1 x = aview segs (w_H W2) m1 x) by (intros; reflexivity).
assert (GRb : forall x, apresent (w_H W2) m1 x -> apresent (w_H W2) m1 x) by (intros x Hx; exact Hx).
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* by_poll = 0: to the mrx cut +0x248 *)
  cbn [branch_taken] in Hc. rewrite D19 in Hc. change (sv_denot E2 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite EPI.mrxk_eqb in Hc by lia. apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan RECV_MRX.
  { rf_awr0. }
  rf_md.
  rf_kd HFr HG KDb GRb KD2 GR2 m1. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E3 := EF) in HS end.
  assert (E3lo : forall nn, (nn < 1024)%nat -> ew E3 nn = ew E2 nn)
    by (intros nn Hnn; unfold E3; repeat rewrite ew_ewset_other by lia; reflexivity).
  assert (KRC : forall r, In r rf_keepl ->
    YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr (ms_regs ms1) (Z_to_bv 5 r)).
  { apply (rf_keep_regs rf_keepl E3 _ (w_H W2) ms (ms_regs ms1) HS); [rf_srget | rf_ewlo E3lo EE2]. }
  destruct (rf_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a ly2 S2
    W2 m1 _ (ms_mem ms) _ LAWS HGX HFIX CUR1 BLK1 HJ (fun x Hx _ => KD2 x Hx) GR2) as [CURC BLKC].
  assert (TWC : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms)) (recv_w2 Bw bytes)).
  { apply (tw_kept TMAP_A (aview segs (w_H W2) m1)); [exact TW1|]. intros x Hx. apply KD2.
    pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. lia. }
  pmkst HS.
  rf_pc RECV_MRX.
  apply (HMRX HL HC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2 S2 W2
    (ms_mem ms) _ (ms_regs ms) HFIX CURC HRES BLKC TWC Hc).
  exact (rf_mrx_of regs regs3 (ms_regs ms) by_poll a bytes HREGS
    (fun r Hr => eq_trans (KRC r Hr) (KR1 r Hr))).
- (* by_poll <> 0: to the poll cut +0x14c *)
  cbn [branch_taken] in Hc. rewrite D19 in Hc. change (sv_denot E2 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite EPI.mrxk_eqb in Hc by lia. apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan RECV_POLL.
  { rf_awr0. }
  rf_md.
  rf_kd HFr HG KDb GRb KD2 GR2 m1. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E3 := EF) in HS end.
  assert (E3lo : forall nn, (nn < 1024)%nat -> ew E3 nn = ew E2 nn)
    by (intros nn Hnn; unfold E3; repeat rewrite ew_ewset_other by lia; reflexivity).
  assert (KRC : forall r, In r (12 :: rf_keepl) ->
    YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr (ms_regs ms1) (Z_to_bv 5 r)).
  { apply (rf_keep_regs (12 :: rf_keepl) E3 _ (w_H W2) ms (ms_regs ms1) HS); [rf_srget | rf_ewlo E3lo EE2]. }
  destruct (rf_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a ly2 S2
    W2 m1 _ (ms_mem ms) _ LAWS HGX HFIX CUR1 BLK1 HJ (fun x Hx _ => KD2 x Hx) GR2) as [CURC BLKC].
  assert (TWC : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms)) (recv_w2 Bw bytes)).
  { apply (tw_kept TMAP_A (aview segs (w_H W2) m1)); [exact TW1|]. intros x Hx. apply KD2.
    pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. lia. }
  pmkst HS.
  rf_pc RECV_POLL.
  apply (HPOLL HL HC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2 S2 W2
    (ms_mem ms) _ (ms_regs ms) HFIX CURC HRES BLKC TWC Hc).
  split.
  + exact (rf_opb_of regs regs3 (ms_regs ms) by_poll a bytes HREGS
      (fun r Hr => eq_trans (KRC r (or_intror Hr)) (KR1 r Hr))).
  + exact (eq_trans (KRC 12 (or_introl eq_refl)) Ya2).
Qed.

(* The cut facts at the memory of runs that wrote nothing, then rf_store. *)
Lemma rf_join : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (p by_poll pf T : Z) (bytes Bw : list byte) ch (a : Z) (Bw' : list byte)
    ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) (mF : word -> option byte) (mdF : Model)
    (regs3 : bvmap 5 word),
  @recv_poll_at fx rc B MT -> @recv_mrx_at fx rc B MT -> recv_laws B MT -> recv_calls B MT ->
  recv_fix B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
  recv_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
  recv_res Bw bytes by_poll pf a Bw' -> recv_blk W2 mem2 a bytes ->
  tw_at TMAP_A (aview segs (w_H W2) mem2) (recv_w1 Bw) -> recv_regs_opb regs regs2 by_poll a bytes ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mF mdF (k + 1) ->
  (forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) mF x = aview segs (w_H W2) mem2 x) ->
  (forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) mF x) ->
  (forall r, In r rf_keepl -> YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)) ->
  YK11.getr regs3 10 = w64 (recv_send bytes) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + (RECV_RF + 148))) mF (YK11.seg_rom segs)) mdF)
    (@transport_recv_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2 S2 W2 mem2 md2
  regs2 mF mdF regs3 HPOLL HMRX HL HC HFIX HCUR HRES HBLK HTW HREGS HJF KD GR KR H10.
pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & LAWS & _ & HGX & _).
destruct (rf_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a ly2 S2 W2
  mem2 md2 mF mdF LAWS HGX HFIX HCUR HBLK HJF (fun x Hx _ => KD x Hx) GR) as [CURF BLKF].
assert (TWF : tw_at TMAP_A (aview segs (w_H W2) mF) (recv_w1 Bw)).
{ apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact HTW|]. intros x Hx. apply KD.
  pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. lia. }
exact (rf_store STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2 S2 W2
  mF mdF regs3 HPOLL HMRX HL HC HFIX CURF HRES BLKF TWF (rf_opb_of regs regs2 regs3 by_poll a bytes HREGS KR) H10).
Qed.

(* ------------------------------------------------------------------ *)
(* The piece                                                           *)
(* ------------------------------------------------------------------ *)

Lemma recv_rf : @recv_rf_stmt fx rc B MT.
Proof.
unfold recv_rf_stmt. intros HPOLL HMRX.
unfold recv_rf_at. intros HL HC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw'
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HRES HBLK HTW HREGS.
pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & LAWS & MTL & HGX & HGNE).
pose proof HCUR as (HJ & Hfrs & Hperm & HMO & HK & HSV & H4096).
pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _).
destruct HREGS as [HOPB H12].
pose proof HOPB as ((Q2 & Q3 & Q4 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27) & Q8 & Q9 & Q18 & Q19 & Q21).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
assert (KD0 : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) mem2 x = aview segs (w_H W2) mem2 x)
  by (intros; reflexivity).
assert (GR0 : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) mem2 x) by (intros x Hx; exact Hx).
destruct (Z_lt_le_dec (Z.of_nat (length bytes)) 30) as [Hlt | Hge].
- (* n < 30: +0x13c, a0 = 0 *)
  assert (Hs0 : recv_send bytes = 0) by (rewrite rf_send_eq; apply RPL.rb_snd_short; lia).
  pose proof (rf_entry0 W2 regs2 mem2 RECV_RF) as HS.
  set (E0 := rf_E0 regs2) in HS.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, rf_E0; apply Eimg_env).
  assert (SHOK : sh_ok segs (SOff 21 0) (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
  assert (EE0 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E0 nn = YK11.getr regs2 rr)
    by (intros nn rr Hnn; unfold E0, rf_E0; apply can_ew_Eimg_Ereg_nat; exact Hnn).
  assert (HBR : branch_taken BC_LTU (sv_denot E0 (SOff 18 0)) (sv_denot E0 (SOff 12 0)) =
    (Z.of_nat (length bytes) <? 30)).
  { rewrite (rf_den_atom E0 18 (Z.of_nat (length bytes))
      ltac:(rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl); exact Q18) ltac:(lia)).
    rewrite (rf_den_atom E0 12 30 ltac:(rewrite (EE0 12%nat (Z_to_bv 5 12) eq_refl); exact H12) ltac:(lia)).
    cbn [branch_taken]. apply EPI.mrxk_ltu; lia. }
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  2: { exfalso. rewrite HBR in Hc. apply Z.ltb_ge in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (RECV_RF + 148).
  { rf_awr0. }
  rf_md.
  rf_kd HFr HG KD0 GR0 KD1 GR1 mem2. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in HS end.
  assert (E1lo : forall nn, (nn < 1024)%nat -> ew E1 nn = ew E0 nn)
    by (intros nn Hnn; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
  rf_reg HS (Z_to_bv 5 10) (w64 (recv_send bytes)) Ya0 ltac:(rewrite Hs0; reflexivity).
  assert (KR : forall r, In r rf_keepl -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)).
  { apply (rf_keep_regs rf_keepl E1 _ (w_H W2) ms regs2 HS); [rf_srget | rf_ewlo E1lo EE0]. }
  pmkst HS.
  rf_pc (RECV_RF + 148).
  exact (rf_join STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2 S2 W2
    mem2 md2 regs2 (ms_mem ms) _ (ms_regs ms) HPOLL HMRX HL HC HFIX HCUR HRES HBLK HTW HOPB HJ KD1 GR1 KR Ya0).
- (* n >= 30: the frame's header *)
  assert (Hin2 : In (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B ly2 S2))
    by exact (Permutation_in _ (Permutation_sym Hperm) (or_introl eq_refl)).
  pose proof (rf_req_ge (Z.max 1 (Z.of_nat (length bytes)))) as Hq.
  assert (HRA : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF a 30)
    by (apply (range_addressable_of_block segs B LAWS ly2 S2 W2 mem2 md2 a _ a 30 HAR2 Hin2); lia).
  assert (Hmr : amem_range a 30)
    by (apply (amem_range_of_block segs B LAWS ly2 S2 W2 mem2 md2 a _ a 30 HAR2 Hin2); lia).
  destruct (rf_entryL W2 regs2 mem2 a bytes Q8 Q21 Hge HBLK HRA ltac:(lia) Hmr) as [HS SHOK].
  set (E0 := rf_EL regs2 bytes) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, rf_EL; apply Eimg_env).
  assert (EE0 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E0 nn = YK11.getr regs2 rr)
    by (intros nn rr Hnn; unfold E0, rf_EL; apply can_ew_Eimg_Ereg_nat; exact Hnn).
  assert (EXB : forall j, (j < 8)%nat -> ew E0 (32 + j) = nth j (rf_vals bytes) (Z_to_bv 64 0))
    by (intros j Hj; unfold E0, rf_EL; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EXB 0%nat ltac:(lia)) as A32. pose proof (EXB 1%nat ltac:(lia)) as A33.
  pose proof (EXB 2%nat ltac:(lia)) as A34. pose proof (EXB 3%nat ltac:(lia)) as A35.
  pose proof (EXB 4%nat ltac:(lia)) as A36. pose proof (EXB 5%nat ltac:(lia)) as A37.
  pose proof (EXB 6%nat ltac:(lia)) as A38. pose proof (EXB 7%nat ltac:(lia)) as A39.
  cbn [Nat.add nth rf_vals] in A32, A33, A34, A35, A36, A37, A38, A39.
  pose proof (rfb_range bytes 12) as R12. pose proof (rfb_range bytes 13) as R13.
  pose proof (rfb_range bytes 14) as R14. pose proof (rfb_range bytes 15) as R15.
  pose proof (rfb_range bytes 18) as R18. pose proof (rfb_range bytes 19) as R19.
  pose proof (rfb_range bytes 20) as R20. pose proof (rfb_range bytes 21) as R21.
  destruct (rf_be16 bytes) as [BE12 BE14].
  pose proof (RPL.r_be16_range bytes 12) as RB12. pose proof (RPL.r_be16_range bytes 14) as RB14.
  assert (HBR : branch_taken BC_LTU (sv_denot E0 (SOff 18 0)) (sv_denot E0 (SOff 12 0)) =
    (Z.of_nat (length bytes) <? 30)).
  { rewrite (rf_den_atom E0 18 (Z.of_nat (length bytes))
      ltac:(rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl); exact Q18) ltac:(lia)).
    rewrite (rf_den_atom E0 12 30 ltac:(rewrite (EE0 12%nat (Z_to_bv 5 12) eq_refl); exact H12) ltac:(lia)).
    cbn [branch_taken]. apply EPI.mrxk_ltu; lia. }
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  1: { exfalso. rewrite HBR in Hc. apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  (* run 1, +0x0ac .. +0x0f0: the checks and loads at a + 12, a + 13; it stops at the ethertype test *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { rf_awr0. }
  rf_md.
  rf_kd HFr HG KD0 GR0 KD1 GR1 mem2. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
  assert (E1lo : forall nn, (nn < 1024)%nat -> ew E1 nn = ew E0 nn)
    by (intros nn Hnn; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
  assert (DET : sv_denot E1 (SAlu ALU_OR (SAlu ALU_SLL (SOff 32 0) (SLit 8)) (SOff 33 0)) =
    Z_to_bv 64 (DSpec.be16 bytes 12)).
  { rewrite BE12. apply (rf_den_or_add E1 _ _ (rfb bytes 12 * 2 ^ 8) (rfb bytes 13) 8).
    - apply rf_den_sll; [apply rf_den_atom; [rewrite E1lo by lia; exact A32 | lia] | lia | lia | lia].
    - apply rf_den_atom; [rewrite E1lo by lia; exact A33 | lia].
    - lia.
    - lia.
    - apply Z_mod_mult.
    - lia.
    - lia. }
  assert (HET : branch_taken BC_NE (sv_denot E1 (SAlu ALU_OR (SAlu ALU_SLL (SOff 32 0) (SLit 8)) (SOff 33 0)))
    (sv_denot E1 (SLit 34911)) = negb (DSpec.be16 bytes 12 =? 34911)).
  { rewrite DET. cbn [branch_taken sv_denot]. rewrite EPI.mrxk_eqb by lia. reflexivity. }
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* the ethertype is not 0x885f: +0x13c, a0 = 0 *)
    rewrite HET in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    assert (Hs0 : recv_send bytes = 0) by (rewrite rf_send_eq; apply RPL.rb_snd_eth; [lia | exact Hc]).
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (RECV_RF + 148).
    { rf_awr0. }
    rf_md.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into msF end.
    rf_kd HFr HG KD1 GR1 KD2 GR2 mem2. clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in HS, SHOK end.
    assert (E2lo : forall nn, (nn < 1024)%nat -> ew E2 nn = ew E0 nn)
      by (intros nn Hnn; unfold E2, E1; repeat rewrite ew_ewset_other by lia; reflexivity).
    rf_reg HS (Z_to_bv 5 10) (w64 (recv_send bytes)) Ya0 ltac:(rewrite Hs0; reflexivity).
    assert (KR : forall r, In r rf_keepl -> YK11.getr (ms_regs msF) (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)).
    { apply (rf_keep_regs rf_keepl E2 _ (w_H W2) msF regs2 HS); [rf_srget | rf_ewlo E2lo EE0]. }
    pmkst HS.
    rf_pc (RECV_RF + 148).
    exact (rf_join STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2 S2 W2
      mem2 md2 regs2 (ms_mem msF) _ (ms_regs msF) HPOLL HMRX HL HC HFIX HCUR HRES HBLK HTW HOPB HJ KD2 GR2 KR Ya0).
  + (* the ethertype is 0x885f *)
    rewrite HET in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HetOK.
    (* run 2, +0x0f0 .. +0x130: the checks and loads at a + 14, a + 15; it stops at `bltu a0, 16` *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { rf_awr0. }
    rf_md.
    rf_kd HFr HG KD1 GR1 KD2 GR2 mem2. clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in * end.
    assert (E2lo : forall nn, (nn < 1024)%nat -> ew E2 nn = ew E0 nn)
      by (intros nn Hnn; unfold E2, E1; repeat rewrite ew_ewset_other by lia; reflexivity).
    assert (DNB : sv_denot E2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 35 0)) =
      Z_to_bv 64 (DSpec.be16 bytes 14)).
    { rewrite BE14. apply (rf_den_or_add E2 _ _ (rfb bytes 14 * 2 ^ 8) (rfb bytes 15) 8).
      - apply rf_den_sll; [apply rf_den_atom; [rewrite E2lo by lia; exact A34 | lia] | lia | lia | lia].
      - apply rf_den_atom; [rewrite E2lo by lia; exact A35 | lia].
      - lia.
      - lia.
      - apply Z_mod_mult.
      - lia.
      - lia. }
    assert (HNS : branch_taken BC_LTU (sv_denot E2 (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 35 0)))
      (sv_denot E2 (SLit 16)) = (DSpec.be16 bytes 14 <? 16)).
    { rewrite DNB. cbn [branch_taken sv_denot]. apply EPI.mrxk_ltu; lia. }
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* numbytes < 16: +0x13c, a0 = 0 *)
      rewrite HNS in Hc. apply Z.ltb_lt in Hc.
      assert (Hs0 : recv_send bytes = 0)
        by (rewrite rf_send_eq; apply RPL.rb_snd_len; [lia | exact HetOK | left; exact Hc]).
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (RECV_RF + 148).
      { rf_awr0. }
      rf_md.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into msF end.
      rf_kd HFr HG KD2 GR2 KD3 GR3 mem2. clear HF HFr HG.
      lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E3 := EF) in HS, SHOK end.
      assert (E3lo : forall nn, (nn < 1024)%nat -> ew E3 nn = ew E0 nn)
        by (intros nn Hnn; unfold E3, E2, E1; repeat rewrite ew_ewset_other by lia; reflexivity).
      rf_reg HS (Z_to_bv 5 10) (w64 (recv_send bytes)) Ya0 ltac:(rewrite Hs0; reflexivity).
      assert (KR : forall r, In r rf_keepl -> YK11.getr (ms_regs msF) (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)).
      { apply (rf_keep_regs rf_keepl E3 _ (w_H W2) msF regs2 HS); [rf_srget | rf_ewlo E3lo EE0]. }
      pmkst HS.
      rf_pc (RECV_RF + 148).
      exact (rf_join STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2 S2
        W2 mem2 md2 regs2 (ms_mem msF) _ (ms_regs msF) HPOLL HMRX HL HC HFIX HCUR HRES HBLK HTW HOPB HJ KD3 GR3 KR Ya0).
    * (* numbytes >= 16 *)
      rewrite HNS in Hc. apply Z.ltb_ge in Hc. rename Hc into HnbLo.
      (* run 3, +0x130 .. +0x138: `addi a1, s2, -14`; it stops at `bgeu a1, a0` *)
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { rf_awr0. }
      rf_md.
      rf_kd HFr HG KD2 GR2 KD3 GR3 mem2. clear HF HFr HG.
      lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E3 := EF) in * end.
      assert (E3lo : forall nn, (nn < 1024)%nat -> ew E3 nn = ew E0 nn)
        by (intros nn Hnn; unfold E3, E2, E1; repeat rewrite ew_ewset_other by lia; reflexivity).
      assert (DNB3 : sv_denot E3 (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 35 0)) =
        Z_to_bv 64 (DSpec.be16 bytes 14)).
      { rewrite BE14. apply (rf_den_or_add E3 _ _ (rfb bytes 14 * 2 ^ 8) (rfb bytes 15) 8).
        - apply rf_den_sll; [apply rf_den_atom; [rewrite E3lo by lia; exact A34 | lia] | lia | lia | lia].
        - apply rf_den_atom; [rewrite E3lo by lia; exact A35 | lia].
        - lia.
        - lia.
        - apply Z_mod_mult.
        - lia.
        - lia. }
      assert (B18 : ew E3 18 = w64 (Z.of_nat (length bytes)))
        by (rewrite E3lo by lia; exact (eq_trans (EE0 18%nat (Z_to_bv 5 18) eq_refl) Q18)).
      assert (HNL : branch_taken BC_GEU (sv_denot E3 (SOff 18 (-14)))
          (sv_denot E3 (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 35 0)))
        = negb (Z.of_nat (length bytes) - 14 <? DSpec.be16 bytes 14)).
      { rewrite DNB3. cbn [branch_taken sv_denot]. rewrite B18. unfold w64.
        rewrite unsigned_lit_small by lia. replace (Z.of_nat (length bytes) + -14) with (Z.of_nat (length bytes) - 14)
          by lia.
        rewrite EPI.mrxk_ltu by lia. reflexivity. }
      psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
      -- (* n - 14 >= numbytes: +0x2a4, the send value, `j` +0x140 *)
         rewrite HNL in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
         assert (Hs : recv_send bytes = DSpec.be32 bytes 18)
           by (rewrite rf_send_eq; apply RPL.rb_snd_ok; [lia | exact HetOK | lia]).
         (* run 4, +0x2a4 .. +0x31c: the checks and loads at a + 18 .. a + 21 *)
         paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (RECV_RF + 148).
         { rf_awr0. }
         rf_md.
         lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into msF end.
         rf_kd HFr HG KD3 GR3 KD4 GR4 mem2. clear HF HFr HG.
         lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E4 := EF) in HS, SHOK end.
         assert (E4lo : forall nn, (nn < 1024)%nat -> ew E4 nn = ew E0 nn)
           by (intros nn Hnn; unfold E4, E3, E2, E1; repeat rewrite ew_ewset_other by lia; reflexivity).
         assert (D32 : sv_denot E4
             (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 16)) (SAlu ALU_SLL (SOff 36 0) (SLit 24)))
                (SAlu ALU_OR (SAlu ALU_SLL (SOff 38 0) (SLit 8)) (SOff 39 0)))
           = w64 (recv_send bytes)).
         { rewrite Hs, rf_be32. unfold w64.
           replace (rfb bytes 18 * 2 ^ 24 + rfb bytes 19 * 2 ^ 16 + rfb bytes 20 * 2 ^ 8 + rfb bytes 21)
             with ((rfb bytes 18 * 2 ^ 24 + rfb bytes 19 * 2 ^ 16) + (rfb bytes 20 * 2 ^ 8 + rfb bytes 21)) by lia.
           apply (rf_den_or_add E4 _ _ (rfb bytes 18 * 2 ^ 24 + rfb bytes 19 * 2 ^ 16)
             (rfb bytes 20 * 2 ^ 8 + rfb bytes 21) 16).
           - apply (rf_den_or_add' E4 _ _ (rfb bytes 18 * 2 ^ 24) (rfb bytes 19 * 2 ^ 16) 24).
             + apply rf_den_sll; [apply rf_den_atom; [rewrite E4lo by lia; exact A36 | lia] | lia | lia | lia].
             + apply rf_den_sll; [apply rf_den_atom; [rewrite E4lo by lia; exact A37 | lia] | lia | lia | lia].
             + lia.
             + lia.
             + apply Z_mod_mult.
             + lia.
             + lia.
           - apply (rf_den_or_add E4 _ _ (rfb bytes 20 * 2 ^ 8) (rfb bytes 21) 8).
             + apply rf_den_sll; [apply rf_den_atom; [rewrite E4lo by lia; exact A38 | lia] | lia | lia | lia].
             + apply rf_den_atom; [rewrite E4lo by lia; exact A39 | lia].
             + lia.
             + lia.
             + apply Z_mod_mult.
             + lia.
             + lia.
           - lia.
           - lia.
           - replace (rfb bytes 18 * 2 ^ 24 + rfb bytes 19 * 2 ^ 16) with ((rfb bytes 18 * 2 ^ 8 + rfb bytes 19) * 2 ^ 16)
               by lia.
             apply Z_mod_mult.
           - lia.
           - lia. }
         rf_reg HS (Z_to_bv 5 10) (w64 (recv_send bytes)) Ya0 ltac:(exact D32).
         assert (KR : forall r, In r rf_keepl ->
           YK11.getr (ms_regs msF) (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)).
         { apply (rf_keep_regs rf_keepl E4 _ (w_H W2) msF regs2 HS); [rf_srget | rf_ewlo E4lo EE0]. }
         pmkst HS.
         rf_pc (RECV_RF + 148).
         exact (rf_join STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2
           S2 W2 mem2 md2 regs2 (ms_mem msF) _ (ms_regs msF) HPOLL HMRX HL HC HFIX HCUR HRES HBLK HTW HOPB HJ KD4 GR4
           KR Ya0).
      -- (* n - 14 < numbytes: +0x13c, a0 = 0 *)
         rewrite HNL in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
         assert (Hs0 : recv_send bytes = 0)
           by (rewrite rf_send_eq; apply RPL.rb_snd_len; [lia | exact HetOK | right; exact Hc]).
         paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (RECV_RF + 148).
         { rf_awr0. }
         rf_md.
         lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into msF end.
         rf_kd HFr HG KD3 GR3 KD4 GR4 mem2. clear HF HFr HG.
         lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E4 := EF) in HS, SHOK end.
         assert (E4lo : forall nn, (nn < 1024)%nat -> ew E4 nn = ew E0 nn)
           by (intros nn Hnn; unfold E4, E3, E2, E1; repeat rewrite ew_ewset_other by lia; reflexivity).
         rf_reg HS (Z_to_bv 5 10) (w64 (recv_send bytes)) Ya0 ltac:(rewrite Hs0; reflexivity).
         assert (KR : forall r, In r rf_keepl ->
           YK11.getr (ms_regs msF) (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)).
         { apply (rf_keep_regs rf_keepl E4 _ (w_H W2) msF regs2 HS); [rf_srget | rf_ewlo E4lo EE0]. }
         pmkst HS.
         rf_pc (RECV_RF + 148).
         exact (rf_join STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2
           S2 W2 mem2 md2 regs2 (ms_mem msF) _ (ms_regs msF) HPOLL HMRX HL HC HFIX HCUR HRES HBLK HTW HOPB HJ KD4 GR4
           KR Ya0).
Qed.

End s.
