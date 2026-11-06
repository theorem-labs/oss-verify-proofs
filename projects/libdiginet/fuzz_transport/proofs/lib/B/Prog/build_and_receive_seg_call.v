(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 536 of its 589 lines of code are new or changed and 1871 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/diginet_session_poll_seg_rel.v, with its module names changed; 1091 of its 1210 lines of code are new or changed and 470 lines of the source are left out. *)
(* build_and_receive_seg_call (image B): Theorem bar_call_piece : bar_call_stmt (lib/B/Prog/build_and_receive_segs.v),
   the piece of the image-B walk of build_and_receive (fuzz_transport.asan-ubsan 0x85998 = transportb_sigma
   TB_build_and_receive) from the cut BAR_CALL (+0x270, the join of the body sum's exit and of the len = 0 path) to the
   call of receive at +0x370, whose return address is the cut BAR_REL. The image-A twin is
   lib/A/Prog/build_and_receive_seg_call.v; image B's code adds a UBSan test of the address after each store.
     run 1  +0x270 .. +0x340  the fourteen plain byte stores of frame[16 .. 30) through s9 = frame[]: the body sum
                              cut to 16 bits (a1 >> 8, a1), 0, 0, the two low bytes of send (the slot s1 + 48; its
                              two high bytes are 0, since send < 2 ^ 16), the four bytes of ack (from s8), 0 and the
                              low byte of retry (the slot s1 + 40), the low byte of cmd (the slot s1 + 32), and
                              ncmds = 1. Between the stores, thirteen UBSan tests of frame[] + 16 .. frame[] + 29
                              (`beq a0, -1` or `bltu -k, s9` / `bltu -k, a0`, at +0x280, +0x28c, +0x2a0, +0x2ac, +0x2bc,
                              +0x2c8, +0x2dc, +0x2ec, +0x2fc, +0x308, +0x318, +0x328, +0x338) to the trap word at
                              +0x3ec: the engine decides each one not taken from the fact on s9 (4096 <= F + 32 <=
                              2 ^ 47: the own frame lies below alloc_ceiling, YCbq.v frames_bounds).
     +0x344                   `beqz s3`: an empty body skips the body memcpy (to the join +0x360).
     run 2  +0x348 .. +0x358  the UBSan test of frame[] + 30 (`bltu -31, s9` at +0x34c, not taken by the same fact),
                              a0 = frame[] + 30, a1 = s4 = bodyp, a2 = len, up to `jal __asan_memcpy` (+0x35c), which
                              writes frame[30 .. 30 + len) = body (TransportGCg.v gx_intrin_at, OCpy).
     run 3  +0x360 .. +0x36c  a1 = n = s5 + 30, a0 = frame[], a2 = by_poll = 0, a3 = poll_flags = 0.
     +0x370                   `jal receive`, a G-form callee in the same journal (receive_cg.v
                              transport_receive_cg at the contexts bar_recv_ctx CTX), whose post is the piece's
                              own post but for the frame, which the release piece then gives back.
   After the stores the frame's n bytes are bar_frame dst src send ack retry cmd body (bc_frame_split, byte by byte
   through garr8_app): the sixteen the mid piece left, the fourteen this run writes, the body, and the memset's
   zeros beyond it. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import notice_cg io_send_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import build_and_receive_cg build_and_receive_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TNeed TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TGNA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The fourteen bytes the run writes, and the frame's split         *)
(* ------------------------------------------------------------------ *)

(* frame[16 .. 30): the body sum cut to 16 bits, send, ack, retry, cmd and ncmds = 1. *)
Definition bc_hdr14 (send ack retry cmd : Z) (body : list byte) : list byte :=
  DSpec.put16 (DSpec.spec_sum body) ++ DSpec.put32 send ++ DSpec.put32 ack ++ DSpec.put16 retry ++
  [DSpec.b8 cmd; DSpec.b8 1].

Lemma bc_hdr14_len : forall s a r c b, length (bc_hdr14 s a r c b) = 14%nat.
Proof. intros. unfold bc_hdr14, DSpec.put16, DSpec.put32. cbn [length app]. reflexivity. Qed.

(* The frame, as the three pieces that write it leave it: the mid piece's sixteen bytes, this run's fourteen, the
   body, and the memset's zeros past it. *)
Lemma bc_frame_split : forall (dst src : list byte) (send ack retry cmd : Z) (body : list byte),
  length dst = 6%nat -> length src = 6%nat ->
  bar_frame dst src send ack retry cmd body =
  bar_pre16 dst src body ++ bc_hdr14 send ack retry cmd body ++ body
    ++ repeat (DSpec.b8 0) (30 - length body)%nat.
Proof.
  intros dst src send ack retry cmd body Hd Hs.
  rewrite (bar_frame_shape dst src send ack retry cmd body Hd Hs).
  unfold bar_pre16, bar_hdr, bc_hdr14, bar_len.
  rewrite <- !app_assoc. reflexivity.
Qed.

(* ---- the bytes of a register, as the model's b8 ---- *)

Lemma bc_b8_eq : forall x y, x mod 256 = y mod 256 -> DSpec.b8 x = DSpec.b8 y.
Proof.
  intros x y H. unfold DSpec.b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. exact H.
Qed.

(* The byte at bit 8j of a register holding x is the model's byte of x cut to w bits (j + 8 <= w). *)
Lemma bc_b8_modw : forall x y j w, 0 <= j -> j + 8 <= w -> x mod 2 ^ w = y ->
  DSpec.b8 (x / 2 ^ j) = DSpec.b8 (y / 2 ^ j).
Proof.
  intros x y j w Hj Hjw Hxy. apply bc_b8_eq.
  assert (Hw : 0 < 2 ^ w) by (apply Z.pow_pos_nonneg; lia).
  assert (Hj0 : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (Hs1 : 2 ^ w = 2 ^ (w - j) * 2 ^ j) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hs2 : 2 ^ (w - j) = 2 ^ (w - j - 8) * 256)
    by (change 256 with (2 ^ 8); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Ex : x = y + (2 ^ (w - j) * (x / 2 ^ w)) * 2 ^ j)
    by (pose proof (Z.mod_eq x (2 ^ w) ltac:(lia)); rewrite Hxy in *; nia).
  rewrite Ex at 1. rewrite Z.div_add by lia.
  replace (2 ^ (w - j) * (x / 2 ^ w)) with ((2 ^ (w - j - 8) * (x / 2 ^ w)) * 256) by nia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

(* The model's sum of the body is the machine sum cut to 16 bits (DgnSpec.v spec_sum_eq, sum16). *)
Lemma bc_sum_eq : forall body, DSpec.spec_sum body = DSpec.sum_bytes body mod 2 ^ 16.
Proof. intros body. rewrite DSpec.spec_sum_eq. reflexivity. Qed.

Lemma bc_sum_range : forall body, Z.of_nat (length body) <= 1484 ->
  0 <= DSpec.sum_bytes body <= 255 * 1484.
Proof.
  intros body H. pose proof (DSpec.sum_bytes_range body) as R. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The byte values of the fourteen stores                           *)
(* ------------------------------------------------------------------ *)

(* The fourteen bytes the code stores, in the order of frame[16 .. 30), are bc_hdr14's, given the register widths
   the contract fixes: send < 2 ^ 16 (so its two high bytes are 0), ack < 2 ^ 32, retry < 2 ^ 8 (so put16 retry's
   high byte is 0), cmd < 2 ^ 8. sm is the machine sum in a1, aw the send register, bw the ack register. *)
Lemma bc_b8_mod16 : forall x, DSpec.b8 (x mod 2 ^ 16) = DSpec.b8 x.
Proof. intros x. apply bc_b8_eq. apply Z.mod_mod_divide. exists (2 ^ 8). reflexivity. Qed.
Lemma bc_b8_mod32 : forall x, DSpec.b8 (x mod 2 ^ 32) = DSpec.b8 x.
Proof. intros x. apply bc_b8_eq. apply Z.mod_mod_divide. exists (2 ^ 24). reflexivity. Qed.

Lemma bc_hdr14_bytes : forall (aw bw : word) (send ack retry cmd sm : Z) (body : list byte),
  bv_unsigned aw mod 2 ^ 32 = send -> 0 <= send < 2 ^ 16 ->
  bv_unsigned bw mod 2 ^ 32 = ack -> 0 <= ack < 2 ^ 32 ->
  0 <= retry < 2 ^ 8 -> 0 <= cmd < 2 ^ 8 ->
  sm = DSpec.sum_bytes body ->
  bc_hdr14 send ack retry cmd body =
  [DSpec.b8 (sm / 2 ^ 8); DSpec.b8 sm; DSpec.b8 0; DSpec.b8 0;
   DSpec.b8 (bv_unsigned aw / 2 ^ 8); DSpec.b8 (bv_unsigned aw);
   DSpec.b8 (bv_unsigned bw / 2 ^ 24); DSpec.b8 (bv_unsigned bw / 2 ^ 16);
   DSpec.b8 (bv_unsigned bw / 2 ^ 8); DSpec.b8 (bv_unsigned bw);
   DSpec.b8 0; DSpec.b8 retry; DSpec.b8 cmd; DSpec.b8 1].
Proof.
  intros aw bw send ack retry cmd sm body HA HS HB HK HR HC HSM.
  unfold bc_hdr14, DSpec.put16, DSpec.put32. cbn [app].
  rewrite bc_sum_eq, <- HSM.
  repeat (apply f_equal2;
    [ first [ symmetry; exact (bc_b8_modw sm (sm mod 2 ^ 16) 8 16 ltac:(lia) ltac:(lia) eq_refl)
            | exact (bc_b8_mod16 sm)
            | symmetry; exact (bc_b8_modw (bv_unsigned aw) send 8 32 ltac:(lia) ltac:(lia) HA)
            | rewrite <- HA; exact (bc_b8_mod32 (bv_unsigned aw))
            | symmetry; exact (bc_b8_modw (bv_unsigned bw) ack 24 32 ltac:(lia) ltac:(lia) HB)
            | symmetry; exact (bc_b8_modw (bv_unsigned bw) ack 16 32 ltac:(lia) ltac:(lia) HB)
            | symmetry; exact (bc_b8_modw (bv_unsigned bw) ack 8 32 ltac:(lia) ltac:(lia) HB)
            | rewrite <- HB; exact (bc_b8_mod32 (bv_unsigned bw))
            | f_equal; apply Z.div_small; lia
            | reflexivity ]
    | ]).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The branch on len, the return point of the body memcpy (the join of the two paths), and the return point of the
   call of receive, as offsets of the listing. *)
Definition BC_BR : Z := AF_build_and_receive + 0x344.
Definition BC_JOIN : Z := AF_build_and_receive + 0x360.
Definition BC_B0 : Z * Z := (0, 0).
Lemma bc_offs : AF_build_and_receive + 0x360 = 19032 /\ AF_build_and_receive + 0x374 = 19052.
Proof. split; reflexivity. Qed.

(* run 1, +0x270: frame[16 .. 30) through s9 (atom 25), and the three slots of the own machine frame through
   s1 (atom 9): cmd (atom 34) at s1 + 32, retry (atom 33) at s1 + 40 and the send register's value (atom 32) at
   s1 + 48. The fact on s9 decides the thirteen UBSan tests of the run. *)
Definition bc_rg_hdr : YP09.region := YP09.mkRegion (Some 25%nat) 16 30 16 30 [].
Definition bc_rg_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 32 56 0 0
    [YP09.mkChunk 32 (CVal 8 (SOff 34 0)); YP09.mkChunk 40 (CVal 8 (SOff 33 0));
     YP09.mkChunk 48 (CVal 8 (SOff 32 0))].
Definition bc_facts1 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (25%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition ss_bc1 : sstate := mkSS BAR_CALL sr_atoms [bc_rg_hdr; bc_rg_slots] None bc_facts1.

(* +0x344, the branch on s3 (len), from a state with no region; the fact on s9 decides the UBSan test of
   frame[] + 30 at +0x34c on the len <> 0 path. *)
Definition bc_factsF : facts := mkFacts [(25%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition ss_bcbr : sstate := mkSS BC_BR sr_atoms [] None bc_factsF.

(* run 3, +0x360: four register moves before the call of receive, no region. *)
Definition ss_bc3 : sstate := mkSS BC_JOIN sr_atoms [] None (mkFacts [] [] []).

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac bc_reg HS r v H tac :=
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
Ltac bc_kreg HS EW r n Q H :=
  lazymatch type of Q with _ = ?v =>
    bc_reg HS r v H ltac:(cbn [sv_denot]; rewrite (EW n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac bc_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
Ltac bc_frame_kept HFr Zs U :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
  intros a Ha Hn; apply (kept_of_frame _ _ _ _ _ Zs HFr); [| exact Ha | exact Hn];
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as <- <- <-; cbn [base_val] in Hx; cbv beta; first [exfalso; lia | rewrite U in Hx; lia] |]);
  destruct Hin.

(* A byte of a 2048-byte frame in application memory is not one of the frame's shadow bytes. *)
Lemma bc_frame_not_shadow {rc : YM05.RunCeil} : forall F i, in_app F 2048 -> 0 <= i < 2048 ->
  ~ (SHADOW_OFF + F / 8 <= F + i < SHADOW_OFF + F / 8 + 256).
Proof.
intros F i (H4 & [HL | (HH & _)]) Hi; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *;
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le F 8 ltac:(lia)); lia.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The valuation of run 1: the 32 registers and the three slot values. *)
Definition bc_E (regs : bvmap 5 word) (sv rv cv : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 sv; w64 rv; w64 cv]).
Definition bc_E0 (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Lemma bc_entry1 : forall (W : world segs) regs mem (F sp1 sv rv cv : Z),
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 25 = w64 (F + 32) ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= F -> F + 2048 <= sp1 ->
  0 <= sv < 2 ^ 64 -> 0 <= rv < 2 ^ 64 -> 0 <= cv < 2 ^ 64 ->
  (forall a, F + 32 + 16 <= a < F + 32 + 30 -> apresent (w_H W) mem a) ->
  rdword (aview segs (w_H W) mem) (sp1 + 32) = Some cv ->
  rdword (aview segs (w_H W) mem) (sp1 + 40) = Some rv ->
  rdword (aview segs (w_H W) mem) (sp1 + 48) = Some sv ->
  st_ok_pi segs VAL (bc_E regs sv rv cv) ss_bc1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + BAR_CALL)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F sp1 sv rv cv R9 R25 Hsp Hsp32 HF0 HFs Hsv Hrv Hcv Hpres Hr32 Hr40 Hr48.
set (E := bc_E regs sv rv cv).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, bc_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 sv)
  by (unfold E, bc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 rv)
  by (unfold E, bc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 cv)
  by (unfold E, bc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = F + 32)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_bc1.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [bc_rg_hdr bc_rg_slots YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U25. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val segs E _ sp1 32 8 (SOff 34 0) cv);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
      exact (val_mem_of_rdword segs _ _ _ _ Hr32).
    * apply (chunk_ok_val segs E _ sp1 40 8 (SOff 33 0) rv);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
      exact (val_mem_of_rdword segs _ _ _ _ Hr40).
    * apply (chunk_ok_val segs E _ sp1 48 8 (SOff 32 0) sv);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
      exact (val_mem_of_rdword segs _ _ _ _ Hr48).
- apply pairwise_disjoint_of_extents.
  unfold bc_rg_hdr, bc_rg_slots, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U25. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold bc_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U25.
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The state of the branch on len: no region, the fact on s9. *)
Lemma bc_entryF : forall (W : world segs) regs mem (F : Z),
  YK11.getr regs 25 = w64 (F + 32) -> 4096 <= F -> F + 32 <= 2 ^ 47 ->
  st_ok_pi segs VAL (bc_E0 regs) ss_bcbr
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + BC_BR)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F R25 HF0 HF47.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (bc_E0 regs) n = YK11.getr regs r)
  by (intros n r Hn; unfold bc_E0; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U25 : bv_unsigned (ew (bc_E0 regs) 25) = F + 32)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_bcbr.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold bc_factsF, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* A state with no region, at any pc of this piece. *)
Lemma bc_entry0 : forall (W : world segs) regs mem (ss : sstate) (pc : Z),
  ss = mkSS pc sr_atoms [] None (mkFacts [] [] []) ->
  st_ok_pi segs VAL (bc_E0 regs) ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem ss pc ->. rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.
(* ------------------------------------------------------------------ *)
(* 4. The frame's bytes as a callee's range                            *)
(* ------------------------------------------------------------------ *)

(* frame[0 .. n) for n <= SPEC_MAX_FRAME, at a state of bar_run and a callee's window [sp' - K, sp') inside the
   statement's: placed in the own frame, readable (its shadow bytes 4 .. 192 are 0 and byte 193 is 2, so every
   granule of frame[0 .. 1514) is addressable), writable by the callee, outside G and outside the window. *)
Lemma bc_buf_at : forall c pos S2 mem2 md2 (regs' : bvmap 5 word) (K n : Z),
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bar_run B MT c pos S2 mem2 md2 ->
  spZ regs' = bar_sp1 c -> 0 <= K -> bar_SP c - BAR_STK <= spZ regs' - K -> 0 <= n <= 1514 ->
  decode_in_fake (cx_lyc c) S2 (bar_F c pos + 32) n /\
  decode_rd_ok (cx_W c) mem2 (bar_F c pos + 32) n /\
  trans_src_ok B (cx_lyc c) S2 (cx_W c) mem2 (bar_F c pos + 32) n /\
  transport_twr_ok_g segs B TG.G_HARNESS_B (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_lyc c) S2
    ((BAR_CID, pos) :: cx_own c) (cx_W c) mem2 (spZ regs') (bar_F c pos + 32) n /\
  decode_off_win regs' K (bar_F c pos + 32) n /\
  (forall x, bar_F c pos + 32 <= x < bar_F c pos + 32 + n -> ~ W_journalG.inG TG.G_HARNESS_B x).
Proof using All.
intros c pos S2 mem2 md2 regs' K n HRT HOK HRUN USP HK0 HKw Hn.
pose proof HRT as (_ & _ & _ & _ & _ & _ & LAWS & _).
destruct (bar_ok_sp B MT c HOK) as (HARc & HSPr & HCE & _ & _ & _ & _ & _ & HS1al & HS1r & Hwin0 & _).
destruct HRUN as (HCUR & Heab & _ & _ & HSH0 & HSH2 & _).
destruct HCUR as (HJ2 & _ & Hfrs & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin : In (BAR_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (ERS : ESTACK <= RECV_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (EBS : BAR_STK = 208 + RECV_STK) by exact bar_stk_eq.
destruct (al_frames _ _ LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin) as (_ & HFapp & HFpres & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ BAR_CID pos HAR2 Hin) as (HF64 & _ & _).
pose proof (fun a Ha => frm_img segs B LAWS _ _ _ _ _ BAR_CID pos a HAR2 Hin Ha) as HFimg.
rewrite bar_fbytes in HFapp, HFpres, HFc, HFsh, HFimg.
change (BAR_FBYTES / 8) with 256 in HFsh. unfold BAR_FBYTES in HFapp, HFpres, HFc, HFsh, HFimg.
set (F := frame_addr (cx_lyc c) BAR_CID pos) in *.
assert (EF : bar_F c pos = F) by reflexivity.
rewrite EF.
assert (DF8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
  pose proof (Z.div_mod F 8 ltac:(lia)) as D8.
  assert (M8 : F mod 8 = 0).
  { rewrite D. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  rewrite M8, Z.add_0_r in D8. exact D8. }
(* placed in the own frame *)
assert (HDF : decode_in_fake (cx_lyc c) S2 (F + 32) n)
  by (exists BAR_CID, pos; rewrite bar_fbytes; unfold BAR_FBYTES; split; [exact Hin | lia]).
(* addressable: shadow bytes 4 .. 192 are 0 (whole granules) and byte 193 is 2 (frame + 1544, + 1545) *)
assert (HRA : range_addressable (aview segs (w_H (cx_W c)) mem2) SHADOW_OFF (F + 32) n).
{ intros x Hx. unfold shadow_of_addr.
  assert (Ex : x / 8 = F / 8 + (x - F) / 8)
    by (replace x with (F / 8 * 8 + (x - F)) at 1 by lia; apply Z.div_add_l; lia).
  rewrite Ex, Z.add_assoc.
  destruct (Z_lt_ge_dec x (F + 1544)) as [Hlt | Hge].
  - exists 0. split; [|left; reflexivity].
    apply HSH0. split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
  - assert (Eq : (x - F) / 8 = 193)
      by (symmetry; apply (Z.div_unique _ _ _ (x - F - 1544)); lia).
    rewrite Eq. exists 2. split; [exact HSH2|]. right.
    assert (Em : x mod 8 = x - F - 1544) by (symmetry; apply (Z.mod_unique _ _ (F / 8 + 193)); lia).
    rewrite Em. lia. }
assert (HH1 : forall m, 1 <= m -> F + 32 + m <= F + 2048 ->
  shadow_hull_vis (aview segs (w_H (cx_W c)) mem2) (F + 32) m).
{ intros m Hm1 Hm2. apply (TGNA.frame_hull_vis _ F 2048 (F + 32) m);
    [lia | exact HF64 | reflexivity | lia | lia | lia |].
  intros i Hi. change (2048 / 8) with 256 in Hi. apply aview_some_of_apresent. exact (proj1 (HFsh i Hi)). }
assert (HRD : decode_rd_ok (cx_W c) mem2 (F + 32) n).
{ split; [intros a Ha; apply aview_some_of_apresent; exact (proj1 (HFpres a ltac:(lia)))|].
  split; [exact HRA|].
  split.
  { destruct (Z.eq_dec n 0) as [-> | Hn0].
    - apply (trans_hull_sub _ (F + 32) 1 (F + 32) 0); [apply HH1; lia | lia | lia].
    - apply HH1; lia. }
  split; [apply (amem_range_sub_app F 2048); [exact HFapp | lia | lia | lia | lia]|].
  split; lia. }
split; [exact HDF|]. split; [exact HRD|].
split; [right; split; [left; exact HDF | exact HRD]|].
split.
{ eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|].
  intros a Ha. left. split.
  - unfold awr_byte. right; right; right. unfold in_frames. exists BAR_CID, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite bar_fbytes. unfold BAR_FBYTES. lia.
  - rewrite USP. lia. }
split; [unfold decode_off_win; left; lia|].
intros x Hx Hg. exact (HFimg x ltac:(lia) (trans_g_img x Hg)).
Qed.

(* ------------------------------------------------------------------ *)
(* 5. bar_run over a step that writes only bytes of the own frame      *)
(* ------------------------------------------------------------------ *)

(* The fourteen header stores and the body memcpy change only bytes of frame[0 .. 1546), inside the own frame and
   below its last word, so everything bar_run states carries: the journal is the step's, the call's kept fact by
   TransportGFrame.v dk_kept_nfz_gw (a byte of the own frame is dkg_nf), the 13 saved words, the frame's last word
   and the slot s1 + 24 because they lie outside [lo, hi), the shadow clauses because a byte of a frame in
   application memory is never one of that frame's shadow bytes (in_app), and G because a byte of G is an image
   byte while the frame is apart from the image. *)
Lemma bc_keep_frame : forall c pos S2 mem2 md2 mem3 md3 (lo hi : Z),
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bar_run B MT c pos S2 mem2 md2 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c)
    (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c) ((BAR_CID, pos) :: cx_own c) (cx_lyc c) S2 (cx_W c) mem3 md3
    (cx_k c + 0) ->
  bar_F c pos <= lo -> hi <= bar_F c pos + 2040 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     aview segs (w_H (cx_W c)) mem3 a = aview segs (w_H (cx_W c)) mem2 a) ->
  (forall a, apresent (w_H (cx_W c)) mem2 a -> apresent (w_H (cx_W c)) mem3 a) ->
  bar_run B MT c pos S2 mem3 md3.
Proof using All.
intros c pos S2 mem2 md2 mem3 md3 lo hi HRT HOK HRUN HJ3 Hlo2 Hhi2 KD GR.
pose proof HRT as (_ & _ & _ & _ & _ & _ & LAWS & MTL & _ & _ & FFL & HGX & _).
destruct (bar_ok_sp B MT c HOK) as (HARc & HSPr & HCE & _ & _ & _ & _ & _ & _ & HS1r & Hwin0 & _).
destruct HRUN as (HCUR & Heab & Hmo0 & HGK & HSH0 & HSH2 & HPR).
destruct HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw & HSL24).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin : In (BAR_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_frames _ _ LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin) as (_ & HFapp & _ & _).
destruct (frames_bounds segs B LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin) as (HF0 & HFc & _).
pose proof (fun a Ha => frm_img segs B LAWS _ _ _ _ _ BAR_CID pos a HAR2 Hin Ha) as HFimg.
rewrite bar_fbytes in HFapp, HFc, HFimg. unfold BAR_FBYTES in HFapp, HFc, HFimg.
set (F := frame_addr (cx_lyc c) BAR_CID pos) in *.
assert (EF : bar_F c pos = F) by reflexivity.
rewrite EF in Hlo2, Hhi2, HSH0, HSH2, HFLw, HSL24.
assert (Hbl : forall bm, In bm (ablocks B (cx_lyc c) (cx_Sc c)) -> In bm (ablocks B (cx_lyc c) S2))
  by (intros bm Hb; rewrite Heab; exact Hb).
assert (HZ : forall a, lo <= a < hi -> dkg_nf BAR_CID F (flag_addr (cx_lyc c) BAR_CID pos) a).
{ intros a Ha. unfold dkg_nf. left. rewrite bar_fbytes. unfold BAR_FBYTES. lia. }
assert (HNS : forall i, 0 <= i < 256 -> ~ (lo <= SHADOW_OFF + F / 8 + i < hi)).
{ intros i Hi Hx.
  pose proof (bc_frame_not_shadow F (SHADOW_OFF + F / 8 + i - F) HFapp ltac:(lia)) as HN.
  apply HN. lia. }
assert (EBS2 : BAR_STK = 208 + RECV_STK) by exact bar_stk_eq.
assert (ERS2 : 0 <= RECV_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSEP : hi + 8 <= bar_SP c - BAR_STK) by lia.
split.
{ split; [exact HJ3|].
  split; [exact He|]. split; [exact Hfrs|]. split; [exact Hperm|]. split; [exact HlyF|]. split; [exact Hmo|].
  split.
  { apply (dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B (cx_lyc c) (cx_Sc c) (cx_lyc c) S2
      (cx_W c) (cx_memc c) (cx_mdc c) (cx_W c) mem2 md2 mem2 mem3 (bar_SP c - BAR_STK) (bar_SP c) BAR_CID pos
      F (flag_addr (cx_lyc c) BAR_CID pos) (recv_wr (bar_fr c)) (fun a => lo <= a < hi)
      HGX HARc HAR2 Hfrs Hbl eq_refl eq_refl eq_refl FFL HCE ltac:(lia));
    [intros a Ha; right; left; exact (HZ a Ha) | exact HK | exact KD | exact GR]. }
  split.
  { rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
    assert (Hob : 8 <= fst o <= 104).
    { unfold BAR_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia |]). destruct Ho. }
    apply rdword_ext. intros k Hk. apply KD; lia. }
  split.
  { rewrite <- HFLw. unfold BAR_FBYTES. apply rdword_ext. intros k Hk. apply KD; lia. }
  change (bar_F c pos) with F. rewrite <- HSL24. apply rdword_ext. intros k Hk. apply KD; lia. }
split; [exact Heab|]. split; [exact Hmo0|].
split.
{ intros a Hg. rewrite <- (HGK a Hg).
  destruct (HGX a Hg) as [HiG _].
  pose proof (transportb_segs_low a HiG) as Hl. unfold kLowMemEnd in Hl.
  apply KD; [lia|]. intros Hx. exact (HFimg a ltac:(lia) HiG). }
split; [intros i Hi; rewrite KD; [exact (HSH0 i Hi) | unfold SHADOW_OFF in *; lia | apply HNS; lia]|].
split; [rewrite KD; [exact HSH2 | unfold SHADOW_OFF in *; lia | apply HNS; lia]|].
intros a Ha Hp. exact (GR a (HPR a Ha Hp)).
Qed.

(* ------------------------------------------------------------------ *)
(* 6. receive's written range lies in G's hull                         *)
(* ------------------------------------------------------------------ *)

(* The bounds of a byte of one row twb_fld o b A n of a harness global: computed when every argument is closed, else
   (an array entry at an index) the row's address unfolded to the index (diginet_session_poll_seg_kit.v pwh_fld). *)
Ltac bcw_fld H :=
  lazymatch type of H with
  | twb_fld _ _ (TW.A_OW_t_state _) _ _ => unfold twb_fld, TW.A_OW_t_state, TW.OW_t_ESZ, TW.OFF_OW, TB_OW in H
  | twb_fld _ _ (TC.A_OW_dn_body _) _ _ => unfold twb_fld, TC.A_OW_dn_body, TW.OFF_OW, TB_OW in H
  | twb_fld _ _ (TW.A_Cmd_st _) _ _ => unfold twb_fld, TW.A_Cmd_st, TW.OFF_g_cmd, TB_g_cmd in H
  | twb_fld _ _ (TW.A_S_queue_bytes _) _ _ =>
      unfold twb_fld, TW.A_S_queue_bytes, TW.S_queue_ESZ, TW.OFF_g_s, TB_g_s in H
  | twb_fld ?o ?b ?A ?n ?x =>
      let lo := eval vm_compute in (b + (A - o)) in
      let ln := eval vm_compute in n in
      change (lo <= x < lo + ln) in H
  end.
(* Each written-range predicate unfolded down to its rows (twb_fld rows, a notice's rows by TransportGNoticeB.v
   notice_wr_G); any other predicate is unfolded by its head (hnf). *)
Ltac bcw_go H :=
  lazymatch type of H with
  | False => destruct H
  | _ \/ _ => let H1 := fresh "Hw" in let H2 := fresh "Hw" in destruct H as [H1 | H2]; [bcw_go H1 | bcw_go H2]
  | ex _ => let x := fresh "i" in let H1 := fresh "Hw" in destruct H as [x H1]; bcw_go H1
  | (_ <= _ < _) /\ _ => let H1 := fresh "Hb" in let H2 := fresh "Hw" in destruct H as [H1 H2]; bcw_go H2
  | _ /\ _ => let H2 := fresh "Hw" in destruct H as [_ H2]; bcw_go H2
  | notice_wr _ _ _ => exact (inG_G_HARNESS_hull _ (notice_wr_G _ _ _ H))
  | twb_fld _ _ _ _ _ =>
      bcw_fld H; unfold TC.TRANS_MAX, TW.OW_dn_N, TC.CMDS_MAX, TW.S_queue_N, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in *;
      lia
  | ?T => first [progress (hnf in H) | idtac "bcw_go: stuck at" T; fail 1]; bcw_go H
  end.

(* Every byte some path of receive stores (receive_cg.v recv_wr) lies in G's hull [G_HARNESS_B_LO, G_HARNESS_B_HI). *)
Lemma bc_wr_hull : forall (bytes : list byte) a, recv_wr bytes a -> TG.G_HARNESS_B_LO <= a < TG.G_HARNESS_B_HI.
Proof. intros bytes a H. unfold recv_wr in H. bcw_go H. Qed.

(* G's hull lies inside one loaded segment of the image (decided by vm_compute). *)
Lemma bc_hull_img : forall a, TG.G_HARNESS_B_LO <= a < TG.G_HARNESS_B_HI -> in_img tfibsegs a.
Proof.
intros a Ha.
apply (decode_seg_covers_img [(TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO)] a).
- vm_compute. reflexivity.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 7. A caller's range carried to a state of the walk                  *)
(* ------------------------------------------------------------------ *)

(* A range that may hold bytes of G (kept by gx_kept) and a written range E inside G's hull (so no byte of a
   caller's block or frame is in it): the range's bytes are kept and its placement holds at the later state. *)
Lemma bc_src_kept : trans_ro_rd_unowned B -> trans_rom_no_errno B -> AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi E ->
  gx_kept segs TG.G_HARNESS_B W memc W2 mem2 ->
  (forall a, E a -> TG.G_HARNESS_B_LO <= a < TG.G_HARNESS_B_HI) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok B lyc Sc W memc q n -> 0 < n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
intros HRU HRE LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hbl Hfr Hfa Elo Ehi
  (K1 & K2 & K3 & K4 & _) HGK HEh Hoff Hs Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HEi : forall a, E a -> in_img segs a) by (intros a Ha; exact (bc_hull_img a (HEh a Ha))).
assert (HnEs : forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a).
{ intros a Ha Hx. pose proof (HEh a Hx). unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI, kLowMemEnd in *. lia. }
assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
   in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
   aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
{ intros cid pos s Hin Hs'. apply (K4 cid pos s Hin (or_intror Hs')). apply HnEs.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold in_zr in Hs'. cbn [fst snd] in Hs'.
  unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a Ha. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
    replace a with (bA + (a - bA)) by lia.
    apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia.
    intros Hx. exact (blk_img segs B LAWS lyc Sc W memc mdc bA nA a HAR Hin ltac:(lia) (HEi a Hx)).
  - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
    + apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia|].
      intros Hx. exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(lia) (HEi a Hx)).
    + exact (HGK a (HG a Ha)).
    + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2]. apply K1; lia.
    + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
      apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
      intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
      unfold TG.G_HARNESS_B_LO in Gh. lia. }
split; [|exact KV].
destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
{ left. exists bA, nA. split; [exact (Hbl _ Hin) | lia]. }
assert (Hrd2 : decode_rd_ok W2 mem2 q n).
{ destruct HL as [HF | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
  + apply (decode_rd_ok_fake_kept B LAWS lyc Sc W W2 memc mem2 mdc q n HAR HF Hrd Hn KV).
    intros cid pos s Hin Hs'. exact (KS cid pos s Hin Hs').
  + destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
  + destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q n HAR2 Hn ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia))
      as [Ha Hh].
    exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh).
  + destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd KV Ha Hh). }
exact (trans_src_ok_inner B lyc Sc W memc ly2 S2 W2 mem2 q n Hbl Hfr Hfa Elo Ehi Hrd2 (or_intror (conj HL Hrd))).
Qed.

(* bar_run over a step that writes bytes of frame[lo, hi) and bytes of a window [wlo, whi) below sp1 inside the
   statement's (a runtime entry's ESTACK bytes): bc_keep_frame with that window added to the changed bytes. *)
Lemma bc_keep_frame_w : forall c pos S2 mem2 md2 mem3 md3 (lo hi wlo whi : Z),
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bar_run B MT c pos S2 mem2 md2 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c)
    (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c) ((BAR_CID, pos) :: cx_own c) (cx_lyc c) S2 (cx_W c) mem3 md3
    (cx_k c + 0) ->
  bar_F c pos <= lo -> hi <= bar_F c pos + 2040 ->
  bar_SP c - BAR_STK <= wlo -> whi <= bar_sp1 c ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (wlo <= a < whi) ->
     aview segs (w_H (cx_W c)) mem3 a = aview segs (w_H (cx_W c)) mem2 a) ->
  (forall a, apresent (w_H (cx_W c)) mem2 a -> apresent (w_H (cx_W c)) mem3 a) ->
  bar_run B MT c pos S2 mem3 md3.
Proof using All.
intros c pos S2 mem2 md2 mem3 md3 lo hi wlo whi HRT HOK HRUN HJ3 Hlo2 Hhi2 Hwlo Hwhi KD GR.
pose proof HRT as (_ & _ & _ & _ & _ & _ & LAWS & MTL & _ & _ & FFL & HGX & _).
destruct (bar_ok_sp B MT c HOK) as (HARc & HSPr & HCE & _ & _ & _ & _ & _ & _ & HS1r & Hwin0 & _).
destruct HRUN as (HCUR & Heab & Hmo0 & HGK & HSH0 & HSH2 & HPR).
destruct HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw & HSL24).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin : In (BAR_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_frames _ _ LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin) as (_ & HFapp & _ & _).
destruct (frames_bounds segs B LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin) as (HF0 & HFc & _).
pose proof (fun a Ha => frm_img segs B LAWS _ _ _ _ _ BAR_CID pos a HAR2 Hin Ha) as HFimg.
rewrite bar_fbytes in HFapp, HFc, HFimg. unfold BAR_FBYTES in HFapp, HFc, HFimg.
set (F := frame_addr (cx_lyc c) BAR_CID pos) in *.
assert (EF : bar_F c pos = F) by reflexivity.
rewrite EF in Hlo2, Hhi2, HSH0, HSH2, HFLw, HSL24.
assert (Hbl : forall bm, In bm (ablocks B (cx_lyc c) (cx_Sc c)) -> In bm (ablocks B (cx_lyc c) S2))
  by (intros bm Hb; rewrite Heab; exact Hb).
assert (EBS2 : BAR_STK = 208 + RECV_STK) by exact bar_stk_eq.
assert (ERS2 : 0 <= RECV_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSEP : hi + 8 <= bar_SP c - BAR_STK) by lia.
assert (HZ : forall a, (lo <= a < hi) \/ (wlo <= a < whi) ->
  (bar_SP c - BAR_STK <= a < bar_SP c) \/ dkg_nf BAR_CID F (flag_addr (cx_lyc c) BAR_CID pos) a \/
  W_journalG.inG TG.G_HARNESS_B a).
{ intros a [Ha | Ha]; [right; left; unfold dkg_nf; left; rewrite bar_fbytes; unfold BAR_FBYTES; lia | left; lia]. }
assert (HNS : forall i, 0 <= i < 256 -> ~ (lo <= SHADOW_OFF + F / 8 + i < hi)).
{ intros i Hi Hx.
  pose proof (bc_frame_not_shadow F (SHADOW_OFF + F / 8 + i - F) HFapp ltac:(lia)) as HN.
  apply HN. lia. }
assert (HNW : forall i, 0 <= i < 256 -> ~ (wlo <= SHADOW_OFF + F / 8 + i < whi)).
{ intros i Hi Hx. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  assert (F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF in Hx. lia. }
split.
{ split; [exact HJ3|].
  split; [exact He|]. split; [exact Hfrs|]. split; [exact Hperm|]. split; [exact HlyF|]. split; [exact Hmo|].
  split.
  { apply (dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B (cx_lyc c) (cx_Sc c) (cx_lyc c) S2
      (cx_W c) (cx_memc c) (cx_mdc c) (cx_W c) mem2 md2 mem2 mem3 (bar_SP c - BAR_STK) (bar_SP c) BAR_CID pos
      F (flag_addr (cx_lyc c) BAR_CID pos) (recv_wr (bar_fr c)) (fun a => (lo <= a < hi) \/ (wlo <= a < whi))
      HGX HARc HAR2 Hfrs Hbl eq_refl eq_refl eq_refl FFL HCE ltac:(lia));
    [exact HZ | exact HK | | exact GR].
    intros a Ha Hn. apply KD; [exact Ha | intros Hx; apply Hn; left; exact Hx | intros Hx; apply Hn; right; exact Hx]. }
  split.
  { rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
    assert (Hob : 8 <= fst o <= 104).
    { unfold BAR_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia |]). destruct Ho. }
    apply rdword_ext. intros k Hk. apply KD; lia. }
  split.
  { rewrite <- HFLw. unfold BAR_FBYTES. apply rdword_ext. intros k Hk. apply KD; lia. }
  change (bar_F c pos) with F. rewrite <- HSL24. apply rdword_ext. intros k Hk. apply KD; lia. }
split; [exact Heab|]. split; [exact Hmo0|].
split.
{ intros a Hg. rewrite <- (HGK a Hg).
  destruct (HGX a Hg) as [HiG _].
  pose proof (transportb_segs_low a HiG) as Hl. unfold kLowMemEnd in Hl.
  apply KD; [lia | intros Hx; exact (HFimg a ltac:(lia) HiG) | lia]. }
split; [intros i Hi; rewrite KD; [exact (HSH0 i Hi) | unfold SHADOW_OFF in *; lia | apply HNS; lia | apply HNW; lia]|].
split; [rewrite KD; [exact HSH2 | unfold SHADOW_OFF in *; lia | apply HNS; lia | apply HNW; lia]|].
intros a Ha Hp. exact (GR a (HPR a Ha Hp)).
Qed.

(* The body's bytes at a state of bar_run, when it is not empty: placed, kept since the call, outside the
   statement's window, and apart from the own frame (trans_src_ok_disj_own). *)
Lemma bc_body_at : forall c pos S2 mem2 md2,
  bar_rt B MT (cx_CTX c) -> bar_ok B MT c -> bar_run B MT c pos S2 mem2 md2 ->
  (0 < length (cx_body c))%nat ->
  trans_src_ok B (cx_lyc c) S2 (cx_W c) mem2 (cx_bodyp c) (bar_len (cx_body c)) /\
  (forall a, cx_bodyp c <= a < cx_bodyp c + bar_len (cx_body c) ->
     aview segs (w_H (cx_W c)) mem2 a = aview segs (w_H (cx_W c)) (cx_memc c) a) /\
  decode_off_win (cx_regs c) BAR_STK (cx_bodyp c) (bar_len (cx_body c)) /\
  (cx_bodyp c + bar_len (cx_body c) <= bar_F c pos \/ bar_F c pos + 2048 <= cx_bodyp c).
Proof using All.
intros c pos S2 mem2 md2 HRT HOK HRUN Hl.
pose proof HRT as (_ & _ & _ & _ & HRU & HRE & LAWS & _).
destruct (bar_ok_sp B MT c HOK) as (HARc & _).
pose proof HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & Hbody & _).
destruct (Hbody Hl) as [Hsrc Hoff].
destruct HRUN as (HCUR & Heab & _ & HGK & _).
destruct HCUR as (HJ2 & _ & Hfrs & Hperm & _ & _ & HK & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hlen : 0 < bar_len (cx_body c)) by (unfold bar_len; lia).
destruct (bc_src_kept HRU HRE LAWS (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) (cx_lyc c) S2 (cx_W c)
  mem2 md2 (bar_SP c - BAR_STK) (bar_SP c) (recv_wr (bar_fr c)) (cx_bodyp c) (bar_len (cx_body c)) HARc HAR2
  ltac:(intros bm Hb; rewrite Heab; exact Hb) ltac:(intros f Hf; rewrite Hfrs; right; exact Hf)
  (fun _ _ => eq_refl) eq_refl eq_refl HK HGK (fun a Ha => bc_wr_hull _ a Ha) Hoff Hsrc Hlen) as [Hs2 KV].
refine (conj Hs2 (conj KV (conj Hoff _))).
pose proof (trans_src_ok_disj_own B LAWS (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) (cx_lyc c) S2 (cx_W c)
  mem2 md2 BAR_CID pos (cx_bodyp c) (bar_len (cx_body c)) HARc HAR2 Hfrs Hperm (fun _ _ => eq_refl) Hsrc Hlen) as HD.
rewrite bar_fbytes in HD. unfold BAR_FBYTES in HD. exact HD.
Qed.

(* ---- small facts the walk reads ---- *)

(* The value of a register atom and of its right shift by a constant. *)
Lemma bc_U_off : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n 0) = v.
Proof.
intros E n v Hn Hv. rewrite U_SOff, Hn, (unsigned_lit_small v Hv), Z.add_0_r. apply zcanon_id. unfold M64. lia.
Qed.
Lemma bc_U_srl : forall E n k v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= k < 64 ->
  U E (SAlu ALU_SRL (SOff n 0) (SLit k)) = v / 2 ^ k.
Proof.
intros E n k v Hn Hv Hk.
pose proof (bc_U_off E n v Hn Hv) as Un.
rewrite U_SAlu. cbn [zalu_raw]. rewrite Un, U_SLit, (zcanon_id k) by (unfold M64; lia).
replace (Z.land k 63) with k
  by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; rewrite Z.mod_small; [reflexivity | cbn; lia]).
rewrite Z.shiftr_div_pow2 by lia.
assert (H2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia|].
apply (Z.le_lt_trans _ v); [apply Z.div_le_upper_bound; nia | lia].
Qed.
Lemma bc_U_lit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. apply zcanon_id. unfold M64. exact Hz. Qed.

(* A one-byte chunk's value, as the model's byte. *)
Lemma bc_vm1 : forall (m : word -> option byte) a a' (u y : Z),
  val_mem segs m a (N.to_nat 1) (u mod 2 ^ (8 * Z.of_N 1)) -> a' = a -> u = y ->
  val_mem segs m a' 1 (bv_unsigned (DSpec.b8 y)).
Proof.
intros m a a' u y V -> ->. unfold DSpec.b8. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. exact V.
Qed.

(* Every value of TW.zs is a byte. *)
Lemma bc_zs_range : forall (l : list byte) j, 0 <= nth j (TW.zs l) 0 < 256.
Proof.
intros l j. unfold TW.zs. destruct (nth_in_or_default j (map bv_unsigned l) 0) as [Hin | Ej]; [|rewrite Ej; lia].
apply in_map_iff in Hin. destruct Hin as (b & Hb & _). rewrite <- Hb.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

(* garr8 at another base, from the bytes there. *)
Lemma bc_garr8_shift : forall (m m' : word -> option byte) p q (l : list Z),
  garr8 segs m p l ->
  (forall j, 0 <= j < Z.of_nat (length l) -> mbyte segs m' (q + j) = mbyte segs m (p + j)) ->
  garr8 segs m' q l.
Proof.
intros m m' p q l Hg Hm j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. pose proof (Hv 0%nat Hk) as H0.
cbn [Z.of_nat] in H0 |- *. rewrite Z.add_0_r in H0 |- *.
rewrite (Hm (Z.of_nat j) ltac:(lia)). exact H0.
Qed.

(* A byte whose view is 0 is the zero byte. *)
Lemma bc_mbyte0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview segs H m a = Some 0 -> mbyte segs (mrestrict H m) a = Some (Z_to_bv 8 0).
Proof.
intros H m a Hz. unfold aview in Hz.
destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; cbn in Hz; [|discriminate].
injection Hz as Hz. f_equal. apply bv_eq. rewrite Hz. reflexivity.
Qed.

(* YCbq.v mbyte_of_aview at two addresses. *)
Lemma bc_mbyte_of_aview2 : forall H H' (m m' : word -> option byte) a a',
  aview segs H' m' a' = aview segs H m a -> mbyte segs (mrestrict H' m') a' = mbyte segs (mrestrict H m) a.
Proof.
intros H H' m m' a a' E. unfold aview in E.
destruct (mbyte segs (mrestrict H' m') a') as [b'|], (mbyte segs (mrestrict H m) a) as [b|]; cbn in E;
  try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* The frame's n bytes from its four parts: the mid piece's sixteen, the fourteen header bytes, the body, and the
   zeros past it. *)
Lemma bc_frame_garr8 : forall (H : word -> bool) (m : word -> option byte) (p : Z) (dst src : list byte)
    (send ack retry cmd : Z) (body : list byte),
  length dst = 6%nat -> length src = 6%nat ->
  garr8 segs (mrestrict H m) p (TW.zs (bar_pre16 dst src body)) ->
  garr8 segs (mrestrict H m) (p + 16) (TW.zs (bc_hdr14 send ack retry cmd body)) ->
  garr8 segs (mrestrict H m) (p + 30) (TW.zs body) ->
  (forall i, 30 + bar_len body <= i < bar_nn body -> aview segs H m (p + i) = Some 0) ->
  garr8 segs (mrestrict H m) p (TW.zs (bar_frame dst src send ack retry cmd body)).
Proof.
intros H m p dst src send ack retry cmd body Hd Hs G1 G2 G3 GZ.
rewrite (bc_frame_split dst src send ack retry cmd body Hd Hs).
unfold TW.zs in *. rewrite !map_app.
apply (proj2 (garr8_app segs _ _ _ _)). split; [exact G1|].
rewrite length_map, (bar_pre16_len dst src body Hd Hs).
apply (proj2 (garr8_app segs _ _ _ _)). split; [replace (p + Z.of_nat 16) with (p + 16) by lia; exact G2|].
rewrite length_map, bc_hdr14_len.
apply (proj2 (garr8_app segs _ _ _ _)). split; [replace (p + Z.of_nat 16 + Z.of_nat 14) with (p + 30) by lia; exact G3|].
rewrite length_map, map_repeat.
change (bv_unsigned (DSpec.b8 0)) with 0.
apply garr8_zeros. intros a Ha.
apply bc_mbyte0. replace a with (p + (a - p)) by lia. apply GZ.
assert (Hn : Z.of_nat (30 - length body) = Z.max 0 (30 - Z.of_nat (length body))) by lia.
unfold bar_len, bar_nn, bar_s8. lia.
Qed.

(* `beq` on a register atom holding v against 0. *)
Lemma bc_br_eq : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v H R. cbn [branch_taken sv_denot]. rewrite H, (unsigned_lit_small v R), Z.add_0_r.
unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0 (2 ^ 64)) by lia. rewrite (Z.mod_small v (2 ^ 64)) by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 8. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Lemma bar_call_holds : @bar_call_stmt fx rc B MT.
Proof.
unfold bar_call_stmt. intros c REL. unfold bar_call_at.
intros HRT HOK pos S2 mem2 md2 regs2 HRUN HRG HSL H11 H21 HG16 HZ16.
pose proof HRT as (HPCS & HCELLS & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGN
  & _ & _ & _ & _ & HCPY0 & HRCV0 & _).
pose proof (bar_ok_sp B MT c HOK)
  as (HARc & HSPr & HCE & Hwin0 & Hsp16 & Hsp0a & Hlo & Hhi & HS1al & HS1r & HWS & HS1al16).
pose proof (bar_ok_len B MT c HOK) as [HLD HLS].
pose proof (bar_ok_frame_len B MT c HOK) as HFLEN.
pose proof HRUN as (HCUR & Heab & Hmo0 & HGK & HSH0 & HSH2 & HPR).
pose proof HCUR as (HJ & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw & HSL24).
destruct HRG as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R25 & R26 & R27) & R19 & R20 & R24).
destruct HSL as (S32 & S40 & S48 & S56).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (Hin : In (BAR_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin) as (_ & HFapp & HFpres & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ BAR_CID pos HAR2 Hin) as (HF64 & _ & _).
rewrite bar_fbytes in HFapp, HFpres, HFc, HFsh. change (BAR_FBYTES / 8) with 256 in HFsh.
unfold BAR_FBYTES in HFapp, HFpres, HFc, HFsh.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (EBS : BAR_STK = 208 + RECV_STK) by exact bar_stk_eq.
assert (ERS : RECV_STK = 16512) by reflexivity.
set (F := frame_addr (cx_lyc c) BAR_CID pos) in *.
assert (EF : bar_F c pos = F) by reflexivity.
rewrite EF in R18, R25, R26, R27, HG16, HZ16, HSH0, HSH2, HFLw, HSL24.
set (sp1 := bar_sp1 c) in *.
set (SP := bar_SP c) in *.
(* the own frame lies below the statement's window *)
assert (HFlo : F + 2048 <= SP - BAR_STK) by (eapply Z.le_trans; [exact HFc | exact HCE]).
set (sndw := bv_unsigned (YK11.getr (cx_regs c) 12)) in *.
pose proof HOK as (HJc & _ & Hra4 & _ & _ & _ & _ & H12 & H13 & _ & _ & _ & _ & Hch & Hctx & _ & _ & _ & Hsnd & Hack
  & Hrty & Hcmd & _ & _ & _ & _ & _ & _ & _ & _ & Hgb & _ & Htw & Hgf & Hm35 & Hrom & I1 & I2 & I3 & I4 & I5 & I6 & I7
  & Hdn & Hc5 & Hc1 & Hc4 & Hc0 & Hc2 & Hev & Hlive & Hmok & Hcost).
pose proof (bar_body_bound (cx_Bw c) (cx_dst c) (cx_src c) (cx_send c) (cx_ack c) (cx_retry c) (cx_cmd c)
  (cx_body c) Hm35) as Hbb.
destruct bar_max_body as [EMB EMF]. rewrite EMB in Hbb.
assert (HN : 60 <= bar_N c <= 1514) by (unfold bar_N, bar_nn, bar_s8, bar_len in *; lia).
assert (Hlen0 : 0 <= bar_len (cx_body c)) by (unfold bar_len; lia).
assert (HT0 : 0 <= cx_T c).
{ pose proof (mo_malloc_nonneg MT MTL (Z.max 1 (bar_N c)) ltac:(lia)). pose proof (mo_free_nonneg MT MTL).
  unfold recv_cost in Hcost. lia. }
(* the entry's layout: its machine stack below 2 ^ 47, and the frames where the call's layout puts them *)
pose proof HJc as (_ & _ & (memSc & HJic & _) & _). rewrite !Z.add_0_r in HJic.
pose proof HJic as (_ & Hlylec & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hlylec as (_ & _ & _ & _ & _ & ELFc & _ & _ & ETOP & _).
pose proof Hstk as (_ & _ & _ & _ & _ & H47s & _ & _ & Htop1).
clear HJic memSc.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* ---- the join +0x360: run 3 and the call of receive, written once ---- *)
assert (TAIL : forall (mJ : word -> option byte) (mdJ : Model) (regsJ : bvmap 5 word),
  bar_run B MT c pos S2 mJ mdJ ->
  YK11.getr regsJ 2 = w64 sp1 -> YK11.getr regsJ 3 = w64 (as_gp B) -> YK11.getr regsJ 4 = w64 (as_tp B) ->
  YK11.getr regsJ 8 = w64 SP -> YK11.getr regsJ 9 = w64 sp1 -> YK11.getr regsJ 18 = w64 F ->
  YK11.getr regsJ 21 = w64 (bar_s8 (cx_body c)) -> YK11.getr regsJ 23 = w64 SHADOW_OFF ->
  YK11.getr regsJ 25 = w64 (F + 32) -> YK11.getr regsJ 26 = w64 (SHADOW_OFF + F / 8) ->
  YK11.getr regsJ 27 = w64 (SHADOW_OFF + F / 8 + 4) ->
  garr8 segs (mrestrict (w_H (cx_W c)) mJ) (F + 32) (TW.zs (bar_fr c)) ->
  SRr segs (cx_W c) (mkCfg (@YK11.mkst fx regsJ (Z_to_bv 64 (BASE + BC_JOIN)) mJ (YK11.seg_rom segs)) mdJ)
    (bar_post B MT c)).
{ intros mJ mdJ regsJ HRJ J2 J3 J4 J8 J9 J18 J21 J23 J25 J26 J27 HGF.
  pose proof HRJ as (HCURJ & _). pose proof HCURJ as (HJJ & _).
  pose proof (bc_entry0 (cx_W c) regsJ mJ ss_bc3 BC_JOIN eq_refl) as HS3.
  set (E3 := bc_E0 regsJ) in HS3.
  assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3, bc_E0; apply Eimg_env).
  assert (EW3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regsJ r)
    by (intros n r Hn; unfold E3, bc_E0; apply can_ew_Eimg_Ereg_nat; exact Hn).
  assert (SHOK3 : sh_ok segs (SOff 23 0) (@nil shent) E3 (mrestrict (w_H (cx_W c)) mJ)) by constructor.
  paj_run_tok RUN HS3 HJJ SHOK3 BC_B0.
  { bc_awr_rs. apply awr_ok_x_nil. }
  (* the registers at the call *)
  bc_reg HS3 (1%bv : bv 5) (Z_to_bv 64 (BASE + 19052)) C1 ltac:(apply codeptr_val; exact HEI3).
  bc_kreg HS3 EW3 (2%bv : bv 5) 2%nat J2 C2. bc_kreg HS3 EW3 (3%bv : bv 5) 3%nat J3 C3.
  bc_kreg HS3 EW3 (4%bv : bv 5) 4%nat J4 C4. bc_kreg HS3 EW3 (8%bv : bv 5) 8%nat J8 C8.
  bc_kreg HS3 EW3 (9%bv : bv 5) 9%nat J9 C9. bc_kreg HS3 EW3 (18%bv : bv 5) 18%nat J18 C18.
  bc_kreg HS3 EW3 (23%bv : bv 5) 23%nat J23 C23. bc_kreg HS3 EW3 (25%bv : bv 5) 25%nat J25 C25.
  bc_kreg HS3 EW3 (26%bv : bv 5) 26%nat J26 C26. bc_kreg HS3 EW3 (27%bv : bv 5) 27%nat J27 C27.
  bc_reg HS3 (10%bv : bv 5) (w64 (F + 32)) C10
    ltac:(cbn [sv_denot]; rewrite (EW3 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact J25).
  bc_reg HS3 (11%bv : bv 5) (w64 (bar_s8 (cx_body c) + 30)) C11
    ltac:(cbn [sv_denot]; rewrite (EW3 21%nat 21%bv eq_refl), J21; unfold w64;
          rewrite unsigned_lit_small by (unfold bar_s8, bar_len in *; lia); reflexivity).
  bc_reg HS3 (12%bv : bv 5) (w64 0) C12 ltac:(reflexivity).
  bc_reg HS3 (13%bv : bv 5) (w64 0) C13 ltac:(reflexivity).
  pmkst HS3.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    set (regsC := rg) in *; set (memC := mm) in *; set (mdC := mdx) in * end.
  (* run 3 wrote nothing *)
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
    aview segs (w_H (cx_W c)) memC a = aview segs (w_H (cx_W c)) mJ a) by (bc_frame_kept HFr (fun _ : Z => False) EF).
  assert (GC : forall a, apresent (w_H (cx_W c)) mJ a -> apresent (w_H (cx_W c)) memC a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (bc_keep_frame c pos S2 mJ mdJ memC mdC (F + 48) (F + 48) HRT HOK HRJ HJJ ltac:(rewrite EF; lia)
    ltac:(rewrite EF; lia) ltac:(intros a Ha _; exact (KC a Ha (fun x => x))) GC) as HRUNC.
  pose proof HRUNC as (HCURC & HeabC & Hmo0C & HGKC & _ & _ & _).
  pose proof HCURC as (HJC & _ & HfrsC & HpermC & _ & _ & HKC & HsavedC & HFLwC & HSLC).
  change (bar_F c pos) with F in HFLwC, HSLC.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJC) as HARC.
  assert (USPC : spZ regsC = sp1) by (unfold spZ; rewrite C2; unfold w64; apply unsigned_lit_small; lia).
  assert (S0C : s0Z regsC = SP) by (unfold s0Z; rewrite C8; unfold w64; apply unsigned_lit_small; lia).
  assert (EBR : BASE + 19052 = BAR_RA_RECV) by (vm_compute; reflexivity).
  assert (RAC : raZ regsC = BAR_RA_RECV)
    by (unfold raZ; rewrite C1, EBR; apply unsigned_lit_small; rewrite bar_ra_recv_at; lia).
  (* the frame-pointer chain at the call: the record at the entry sp (s0), or none near ly_top *)
  assert (E51 : Z_to_bv 5 1 = (1%bv : bv 5)) by (apply bv_eq; reflexivity).
  assert (E58 : Z_to_bv 5 8 = (8%bv : bv 5)) by (apply bv_eq; reflexivity).
  assert (SV8 : rdword (aview segs (w_H (cx_W c)) memC) (SP - 8) = Some (raZ (cx_regs c))).
  { pose proof (proj1 (Forall_forall _ _) HsavedC (8, 1) ltac:(unfold BAR_SAVED; cbn [In]; left; reflexivity)) as X.
    cbv beta in X. cbn [fst snd] in X. rewrite E51 in X. exact X. }
  assert (SV16 : rdword (aview segs (w_H (cx_W c)) memC) (SP - 16) = Some (s0Z (cx_regs c))).
  { pose proof (proj1 (Forall_forall _ _) HsavedC (16, 8) ltac:(unfold BAR_SAVED; cbn [In]; right; left; reflexivity))
      as X.
    cbv beta in X. cbn [fst snd] in X. rewrite E58 in X. exact X. }
  assert (HCH : exists chC,
    @achain rc (cx_lyc c) (aview segs (w_H (cx_W c)) memC) (spZ regsC) (s0Z regsC) chC /\
    In (raZ regsC :: spine chC) (bar_recv_ctx (cx_CTX c))).
  { rewrite USPC, S0C, RAC.
    destruct (Z_lt_ge_dec SP (ly_top (cx_lyc c) - 16)) as [Htop | Htop].
    - exists ((SP, raZ (cx_regs c), s0Z (cx_regs c)) :: cx_ch c). split.
      + apply (achain_push (cx_lyc c) (aview segs (w_H (cx_W c)) (cx_memc c)) (aview segs (w_H (cx_W c)) memC) SP
          (s0Z (cx_regs c)) (raZ (cx_regs c)) (cx_ch c) sp1 Hch).
        * lia.
        * intros a Ha. pose proof HKC as (L1 & _). apply L1; lia.
        * exact SV8.
        * exact SV16.
        * exact Hra4.
        * lia.
        * pose proof (Z.div_mod SP 16 ltac:(lia)) as D. rewrite Hsp16, Z.add_0_r in D. rewrite D.
          replace (16 * (SP / 16)) with ((2 * (SP / 16)) * 8) by ring. apply Z.mod_mul. lia.
        * exact Htop.
        * lia.
      + right. apply in_map_iff. exists (raZ (cx_regs c) :: spine (cx_ch c)). split; [reflexivity | exact Hctx].
    - exists []. split.
      + left. split; [right; left; lia | reflexivity].
      + left. reflexivity. }
  destruct HCH as (chC & HCHa & HCHb).
  (* receive's other premises at the call state *)
  pose proof (bc_buf_at c pos S2 memC mdC regsC RECV_STK (bar_N c) HRT HOK HRUNC USPC ltac:(lia) ltac:(lia)
    ltac:(lia)) as (_ & _ & HSRCC & _ & HOFFC & _).
  change (bar_F c pos) with F in HSRCC, HOFFC.
  assert (PTW : tw_at TMAP_B (aview segs (w_H (cx_W c)) memC) (cx_Bw c)).
  { apply (tw_kept_GB (aview segs (w_H (cx_W c)) (cx_memc c))); [exact Htw|].
    intros b n i Hbn Hi. apply HGKC. unfold inG. apply Exists_exists. exists (b, n).
    split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]. }
  assert (PROM : trans_rom_view_rd (cx_W c) memC).
  { intros a0 Ha0. rewrite <- (Hrom a0 Ha0). pose proof HKC as (_ & _ & K3 & _).
    destruct (trans_ro_rd_scoped B HRU HRE a0 Ha0) as [Ho Hx].
    apply (K3 a0 (trans_ro_img a0 Ha0)); [|exact Ho | exact Hx].
    intro Ga. pose proof (inG_G_HARNESS_hull a0 Ga) as Gh. pose proof (trans_ro_rd_bounds a0 Ha0) as Rb.
    unfold TG.G_HARNESS_B_LO in Gh. lia. }
  assert (PMOD : forall a0, recv_addr_ok a0 -> TOP.receive_m timg_B (cx_Bw c) a0 (bar_fr c) 0 0 <> None).
  { intros a0 Ha0 Hn. apply (Hm35 a0 Ha0). rewrite bar_model.
    rewrite (proj2 (Z.ltb_ge TC.SPEC_MAX_BODY (Z.of_nat (length (cx_body c))))) by (rewrite EMB; exact Hbb).
    exact Hn. }
  assert (HGFC : garr8 segs (mrestrict (w_H (cx_W c)) memC) (F + 32) (TW.zs (bar_fr c))).
  { apply (garr8_frame segs _ _ _ _ HGF). intros a Ha. apply mbyte_of_aview. apply KC; [|tauto].
    unfold TW.zs in Ha. rewrite length_map, HFLEN in Ha. lia. }
  assert (PC5 : count_cid POLL_CID (frames S2) + 1 < fs_frames POLL_CID).
  { rewrite Hfrs.
    assert (EC : count_cid POLL_CID ((BAR_CID, pos) :: frames (cx_Sc c)) = 1 + count_cid BAR_CID (frames (cx_Sc c)))
      by reflexivity.
    rewrite EC. change (fs_frames POLL_CID) with (fs_frames BAR_CID). lia. }
  assert (PC1 : count_cid SRX_CID (frames S2) + 1 < fs_frames SRX_CID).
  { rewrite Hfrs.
    assert (EC : count_cid SRX_CID ((BAR_CID, pos) :: frames (cx_Sc c)) = count_cid SRX_CID (frames (cx_Sc c)))
      by reflexivity.
    rewrite EC. exact Hc1. }
  assert (PC4 : count_cid ONANN_CID (frames S2) < fs_frames ONANN_CID).
  { rewrite Hfrs.
    assert (EC : count_cid ONANN_CID ((BAR_CID, pos) :: frames (cx_Sc c)) = count_cid ONANN_CID (frames (cx_Sc c)))
      by reflexivity.
    rewrite EC. exact Hc4. }
  assert (PC0 : count_cid SENDDATA_CID (frames S2) < fs_frames SENDDATA_CID).
  { rewrite Hfrs.
    assert (EC : count_cid SENDDATA_CID ((BAR_CID, pos) :: frames (cx_Sc c)) =
      count_cid SENDDATA_CID (frames (cx_Sc c))) by reflexivity.
    rewrite EC. exact Hc0. }
  assert (PC2 : count_cid ONDATA_CID (frames S2) + 2 < fs_frames ONDATA_CID).
  { rewrite Hfrs.
    assert (EC : count_cid ONDATA_CID ((BAR_CID, pos) :: frames (cx_Sc c)) = count_cid ONDATA_CID (frames (cx_Sc c)))
      by reflexivity.
    rewrite EC. exact Hc2. }
  assert (PLIVE : blocks_bytes S2 + RECV_LIVE <= LIVE_MAX).
  { rewrite (blocks_bytes_bsum B (cx_lyc c) S2), Heab, <- (blocks_bytes_bsum B (cx_lyc c) (cx_Sc c)). exact Hlive. }
  assert (PMOK : mo_ok MT S2 (cx_T c))
    by exact (mok_station MT (cx_Sc c) S2 (cx_T c) 0 (cx_T c) MTL Hmok Hmo0 HT0 ltac:(lia)).
  (* +0x370: receive *)
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB_receive)) mm rom) mdx) Q) end.
  eapply SRr_bind.
  { exact (HRCV0 fx (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
      ((BAR_CID, pos) :: cx_own c) (cx_lyc c) S2 (cx_W c) memC mdC (cx_k c + 0) regsC
      (F + 32) 0 0 (cx_T c) (bar_fr c) (cx_Bw c) chC
      HJC
      ltac:(rewrite C1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
      ltac:(rewrite RAC, bar_ra_recv_at; lia)
      C3 C4 C10 ltac:(rewrite HFLEN; exact C11) C12
      ltac:(rewrite C13; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
      HCHa HCHb
      ltac:(rewrite USPC; exact HS1al16) ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
      ltac:(lia) ltac:(lia) ltac:(rewrite HFLEN; lia)
      HGFC
      ltac:(intros _; rewrite HFLEN; exact (conj HSRCC HOFFC))
      PTW Hgf PMOD PROM I1 I2 I3 I4 I5 I6 I7 Hdn PC5 PC1 PC4 PC0 PC2
      ltac:(rewrite Z.add_0_r; exact Hev) PLIVE PMOK ltac:(rewrite HFLEN; exact Hcost)). }
  cbv beta. intros W3 c3 _ HPOST.
  unfold transport_recv_post, transport_cg_post in HPOST. cbv beta in HPOST.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
    (a & Bw' & Haok & Hrm & Htw3 & Hgf3)).
  rewrite C1. change (Z_to_bv 64 (BASE + 19052)) with (Z_to_bv 64 (BASE + BAR_REL)).
  apply (REL HRT HOK pos ly3 S3 W3 mem3 md3 regs3 e a Bw').
  - (* bar_cur at receive's return *)
    destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low (cx_lyc c) (cx_Sc c) (cx_lyc c) S2 (cx_W c) memC mdC
      BAR_CID pos F (flag_addr (cx_lyc c) BAR_CID pos) HARC HfrsC
      ltac:(intros bm Hb; rewrite HeabC; exact Hb) eq_refl eq_refl eq_refl FFL) as (N1 & N2 & N3 & N4).
    pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
    pose proof HJi3 as (_ & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
    clear HJi3 memS3.
    unfold bar_cur. change (bar_F c pos) with F.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
    + replace (cx_k c + e) with (cx_k c + 0 + e) by lia. exact HJ3.
    + exact He3.
    + rewrite Hfr3. exact Hfrs.
    + rewrite <- Heab. exact Hperm3.
    + rewrite ELF3, ELFc. reflexivity.
    + rewrite HFLEN in Hmo3. replace (recv_cost MT (bar_N c)) with (0 + recv_cost MT (bar_N c)) by lia.
      exact (mo_le_trans MT MTL _ _ _ _ _ Hmo0 Hmo3).
    + apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B (cx_lyc c) (cx_Sc c) (cx_lyc c) S2 (cx_W c) (cx_memc c)
        (cx_W c) memC W3 mem3 (SP - BAR_STK) SP (spZ regsC - RECV_STK) (spZ regsC) (recv_wr (bar_fr c))
        (recv_wr (bar_fr c)) (dkg_nf BAR_CID F (flag_addr (cx_lyc c) BAR_CID pos)));
        [lia | lia | intros; reflexivity | intros f Hf; rewrite HfrsC; right; exact Hf
        | intros bm Hb; rewrite HeabC; exact Hb | exact N1 | exact N3 | exact HKC | exact HK3
        | rewrite USPC; lia | rewrite USPC; lia | intros a0 Ha0; left; exact Ha0].
    + rewrite Forall_forall in HsavedC |- *. intros o Ho. rewrite <- (HsavedC o Ho).
      assert (Hob : 8 <= fst o <= 104).
      { unfold BAR_SAVED in Ho. cbn [In] in Ho.
        repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia |]). destruct Ho. }
      pose proof HK3 as (L1 & _).
      apply rdword_ext. intros k0 Hk0. apply L1; [lia | rewrite USPC; lia].
    + rewrite <- HFLwC. apply rdword_ext. intros k0 Hk0. pose proof HK3 as (_ & _ & _ & L4 & _).
      apply (L4 BAR_CID pos (F + BAR_FBYTES - 8 + k0) Hin).
      * left. unfold in_zr, frame_rng. cbn [fst snd]. change (frame_addr (cx_lyc c) BAR_CID pos) with F.
        rewrite bar_fbytes. unfold BAR_FBYTES. lia.
      * intros Hw. pose proof (bc_wr_hull _ _ Hw) as Hh.
        apply (N2 (F + BAR_FBYTES - 8 + k0)); [unfold dkg_nf; left; rewrite bar_fbytes; unfold BAR_FBYTES; lia|].
        exact (bc_hull_img _ Hh).
    + rewrite <- HSLC. apply rdword_ext. intros k0 Hk0. pose proof HK3 as (L1 & _).
      apply L1; [lia | rewrite USPC; lia].
  - (* bar_rg at receive's return *)
    unfold bar_rg.
    refine (conj (eq_trans (HP3 2 ltac:(hnf; lia)) C2) (conj (eq_trans (HP3 3 ltac:(hnf; lia)) C3)
      (conj (eq_trans (HP3 4 ltac:(hnf; lia)) C4) (conj (eq_trans (HP3 8 ltac:(hnf; lia)) C8)
      (conj (eq_trans (HP3 9 ltac:(hnf; lia)) C9) (conj (eq_trans (HP3 18 ltac:(hnf; lia)) C18)
      (conj (eq_trans (HP3 23 ltac:(hnf; lia)) C23) (conj (eq_trans (HP3 25 ltac:(hnf; lia)) C25)
      (conj (eq_trans (HP3 26 ltac:(hnf; lia)) C26) (eq_trans (HP3 27 ltac:(hnf; lia)) C27)))))))))).
  - exact Haok.
  - rewrite bar_model.
    rewrite (proj2 (Z.ltb_ge TC.SPEC_MAX_BODY (Z.of_nat (length (cx_body c))))) by (rewrite EMB; exact Hbb).
    exact Hrm.
  - exact Htw3.
  - exact Hgf3. }
(* ---- run 1: +0x270 .. the branch on len ---- *)
pose proof (bc_entry1 (cx_W c) regs2 mem2 F sp1 sndw (cx_retry c) (cx_cmd c) R9 R25 ltac:(lia) HS1al HF0 ltac:(lia)
  ltac:(unfold sndw; pose proof (bv_unsigned_in_range 64 (YK11.getr (cx_regs c) 12)) as Hrg; unfold bv_modulus in Hrg;
        change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia)
  ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFpres a ltac:(lia)))) S32 S40 S48) as HS.
set (E := bc_E regs2 sndw (cx_retry c) (cx_cmd c)) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, bc_E; apply Eimg_env).
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E, bc_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U25 : bv_unsigned (ew E 25) = F + 32)
  by (rewrite (EW 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs (SOff 23 0) (@nil shent) E (mrestrict (w_H (cx_W c)) mem2)) by constructor.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + BAR_CALL)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK BC_B0 BC_BR.
{ bc_awr_rs.
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ BAR_CID pos); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U25 in Ha.
    left. unfold in_zr. cbn [fst snd]. change (frame_addr (cx_lyc c) BAR_CID pos) with F.
    rewrite bar_fbytes. unfold BAR_FBYTES. lia.
  - apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
pose proof (st_ok_pi_region_nth E _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
(* the registers at the branch *)
bc_kreg HS EW (2%bv : bv 5) 2%nat R2 T2. bc_kreg HS EW (3%bv : bv 5) 3%nat R3 T3.
bc_kreg HS EW (4%bv : bv 5) 4%nat R4 T4. bc_kreg HS EW (8%bv : bv 5) 8%nat R8 T8.
bc_kreg HS EW (9%bv : bv 5) 9%nat R9 T9.
bc_kreg HS EW (18%bv : bv 5) 18%nat R18 T18. bc_kreg HS EW (19%bv : bv 5) 19%nat R19 T19.
bc_kreg HS EW (20%bv : bv 5) 20%nat R20 T20. bc_kreg HS EW (21%bv : bv 5) 21%nat H21 T21.
bc_kreg HS EW (23%bv : bv 5) 23%nat R23 T23. bc_kreg HS EW (25%bv : bv 5) 25%nat R25 T25.
bc_kreg HS EW (26%bv : bv 5) 26%nat R26 T26. bc_kreg HS EW (27%bv : bv 5) 27%nat R27 T27.
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + BC_BR)) mm rom) mdx) Q);
  set (r1 := rg) in *; set (mR1 := mm) in *; set (mdR1 := mdx) in * end.
(* the fourteen bytes run 1 stored *)
assert (EW11 : ew E 11 = Z_to_bv 64 (DSpec.sum_bytes (cx_body c)))
  by (rewrite (EW 11%nat 11%bv eq_refl); exact H11).
assert (EW24 : ew E 24 = Z_to_bv 64 (bv_unsigned (YK11.getr (cx_regs c) 13)))
  by (rewrite (EW 24%nat 24%bv eq_refl), R24; symmetry; apply Z_to_bv_bv_unsigned).
assert (EW32 : ew E 32 = Z_to_bv 64 sndw)
  by (unfold E, bc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (EW33 : ew E 33 = Z_to_bv 64 (cx_retry c))
  by (unfold E, bc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (EW34 : ew E 34 = Z_to_bv 64 (cx_cmd c))
  by (unfold E, bc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (Rsm : 0 <= DSpec.sum_bytes (cx_body c) < 2 ^ 64)
  by (pose proof (bc_sum_range (cx_body c) ltac:(unfold bar_len in Hbb; lia)); lia).
assert (Rsw : 0 <= sndw < 2 ^ 64)
  by (unfold sndw; pose proof (bv_unsigned_in_range 64 (YK11.getr (cx_regs c) 12)) as Hrg; unfold bv_modulus in Hrg;
      change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia).
assert (Rbw : 0 <= bv_unsigned (YK11.getr (cx_regs c) 13) < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (YK11.getr (cx_regs c) 13)) as Hrg; unfold bv_modulus in Hrg;
      change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia).
lazymatch type of RG0 with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
  assert (V : forall a od (e : sv) y, a = F + 32 + od -> In (YP09.mkChunk od (CVal 1 e)) cs -> U E e = y ->
    val_mem segs (mrestrict (w_H (cx_W c)) mR1) a 1 (bv_unsigned (DSpec.b8 y)))
  by (intros a od e y Ha Hcs Hy;
      exact (bc_vm1 _ _ _ _ _ (field_of_region_any E _ 25 (F + 32) _ 16 30 16 30 od 1%N e RG0 U25 Hcs ltac:(lia))
               Ha Hy))
end.
assert (HG14 : garr8 segs (mrestrict (w_H (cx_W c)) mR1) (F + 32 + 16)
  (TW.zs (bc_hdr14 (cx_send c) (cx_ack c) (cx_retry c) (cx_cmd c) (cx_body c)))).
{ rewrite (bc_hdr14_bytes (YK11.getr (cx_regs c) 12) (YK11.getr (cx_regs c) 13) (cx_send c) (cx_ack c)
    (cx_retry c) (cx_cmd c) (DSpec.sum_bytes (cx_body c)) (cx_body c) H12 Hsnd H13 Hack Hrty Hcmd eq_refl).
  intros j Hj. split; [|apply bc_zs_range].
  unfold TW.zs in Hj |- *. rewrite length_map in Hj. cbn [length] in Hj.
  destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]]]; [ | | | | | | | | | | | | | | lia];
    cbn [map nth];
    (lazymatch goal with |- val_mem _ _ (_ + ?z) _ _ => eapply (V _ (16 + z) _ _) end;
     [ lia | cbn [In]; repeat (first [left; reflexivity | right]) | ]);
    [ exact (bc_U_srl E 11 8 _ EW11 Rsm ltac:(lia))
    | exact (bc_U_off E 11 _ EW11 Rsm)
    | exact (bc_U_lit E 0 ltac:(lia))
    | exact (bc_U_lit E 0 ltac:(lia))
    | exact (bc_U_srl E 32 8 _ EW32 Rsw ltac:(lia))
    | exact (bc_U_off E 32 _ EW32 Rsw)
    | exact (bc_U_srl E 24 24 _ EW24 Rbw ltac:(lia))
    | exact (bc_U_srl E 24 16 _ EW24 Rbw ltac:(lia))
    | exact (bc_U_srl E 24 8 _ EW24 Rbw ltac:(lia))
    | exact (bc_U_off E 24 _ EW24 Rbw)
    | exact (bc_U_lit E 0 ltac:(lia))
    | exact (bc_U_off E 33 _ EW33 ltac:(lia))
    | exact (bc_U_off E 34 _ EW34 ltac:(lia))
    | exact (bc_U_lit E 1 ltac:(lia)) ]. }
clear V.
(* run 1 wrote frame[16 .. 30) only *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 48 <= a < F + 62) ->
  aview segs (w_H (cx_W c)) mR1 a = aview segs (w_H (cx_W c)) mem2 a)
  by (bc_frame_kept HFr1 (fun x => F + 48 <= x < F + 62) U25).
assert (GR1 : forall a, apresent (w_H (cx_W c)) mem2 a -> apresent (w_H (cx_W c)) mR1 a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG1 Ha)).
pose proof (bc_keep_frame c pos S2 mem2 md2 mR1 mdR1 (F + 48) (F + 62) HRT HOK HRUN HJ ltac:(rewrite EF; lia)
  ltac:(rewrite EF; lia) K1 GR1) as HRUN1.
assert (HG16a : garr8 segs (mrestrict (w_H (cx_W c)) mR1) (F + 32)
  (TW.zs (bar_pre16 (cx_dst c) (cx_src c) (cx_body c)))).
{ apply (garr8_frame segs _ _ _ _ HG16). intros a Ha. apply mbyte_of_aview.
  unfold TW.zs in Ha. rewrite length_map, (bar_pre16_len _ _ _ HLD HLS) in Ha. apply K1; lia. }
assert (HZ1 : forall i, 30 + bar_len (cx_body c) <= i < bar_N c ->
  aview segs (w_H (cx_W c)) mR1 (F + 32 + i) = Some 0).
{ intros i Hi. rewrite K1; [apply HZ16; lia | unfold bar_N, bar_nn, bar_s8, bar_len in *; lia | lia]. }
(* +0x344: `beqz s3`, from a state with no region and the fact on s9 *)
pose proof (bc_entryF (cx_W c) r1 mR1 F T25 HF0 ltac:(lia)) as HSB.
set (EB := bc_E0 r1) in HSB.
assert (HEIB : img_env VAL A_LIM EB) by (unfold EB, bc_E0; apply Eimg_env).
assert (EWB : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EB n = YK11.getr r1 r)
  by (intros n r Hn; unfold EB, bc_E0; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (SHOKB : sh_ok segs (SOff 23 0) (@nil shent) EB (mrestrict (w_H (cx_W c)) mR1)) by constructor.
assert (EB19 : ew EB 19 = Z_to_bv 64 (bar_len (cx_body c))) by (rewrite (EWB 19%nat 19%bv eq_refl); exact T19).
clear HS SHOK.
psrr_branch_tok RUN BR HSB SHOKB BC_B0.
- (* len = 0: to the join *)
  rewrite (bc_br_eq EB 19 _ EB19 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
  assert (Hb0 : cx_body c = []) by (apply length_zero_iff_nil; unfold bar_len in Hc; lia).
  paj_run_to_tok RUNTO HSB HJ SHOKB BC_B0 BC_JOIN.
  { bc_awr_rs. apply awr_ok_x_nil. }
  bc_kreg HSB EWB (2%bv : bv 5) 2%nat T2 P2. bc_kreg HSB EWB (3%bv : bv 5) 3%nat T3 P3.
  bc_kreg HSB EWB (4%bv : bv 5) 4%nat T4 P4. bc_kreg HSB EWB (8%bv : bv 5) 8%nat T8 P8.
  bc_kreg HSB EWB (9%bv : bv 5) 9%nat T9 P9. bc_kreg HSB EWB (18%bv : bv 5) 18%nat T18 P18.
  bc_kreg HSB EWB (21%bv : bv 5) 21%nat T21 P21. bc_kreg HSB EWB (23%bv : bv 5) 23%nat T23 P23.
  bc_kreg HSB EWB (25%bv : bv 5) 25%nat T25 P25.
  bc_kreg HSB EWB (26%bv : bv 5) 26%nat T26 P26. bc_kreg HSB EWB (27%bv : bv 5) 27%nat T27 P27.
  pmkst HSB.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + BC_JOIN)) mm rom) mdx) Q);
    set (rJ := rg) in *; set (mJ := mm) in *; set (mdJ := mdx) in * end.
  assert (KJ : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
    aview segs (w_H (cx_W c)) mJ a = aview segs (w_H (cx_W c)) mR1 a) by (bc_frame_kept HFr (fun _ : Z => False) EF).
  assert (GJ : forall a, apresent (w_H (cx_W c)) mR1 a -> apresent (w_H (cx_W c)) mJ a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (bc_keep_frame c pos S2 mR1 mdR1 mJ mdJ (F + 48) (F + 48) HRT HOK HRUN1 HJ ltac:(rewrite EF; lia)
    ltac:(rewrite EF; lia) ltac:(intros a Ha _; exact (KJ a Ha (fun x => x))) GJ) as HRUNJ.
  apply (TAIL mJ mdJ rJ HRUNJ P2 P3 P4 P8 P9 P18 P21 P23 P25 P26 P27).
  apply (bc_frame_garr8 (w_H (cx_W c)) mJ (F + 32) (cx_dst c) (cx_src c) (cx_send c) (cx_ack c) (cx_retry c)
    (cx_cmd c) (cx_body c) HLD HLS).
  + apply (garr8_frame segs _ _ _ _ HG16a). intros a Ha. apply mbyte_of_aview. apply KJ; [|tauto].
    unfold TW.zs in Ha. rewrite length_map, (bar_pre16_len _ _ _ HLD HLS) in Ha. lia.
  + apply (garr8_frame segs _ _ _ _ HG14). intros a Ha. apply mbyte_of_aview. apply KJ; [|tauto].
    unfold TW.zs in Ha. rewrite length_map, bc_hdr14_len in Ha. lia.
  + rewrite Hb0. apply garr8_nil.
  + intros i Hi. rewrite (KJ (F + 32 + i) ltac:(unfold bar_nn, bar_s8, bar_len in *; lia) (fun x => x)).
    apply HZ1. exact Hi.
- (* len <> 0: the UBSan test of frame[] + 30 and the body memcpy *)
  rewrite (bc_br_eq EB 19 _ EB19 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
  assert (Hl0 : (0 < length (cx_body c))%nat) by (unfold bar_len in Hc; lia).
  paj_run_tok RUN HSB HJ SHOKB BC_B0.
  { bc_awr_rs. apply awr_ok_x_nil. }
  bc_reg HSB (1%bv : bv 5) (Z_to_bv 64 (BASE + 19032)) Q1 ltac:(apply codeptr_val; exact HEIB).
  bc_kreg HSB EWB (2%bv : bv 5) 2%nat T2 Q2. bc_kreg HSB EWB (3%bv : bv 5) 3%nat T3 Q3.
  bc_kreg HSB EWB (4%bv : bv 5) 4%nat T4 Q4. bc_kreg HSB EWB (8%bv : bv 5) 8%nat T8 Q8.
  bc_kreg HSB EWB (9%bv : bv 5) 9%nat T9 Q9. bc_kreg HSB EWB (18%bv : bv 5) 18%nat T18 Q18.
  bc_kreg HSB EWB (21%bv : bv 5) 21%nat T21 Q21. bc_kreg HSB EWB (23%bv : bv 5) 23%nat T23 Q23.
  bc_kreg HSB EWB (25%bv : bv 5) 25%nat T25 Q25.
  bc_kreg HSB EWB (26%bv : bv 5) 26%nat T26 Q26. bc_kreg HSB EWB (27%bv : bv 5) 27%nat T27 Q27.
  bc_reg HSB (10%bv : bv 5) (w64 (F + 32 + 30)) Q10
    ltac:(cbn [sv_denot]; rewrite (EWB 25%nat 25%bv eq_refl), T25; unfold w64;
          rewrite (unsigned_lit_small (F + 32)) by lia; reflexivity).
  bc_reg HSB (11%bv : bv 5) (w64 (cx_bodyp c)) Q11
    ltac:(cbn [sv_denot]; rewrite (EWB 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact T20).
  bc_reg HSB (12%bv : bv 5) (w64 (bar_len (cx_body c))) Q12
    ltac:(cbn [sv_denot]; rewrite (EWB 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact T19).
  pmkst HSB.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q);
    set (rT := rg) in *; set (mT := mm) in *; set (mdT := mdx) in * end.
  assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
    aview segs (w_H (cx_W c)) mT a = aview segs (w_H (cx_W c)) mR1 a) by (bc_frame_kept HFr (fun _ : Z => False) EF).
  assert (GT : forall a, apresent (w_H (cx_W c)) mR1 a -> apresent (w_H (cx_W c)) mT a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (bc_keep_frame c pos S2 mR1 mdR1 mT mdT (F + 48) (F + 48) HRT HOK HRUN1 HJ ltac:(rewrite EF; lia)
    ltac:(rewrite EF; lia) ltac:(intros a Ha _; exact (KT a Ha (fun x => x))) GT) as HRUNT.
  assert (USPT : spZ rT = sp1) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
  pose proof (bc_buf_at c pos S2 mT mdT rT ESTACK (bar_N c) HRT HOK HRUNT USPT ltac:(lia) ltac:(lia) ltac:(lia))
    as (_ & HRDT & _ & HTWT & _ & _).
  change (bar_F c pos) with F in HRDT, HTWT.
  destruct (trans_rd_ok_sub (cx_W c) mT (F + 32) (bar_N c) (F + 32 + 30) (bar_len (cx_body c)) HRDT ltac:(lia)
    ltac:(unfold bar_N, bar_nn, bar_s8 in *; lia) ltac:(lia)) as (_ & Dra & Dh & Dam & _).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HART.
  destruct (bc_body_at c pos S2 mT mdT HRT HOK HRUNT Hl0) as (HsB & KVB & HoffB & HapB).
  change (bar_F c pos) with F in HapB. unfold decode_off_win in HoffB. change (spZ (cx_regs c)) with SP in HoffB.
  assert (Hlp : 0 < bar_len (cx_body c)) by (unfold bar_len; lia).
  destruct (trans_src_ok_rd B LAWS (cx_lyc c) S2 (cx_W c) mT mdT (cx_bodyp c) (bar_len (cx_body c)) HART HsB Hlp)
    as (Rv & Rra & Rh & Ram & R0 & R63).
  (* +0x35c: the body memcpy, frame[30 .. 30 + len) = body *)
  eapply SRr_bind.
  { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OCpy (transportb_sigma TB___asan_memcpy)
      (HCPY0 fx) TG.G_HARNESS_B (cx_W c) rT mT (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c)
      (cx_mem0 c) (cx_md0 c) ((BAR_CID, pos) :: cx_own c) (cx_lyc c) S2 mdT (cx_k c + 0) (F + 32 + 30)
      (cx_bodyp c) (bar_len (cx_body c)) (sp1 - cx_sp0 c) (Z_to_bv 64 (BASE + 19032)) HGX G_HARNESS_B_rw HJ Q10 Q11 Q12).
    - lia.
    - lia.
    - lia.
    - rewrite USPT. lia.
    - rewrite Zminus_mod, HS1al16, Hsp0a. reflexivity.
    - lia.
    - lia.
    - exact Q3.
    - exact Q4.
    - exact Q1.
    - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
    - intros a Ha. apply HTWT. unfold bar_N, bar_nn, bar_s8 in *. lia.
    - exact Dam.
    - exact Dra.
    - intros _. exact Dh.
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split; [exact (Rv a Ha) | rewrite USPT; lia]. }
      split; [lia|]. split; [exact Ram|]. split; [exact Rra|]. intros _. exact Rh. }
  cbv beta. intros W2 c2 _ (-> & rM & mM & mdM & -> & HJM & HPM & HA0M & Hcpy & Heff & Hgr).
  cbv iota in Hcpy.
  pose proof (bc_keep_frame_w c pos S2 mT mdT mM mdM (F + 32 + 30) (F + 32 + 30 + bar_len (cx_body c))
    (sp1 - ESTACK) sp1 HRT HOK HRUNT HJM ltac:(rewrite EF; lia) ltac:(rewrite EF; lia) ltac:(lia) ltac:(lia)
    ltac:(intros a Ha H1 H2; apply Heff; [exact Ha | exact H1 | intros Hx; apply H2; lia]) Hgr) as HRUNM.
  assert (M2 : YK11.getr rM 2 = w64 sp1) by exact (eq_trans (HPM 2 ltac:(hnf; lia)) Q2).
  assert (M3 : YK11.getr rM 3 = w64 (as_gp B)) by exact (eq_trans (HPM 3 ltac:(hnf; lia)) Q3).
  assert (M4 : YK11.getr rM 4 = w64 (as_tp B)) by exact (eq_trans (HPM 4 ltac:(hnf; lia)) Q4).
  assert (M8 : YK11.getr rM 8 = w64 SP) by exact (eq_trans (HPM 8 ltac:(hnf; lia)) Q8).
  assert (M9 : YK11.getr rM 9 = w64 sp1) by exact (eq_trans (HPM 9 ltac:(hnf; lia)) Q9).
  assert (M18 : YK11.getr rM 18 = w64 F) by exact (eq_trans (HPM 18 ltac:(hnf; lia)) Q18).
  assert (M21 : YK11.getr rM 21 = w64 (bar_s8 (cx_body c))) by exact (eq_trans (HPM 21 ltac:(hnf; lia)) Q21).
  assert (M23 : YK11.getr rM 23 = w64 SHADOW_OFF) by exact (eq_trans (HPM 23 ltac:(hnf; lia)) Q23).
  assert (M25 : YK11.getr rM 25 = w64 (F + 32)) by exact (eq_trans (HPM 25 ltac:(hnf; lia)) Q25).
  assert (M26 : YK11.getr rM 26 = w64 (SHADOW_OFF + F / 8)) by exact (eq_trans (HPM 26 ltac:(hnf; lia)) Q26).
  assert (M27 : YK11.getr rM 27 = w64 (SHADOW_OFF + F / 8 + 4)) by exact (eq_trans (HPM 27 ltac:(hnf; lia)) Q27).
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 + 30 <= a < F + 32 + 30 + bar_len (cx_body c)) ->
    ~ (sp1 - ESTACK <= a < sp1) -> aview segs (w_H (cx_W c)) mM a = aview segs (w_H (cx_W c)) mR1 a).
  { intros a Ha H1 H2. rewrite Heff; [exact (KT a Ha (fun x => x)) | exact Ha | exact H1 | intros Hx; apply H2; lia]. }
  change (Z_to_bv 64 (BASE + 19032)) with (Z_to_bv 64 (BASE + BC_JOIN)).
  apply (TAIL mM mdM rM HRUNM M2 M3 M4 M8 M9 M18 M21 M23 M25 M26 M27).
  apply (bc_frame_garr8 (w_H (cx_W c)) mM (F + 32) (cx_dst c) (cx_src c) (cx_send c) (cx_ack c) (cx_retry c)
    (cx_cmd c) (cx_body c) HLD HLS).
  + apply (garr8_frame segs _ _ _ _ HG16a). intros a Ha. apply mbyte_of_aview.
    unfold TW.zs in Ha. rewrite length_map, (bar_pre16_len _ _ _ HLD HLS) in Ha. apply KM; lia.
  + apply (garr8_frame segs _ _ _ _ HG14). intros a Ha. apply mbyte_of_aview.
    unfold TW.zs in Ha. rewrite length_map, bc_hdr14_len in Ha. apply KM; lia.
  + apply (bc_garr8_shift _ _ (cx_bodyp c) (F + 32 + 30) _ Hgb). intros j Hj.
    unfold TW.zs in Hj. rewrite length_map in Hj. apply bc_mbyte_of_aview2.
    rewrite (Hcpy j ltac:(unfold bar_len; lia)). exact (KVB (cx_bodyp c + j) ltac:(unfold bar_len; lia)).
  + intros i Hi. rewrite KM; [apply HZ1; exact Hi | unfold bar_nn, bar_s8, bar_len in *; lia | lia |].
    change (bar_N c) with (bar_nn (cx_body c)) in HN. lia.
Qed.

End s.

Theorem bar_call_piece : forall fx rc B MT, @bar_call_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@bar_call_holds fx rc B MT). Qed.
