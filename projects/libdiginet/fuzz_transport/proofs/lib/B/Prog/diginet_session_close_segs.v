(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 397 of its 445 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SendctlBCut.v, with its module paths and module names changed; 221 of its 291 lines of code are new or changed and 375 lines of the source are left out. *)
(* diginet_session_close_segs: the cuts of image B's walk of diginet_session_close (fuzz_transport.asan-ubsan 0x87648 =
   transportb_sigma TB_diginet_session_close, AF_diginet_session_close = 0x63a8 of lib/B/Prog/DgnTransportBList.v,
   316 bytes), as STATEMENTS only, the composition close_holds_of (the statement
   transport_diginet_session_close_cg_holds_stmt of lib/B/Prog/diginet_session_close_cg.v from the three piece
   Props), and the lemmas the pieces share. The walk holds the CALLER's G journal (lib/A/W_journalG.v ajournal_gx
   G_HARNESS_B 0 []) from the entry to the return; the function takes no side-stack frame. The pieces:
     head  +0x00 .. +0x88  the frame (`addi sp, sp, -32`), the four saves (ra, s0, s1, s2 at sp + 24 .. sp + 0),
                           `beqz a0` and the alignment test of s (decided: s = &g_s), s2 = the shadow base, the
                           checked loads of s + 116, s + 136 and s + 112 and the three tests of :153 (close_go):
                           close_go Bw = false runs `li s1, 0` (+0x88) to the join cut, else the send cut.
                           Prop: close_head_stmt.
     send  +0xd8 .. +0xf4  a1 = 0xe3, a0 = s0, a2 = a3 = a4 = 0, `jal send_control` (+0xec; send_control_cg.v
                           transport_send_control_cg, a G-form callee in the same G journal), s1 = a0, `j` to the
                           join cut. Prop: close_send_stmt.
     join  +0x8c .. +0xd4  the checked store of 0 at s + 212 (close_w1 B1), a1 = 3, a2 = 8, a0 = s0, `jal set_state`
                           (+0xb0; set_state_cg.v transport_set_state_cg, a G-form callee in the same G journal), `j`
                           to the epilogue: a0 = s1, ra, s0, s1, s2 loaded back, sp + 32, `ret`. Prop: close_join_stmt.
   Each cut holds the caller's facts (close_fix), the journal and the facts carried at the cut (close_send_cur,
   close_join_cur, each over close_cur: the journal, the frames and blocks of the call, the meter, what the call has
   kept so far, the four saved words) and the registers the code after the cut reads (close_regs_base,
   close_regs_join), and concludes the statement's post (diginet_session_close_cg.v transport_close_post) at the cut's
   pc. The world at the join cut is B1 with close_sent timg_B TF Bw = Some (B1, r): send_control's world when
   close_go Bw holds, else Bw (and r = 0). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_close_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The two cut points, as offsets from the listing's base: the send path's first instruction (`li a1, 0xe3`, the
   target of `bne a0, a1` at +0x84) and the join (`addi a0, s0, 212`: the instruction after `li s1, 0` at +0x88 and
   the target of the send path's `j` at +0xf4). *)
Definition CLOSE_SEND : Z := AF_diginet_session_close + 0xd8.
Definition CLOSE_JOIN : Z := AF_diginet_session_close + 0x8c.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 (sd at sp + 24 .. sp + 0
   after `addi sp, sp, -32`). *)
Definition CLOSE_SAVED : list (Z * Z) := [(8, 1); (16, 8); (24, 9); (32, 18)].

(* The numerals of the stack windows: CLOSE_STK = 32 + SENDCTL_STK, set_state's SSTATE_STK below it. *)
Lemma close_stk_val : CLOSE_STK = 8688 /\ SENDCTL_STK = 8656 /\ SSTATE_STK = 8416 /\ CLOSE_FRAME = 32.
Proof. repeat split; reflexivity. Qed.
Lemma close_ev_val : CLOSE_EV = 0 /\ SENDCTL_EV = 0 /\ SSTATE_EV = 0.
Proof. repeat split; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* The constants the code holds as literals. *)
Lemma close_consts : TS0.DIGINET_CMD_DISCONNECT = 227 /\ TS0.DIGINET_S_CLOSED = 3 /\ TS0.DIGINET_R_CLOSED = 8.
Proof. repeat split; reflexivity. Qed.

(* The result of the call is the r of the send. *)
Lemma close_r_eq : forall I F Bw now Bw' B1 r1 r,
  TSS.diginet_session_close_m I F Bw now = Some (Bw', r) -> close_sent I F Bw = Some (B1, r1) -> r1 = r.
Proof.
  intros I F Bw now Bw' B1 r1 r Hm Hs. rewrite close_model, Hs in Hm. cbv beta iota in Hm.
  destruct (TSS.set_state_m I F (close_w1 B1) TS0.DIGINET_S_CLOSED TS0.DIGINET_R_CLOSED) as [[B2 u]|];
    [|discriminate Hm].
  exact (f_equal (fun o : option (list byte * Z) => match o with Some (_, x) => x | None => r1 end) Hm).
Qed.

(* close_go Bw false: no send, the world Bw and r = 0. *)
Lemma close_sent_nogo : forall I F Bw, close_go Bw = false -> close_sent I F Bw = Some (Bw, 0).
Proof. intros I F Bw H. unfold close_sent. rewrite H. reflexivity. Qed.

(* close_go Bw true: send_control_m gives the send's world B1 and the result r. *)
Lemma close_send_some : forall I F Bw now Bw' r,
  TSS.diginet_session_close_m I F Bw now = Some (Bw', r) -> close_go Bw = true ->
  exists B1 f, TSS.send_control_m I F Bw TS0.DIGINET_CMD_DISCONNECT 0 = Some (B1, (r, f)) /\
    close_sent I F Bw = Some (B1, r).
Proof.
  intros I F Bw now Bw' r Hm Hgo.
  assert (ES : close_sent I F Bw =
    match TSS.send_control_m I F Bw TS0.DIGINET_CMD_DISCONNECT 0 with
    | None => None
    | Some (B1, (r, _)) => Some (B1, r)
    end) by (unfold close_sent; rewrite Hgo; reflexivity).
  destruct (TSS.send_control_m I F Bw TS0.DIGINET_CMD_DISCONNECT 0) as [[B1 [r1 f]]|] eqn:EC.
  - pose proof (close_r_eq I F Bw now Bw' B1 r1 r Hm ES) as Er. subst r1.
    exists B1, f. split; [reflexivity | exact ES].
  - rewrite close_model, ES in Hm. discriminate Hm.
Qed.

(* After the send, the model is set_state_m at close_w1 B1 with S_CLOSED and R_CLOSED, giving Bw'. *)
Lemma close_sstate_some : forall I F Bw now Bw' B1 r1 r,
  TSS.diginet_session_close_m I F Bw now = Some (Bw', r) -> close_sent I F Bw = Some (B1, r1) ->
  TSS.set_state_m I F (close_w1 B1) TS0.DIGINET_S_CLOSED TS0.DIGINET_R_CLOSED = Some (Bw', tt).
Proof.
  intros I F Bw now Bw' B1 r1 r Hm Hs. rewrite close_model, Hs in Hm. cbv beta iota in Hm.
  destruct (TSS.set_state_m I F (close_w1 B1) TS0.DIGINET_S_CLOSED TS0.DIGINET_R_CLOSED) as [[B2 u]|];
    [|discriminate Hm].
  destruct u. f_equal. f_equal.
  exact (f_equal (fun o : option (list byte * Z) => match o with Some (b, _) => b | None => B2 end) Hm).
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The worlds                                                       *)
(* ------------------------------------------------------------------ *)

(* close_w1 at the numeral offset of g_s.inflight (s + 212). *)
Lemma close_w1_eq : forall B1, close_w1 B1 = TW.upd B1 (TW.OFF_g_s + 212) (TW.put 4 0).
Proof. intros B1. reflexivity. Qed.

(* g_fail_next is not g_s.inflight. *)
Lemma close_gfn1 : forall B1, Z.of_nat (length B1) = TW.W_LEN -> TW.g_fail_next (close_w1 B1) = TW.g_fail_next B1.
Proof.
intros B1 HL. assert (WL : TW.W_LEN = 65616) by reflexivity.
unfold close_w1, TW.g_fail_next, TW.set_S_inflight, TW.A_S_inflight.
rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia | |].
- right. rewrite TWL.length_put. change (Z.of_nat 4) with 4. unfold TW.OFF_g_s, TW.OFF_g_fail_next. lia.
- rewrite TWL.length_put, HL, WL. change (Z.of_nat 4) with 4. unfold TW.OFF_g_s. lia.
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma close_inG : forall a, CLOSE_S <= a < CLOSE_S + TW.SZ_g_s -> inG G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, CLOSE_S in *; cbn [fst snd]; lia].
Qed.

(* The world after the store of 0 at s + 212. *)
Lemma close_tw_w1 : forall (rd rd' : Z -> option Z) B1,
  tw_at TMAP_B rd B1 ->
  (forall j, 0 <= j < 4 -> rd' (CLOSE_S + 212 + j) = Some 0) ->
  (forall x, tw_in TMAP_B x -> ~ (CLOSE_S + 212 <= x < CLOSE_S + 216) -> rd' x = rd x) ->
  tw_at TMAP_B rd' (close_w1 B1).
Proof.
intros rd rd' B1 Hat HI HO.
assert (CS : CLOSE_S = TB_g_s) by reflexivity.
rewrite close_w1_eq.
apply (tw_write TMAP_B rd rd' B1 TW.OFF_g_s TB_g_s TW.SZ_g_s 212 4 0 TMAP_B_ok Hat TMAP_B_g_s);
  [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. rewrite <- CS, (HI (Z.of_nat j) ltac:(lia)).
  destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
- intros x Hx Hn. rewrite <- CS in Hn. apply HO; [exact Hx | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The written range                                                *)
(* ------------------------------------------------------------------ *)

(* A byte inside a row of G is a byte of G. *)
Lemma close_inG_row : forall b n a, In (b, n) G_HARNESS_B -> b <= a < b + n -> inG G_HARNESS_B a.
Proof.
  intros b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn; lia].
Qed.

(* A byte of a field of the TMAP_B row (o, b, n), inside the row. *)
Lemma close_fld_G : forall o b n A w a, In (o, b, n) TMAP_B -> twb_fld o b A w a -> o <= A -> A + w <= o + n ->
  inG G_HARNESS_B a.
Proof.
  intros o b n A w a Hin Ha H1 H2. apply (close_inG_row b n a (TMAP_B_in_G o b n Hin)).
  unfold twb_fld in Ha. lia.
Qed.

Ltac close_cz := apply Z.leb_le; vm_compute; reflexivity.
Ltac close_czl :=
  unfold TW.A_Cmd_st, TW.OFF_g_cmd, TW.SZ_g_cmd, TW.A_GOT_t_state, TW.GOT_t_ESZ, TW.OFF_GOT, TW.SZ_GOT,
    TC.CMDS_MAX, TC.TRANS_MAX in *; lia.

(* io_send's stores (iosend_wr n), field by field, for any n. *)
Lemma close_iosend_wr_G : forall n a, iosend_wr n a -> inG G_HARNESS_B a.
Proof.
  intros n a H. unfold iosend_wr in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]].
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_g_fail_next H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_GOT H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_GOT H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_GOT H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_g_last_counter H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_M H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_M H); [close_cz|].
    pose proof (Z.le_min_r n TC.SPEC_MAX_FRAME) as Hm.
    assert (C : TW.A_M_fly_frame + TC.SPEC_MAX_FRAME <= TW.OFF_M + TW.SZ_M) by close_cz.
    lia.
  - destruct H as (s & Hs & H). apply (close_fld_G _ _ _ _ _ a TMAP_B_g_cmd H); close_czl.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_g_q H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_g_nq H); close_cz.
Qed.

(* send_control's stores with kp = klp = 0. *)
Lemma close_sendctl_wr_G : forall a, sendctl_wr 0 0 a -> inG G_HARNESS_B a.
Proof.
  intros a H. unfold sendctl_wr in H. destruct H as [H | [H | (H & _)]].
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_g_s H); close_cz.
  - exact (close_iosend_wr_G _ a H).
  - exfalso. exact (H eq_refl).
Qed.

(* Every byte the call stores is a byte of G (notice's stores: TransportGNoticeB.v notice_wr_G). *)
Lemma close_wr_G : forall (F : option TI.tframe) Bw a, close_wr F Bw a -> inG G_HARNESS_B a.
Proof.
  intros F Bw a H. unfold close_wr in H. destruct H as [(_ & H) | [H | (B1 & r & _ & _ & [H | H])]].
  - exact (close_sendctl_wr_G a H).
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_g_s H); close_cz.
  - apply (close_fld_G _ _ _ _ _ a TMAP_B_g_s H); close_cz.
  - exact (notice_wr_G (close_w2 B1) (close_ntc B1) a H).
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The cuts                                                         *)
(* ------------------------------------------------------------------ *)

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma close_cut_pcs :
  BASE + AF_diginet_session_close = transportb_sigma TB_diginet_session_close /\ BASE + CLOSE_SEND = 0x87720 /\
  BASE + CLOSE_JOIN = 0x876d4.
Proof. vm_compute. repeat split. Qed.

(* The TRANS_RO_RD bytes at a later memory: the image clause of the walk's acall_kept_g (a TRANS_RO_RD byte is an
   image byte outside G, not an owned static, not errno). *)
Lemma close_rom : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (E : Z -> Prop),
  acall_kept_g segs B G_HARNESS_B lyc Sc W memc W2 mem2 slo shi E ->
  trans_rom_view_rd W memc -> trans_rom_view_rd W2 mem2.
Proof.
  intros HRU HRE lyc Sc W memc W2 mem2 slo shi E (_ & _ & K3 & _) HR a Ha.
  rewrite <- (HR a Ha).
  destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold G_HARNESS_B_LO in Gh. lia.
Qed.

(* The facts of the record every piece may use: the premises of transport_diginet_session_close_cg_holds_stmt that
   are not callee contracts. *)
Definition close_laws : Prop :=
  transport_cells B /\ trans_close_cells B /\ trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ gx_ok segs B G_HARNESS_B.

(* The caller's facts: the premises of transport_diginet_session_close_cg at the entry registers regs. *)
Definition close_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (now r : Z) (TF : option TI.tframe) (Bw Bw' : list byte) : Prop :=
  ajournal_gx G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 CLOSE_S /\ YK11.getr regs 11 = w64 now /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - CLOSE_STK /\ spZ regs <= sp0 /\
  0 <= now < 2 ^ 64 /\
  tw_at TMAP_B (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.diginet_session_close_m timg_B TF Bw now = Some (Bw', r) /\
  trans_tframe_at B lyc Sc W memc regs CLOSE_STK TF /\
  trans_rom_view_rd W memc /\
  close_apart TF Bw /\
  trans_tf_off_g TF /\
  (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) /\
  count_cid CLOSE_CID (frames Sc) + 1 < fs_frames CLOSE_CID /\
  st_nev S + k + CLOSE_EV <= EV_MAX.

(* What every cut carries, at the current state (ly2, S2, W2, mem2, md2) after e events: the caller's G journal; the
   call's frames exactly, the call's blocks, the frames where the call's layout puts them, the meter; what the call
   has kept so far (acall_kept_g over the statement's window and written range close_wr TF Bw); the four saved words
   below the entry sp. *)
Definition close_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (TF : option TI.tframe) (Bw : list byte)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= CLOSE_EV /\
  frames S2 = frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - CLOSE_STK) (spZ regs) (close_wr TF Bw) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) CLOSE_SAVED.

(* The state at the send cut (+0xd8), reached from the head only, when close_go Bw holds: the layout, the state, the
   world and the event count are the call's; the memory relates to the world Bw (the head stores only its frame). *)
Definition close_send_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (TF : option TI.tframe) (Bw : list byte)
    (mem2 : word -> option byte) (md2 : Model) : Prop :=
  close_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw lyc Sc W mem2 md2 0 /\
  tw_at TMAP_B (aview segs (w_H W) mem2) Bw /\
  close_go Bw = true.

(* The state at the join cut (+0x8c), from the head (close_go Bw false: B1 = Bw, r = 0) or after send_control
   returns: close_cur; the model's send (close_sent) gave B1 and r; the memory relates to the world B1;
   g_fail_next B1 <= 1. *)
Definition close_join_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (TF : option TI.tframe) (Bw B1 : list byte) (r : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  close_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw ly2 S2 W2 mem2 md2 e /\
  close_sent timg_B TF Bw = Some (B1, r) /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) B1 /\ TW.g_fail_next B1 <= 1.

(* The registers every cut holds: sp = the entry sp - 32, gp, tp, s0 = s, s2 = the shadow base, and s3 .. s11 the
   entry's (the epilogue reloads ra, s0, s1, s2 from the frame; s3 .. s11 are the caller's). *)
Definition close_regs_base (regs regs2 : bvmap 5 word) : Prop :=
  YK11.getr regs2 2 = w64 (spZ regs - CLOSE_FRAME) /\ YK11.getr regs2 3 = YK11.getr regs 3 /\
  YK11.getr regs2 4 = YK11.getr regs 4 /\ YK11.getr regs2 8 = w64 CLOSE_S /\ YK11.getr regs2 18 = w64 SHADOW_OFF /\
  (forall q, 19 <= q <= 27 -> YK11.getr regs2 (Z_to_bv 5 q) = YK11.getr regs (Z_to_bv 5 q)).
(* The join also reads s1 = r. *)
Definition close_regs_join (regs regs2 : bvmap 5 word) (r : Z) : Prop :=
  close_regs_base regs regs2 /\ YK11.getr regs2 9 = w64 r.

(* The join cut, +0x8c: from the state close_join_cur, the post; set_state's contract is its callee's. *)
Definition close_join_at : Prop :=
  close_laws ->
  (forall fx' : YK11.FPState, @transport_set_state_cg fx' rc B MT (transportb_sigma TB_set_state)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' B1 : list byte) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    close_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' ->
    close_join_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw B1 r ly2 S2 W2 mem2 md2 e ->
    close_regs_join regs regs2 r ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CLOSE_JOIN)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_close_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw Bw' r).

(* The send cut, +0xd8: from the state close_send_cur, the post; send_control's contract and the join's callee. *)
Definition close_send_at : Prop :=
  close_laws ->
  (forall fx' : YK11.FPState, @transport_set_state_cg fx' rc B MT (transportb_sigma TB_set_state)) ->
  (forall fx' : YK11.FPState, @transport_send_control_cg fx' rc B MT (transportb_sigma TB_send_control)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (mem2 : word -> option byte) (md2 : Model)
         (regs2 : bvmap 5 word),
    close_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' ->
    close_send_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw mem2 md2 ->
    close_regs_base regs regs2 ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CLOSE_SEND)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_close_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw Bw' r).

(* The three pieces. join: +0x8c .. the return. send: +0xd8 .. +0xf4, then the join cut. head: the entry .. +0x88,
   then the send or the join cut. *)
Definition close_join_stmt : Prop := close_join_at.
Definition close_send_stmt : Prop := close_join_at -> close_send_at.
Definition close_head_stmt : Prop :=
  close_send_at -> close_join_at -> @transport_diginet_session_close_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Lemma close_holds_of : close_head_stmt -> close_send_stmt -> close_join_stmt ->
  @transport_diginet_session_close_cg_holds_stmt fx rc B MT.
Proof. intros HEAD SEND JOIN. exact (HEAD (SEND JOIN) JOIN). Qed.
End cut.
