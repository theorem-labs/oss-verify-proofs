(* build_and_receive_segs (image B): the cut layer of the image-B walk of build_and_receive (fuzz_transport.asan-ubsan
   0x85998 = transportb_sigma TB_build_and_receive, AF_build_and_receive = 0x46f8 of lib/B/Prog/DgnTransportBList.v,
   252 words; statement lib/B/Prog/build_and_receive_cg.v). Definitions, the cut statements, the piece statements and
   their composition; no run. The image-A twin is lib/A/Prog/build_and_receive_segs.v: the same four pieces at image
   B's offsets, with image B's registers (s9 = frame[], s10 = the frame's shadow address, s7 = the shadow base, s4 =
   bodyp, s5 = max (len, 30), s8 = ack), its slots (the stack malloc's result at s1 + 24, cmd, retry, send and srcp at
   s1 + 32 .. s1 + 56), its order (the memset before the MAC memcpys) and its 23 UBSan tests (each to the trap word at
   +0x3ec, none taken).

   The walk holds the CALLER's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []) from the entry to the
   return, with (BAR_CID, pos) :: own while the class-5 frame is live. A cut is a concrete state at one pc. The
   pieces (offsets from the entry; each cut is the first instruction of its block):
     head  +0x000 .. +0x174  the 192-byte frame, the zero word at sp, the 13 saves, s0 = the entry sp, the realign
                             into s1, s3 = len, s4 = bodyp, the slots s1 + 32 (cmd), s1 + 40 (retry), s8 = ack, the
                             slots s1 + 48 (send), s1 + 56 (srcp), the two runtime cells (the flag word is 1, so
                             `beqz a2` at +0x080 is not taken), s7 = the shadow base, s6 = dstp, a0 = 1696 and
                             `jal __asan_stack_malloc_5` (+0x088; TransportGFrame.v gx_stack_malloc_at), `j +0x094`,
                             s2 = the frame F, the slot s1 + 24 := F (F >= 4096, so `bnez a0` at +0x09c skips the
                             real-stack arm), the slot s1 + 80, s9 = F + 32 = frame[], the frame's 24-byte header,
                             s10 = its shadow address and its shadow bytes 0 .. 3 := 0xf1, s11 = s10 + 4, `jal
                             __asan_set_shadow_f8` (+0x110; TransportGRt.v gx_set_shadow_at, 190 bytes), the shadow
                             bytes 194 .. 211 := 0xf3, `jal __asan_set_shadow_00` (+0x168, 189 bytes), the shadow byte
                             193 := 2. Prop: bar_head_stmt.
     mid   +0x178 .. +0x26c  s5 = max (len, 30), `jal __asan_memset` (+0x190: frame[6 .. n) = 0), `jal __asan_memcpy`
                             (+0x1a0: frame[0 .. 6) = dst), the UBSan test of frame[] + 6, `jal __asan_memcpy` (+0x1b8:
                             frame[6 .. 12) = src), the four stores frame[12 .. 16) with their UBSan tests, a1 = 0 and
                             the body sum loop (+0x214 .. +0x260; at each byte the three UBSan tests of bodyp + i and
                             the instrumented check, decided by the body's placement), or the len = 0 path (`beqz s3`
                             at +0x210). Prop: bar_mid_stmt.
     call  +0x270 .. +0x370  the fourteen stores frame[16 .. 30) with their UBSan tests, `jal __asan_memcpy` (+0x35c:
                             frame[30 .. 30 + len) = body, skipped when len = 0, after the UBSan test of frame[] + 30),
                             the four argument registers and `jal receive` (+0x370; a G-form callee in the same
                             journal). Prop: bar_call_stmt.
     rel   +0x374 .. +0x3e8  `jal __asan_set_shadow_f8` (+0x37c, 190 bytes), the header word 0x45e0360e at F, a0 = the
                             slot s1 + 24 (F), `beqz a0` (not taken), `jal __asan_stack_free_5` (+0x398;
                             TransportGRt.v gx_stack_free_cls_at), `j +0x3ac`, sp = s0 - 192, the 13 reloads,
                             sp = sp + 192, `ret`. Prop: bar_rel_stmt.
   Each cut holds the context's facts (bar_ok), the journal and the facts carried while the frame is live (bar_cur;
   bar_run adds the frame's shadow bytes, which every later check reads), the registers the code after the cut
   reads, and the frame's bytes written so far. Every cut concludes the statement's post transport_bar_post. *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_data_cg on_announce_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import build_and_receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TNeed TNeedLink TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TNL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeedLink.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The addresses, the frame and the saved words                     *)
(* ------------------------------------------------------------------ *)

(* The three cut points, as offsets of the listing: mid `mv s5, s3` (+0x178, the fall-through of the shadow byte 193
   store); call `addi a0, s9, 0x10` (+0x270, the join of the sum loop's exit `j +0x270` at +0x260 and of the len = 0
   path's `beqz s3` at +0x210); rel `addi a1, zero, 190` (+0x374, the return address of the call of receive,
   BAR_RA_RECV). The trap word `unimp` is at +0x3ec, the target of the 23 UBSan branches. *)
Definition BAR_MID : Z := AF_build_and_receive + 0x178.
Definition BAR_CALL : Z := AF_build_and_receive + 0x270.
Definition BAR_REL : Z := AF_build_and_receive + 0x374.
Definition BAR_TRAP : Z := AF_build_and_receive + 0x3ec.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11 (sd at sp + 184 ..
   sp + 88 after `addi sp, sp, -192`). *)
Definition BAR_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26); (104, 27)].
(* The class-5 frame's size; its last word (frame + 2040) holds the address of its flag byte. *)
Definition BAR_FBYTES : Z := 2048.
Lemma bar_fbytes : fs_frame_bytes BAR_CID = BAR_FBYTES.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 2. The frame the function builds                                    *)
(* ------------------------------------------------------------------ *)

(* The body's length, the value s5 holds (`max (len, 30)`, +0x178 .. +0x180) and the frame's length n = s5 + 30
   (TNeed.v spec_build_frame's n at :232). *)
Definition bar_len (body : list byte) : Z := Z.of_nat (length body).
Definition bar_s8 (body : list byte) : Z := Z.max (bar_len body) 30.
Definition bar_nn (body : list byte) : Z := bar_s8 body + 30.

(* The 18 header bytes spec_build_frame writes at frame[12 .. 30). *)
Definition bar_hdr (len send ack retry cmd : Z) (body : list byte) : list byte :=
  DSpec.put16 34911 ++ DSpec.put16 (16 + len) ++ DSpec.put16 (DSpec.spec_sum body) ++
  DSpec.put32 send ++ DSpec.put32 ack ++ DSpec.put16 retry ++ [DSpec.b8 cmd; DSpec.b8 1].

Lemma bar_hdr_len : forall l s a r c b, length (bar_hdr l s a r c b) = 18%nat.
Proof. intros. unfold bar_hdr, DSpec.put16, DSpec.put32. cbn [length app]. reflexivity. Qed.

(* The frame's bytes: the two MACs, the 18 header bytes, the body, and the zero padding of a body below 30 bytes
   (DgnSpec.v build_frame through TNeedLink.v tneed_spec_build_frame). *)
Lemma bar_frame_shape : forall (dst src : list byte) (send ack retry cmd : Z) (body : list byte),
  length dst = 6%nat -> length src = 6%nat ->
  bar_frame dst src send ack retry cmd body =
  dst ++ src ++ bar_hdr (bar_len body) send ack retry cmd body ++ body
      ++ repeat (DSpec.b8 0) (30 - length body)%nat.
Proof.
  intros dst src send ack retry cmd body Hd Hs.
  unfold bar_frame. rewrite (TNL.tneed_spec_build_frame dst src send ack retry cmd 1 body 0 Hd Hs).
  cbn [fst]. unfold DSpec.build_frame, bar_hdr, bar_len.
  cbn [negb Z.eqb]. rewrite !app_assoc. reflexivity.
Qed.

Lemma bar_frame_len : forall (dst src : list byte) (send ack retry cmd : Z) (body : list byte),
  length dst = 6%nat -> length src = 6%nat ->
  Z.of_nat (length (bar_frame dst src send ack retry cmd body)) = bar_nn body.
Proof.
  intros dst src send ack retry cmd body Hd Hs.
  rewrite (bar_frame_shape dst src send ack retry cmd body Hd Hs).
  rewrite !length_app, bar_hdr_len, repeat_length, Hd, Hs.
  unfold bar_nn, bar_s8, bar_len. lia.
Qed.

(* The first sixteen bytes: the two MACs, SPEC_ETHERTYPE and the length, which the mid piece writes (+0x190 ..
   +0x204) before the body sum. *)
Definition bar_pre16 (dst src : list byte) (body : list byte) : list byte :=
  dst ++ src ++ DSpec.put16 34911 ++ DSpec.put16 (16 + bar_len body).

Lemma bar_pre16_len : forall dst src body, length dst = 6%nat -> length src = 6%nat ->
  length (bar_pre16 dst src body) = 16%nat.
Proof.
  intros dst src body Hd Hs. unfold bar_pre16, DSpec.put16.
  rewrite !length_app, Hd, Hs. cbn [length]. reflexivity.
Qed.

Lemma bar_pre16_firstn : forall (dst src : list byte) (send ack retry cmd : Z) (body : list byte),
  length dst = 6%nat -> length src = 6%nat ->
  firstn 16 (bar_frame dst src send ack retry cmd body) = bar_pre16 dst src body.
Proof.
  intros dst src send ack retry cmd body Hd Hs.
  rewrite (bar_frame_shape dst src send ack retry cmd body Hd Hs).
  unfold bar_pre16, bar_hdr.
  destruct dst as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 [|? ?]]]]]]]; try discriminate Hd.
  destruct src as [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|? ?]]]]]]]; try discriminate Hs.
  unfold DSpec.put16, DSpec.put32. cbn [app firstn]. reflexivity.
Qed.

(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma bar_some_inv : forall Bx By : list byte, Some (Bx, tt) = Some (By, tt) -> Bx = By.
Proof. intros Bx By H. exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H). Qed.

(* The model premise rules the body bound out: build_and_receive_m is not None for the addresses recv_addr_ok
   names, and bar_model's first branch is None exactly when SPEC_MAX_BODY < len. *)
Lemma bar_body_bound : forall (Bw : list byte) (dst src : list byte) (send ack retry cmd : Z) (body : list byte),
  (forall a, recv_addr_ok a -> TOP.build_and_receive_m timg_B Bw a dst src send ack retry cmd body <> None) ->
  bar_len body <= TC.SPEC_MAX_BODY.
Proof.
  intros Bw dst src send ack retry cmd body HM.
  destruct (Z.leb_spec (bar_len body) TC.SPEC_MAX_BODY) as [Hle | Hgt]; [exact Hle|].
  assert (HA : recv_addr_ok 4096) by (unfold recv_addr_ok; lia).
  exfalso. apply (HM 4096 HA).
  rewrite bar_model.
  assert (HB : (TC.SPEC_MAX_BODY <? Z.of_nat (length body)) = true)
    by (apply Z.ltb_lt; unfold bar_len in Hgt; lia).
  rewrite HB. reflexivity.
Qed.

Lemma bar_max_body : TC.SPEC_MAX_BODY = 1484 /\ TC.SPEC_MAX_FRAME = 1514.
Proof. split; reflexivity. Qed.

(* The frame's length is at most SPEC_MAX_FRAME when the body is: n = 30 + max (len, 30) <= 1514. *)
Lemma bar_nn_bound : forall body, bar_len body <= TC.SPEC_MAX_BODY -> 60 <= bar_nn body <= TC.SPEC_MAX_FRAME.
Proof.
  intros body H. destruct bar_max_body as [E1 E2]. rewrite E1 in H. rewrite E2.
  unfold bar_nn, bar_s8, bar_len in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The context                                                      *)
(* ------------------------------------------------------------------ *)

Record bar_ctx : Type := mkBAR {
  cx_STK : Z; cx_sp0 : Z; cx_FP : list (Z * Z); cx_ly : alayout; cx_S : astate;
  cx_W0 : world tfibsegs; cx_mem0 : word -> option byte; cx_md0 : Model; cx_own : list (Z * Z);
  cx_lyc : alayout; cx_Sc : astate; cx_W : world tfibsegs; cx_memc : word -> option byte; cx_mdc : Model;
  cx_k : Z; cx_regs : bvmap 5 word;
  cx_dstp : Z; cx_srcp : Z; cx_bodyp : Z; cx_send : Z; cx_ack : Z; cx_retry : Z; cx_cmd : Z; cx_T : Z;
  cx_dst : list byte; cx_src : list byte; cx_body : list byte; cx_Bw : list byte;
  cx_ch : list (Z * Z * Z); cx_CTX : list (list Z) }.

Section bar. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS_B.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma bar_cut_pcs :
  BASE + AF_build_and_receive = transportb_sigma TB_build_and_receive /\
  BASE + BAR_MID = 0x85b10 /\ BASE + BAR_CALL = 0x85c08 /\ BASE + BAR_REL = 0x85d0c /\
  BASE + BAR_REL = BAR_RA_RECV /\ BASE + BAR_TRAP = 0x85d84.
Proof. repeat split; reflexivity. Qed.

(* The entry sp, the realigned sp (`addi sp, sp, -192`, `andi sp, sp, -32`) and the frame's address. *)
Definition bar_SP (c : bar_ctx) : Z := spZ (cx_regs c).
Definition bar_sp1 (c : bar_ctx) : Z := 32 * ((bar_SP c - BAR_FRAME) / 32).
Definition bar_F (c : bar_ctx) (pos : Z) : Z := frame_addr (cx_lyc c) BAR_CID pos.
(* The frame's bytes, as the code builds them, and its length. *)
Definition bar_fr (c : bar_ctx) : list byte :=
  bar_frame (cx_dst c) (cx_src c) (cx_send c) (cx_ack c) (cx_retry c) (cx_cmd c) (cx_body c).
Definition bar_N (c : bar_ctx) : Z := bar_nn (cx_body c).

(* The record facts and the callee contracts: the premises of transport_build_and_receive_cg_holds_stmt, with gx_ok
   and gx_noerrno of G_HARNESS_B (DgnTransportBCg.v G_HARNESS_gx_ok, G_HARNESS_gx_noerrno). *)
Definition bar_rt (CTX : list (list Z)) : Prop :=
  pc_stack_malloc (as_code B) BAR_CID = transportb_sigma TB___asan_stack_malloc_5 /\
  transport_cells B /\
  trans_g_unowned B /\ trans_g_no_errno B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ frame_flag_lawP segs B /\
  gx_ok segs B G /\ gx_noerrno B G /\
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B BAR_CID) /\
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transportb_sigma TB___asan_set_shadow_f8) 0xf8) /\
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transportb_sigma TB___asan_set_shadow_00) 0) /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset)) /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) /\
  (forall fx' : YK11.FPState, @transport_receive_cg fx' rc B MT (transportb_sigma TB_receive) (bar_recv_ctx CTX)) /\
  (forall fx' : YK11.FPState,
     @astack_free_cls_realizes fx' rc segs B (transportb_sigma TB___asan_stack_free_5) BAR_CID).

(* The contract's premises at the context (build_and_receive_cg.v transport_build_and_receive_cg). *)
Definition bar_ok (c : bar_ctx) : Prop :=
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    (cx_own c) (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) (cx_k c) /\
  YK0s.ret_ok (YK11.getr (cx_regs c) 1) /\ 4096 <= raZ (cx_regs c) /\
  YK11.getr (cx_regs c) 3 = w64 (as_gp B) /\ YK11.getr (cx_regs c) 4 = w64 (as_tp B) /\
  YK11.getr (cx_regs c) 10 = w64 (cx_dstp c) /\ YK11.getr (cx_regs c) 11 = w64 (cx_srcp c) /\
  bv_unsigned (YK11.getr (cx_regs c) 12) mod 2 ^ 32 = cx_send c /\
  bv_unsigned (YK11.getr (cx_regs c) 13) mod 2 ^ 32 = cx_ack c /\
  YK11.getr (cx_regs c) 14 = w64 (cx_retry c) /\ YK11.getr (cx_regs c) 15 = w64 (cx_cmd c) /\
  YK11.getr (cx_regs c) 16 = w64 (cx_bodyp c) /\
  YK11.getr (cx_regs c) 17 = w64 (bar_len (cx_body c)) /\
  @achain rc (cx_lyc c) (aview segs (w_H (cx_W c)) (cx_memc c)) (bar_SP c) (s0Z (cx_regs c)) (cx_ch c) /\
  In (raZ (cx_regs c) :: spine (cx_ch c)) (cx_CTX c) /\
  bar_SP c mod 16 = 0 /\ cx_sp0 c - cx_STK c <= bar_SP c - BAR_STK /\ bar_SP c <= cx_sp0 c /\
  0 <= cx_send c < 2 ^ 16 /\ 0 <= cx_ack c < 2 ^ 32 /\ 0 <= cx_retry c < 2 ^ 8 /\ 0 <= cx_cmd c < 2 ^ 8 /\
  length (cx_dst c) = 6%nat /\
  garr8 segs (mrestrict (w_H (cx_W c)) (cx_memc c)) (cx_dstp c) (TW.zs (cx_dst c)) /\
  trans_src_ok B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_dstp c) BAR_MAC /\
  decode_off_win (cx_regs c) BAR_STK (cx_dstp c) BAR_MAC /\
  length (cx_src c) = 6%nat /\
  garr8 segs (mrestrict (w_H (cx_W c)) (cx_memc c)) (cx_srcp c) (TW.zs (cx_src c)) /\
  trans_src_ok B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_srcp c) BAR_MAC /\
  decode_off_win (cx_regs c) BAR_STK (cx_srcp c) BAR_MAC /\
  garr8 segs (mrestrict (w_H (cx_W c)) (cx_memc c)) (cx_bodyp c) (TW.zs (cx_body c)) /\
  ((0 < length (cx_body c))%nat ->
     trans_src_ok B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_bodyp c) (bar_len (cx_body c)) /\
     decode_off_win (cx_regs c) BAR_STK (cx_bodyp c) (bar_len (cx_body c))) /\
  tw_at TMAP_B (aview segs (w_H (cx_W c)) (cx_memc c)) (cx_Bw c) /\ TW.g_fail_next (cx_Bw c) <= 1 /\
  (forall a, recv_addr_ok a ->
     TOP.build_and_receive_m timg_B (cx_Bw c) a (cx_dst c) (cx_src c) (cx_send c) (cx_ack c) (cx_retry c)
       (cx_cmd c) (cx_body c) <> None) /\
  trans_rom_view_rd (cx_W c) (cx_memc c) /\
  (TW.M_fly_on (cx_Bw c) <> 0 -> TW.M_fly_len (cx_Bw c) <= TC.SPEC_MAX_FRAME) /\
  (forall i, 0 <= i < TW.S_queued (cx_Bw c) -> TW.S_queue_len (cx_Bw c) i <= TS0.DIGINET_CMD_MAX_LEN) /\
  TW.S_queued (cx_Bw c) <= TC.QUEUE_MAX /\
  (forall s, 0 <= s < TW.g_ncmd (cx_Bw c) -> TW.Cmd_st (cx_Bw c) s = TC.PENDING ->
     TW.Cmd_len (cx_Bw c) s <= DSpec.SPEC_CMD_MAX) /\
  TW.g_ncmd (cx_Bw c) <= TC.CMDS_MAX /\
  1 <= TW.S_cfg_max_cmds (cx_Bw c) /\ 1 <= TW.S_cfg_max_body (cx_Bw c) /\
  recv_dn_each timg_B (cx_Bw c) (bar_fr c) 0 0 /\
  count_cid BAR_CID (frames (cx_Sc c)) + 2 < fs_frames BAR_CID /\
  count_cid SRX_CID (frames (cx_Sc c)) + 1 < fs_frames SRX_CID /\
  count_cid ONANN_CID (frames (cx_Sc c)) < fs_frames ONANN_CID /\
  count_cid SENDDATA_CID (frames (cx_Sc c)) < fs_frames SENDDATA_CID /\
  count_cid ONDATA_CID (frames (cx_Sc c)) + 2 < fs_frames ONDATA_CID /\
  st_nev (cx_S c) + cx_k c + BAR_EV <= EV_MAX /\
  blocks_bytes (cx_Sc c) + RECV_LIVE <= LIVE_MAX /\
  mo_ok MT (cx_Sc c) (cx_T c) /\ recv_cost MT (bar_N c) <= cx_T c.

(* bar_ok is a chain of 53 conjuncts, so every piece that counted underscores to reach one would break whenever a
   clause is added. These two accessors name what the pieces read most and cannot read off cheaply: the stack
   facts, which take the journal apart, and the two MAC lengths. *)

(* The stack facts of the context, from its journal: AR at the call state, the entry sp's range and alignment, the
   statement's window above the allocation ceiling and present at the call memory, and the realigned sp of
   `addi sp, sp, -192` / `andi sp, sp, -32`, with every callee window below it inside the statement's. *)
Lemma bar_ok_sp : forall c, bar_ok c ->
  @AR rc segs B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) /\
  2 ^ 46 <= bar_SP c <= 2 ^ 47 /\ YM05.alloc_ceiling <= bar_SP c - BAR_STK /\
  (forall a, bar_SP c - BAR_STK <= a < bar_SP c -> apresent (w_H (cx_W c)) (cx_memc c) a) /\
  bar_SP c mod 16 = 0 /\ cx_sp0 c mod 16 = 0 /\
  cx_sp0 c - cx_STK c <= bar_SP c - BAR_STK /\ bar_SP c <= cx_sp0 c /\
  bar_sp1 c mod 32 = 0 /\ bar_SP c - 208 <= bar_sp1 c <= bar_SP c - 192 /\
  bar_SP c - BAR_STK <= bar_sp1 c - RECV_STK /\ bar_sp1 c mod 16 = 0.
Proof.
  intros c HOK.
  destruct HOK as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & _).
  pose proof HJ as (HSTK & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  clear HJi memS.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EBS : BAR_STK = 208 + RECV_STK) by exact bar_stk_eq.
  assert (ERS : 0 <= RECV_STK) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (Hx : 0 <= bar_SP c - BAR_FRAME) by (unfold BAR_FRAME; lia).
  assert (Hx16 : (bar_SP c - BAR_FRAME) mod 16 = 0)
    by (unfold BAR_FRAME; rewrite Zminus_mod, Hsp16; reflexivity).
  destruct (can_sp1_facts (bar_SP c - BAR_FRAME) Hx Hx16) as (HS1r & HS1al & HS1al16).
  assert (ES1 : bar_sp1 c = 32 * ((bar_SP c - BAR_FRAME) / 32)) by reflexivity.
  rewrite <- ES1 in HS1r, HS1al, HS1al16.
  split; [exact HAR|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; apply Hpres0; lia|].
  split; [exact Hsp16|]. split; [exact Hsp0a|].
  split; [exact Hlo|]. split; [exact Hhi|].
  split; [exact HS1al|]. split; [unfold BAR_FRAME in HS1r; lia|].
  split; [unfold BAR_FRAME in HS1r; lia | lia].
Qed.

(* The two MAC lengths, which the frame lemmas bar_frame_shape / bar_frame_len / bar_pre16_firstn ask for. *)
Lemma bar_ok_len : forall c, bar_ok c -> length (cx_dst c) = 6%nat /\ length (cx_src c) = 6%nat.
Proof.
  intros c HOK.
  destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HLD & _ & _ & _ & HLS & _).
  exact (conj HLD HLS).
Qed.

(* The frame's length, as the post's cost and written range read it. *)
Lemma bar_ok_frame_len : forall c, bar_ok c -> Z.of_nat (length (bar_fr c)) = bar_N c.
Proof.
  intros c HOK. destruct (bar_ok_len c HOK) as [HLD HLS].
  exact (bar_frame_len (cx_dst c) (cx_src c) (cx_send c) (cx_ack c) (cx_retry c) (cx_cmd c) (cx_body c) HLD HLS).
Qed.
(* The contract's post at the context. *)
Definition bar_post (c : bar_ctx) : world segs -> config -> Prop :=
  @transport_bar_post fx rc B MT (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c)
    (cx_md0 c) (cx_own c) (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_k c) (cx_regs c) (cx_Bw c)
    (cx_dst c) (cx_src c) (cx_send c) (cx_ack c) (cx_retry c) (cx_cmd c) (cx_body c).

(* ------------------------------------------------------------------ *)
(* 4. What the cuts carry                                             *)
(* ------------------------------------------------------------------ *)

(* What every cut carries while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames
   where the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's
   window and written range recv_wr of the frame); the 13 saved words below the entry sp; the frame's last word, the
   address of its flag byte (astack_malloc_realizes' rdword); the slot s1 + 24, the stack malloc's result (the frame),
   which the release reloads at +0x38c (image A kept it in s4). *)
Definition bar_cur (c : bar_ctx) (pos : Z) (ly2 : alayout) (S2 : astate) (W2 : world segs)
    (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((BAR_CID, pos) :: cx_own c) ly2 S2 W2 mem2 md2 (cx_k c + e) /\
  0 <= e <= BAR_EV /\
  frames S2 = (BAR_CID, pos) :: frames (cx_Sc c) /\
  Permutation (ablocks B ly2 S2) (ablocks B (cx_lyc c) (cx_Sc c)) /\
  ly_F ly2 = ly_F (cx_lyc c) /\
  mo_le MT (cx_Sc c) S2 (recv_cost MT (bar_N c)) /\
  acall_kept_g segs B G (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) W2 mem2 (bar_SP c - BAR_STK) (bar_SP c)
    (recv_wr (bar_fr c)) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (bar_SP c - fst o) =
      Some (bv_unsigned (YK11.getr (cx_regs c) (Z_to_bv 5 (snd o))))) BAR_SAVED /\
  rdword (aview segs (w_H W2) mem2) (bar_F c pos + BAR_FBYTES - 8) = Some (flag_addr (cx_lyc c) BAR_CID pos) /\
  rdword (aview segs (w_H W2) mem2) (bar_sp1 c + 24) = Some (bar_F c pos).

(* Before the call of receive the walk has written no byte of G, so the state is the entry's: the layout, the world,
   the blocks and the event count are the call's, the meter has not moved, and the world relation holds at Bw. The
   frame's shadow bytes 4 .. 192 are 0 and byte 193 is 2 (the two fills and the store at +0x174), so every
   instrumented check of a byte of frame[0 .. 1514) is decided. Presence is stated at or above alloc_ceiling only:
   that is what the class-5 stack malloc's acall_kept promises (its two presence clauses are the window and the
   bytes at or above the ceiling). Below the ceiling the own frame's bytes and shadow bytes are present at the
   current state by AR's own frame law (al_frames), and a caller's block or frame byte keeps its view, which is
   presence for a byte outside the image (apresent_transfer). *)
Definition bar_run (c : bar_ctx) (pos : Z) (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  bar_cur c pos (cx_lyc c) S2 (cx_W c) mem2 md2 0 /\
  ablocks B (cx_lyc c) S2 = ablocks B (cx_lyc c) (cx_Sc c) /\
  mo_le MT (cx_Sc c) S2 0 /\
  gx_kept segs G (cx_W c) (cx_memc c) (cx_W c) mem2 /\
  (forall i, 4 <= i < 193 -> aview segs (w_H (cx_W c)) mem2 (SHADOW_OFF + bar_F c pos / 8 + i) = Some 0) /\
  aview segs (w_H (cx_W c)) mem2 (SHADOW_OFF + bar_F c pos / 8 + 193) = Some 2 /\
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 ->
     apresent (w_H (cx_W c)) (cx_memc c) a -> apresent (w_H (cx_W c)) mem2 a).

(* ---- the registers at the cuts ---- *)

(* What every cut holds: sp = s1 = sp1, gp, tp, s0 = the entry sp, s2 = the frame, s7 = the shadow base,
   s9 = frame[] = F + 32, s10 = the frame's shadow address, s11 = s10 + 4. *)
Definition bar_rg (c : bar_ctx) (pos : Z) (regs2 : bvmap 5 word) : Prop :=
  YK11.getr regs2 2 = w64 (bar_sp1 c) /\ YK11.getr regs2 3 = w64 (as_gp B) /\
  YK11.getr regs2 4 = w64 (as_tp B) /\
  YK11.getr regs2 8 = w64 (bar_SP c) /\ YK11.getr regs2 9 = w64 (bar_sp1 c) /\
  YK11.getr regs2 18 = w64 (bar_F c pos) /\
  YK11.getr regs2 23 = w64 SHADOW_OFF /\
  YK11.getr regs2 25 = w64 (bar_F c pos + 32) /\
  YK11.getr regs2 26 = w64 (SHADOW_OFF + bar_F c pos / 8) /\
  YK11.getr regs2 27 = w64 (SHADOW_OFF + bar_F c pos / 8 + 4).
(* The mid and call cuts also hold s3 = len, s4 = bodyp and s8 = ack. *)
Definition bar_rg_run (c : bar_ctx) (pos : Z) (regs2 : bvmap 5 word) : Prop :=
  bar_rg c pos regs2 /\
  YK11.getr regs2 19 = w64 (bar_len (cx_body c)) /\
  YK11.getr regs2 20 = w64 (cx_bodyp c) /\
  YK11.getr regs2 24 = YK11.getr (cx_regs c) 13.

(* The four slots of its own machine frame the code reads back: s1 + 32 (cmd, read at +0x330), s1 + 40 (retry,
   +0x320), s1 + 48 (send, +0x29c) and s1 + 56 (srcp, +0x1b4). srcp, retry and cmd have a range of their own in the
   contract (trans_src_ok of [srcp, srcp + 6); 0 <= retry, cmd < 2 ^ 8), so the slot holds the number; the send
   register does not (a0-width send is cut to 32 bits), so its slot is stated as the register's unsigned value. *)
Definition bar_slots (c : bar_ctx) (W2 : world segs) (mem2 : word -> option byte) : Prop :=
  rdword (aview segs (w_H W2) mem2) (bar_sp1 c + 32) = Some (cx_cmd c) /\
  rdword (aview segs (w_H W2) mem2) (bar_sp1 c + 40) = Some (cx_retry c) /\
  rdword (aview segs (w_H W2) mem2) (bar_sp1 c + 48) = Some (bv_unsigned (YK11.getr (cx_regs c) 12)) /\
  rdword (aview segs (w_H W2) mem2) (bar_sp1 c + 56) = Some (cx_srcp c).

(* ---- the cuts: from the cut's state, the post ---- *)

(* rel (+0x374): after receive. The frame is live, the world is receive's, and the post's X already holds. *)
Definition bar_rel_at (c : bar_ctx) : Prop :=
  bar_rt (cx_CTX c) -> bar_ok c ->
  forall pos ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) (e : Z) (a : Z) (Bw' : list byte),
    bar_cur c pos ly2 S2 W2 mem2 md2 e -> bar_rg c pos regs2 ->
    recv_addr_ok a ->
    TOP.build_and_receive_m timg_B (cx_Bw c) a (cx_dst c) (cx_src c) (cx_send c) (cx_ack c) (cx_retry c)
      (cx_cmd c) (cx_body c) = Some (Bw', tt) ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' -> TW.g_fail_next Bw' <= 1 ->
    SRr segs W2 (@cfg_at fx segs (BASE + BAR_REL) regs2 mem2 md2) (bar_post c).

(* call (+0x270): the fourteen header stores, the body memcpy and the call of receive. a1 = the body's sum, s5 =
   max (len, 30), the first sixteen frame bytes written, the rest of frame[0 .. n) still 0 (the memset's). *)
Definition bar_call_at (c : bar_ctx) : Prop :=
  bar_rt (cx_CTX c) -> bar_ok c ->
  forall pos S2 mem2 md2 (regs2 : bvmap 5 word),
    bar_run c pos S2 mem2 md2 -> bar_rg_run c pos regs2 -> bar_slots c (cx_W c) mem2 ->
    YK11.getr regs2 11 = w64 (DSpec.sum_bytes (cx_body c)) ->
    YK11.getr regs2 21 = w64 (bar_s8 (cx_body c)) ->
    garr8 segs (mrestrict (w_H (cx_W c)) mem2) (bar_F c pos + 32)
      (TW.zs (bar_pre16 (cx_dst c) (cx_src c) (cx_body c))) ->
    (forall i, 16 <= i < bar_N c ->
       aview segs (w_H (cx_W c)) mem2 (bar_F c pos + 32 + i) = Some 0) ->
    SRr segs (cx_W c) (@cfg_at fx segs (BASE + BAR_CALL) regs2 mem2 md2) (bar_post c).

(* mid (+0x178): s5 = max (len, 30), the memset, the two MAC memcpys, the four stores and the body sum. a1 holds
   30, the constant `addi a1, zero, 30` at +0x170 left for the `bltu a1, s3` at +0x17c; s6 = dstp. *)
Definition bar_mid_at (c : bar_ctx) : Prop :=
  bar_rt (cx_CTX c) -> bar_ok c ->
  forall pos S2 mem2 md2 (regs2 : bvmap 5 word),
    bar_run c pos S2 mem2 md2 -> bar_rg_run c pos regs2 -> bar_slots c (cx_W c) mem2 ->
    YK11.getr regs2 22 = w64 (cx_dstp c) ->
    YK11.getr regs2 11 = w64 30 ->
    SRr segs (cx_W c) (@cfg_at fx segs (BASE + BAR_MID) regs2 mem2 md2) (bar_post c).

(* The walk from the entry. *)
Definition bar_entry (c : bar_ctx) : Prop :=
  bar_rt (cx_CTX c) -> bar_ok c ->
  SRr segs (cx_W c)
    (@cfg_at fx segs (transportb_sigma TB_build_and_receive) (cx_regs c) (cx_memc c) (cx_mdc c)) (bar_post c).

(* ---- the four pieces, in continuation form ---- *)
Definition bar_rel_stmt : Prop := forall c, bar_rel_at c.
Definition bar_call_stmt : Prop := forall c, bar_rel_at c -> bar_call_at c.
Definition bar_mid_stmt : Prop := forall c, bar_call_at c -> bar_mid_at c.
Definition bar_head_stmt : Prop := forall c, bar_mid_at c -> bar_entry c.

(* The walk from its pieces. *)
Lemma bar_walk : bar_head_stmt -> bar_mid_stmt -> bar_call_stmt -> bar_rel_stmt -> forall c, bar_entry c.
Proof.
  intros HEAD MID CALL REL c.
  exact (HEAD c (MID c (CALL c (REL c)))).
Qed.

End bar.
