(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1223 of its 1346 lines of code are new or changed and 1016 lines of the source are left out. *)
(* diginet_session_poll_seg_head (image B): Theorem pw_head_piece : pw_head_stmt
   (lib/B/Prog/diginet_session_poll_segs.v), the head piece: from the entry (0x8aa98) to the cut now1 or rel: the
   frame, the 13 saves, s0, the realign into s1, s9 = max_wait_ms, the two runtime cells, `jal __asan_stack_malloc_5`
   (+0x070; lib/A/Prog/TransportGFrame.v gx_stack_malloc_at), the frame word at s1 + 48, the frame's header and shadow
   bytes 0 .. 3, `jal __asan_set_shadow_f8` (+0x0f4; lib/A/Prog/diginet_session_poll_seg_rt.v gx_set_shadow_at), shadow
   bytes 194 .. 211, `jal __asan_set_shadow_00` (+0x14c), shadow byte 193 := 2, s10 = -1, the slots s1 + 16 and s1 + 8,
   `beqz s3` (not taken), the UBSan alignment check of s (`andi a0, s3, 7`, `bnez a0` to the trap word at +0x390; not
   taken), the checked loads of io.recv (s + 80), io.now_us (s + 88; the slot s1 + 24) and io.ctx (s + 64): a NULL
   pointer to the cut rel (the model's DIGINET_E_ARG), else to the cut now1.
   The image-A twin is lib/A/Prog/diginet_session_poll_seg_head.v; image B's code is image A's with the alignment check
   added at +0x168, so every offset from +0x168 on is image A's + 8.
   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []); four runs of the
   position-abstract engine (lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x) and three calls:
     run 1  +0x000 .. +0x070  the frame, the saves, the realign, the runtime cells (the flag word is 1, so `beqz a2`
                              is not taken), s5 = the shadow base, s3 = s, a0 = 1696, up to `jal __asan_stack_malloc_5`;
     run 2  +0x074 .. +0x0f4  the frame F in a0 (F >= 4096, so `bnez s6` skips the real-stack arm), s2 = s6 = F, the
                              frame word at s1 + 48, the 24-byte header, s4 = the frame's shadow address (atom 33 by
                              the engine's shadow alias, lib/Reusable/YP0i.v shadow_norm) and its shadow bytes 0 .. 3,
                              s7 = s4 + 4, up to `jal __asan_set_shadow_f8` (a0 = s7, a1 = 190);
     run 3  +0x0f8 .. +0x14c  shadow bytes 194 .. 211, up to `jal __asan_set_shadow_00` (a0 = s7, a1 = 189);
     run 4  +0x150 ..         shadow byte 193 := 2, s10 = -1, the slots s1 + 16 and s1 + 8, `beqz s3` (s = g_s, not
                              taken), `andi a0, s3, 7` and `bnez a0` (not taken: atom 19 is g_s, a multiple of 64 by
                              its fact), the checks of s + 80, s + 88 and s + 64 (each reads a zero shadow byte of g_s,
                              a chunk of the run's region at g_s's shadow address: the alias (s3 >> 3) + s5 = atom 33;
                              trans_poll_cells), the loads of io.recv and io.now_us (the world's, tw_read_val) and the
                              two tests (:508-509): a NULL pointer goes to rel (+0x314), else the run reaches now1
                              (+0x1c4) with a0 = io.ctx and a1 = io.now_us.
   The facts the cuts carry are stated once (ph_cur below, at any memory that differs from the stack malloc's only in
   the written ranges PH_ZS: the frame's header, the frame's 256 shadow bytes and the call's window from sp1 - ESTACK
   to sp1 + 56) and read off at each cut. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YF0x YE2y.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require io_now_cg diginet_session_deadline_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TRunInv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_seg_rt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  diginet_session_poll_seg_leaf diginet_session_poll_seg_grecv diginet_session_poll_seg_grx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TPoll TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TPL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TPoll.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module TRI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRunInv.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. Numerals                                                         *)
(* ------------------------------------------------------------------ *)

(* The world offsets of the three g_s fields the head loads, as numerals: the walk never leaves the kernel a
   conversion between a world accessor and its definition. *)
Definition PH_O_CTX : Z := 1712.   (* s + 64, S_io_ctx *)
Definition PH_O_RECV : Z := 1728.  (* s + 80, S_io_recv *)
Definition PH_O_NOW : Z := 1736.   (* s + 88, S_io_now_us *)
Lemma ph_recv_eq : forall Bw, TW.S_io_recv Bw = TW.u_at Bw PH_O_RECV 8.
Proof. intros Bw. reflexivity. Qed.
Lemma ph_now_eq : forall Bw, TW.S_io_now_us Bw = TW.u_at Bw PH_O_NOW 8.
Proof. intros Bw. reflexivity. Qed.

(* g_s's shadow address. *)
Definition PH_GSH : Z := SHADOW_OFF + POLL_S / 8.

Lemma ph_nums : PH_GSH = 2148220616 /\ POLL_S = 6157888 /\ SHADOW_OFF = 2147450880 /\ TW.SZ_g_s = 18264 /\
  kLowShadowBeg = 2147446784 /\ kHighMemBeg = 17594333495296 /\ kLowMemEnd = 2147450880 /\
  POLL_S / 8 = 769736 /\ POLL_FRAME = 160 /\ POLL_STK = 9360 /\ ESTACK = 4096 /\ POLL_CID = 5 /\
  POLL_FBYTES = 2048 /\ TB_g_s = 6157888 /\ AF_diginet_session_poll = 38904 /\
  PW_SH64 = 2148220624 /\ PW_SH80 = 2148220626 /\ PW_SH88 = 2148220627 /\
  PW_REL = 39692 /\ PW_NOW1 = 39356.
Proof. repeat split; reflexivity. Qed.
Ltac ph_lia :=
  let HN := fresh "HN" in pose proof ph_nums as HN;
  destruct HN as (?EG & ?ESg & ?ESH & ?ESZ & ?ELS & ?EHM & ?ELM & ?EQS & ?EFR & ?ESTK & ?EES & ?ECID & ?EFB
    & ?ETAG & ?EAF & ?E64 & ?E80 & ?E88 & ?EREL & ?ENOW);
  lia.

(* ------------------------------------------------------------------ *)
(* 2. The four symbolic states                                         *)
(* ------------------------------------------------------------------ *)

(* run 1: the entry.  Regions: the 160-byte frame below sp (the zero word and the 13 saves), and the two runtime
   cells through their GOT words (objects 1 / 95: the shadow base; objects 0 / 96: the use-after-return flag). *)
Definition ph_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 96) 0))].
Definition ph_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 96)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition ph_img_regions : smem := [got_regionP; bcell_regionP 32; ph_got_uar; ph_uar_cell].
Definition ph_regions1 : smem := stack_region POLL_FRAME :: ph_img_regions.
Definition ph_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (10%nat, mkAF POLL_S POLL_S 0)] [] [].
Definition ss_ph1 : sstate := mkSS AF_diginet_session_poll sr_atoms ph_regions1 None ph_facts1.
(* No run uses the token engine: every instrumented check reads a shadow region of its state. *)
Definition PH_B0 : Z * Z := (0, 0).

(* run 2: +0x74, the frame in a0 (atom 10); atom 33 is its shadow address, which the alias lets the engine reach
   from `(s2 >> 3) + s5`. *)
Definition PH_C2 : Z := AF_diginet_session_poll + 0x74.
Definition ph_alias2 : list (sv * sv) :=
  [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 21 0), SOff 33 0)].
Definition ph_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition ph_rg_fsh : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 4 [].
Definition ph_rg_fslot : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [].
Definition ph_regions2 : smem := [ph_rg_hdr; ph_rg_fsh; ph_rg_fslot].
Definition ph_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (21%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] ph_alias2.
Definition ss_ph2 : sstate := mkSS PH_C2 sr_atoms ph_regions2 None ph_facts2.

(* run 3: +0xf8, s4 (atom 20) the frame's shadow address. *)
Definition PH_C3 : Z := AF_diginet_session_poll + 0xf8.
Definition ph_rg_rg : YP09.region := YP09.mkRegion (Some 20%nat) 194 212 194 212 [].
Definition ph_facts3 : facts := mkFacts [(20%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_ph3 : sstate := mkSS PH_C3 sr_atoms [ph_rg_rg] None ph_facts3.

(* run 4: +0x150.  Atom 33 is g_s's shadow address (the alias of `(s3 >> 3) + s5`), atoms 34, 35, 36 the three
   8-byte fields io.ctx, io.recv and io.now_us. *)
Definition PH_C4 : Z := AF_diginet_session_poll + 0x150.
Definition ph_alias4 : list (sv * sv) :=
  [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 21 0), SOff 33 0)].
Definition ph_rg_b193 : YP09.region := YP09.mkRegion (Some 20%nat) 193 194 193 194 [].
Definition ph_rg_slots : YP09.region := YP09.mkRegion (Some 9%nat) 8 32 8 32 [].
Definition ph_rg_gsh : YP09.region := YP09.mkRegion (Some 33%nat) 8 12 0 0
  [YP09.mkChunk 8 (CVal 1 (SLit 0)); YP09.mkChunk 9 (CVal 1 (SLit 0));
   YP09.mkChunk 10 (CVal 1 (SLit 0)); YP09.mkChunk 11 (CVal 1 (SLit 0))].
Definition ph_rg_gs : YP09.region := YP09.mkRegion (Some 19%nat) 64 96 0 0
  [YP09.mkChunk 64 (CVal 8 (SOff 34 0)); YP09.mkChunk 80 (CVal 8 (SOff 35 0));
   YP09.mkChunk 88 (CVal 8 (SOff 36 0))].
Definition ph_regions4 : smem := [ph_rg_b193; ph_rg_slots; ph_rg_gsh; ph_rg_gs].
Definition ph_facts4 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (19%nat, mkAF POLL_S POLL_S 6); (20%nat, mkAF SHADOW_OFF (2 ^ 46) 0);
           (21%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF PH_GSH PH_GSH 0)] [] ph_alias4.
Definition ss_ph4 : sstate := mkSS PH_C4 sr_atoms ph_regions4 None ph_facts4.

(* The values of atoms 32 .. 36 of run 4's valuation. *)
Definition ph_vals4 (Bw : list byte) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 PH_GSH; Z_to_bv 64 (TW.u_at Bw PH_O_CTX 8);
   Z_to_bv 64 (TW.u_at Bw PH_O_RECV 8); Z_to_bv 64 (TW.u_at Bw PH_O_NOW 8)].

(* The bytes the head may change after the stack malloc: the frame's header, the frame's 256 shadow bytes, and the
   call's window from the runtime entries' ESTACK bytes below sp1 to the slots below sp1 + 56. *)
Definition PH_ZS (F sp1 a : Z) : Prop :=
  (F <= a < F + 24) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 256) \/ (sp1 - ESTACK <= a < sp1 + 56).
(* The bytes run 4 may change: shadow byte 193 and the slots s1 + 8 .. s1 + 32. *)
Definition PH_Z4 (F sp1 a : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 193 <= a < SHADOW_OFF + F / 8 + 194) \/ (sp1 + 8 <= a < sp1 + 32).

(* ------------------------------------------------------------------ *)
(* 3. The model on this path                                           *)
(* ------------------------------------------------------------------ *)

(* `beqz` on an 8-byte field: the model's test of the field against 0. *)
Lemma ph_br_eq64 : forall E Bw n o, ew E n = Z_to_bv 64 (TW.u_at Bw o 8) ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (TW.u_at Bw o 8 =? 0).
Proof.
intros E Bw n o H. pose proof (TWL.u_at_range Bw o 8) as R.
cbn [branch_taken sv_denot]. rewrite H, unsigned_lit_small, Z.add_0_r by lia.
unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0 (2 ^ 64)) by lia. rewrite (Z.mod_small (TW.u_at Bw o 8) (2 ^ 64)) by lia.
reflexivity.
Qed.

(* A one-byte cell read off its value. *)
Lemma ph_aview_of_val1 : forall H (m : word -> option byte) a v,
  val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview tfibsegs H m a = Some v.
Proof.
intros H m a v HV Hv. pose proof (HV 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
lazymatch goal with |- context [?f v 1%nat 0%nat] => unfold f end.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. repeat rewrite (Z.mod_small v 256) by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma ph_vals_img : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 96) = FCells.UAR /\
  BASE + AF_diginet_session_poll = transportb_sigma TB_diginet_session_poll.
Proof using All. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma ph_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 96) = Z_to_bv 64 (VAL (A_OBJ 96)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) ph_img_regions /\
  pairwise_disjoint E ph_img_regions.
Proof using All.
  intros ly S W mem md E HCELLS HAR E1 E93 E0 E94 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct ph_vals_img as (V1 & V93 & V0 & V94 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (Kguar : rdword (aview segs (w_H W) mem) FCells.GOT_UAR = Some FCells.UAR)
    by (apply (rdword_cell B ly); [unfold FCells.UAR; lia | exact (CH _ I7)]).
  assert (Kuar : rd32 (aview segs (w_H W) mem) FCells.UAR 1).
  { pose proof (CH _ I6) as H6. unfold cell_holds in H6. cbn [c_at c_val c_w z4 c4 aeval] in H6.
    intros j Hj. exact (H6 j Hj). }
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  split.
  - unfold ph_img_regions, got_regionP, bcell_regionP, ph_got_uar, ph_uar_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      split; [rewrite V1; unfold FCells.GOT_CELL_K; lia|].
      split; [rewrite V1; unfold FCells.GOT_CELL_K; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 95) 0) (VAL (A_OBJ 95)));
      [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite V93; unfold FCells.CELL_K; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E93) by (rewrite V93; unfold FCells.CELL_K; lia).
      split; [rewrite V93; unfold FCells.CELL_K; lia|].
      split; [rewrite V93; unfold FCells.CELL_K; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 95)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (rewrite V0; unfold FCells.GOT_UAR; lia).
      split; [rewrite V0; unfold FCells.GOT_UAR; lia|].
      split; [rewrite V0; unfold FCells.GOT_UAR; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 96) 0) (VAL (A_OBJ 96)));
      [cbn [sv_denot]; rewrite E94, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite V94; unfold FCells.UAR; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r, V0, V94. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
    + rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) E94) by (rewrite V94; unfold FCells.UAR; lia).
      split; [rewrite V94; unfold FCells.UAR; lia|].
      split; [rewrite V94; unfold FCells.UAR; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 96)) 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r, V94. exact (can_val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold ph_img_regions, got_regionP, bcell_regionP, ph_got_uar, ph_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E93) by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) E94) by (rewrite V94; unfold FCells.UAR; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

Definition ph_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transportb) (Ereg regs extra).

Lemma ph_env_img : forall regs extra, img_env VAL A_LIM (ph_E regs extra).
Proof using All. intros regs extra. unfold ph_E. apply Eimg_env. Qed.
Lemma ph_ew_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (ph_E regs extra) n = YK11.getr regs r.
Proof using All. intros. unfold ph_E. apply can_ew_Eimg_Ereg_nat. assumption. Qed.
Lemma ph_ew_extra : forall regs extra j, (j < length extra)%nat -> (j < 200)%nat ->
  ew (ph_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof using All.
  intros regs extra j Hj Hj2. unfold ph_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.
Lemma ph_ew_obj : forall regs extra i, (i < 97)%nat -> ew (ph_E regs extra) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof using All. intros. unfold ph_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.

Lemma ph_den : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof using All.
intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv. reflexivity.
Qed.

(* The entry state of run 1. *)
Lemma ph_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - POLL_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> YK11.getr regs 10 = w64 POLL_S ->
  st_ok_pi segs VAL (ph_E regs [w64 SHADOW_OFF]) ss_ph1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_poll)) mem (YK11.seg_rom segs))).
Proof using All.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16 H10.
  set (E := ph_E regs [w64 SHADOW_OFF]).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (exact (ph_ew_extra regs [w64 SHADOW_OFF] 0 ltac:(cbn; lia) ltac:(lia))).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs)
    by (unfold E; rewrite (ph_ew_reg regs [w64 SHADOW_OFF] 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 POLL_S)
    by (unfold E; rewrite (ph_ew_reg regs [w64 SHADOW_OFF] 10 10%bv eq_refl); exact H10).
  assert (U10 : bv_unsigned (ew E 10) = POLL_S)
    by (rewrite E10; apply unsigned_lit_small; ph_lia).
  destruct (ph_img_ok ly S W mem md E HCELLS HAR
    (ph_ew_obj regs [w64 SHADOW_OFF] 1 ltac:(lia)) (ph_ew_obj regs [w64 SHADOW_OFF] 95 ltac:(lia))
    (ph_ew_obj regs [w64 SHADOW_OFF] 0 ltac:(lia)) (ph_ew_obj regs [w64 SHADOW_OFF] 96 ltac:(lia)) E32)
    as [HRs HPd].
  destruct ph_vals_img as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  rewrite restrict_mkst_fx. unfold ss_ph1, ph_regions1.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold POLL_FRAME.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. unfold POLL_FRAME. lia.
  - unfold ph_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, ph_got_uar, ph_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (ph_ew_obj regs [w64 SHADOW_OFF] 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (ph_ew_obj regs [w64 SHADOW_OFF] 95 ltac:(lia)))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (ph_ew_obj regs [w64 SHADOW_OFF] 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) (ph_ew_obj regs [w64 SHADOW_OFF] 96 ltac:(lia)))
      by (rewrite V94; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94.
    unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, POLL_FRAME.
    repeat split; first [exact I | lia].
  - unfold ph_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, U10, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I;
      first [unfold SHADOW_OFF; lia | ph_lia | lia].
Qed.

(* The entry state of run 2, at +0x74. *)
Lemma ph_entry2 : forall (W : world segs) regs2 mem2 F sp1,
  YK11.getr regs2 2 = Z_to_bv 64 sp1 -> YK11.getr regs2 9 = Z_to_bv 64 sp1 ->
  YK11.getr regs2 10 = w64 F -> YK11.getr regs2 21 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 -> F + 2048 <= sp1 ->
  (F + 2048 <= kLowShadowBeg \/ kHighMemBeg <= F) ->
  (forall a, sp1 + 48 <= a < sp1 + 56 -> apresent (w_H W) mem2 a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem2 a) ->
  (forall j, 0 <= j < 4 -> apresent (w_H W) mem2 (SHADOW_OFF + F / 8 + j)) ->
  st_ok_pi segs VAL (ph_E regs2 [w64 SHADOW_OFF; w64 (SHADOW_OFF + F / 8)]) ss_ph2
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + PH_C2)) mem2 (YK11.seg_rom segs))).
Proof using All.
  intros W regs2 mem2 F sp1 R2 R9 R10 R21 Hsp Hsp32 HF0 HF64 HFc HFsp Happ Hpsl Hphd Hpsh.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (E := ph_E regs2 [w64 SHADOW_OFF; w64 (SHADOW_OFF + F / 8)]).
  assert (HQ0 : 0 <= F / 8) by (apply Z.div_pos; lia).
  assert (HQc : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  assert (E33 : ew E 33 = Z_to_bv 64 (SHADOW_OFF + F / 8)).
  { exact (ph_ew_extra regs2 [w64 SHADOW_OFF; w64 (SHADOW_OFF + F / 8)] 1 ltac:(cbn; lia) ltac:(lia)). }
  assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (unfold E; rewrite (ph_ew_reg regs2 _ 9 9%bv eq_refl); exact R9).
  assert (E2' : ew E 2 = Z_to_bv 64 sp1) by (unfold E; rewrite (ph_ew_reg regs2 _ 2 2%bv eq_refl); exact R2).
  assert (E10 : ew E 10 = Z_to_bv 64 F) by (unfold E; rewrite (ph_ew_reg regs2 _ 10 10%bv eq_refl); exact R10).
  assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E; rewrite (ph_ew_reg regs2 _ 21 21%bv eq_refl); exact R21).
  assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2'; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew E 10) = F) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite E21; apply unsigned_lit_small; ph_lia).
  assert (U33 : bv_unsigned (ew E 33) = SHADOW_OFF + F / 8) by (rewrite E33; apply unsigned_lit_small; ph_lia).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  rewrite restrict_mkst_fx. unfold ss_ph2, ph_regions2.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil;
    unfold ph_rg_hdr, ph_rg_fsh, ph_rg_fslot, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB 10%nat F E10 ltac:(lia)). split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hphd. lia.
    + rewrite (VB 33%nat (SHADOW_OFF + F / 8) E33 ltac:(ph_lia)).
      split; [ph_lia|]. split; [ph_lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + rewrite (VB 9%nat sp1 E9 ltac:(lia)). split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsl. lia.
  - apply pairwise_disjoint_of_extents.
    unfold ph_rg_hdr, ph_rg_fsh, ph_rg_fslot, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat F E10 ltac:(lia)), (VB 9%nat sp1 E9 ltac:(lia)),
      (VB 33%nat (SHADOW_OFF + F / 8) E33 ltac:(ph_lia)).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
    repeat split; first [exact I | lia].
  - unfold ph_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U21, U33.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end;
      try exact I; try reflexivity; try assumption; try ph_lia.
    unfold ph_alias2. cbn [alias_ok]. split; [|exact I].
    etransitivity;
    [ apply (denot_shx E 10 21 0 F SHADOW_OFF E10 E21 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ph_lia))
    | rewrite Z.add_0_r; symmetry; apply (ph_den E 33%nat (SHADOW_OFF + F / 8) E33 ltac:(ph_lia)) ].
Qed.

(* The entry state of run 3, at +0xf8. *)
Lemma ph_entry3 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 20 = w64 SH -> SHADOW_OFF <= SH -> SH + 212 <= 2 ^ 46 ->
  (forall a, SH + 194 <= a < SH + 212 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (ph_E regs []) ss_ph3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + PH_C3)) mem (YK11.seg_rom segs))).
Proof using All.
  intros W regs mem SH R20 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_ph3.
  assert (U20 : bv_unsigned (ew (ph_E regs []) 20) = SH)
    by (rewrite (ph_ew_reg regs [] 20 20%bv eq_refl), R20; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold ph_rg_rg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold ph_rg_rg, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold ph_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* g_s's shadow bytes are 0 (trans_poll_cells). *)
Lemma ph_gsh_zero : forall ly S (W : world segs) mem md j,
  trans_poll_cells B -> @AR rc segs B ly S W mem md -> 0 <= j < 2283 ->
  aview segs (w_H W) mem (PH_GSH + j) = Some 0.
Proof using All.
  intros ly S W mem md j HZ HAR Hj.
  assert (Hz := decode_zshadow_rd B ly S W mem md POLL_S (POLL_S + TW.SZ_g_s) (POLL_S + 8 * j) HAR
    ltac:(replace (POLL_S + 8 * j) with ((769736 + j) * 8) by ph_lia; apply Z_mod_mult)
    ltac:(lia) ltac:(ph_lia) HZ).
  replace (PH_GSH + j) with (FCells.shadow_addr (POLL_S + 8 * j)); [exact Hz|].
  unfold FCells.shadow_addr, FCells.ASAN_K, PH_GSH, SHADOW_OFF, POLL_S, TB_g_s.
  replace (6157888 + 8 * j) with ((769736 + j) * 8) by lia.
  rewrite Z.div_mul by lia. replace (6157888 / 8) with 769736 by reflexivity. lia.
Qed.

(* g_s's payload is a range of G. *)
Lemma ph_inG : forall a, POLL_S <= a < POLL_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof using All.
intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
split; [exact (TMAP_B_in_G TW.OFF_g_s TB_g_s TW.SZ_g_s TMAP_B_g_s)|].
unfold in_zr. cbn [fst snd]. unfold POLL_S in Ha. lia.
Qed.

(* The entry state of run 4, at +0x150. *)
Lemma ph_entry4 : forall ly S (W : world segs) regs4 mem4 md4 Bw SH sp1,
  trans_poll_cells B -> @AR rc segs B ly S W mem4 md4 ->
  tw_at TMAP_B (aview segs (w_H W) mem4) Bw ->
  YK11.getr regs4 2 = w64 sp1 -> YK11.getr regs4 9 = w64 sp1 ->
  YK11.getr regs4 19 = w64 POLL_S -> YK11.getr regs4 20 = w64 SH -> YK11.getr regs4 21 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  SHADOW_OFF <= SH -> SH + 194 <= 2 ^ 46 ->
  (SH + 194 <= PH_GSH + 8 \/ PH_GSH + 12 <= SH + 193) ->
  (forall a, SH + 193 <= a < SH + 194 -> apresent (w_H W) mem4 a) ->
  (forall a, sp1 + 8 <= a < sp1 + 32 -> apresent (w_H W) mem4 a) ->
  st_ok_pi segs VAL (ph_E regs4 (ph_vals4 Bw)) ss_ph4
    (restrict (w_H W) (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + PH_C4)) mem4 (YK11.seg_rom segs))).
Proof using All.
  intros ly S W regs4 mem4 md4 Bw SH sp1 HPC HAR Htw R2 R9 R19 R20 R21 Hsp Hsp32 HSH0 HSH1 HSHg Hpb Hpsl.
  set (E := ph_E regs4 (ph_vals4 Bw)).
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (ph_vals4 Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E; apply ph_ew_extra; [cbn; lia | lia]).
  pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
  pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
  cbn [Nat.add nth ph_vals4] in E33, E34, E35, E36.
  assert (E2' : ew E 2 = Z_to_bv 64 sp1) by (unfold E; rewrite (ph_ew_reg regs4 _ 2 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (unfold E; rewrite (ph_ew_reg regs4 _ 9 9%bv eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 POLL_S)
    by (unfold E; rewrite (ph_ew_reg regs4 _ 19 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = Z_to_bv 64 SH) by (unfold E; rewrite (ph_ew_reg regs4 _ 20 20%bv eq_refl); exact R20).
  assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E; rewrite (ph_ew_reg regs4 _ 21 21%bv eq_refl); exact R21).
  assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2'; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U19 : bv_unsigned (ew E 19) = POLL_S) by (rewrite E19; apply unsigned_lit_small; ph_lia).
  assert (U20 : bv_unsigned (ew E 20) = SH) by (rewrite E20; apply unsigned_lit_small; ph_lia).
  assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite E21; apply unsigned_lit_small; ph_lia).
  assert (U33 : bv_unsigned (ew E 33) = PH_GSH) by (rewrite E33; apply unsigned_lit_small; ph_lia).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  pose proof (TWL.u_at_range Bw PH_O_CTX 8) as RCX. pose proof (TWL.u_at_range Bw PH_O_RECV 8) as RRV.
  pose proof (TWL.u_at_range Bw PH_O_NOW 8) as RNW.
  rewrite restrict_mkst_fx. unfold ss_ph4, ph_regions4.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil;
    unfold ph_rg_b193, ph_rg_slots, ph_rg_gsh, ph_rg_gs, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB 20%nat SH E20 ltac:(ph_lia)). split; [ph_lia|]. split; [ph_lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpb. lia.
    + rewrite (VB 9%nat sp1 E9 ltac:(lia)). split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsl. lia.
    + rewrite (VB 33%nat PH_GSH E33 ltac:(ph_lia)).
      split; [ph_lia|]. split; [ph_lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o _) =>
        apply (chunk_ok_val segs E _ PH_GSH o 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |];
        apply YE2y.val_mem1_of_aview; apply (ph_gsh_zero ly S W mem4 md4 o HPC HAR ltac:(lia)) end.
    + rewrite (VB 19%nat POLL_S E19 ltac:(ph_lia)).
      split; [ph_lia|]. split; [ph_lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ POLL_S 64 8 (SOff 34 0) (TW.u_at Bw PH_O_CTX 8));
          [apply ph_den; [exact E34 | lia] | cbn; lia | cbn; lia |].
        exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 64 8 TMAP_B_ok Htw TMAP_B_g_s
          ltac:(lia) ltac:(ph_lia)).
      * apply (chunk_ok_val segs E _ POLL_S 80 8 (SOff 35 0) (TW.u_at Bw PH_O_RECV 8));
          [apply ph_den; [exact E35 | lia] | cbn; lia | cbn; lia |].
        exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 80 8 TMAP_B_ok Htw TMAP_B_g_s
          ltac:(lia) ltac:(ph_lia)).
      * apply (chunk_ok_val segs E _ POLL_S 88 8 (SOff 36 0) (TW.u_at Bw PH_O_NOW 8));
          [apply ph_den; [exact E36 | lia] | cbn; lia | cbn; lia |].
        exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 88 8 TMAP_B_ok Htw TMAP_B_g_s
          ltac:(lia) ltac:(ph_lia)).
  - apply pairwise_disjoint_of_extents.
    unfold ph_rg_b193, ph_rg_slots, ph_rg_gsh, ph_rg_gs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 20%nat SH E20 ltac:(ph_lia)), (VB 9%nat sp1 E9 ltac:(lia)),
      (VB 33%nat PH_GSH E33 ltac:(ph_lia)), (VB 19%nat POLL_S E19 ltac:(ph_lia)).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | ph_lia].
  - unfold ph_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U19, U20, U21, U33.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end;
      try exact I; try reflexivity; try assumption; try ph_lia.
    unfold ph_alias4. cbn [alias_ok]. split; [|exact I].
    etransitivity;
    [ apply (denot_shx E 19 21 0 POLL_S SHADOW_OFF E19 E21 ltac:(ph_lia) ltac:(lia) ltac:(ph_lia) ltac:(ph_lia))
    | rewrite Z.add_0_r; symmetry; apply (ph_den E 33%nat PH_GSH E33 ltac:(ph_lia)) ].
Qed.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac ph_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ph_reg: no match for" T; fail
  end.
(* A register whose symbolic value is its own atom n at the run's start, ew Ex n = v (EQ). *)
Ltac ph_kreg HS r EQ H :=
  lazymatch type of EQ with ew _ _ = ?v =>
    ph_reg HS r v H ltac:(cbn [sv_denot]; rewrite EQ, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) end.

(* The write right of run 1: the 160-byte frame below the entry sp (a byte of the call's own stack window), and the
   four read-only image regions. *)
Ltac ph_awr1 Usp :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; ph_lia | ph_lia] |];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; ph_lia |]);
  apply awr_ok_x_nil.

(* The write right of run 2: the frame's header and its shadow bytes (bytes of the own frame), the slot s1 + 48
   (the call's stack window). *)
Ltac ph_awr2 U10 U33 U9 pos Fv :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ POLL_CID pos);
  [ left; reflexivity
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U10 in Ha;
    left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes POLL_CID) with 2048; fold Fv; ph_lia |];
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ POLL_CID pos);
  [ left; reflexivity
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U33 in Ha;
    right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes POLL_CID / 8) with 256;
    unfold shadow_addr; fold Fv; ph_lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
    left; split; [unfold awr_byte; left; ph_lia | ph_lia] |];
  apply awr_ok_x_nil.

(* The write right of run 3: shadow bytes 194 .. 211 of the own frame. *)
Ltac ph_awr3 U20 pos Fv :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ POLL_CID pos);
  [ left; reflexivity
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20 in Ha;
    right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes POLL_CID / 8) with 256;
    unfold shadow_addr; fold Fv; ph_lia |];
  apply awr_ok_x_nil.

(* The write right of run 4: shadow byte 193 of the own frame, the slots s1 + 8 .. s1 + 32 (the call's stack window),
   and the two read-only regions of g_s and its shadow. *)
Ltac ph_awr4 U20 U9 pos Fv :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ POLL_CID pos);
  [ left; reflexivity
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20 in Ha;
    right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes POLL_CID / 8) with 256;
    unfold shadow_addr; fold Fv; ph_lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
    left; split; [unfold awr_byte; left; ph_lia | ph_lia] |];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; ph_lia |]);
  apply awr_ok_x_nil.

(* The kept bytes of one run of run 4's regions (their windows are PH_Z4), carried from mem4. *)
Ltac ph_chain4 K4 G4 U20 U9 Fv Sv Mem4 :=
  lazymatch goal with
  | HFrx : frame_of ?E ?rs (mrestrict (w_H ?Wx) ?mo) (mrestrict (w_H ?Wx) ?mn) |- _ =>
    lazymatch goal with
    | HGx : mem_grows (mrestrict (w_H Wx) mo) (mrestrict (w_H Wx) mn) |- _ =>
      let K2 := fresh "K2" in let G2 := fresh "G2" in let K3 := fresh "K3" in
      assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ PH_Z4 Fv Sv a ->
        aview segs (w_H Wx) mn a = aview segs (w_H Wx) mo a);
      [ let aa := fresh "aa" in let Haa := fresh "Haa" in let Hnn := fresh "Hnn" in
        intros aa Haa Hnn;
        apply (kept_of_frame E rs (w_H Wx) mo mn (PH_Z4 Fv Sv) HFrx); [| exact Haa | exact Hnn];
        let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in
        let x := fresh "x" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
        intros b wlo whi x Hin Hx; cbv beta;
        lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
        cbn [In] in Hin;
        repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
          rewrite ?U20, ?U9 in Hx; unfold PH_Z4; first [left; lia | right; lia] |]);
        destruct Hin
      | ];
      assert (G2 : forall a, apresent (w_H Wx) Mem4 a -> apresent (w_H Wx) mn a)
        by (let aa := fresh "aa" in let Haa := fresh "Haa" in
            intros aa Haa; exact (apresent_grows (w_H Wx) mo mn aa HGx (G4 aa Haa)));
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ PH_Z4 Fv Sv a ->
          aview segs (w_H Wx) mn a = aview segs (w_H Wx) Mem4 a)
        by (let aa := fresh "aa" in let Haa := fresh "Haa" in let Hnn := fresh "Hnn" in
            intros aa Haa Hnn; exact (eq_trans (K2 aa Haa Hnn) (K4 aa Haa Hnn)));
      clear K4 G4 K2; rename K3 into K4; rename G2 into G4
    end
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  repeat match goal with H : mem_grows _ _ |- _ => clear H end.

(* The cut handoff: what every cut of the head carries, at any memory mF that differs from the stack malloc's mem2
   only in PH_ZS and holds the two slots s1 + 8 and s1 + 16. *)
Lemma ph_cur : forall c pos S2 mem2 md2 mF mdF (sp1 : Z) (Bx : list byte),
  pw_rt B MT -> pw_ok B c ->
  sp1 = pw_sp1 c ->
  @AR rc segs B (cx_lyc c) S2 (cx_W c) mem2 md2 ->
  frames S2 = (POLL_CID, pos) :: frames (cx_Sc c) ->
  ablocks B (cx_lyc c) S2 = ablocks B (cx_lyc c) (cx_Sc c) ->
  mo_le MT (cx_Sc c) S2 0 ->
  acall_kept_g segs B TG.G_HARNESS_B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_W c) mem2
    (pw_SP c - POLL_STK) (pw_SP c) poll_wr ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H (cx_W c)) mem2) (pw_SP c - fst o) =
      Some (bv_unsigned (YK11.getr (cx_regs c) (Z_to_bv 5 (snd o))))) POLL_SAVED ->
  rdword (aview segs (w_H (cx_W c)) mem2) (pw_F c pos + POLL_FBYTES - 8) =
    Some (flag_addr (cx_lyc c) POLL_CID pos) ->
  tw_at TMAP_B (aview segs (w_H (cx_W c)) mem2) (cx_Bw c) ->
  pw_SP c - 176 <= sp1 <= pw_SP c - 160 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c)
    (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c) ((POLL_CID, pos) :: cx_own c) (cx_lyc c) S2 (cx_W c) mF mdF (cx_k c) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PH_ZS (pw_F c pos) sp1 a ->
     aview segs (w_H (cx_W c)) mF a = aview segs (w_H (cx_W c)) mem2 a) ->
  (forall a, apresent (w_H (cx_W c)) mem2 a -> apresent (w_H (cx_W c)) mF a) ->
  rdword (aview segs (w_H (cx_W c)) mF) (sp1 + 8) = Some (SHADOW_OFF + pw_F c pos / 8 + 4) ->
  rdword (aview segs (w_H (cx_W c)) mF) (sp1 + 16) = Some (pw_F c pos) ->
  Bx = cx_Bw c ->
  pw_cur B MT c pos (cx_lyc c) S2 (cx_W c) mF mdF Bx.
Proof using All.
intros c pos S2 mem2 md2 mF mdF sp1 Bx HRT HOK Esp1 HAR2 Hfrs2 Eab2 HMO KPT0 HSV2 HFL2 Htw2 Gsp1 HJF KA GA HS8 HS16
  EBx.
subst Bx.
pose proof HRT as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & FFL & HGX & _).
pose proof HOK as (HJ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _ & _ & Hgf & _ & _ & _ & _ & _ & _ & Hinv & _).
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (F := pw_F c pos) in *.
set (SP := pw_SP c) in *.
assert (Hin2 : In (POLL_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds segs B LAWS _ _ _ _ _ POLL_CID pos HAR2 Hin2) as (HF0 & HFc & HFapp).
change (fs_frame_bytes POLL_CID) with 2048 in HFc, HFapp.
assert (EF : frame_addr (cx_lyc c) POLL_CID pos = F) by reflexivity. rewrite EF in HF0, HFc, HFapp.
assert (HFimg : forall a, F <= a < F + 2048 -> ~ in_img segs a).
{ intros a Ha. apply (frm_img segs B LAWS _ _ _ _ _ POLL_CID pos a HAR2 Hin2).
  change (fs_frame_bytes POLL_CID) with 2048. rewrite EF. exact Ha. }
assert (HQ0 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HQc : F / 8 + 256 <= 2 ^ 44).
{ assert (Hd : (F + 2048) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  replace (F + 2048) with (F + 256 * 8) in Hd by lia. rewrite Z.div_add in Hd by lia.
  change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
assert (HappD : F + 2048 <= kLowShadowBeg \/ kHighMemBeg <= F)
  by (destruct HFapp as (_ & [Hx | [Hx _]]); [left; exact Hx | right; exact Hx]).
clear HFapp.
assert (Hspr : alloc_ceiling + POLL_STK <= SP /\ SP <= 2 ^ 47) by ph_lia.
assert (HZw : forall a, PH_ZS F sp1 a -> ~ inG TG.G_HARNESS_B a).
{ intros a Hz HaG. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX HaG) as Hl.
  unfold PH_ZS in Hz. destruct Hz as [Hz | [Hz | Hz]].
  - apply (HFimg a); [lia | exact (proj1 (HGX a HaG))].
  - ph_lia.
  - ph_lia. }
unfold pw_cur. rewrite <- Esp1. change (pw_SP c) with SP. change (pw_F c pos) with F.
refine (conj HJF (conj Hfrs2 (conj _ (conj eq_refl (conj HMO (conj _ (conj _ (conj _ (conj _ (conj _
  (conj _ (conj Hgf (conj Hinv eq_refl))))))))))))).
- rewrite Eab2. apply Permutation_refl.
- apply (dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B (cx_lyc c) (cx_Sc c) (cx_lyc c) S2 (cx_W c)
    (cx_memc c) (cx_mdc c) (cx_W c) mem2 md2 mem2 mF (SP - POLL_STK) SP POLL_CID pos F
    (flag_addr (cx_lyc c) POLL_CID pos) poll_wr (PH_ZS F sp1) HGX HAR HAR2 Hfrs2
    ltac:(intros bm Hbm; rewrite Eab2; exact Hbm) eq_refl eq_refl eq_refl FFL ltac:(ph_lia) ltac:(ph_lia));
    [| exact KPT0 | exact KA | exact GA].
  intros a Hz. unfold dkg_nf. unfold PH_ZS in Hz. destruct Hz as [Hz | [Hz | Hz]].
  + right; left; left. change (fs_frame_bytes POLL_CID) with 2048. lia.
  + right; left; right; left. change (fs_frame_bytes POLL_CID / 8) with 256. lia.
  + left. ph_lia.
- apply Forall_forall. intros o Hin. pose proof (proj1 (Forall_forall _ _) HSV2 o Hin) as Ho. cbv beta in Ho |- *.
  assert (Hor : 8 <= fst o <= 104).
  { unfold POLL_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  apply (YF0x.rdword_ext (aview segs (w_H (cx_W c)) mem2)); [|exact Ho].
  intros i Hi. apply KA; [ph_lia|].
  unfold PH_ZS. intros [Hx | [Hx | Hx]]; ph_lia.
- apply (YF0x.rdword_ext (aview segs (w_H (cx_W c)) mem2)); [|exact HFL2].
  intros i Hi. apply KA; [unfold POLL_FBYTES in Hi |- *; lia|].
  unfold PH_ZS, POLL_FBYTES. intros [Hx | [Hx | Hx]]; [lia | | ph_lia].
  destruct HappD as [Hx1 | Hx1]; ph_lia.
- exact HS8.
- exact HS16.
- apply (tw_kept TMAP_B (aview segs (w_H (cx_W c)) mem2)); [exact Htw2|].
  intros x Hx.
  assert (HxG : inG TG.G_HARNESS_B x).
  { destruct Hx as (o & b & n & Hinr & Hy). unfold inG. apply Exists_exists. exists (b, n).
    split; [exact (TMAP_B_in_G o b n Hinr) | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX HxG) as Hl.
  apply KA; [ph_lia | intros Hz; exact (HZw x Hz HxG)].
Qed.

(* The registers the cut rel reads, from their values. *)
Lemma ph_rg_base_intro : forall c pos (regsF : bvmap 5 word) sp1,
  sp1 = pw_sp1 c ->
  YK11.getr regsF 2 = w64 sp1 -> YK11.getr regsF 3 = w64 (as_gp B) -> YK11.getr regsF 4 = w64 (as_tp B) ->
  YK11.getr regsF 8 = w64 (pw_SP c) -> YK11.getr regsF 9 = w64 sp1 -> YK11.getr regsF 18 = w64 (pw_F c pos) ->
  pw_rg_base B c pos regsF.
Proof using All.
intros c pos regsF sp1 -> H2 H3 H4 H8 H9 H18. exact (conj H2 (conj H3 (conj H4 (conj H8 (conj H9 H18))))).
Qed.

(* The registers the cut now1 reads, from their values. *)
Lemma ph_rg_run_intro : forall c pos (regsF : bvmap 5 word),
  pw_rg_base B c pos regsF ->
  YK11.getr regsF 19 = w64 POLL_S -> YK11.getr regsF 20 = w64 (SHADOW_OFF + pw_F c pos / 8) ->
  YK11.getr regsF 21 = w64 PW_SH64 -> YK11.getr regsF 22 = w64 (POLL_S + 80) ->
  YK11.getr regsF 23 = w64 (POLL_S + 88) -> YK11.getr regsF 24 = w64 (POLL_S + 64) ->
  YK11.getr regsF 27 = w64 PW_SH80 -> pw_rg_run B c pos regsF.
Proof using All.
intros c pos regsF HB H19 H20 H21 H22 H23 H24 H27.
exact (conj HB (conj H19 (conj H20 (conj H21 (conj H22 (conj H23 (conj H24 H27))))))).
Qed.

(* What run 4 left at a cut state HS (valuation Ex, memory of msF): the slots s1 + 8 and s1 + 16. *)
Ltac ph_slots HS Ex Wx U9 EE22 EE23 Fv Sv R8 R16 S8 S16 :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  let RG1 := fresh "RG1" in
  pose proof (st_ok_pi_region_nth Ex _ _ 1 _ HS eq_refl) as RG1; cbn [ms_mem restrict] in RG1;
  assert (S8 : rdword (aview segs (w_H Wx) (ms_mem msF)) (Sv + 8) = Some (SHADOW_OFF + Fv / 8 + 4))
    by (apply (YF0x.val_mem_rdword (w_H Wx) (ms_mem msF) (Sv + 8) (SHADOW_OFF + Fv / 8 + 4) R8);
        apply (can_field_of_region Ex _ 9 Sv _ 8 32 8 32 8 8%N (SOff 23 0) (SHADOW_OFF + Fv / 8 + 4) RG1 U9);
        [ repeat (first [left; reflexivity | right]) | apply ph_den; [exact EE23 | exact R8]
        | exact R8 | cbn; lia ]);
  assert (S16 : rdword (aview segs (w_H Wx) (ms_mem msF)) (Sv + 16) = Some Fv)
    by (apply (YF0x.val_mem_rdword (w_H Wx) (ms_mem msF) (Sv + 16) Fv R16);
        apply (can_field_of_region Ex _ 9 Sv _ 8 32 8 32 16 8%N (SOff 22 0) Fv RG1 U9);
        [ repeat (first [left; reflexivity | right]) | apply ph_den; [exact EE22 | exact R16]
        | exact R16 | cbn; lia ]);
  clear RG1
  end.

(* The registers the cut rel reads, at a cut state HS of run 4. *)
Ltac ph_regs_rel HS EE2 EE3 EE4 EE8 EE9 EE18 V2 V3 V4 V8 V9 V18 V26 :=
  ph_kreg HS (2%bv : bv 5) EE2 V2; ph_kreg HS (3%bv : bv 5) EE3 V3; ph_kreg HS (4%bv : bv 5) EE4 V4;
  ph_kreg HS (8%bv : bv 5) EE8 V8; ph_kreg HS (9%bv : bv 5) EE9 V9; ph_kreg HS (18%bv : bv 5) EE18 V18;
  ph_reg HS (26%bv : bv 5) (w64 (-1)) V26
    ltac:(change (Z_to_bv 64 18446744073709551615 = w64 (-1)); unfold w64; apply Z_to_bv64_eq_mod; reflexivity).

Lemma pw_head_holds : @pw_head_stmt fx rc B MT.
Proof using All.
unfold pw_head_stmt. intros c NOW1 REL. unfold pw_entry. intros HRT HKP HOK.
destruct c as [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs w r TF Bw Bw'].
pose proof HRT as (HPCS & HCELLS & HPC & _ & _ & _ & _ & LAWS & MTL & MTF & SMP & FFL & HGX & HGN
  & ASM0 & ASF80 & ASF00 & _).
pose proof HOK as HOK'. unfold pw_ok, pw_SP in HOK'.
cbn [cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc cx_mdc cx_k cx_regs cx_w
  cx_r cx_TF cx_Bw cx_Bw'] in HOK'.
destruct HOK' as (HJ & Hra & Hra4 & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hwr & Htw & Hgf & Hm
  & _ & _ & _ & _ & _ & _ & _ & Hc5 & _).
pose (c := mkPW STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs w r TF Bw Bw').
pose proof (ASM0 fx) as ASM. pose proof (ASF80 fx) as ASF8. pose proof (ASF00 fx) as ASF0.
clear ASM0 ASF80 ASF00.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hspr : 2 ^ 46 <= spZ regs <= 2 ^ 47) by ph_lia.
assert (Hwin0 : forall a, spZ regs - POLL_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; ph_lia).
(* the realigned stack pointer *)
destruct (can_sp1_facts (spZ regs + -160) ltac:(ph_lia)
  ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
set (sp1 := 32 * ((spZ regs + -160) / 32)) in *.
assert (Esp1 : sp1 = 32 * ((spZ regs - POLL_FRAME) / 32)) by (unfold sp1; do 3 f_equal; ph_lia).
assert (Gsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by (clear - Hsp1r; lia).
(* run 1: the entry to the stack-malloc call *)
set (E0 := ph_E regs [w64 SHADOW_OFF]).
assert (HEI : img_env VAL A_LIM E0) by apply ph_env_img.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs)
  by (unfold E0; rewrite (ph_ew_reg regs [w64 SHADOW_OFF] 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF)
  by (exact (ph_ew_extra regs [w64 SHADOW_OFF] 0 ltac:(cbn; lia) ltac:(lia))).
pose proof (ph_entry1 lyc Sc W regs memc mdc HCELLS HAR ltac:(intros a Ha; apply Hpres0; ph_lia)
  Hspr Hsp16 H10) as HS. fold E0 in HS.
assert (SHOK : sh_ok segs (SOff 32 0) [] E0 (mrestrict (w_H W) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ _ _ ?Q =>
  change (SRr segs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_poll)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
paj_run_tok RUN HS HJ SHOK PH_B0.
{ ph_awr1 Usp. }
(* the thirteen saved words, read back from the stack region the run wrote *)
pose proof (st_ok_region_nth E0 _ _ 0 _ HS eq_refl) as HRsk. cbn [ms_mem restrict] in HRsk.
assert (HSV : forall o r0, In (o, r0) POLL_SAVED ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs - o) =
  Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 r0)))).
{ intros o r0 Hin.
  assert (Ho : 8 <= o <= 104 /\ 0 <= r0 <= 27).
  { unfold POLL_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
  assert (Er : Z.of_nat (Z.to_nat r0) = bv_unsigned (Z_to_bv 5 r0)).
  { rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
  apply (YF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs - o)
    (bv_unsigned (YK11.getr regs (Z_to_bv 5 r0)))
    ltac:(pose proof (bv_unsigned_in_range 64 (YK11.getr regs (Z_to_bv 5 r0))) as Hrg;
          unfold bv_modulus in Hrg; change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia)).
  replace (spZ regs - o) with (spZ regs + - o) by ring.
  apply (can_field_of_region E0 _ 2 (spZ regs) _ (-160) 0 (-160) 0 (- o) 8%N
    (SOff (Z.to_nat r0) 0) (bv_unsigned (YK11.getr regs (Z_to_bv 5 r0))) HRsk Usp);
  [ unfold POLL_SAVED in Hin; cbn [In] in Hin;
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add];
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; unfold E0;
    rewrite (ph_ew_reg regs [w64 SHADOW_OFF] (Z.to_nat r0) (Z_to_bv 5 r0) Er), Z.add_0_r, Z_to_bv_bv_unsigned;
    reflexivity
  | cbn; pose proof (bv_unsigned_in_range 64 (YK11.getr regs (Z_to_bv 5 r0))) as Hrg;
    unfold bv_modulus in Hrg; change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia
  | cbn; lia ]. }
(* the registers at the call *)
pmkst HS.
ph_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 39020)) R1 ltac:(apply codeptr_val; exact HEI).
ph_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 E0 2 (spZ regs) (-160)
    ltac:(unfold E0; rewrite (ph_ew_reg regs [w64 SHADOW_OFF] 2 2%bv eq_refl); unfold spZ;
          symmetry; apply Z_to_bv_bv_unsigned) ltac:(ph_lia) ltac:(ph_lia) ltac:(ph_lia))).
ph_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; unfold E0; rewrite (ph_ew_reg regs [w64 SHADOW_OFF] 3 3%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Hgp).
ph_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; unfold E0; rewrite (ph_ew_reg regs [w64 SHADOW_OFF] 4 4%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Htp).
ph_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
ph_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 E0 2 (spZ regs) (-160)
    ltac:(unfold E0; rewrite (ph_ew_reg regs [w64 SHADOW_OFF] 2 2%bv eq_refl); unfold spZ;
          symmetry; apply Z_to_bv_bv_unsigned) ltac:(ph_lia) ltac:(ph_lia) ltac:(ph_lia))).
ph_reg HS (19%bv : bv 5) (w64 POLL_S) R19
  ltac:(cbn [sv_denot]; unfold E0; rewrite (ph_ew_reg regs [w64 SHADOW_OFF] 10 10%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H10).
ph_reg HS (21%bv : bv 5) (w64 SHADOW_OFF) R21
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ph_reg HS (25%bv : bv 5) (w64 w) R25
  ltac:(cbn [sv_denot]; unfold E0; rewrite (ph_ew_reg regs [w64 SHADOW_OFF] 11 11%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H11).
(* +0x070: the class-5 stack malloc, at the pc the record names *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_stack_malloc_5)) mm rom) mdx) Q)
  end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  exact (@gx_stack_malloc_at fx rc tfib_sink_head segs B LAWS transportb_segs_low SMP POLL_CID ASM
    ltac:(ph_lia) TG.G_HARNESS_B W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 39020)) HJ
    ltac:(unfold spZ at 1; rewrite R2, unsigned_lit_small by ph_lia; lia)
    ltac:(rewrite Zminus_mod, Hsp1al16, Hsp0a; reflexivity)
    ltac:(ph_lia) ltac:(ph_lia) R3 R4 R1
    ltac:(apply (ret_ok_codeptr_v (PI := PI_transportb)); [ph_lia | reflexivity]) ltac:(lia)) end. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
set (F := frame_addr lyc POLL_CID pos) in *.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (POLL_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ POLL_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ POLL_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ POLL_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes POLL_CID / 8) with 256 in HFsh.
change (fs_frame_bytes POLL_CID) with 2048 in HFb, HFc, HFapp, Hflag, Hfpres, HFsh.
fold F in HFal, HFapp, HFb, HFsh, HF0, HFc, HF64, Hflag, Hfpres.
clear Hz Hnev2 HFal.
assert (HFq8 : 0 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | ph_lia]]).
assert (HappD : F + 2048 <= kLowShadowBeg \/ kHighMemBeg <= F)
  by (destruct HFapp as (_ & [Hx | [Hx _]]); [left; exact Hx | right; exact Hx]).
clear HFapp.
destruct HK1 as (K1a & K1b & K1c & K1d & K1e & K1f).
assert (Hpsl : forall a, sp1 <= a < sp1 + 56 -> apresent (w_H W) mem2 a).
{ intros a Ha. apply K1e.
  - ph_lia.
  - intros [Hx Hy]. ph_lia.
  - apply (apresent_grows (w_H W) memc (ms_mem ms) a HG). apply Hpres0. ph_lia. }
assert (HFimg : forall a, F <= a < F + 2048 -> ~ in_img segs a).
{ intros a Ha. apply (frm_img segs B LAWS _ _ _ _ _ POLL_CID pos a HAR2 Hin2).
  change (fs_frame_bytes POLL_CID) with 2048. fold F. exact Ha. }
(* g_s's payload and the frame are apart: a frame byte is not an image byte *)
assert (HFg : F + 2048 <= POLL_S \/ POLL_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 2048) POLL_S) as [Hx|Hx]; [left; exact Hx|].
  destruct (Z_le_gt_dec (POLL_S + TW.SZ_g_s) F) as [Hy|Hy]; [right; exact Hy|].
  exfalso. apply (HFimg (Z.max F POLL_S)); [ph_lia|].
  exact (proj1 (HGX (Z.max F POLL_S) (ph_inG (Z.max F POLL_S) ltac:(ph_lia)))). }
assert (HDJ : SHADOW_OFF + F / 8 + 194 <= PH_GSH + 8 \/ PH_GSH + 12 <= SHADOW_OFF + F / 8 + 193)
  by (destruct HFg as [Hx | Hx]; [left | right]; ph_lia).
clear HFg.
(* the saved words and the frame's flag word, kept by the call *)
assert (HSVF : Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem2) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) POLL_SAVED).
{ apply Forall_forall. intros [o r0] Hin. cbn [fst snd].
  assert (Ho : 8 <= o <= 104).
  { unfold POLL_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
  apply (YF0x.rdword_ext (aview segs (w_H W) (ms_mem ms))); [|exact (HSV o r0 Hin)].
  intros i Hi. apply K1a; ph_lia. }
assert (Q2 : YK11.getr regs2 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact R2]).
assert (Q3 : YK11.getr regs2 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]).
assert (Q4 : YK11.getr regs2 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]).
assert (Q8 : YK11.getr regs2 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]).
assert (Q9 : YK11.getr regs2 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]).
assert (Q19 : YK11.getr regs2 19 = w64 POLL_S)
  by (transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q21 : YK11.getr regs2 21 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact R21]).
assert (Q25 : YK11.getr regs2 25 = w64 w)
  by (transitivity (YK11.getr (ms_regs ms) 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact R25]).
(* run 1 wrote only the 160 bytes below the entry sp *)
assert (HG1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 160 <= a < spZ regs) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a).
{ intros a Ha Hn.
  apply (kept_of_frame E0 ph_regions1 (w_H W) memc (ms_mem ms)
    (fun x => spZ regs - 160 <= x < spZ regs) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. cbv beta.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
    rewrite ?Usp in Hx; ph_lia |]). destruct Hin. }
(* the world, carried through run 1 and the call *)
assert (HGK : gx_kept segs TG.G_HARNESS_B W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS_B W memc W (ms_mem ms) W mem2).
  - intros a HaG. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX HaG) as Hlow.
    apply HG1; ph_lia.
  - apply (gx_kept_of_acall_kept segs B TG.G_HARNESS_B lyc Sc W (ms_mem ms) W mem2
      (sp0 + (sp1 - sp0) - ESTACK) (sp0 + (sp1 - sp0)) (fun _ => False) HGX HGN).
    exact (conj K1a (conj K1b (conj K1c (conj K1d (conj K1e K1f))))). }
assert (Htw2 : tw_at TMAP_B (aview segs (w_H W) mem2) Bw)
  by (apply (tw_kept_GB (aview segs (w_H W) memc)); [exact Htw|];
      intros b n i Hbn Hi; apply HGK; unfold inG; apply Exists_exists; exists (b, n);
      split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
(* what the entry and the call keep of the caller's memory *)
assert (KPT0 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W mem2 (spZ regs - POLL_STK) (spZ regs) poll_wr).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W (ms_mem ms) W mem2
    (spZ regs - POLL_STK) (spZ regs) (sp0 + (sp1 - sp0) - ESTACK) (sp0 + (sp1 - sp0))
    poll_wr (fun _ => False)); [ph_lia | ph_lia | | | ph_lia | ph_lia | intros a [] ].
  - apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc (ms_mem ms)
      (spZ regs - POLL_STK) (spZ regs) poll_wr (fun a => spZ regs - 160 <= a < spZ regs) HAR).
    + apply dk_kept_refl_g. exact Hwin0.
    + intros a Ha Hn. apply HG1; [exact Ha | exact Hn].
    + intros a Hp. exact (apresent_grows (w_H W) memc (ms_mem ms) a HG Hp).
    + intros a Hz1 Hc1. ph_lia.
    + intros b m i Hb Hi Hz2. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4096 & Hbce & _). ph_lia.
    + intros a Hz3 Hi3 _ _. exfalso. pose proof (transportb_segs_low a Hi3). ph_lia.
    + intros c0 p0 a Hin Hr Hz4. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c0 p0 HAR Hin) as (G4096 & Gce & _).
      pose proof (fs_frame_bytes_nonneg c0) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [ph_lia|].
      pose proof (shadow_range_end (frame_addr lyc c0 p0) (fs_frame_bytes c0) Hfs) as Hse.
      assert (Hd : (frame_addr lyc c0 p0 + fs_frame_bytes c0) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc c0 p0) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr in Hr, Hse. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. ph_lia.
  - apply acall_kept_g_of. exact (conj K1a (conj K1b (conj K1c (conj K1d (conj K1e K1f))))). }
assert (HFL2 : rdword (aview segs (w_H W) mem2) (F + POLL_FBYTES - 8) = Some (flag_addr lyc POLL_CID pos))
  by (replace (F + POLL_FBYTES - 8) with (F + 2048 - 8) by ph_lia; exact Hflag).
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
(* what every cut carries, at any later memory that differs from mem2 only in PH_ZS *)
assert (HCUR : forall (mF : word -> option byte) (mdF : Model) (Bx : list byte),
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((POLL_CID, pos) :: own) lyc S2 W mF mdF k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PH_ZS F sp1 a -> aview segs (w_H W) mF a = aview segs (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mF a) ->
  rdword (aview segs (w_H W) mF) (sp1 + 8) = Some (SHADOW_OFF + F / 8 + 4) ->
  rdword (aview segs (w_H W) mF) (sp1 + 16) = Some F ->
  Bx = Bw ->
  pw_cur B MT c pos lyc S2 W mF mdF Bx).
{ intros mF mdF Bx HJF KA GA HS8 HS16 EBx.
  exact (ph_cur c pos S2 mem2 md2 mF mdF sp1 Bx HRT HOK Esp1 HAR2 Hfrs2 Eab2 HMO KPT0 HSVF HFL2 Htw2 Gsp1
    HJF KA GA HS8 HS16 EBx). }
clear HSV HG1 HF HFr HG K1a K1b K1c K1d K1e K1f Hflag Hfpres HP2 Hset2 HRsk R1 R2 R3 R4 R8 R9 R19 R21 R25.
clear HS SHOK. repeat match goal with H : img_env _ _ _ |- _ => clear H end.
clear dependent ms.
(* run 2: +0x74 .. `jal __asan_set_shadow_f8` *)
set (E1 := ph_E regs2 [w64 SHADOW_OFF; w64 (SHADOW_OFF + F / 8)]).
assert (HEI : img_env VAL A_LIM E1) by apply ph_env_img.
assert (SHOK : sh_ok segs (SOff 21 0) [] E1 (mrestrict (w_H W) mem2)) by (unfold sh_ok; apply Forall_nil).
pose proof (ph_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q21 ltac:(ph_lia) Hsp1al HF0 HF64 ltac:(ph_lia) ltac:(ph_lia)
  HappD ltac:(intros a Ha; apply Hpsl; lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros j Hj; replace (SHADOW_OFF + F / 8 + j) with (shadow_addr F + j) by reflexivity;
        exact (proj1 (HFsh j ltac:(lia))))) as HS.
fold E1 in HS.
assert (EE2 : ew E1 2 = Z_to_bv 64 sp1) by (unfold E1; rewrite (ph_ew_reg regs2 _ 2 2%bv eq_refl); exact Q2).
assert (EE3 : ew E1 3 = w64 (as_gp B)) by (unfold E1; rewrite (ph_ew_reg regs2 _ 3 3%bv eq_refl); exact Q3).
assert (EE4 : ew E1 4 = w64 (as_tp B)) by (unfold E1; rewrite (ph_ew_reg regs2 _ 4 4%bv eq_refl); exact Q4).
assert (EE8 : ew E1 8 = w64 (spZ regs)) by (unfold E1; rewrite (ph_ew_reg regs2 _ 8 8%bv eq_refl); exact Q8).
assert (EE9 : ew E1 9 = Z_to_bv 64 sp1) by (unfold E1; rewrite (ph_ew_reg regs2 _ 9 9%bv eq_refl); exact Q9).
assert (EE10 : ew E1 10 = w64 F) by (unfold E1; rewrite (ph_ew_reg regs2 _ 10 10%bv eq_refl); exact Ha0).
assert (EE19 : ew E1 19 = w64 POLL_S) by (unfold E1; rewrite (ph_ew_reg regs2 _ 19 19%bv eq_refl); exact Q19).
assert (EE21 : ew E1 21 = w64 SHADOW_OFF) by (unfold E1; rewrite (ph_ew_reg regs2 _ 21 21%bv eq_refl); exact Q21).
assert (EE25 : ew E1 25 = w64 w) by (unfold E1; rewrite (ph_ew_reg regs2 _ 25 25%bv eq_refl); exact Q25).
assert (EE33 : ew E1 33 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (exact (ph_ew_extra regs2 [w64 SHADOW_OFF; w64 (SHADOW_OFF + F / 8)] 1 ltac:(cbn; lia) ltac:(lia))).
assert (U10' : bv_unsigned (ew E1 10) = F) by (rewrite EE10; apply unsigned_lit_small; ph_lia).
assert (U9' : bv_unsigned (ew E1 9) = sp1) by (rewrite EE9; apply unsigned_lit_small; ph_lia).
assert (U33' : bv_unsigned (ew E1 33) = SHADOW_OFF + F / 8) by (rewrite EE33; apply unsigned_lit_small; ph_lia).
clear Q2 Q3 Q4 Q8 Q9 Q19 Q21 Q25 Ha0.
lazymatch goal with |- SRr _ _ _ ?Q =>
  change (SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + PH_C2)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
paj_run_tok RUN HS HJ2 SHOK PH_B0.
{ ph_awr2 U10' U33' U9' pos F. }
(* run 2 wrote the header, shadow bytes 0 .. 3 and the slot s1 + 48: bytes of PH_ZS *)
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ PH_ZS F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame E1 ph_regions2 (w_H W) mem2 (ms_mem ms) (PH_ZS F sp1) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. cbv beta.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
    rewrite ?U10', ?U33', ?U9' in Hx; unfold PH_ZS; ph_lia |]). destruct Hin. }
assert (GA2 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows (w_H W) mem2 (ms_mem ms) a HG Ha)).
clear HF HFr HG.
(* the registers at the call *)
ph_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 39152)) T1 ltac:(apply codeptr_val; exact HEI).
ph_kreg HS (2%bv : bv 5) EE2 T2. ph_kreg HS (3%bv : bv 5) EE3 T3. ph_kreg HS (4%bv : bv 5) EE4 T4.
ph_kreg HS (8%bv : bv 5) EE8 T8. ph_kreg HS (9%bv : bv 5) EE9 T9. ph_kreg HS (18%bv : bv 5) EE10 T18.
ph_kreg HS (19%bv : bv 5) EE19 T19. ph_kreg HS (20%bv : bv 5) EE33 T20. ph_kreg HS (21%bv : bv 5) EE21 T21.
ph_kreg HS (22%bv : bv 5) EE10 T22. ph_kreg HS (25%bv : bv 5) EE25 T25.
ph_reg HS (23%bv : bv 5) (w64 (SHADOW_OFF + F / 8 + 4)) T23
  ltac:(cbn [sv_denot]; rewrite EE33, unsigned_lit_small by ph_lia; reflexivity).
ph_reg HS (10%bv : bv 5) (w64 (SHADOW_OFF + F / 8 + 4)) T10
  ltac:(cbn [sv_denot]; rewrite EE33, unsigned_lit_small by ph_lia; reflexivity).
ph_reg HS (11%bv : bv 5) (w64 190) T11 ltac:(reflexivity).
(* +0x0f4: __asan_set_shadow_f8 (shadow bytes 4 .. 193 of the frame) *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_set_shadow_f8)) mm rom) mdx) Q)
  end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  exact (@gx_set_shadow_at fx rc tfib_sink_head segs B LAWS transportb_segs_low
    (transportb_sigma TB___asan_set_shadow_f8) 0xf8 ASF8 TG.G_HARNESS_B W rg mm STK sp0 FP ly S W0 mem0 md0
    ((POLL_CID, pos) :: own) lyc S2 mdx k (sp1 - sp0) (Z_to_bv 64 (BASE + 39152)) POLL_CID pos
    (SHADOW_OFF + F / 8 + 4) 190 HGX HJ2 (or_introl eq_refl) Hin2
    ltac:(unfold spZ at 1; rewrite T2, unsigned_lit_small by ph_lia; lia)
    ltac:(rewrite Zminus_mod, Hsp1al16, Hsp0a; reflexivity)
    ltac:(ph_lia) ltac:(ph_lia) T3 T4 T1
    ltac:(apply (ret_ok_codeptr_v (PI := PI_transportb)); [ph_lia | reflexivity])
    T10 T11 ltac:(lia) ltac:(unfold shadow_addr; fold F; lia)
    ltac:(change (fs_frame_bytes POLL_CID / 8) with 256; unfold shadow_addr; fold F; lia)) end. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hkeep3 & Hgr3).
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ PH_ZS F sp1 a ->
  aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite Hkeep3; [exact (K2 a Ha Hn) | exact Ha | |].
  - intros Hx. apply Hn. unfold PH_ZS. ph_lia.
  - intros Hx. apply Hn. unfold PH_ZS. ph_lia. }
assert (GA3 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a)
  by (intros a Ha; exact (Hgr3 a (GA2 a Ha))).
assert (P2 : YK11.getr regs3 2 = Z_to_bv 64 sp1) by exact (eq_trans (HP3 2 ltac:(hnf; lia)) T2).
assert (P3 : YK11.getr regs3 3 = w64 (as_gp B)) by exact (eq_trans (HP3 3 ltac:(hnf; lia)) T3).
assert (P4 : YK11.getr regs3 4 = w64 (as_tp B)) by exact (eq_trans (HP3 4 ltac:(hnf; lia)) T4).
assert (P8 : YK11.getr regs3 8 = w64 (spZ regs)) by exact (eq_trans (HP3 8 ltac:(hnf; lia)) T8).
assert (P9 : YK11.getr regs3 9 = Z_to_bv 64 sp1) by exact (eq_trans (HP3 9 ltac:(hnf; lia)) T9).
assert (P18 : YK11.getr regs3 18 = w64 F) by exact (eq_trans (HP3 18 ltac:(hnf; lia)) T18).
assert (P19 : YK11.getr regs3 19 = w64 POLL_S) by exact (eq_trans (HP3 19 ltac:(hnf; lia)) T19).
assert (P20 : YK11.getr regs3 20 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by exact (eq_trans (HP3 20 ltac:(hnf; lia)) T20).
assert (P21 : YK11.getr regs3 21 = w64 SHADOW_OFF) by exact (eq_trans (HP3 21 ltac:(hnf; lia)) T21).
assert (P22 : YK11.getr regs3 22 = w64 F) by exact (eq_trans (HP3 22 ltac:(hnf; lia)) T22).
assert (P23 : YK11.getr regs3 23 = w64 (SHADOW_OFF + F / 8 + 4)) by exact (eq_trans (HP3 23 ltac:(hnf; lia)) T23).
assert (P25 : YK11.getr regs3 25 = w64 w) by exact (eq_trans (HP3 25 ltac:(hnf; lia)) T25).
clear K2 GA2 Hkeep3 Hgr3 HP3 T1 T2 T3 T4 T8 T9 T10 T11 T18 T19 T20 T21 T22 T23 T25.
clear HS SHOK EE2 EE3 EE4 EE8 EE9 EE10 EE19 EE21 EE25 EE33 U10' U9' U33'.
repeat match goal with H : img_env _ _ _ |- _ => clear H end.
clear dependent ms.
(* run 3: +0xf8 .. `jal __asan_set_shadow_00` *)
set (E2 := ph_E regs3 []).
assert (HEI : img_env VAL A_LIM E2) by apply ph_env_img.
assert (SHOK : sh_ok segs (SOff 21 0) [] E2 (mrestrict (w_H W) mem3)) by (unfold sh_ok; apply Forall_nil).
pose proof (ph_entry3 W regs3 mem3 (SHADOW_OFF + F / 8) P20 ltac:(ph_lia) ltac:(ph_lia)
  ltac:(intros a Ha; apply GA3;
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
fold E2 in HS.
assert (FF2 : ew E2 2 = Z_to_bv 64 sp1) by (unfold E2; rewrite (ph_ew_reg regs3 _ 2 2%bv eq_refl); exact P2).
assert (FF3 : ew E2 3 = w64 (as_gp B)) by (unfold E2; rewrite (ph_ew_reg regs3 _ 3 3%bv eq_refl); exact P3).
assert (FF4 : ew E2 4 = w64 (as_tp B)) by (unfold E2; rewrite (ph_ew_reg regs3 _ 4 4%bv eq_refl); exact P4).
assert (FF8 : ew E2 8 = w64 (spZ regs)) by (unfold E2; rewrite (ph_ew_reg regs3 _ 8 8%bv eq_refl); exact P8).
assert (FF9 : ew E2 9 = Z_to_bv 64 sp1) by (unfold E2; rewrite (ph_ew_reg regs3 _ 9 9%bv eq_refl); exact P9).
assert (FF18 : ew E2 18 = w64 F) by (unfold E2; rewrite (ph_ew_reg regs3 _ 18 18%bv eq_refl); exact P18).
assert (FF19 : ew E2 19 = w64 POLL_S) by (unfold E2; rewrite (ph_ew_reg regs3 _ 19 19%bv eq_refl); exact P19).
assert (FF20 : ew E2 20 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (unfold E2; rewrite (ph_ew_reg regs3 _ 20 20%bv eq_refl); exact P20).
assert (FF21 : ew E2 21 = w64 SHADOW_OFF) by (unfold E2; rewrite (ph_ew_reg regs3 _ 21 21%bv eq_refl); exact P21).
assert (FF22 : ew E2 22 = w64 F) by (unfold E2; rewrite (ph_ew_reg regs3 _ 22 22%bv eq_refl); exact P22).
assert (FF23 : ew E2 23 = w64 (SHADOW_OFF + F / 8 + 4))
  by (unfold E2; rewrite (ph_ew_reg regs3 _ 23 23%bv eq_refl); exact P23).
assert (FF25 : ew E2 25 = w64 w) by (unfold E2; rewrite (ph_ew_reg regs3 _ 25 25%bv eq_refl); exact P25).
assert (U20b : bv_unsigned (ew E2 20) = SHADOW_OFF + F / 8) by (rewrite FF20; apply unsigned_lit_small; ph_lia).
clear P2 P3 P4 P8 P9 P18 P19 P20 P21 P22 P23 P25.
lazymatch goal with |- SRr _ _ _ ?Q =>
  change (SRr segs W (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + PH_C3)) mem3
    (YK11.seg_rom segs)) md3) Q) end.
paj_run_tok RUN HS HJ3 SHOK PH_B0.
{ ph_awr3 U20b pos F. }
assert (K3b : forall a, 0 <= a < 2 ^ 64 -> ~ PH_ZS F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite <- (K3 a Ha Hn).
  apply (kept_of_frame E2 [ph_rg_rg] (w_H W) mem3 (ms_mem ms) (PH_ZS F sp1) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. cbv beta.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
    rewrite ?U20b in Hx; unfold PH_ZS; ph_lia |]). destruct Hin. }
assert (GA3b : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows (w_H W) mem3 (ms_mem ms) a HG (GA3 a Ha))).
clear HF HFr HG K3 GA3.
ph_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 39240)) V1 ltac:(apply codeptr_val; exact HEI).
ph_kreg HS (2%bv : bv 5) FF2 V2. ph_kreg HS (3%bv : bv 5) FF3 V3. ph_kreg HS (4%bv : bv 5) FF4 V4.
ph_kreg HS (8%bv : bv 5) FF8 V8. ph_kreg HS (9%bv : bv 5) FF9 V9. ph_kreg HS (18%bv : bv 5) FF18 V18.
ph_kreg HS (19%bv : bv 5) FF19 V19. ph_kreg HS (20%bv : bv 5) FF20 V20. ph_kreg HS (21%bv : bv 5) FF21 V21.
ph_kreg HS (22%bv : bv 5) FF22 V22. ph_kreg HS (23%bv : bv 5) FF23 V23. ph_kreg HS (25%bv : bv 5) FF25 V25.
ph_kreg HS (10%bv : bv 5) FF23 V10.
ph_reg HS (11%bv : bv 5) (w64 189) V11 ltac:(reflexivity).
(* +0x14c: __asan_set_shadow_00 (shadow bytes 4 .. 192 of the frame) *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_set_shadow_00)) mm rom) mdx) Q)
  end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  exact (@gx_set_shadow_at fx rc tfib_sink_head segs B LAWS transportb_segs_low
    (transportb_sigma TB___asan_set_shadow_00) 0 ASF0 TG.G_HARNESS_B W rg mm STK sp0 FP ly S W0 mem0 md0
    ((POLL_CID, pos) :: own) lyc S2 mdx k (sp1 - sp0) (Z_to_bv 64 (BASE + 39240)) POLL_CID pos
    (SHADOW_OFF + F / 8 + 4) 189 HGX HJ3 (or_introl eq_refl) Hin2
    ltac:(unfold spZ at 1; rewrite V2, unsigned_lit_small by ph_lia; lia)
    ltac:(rewrite Zminus_mod, Hsp1al16, Hsp0a; reflexivity)
    ltac:(ph_lia) ltac:(ph_lia) V3 V4 V1
    ltac:(apply (ret_ok_codeptr_v (PI := PI_transportb)); [ph_lia | reflexivity])
    V10 V11 ltac:(lia) ltac:(unfold shadow_addr; fold F; lia)
    ltac:(change (fs_frame_bytes POLL_CID / 8) with 256; unfold shadow_addr; fold F; lia)) end. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfill4 & Hkeep4 & Hgr4).
assert (K4b : forall a, 0 <= a < 2 ^ 64 -> ~ PH_ZS F sp1 a ->
  aview segs (w_H W) mem4 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite Hkeep4; [exact (K3b a Ha Hn) | exact Ha | |].
  - intros Hx. apply Hn. unfold PH_ZS. ph_lia.
  - intros Hx. apply Hn. unfold PH_ZS. ph_lia. }
assert (GA4b : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem4 a)
  by (intros a Ha; exact (Hgr4 a (GA3b a Ha))).
assert (Z4 : forall i, 4 <= i < 193 -> aview segs (w_H W) mem4 (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. replace (SHADOW_OFF + F / 8 + i) with (SHADOW_OFF + F / 8 + 4 + (i - 4)) by lia.
  apply Hfill4. lia. }
assert (G2 : YK11.getr regs4 2 = Z_to_bv 64 sp1) by exact (eq_trans (HP4 2 ltac:(hnf; lia)) V2).
assert (G3 : YK11.getr regs4 3 = w64 (as_gp B)) by exact (eq_trans (HP4 3 ltac:(hnf; lia)) V3).
assert (G4 : YK11.getr regs4 4 = w64 (as_tp B)) by exact (eq_trans (HP4 4 ltac:(hnf; lia)) V4).
assert (G8 : YK11.getr regs4 8 = w64 (spZ regs)) by exact (eq_trans (HP4 8 ltac:(hnf; lia)) V8).
assert (G9 : YK11.getr regs4 9 = Z_to_bv 64 sp1) by exact (eq_trans (HP4 9 ltac:(hnf; lia)) V9).
assert (G18 : YK11.getr regs4 18 = w64 F) by exact (eq_trans (HP4 18 ltac:(hnf; lia)) V18).
assert (G19 : YK11.getr regs4 19 = w64 POLL_S) by exact (eq_trans (HP4 19 ltac:(hnf; lia)) V19).
assert (G20 : YK11.getr regs4 20 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by exact (eq_trans (HP4 20 ltac:(hnf; lia)) V20).
assert (G21 : YK11.getr regs4 21 = w64 SHADOW_OFF) by exact (eq_trans (HP4 21 ltac:(hnf; lia)) V21).
assert (G22 : YK11.getr regs4 22 = w64 F) by exact (eq_trans (HP4 22 ltac:(hnf; lia)) V22).
assert (G23 : YK11.getr regs4 23 = w64 (SHADOW_OFF + F / 8 + 4)) by exact (eq_trans (HP4 23 ltac:(hnf; lia)) V23).
assert (G25 : YK11.getr regs4 25 = w64 w) by exact (eq_trans (HP4 25 ltac:(hnf; lia)) V25).
clear K3b GA3b Hkeep4 Hgr4 Hfill4 HP4 V1 V2 V3 V4 V8 V9 V10 V11 V18 V19 V20 V21 V22 V23 V25.
clear HS SHOK FF2 FF3 FF4 FF8 FF9 FF18 FF19 FF20 FF21 FF22 FF23 FF25 U20b.
repeat match goal with H : img_env _ _ _ |- _ => clear H end.
clear dependent ms.
(* run 4: +0x150 .. the tests of :508-509 *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
assert (HZG : forall a, PH_ZS F sp1 a -> ~ inG TG.G_HARNESS_B a).
{ intros a Hz HaG. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX HaG) as Hl.
  unfold PH_ZS in Hz. destruct Hz as [Hz | [Hz | Hz]].
  - apply (HFimg a); [lia | exact (proj1 (HGX a HaG))].
  - ph_lia.
  - ph_lia. }
assert (Htw4 : tw_at TMAP_B (aview segs (w_H W) mem4) Bw).
{ apply (tw_kept TMAP_B (aview segs (w_H W) mem2)); [exact Htw2|].
  intros x Hx.
  assert (HxG : inG TG.G_HARNESS_B x).
  { destruct Hx as (o & b & n & Hinr & Hy). unfold inG. apply Exists_exists. exists (b, n).
    split; [exact (TMAP_B_in_G o b n Hinr) | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX HxG) as Hl.
  apply K4b; [ph_lia | intros Hz; exact (HZG x Hz HxG)]. }
set (E3 := ph_E regs4 (ph_vals4 Bw)).
assert (HEI : img_env VAL A_LIM E3) by apply ph_env_img.
assert (SHOK : sh_ok segs (SOff 21 0) [] E3 (mrestrict (w_H W) mem4)) by (unfold sh_ok; apply Forall_nil).
pose proof (ph_entry4 lyc S2 W regs4 mem4 md4 Bw (SHADOW_OFF + F / 8) sp1 HPC HAR4 Htw4 G2 G9 G19 G20 G21
  ltac:(ph_lia) Hsp1al ltac:(ph_lia) ltac:(ph_lia) HDJ
  ltac:(intros a Ha; apply GA4b;
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))
  ltac:(intros a Ha; apply GA4b; apply Hpsl; lia)) as HS.
fold E3 in HS.
assert (EX : forall j, (j < 5)%nat -> ew E3 (32 + j) = nth j (ph_vals4 Bw) (Z_to_bv 64 0))
  by (intros j Hj; unfold E3; apply ph_ew_extra; [cbn; lia | lia]).
pose proof (EX 3%nat ltac:(lia)) as H35. pose proof (EX 4%nat ltac:(lia)) as H36.
cbn [Nat.add nth ph_vals4] in H35, H36. clear EX.
assert (H2' : ew E3 2 = Z_to_bv 64 sp1) by (unfold E3; rewrite (ph_ew_reg regs4 _ 2 2%bv eq_refl); exact G2).
assert (H3' : ew E3 3 = w64 (as_gp B)) by (unfold E3; rewrite (ph_ew_reg regs4 _ 3 3%bv eq_refl); exact G3).
assert (H4' : ew E3 4 = w64 (as_tp B)) by (unfold E3; rewrite (ph_ew_reg regs4 _ 4 4%bv eq_refl); exact G4).
assert (H8' : ew E3 8 = w64 (spZ regs)) by (unfold E3; rewrite (ph_ew_reg regs4 _ 8 8%bv eq_refl); exact G8).
assert (H9' : ew E3 9 = Z_to_bv 64 sp1) by (unfold E3; rewrite (ph_ew_reg regs4 _ 9 9%bv eq_refl); exact G9).
assert (H18' : ew E3 18 = w64 F) by (unfold E3; rewrite (ph_ew_reg regs4 _ 18 18%bv eq_refl); exact G18).
assert (H19' : ew E3 19 = w64 POLL_S) by (unfold E3; rewrite (ph_ew_reg regs4 _ 19 19%bv eq_refl); exact G19).
assert (H20' : ew E3 20 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (unfold E3; rewrite (ph_ew_reg regs4 _ 20 20%bv eq_refl); exact G20).
assert (H21' : ew E3 21 = w64 SHADOW_OFF) by (unfold E3; rewrite (ph_ew_reg regs4 _ 21 21%bv eq_refl); exact G21).
assert (H22' : ew E3 22 = w64 F) by (unfold E3; rewrite (ph_ew_reg regs4 _ 22 22%bv eq_refl); exact G22).
assert (H23' : ew E3 23 = w64 (SHADOW_OFF + F / 8 + 4))
  by (unfold E3; rewrite (ph_ew_reg regs4 _ 23 23%bv eq_refl); exact G23).
assert (H25' : ew E3 25 = w64 w) by (unfold E3; rewrite (ph_ew_reg regs4 _ 25 25%bv eq_refl); exact G25).
assert (U20c : bv_unsigned (ew E3 20) = SHADOW_OFF + F / 8) by (rewrite H20'; apply unsigned_lit_small; ph_lia).
assert (U9c : bv_unsigned (ew E3 9) = sp1) by (rewrite H9'; apply unsigned_lit_small; ph_lia).
clear G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G25.
assert (RG8 : 0 <= SHADOW_OFF + F / 8 + 4 < 2 ^ 64) by ph_lia.
assert (RG16 : 0 <= F < 2 ^ 64) by ph_lia.
(* a cut of run 4: what it carries, from the kept bytes since mem4 *)
assert (KCUT : forall mF : word -> option byte,
  (forall a, 0 <= a < 2 ^ 64 -> ~ PH_Z4 F sp1 a -> aview segs (w_H W) mF a = aview segs (w_H W) mem4 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ PH_ZS F sp1 a -> aview segs (w_H W) mF a = aview segs (w_H W) mem2 a).
{ intros mF KF a Ha Hn. rewrite KF; [exact (K4b a Ha Hn) | exact Ha |].
  intros Hz. apply Hn. unfold PH_Z4 in Hz. unfold PH_ZS. ph_lia. }
(* the release exit (:508-509): a NULL pointer, the model's DIGINET_E_ARG with the world unchanged *)
assert (RELCLOSE : forall (mF : word -> option byte) (mdF : Model) (regsF : bvmap 5 word),
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((POLL_CID, pos) :: own) lyc S2 W mF mdF k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PH_Z4 F sp1 a -> aview segs (w_H W) mF a = aview segs (w_H W) mem4 a) ->
  (forall a, apresent (w_H W) mem4 a -> apresent (w_H W) mF a) ->
  rdword (aview segs (w_H W) mF) (sp1 + 8) = Some (SHADOW_OFF + F / 8 + 4) ->
  rdword (aview segs (w_H W) mF) (sp1 + 16) = Some F ->
  (TW.S_io_recv Bw = 0 \/ TW.S_io_now_us Bw = 0) ->
  YK11.getr regsF 2 = Z_to_bv 64 sp1 -> YK11.getr regsF 3 = w64 (as_gp B) -> YK11.getr regsF 4 = w64 (as_tp B) ->
  YK11.getr regsF 8 = w64 (spZ regs) -> YK11.getr regsF 9 = Z_to_bv 64 sp1 -> YK11.getr regsF 18 = w64 F ->
  YK11.getr regsF 26 = w64 (-1) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 (BASE + PW_REL)) mF (YK11.seg_rom segs)) mdF)
    (pw_post B MT c)).
{ intros mF mdF regsF HJF KF GF HS8 HS16 HNULL V2 V3 V4 V8 V9 V18 V26.
  destruct (pw_m_arg timg_B TF Bw w Bw' r Hm HNULL) as [EBw Er].
  pose proof (HCUR mF mdF Bw' HJF (KCUT mF KF) (fun a Ha => GF a (GA4b a Ha)) HS8 HS16 EBw) as CUR.
  refine (REL HRT HOK pos lyc S2 W mF mdF regsF CUR
    (ph_rg_base_intro c pos regsF sp1 Esp1 V2 V3 V4 V8 V9 V18) _).
  cbn [cx_r]. rewrite Er. exact V26. }
(* the now1 exit: both pointers set *)
assert (NOWCLOSE : forall (mF : word -> option byte) (mdF : Model) (regsF : bvmap 5 word),
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((POLL_CID, pos) :: own) lyc S2 W mF mdF k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PH_Z4 F sp1 a -> aview segs (w_H W) mF a = aview segs (w_H W) mem4 a) ->
  (forall a, apresent (w_H W) mem4 a -> apresent (w_H W) mF a) ->
  rdword (aview segs (w_H W) mF) (sp1 + 8) = Some (SHADOW_OFF + F / 8 + 4) ->
  rdword (aview segs (w_H W) mF) (sp1 + 16) = Some F ->
  aview segs (w_H W) mF (SHADOW_OFF + F / 8 + 193) = Some 2 ->
  rdword (aview segs (w_H W) mF) (sp1 + 24) = Some PW_SH88 ->
  TW.S_io_recv Bw <> 0 -> TW.S_io_now_us Bw <> 0 ->
  YK11.getr regsF 2 = Z_to_bv 64 sp1 -> YK11.getr regsF 3 = w64 (as_gp B) -> YK11.getr regsF 4 = w64 (as_tp B) ->
  YK11.getr regsF 8 = w64 (spZ regs) -> YK11.getr regsF 9 = Z_to_bv 64 sp1 -> YK11.getr regsF 18 = w64 F ->
  YK11.getr regsF 19 = w64 POLL_S -> YK11.getr regsF 20 = Z_to_bv 64 (SHADOW_OFF + F / 8) ->
  YK11.getr regsF 21 = w64 PW_SH64 -> YK11.getr regsF 22 = w64 (POLL_S + 80) ->
  YK11.getr regsF 23 = w64 (POLL_S + 88) -> YK11.getr regsF 24 = w64 (POLL_S + 64) ->
  YK11.getr regsF 27 = w64 PW_SH80 -> YK11.getr regsF 25 = w64 w ->
  YK11.getr regsF 11 = w64 (TW.S_io_now_us Bw) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 (BASE + PW_NOW1)) mF (YK11.seg_rom segs)) mdF)
    (pw_post B MT c)).
{ intros mF mdF regsF HJF KF GF HS8 HS16 H193 HS24 Hrv Hnw V2 V3 V4 V8 V9 V18 V19 V20 V21 V22 V23 V24 V27 V25 V11.
  pose proof (HCUR mF mdF Bw HJF (KCUT mF KF) (fun a Ha => GF a (GA4b a Ha)) HS8 HS16 eq_refl) as CUR.
  assert (ZF : forall i, 4 <= i < 193 -> aview segs (w_H W) mF (SHADOW_OFF + F / 8 + i) = Some 0).
  { intros i Hi. rewrite KF; [exact (Z4 i Hi) | ph_lia |]. unfold PH_Z4. ph_lia. }
  refine (NOW1 HRT HKP HOK pos lyc S2 W mF mdF regsF (conj CUR (conj ZF (conj H193 HS24)))
    (ph_rg_run_intro c pos regsF (ph_rg_base_intro c pos regsF sp1 Esp1 V2 V3 V4 V8 V9 V18)
      V19 V20 V21 V22 V23 V24 V27) V25 V11 Hrv Hnw). }
clear HCUR KCUT Z4.
(* run 4 to the first test (io.recv) *)
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ PH_Z4 F sp1 a -> aview segs (w_H W) mem4 a = aview segs (w_H W) mem4 a)
  by (intros; reflexivity).
assert (GA4 : forall a, apresent (w_H W) mem4 a -> apresent (w_H W) mem4 a) by (intros a Ha; exact Ha).
lazymatch goal with |- SRr _ _ _ ?Q =>
  change (SRr segs W (mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + PH_C4)) mem4
    (YK11.seg_rom segs)) md4) Q) end.
paj_run_tok RUN HS HJ4 SHOK PH_B0.
{ ph_awr4 U20c U9c pos F. }
ph_chain4 K4 GA4 U20c U9c F sp1 mem4.
psrr_branch_tok RUN BR HS SHOK PH_B0.
- (* io.recv = NULL: the release cut *)
  rewrite (ph_br_eq64 E3 Bw 35 PH_O_RECV H35) in Hc. apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ4 SHOK PH_B0 PW_REL.
  { ph_awr4 U20c U9c pos F. }
  ph_chain4 K4 GA4 U20c U9c F sp1 mem4.
  ph_slots HS E3 W U9c H22' H23' F sp1 RG8 RG16 S8 S16.
  ph_regs_rel HS H2' H3' H4' H8' H9' H18' V2 V3 V4 V8 V9 V18 V26.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + PW_REL)) mm rom) mdx) Q) end.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    exact (RELCLOSE mm mdx rg HJ4 K4 GA4 S8 S16 (or_introl (eq_trans (ph_recv_eq Bw) Hc))
      V2 V3 V4 V8 V9 V18 V26) end.
- rewrite (ph_br_eq64 E3 Bw 35 PH_O_RECV H35) in Hc. apply Z.eqb_neq in Hc.
  assert (Hrv : TW.S_io_recv Bw <> 0) by (rewrite ph_recv_eq; exact Hc). clear Hc.
  paj_run_tok RUN HS HJ4 SHOK PH_B0.
  { ph_awr4 U20c U9c pos F. }
  ph_chain4 K4 GA4 U20c U9c F sp1 mem4.
  psrr_branch_tok RUN BR HS SHOK PH_B0.
  + (* io.now_us = NULL: the release cut *)
    rewrite (ph_br_eq64 E3 Bw 36 PH_O_NOW H36) in Hc. apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ4 SHOK PH_B0 PW_REL.
    { ph_awr4 U20c U9c pos F. }
    ph_chain4 K4 GA4 U20c U9c F sp1 mem4.
    ph_slots HS E3 W U9c H22' H23' F sp1 RG8 RG16 S8 S16.
    ph_regs_rel HS H2' H3' H4' H8' H9' H18' V2 V3 V4 V8 V9 V18 V26.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + PW_REL)) mm rom) mdx) Q) end.
    lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      exact (RELCLOSE mm mdx rg HJ4 K4 GA4 S8 S16 (or_intror (eq_trans (ph_now_eq Bw) Hc))
        V2 V3 V4 V8 V9 V18 V26) end.
  + rewrite (ph_br_eq64 E3 Bw 36 PH_O_NOW H36) in Hc. apply Z.eqb_neq in Hc.
    assert (Hnw : TW.S_io_now_us Bw <> 0) by (rewrite ph_now_eq; exact Hc). clear Hc.
    paj_run_to_tok RUNTO HS HJ4 SHOK PH_B0 PW_NOW1.
    { ph_awr4 U20c U9c pos F. }
    ph_chain4 K4 GA4 U20c U9c F sp1 mem4.
    ph_slots HS E3 W U9c H22' H23' F sp1 RG8 RG16 S8 S16.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    pose proof (st_ok_pi_region_nth E3 _ _ 0 _ HS eq_refl) as RG0; cbn [ms_mem restrict] in RG0;
    pose proof (st_ok_pi_region_nth E3 _ _ 1 _ HS eq_refl) as RG1; cbn [ms_mem restrict] in RG1;
    assert (H193 : aview segs (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + 193) = Some 2)
      by (apply ph_aview_of_val1; [| lia];
          exact (can_field_of_region E3 _ 20 (SHADOW_OFF + F / 8) _ 193 194 193 194 193 1%N (SLit 2) 2 RG0 U20c
            ltac:(repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)));
    assert (HS24 : rdword (aview segs (w_H W) (ms_mem msF)) (sp1 + 24) = Some PW_SH88)
      by (apply (YF0x.val_mem_rdword (w_H W) (ms_mem msF) (sp1 + 24) PW_SH88 ltac:(ph_lia));
          apply (can_field_of_region E3 _ 9 sp1 _ 8 32 8 32 24 8%N
            (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 88) (SLit 3)) (SOff 21 0)) PW_SH88 RG1 U9c);
          [ repeat (first [left; reflexivity | right])
          | exact (denot_shx E3 19 21 88 POLL_S SHADOW_OFF H19' H21' ltac:(ph_lia) ltac:(lia) ltac:(ph_lia)
              ltac:(ph_lia))
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); ph_lia | cbn; lia ])
    end.
    clear RG0 RG1.
    ph_regs_rel HS H2' H3' H4' H8' H9' H18' V2 V3 V4 V8 V9 V18 V26.
    ph_kreg HS (19%bv : bv 5) H19' V19. ph_kreg HS (20%bv : bv 5) H20' V20. ph_kreg HS (25%bv : bv 5) H25' V25.
    ph_reg HS (21%bv : bv 5) (w64 PW_SH64) V21
      ltac:(exact (denot_shx E3 19 21 64 POLL_S SHADOW_OFF H19' H21' ltac:(ph_lia) ltac:(lia) ltac:(ph_lia)
              ltac:(ph_lia))).
    ph_reg HS (27%bv : bv 5) (w64 PW_SH80) V27
      ltac:(exact (denot_shx E3 19 21 80 POLL_S SHADOW_OFF H19' H21' ltac:(ph_lia) ltac:(lia) ltac:(ph_lia)
              ltac:(ph_lia))).
    ph_reg HS (22%bv : bv 5) (w64 (POLL_S + 80)) V22
      ltac:(cbn [sv_denot]; rewrite H19', unsigned_lit_small by ph_lia; reflexivity).
    ph_reg HS (23%bv : bv 5) (w64 (POLL_S + 88)) V23
      ltac:(cbn [sv_denot]; rewrite H19', unsigned_lit_small by ph_lia; reflexivity).
    ph_reg HS (24%bv : bv 5) (w64 (POLL_S + 64)) V24
      ltac:(cbn [sv_denot]; rewrite H19', unsigned_lit_small by ph_lia; reflexivity).
    ph_reg HS (11%bv : bv 5) (w64 (TW.S_io_now_us Bw)) V11
      ltac:(rewrite ph_now_eq; exact (ph_den E3 36 _ H36 (TWL.u_at_range Bw PH_O_NOW 8))).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + PW_NOW1)) mm rom) mdx) Q) end.
    lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      exact (NOWCLOSE mm mdx rg HJ4 K4 GA4 S8 S16 H193 HS24 Hrv Hnw
        V2 V3 V4 V8 V9 V18 V19 V20 V21 V22 V23 V24 V27 V25 V11) end.
Qed.

End s.

Theorem pw_head_piece : forall fx rc B MT, @pw_head_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@pw_head_holds fx rc B MT). Qed.
