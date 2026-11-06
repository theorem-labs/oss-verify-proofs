(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 311 of its 378 lines of code are new or changed and 492 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxArmKit.v, with its module paths and module names changed; 315 of its 432 lines of code are new or changed and 261 lines of the source are left out. *)
(* SrxBCallKit: image B's twin of lib/A/Prog/SrxCallKit.v, the lemmas the ack, lost and tick pieces of
   diginet_session_rx's image-B walk share (SrxBAck.v, SrxBLost.v, SrxBTick.v; the cut interface is SrxBCut.v). Each
   piece runs from its cut to a `jal` of a G-form callee (on_ack, set_state, diginet_session_tick), applies the
   callee's contract in the walk's own G journal while the class-1 frame is live, and runs the `j` after the call to
   the next cut. The kit, at image B's names (lib/B/TransportGB.v G_HARNESS_B, lib/B/Prog/TWorldB.v TMAP_B, the B
   statements' written ranges):
   - srxbk_entry: the symbolic state at a cut pc with no region (the registers as atoms, no fact);
   - srxbk_mem_eq: a run from a state with no region stores nothing (its frame_of over no region is the identity),
     so the memory after it is the memory before it;
   - srxbk_*_wr_G: every byte the three callees may store is a byte of G, field by field (srxbk_G decomposes a
     written range down to its twb_fld rows; notice's by lib/B/Prog/TransportGNoticeB.v notice_wr_G);
   - srxbk_tf_win: the current heap frame at a smaller window inside the walk's; srxbk_tf_step and srxbk_rom_step:
     the heap frame and the read-only bytes after a run of the walk's own that stores bytes of G only; srxbk_tf_kept
     and srxbk_rom_kept: the same after a G-form callee (its acall_kept_g; its written range is G and misses TF);
   - srxbk_cur_step: the cut's srxb_cur after a run of the walk's own that stores bytes of srx_wr in G only;
     srxbk_cur_call: srxb_cur after a G-form callee called with the frame live (the callee's acall_kept_g folded into
     the walk's by TransportGCg.v dk_kept_trans_nf_g; the 13 saved words above the realigned sp and the frame's last
     word kept, since the callee writes only bytes of G);
   - the stack arithmetic of the realigned sp (srxbk_sp1, srxbk_stk_le, srxbk_ceil) and the frame counts at the call
     state (srxbk_count). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import set_state_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_rx_cg SrxBCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TGNB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.TransportGNoticeB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model: the switch's result and the tick                      *)
(* ------------------------------------------------------------------ *)

Lemma srxbk_after : forall I F Bs b now B2, srx_sw I F Bs b now = Some (B2, tt) ->
  srxb_after I F Bs b now = TSS.diginet_session_tick_m I F B2 now.
Proof. intros I F Bs b now B2 H. unfold srxb_after. rewrite H. reflexivity. Qed.

Lemma srxbk_after_none : forall I F Bs b now, srx_sw I F Bs b now = None -> srxb_after I F Bs b now = None.
Proof. intros I F Bs b now H. unfold srxb_after. rewrite H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 2. The written ranges lie in G                                      *)
(* ------------------------------------------------------------------ *)

(* A field of a world row lies in that row's global, a byte of G. *)
Lemma srxbk_row : forall o b n A w a, In (o, b, n) TMAP_B -> o <= A -> A + w <= o + n -> twb_fld o b A w a ->
  inG TG.G_HARNESS_B a.
Proof.
  intros o b n A w a Hin H1 H2 Ha. unfold inG. apply Exists_exists. exists (b, n).
  split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr, twb_fld in *; cbn [fst snd]; lia].
Qed.

(* The bounds of a field inside its row: closed ones computed, indexed ones by lia over the index's bound. *)
Ltac srxbk_num :=
  first
    [ apply Z.leb_le; reflexivity
    | unfold TW.A_GOT_t_state, TW.GOT_t_ESZ, TW.OFF_GOT, TW.SZ_GOT, TC.TRANS_MAX, TW.A_Cmd_st, TW.OFF_g_cmd,
        TW.SZ_g_cmd, TC.CMDS_MAX, TW.A_M_fly_frame, TW.OFF_M, TW.SZ_M, TC.SPEC_MAX_FRAME, TW.A_S_queue_bytes,
        TW.S_queue_ESZ, TW.S_queue_N, TW.OFF_g_s, TW.SZ_g_s in *; lia ].

Ltac srxbk_rowG row H := refine (srxbk_row _ _ _ _ _ _ row _ _ H); srxbk_num.

Ltac srxbk_anyrow H :=
  first
    [ srxbk_rowG TMAP_B_g_s H | srxbk_rowG TMAP_B_M H | srxbk_rowG TMAP_B_GOT H | srxbk_rowG TMAP_B_g_cmd H
    | srxbk_rowG TMAP_B_g_q H | srxbk_rowG TMAP_B_g_nq H | srxbk_rowG TMAP_B_g_fail_next H
    | srxbk_rowG TMAP_B_g_last_counter H ].

(* A written range, down to its rows: disjunctions split, guards kept in the context, each row a field of G. *)
Ltac srxbk_G H :=
  lazymatch type of H with
  | _ \/ _ => let H1 := fresh "Hw" in let H2 := fresh "Hw" in destruct H as [H1 | H2]; [srxbk_G H1 | srxbk_G H2]
  | _ /\ _ => let H1 := fresh "Hg" in let H2 := fresh "Hw" in destruct H as [H1 H2]; srxbk_G H2
  | exists _, _ => let x := fresh "x" in let H1 := fresh "Hw" in destruct H as [x H1]; srxbk_G H1
  | twb_fld _ _ _ _ _ => srxbk_anyrow H
  | _ => fail "srxbk_G: no row for" H
  end.

Lemma srxbk_nwr_G : forall Bw n a, notice_wr Bw n a -> inG TG.G_HARNESS_B a.
Proof. exact TGNB.notice_wr_G. Qed.

Lemma srxbk_iosend_wr_G : forall n a, iosend_wr n a -> inG TG.G_HARNESS_B a.
Proof. intros n a H. unfold iosend_wr in H. srxbk_G H. Qed.

Lemma srxbk_senddata_wr_G : forall a, senddata_wr a -> inG TG.G_HARNESS_B a.
Proof.
  intros a H. unfold senddata_wr in H.
  destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]];
    [srxbk_G H | srxbk_G H | srxbk_G H | srxbk_G H | srxbk_G H | srxbk_G H | srxbk_G H | srxbk_G H | srxbk_G H |
     exact (srxbk_iosend_wr_G _ _ H)].
Qed.

Lemma srxbk_maybeon_wr_G : forall Bw a, maybeon_wr Bw a -> inG TG.G_HARNESS_B a.
Proof.
  intros Bw a (_ & [H | (_ & [H | H])]); [srxbk_G H | srxbk_G H | exact (srxbk_nwr_G _ _ _ H)].
Qed.

Lemma srxbk_onack_wr_G : forall Bw b a, onack_wr Bw b a -> inG TG.G_HARNESS_B a.
Proof.
  intros Bw b a H. unfold onack_wr in H.
  destruct H as [H | [H | [H | [H | H]]]];
    [srxbk_G H | srxbk_G H | exact (srxbk_nwr_G _ _ _ H) | srxbk_G H | exact (srxbk_maybeon_wr_G _ _ H)].
Qed.

Lemma srxbk_sstate_wr_G : forall Bw st why a, sstate_wr Bw st why a -> inG TG.G_HARNESS_B a.
Proof.
  intros Bw st why a (_ & [H | H]); [srxbk_G H | exact (srxbk_nwr_G _ _ _ H)].
Qed.

Lemma srxbk_tick_wr_G : forall Bw a, tick_wr Bw a -> inG TG.G_HARNESS_B a.
Proof.
  intros Bw a H. unfold tick_wr in H.
  do 13 (destruct H as [H | H]; [srxbk_G H |]).
  destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
  - exact (srxbk_nwr_G _ _ _ H).
  - exact (srxbk_nwr_G _ _ _ H).
  - exact (srxbk_nwr_G _ _ _ H).
  - exact (srxbk_iosend_wr_G _ _ H).
  - srxbk_G H.
  - srxbk_G H.
  - exact (srxbk_senddata_wr_G _ H).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Stack arithmetic, frame counts, a run that stores nothing        *)
(* ------------------------------------------------------------------ *)

(* The realigned sp: `addi sp, sp, -160`, `andi sp, sp, -32` from a 16-aligned entry sp. *)
Lemma srxbk_sp1 : forall (spz sp1 : Z), spz mod 16 = 0 -> sp1 = 32 * ((spz - SRX_FRAME) / 32) ->
  spz - 176 <= sp1 <= spz - 160 /\ sp1 mod 32 = 0.
Proof.
  intros spz sp1 H16 E. rewrite E. unfold SRX_FRAME.
  pose proof (Z.div_mod (spz - 160) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spz - 160) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod spz 16 ltac:(lia)) as D16. rewrite H16, Z.add_0_r in D16.
  set (q := (spz - 160) / 32) in *. set (r := (spz - 160) mod 32) in *. set (t := spz / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

(* The three callees' windows, and the realignment's 176 bytes, fit in the walk's window. *)
Lemma srxbk_stk_le : 176 <= SRX_STK /\ ONACK_STK + 176 <= SRX_STK /\ SSTATE_STK + 176 <= SRX_STK /\
  TICK_STK + 176 <= SRX_STK.
Proof. repeat split; apply Z.leb_le; reflexivity. Qed.

(* A 32-aligned sp is 16-aligned. *)
Lemma srxbk_al16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
  intros x H. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
  replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by ring. apply Z.mod_mul. lia.
Qed.

(* A 64-aligned address is 8-aligned. *)
Lemma srxbk_al64_8 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof.
  intros x H. pose proof (Z.div_mod x 64 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
  replace (64 * (x / 64)) with ((8 * (x / 64)) * 8) by ring. apply Z.mod_mul. lia.
Qed.

(* The class-1 frame on top of the caller's frames changes no other class's count. *)
Lemma srxbk_count : forall c pos l, c <> SRX_CID -> count_cid c ((SRX_CID, pos) :: l) = count_cid c l.
Proof.
  intros c pos l H. cbn [count_cid]. rewrite (proj2 (Z.eqb_neq SRX_CID c)) by (intros E; apply H; symmetry; exact E).
  lia.
Qed.

(* A run from a state with no region stores nothing: its memory is the memory before it. *)
Lemma srxbk_mem_eq : forall E (m m' : word -> option byte), frame_of E [] m m' -> m' = m.
Proof.
  intros E m m' H. apply functional_extensionality. intros x. apply H. intros (r & Hr & _). destruct Hr.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The symbolic state at a cut pc: the registers as atoms, no region, no fact. *)
Lemma srxbk_entry : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split.
Qed.

(* The walk's journal: its window lies at or above alloc_ceiling and below 2 ^ 47; its layout keeps the side-stack
   base and the machine stack. *)
Lemma srxbk_ceil : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  alloc_ceiling <= sp0 - STK /\ sp0 <= 2 ^ 47.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hc & Hl & Hh & H47 & _). lia.
Qed.

Lemma srxbk_ly : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  ly_F ly' = ly_F ly /\ ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
  destruct HJ as (_ & _ & (memS & HJi & _) & _).
  destruct HJi as (_ & Hl & _). destruct Hl as (_ & _ & _ & _ & _ & EF & _ & _ & _ & ELo & EHi & _).
  split; [exact EF|]. split; [exact ELo | exact EHi].
Qed.

(* The current heap frame at a window inside the walk's (only decode_off_win reads the registers). *)
Lemma srxbk_tf_win : forall ly S (W : world segs) m (regs regs' : bvmap 5 word) K K' TF,
  spZ regs - K <= spZ regs' - K' -> spZ regs' <= spZ regs ->
  trans_tframe_at B ly S W m regs K TF -> trans_tframe_at B ly S W m regs' K' TF.
Proof.
  intros ly S W m regs regs' K K' TF H1 H2 HT. destruct TF as [fr|]; [|exact I].
  destruct HT as (Ha & Hg & Hs & Hoff). split; [exact Ha|]. split; [exact Hg|]. split; [exact Hs|].
  unfold decode_off_win in *. destruct Hoff as [Ho | Ho]; [left | right]; lia.
Qed.

(* The current heap frame after a G-form callee: its bytes kept (a heap block, a frame, the machine stack outside the
   callee's window, the read-only bytes; not G: trans_tf_off_g), the frames' shadow kept (the callee writes G only),
   so its placement at the state after the call (DgnTransportCg.v trans_src_ok_kept_ge0). *)
Lemma srxbk_tf_kept : AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall ly2 S2 (W2 : world segs) mem2 md2 ly3 S3 (W3 : world segs) mem3 md3 (regs : bvmap 5 word) K slo shi
    (E : Z -> Prop) (TF : option TI.tframe),
  @AR rc segs B ly2 S2 W2 mem2 md2 -> @AR rc segs B ly3 S3 W3 mem3 md3 ->
  Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> frames S3 = frames S2 ->
  ly_F ly3 = ly_F ly2 -> ly_stk_lo ly3 = ly_stk_lo ly2 -> ly_stk_hi ly3 = ly_stk_hi ly2 ->
  acall_kept_g segs B TG.G_HARNESS_B ly2 S2 W2 mem2 W3 mem3 slo shi E ->
  (forall a, E a -> inG TG.G_HARNESS_B a) ->
  (forall x, E x -> forall fr, TF = Some fr ->
     ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)))) ->
  trans_tf_off_g TF ->
  spZ regs - K <= slo -> shi <= spZ regs ->
  trans_tframe_at B ly2 S2 W2 mem2 regs K TF -> trans_tframe_at B ly3 S3 W3 mem3 regs K TF.
Proof.
  intros LAWS HGX HRU HRE ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md3 regs K slo shi E TF HAR2 HAR3 Hperm Hfr ELF Elo Ehi
    (K1 & K2 & K3 & K4 & K5 & K6) HEG Hap Hoffg Hs1 Hs2 HT.
  destruct TF as [fr|]; [|exact I].
  destruct HT as (Ha0 & Hg8 & Hsrc & Hoff).
  set (q := TI.tf_addr fr) in *. set (n := Z.of_nat (length (TI.tf_bytes fr))) in *.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  assert (HnE : forall a, q <= a < q + n -> ~ E a) by (intros a Ha Hx; exact (Hap a Hx fr eq_refl Ha)).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
  { intros a Ha. destruct Hsrc as [(bA & nA & HinA & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 bA nA HAR2 HinA) as (_ & _ & _ & _ & _ & _ & Hn1).
      pose proof (req_size_pos nA (proj1 Hn1)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K2 bA nA (a - bA) HinA ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
    - destruct HL as [(c & p & Hin & F1 & F2) | [(HG & _) | [(S1 & S3') | (HR & _)]]].
      + apply (K4 c p a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
      + exfalso. exact (Hoffg fr eq_refl a Ha (HG a Ha)).
      + destruct (trans_stk_bounds B ly2 S2 W2 mem2 md2 HAR2) as [T1 T2].
        unfold decode_off_win in Hoff.
        destruct Hoff as [Ho | Ho]; (apply K1; [lia | lia]).
      + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
        apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
        intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
        unfold TG.G_HARNESS_B_LO in Gh. lia. }
  assert (KS : forall c p s, In (c, p) (frames S2) ->
     in_zr s (shadow_addr (frame_addr ly2 c p), fs_frame_bytes c / 8) ->
     aview segs (w_H W3) mem3 s = aview segs (w_H W2) mem2 s).
  { intros c p s Hin Hs. apply (K4 c p s Hin (or_intror Hs)). intros Hw.
    pose proof (inG_low segs B transportb_segs_low _ s HGX (HEG s Hw)) as Hl.
    destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 c p HAR2 Hin) as (F1 & F2 & _).
    pose proof (Z.div_pos (frame_addr ly2 c p) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs. cbn [fst snd] in Hs. unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia. }
  split; [exact Ha0|]. split.
  { eapply garr8_frame; [exact Hg8|]. intros a Ha. rewrite length_map in Ha. apply (mbyte_of_aview segs).
    apply KV. exact Ha. }
  split; [|exact Hoff].
  exact (trans_src_ok_kept_ge0 B LAWS ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md3 q n HAR2 HAR3 Hperm Hfr
    ltac:(intros c p; unfold frame_addr; rewrite ELF; reflexivity) Elo Ehi KV KS Hsrc Hn0).
Qed.

(* The read-only bytes after a G-form callee: each lies in the image, outside G, outside the owned statics and
   errno, so acall_kept_g's image clause keeps it. *)
Lemma srxbk_rom_kept : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall ly2 S2 (W2 : world segs) mem2 (W3 : world segs) mem3 slo shi (E : Z -> Prop),
  acall_kept_g segs B TG.G_HARNESS_B ly2 S2 W2 mem2 W3 mem3 slo shi E ->
  trans_rom_view_rd W2 mem2 -> trans_rom_view_rd W3 mem3.
Proof.
  intros HRU HRE ly2 S2 W2 mem2 W3 mem3 slo shi E (_ & _ & K3 & _) Hrom a Ha.
  rewrite <- (Hrom a Ha). destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_B_LO in Gh. lia.
Qed.

(* The cut's srx_cur after a G-form callee called at the state (ly2, S2, W2, mem2) of srx_cur, with the journal after
   the run that follows it: the frames and blocks the callee leaves, the meter, the callee's acall_kept_g folded into
   the walk's (its written range lies in srx_wr b), the 13 saved words (above the callee's window) and the frame's last
   word (a frame byte, not a byte of G) kept. *)
Lemma srxbk_cur_call : AR_laws segs B -> frame_flag_lawP segs B -> ameter_laws MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) buf now r b TF Bw Bw' pos sp1 F
    ly2 S2 (W2 : world segs) mem2 md2 ly3 S3 (W3 : world segs) mem3 md3 slo shi (E : Z -> Prop),
  srxb_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
  srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 0 ->
  @ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own)
    ly3 S3 W3 mem3 md3 (k + 0) ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  acall_kept_g segs B TG.G_HARNESS_B ly2 S2 W2 mem2 W3 mem3 slo shi E ->
  mo_le MT S2 S3 0 ->
  (forall a, E a -> srx_wr b a /\ inG TG.G_HARNESS_B a) ->
  spZ regs - SRX_STK <= slo -> shi <= spZ regs - SRX_FRAME ->
  srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly3 S3 W3 mem3 md3 0.
Proof.
  intros LAWS FFL MTL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md3 slo shi E HFIX HCUR HJ3 Hfr3 Hperm3 HK3 Hmo3 HEw Hslo Hshi.
  pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF & HF0 & HF64 & HFc & HFapp).
  pose proof HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
  destruct (srxbk_ceil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [Hce H47].
  destruct (srxbk_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as (ELFc & _ & _).
  destruct (srxbk_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (ELF3 & _ & _).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  pose proof srxbk_stk_le as (HS176 & _).
  unfold SRXB_FBYTES in HFc, HFapp. unfold SRX_FRAME in Hshi.
  assert (Hin2 : In (SRX_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  assert (EF2 : frame_addr ly2 SRX_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
  pose proof HK3 as (K1 & _ & _ & K4 & _).
  split; [exact HJ3|]. split; [exact He|].
  split; [rewrite Hfr3; exact Hfrs|].
  split; [exact (Permutation_trans Hperm3 Hperm)|].
  split; [rewrite ELF3, <- ELFc; reflexivity|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
  split.
  { apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 mem2 W3 mem3
      (spZ regs - SRX_STK) (spZ regs) slo shi (srx_wr b) E (fun _ => False)).
    - lia.
    - lia.
    - intros c p. unfold frame_addr. rewrite HlyF. reflexivity.
    - intros f Hf. rewrite Hfrs. right. exact Hf.
    - intros bm Hbm. exact (Permutation_in _ (Permutation_sym Hperm) Hbm).
    - intros b0 m i _ _ [].
    - intros c p a _ _ [].
    - exact HK.
    - exact HK3.
    - exact Hslo.
    - lia.
    - intros a Ha. left. exact (proj1 (HEw a Ha)). }
  split.
  { rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
    assert (Hob : 8 <= fst o <= 104).
    { unfold SRXB_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
    apply rdword_ext. intros i Hi. apply K1; lia. }
  rewrite <- HFLw. apply rdword_ext. intros i Hi.
  apply (K4 SRX_CID pos _ Hin2).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF2. change (fs_frame_bytes SRX_CID) with 128.
    unfold SRXB_FBYTES. lia.
  - intros HE. destruct (HEw _ HE) as [_ HG].
    apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 SRX_CID pos (F + SRXB_FBYTES - 8 + i) HAR2 Hin2);
      [rewrite EF2; change (fs_frame_bytes SRX_CID) with 128; unfold SRXB_FBYTES; lia | exact (trans_g_img _ HG)].
Qed.

(* The current heap frame after a run of the walk's own whose stores (Zs) are bytes of G: its bytes are not G
   (trans_tf_off_g), the shadow band is not G, so its placement is carried by trans_src_ok_view; its window may move
   to a callee's inside the walk's. *)
Lemma srxbk_tf_step : AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B ->
  forall ly2 S2 (W2 : world segs) mem2 md2 m1 (regs regs' : bvmap 5 word) K K' (Zs : Z -> Prop) TF,
  @AR rc segs B ly2 S2 W2 mem2 md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) m1 a = aview segs (w_H W2) mem2 a) ->
  (forall a, Zs a -> inG TG.G_HARNESS_B a) -> trans_tf_off_g TF ->
  spZ regs - K <= spZ regs' - K' -> spZ regs' <= spZ regs ->
  trans_tframe_at B ly2 S2 W2 mem2 regs K TF -> trans_tframe_at B ly2 S2 W2 m1 regs' K' TF.
Proof.
  intros LAWS HGX ly2 S2 W2 mem2 md2 m1 regs regs' K K' Zs TF HAR KV HZG Hoffg H1 H2 HT.
  destruct TF as [fr|]; [|exact I].
  destruct HT as (Ha0 & Hg8 & Hsrc & Hoff).
  set (q := TI.tf_addr fr) in *. set (n := Z.of_nat (length (TI.tf_bytes fr))) in *.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hqn : 0 <= q /\ q + n <= 2 ^ 64).
  { destruct Hsrc as [(bA & nA & HinA & B1 & B2) | (_ & (_ & _ & _ & _ & R5 & R6))].
    - destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 bA nA HAR HinA) as (_ & H4096 & Hbc & _ & _ & _ & Hn1).
      pose proof (req_size_pos nA (proj1 Hn1)) as [_ Hreq]. lia.
    - lia. }
  assert (KT : forall a, q <= a < q + n -> aview segs (w_H W2) m1 a = aview segs (w_H W2) mem2 a).
  { intros a Ha. apply KV; [lia|]. intros Hz. exact (Hoffg fr eq_refl a Ha (HZG a Hz)). }
  assert (KSB : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W2) m1 s = aview segs (w_H W2) mem2 s).
  { intros s Hs. apply KV; [lia|]. intros Hz.
    pose proof (inG_low segs B transportb_segs_low _ s HGX (HZG s Hz)). lia. }
  split; [exact Ha0|]. split.
  { eapply garr8_frame; [exact Hg8|]. intros a Ha. rewrite length_map in Ha. apply (mbyte_of_aview segs).
    apply KT. exact Ha. }
  split.
  - exact (trans_src_ok_view B ly2 S2 W2 W2 mem2 m1 q n Hsrc KT KSB).
  - unfold decode_off_win in *. destruct Hoff as [Ho | Ho]; [left | right]; lia.
Qed.

(* The read-only bytes after a run of the walk's own whose stores are bytes of G (no TRANS_RO_RD byte is one). *)
Lemma srxbk_rom_step : forall (W2 : world segs) mem2 m1 (Zs : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) m1 a = aview segs (w_H W2) mem2 a) ->
  (forall a, Zs a -> inG TG.G_HARNESS_B a) ->
  trans_rom_view_rd W2 mem2 -> trans_rom_view_rd W2 m1.
Proof.
  intros W2 mem2 m1 Zs KV HZG Hrom a Ha. rewrite <- (Hrom a Ha). pose proof (trans_ro_rd_bounds a Ha) as Rb.
  apply KV; [lia|]. intros Hz. pose proof (inG_G_HARNESS_hull a (HZG a Hz)) as Gh.
  unfold TG.G_HARNESS_B_LO in Gh. lia.
Qed.

(* The cut's srxb_cur after a run of the walk's own whose stores (Zs) are bytes of srx_wr b in G: every byte outside
   Zs keeps its view (acall_kept_g's clauses: the stack above alloc_ceiling, the blocks, the image outside G and the
   frames are not G, or are in srx_wr b), presence grows, and the saved words and the frame's last word are not G. *)
Lemma srxbk_cur_step : AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) buf now r b TF Bw Bw' pos sp1 F
    ly2 S2 (W2 : world segs) mem2 md2 m1 md1 (Zs : Z -> Prop),
  srxb_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
  srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 0 ->
  @ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own)
    ly2 S2 W2 m1 md1 (k + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) m1 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) m1 a) ->
  (forall a, Zs a -> srx_wr b a /\ inG TG.G_HARNESS_B a) ->
  srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 m1 md1 0.
Proof.
  intros LAWS HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 m1 md1 Zs HFIX HCUR HJ1 KV GR HZ.
  pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF & HF0 & HF64 & HFc & HFapp).
  pose proof HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
  destruct (srxbk_ceil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [Hce H47].
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  pose proof srxbk_stk_le as (HS176 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold SRXB_FBYTES in HFc, HFapp.
  assert (Hin2 : In (SRX_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  assert (EF2 : frame_addr ly2 SRX_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
  assert (HZl : forall a, Zs a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (inG_low segs B transportb_segs_low _ a HGX (proj2 (HZ a Ha)))).
  split; [exact HJ1|]. split; [exact He|]. split; [exact Hfrs|]. split; [exact Hperm|]. split; [exact HlyF|].
  split; [exact Hmo|].
  split.
  { destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
    split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha Hw. rewrite KV; [exact (K1 a Ha Hw) | lia | intros Hz; pose proof (HZl a Hz); lia].
    - intros b0 m i Hb Hi Hn.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m HARc Hb) as (_ & H4096 & Hbc & _).
      rewrite KV; [exact (K2 b0 m i Hb Hi Hn) | lia | intros Hz; exact (Hn (proj1 (HZ _ Hz)))].
    - intros a Hi HnG Hno He'. pose proof (transportb_segs_low a Hi) as Hl.
      rewrite KV; [exact (K3 a Hi HnG Hno He') | lia | intros Hz; exact (HnG (proj2 (HZ a Hz)))].
    - intros cid p a Hin Hr Hn.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid p HARc Hin) as (G4096 & Gce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      assert (Ha : 0 <= a < 2 ^ 64).
      { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
        pose proof (shadow_range_end (frame_addr lyc cid p) (fs_frame_bytes cid) Hfs) as Hse.
        assert (Hd : (frame_addr lyc cid p + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
        pose proof (Z.div_pos (frame_addr lyc cid p) 8 ltac:(lia) ltac:(lia)).
        unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
      rewrite KV; [exact (K4 cid p a Hin Hr Hn) | exact Ha | intros Hz; exact (Hn (proj1 (HZ a Hz)))].
    - intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
    - intros a Ha. apply GR. exact (K6 a Ha). }
  split.
  { rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
    assert (Hob : 8 <= fst o <= 104).
    { unfold SRXB_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
    apply rdword_ext. intros i Hi.
    apply KV; [lia | intros Hz; pose proof (HZl _ Hz); lia]. }
  rewrite <- HFLw. apply rdword_ext. intros i Hi.
  apply KV.
  - unfold SRXB_FBYTES. lia.
  - intros Hz.
    apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 SRX_CID pos (F + SRXB_FBYTES - 8 + i) HAR2 Hin2);
      [rewrite EF2; change (fs_frame_bytes SRX_CID) with 128; unfold SRXB_FBYTES; lia |
       exact (trans_g_img _ (proj2 (HZ _ Hz)))].
Qed.

End k.
