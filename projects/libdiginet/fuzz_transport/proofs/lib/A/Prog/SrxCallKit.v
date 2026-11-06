(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module names changed; 1031 of its 1126 lines of code are new or changed and 935 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_session_wake_seg_ntc.v, with its module names and numbers changed; 773 of its 1107 lines of code are new or changed and 792 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_ack_seg_ntc.v, with its module names changed; 221 of its 324 lines of code are new or changed and 1004 lines of the source are left out. *)
(* SrxCallKit: the lemmas the ack, lost and tick pieces of diginet_session_rx's image-A walk share (SrxAck.v,
   SrxLost.v, SrxTick.v; the cut interface is SrxCut.v). Each of the three pieces runs a few register moves from its
   cut to a `jal` of a G-form callee (on_ack, session_lost, diginet_session_tick), applies the callee's contract in the
   walk's own G journal while the class-1 frame is live, and runs the `j` after the call to the next cut. The kit:
   - srxk_entry: the symbolic state at a cut pc with no region (the registers as atoms, no fact);
   - srxk_mem_eq: a run from a state with no region stores nothing (its frame_of over no region is the identity), so
     the memory after it is the memory before it;
   - srxk_*_wr_G: every byte the three callees may store is a byte of G (TransportG.v G_HARNESS), field by field
     (srxk_G decomposes a written range down to its twa_fld rows);
   - srxk_tf_win: the current heap frame at a smaller window inside the walk's; srxk_tf_kept and srxk_rom_kept: the
     heap frame and the read-only bytes after a G-form callee (its acall_kept_g; its written range is G and misses TF);
   - srxk_cur_call: the cut's srx_cur after a G-form callee called with the frame live (the callee's acall_kept_g
     folded into the walk's by TransportGCg.v dk_kept_trans_nf_g; the 13 saved words above the realigned sp and the
     frame's last word kept, since the callee writes only bytes of G);
   - the stack arithmetic of the realigned sp (srxk_sp1, srxk_stk_le, srxk_ceil) and the frame counts at the call
     state (srxk_count). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_rx_cg SrxCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
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

Lemma srxk_after : forall I F Bs b now B2, srx_sw I F Bs b now = Some (B2, tt) ->
  srx_after I F Bs b now = TSS.diginet_session_tick_m I F B2 now.
Proof. intros I F Bs b now B2 H. unfold srx_after. rewrite H. reflexivity. Qed.

Lemma srxk_after_none : forall I F Bs b now, srx_sw I F Bs b now = None -> srx_after I F Bs b now = None.
Proof. intros I F Bs b now H. unfold srx_after. rewrite H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 2. The written ranges lie in G                                      *)
(* ------------------------------------------------------------------ *)

(* A field of a world row lies in that row's global, a byte of G. *)
Lemma srxk_row : forall o b n A w a, In (o, b, n) TMAP_A -> o <= A -> A + w <= o + n -> twa_fld o b A w a ->
  inG TG.G_HARNESS a.
Proof.
  intros o b n A w a Hin H1 H2 Ha. unfold inG. apply Exists_exists. exists (b, n).
  split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr, twa_fld in *; cbn [fst snd]; lia].
Qed.

(* The bounds of a field inside its row: closed ones computed, indexed ones by lia over the index's bound. *)
Ltac srxk_num :=
  first
    [ apply Z.leb_le; reflexivity
    | unfold TW.A_GOT_t_state, TW.GOT_t_ESZ, TW.OFF_GOT, TW.SZ_GOT, TC.TRANS_MAX, TW.A_Cmd_st, TW.OFF_g_cmd,
        TW.SZ_g_cmd, TC.CMDS_MAX, TW.A_M_fly_frame, TW.OFF_M, TW.SZ_M, TC.SPEC_MAX_FRAME, TW.A_S_queue_bytes,
        TW.S_queue_ESZ, TW.S_queue_N, TW.OFF_g_s, TW.SZ_g_s in *; lia ].

Ltac srxk_rowG row H := refine (srxk_row _ _ _ _ _ _ row _ _ H); srxk_num.

Ltac srxk_anyrow H :=
  first
    [ srxk_rowG TMAP_A_g_s H | srxk_rowG TMAP_A_M H | srxk_rowG TMAP_A_GOT H | srxk_rowG TMAP_A_g_cmd H
    | srxk_rowG TMAP_A_g_q H | srxk_rowG TMAP_A_g_nq H | srxk_rowG TMAP_A_g_fail_next H
    | srxk_rowG TMAP_A_g_last_counter H ].

(* A written range, down to its rows: disjunctions split, guards kept in the context, each row a field of G. *)
Ltac srxk_G H :=
  lazymatch type of H with
  | _ \/ _ => let H1 := fresh "Hw" in let H2 := fresh "Hw" in destruct H as [H1 | H2]; [srxk_G H1 | srxk_G H2]
  | _ /\ _ => let H1 := fresh "Hg" in let H2 := fresh "Hw" in destruct H as [H1 H2]; srxk_G H2
  | exists _, _ => let x := fresh "x" in let H1 := fresh "Hw" in destruct H as [x H1]; srxk_G H1
  | twa_fld _ _ _ _ _ => srxk_anyrow H
  | _ => fail "srxk_G: no row for" H
  end.

Lemma srxk_nwr_G : forall Bw n a, notice_wr Bw n a -> inG TG.G_HARNESS a.
Proof. intros Bw n a H. unfold notice_wr in H. srxk_G H. Qed.

Lemma srxk_iosend_wr_G : forall n a, iosend_wr n a -> inG TG.G_HARNESS a.
Proof. intros n a H. unfold iosend_wr in H. srxk_G H. Qed.

Lemma srxk_senddata_wr_G : forall a, senddata_wr a -> inG TG.G_HARNESS a.
Proof.
  intros a H. unfold senddata_wr in H.
  destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]];
    [srxk_G H | srxk_G H | srxk_G H | srxk_G H | srxk_G H | srxk_G H | srxk_G H | srxk_G H | srxk_G H |
     exact (srxk_iosend_wr_G _ _ H)].
Qed.

Lemma srxk_maybeon_wr_G : forall Bw a, maybeon_wr Bw a -> inG TG.G_HARNESS a.
Proof.
  intros Bw a (_ & [H | (_ & [H | H])]); [srxk_G H | srxk_G H | exact (srxk_nwr_G _ _ _ H)].
Qed.

Lemma srxk_onack_wr_G : forall Bw b a, onack_wr Bw b a -> inG TG.G_HARNESS a.
Proof.
  intros Bw b a H. unfold onack_wr in H.
  destruct H as [H | [H | [H | [H | H]]]];
    [srxk_G H | srxk_G H | exact (srxk_nwr_G _ _ _ H) | srxk_G H | exact (srxk_maybeon_wr_G _ _ H)].
Qed.

Lemma srxk_slost_wr_G : forall Bw why a, slost_wr Bw why a -> inG TG.G_HARNESS a.
Proof.
  intros Bw why a H. unfold slost_wr in H.
  destruct H as [H | [H | (_ & [H | H])]]; [srxk_G H | srxk_G H | srxk_G H | exact (srxk_nwr_G _ _ _ H)].
Qed.

Lemma srxk_tick_wr_G : forall Bw a, tick_wr Bw a -> inG TG.G_HARNESS a.
Proof.
  intros Bw a H. unfold tick_wr in H.
  do 13 (destruct H as [H | H]; [srxk_G H |]).
  destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
  - exact (srxk_nwr_G _ _ _ H).
  - exact (srxk_nwr_G _ _ _ H).
  - exact (srxk_nwr_G _ _ _ H).
  - exact (srxk_iosend_wr_G _ _ H).
  - srxk_G H.
  - srxk_G H.
  - exact (srxk_senddata_wr_G _ H).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Stack arithmetic, frame counts, a run that stores nothing        *)
(* ------------------------------------------------------------------ *)

(* The realigned sp: `addi sp, sp, -160`, `andi sp, sp, -32` from a 16-aligned entry sp. *)
Lemma srxk_sp1 : forall (spz sp1 : Z), spz mod 16 = 0 -> sp1 = 32 * ((spz - SRX_FRAME) / 32) ->
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
Lemma srxk_stk_le : 176 <= SRX_STK /\ ONACK_STK + 176 <= SRX_STK /\ SLOST_STK + 176 <= SRX_STK /\
  TICK_STK + 176 <= SRX_STK.
Proof. repeat split; apply Z.leb_le; reflexivity. Qed.

(* A 32-aligned sp is 16-aligned. *)
Lemma srxk_al16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
  intros x H. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
  replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by ring. apply Z.mod_mul. lia.
Qed.

(* A 64-aligned address is 8-aligned. *)
Lemma srxk_al64_8 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof.
  intros x H. pose proof (Z.div_mod x 64 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
  replace (64 * (x / 64)) with ((8 * (x / 64)) * 8) by ring. apply Z.mod_mul. lia.
Qed.

(* The class-1 frame on top of the caller's frames changes no other class's count. *)
Lemma srxk_count : forall c pos l, c <> SRX_CID -> count_cid c ((SRX_CID, pos) :: l) = count_cid c l.
Proof.
  intros c pos l H. cbn [count_cid]. rewrite (proj2 (Z.eqb_neq SRX_CID c)) by (intros E; apply H; symmetry; exact E).
  lia.
Qed.

(* A run from a state with no region stores nothing: its memory is the memory before it. *)
Lemma srxk_mem_eq : forall E (m m' : word -> option byte), frame_of E [] m m' -> m' = m.
Proof.
  intros E m m' H. apply functional_extensionality. intros x. apply H. intros (r & Hr & _). destruct Hr.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The symbolic state at a cut pc: the registers as atoms, no region, no fact. *)
Lemma srxk_entry : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split.
Qed.

(* The walk's journal: its window lies at or above alloc_ceiling and below 2 ^ 47; its layout keeps the side-stack
   base and the machine stack. *)
Lemma srxk_ceil : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  alloc_ceiling <= sp0 - STK /\ sp0 <= 2 ^ 47.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hc & Hl & Hh & H47 & _). lia.
Qed.

Lemma srxk_ly : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  ly_F ly' = ly_F ly /\ ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
  destruct HJ as (_ & _ & (memS & HJi & _) & _).
  destruct HJi as (_ & Hl & _). destruct Hl as (_ & _ & _ & _ & _ & EF & _ & _ & _ & ELo & EHi & _).
  split; [exact EF|]. split; [exact ELo | exact EHi].
Qed.

(* The current heap frame at a window inside the walk's (only decode_off_win reads the registers). *)
Lemma srxk_tf_win : forall ly S (W : world segs) m (regs regs' : bvmap 5 word) K K' TF,
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
Lemma srxk_tf_kept : AR_laws segs B -> gx_ok segs B TG.G_HARNESS -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall ly2 S2 (W2 : world segs) mem2 md2 ly3 S3 (W3 : world segs) mem3 md3 (regs : bvmap 5 word) K slo shi
    (E : Z -> Prop) (TF : option TI.tframe),
  @AR rc segs B ly2 S2 W2 mem2 md2 -> @AR rc segs B ly3 S3 W3 mem3 md3 ->
  Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> frames S3 = frames S2 ->
  ly_F ly3 = ly_F ly2 -> ly_stk_lo ly3 = ly_stk_lo ly2 -> ly_stk_hi ly3 = ly_stk_hi ly2 ->
  acall_kept_g segs B TG.G_HARNESS ly2 S2 W2 mem2 W3 mem3 slo shi E ->
  (forall a, E a -> inG TG.G_HARNESS a) ->
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
        unfold TG.G_HARNESS_LO in Gh. lia. }
  assert (KS : forall c p s, In (c, p) (frames S2) ->
     in_zr s (shadow_addr (frame_addr ly2 c p), fs_frame_bytes c / 8) ->
     aview segs (w_H W3) mem3 s = aview segs (w_H W2) mem2 s).
  { intros c p s Hin Hs. apply (K4 c p s Hin (or_intror Hs)). intros Hw.
    pose proof (inG_low segs B transport_segs_low _ s HGX (HEG s Hw)) as Hl.
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
Lemma srxk_rom_kept : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall ly2 S2 (W2 : world segs) mem2 (W3 : world segs) mem3 slo shi (E : Z -> Prop),
  acall_kept_g segs B TG.G_HARNESS ly2 S2 W2 mem2 W3 mem3 slo shi E ->
  trans_rom_view_rd W2 mem2 -> trans_rom_view_rd W3 mem3.
Proof.
  intros HRU HRE ly2 S2 W2 mem2 W3 mem3 slo shi E (_ & _ & K3 & _) Hrom a Ha.
  rewrite <- (Hrom a Ha). destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_LO in Gh. lia.
Qed.

(* The cut's srx_cur after a G-form callee called at the state (ly2, S2, W2, mem2) of srx_cur, with the journal after
   the run that follows it: the frames and blocks the callee leaves, the meter, the callee's acall_kept_g folded into
   the walk's (its written range lies in srx_wr b), the 13 saved words (above the callee's window) and the frame's last
   word (a frame byte, not a byte of G) kept. *)
Lemma srxk_cur_call : AR_laws segs B -> frame_flag_lawP segs B -> ameter_laws MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) buf now r b TF Bw Bw' pos sp1 F
    ly2 S2 (W2 : world segs) mem2 md2 ly3 S3 (W3 : world segs) mem3 md3 slo shi (E : Z -> Prop),
  srx_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
  srx_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 0 ->
  @ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own)
    ly3 S3 W3 mem3 md3 (k + 0) ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  acall_kept_g segs B TG.G_HARNESS ly2 S2 W2 mem2 W3 mem3 slo shi E ->
  mo_le MT S2 S3 0 ->
  (forall a, E a -> srx_wr b a /\ inG TG.G_HARNESS a) ->
  spZ regs - SRX_STK <= slo -> shi <= spZ regs - SRX_FRAME ->
  srx_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly3 S3 W3 mem3 md3 0.
Proof.
  intros LAWS FFL MTL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md3 slo shi E HFIX HCUR HJ3 Hfr3 Hperm3 HK3 Hmo3 HEw Hslo Hshi.
  pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF & HF0 & HF64 & HFc & HFapp).
  pose proof HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
  destruct (srxk_ceil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [Hce H47].
  destruct (srxk_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as (ELFc & _ & _).
  destruct (srxk_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (ELF3 & _ & _).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  pose proof srxk_stk_le as (HS176 & _).
  unfold SRX_FBYTES in HFc, HFapp. unfold SRX_FRAME in Hshi.
  assert (Hin2 : In (SRX_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  assert (EF2 : frame_addr ly2 SRX_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
  pose proof HK3 as (K1 & _ & _ & K4 & _).
  split; [exact HJ3|]. split; [exact He|].
  split; [rewrite Hfr3; exact Hfrs|].
  split; [exact (Permutation_trans Hperm3 Hperm)|].
  split; [rewrite ELF3, <- ELFc; reflexivity|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
  split.
  { apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 mem2 W3 mem3
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
    { unfold SRX_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
    apply rdword_ext. intros i Hi. apply K1; lia. }
  rewrite <- HFLw. apply rdword_ext. intros i Hi.
  apply (K4 SRX_CID pos _ Hin2).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF2. change (fs_frame_bytes SRX_CID) with 128.
    unfold SRX_FBYTES. lia.
  - intros HE. destruct (HEw _ HE) as [_ HG].
    apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 SRX_CID pos (F + SRX_FBYTES - 8 + i) HAR2 Hin2);
      [rewrite EF2; change (fs_frame_bytes SRX_CID) with 128; unfold SRX_FBYTES; lia | exact (trans_g_img _ HG)].
Qed.

End k.
