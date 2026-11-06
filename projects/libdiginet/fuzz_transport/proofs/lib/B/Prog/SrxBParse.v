(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 590 of its 658 lines of code are new or changed and 491 lines of the source are left out. *)
(* SrxBParse: Theorem srxb_parse_ok : srxb_parse_stmt (lib/B/Prog/SrxBCut.v), the parse piece of the walk of
   diginet_session_rx on fuzz_transport.asan-ubsan (AF_diginet_session_rx = 0x64e4, BASE + 0x64e4 = 0x87784), from the
   parse cut (+0x130, 0x878b4) to the mac cut (+0x17c) or the ignored cut (+0x1d4). Image A's lib/A/Prog/SrxParse.v at
   image B's listing. The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []) with the
   class-1 frame F owned; the runs are lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x from states with no
   region:
     run 1  +0x130 .. +0x148  s5 = s + 18152, s6 = f = F + 32, a0 = buf, a1 = len, a2 = f, up to `jal
                              diginet_frame_parse` (+0x14c);
     +0x14c                   diginet_frame_parse (lib/B/Prog/diginet_frame_parse_cg.v, a donor-form callee) lifted into
                              the G journal by lib/A/Prog/TransportGCg.v gx_call_cg, with image B's premise f mod 8 = 0
                              (F is 64-aligned); fj is whatever f's 64 bytes hold at the call (srxbp_fj); its window lies
                              inside this call's (TRANS_FP_STK + 176 <= SRX_STK); its X gives a0 = fr_code b and f's
                              bytes trans_fp_f_bytes buf b fj (= frame_f_bytes), gx_call_cg every byte of G kept;
     +0x150 .. +0x154         `andi a1, s4, 7`, a run to `beq a0, zero`, then split by DgnTransportBPaLib.v paj_branch:
                              s4 is pinned to s = TB_g_s, 64-aligned, so a1 = 0 and the engine decides both UBSan tests
                              `bne a1, zero` (+0x158, +0x178) not taken: the trap word at +0x4d0 is not reached;
                              fr_code b = 0 runs to the mac cut; any other code runs `addi a1, s5, 32`, the shadow byte
                              of s + 18184 (0: g_s's payload is a zero-shadow range of the record, trans_srx_cells, so
                              the run's shadow entry SRXBP_SH holds and the `beq` to +0x1d4 is taken; the report at
                              +0x174 is not reached), to the ignored cut with a0 = fr_code b = r and Bw' = srx_ign Bw
                              (srxb_m_code).
   What the call keeps from its entry composes with the callee's acall_kept_g by TransportGCg.v dk_kept_trans_nf_g (the
   callee writes bytes of f, inside the own frame: TransportGFrame.v dkg_nf_sep_gw); the reads the later code hands on
   (srxb_rd) keep their placement and bytes across the callee by DgnTransportBCg.v trans_src_ok_acall_g_ge0; f's
   decode_rd_ok holds after the call from the frame's presence and its shadow bytes kept (srxbp_rd_vis). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f YO0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_rx_cg SrxBCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Definition SRXBP_B0 : Z * Z := (0, 0).
(* +0x130 .. +0x14c: no region, no fact. *)
Definition ss_srxbp1 : sstate := mkSS SRXB_PARSE sr_atoms [] None (mkFacts [] [] []).
(* +0x150 (diginet_frame_parse's return) .. the cut: no region; s4 (atom 20) = s, s5 (atom 21) = s + 18152 and s11
   (atom 27) = the shadow base pinned, the shadow entry of [s5 + 32, s5 + 40) = [s + 18184, s + 18192)
   (g_s.stats.rx_ignored). *)
Definition SRXBP_C1 : Z := SRXB_PARSE + 0x20.
Definition ss_srxbp2 : sstate := mkSS SRXBP_C1 sr_atoms [] None
  (mkFacts [(20%nat, mkAF SRX_S SRX_S 6); (21%nat, mkAF (SRX_S + 18152) (SRX_S + 18152) 3);
            (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
Definition SRXBP_SH : list shent := [mkSHE 21 32 40].
Definition SRXBP_Bx : sv := SOff 27 0.

(* `beq a0, zero` on diginet_frame_parse's result (a small negative code or 0, sign-extended). *)
Lemma srxbp_eqb0 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0 (2 ^ 64)) by lia.
destruct (Z.eqb_spec v 0) as [-> | Hne]; [reflexivity|].
apply Z.eqb_neq. intros HH. apply Hne.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

Lemma srxbp_code_range : forall b, - 2 ^ 31 <= DSpec.fr_code b < 2 ^ 31.
Proof. intros b. destruct (DSpec.fr_code_cases b) as [E | [E | [E | E]]]; rewrite E; lia. Qed.

(* Byte values read back as bytes. *)
Lemma srxbp_bz_b8 : forall l : list Z, Forall (fun x => 0 <= x < 256) l -> map DSpec.bz (map (Z_to_bv 8) l) = l.
Proof.
intros l H. induction l as [|x l IH]; [reflexivity|].
apply Forall_cons_iff in H as [Hx Hl]. cbn [map]. rewrite (IH Hl). f_equal.
unfold DSpec.bz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

Section sp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition srxbp_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Lemma srxbp_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (srxbp_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold srxbp_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma srxbp_entry1 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (srxbp_E regs) ss_srxbp1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SRXB_PARSE)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_srxbp1.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The state at +0x150 and the shadow entry of [s + 18184, s + 18192): g_s's payload is a zero-shadow range of the
   record (trans_srx_cells), so the granule's shadow byte is 0 at every AR state. *)
Lemma srxbp_entry2 : forall ly S (W : world segs) regs mem md,
  trans_srx_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 20 = w64 SRX_S -> YK11.getr regs 21 = w64 (SRX_S + 18152) -> YK11.getr regs 27 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (srxbp_E regs) ss_srxbp2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SRXBP_C1)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SRXBP_Bx SRXBP_SH (srxbp_E regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md HSC HAR R20 R21 R27.
assert (U20 : bv_unsigned (ew (srxbp_E regs) 20) = SRX_S)
  by (rewrite (srxbp_ew_reg regs 20 20%bv eq_refl), R20; apply unsigned_lit_small; unfold SRX_S, TB_g_s; lia).
assert (U21 : bv_unsigned (ew (srxbp_E regs) 21) = SRX_S + 18152)
  by (rewrite (srxbp_ew_reg regs 21 21%bv eq_refl), R21; apply unsigned_lit_small; unfold SRX_S, TB_g_s; lia).
assert (U27 : bv_unsigned (ew (srxbp_E regs) 27) = SHADOW_OFF)
  by (rewrite (srxbp_ew_reg regs 27 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_srxbp2.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  + unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U21, U27.
    change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SRX_S, TB_g_s, SHADOW_OFF;
    first [lia | reflexivity].
- destruct (decode_zshadow_ra B ly S W mem md SRX_S (SRX_S + TW.SZ_g_s) (SRX_S + 18184) 8 HAR (proj1 HSC)
    ltac:(lia) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)) as [HRA _].
  assert (UB : U (srxbp_E regs) SRXBP_Bx = SHADOW_OFF).
  { unfold U, SRXBP_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, SRXBP_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ SRXBP_Bx 21 (SRX_S + 18184) 8 (SRX_S + 18152) 32 40 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U21, Z.add_0_r. apply unsigned_lit_small. unfold SRX_S, TB_g_s; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SRX_S, TB_g_s, SHADOW_OFF in *. lia.
Qed.

(* A present byte is a byte of the restricted memory. *)
Lemma srxbp_present : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> YO0d.present (mrestrict H m) a.
Proof. intros H m a (Hh & bb & Hb). unfold YO0d.present, mrestrict. exists bb. rewrite Hh. exact Hb. Qed.

(* The 64 bytes of f before the call, whatever they are: f's bytes are present (the frame is live). *)
Lemma srxbp_fj : forall (H : word -> bool) (m : word -> option byte) q,
  (forall a, q <= a < q + 64 -> apresent H m a) ->
  exists fj : list byte, length fj = 64%nat /\ garr8 segs (mrestrict H m) q (map DSpec.bz fj).
Proof.
intros H m q Hp.
destruct (garr8_of_present segs (mrestrict H m) q 64 ltac:(intros a Ha; apply srxbp_present; apply Hp; lia))
  as (l & Hl & Hg).
exists (map (Z_to_bv 8) l). split; [rewrite length_map; exact Hl|].
rewrite (srxbp_bz_b8 l (garr8_bytes_ok segs _ _ _ Hg)). exact Hg.
Qed.

(* decode_rd_ok of a range of a live side-stack frame at a later memory where its bytes are visible and the frames'
   shadow bytes kept (DgnTransportBCg.v decode_rd_ok_fake_kept_ge0 with visibility in place of the bytes kept). *)
Lemma srxbp_rd_vis : AR_laws segs B -> forall lyc Sc (W W' : world segs) memc mem' mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> decode_in_fake lyc Sc q n -> decode_rd_ok W memc q n -> 0 <= n ->
  (forall a, q <= a < q + n -> aview segs (w_H W') mem' a <> None) ->
  (forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W') mem' s = aview segs (w_H W) memc s) ->
  decode_rd_ok W' mem' q n.
Proof.
  intros LAWS lyc Sc W W' memc mem' mdc q n HAR (cid & pos & Hin & F1 & F2) (R1 & R2 & R3 & R4 & R5 & R6) Hn K1 K2.
  destruct (TransportGCg.dkg_frame_al64 segs B lyc Sc W memc mdc cid pos HAR Hin) as (A1 & A2 & A3).
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (B1 & B2 & _).
  assert (KG : forall g, frame_addr lyc cid pos <= g < frame_addr lyc cid pos + fs_frame_bytes cid ->
    aview segs (w_H W') mem' (shadow_addr g) = aview segs (w_H W) memc (shadow_addr g)).
  { intros g Hg. apply (K2 cid pos); [exact Hin|]. unfold in_zr, shadow_addr. cbn [fst snd].
    pose proof (Z.div_mod (frame_addr lyc cid pos) 64 ltac:(lia)).
    pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)).
    pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (frame_addr lyc cid pos) 8 ltac:(lia)).
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)).
    pose proof (Z.div_mod g 8 ltac:(lia)). pose proof (Z.mod_pos_bound g 8 ltac:(lia)). lia. }
  split; [|split; [|split; [|exact (conj R4 (conj R5 R6))]]].
  - exact K1.
  - intros x Hx. destruct (R2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hs |- *.
    rewrite (KG x ltac:(lia)). exact Hs.
  - intros s Hs.
    assert (Hhi : (frame_addr lyc cid pos + fs_frame_bytes cid) mod 64 = 0)
      by (rewrite Z.add_mod, A1, A2 by lia; reflexivity).
    destruct (trans_hull_in (frame_addr lyc cid pos) (frame_addr lyc cid pos + fs_frame_bytes cid) q n s
      A1 Hhi F1 F2 Hn Hs) as (g & Hg8 & Hg1 & Hg2 & ->).
    rewrite (KG g ltac:(lia)). exact (R3 _ Hs).
Qed.

(* acall_kept_g at a later memory with the same view and more present bytes. *)
Lemma srxbp_kept_view : forall G lyc Sc (W : world segs) memc (W2 : world segs) mem2 mem3 slo shi (E : Z -> Prop),
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  acall_kept_g segs B G lyc Sc W memc W2 mem3 slo shi E.
Proof.
intros G lyc Sc W memc W2 mem2 mem3 slo shi E (K1 & K2 & K3 & K4 & K5 & K6) KD GR.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
- intros bb m i Hb Hi Hn. rewrite KD. exact (K2 bb m i Hb Hi Hn).
- intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
- intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
- intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
- intros a Ha. apply GR. exact (K6 a Ha).
Qed.

(* What the cuts carry moves to a later memory with the same view and more present bytes. *)
Lemma srxbp_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2
    (W2 : world segs) mem2 md2 mem3 md3 e,
  srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((SRX_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 KD GR.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- exact (srxbp_kept_view _ _ _ _ _ _ _ _ _ _ _ HK KD GR).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
Qed.

(* The reads the later code hands on move to a later memory with the same view. *)
Lemma srxbp_rd_move : forall ly2 S2 (W2 : world segs) mem2 mem3 regs buf b TF Bw,
  srxb_rd B ly2 S2 W2 mem2 regs buf b TF Bw ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  srxb_rd B ly2 S2 W2 mem3 regs buf b TF Bw.
Proof.
intros ly2 S2 W2 mem2 mem3 regs buf b TF Bw (G8 & Src & TFa & Rom & Nd) KD.
assert (KM : forall a, mbyte segs (mrestrict (w_H W2) mem3) a = mbyte segs (mrestrict (w_H W2) mem2) a)
  by (intros a; apply (mbyte_of_aview segs); exact (KD a)).
split; [exact (garr8_frame segs _ _ _ _ G8 (fun a _ => KM a))|].
split; [exact (trans_src_ok_view B ly2 S2 W2 W2 mem2 mem3 _ _ Src (fun a _ => KD a) (fun a _ => KD a))|].
split.
{ destruct TF as [fr|]; [|exact I]. destruct TFa as (T0 & T8 & TS & TO).
  split; [exact T0|]. split; [exact (garr8_frame segs _ _ _ _ T8 (fun a _ => KM a))|].
  split; [exact (trans_src_ok_view B ly2 S2 W2 W2 mem2 mem3 _ _ TS (fun a _ => KD a) (fun a _ => KD a)) | exact TO]. }
split; [intros a Ha; rewrite KD; exact (Rom a Ha)|].
intros H1 H2 H3 H4 H5 H6 H7 H8. destruct (Nd H1 H2 H3 H4 H5 H6 H7 H8) as [NS NO].
split; [exact (trans_src_ok_view B ly2 S2 W2 W2 mem2 mem3 _ _ NS (fun a _ => KD a) (fun a _ => KD a)) | exact NO].
Qed.

End sp.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac srxbp_reg HS r v H tac :=
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
(* A register a run did not write: its value at the run's start (Q), read through the valuation srxbp_E rg. *)
Ltac srxbp_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    srxbp_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (srxbp_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* After a run with no region: every byte of the view as before (KD), presence grown (GR). *)
Ltac srxbp_after_run HS W KD GR m0 msF :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?mf) => rename mf into msF
  end;
  assert (KD : forall a, aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m0 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a; rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m0 a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m0) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (can_aview_kept_frame E rs (w_H W) m0 (ms_mem msF) 0 HFx ltac:(lia)
               ltac:(let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
                     intros x Hx; unfold in_wrange; intros (r & Hr & _); vm_compute in Hr; destruct Hr) _ Ha) end
  | ];
  assert (GR : forall a, apresent (w_H W) m0 a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m0) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].

Section sp2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma srxbp_holds : @srxb_parse_stmt fx rc B MT.
Proof.
unfold srxb_parse_stmt. intros IGN MAC. unfold srxb_parse_at.
intros LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HRD HRDF HTW2 HREGS.
pose proof LAWS0 as (HPCS & HCELLS & HSC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof CALLS as (ASM & AFP & ABC & ALEAF & AMC & AONA & AONK & ASST & AOND & ATICK).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & H13 & Hsp16 & Hlo & Hhi & Hnow & Hbuf0 & Hg8b &
  Hsrcb & Hoffb & Hboffg & Htw0 & Hgf & Hm & HTF & Htfg & Hrom & Hap & Hinv & Hnd & Hc1 & Hc4 & Hc5 & Hc0 & Hc2 & Hev &
  Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HRD as (Hg8 & Hsrc2 & HTF2 & Hrom2 & Hnd2).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R23 & R24).
assert (Ee : e = 0) by (rewrite srx_ev_zero in He; lia). subst e. rewrite Z.add_0_r in HJ2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EST : SRX_STK = 9184) by reflexivity. assert (EFP : TRANS_FP_STK = 4176) by reflexivity.
assert (EES : ESTACK = 4096) by reflexivity.
unfold SRXB_FBYTES in HFc, HFapp, HFLw.
(* the caller's journal: its window and layout *)
pose proof HJ0 as (HSTK & _ & (memS0 & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARc & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF0 & _ & _ & _ & ESLO0 & ESHI0 & _).
clear HJi memS0.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold SRX_FRAME.
  pose proof (Z.div_mod (spZ regs - 160) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 160) / 32) in *. set (rr := (spZ regs - 160) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (Hfa2c : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite HlyF; reflexivity).
assert (Hin2 : In (SRX_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
set (FL := flag_addr lyc SRX_CID pos) in *.
(* the frame and the bytes at buf are apart; so are the frame and every range the caller placed *)
assert (DISJ : forall q n, trans_src_ok B lyc Sc W memc q n -> 0 < n -> q + n <= F \/ F + 128 <= q).
{ intros q n Hq Hn.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  destruct (trans_src_ok_disj_own B LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 SRX_CID pos q n HARc HAR2 Hfrs Hperm
    Hfa2c Hq Hn) as [X | X]; rewrite Hfa2c, <- EF in X; change (fs_frame_bytes SRX_CID) with 128 in X; [left | right];
    exact X. }
(* +0x130 .. +0x14c: s5 = s + 18152, s6 = f, a0 = buf, a1 = len, a2 = f, `jal diginet_frame_parse` *)
pose proof (srxbp_entry1 W2 regs2 mem2) as HS.
assert (HEI : img_env VAL A_LIM (srxbp_E regs2)) by (unfold srxbp_E; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (srxbp_E regs2) (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
paj_run_tok RUN HS HJ2 SHOK SRXBP_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
clear HEI0.
srxbp_after_run HS W2 KD1 GR1 mem2 msC.
set (mdC := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdC. clear mat HF HFr HG.
srxbp_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 26164)) Q1 ltac:(apply codeptr_val; exact HEI).
srxbp_kreg HS regs2 (2%bv : bv 5) 2%nat R2 Q2.
srxbp_kreg HS regs2 (3%bv : bv 5) 3%nat (eq_trans R3 Hgp) Q3.
srxbp_kreg HS regs2 (4%bv : bv 5) 4%nat (eq_trans R4 Htp) Q4.
srxbp_kreg HS regs2 (8%bv : bv 5) 8%nat R8 Q8.
srxbp_kreg HS regs2 (9%bv : bv 5) 9%nat R9 Q9.
srxbp_kreg HS regs2 (18%bv : bv 5) 18%nat R18 Q18.
srxbp_kreg HS regs2 (19%bv : bv 5) 19%nat R19 Q19.
srxbp_kreg HS regs2 (20%bv : bv 5) 20%nat R20 Q20.
srxbp_kreg HS regs2 (25%bv : bv 5) 25%nat R25 Q25.
srxbp_kreg HS regs2 (26%bv : bv 5) 26%nat R26 Q26.
srxbp_kreg HS regs2 (27%bv : bv 5) 27%nat R27 Q27.
srxbp_kreg HS regs2 (23%bv : bv 5) 23%nat R23 Q23.
srxbp_kreg HS regs2 (24%bv : bv 5) 24%nat R24 Q24.
srxbp_reg HS (10%bv : bv 5) (w64 buf) Q10
  ltac:(cbn [sv_denot]; rewrite (srxbp_ew_reg regs2 24 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R24).
srxbp_reg HS (11%bv : bv 5) (w64 (Z.of_nat (length b))) Q11
  ltac:(cbn [sv_denot]; rewrite (srxbp_ew_reg regs2 23 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R23).
srxbp_reg HS (12%bv : bv 5) (w64 (F + SRX_F)) Q12
  ltac:(cbn [sv_denot]; rewrite (srxbp_ew_reg regs2 26 26%bv eq_refl), R26; unfold w64, SRX_F;
        rewrite (unsigned_lit_small F) by lia; reflexivity).
srxbp_reg HS (22%bv : bv 5) (w64 (F + SRX_F)) Q22
  ltac:(cbn [sv_denot]; rewrite (srxbp_ew_reg regs2 26 26%bv eq_refl), R26; unfold w64, SRX_F;
        rewrite (unsigned_lit_small F) by lia; reflexivity).
srxbp_reg HS (21%bv : bv 5) (w64 (SRX_S + 18152)) Q21
  ltac:(cbn [sv_denot]; rewrite (srxbp_ew_reg regs2 20 20%bv eq_refl), R20; unfold w64;
        rewrite (unsigned_lit_small SRX_S) by (unfold SRX_S, TB_g_s; lia); reflexivity).
assert (USPC : spZ (ms_regs msC) = sp1) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB_diginet_frame_parse)) mm rom) mdx) Q)
end.
clear HS SHOK.
(* the call state: the frame's bytes are present, f's 64 bytes fj *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARC.
destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem msC) mdC SRX_CID pos HARC Hin2) as (_ & _ & HFbC & HFshC).
rewrite Hfa2c, <- EF in HFbC, HFshC. change (fs_frame_bytes SRX_CID) with 128 in HFbC.
destruct (srxbp_fj (w_H W2) (ms_mem msC) (F + SRX_F)
  ltac:(intros a Ha; unfold SRX_F in Ha; exact (proj1 (HFbC a ltac:(lia))))) as (fj & Hfj & Hg8f).
assert (EBR : BASE + 26164 = 0x878d4) by (vm_compute; reflexivity).
assert (Hf8 : (F + SRX_F) mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. unfold SRX_F. rewrite D.
  replace (64 * (F / 64) + 32) with ((8 * (F / 64) + 4) * 8) by ring. apply Z.mod_mul. lia. }
(* +0x14c: diginet_frame_parse (buf, len, f), a donor-form callee lifted into the G journal *)
eapply SRr_bind.
{ apply (@gx_call_cg fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own)
    ly2 S2 W2 (ms_mem msC) mdC k _ (ms_regs msC) TRANS_FP_STK TRANS_FP_EV 0 (trans_fp_wr (F + SRX_F))
    (fun regs3 W3 mem3 => YK11.getr regs3 10 = w64 (DSpec.fr_code b) /\
       garr8 segs (mrestrict (w_H W3) mem3) (F + SRX_F) (trans_fp_f_bytes buf b fj)) HGX HGNE HJ2).
  intros memS HJS. eapply SRr_mono.
  { apply (AFP fx STK sp0 FP ly S W0 memS md0 ((SRX_CID, pos) :: own) ly2 S2 W2 (ms_mem msC) mdC k (ms_regs msC)
      buf (F + SRX_F) b fj HJS).
    - rewrite Q1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
    - unfold raZ. rewrite Q1, EBR. rewrite unsigned_lit_small by lia. lia.
    - exact Q3.
    - exact Q4.
    - exact Q10.
    - exact Q11.
    - exact Q12.
    - rewrite USPC. pose proof Hsp1 as (_ & M1). pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1.
      rewrite M1, Z.add_0_r in D1. rewrite D1. replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring.
      apply Z.mod_mul. lia.
    - rewrite USPC, EFP. rewrite EST in Hlo. lia.
    - rewrite USPC. lia.
    - lia.
    - unfold SRX_F. lia.
    - exact Hf8.
    - exact (trans_src_ok_view B ly2 S2 W2 W2 mem2 (ms_mem msC) _ _ Hsrc2 (fun a _ => KD1 a) (fun a _ => KD1 a)).
    - unfold decode_off_win in Hoffb |- *. rewrite USPC, EFP. rewrite EST in Hoffb.
      destruct Hoffb as [X | X]; [left | right]; lia.
    - exact (garr8_frame segs _ _ _ _ Hg8 (fun a _ => mbyte_of_aview segs _ _ _ _ a (KD1 a))).
    - exact Hfj.
    - exact Hg8f.
    - exists SRX_CID, pos. split; [exact Hin2|]. rewrite Hfa2c, <- EF. change (fs_frame_bytes SRX_CID) with 128.
      unfold SRX_F, TRANS_FP_F_SIZE. lia.
    - intros a Ha. unfold SRX_F, TRANS_FP_F_SIZE in Ha.
      assert (Haw : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 ((SRX_CID, pos) :: own) a).
      { right; right; right. exists SRX_CID, pos. split; [left; reflexivity|].
        left. unfold in_zr. cbn [fst snd]. rewrite Hfa2c, <- EF. change (fs_frame_bytes SRX_CID) with 128. lia. }
      destruct (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJS Haw) as [Hp Ho].
      split; [exact Haw|]. split; [exact Hp|]. split; [exact Ho|]. rewrite USPC. lia.
    - exact (trans_rd_ok_view W2 W2 mem2 (ms_mem msC) _ _ HRDF (fun a _ => KD1 a) (fun a _ => KD1 a)).
    - unfold decode_off_win. left. rewrite USPC, EFP. unfold SRX_F, TRANS_FP_F_SIZE. rewrite EST in Hlo. lia.
    - intros Hl. destruct (DISJ buf _ Hsrcb ltac:(lia)) as [X | X]; [right | left]; unfold SRX_F, TRANS_FP_F_SIZE; lia.
    - unfold TRANS_FP_EV. rewrite srx_ev_zero in Hev. lia. }
  intros W' c' _ Hp.
  exact (decode_cg_post_dcg B MT STK sp0 FP ly S W0 memS md0 ((SRX_CID, pos) :: own) ly2 S2 W2 (ms_mem msC) k
    (ms_regs msC) _ _ _ _ _ W' c' Hp). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
  (HX10 & HXf) & HGK3).
assert (Ee3 : e3 = 0) by (unfold TRANS_FP_EV in He3; lia). subst e3. rewrite Z.add_0_r in HJ3.
rewrite Q1. change (Z_to_bv 64 (BASE + 26164)) with (Z_to_bv 64 (BASE + SRXBP_C1)).
(* the layouts: the frames where the caller's layout puts them, the same machine stack *)
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _ & _ & _ & ESLO3 & ESHI3 & _).
clear HJi3 memS3.
pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). rewrite !Z.add_0_r in HJi2.
pose proof HJi2 as (_ & Hlyle2 & _). pose proof Hlyle2 as (_ & _ & _ & _ & _ & ELF2 & _ & _ & _ & ESLO2 & ESHI2 & _).
clear HJi2 memS2.
assert (Hfa32 : forall c p, frame_addr ly3 c p = frame_addr ly2 c p)
  by (intros c p; unfold frame_addr; rewrite ELF3, ELF2; reflexivity).
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF0; reflexivity).
assert (ES32 : ly_stk_lo ly3 = ly_stk_lo ly2) by (rewrite ESLO3, ESLO2; reflexivity).
assert (EH32 : ly_stk_hi ly3 = ly_stk_hi ly2) by (rewrite ESHI3, ESHI2; reflexivity).
assert (Hfrs3 : frames S3 = (SRX_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hperm3c : Permutation (ablocks B ly3 S3) (ablocks B lyc Sc)) by exact (Permutation_trans Hperm3 Hperm).
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
assert (Hfin2 : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf; rewrite Hfrs; right; exact Hf).
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 (ms_mem msC) mdC SRX_CID pos F FL HARC Hfrs
  Hbl2 HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
(* the callee's written range lies in f, a range of the own frame in application memory *)
assert (HEw : forall a, trans_fp_wr (F + SRX_F) a -> F <= a < F + 128)
  by (intros a Ha; unfold trans_fp_wr, SRX_F in Ha; lia).
assert (HEsh : forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ trans_fp_wr (F + SRX_F) a).
{ intros a Ha Hw. pose proof (HEw a Hw) as X.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold kLowMemEnd, kHighShadowEnd in Ha.
  destruct HFapp as (_ & [HL | (HH1 & HH2)]); lia. }
(* a range the caller placed, apart from the frame and from the callee's window, keeps its placement and bytes *)
assert (AC : forall q n, 0 <= n -> (0 < n -> q + n <= F \/ F + 128 <= q) -> (q + n <= sp1 - 4176 \/ sp1 <= q) ->
  trans_src_ok B ly2 S2 W2 (ms_mem msC) q n ->
  trans_src_ok B ly3 S3 W3 mem3 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) (ms_mem msC) a)).
{ intros q n Hn Hd Hw Hs.
  apply (trans_src_ok_acall_g_ge0 B LAWS HRU HRE ly2 S2 W2 (ms_mem msC) mdC ly3 S3 W3 mem3 md3
    (spZ (ms_regs msC) - TRANS_FP_STK) (spZ (ms_regs msC)) (trans_fp_wr (F + SRX_F)) q n HARC HAR3 Hperm3 Hfr3 Hfa32
    ES32 EH32 HK3 HGK3); [| exact HEsh | rewrite USPC, EFP; exact Hw | exact Hs | exact Hn].
  intros a Ha Hx. pose proof (HEw a Hx) as X. destruct (Hd ltac:(lia)) as [Y | Y]; lia. }
(* what the call kept from its entry: the stack malloc's frame (dkg_nf) holds the callee's written range *)
assert (KC2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (ms_mem msC) (spZ regs - SRX_STK) (spZ regs)
  (srx_wr b)) by exact (srxbp_kept_view B _ _ _ _ _ _ _ _ _ _ _ HK KD1 GR1).
assert (KC3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - SRX_STK) (spZ regs) (srx_wr b)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 (ms_mem msC) W3 mem3
    (spZ regs - SRX_STK) (spZ regs) (spZ (ms_regs msC) - TRANS_FP_STK) (spZ (ms_regs msC)) (srx_wr b)
    (trans_fp_wr (F + SRX_F)) (dkg_nf SRX_CID F FL)).
  - rewrite EST. lia.
  - lia.
  - exact Hfa2c.
  - exact Hfin2.
  - exact Hbl2.
  - exact N1.
  - exact N3.
  - exact KC2.
  - exact HK3.
  - rewrite USPC, EFP, EST. lia.
  - rewrite USPC. lia.
  - intros a Ha. right. left. change (fs_frame_bytes SRX_CID) with 128. exact (HEw a Ha). }
(* the bytes at or above sp1 are those at the parse cut *)
pose proof HK3 as (K31 & _ & K33 & K34 & _).
assert (KHI : forall a, sp1 <= a < 2 ^ 64 -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite K31 by (rewrite ?USPC; lia). exact (KD1 a). }
assert (HSo : forall o, In o SRXB_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold SRXB_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
assert (HSV3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem3) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SRXB_SAVED).
{ rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
  pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KHI. lia. }
(* the frame's last word is the one the stack malloc left *)
assert (HFL3 : rdword (aview segs (w_H W3) mem3) (F + 128 - 8) = Some FL).
{ rewrite <- HFLw. apply rdword_ext. intros i Hi. rewrite <- (KD1 (F + 128 - 8 + i)).
  apply (K34 SRX_CID pos (F + 128 - 8 + i) Hin2).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa2c, <- EF. change (fs_frame_bytes SRX_CID) with 128. lia.
  - unfold trans_fp_wr, SRX_F. lia. }
(* the world relation: G is kept *)
assert (TW3 : tw_at TMAP_B (aview segs (w_H W3) mem3) Bw).
{ apply (tw_kept_GB (aview segs (w_H W2) mem2)); [exact HTW2|]. intros bb n i Hin Hi.
  assert (HiG : inG TG.G_HARNESS_B (bb + i))
    by (unfold inG; apply Exists_exists; exists (bb, n); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  exact (eq_trans (HGK3 (bb + i) HiG) (KD1 (bb + i))). }
(* the reads the later code hands on, after the call *)
pose proof (srxbp_rd_move B ly2 S2 W2 mem2 (ms_mem msC) regs buf b TF Bw HRD KD1)
  as (Hg8C & HsrcC & HTFC & HromC & HndC).
assert (WIN : forall q n, decode_off_win regs SRX_STK q n -> q + n <= sp1 - 4176 \/ sp1 <= q).
{ intros q n Hw. unfold decode_off_win in Hw. rewrite EST in Hw. destruct Hw as [X | X]; [left | right]; lia. }
destruct (AC buf (Z.of_nat (length b)) ltac:(lia) (DISJ buf _ Hsrcb) (WIN _ _ Hoffb) HsrcC) as (Hsrc3 & Kbuf).
assert (RD3 : srxb_rd B ly3 S3 W3 mem3 regs buf b TF Bw).
{ split; [|split; [exact Hsrc3|split; [|split]]].
  - apply (garr8_frame segs _ _ _ _ Hg8C). intros a Ha. unfold TW.zs in Ha. rewrite length_map in Ha.
    apply (mbyte_of_aview segs). exact (Kbuf a Ha).
  - destruct TF as [fr|]; [|exact I]. destruct HTFC as (T0 & T8 & TS & TO). pose proof HTF as (_ & _ & TSc & _).
    destruct (AC (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) ltac:(lia) (DISJ _ _ TSc) (WIN _ _ TO) TS)
      as (TS3 & KT).
    split; [exact T0|]. split; [|exact (conj TS3 TO)].
    apply (garr8_frame segs _ _ _ _ T8). intros a Ha. rewrite length_map in Ha.
    apply (mbyte_of_aview segs). exact (KT a Ha).
  - intros a Ha. rewrite <- (HromC a Ha). destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho Hne].
    apply (K33 a (trans_ro_img a Ha)); [|exact Ho | exact Hne].
    intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
    unfold TG.G_HARNESS_B_LO in Gh. lia.
  - intros H1 H2 H3 H4 H5 H6 H7 H8.
    destruct (HndC H1 H2 H3 H4 H5 H6 H7 H8) as [NS NO]. destruct (Hnd H1 H2 H3 H4 H5 H6 H7 H8) as [NSc _].
    pose proof (DSpec.fr_code_ok b H1) as (_ & _ & Hnb & _).
    destruct (AC (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (DSpec.fr_body_len b) ltac:(unfold DSpec.fr_body_len; lia)
      (DISJ _ _ NSc) (WIN _ _ NO) NS) as (NS3 & _).
    exact (conj NS3 NO). }
(* f's 64 bytes after the call: visible (the frame is live), its shadow bytes the call's (E misses the shadow) *)
assert (Hin3 : In (SRX_CID, pos) (frames S3)) by (rewrite Hfr3; exact Hin2).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 SRX_CID pos HAR3 Hin3) as (_ & _ & HFb3 & _).
rewrite Hfa32, Hfa2c, <- EF in HFb3. change (fs_frame_bytes SRX_CID) with 128 in HFb3.
assert (Hfake : decode_in_fake ly2 S2 (F + SRX_F) FRAME_F_SIZE).
{ exists SRX_CID, pos. split; [exact Hin2|]. rewrite Hfa2c, <- EF. change (fs_frame_bytes SRX_CID) with 128.
  unfold SRX_F, FRAME_F_SIZE. lia. }
assert (RDF3 : decode_rd_ok W3 mem3 (F + SRX_F) FRAME_F_SIZE).
{ apply (srxbp_rd_vis B LAWS ly2 S2 W2 W3 (ms_mem msC) mem3 mdC (F + SRX_F) FRAME_F_SIZE HARC Hfake
    (trans_rd_ok_view W2 W2 mem2 (ms_mem msC) _ _ HRDF (fun a _ => KD1 a) (fun a _ => KD1 a))).
  - unfold FRAME_F_SIZE. lia.
  - intros a Ha. unfold SRX_F, FRAME_F_SIZE in Ha. apply can_aview_vis. exact (proj1 (HFb3 a ltac:(lia))).
  - intros cid p s Hin Hs. apply (K34 cid p s Hin (or_intror Hs)). intros Hw. pose proof (HEw s Hw) as X.
    destruct (frames_bounds segs B LAWS ly2 S2 W2 (ms_mem msC) mdC cid p HARC Hin) as (G1 & G2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    pose proof (shadow_range_end (frame_addr ly2 cid p) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr ly2 cid p + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr ly2 cid p) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs. cbn [fst snd] in Hs.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd.
    destruct HFapp as (_ & [HL | (HH1 & HH2)]); lia. }
assert (FB3 : srxb_fbytes W3 mem3 F buf b fj) by exact (conj Hfj HXf).
assert (CUR3 : srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly3 S3 W3 mem3 md3 0).
{ refine (conj _ (conj _ (conj Hfrs3 (conj Hperm3c (conj ELF3c (conj _ (conj KC3 (conj HSV3 _)))))))).
  - rewrite Z.add_0_r. exact HJ3.
  - rewrite srx_ev_zero. lia.
  - exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3).
  - unfold SRXB_FBYTES. exact HFL3. }
(* the callee-saved registers at the return *)
assert (V2 : YK11.getr regs3 2%bv = w64 sp1)
  by (transitivity (YK11.getr (ms_regs msC) 2%bv); [exact (HP3 2 ltac:(unfold acallee_saved; lia)) | exact Q2]).
assert (V3 : YK11.getr regs3 3%bv = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs msC) 3%bv); [exact (HP3 3 ltac:(unfold acallee_saved; lia)) | exact Q3]).
assert (V4 : YK11.getr regs3 4%bv = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs msC) 4%bv); [exact (HP3 4 ltac:(unfold acallee_saved; lia)) | exact Q4]).
assert (V8 : YK11.getr regs3 8%bv = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs msC) 8%bv); [exact (HP3 8 ltac:(unfold acallee_saved; lia)) | exact Q8]).
assert (V9 : YK11.getr regs3 9%bv = w64 sp1)
  by (transitivity (YK11.getr (ms_regs msC) 9%bv); [exact (HP3 9 ltac:(unfold acallee_saved; lia)) | exact Q9]).
assert (V18 : YK11.getr regs3 18%bv = w64 F)
  by (transitivity (YK11.getr (ms_regs msC) 18%bv); [exact (HP3 18 ltac:(unfold acallee_saved; lia)) | exact Q18]).
assert (V19 : YK11.getr regs3 19%bv = w64 now)
  by (transitivity (YK11.getr (ms_regs msC) 19%bv); [exact (HP3 19 ltac:(unfold acallee_saved; lia)) | exact Q19]).
assert (V20 : YK11.getr regs3 20%bv = w64 SRX_S)
  by (transitivity (YK11.getr (ms_regs msC) 20%bv); [exact (HP3 20 ltac:(unfold acallee_saved; lia)) | exact Q20]).
assert (V21 : YK11.getr regs3 21%bv = w64 (SRX_S + 18152))
  by (transitivity (YK11.getr (ms_regs msC) 21%bv); [exact (HP3 21 ltac:(unfold acallee_saved; lia)) | exact Q21]).
assert (V22 : YK11.getr regs3 22%bv = w64 (F + SRX_F))
  by (transitivity (YK11.getr (ms_regs msC) 22%bv); [exact (HP3 22 ltac:(unfold acallee_saved; lia)) | exact Q22]).
assert (V25 : YK11.getr regs3 25%bv = w64 (SHADOW_OFF + F / 8))
  by (transitivity (YK11.getr (ms_regs msC) 25%bv); [exact (HP3 25 ltac:(unfold acallee_saved; lia)) | exact Q25]).
assert (V26 : YK11.getr regs3 26%bv = w64 F)
  by (transitivity (YK11.getr (ms_regs msC) 26%bv); [exact (HP3 26 ltac:(unfold acallee_saved; lia)) | exact Q26]).
assert (V27 : YK11.getr regs3 27%bv = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs msC) 27%bv); [exact (HP3 27 ltac:(unfold acallee_saved; lia)) | exact Q27]).
clear HJ2 HK HK3 KC2 Hsaved HFLw HRD HRDF HTW2 Hg8 Hsrc2 HTF2 Hrom2 Hnd2 Hg8C HsrcC HTFC HromC HndC AC.
(* +0x150 .. : a1 = s & 7, `beq a0, zero` on diginet_frame_parse's result *)
pose proof (srxbp_entry2 B ly3 S3 W3 regs3 mem3 md3 HSC HAR3 V20 V21 V27) as [HS SHOK].
assert (HEI3 : img_env VAL A_LIM (srxbp_E regs3)) by (unfold srxbp_E; apply Eimg_env).
assert (D10 : sv_denot (srxbp_E regs3) (SOff 10 0) = Z_to_bv 64 (DSpec.fr_code b))
  by (cbn [sv_denot]; rewrite (srxbp_ew_reg regs3 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact HX10).
paj_run_to_tok RUNTO HS HJ3 SHOK YC4b.Bspan (SRXBP_C1 + 4).
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
clear HEI0.
srxbp_after_run HS W3 KDa GRa mem3 msA.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* fr_code b = 0: `beq` taken; `bne a1, zero` at +0x178 not taken (a1 = s & 7 = 0); the mac cut +0x17c *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (srxbp_E regs3) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (srxbp_eqb0 _ (srxbp_code_range b)) in Hc. apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ3 SHOK YC4b.Bspan SRXB_MAC.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_nil. }
  srxbp_after_run HS W3 KDb GRb (ms_mem msA) msF.
  assert (KD2 : forall a, aview tfibsegs (w_H W3) (ms_mem msF) a = aview tfibsegs (w_H W3) mem3 a)
    by (intros a; exact (eq_trans (KDb a) (KDa a))).
  assert (GR2 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msF) a)
    by (intros a Ha; exact (GRb a (GRa a Ha))).
  srxbp_kreg HS regs3 (2%bv : bv 5) 2%nat V2 Y2. srxbp_kreg HS regs3 (3%bv : bv 5) 3%nat V3 Y3.
  srxbp_kreg HS regs3 (4%bv : bv 5) 4%nat V4 Y4. srxbp_kreg HS regs3 (8%bv : bv 5) 8%nat V8 Y8.
  srxbp_kreg HS regs3 (9%bv : bv 5) 9%nat V9 Y9. srxbp_kreg HS regs3 (18%bv : bv 5) 18%nat V18 Y18.
  srxbp_kreg HS regs3 (19%bv : bv 5) 19%nat V19 Y19. srxbp_kreg HS regs3 (20%bv : bv 5) 20%nat V20 Y20.
  srxbp_kreg HS regs3 (21%bv : bv 5) 21%nat V21 Y21. srxbp_kreg HS regs3 (22%bv : bv 5) 22%nat V22 Y22.
  srxbp_kreg HS regs3 (25%bv : bv 5) 25%nat V25 Y25. srxbp_kreg HS regs3 (26%bv : bv 5) 26%nat V26 Y26.
  srxbp_kreg HS regs3 (27%bv : bv 5) 27%nat V27 Y27.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_MAC)) mm rom) mdx) Q) end.
  apply (MAC LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
    ly3 S3 W3 (ms_mem msF) _ 0 (ms_regs msF) HFIX).
  + exact (srxbp_cur_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly3 S3 W3 mem3 md3
      (ms_mem msF) _ 0 CUR3 ltac:(rewrite Z.add_0_r; exact HJ3) KD2 GR2).
  + exact (srxbp_rd_move B ly3 S3 W3 mem3 (ms_mem msF) regs buf b TF Bw RD3 KD2).
  + exact (trans_rd_ok_view W3 W3 mem3 (ms_mem msF) _ _ RDF3 (fun a _ => KD2 a) (fun a _ => KD2 a)).
  + exact (conj Hfj (garr8_frame segs _ _ _ _ HXf (fun a _ => mbyte_of_aview segs _ _ _ _ a (KD2 a)))).
  + exact (tw_kept TMAP_B (aview segs (w_H W3) mem3) _ Bw TW3 (fun x _ => KD2 x)).
  + exact Hc.
  + refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y19 (conj Y20 (conj Y25 (conj Y26
      Y27)))))))))) (conj Y21 Y22)).
    * rewrite Y3. symmetry. exact Hgp.
    * rewrite Y4. symmetry. exact Htp.
- (* fr_code b <> 0: `bne a1, zero` at +0x158 not taken (s & 7 = 0), the checked access at s + 18184 (its shadow
     byte is 0), to the ignored cut +0x1d4 *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (srxbp_E regs3) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (srxbp_eqb0 _ (srxbp_code_range b)) in Hc. apply Z.eqb_neq in Hc.
  pose proof (srxb_m_code timg_B TF Bw b now Hc) as HMc. rewrite HMc in Hm.
  destruct (srxb_some_inv _ _ _ _ Hm) as [EBw' Er].
  paj_run_to_tok RUNTO HS HJ3 SHOK YC4b.Bspan SRXB_IGN.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_nil. }
  srxbp_after_run HS W3 KDb GRb (ms_mem msA) msF.
  assert (KD2 : forall a, aview tfibsegs (w_H W3) (ms_mem msF) a = aview tfibsegs (w_H W3) mem3 a)
    by (intros a; exact (eq_trans (KDb a) (KDa a))).
  assert (GR2 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msF) a)
    by (intros a Ha; exact (GRb a (GRa a Ha))).
  srxbp_kreg HS regs3 (2%bv : bv 5) 2%nat V2 Y2. srxbp_kreg HS regs3 (3%bv : bv 5) 3%nat V3 Y3.
  srxbp_kreg HS regs3 (4%bv : bv 5) 4%nat V4 Y4. srxbp_kreg HS regs3 (8%bv : bv 5) 8%nat V8 Y8.
  srxbp_kreg HS regs3 (9%bv : bv 5) 9%nat V9 Y9. srxbp_kreg HS regs3 (18%bv : bv 5) 18%nat V18 Y18.
  srxbp_kreg HS regs3 (19%bv : bv 5) 19%nat V19 Y19. srxbp_kreg HS regs3 (20%bv : bv 5) 20%nat V20 Y20.
  srxbp_kreg HS regs3 (21%bv : bv 5) 21%nat V21 Y21. srxbp_kreg HS regs3 (22%bv : bv 5) 22%nat V22 Y22.
  srxbp_kreg HS regs3 (25%bv : bv 5) 25%nat V25 Y25. srxbp_kreg HS regs3 (26%bv : bv 5) 26%nat V26 Y26.
  srxbp_kreg HS regs3 (27%bv : bv 5) 27%nat V27 Y27.
  srxbp_reg HS (10%bv : bv 5) (w64 r) Y10
    ltac:(cbn [sv_denot]; rewrite (srxbp_ew_reg regs3 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, HX10, Er;
          reflexivity).
  srxbp_reg HS (11%bv : bv 5) (w64 SRXB_RXIGN) Y11
    ltac:(cbn [sv_denot]; rewrite (srxbp_ew_reg regs3 21 21%bv eq_refl), V21; unfold w64, SRXB_RXIGN;
          rewrite unsigned_lit_small by (unfold SRX_S, TB_g_s; lia); f_equal; lia).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_IGN)) mm rom) mdx) Q) end.
  apply (IGN LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' Bw pos sp1 F
    ly3 S3 W3 (ms_mem msF) _ 0 (ms_regs msF) HFIX).
  + exact (srxbp_cur_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly3 S3 W3 mem3 md3
      (ms_mem msF) _ 0 CUR3 ltac:(rewrite Z.add_0_r; exact HJ3) KD2 GR2).
  + exact (tw_kept TMAP_B (aview segs (w_H W3) mem3) _ Bw TW3 (fun x _ => KD2 x)).
  + exact Hgf.
  + exact (eq_sym EBw').
  + refine (conj (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y19 (conj Y20 (conj Y25 (conj Y26
      Y27)))))))))) (conj Y21 Y22)) (conj Y10 Y11)).
    * rewrite Y3. symmetry. exact Hgp.
    * rewrite Y4. symmetry. exact Htp.
Qed.
End sp2.

(* The parse piece of the walk of diginet_session_rx on image B (SrxBCut.v srxb_parse_stmt), at every machine, run
   ceiling, record and meter. *)
Theorem srxb_parse_ok : forall fx rc B MT, @srxb_parse_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@srxbp_holds fx rc B MT). Qed.
