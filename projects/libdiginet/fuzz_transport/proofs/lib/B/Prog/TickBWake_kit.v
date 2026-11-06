(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths and module names changed; 202 of its 283 lines of code are new or changed and 1129 lines of the source are left out. *)
(* TickBWake_kit: what the wake piece (TickBWake.v) and the online piece (TickBOnline.v) of the image-B walk of
   diginet_session_tick (lib/B/Prog/TickCutB.v) share. rule 24: proves no function (lemmas for two pieces of a walk;
   the walk is composed at TickCutB.v tick_holds_of). Both pieces run a timeout test and, when it fails, the same
   lost-arm code at two addresses (wake: +0x20c .. +0x240, online: +0x444 .. +0x474): the checked 4-byte stores of 0
   at s + 212 and s + 168, then a2 = why, to the lost cut (+0x478). This file holds, at image B's names
   (lib/B/YB1v.v tfibsegs, lib/B/TransportGB.v G_HARNESS_B, lib/B/Prog/TWorldB.v TMAP_B):
   - twb_gsh0: g_s's shadow bytes read 0 at every AR state (trans_tick_cells; image A's TickWake.v tw_gsh0);
   - twb_aview_of_val0: a region cell holding 0 reads 0 through the view (image A's SlostHead.v slh_aview_of_val0,
     which is stated over image A's segments);
   - twb_pre_move: the facts of the wake / online cut move to a later memory with the same view (TickWake.v
     tw_pre_move), for the step cut when no byte was stored;
   - ss_twb2, twb_entry2: the symbolic state of the lost-arm stores at any entry pc (the g_s cells s + 212, s + 168
     writable bytes of G, the two shadow bytes 21 and 26 of g_s read as 0);
   - twb_lost_cur: the lost cut's facts (TickCutB.v tick_lost_cur) from the cut's tick_pre_cur and what the stores
     leave: the four bytes at s + 212 and at s + 168 read 0, every other byte keeps its view
     (TransportGFrame.v dk_kept_nfz_gw for acall_kept_g; TickBKit.v slh_tw_w1B for the world at slost_w1 Bw);
   - the run tactics twb_awr_vac, twb_awr2, twb_kept_vac and twb_keep (TickWake.v tw_awr_vac, tw_awr2, tw_kept_vac,
     and its sn_reg calls). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k YE2y AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg TickCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB TickBKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TickCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TCA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TickCut.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The constants and the lost-arm symbolic state                       *)
(* ------------------------------------------------------------------ *)

(* The shadow byte of g_s (s + 0, s = 0x5df640); the checks of s + 40, s + 44, s + 152, s + 168, s + 176 and s + 212
   read the bytes 5, 5, 19, 21, 22 and 26 after it. *)
Definition TWB_SH : Z := 2148220616.
Lemma TWB_SH_eq : TWB_SH = SHADOW_OFF + TICK_S / 8.
Proof. reflexivity. Qed.
(* The runs' base sv and span (no shadow-relative region). *)
Definition TWB_Bx : sv := SLit 0.
Definition TWB_B0 : Z * Z := (0, 0).

(* The bytes the lost arm stores: g_s.inflight (s + 212) and g_s.desk_counter_valid (s + 168). *)
Definition twb_Z (x : Z) : Prop := (TICK_S + 212 <= x < TICK_S + 216) \/ (TICK_S + 168 <= x < TICK_S + 172).

(* The lost arm's stores, from its first instruction (+0x20c on wake, +0x444 on online) to the lost cut: the two
   g_s cells, each a writable window of G, and the two shadow bytes 21 and 26 of g_s, read as 0; s4 = s and s8 = the
   shadow base as literals. *)
Definition TWB_R2_inf : YP09.region :=
  YP09.mkRegion None (TICK_S + 212) (TICK_S + 216) (TICK_S + 212) (TICK_S + 216) [].
Definition TWB_R2_dcv : YP09.region :=
  YP09.mkRegion None (TICK_S + 168) (TICK_S + 172) (TICK_S + 168) (TICK_S + 172) [].
Definition TWB_R2_shg : YP09.region :=
  YP09.mkRegion None (TWB_SH + 21) (TWB_SH + 27) 0 0
    [YP09.mkChunk (TWB_SH + 21) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TWB_SH + 26) (YP09.CVal 1 (SLit 0))].
Definition TWB_FACTS2 : facts := mkFacts [] [] [].
Definition TWB_REGS2 : list sv :=
  sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_twb2 (pc : Z) : sstate :=
  mkSS pc TWB_REGS2 [TWB_R2_inf; TWB_R2_dcv; TWB_R2_shg] None TWB_FACTS2.

(* ------------------------------------------------------------------ *)
(* The run tactics                                                     *)
(* ------------------------------------------------------------------ *)

(* The write rights of a run whose regions have no write window. *)
Ltac twb_awr_vac :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* The write rights of the lost arm's run (the regions of ss_twb2: two windows of g_s, bytes of G). *)
Ltac twb_awr2 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  do 2 (apply awr_ok_x_cons_g;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      apply slh_inGB; unfold TICK_S, TB_g_s, TW.SZ_g_s; lia |]);
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil.

(* Every byte kept by a run whose regions have no write window. *)
Ltac twb_kept_vac HFr KD :=
  lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m) (mrestrict ?H ?m') =>
    assert (KD : forall a, aview tfibsegs H m' a = aview tfibsegs H m a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in
      intros a; rewrite (aview_wrap64 tfibsegs _ m' a), (aview_wrap64 tfibsegs _ m a);
      pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
      apply (kept_of_frame E rs H m m' (fun _ => False) HFr); [| exact Ha | intros []];
      let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
      let Hiw := fresh "Hiw" in let Hx := fresh "Hx" in
      intros b wlo whi x Hiw Hx; cbv beta; sn_winB Hiw Hx ltac:(lia)
    | ] end.

(* Register nz (atom nn) of the machine state of HS is the run's start value in rg (EE: the start environment's
   atoms are rg's registers). *)
Ltac twb_keep HS EE rg nz nn H :=
  sn_regB HS (Z_to_bv 5 nz) (YK11.getr rg (Z_to_bv 5 nz)) H
    ltac:(cbn [sv_denot]; rewrite (EE nn (Z_to_bv 5 nz) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).

(* A region cell of n bytes holding 0, read byte by byte through the view. *)
Lemma twb_aview_of_val0 : forall H (m : word -> option byte) a (n : nat),
  val_mem tfibsegs (mrestrict H m) a n 0 -> forall j, 0 <= j < Z.of_nat n -> aview tfibsegs H m (a + j) = Some 0.
Proof.
intros H m a n HV j Hj. pose proof (HV (Z.to_nat j) ltac:(lia)) as H0.
rewrite Z2Nat.id in H0 by lia. unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
lazymatch goal with |- context [?f 0 n (Z.to_nat j)] => unfold f end.
rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity.
Qed.

Section twb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* g_s's shadow bytes are 0 at every AR state (trans_tick_cells). *)
Lemma twb_gsh0 : forall ly S (W : world segs) mem md o,
  trans_tick_cells B -> @AR rc segs B ly S W mem md -> 0 <= o < 2283 ->
  aview segs (w_H W) mem (TWB_SH + o) = Some 0.
Proof.
  intros ly S W mem md o HTC HAR Ho.
  replace (TWB_SH + o) with (FCells.shadow_addr (TICK_S + 8 * o)).
  - apply (decode_zshadow_rd B ly S W mem md TICK_S (TICK_S + TW.SZ_g_s) _ HAR); [| | | exact HTC].
    + unfold TICK_S, TB_g_s. rewrite Z.add_mod, Z.mul_comm, Z.mod_mul by lia. reflexivity.
    + lia.
    + unfold TW.SZ_g_s. lia.
  - unfold FCells.shadow_addr, FCells.ASAN_K, TWB_SH, TICK_S, TB_g_s.
    replace (6157888 + 8 * o) with ((769736 + o) * 8) by lia.
    rewrite Z.div_mul by lia. lia.
Qed.

(* The facts a cut before any store carries move to a later memory whose view is the same at every address. *)
Lemma twb_pre_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 mem3 md3,
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((TICK_CID, pos) :: own) lyc S2 W mem3 md3 (k + 0) ->
  (forall a, aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a) ->
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem3 md3.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 mem3 md3
  (((HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) & HN) & Hbl & HGK & Htw) HJ3 KD GR.
refine (conj (conj (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))) _)
  (conj Hbl (conj _ _))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b m i Hb Hi Hn. rewrite KD. exact (K2 b m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HN.
- intros a Ha. rewrite KD. exact (HGK a Ha).
- apply (tw_kept TMAP_B (aview segs (w_H W) mem2)); [exact Htw | intros x _; exact (KD x)].
Qed.

(* The lost arm's symbolic state at its entry pc, before the registers are pinned. *)
Lemma twb_entry2_0 : forall ly S (W : world segs) regs mem md pc,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs []))
    (mkSS pc sr_atoms [TWB_R2_inf; TWB_R2_dcv; TWB_R2_shg] None TWB_FACTS2)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md pc HTC HAR.
  set (E := Eimg (PI := PI_transportb) (Ereg regs [])).
  assert (HGW : forall o, TICK_S <= o < TICK_S + TW.SZ_g_s -> writable_at segs (mrestrict (w_H W) mem) o).
  { intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B o G_HARNESS_B_rw). apply slh_inGB. exact Ho. }
  assert (ZG : forall o, 0 <= o < 2283 ->
    val_mem segs (mrestrict (w_H W) mem) (0 + (TWB_SH + o)) (N.to_nat 1) 0).
  { intros o Ho. rewrite Z.add_0_l. apply YE2y.val_mem1_of_aview. exact (twb_gsh0 ly S W mem md o HTC HAR Ho). }
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TWB_R2_inf TWB_R2_dcv TWB_R2_shg
        base_val].
    + split; [unfold TICK_S, TB_g_s; lia|]. split; [unfold TICK_S, TB_g_s; lia|]. split; [|constructor].
      intros o Ho. apply HGW. unfold TW.SZ_g_s. lia.
    + split; [unfold TICK_S, TB_g_s; lia|]. split; [unfold TICK_S, TB_g_s; lia|]. split; [|constructor].
      intros o Ho. apply HGW. unfold TW.SZ_g_s. lia.
    + split; [unfold TWB_SH; lia|]. split; [unfold TWB_SH; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 (TWB_SH + 21) 1 (SLit 0) 0); [reflexivity | lia | lia | exact (ZG 21 ltac:(lia))].
      * apply (chunk_ok_val segs E _ 0 (TWB_SH + 26) 1 (SLit 0) 0); [reflexivity | lia | lia | exact (ZG 26 ltac:(lia))].
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, TWB_R2_inf, TWB_R2_dcv, TWB_R2_shg.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TWB_SH, TICK_S, TB_g_s. repeat split; first [exact I | lia].
  - unfold TWB_FACTS2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The lost arm's symbolic state at its entry pc: s4 = s and s8 = the shadow base, pinned. *)
Lemma twb_entry2 : forall ly S (W : world segs) regs mem md pc,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) (ss_twb2 pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md pc HTC HAR R20 R24.
  rewrite restrict_mkst_fx.
  pose proof (twb_entry2_0 ly S W regs mem md pc HTC HAR) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  exact H2.
Qed.

(* The lost cut's facts: from the facts of the wake / online cut at mem2 (tick_pre_cur), a later memory mem3 of the
   same journal state whose bytes at s + 212 .. s + 215 and s + 168 .. s + 171 read 0 and whose other bytes keep their
   views and presence, and the lost arm's model fact. *)
Lemma twb_lost_cur : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) now r
    (TF : option TI.tframe) Bw Bw' pos sp1 F S2 mem2 md2 mem3 md3 why,
  tick_laws B MT ->
  tick_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((TICK_CID, pos) :: own) lyc S2 W mem3 md3 (k + 0) ->
  (forall j, 0 <= j < 4 -> aview segs (w_H W) mem3 (TICK_S + 212 + j) = Some 0) ->
  (forall j, 0 <= j < 4 -> aview segs (w_H W) mem3 (TICK_S + 168 + j) = Some 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ twb_Z a -> aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a) ->
  why = TS0.DIGINET_R_WAKE_TIMEOUT \/ why = TS0.DIGINET_R_SILENCE ->
  tick_lost_m timg_B TF Bw why = Some (Bw', r) ->
  tick_lost_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs r TF Bw Bw' pos F why S2 mem3 md3.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2 mem2 md2 mem3 md3 why
  LAWS0 HFIX HCUR HJ3 Z212 Z168 KAN GAN Hwhy HLM.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGNE & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGE).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTF & Hrom &
  Hapart & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hnow56) & Hbl & HGK & Htw1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TCA.TICK_FBYTES in HFc, HFapp, HFLw.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HTS : TICK_STK = 208 + SENDDATA_STK) by reflexivity.
assert (HES : ESTACK <= SENDDATA_STK) by (apply Z.leb_le; reflexivity).
assert (EST : ESTACK = 4096) by reflexivity.
assert (Hin : In (TICK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
set (FL := flag_addr lyc TICK_CID pos) in *.
(* the own frame lies apart from g_s *)
assert (HFG : F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 2048) TICK_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (TICK_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 2048 /\ TICK_S <= x < TICK_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F TICK_S) as [h3|h3]; [exists TICK_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS lyc S2 W mem2 md2 TICK_CID pos x HAR2 Hin);
    [rewrite <- EF; change (fs_frame_bytes TICK_CID) with 2048; lia|].
  apply trans_g_img. apply slh_inGB. exact Hx2. }
assert (HZg : forall a, twb_Z a -> TICK_S <= a < TICK_S + TW.SZ_g_s)
  by (intros a [Hz | Hz]; unfold TW.SZ_g_s; lia).
(* what the call kept, from its entry to the lost cut *)
assert (HSZ : forall a, twb_Z a ->
  (spZ regs - TICK_STK <= a < spZ regs) \/ dkg_nf TICK_CID F FL a \/ inG TG.G_HARNESS_B a)
  by (intros a Ha; right; right; exact (slh_inGB a (HZg a Ha))).
pose proof (dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc lyc S2 W memc mdc W mem2 md2 mem2
  mem3 (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F FL (tick_wr Bw) twb_Z HGX HARc HAR2 Hfrs
  ltac:(intros bm Hb; rewrite Hbl; exact Hb) eq_refl EF eq_refl FFL ltac:(lia) ltac:(lia) HSZ HK KAN GAN)
  as KC3.
assert (HSo : forall o, In o TICK_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold TCA.TICK_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
refine (conj (conj HJ3 (conj He0 (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj KC3 (conj _ _))))))))
  (conj Hbl (conj _ (conj _ (conj Hwhy HLM))))).
- (* the saved words *)
  rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
  pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi.
  apply KAN; [lia|]. intros Hz. pose proof (HZg _ Hz) as Hz2. unfold TICK_S, TB_g_s, TW.SZ_g_s in Hz2. lia.
- (* the flag word *)
  unfold TCA.TICK_FBYTES. change (flag_addr lyc TICK_CID pos) with FL. rewrite <- HFLw. apply rdword_ext. intros i Hi.
  apply KAN; [lia|]. intros Hz. pose proof (HZg _ Hz) as Hz2. destruct HFG; lia.
- (* every byte of G outside tick_wr Bw is the call's *)
  intros a Ha Hn. rewrite <- (HGK a Ha).
  apply KAN; [pose proof (inG_low segs B transportb_segs_low _ a HGX Ha); unfold kLowMemEnd in *; lia|].
  intros Hz. apply Hn. unfold tick_wr. destruct Hz as [Hz | Hz].
  + left. unfold twb_fld, TW.A_S_inflight, TW.OFF_g_s, TICK_S in *. lia.
  + right; left. unfold twb_fld, TW.A_S_desk_counter_valid, TW.OFF_g_s, TICK_S in *. lia.
- (* the world relation at slost_w1 Bw *)
  apply (slh_tw_w1B (aview segs (w_H W) mem2) _ Bw Htw1 Z212 Z168).
  intros x Hx H1 H2. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KAN; [lia|]. intros [Hz | Hz]; [exact (H1 Hz) | exact (H2 Hz)].
Qed.

End twb.
