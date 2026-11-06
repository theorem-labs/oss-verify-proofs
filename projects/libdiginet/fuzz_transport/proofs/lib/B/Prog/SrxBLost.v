(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 366 of its 434 lines of code are new or changed and 697 lines of the source are left out. *)
(* SrxBLost: the disconnect arm of diginet_session_rx's image-B walk, srxb_lost_ok : srxb_lost_stmt (SrxBCut.v), code
   +0x448 .. +0x488 (0x87bcc .. 0x87c0c). On image B session_lost is inlined (SrxBCut.v srxb_sw_lost): run 1 (PaRun
   token engine at image B's listing, from the arm cut) takes the two checked 4-byte stores of 0 at s + 212
   (g_s.inflight) and s + 168 (g_s.desk_counter_valid), whose shadow checks read g_s's zero shadow (the shadow entry
   [s + 168, s + 216) of trans_srx_cells), so the slow paths +0x50c and +0x51c and their __asan_report_store4 calls
   (0x87c9c, 0x87cac) are not taken; then a2 = 7 (DIGINET_R_DESK_DISCONNECT), a0 = s, a1 = 0 (S_IDLE) and
   `jal set_state` (+0x484, return address +0x488). The stores are bytes of G in srx_wr (its inflight and
   desk_counter_valid rows), admitted by awr_ok_x; the world after them is slost_w1 Bs (lib/B/Prog/
   diginet_session_tick_cg.v), Bs = srx_w1 Bx now (two tw_writes of g_s), g_fail_next unchanged. set_state is called
   through its contract transport_set_state_cg (lib/B/Prog/set_state_cg.v) in the walk's own G journal with the
   class-1 frame live: the heap frame and the read-only bytes carried across the two stores (SrxBCallKit.v
   srxbk_tf_step, srxbk_rom_step), sstate_apart from srx_apart (sstate_wr (slost_w1 Bs) is a row of srx_wr), the
   class-2 count from srxb_fix. Run 2 is the `j` to the tick cut (+0x4c0), where the switch's result is set_state's
   world (srxb_sw_lost), and srxb_cur is folded across the stores (srxbk_cur_step) and the call (srxbk_cur_call). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import set_state_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_rx_cg SrxBCut SrxBCallKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.


(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac srxbl_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "srxbl_reg: no match for" T; fail
  end.

(* A register run 1 keeps: its value is the cut's (Elo: the run's valuation agrees with the entry's below 1024; EE
   reads the entry's atoms). *)
Ltac srxbl_keep1 HS Elo EE regs0 nn zn H :=
  srxbl_reg HS (Z_to_bv 5 zn) (YK11.getr regs0 (Z_to_bv 5 zn)) H
    ltac:(cbn [sv_denot]; rewrite (Elo nn ltac:(lia)), (EE nn (Z_to_bv 5 zn) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).

(* A register run 2 (no region) keeps. *)
Ltac srxbl_keep HS EE regs0 nn zn H :=
  srxbl_reg HS (Z_to_bv 5 zn) (YK11.getr regs0 (Z_to_bv 5 zn)) H
    ltac:(cbn [sv_denot]; rewrite (EE nn (Z_to_bv 5 zn) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).

(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac srxbl_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.

(* run 1's state at the arm cut: the two 4-byte fields of g_s it stores (based at s4, atom 20), the facts that s4 is
   g_s (64-aligned) and s11 (atom 27) the shadow base, the shadow entry of [s + 168, s + 216). *)
Definition srxbl_rg_dcv : YP09.region := YP09.mkRegion (Some 20%nat) 168 172 168 172 [].
Definition srxbl_rg_inf : YP09.region := YP09.mkRegion (Some 20%nat) 212 216 212 216 [].
Definition srxbl_facts : facts :=
  mkFacts [(20%nat, mkAF SRX_S SRX_S 6); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_srxbl : sstate := mkSS SRXB_LOST sr_atoms [srxbl_rg_dcv; srxbl_rg_inf] None srxbl_facts.
Definition SRXBL_SH : list shent := [mkSHE 20 168 216].
Definition SRXBL_Bx : sv := SOff 27 0.

(* The two fields the run stores. *)
Definition srxbl_Z (x : Z) : Prop := SRX_S + 168 <= x < SRX_S + 172 \/ SRX_S + 212 <= x < SRX_S + 216.

(* g_s's payload bytes are bytes of G. *)
Lemma srxbl_inG : forall a, SRX_S <= a < SRX_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
  intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, SRX_S in *; cbn [fst snd]; lia].
Qed.

Lemma srxbl_Z_G : forall a, srxbl_Z a -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply srxbl_inG. unfold srxbl_Z, TW.SZ_g_s in *. lia. Qed.

(* The two fields are srx_wr's inflight and desk_counter_valid rows. *)
Lemma srxbl_Z_wr : forall b a, srxbl_Z a -> srx_wr b a /\ inG TG.G_HARNESS_B a.
Proof.
  intros b a Ha. split; [|exact (srxbl_Z_G a Ha)].
  destruct Ha as [Ha | Ha].
  - do 9 right. left. unfold twb_fld, TW.A_S_desk_counter_valid, TW.OFF_g_s, SRX_S in *. lia.
  - do 8 right. left. unfold twb_fld, TW.A_S_inflight, TW.OFF_g_s, SRX_S in *. lia.
Qed.

(* The model's world after the two stores. *)
Lemma srxbl_w1_eq : forall Bw,
  slost_w1 Bw = TW.upd (TW.upd Bw (TW.OFF_g_s + 212) (TW.put 4 0)) (TW.OFF_g_s + 168) (TW.put 4 0).
Proof. intros Bw. reflexivity. Qed.

(* The two stores keep g_fail_next. *)
Lemma srxbl_w1_gfn : forall Bw, length Bw = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (slost_w1 Bw) = TW.g_fail_next Bw.
Proof.
intros Bw HL.
assert (LZ : Z.of_nat (length Bw) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
assert (L1 : Z.of_nat (length (TW.upd Bw TW.A_S_inflight (TW.put 4 0))) = TW.W_LEN).
{ rewrite TWL.length_upd_put; [exact LZ | unfold TW.A_S_inflight, TW.OFF_g_s; lia |].
  rewrite LZ. unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN. lia. }
unfold slost_w1, TW.set_S_desk_counter_valid, TW.set_S_inflight, TW.g_fail_next.
rewrite TWL.u_at_upd_out;
  [| unfold TW.A_S_desk_counter_valid, TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia
   | rewrite TWL.length_put; unfold TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.OFF_g_fail_next; lia
   | rewrite TWL.length_put, L1; unfold TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.W_LEN; lia].
rewrite TWL.u_at_upd_out;
  [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia
   | rewrite TWL.length_put; unfold TW.A_S_inflight, TW.OFF_g_s, TW.OFF_g_fail_next; lia
   | rewrite TWL.length_put, LZ; unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* The world relation after the stores of 0 at s + 212 and s + 168. *)
Lemma srxbl_tw_w1 : forall (rd rd' : Z -> option Z) Bw,
  tw_at TMAP_B rd Bw ->
  (forall j, 0 <= j < 4 -> rd' (SRX_S + 212 + j) = Some 0) ->
  (forall j, 0 <= j < 4 -> rd' (SRX_S + 168 + j) = Some 0) ->
  (forall x, tw_in TMAP_B x -> ~ (SRX_S + 212 <= x < SRX_S + 216) -> ~ (SRX_S + 168 <= x < SRX_S + 172) ->
     rd' x = rd x) ->
  tw_at TMAP_B rd' (slost_w1 Bw).
Proof.
intros rd rd' Bw Hat HI HD HO.
assert (CS : SRX_S = TB_g_s) by reflexivity.
set (rdm := fun x => if ((SRX_S + 168 <=? x) && (x <? SRX_S + 172))%bool then rd x else rd' x).
assert (H1 : tw_at TMAP_B rdm (TW.upd Bw (TW.OFF_g_s + 212) (TW.put 4 0))).
{ apply (tw_write TMAP_B rd rdm Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 212 4 0 TMAP_B_ok Hat TMAP_B_g_s);
    [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. unfold rdm. rewrite <- CS.
    assert (Hb : ((SRX_S + 168 <=? SRX_S + 212 + Z.of_nat j) && (SRX_S + 212 + Z.of_nat j <? SRX_S + 172))%bool
      = false) by (apply andb_false_iff; right; apply Z.ltb_ge; lia).
    rewrite Hb, (HI (Z.of_nat j) ltac:(lia)).
    destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
  - intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
    destruct ((SRX_S + 168 <=? x) && (x <? SRX_S + 172))%bool eqn:Eb; [reflexivity|].
    apply andb_false_iff in Eb.
    apply HO; [exact Hx | lia |].
    destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia. }
rewrite srxbl_w1_eq.
apply (tw_write TMAP_B rdm rd' _ TW.OFF_g_s TB_g_s TW.SZ_g_s 168 4 0 TMAP_B_ok H1 TMAP_B_g_s);
  [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. rewrite <- CS, (HD (Z.of_nat j) ltac:(lia)).
  destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
- intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
  destruct ((SRX_S + 168 <=? x) && (x <? SRX_S + 172))%bool eqn:Eb; [|reflexivity].
  apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  exfalso. apply Hn. lia.
Qed.

(* A region cell of n bytes holding 0, read byte by byte through the view. *)
Lemma srxbl_aview_of_val0 : forall H (m : word -> option byte) a (n : nat),
  val_mem tfibsegs (mrestrict H m) a n 0 -> forall j, 0 <= j < Z.of_nat n -> aview tfibsegs H m (a + j) = Some 0.
Proof.
intros H m a n HV j Hj. pose proof (HV (Z.to_nat j) ltac:(lia)) as H0.
rewrite Z2Nat.id in H0 by lia.
unfold aview. rewrite H0. cbn [option_map]. f_equal.
unfold YO0f.le_byte. rewrite Z.shiftr_0_l, Z.mod_0_l by lia. reflexivity.
Qed.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* run 1's entry: the two regions are writable bytes of G, the facts hold, the shadow entry of [s + 168, s + 216)
   holds at every AR state (g_s's zero shadow, trans_srx_cells' first conjunct). *)
Lemma srxbl_entry : forall ly S (W : world segs) regs mem md,
  trans_srx_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 20 = w64 SRX_S -> YK11.getr regs 27 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) ss_srxbl
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SRXB_LOST)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SRXBL_Bx SRXBL_SH (Eimg (PI := PI_transportb) (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md HSC HAR R20 R27.
set (E := Eimg (PI := PI_transportb) (Ereg regs [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (CS : SRX_S = 6157888) by reflexivity.
assert (U20 : bv_unsigned (ew E 20) = SRX_S)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_srxbl.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [srxbl_rg_dcv srxbl_rg_inf YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite U20.
    * split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (SRX_S + o) G_HARNESS_B_rw).
      apply srxbl_inG. unfold TW.SZ_g_s. lia.
    * split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (SRX_S + o) G_HARNESS_B_rw).
      apply srxbl_inG. unfold TW.SZ_g_s. lia.
  + apply pairwise_disjoint_of_extents.
    unfold srxbl_rg_dcv, srxbl_rg_inf, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U20. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + unfold srxbl_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U27.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- destruct HSC as (HZS & _).
  destruct (decode_zshadow_ra B ly S W mem md SRX_S (SRX_S + TW.SZ_g_s) (SRX_S + 168) 48 HAR HZS ltac:(lia)
    ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as [HRA _].
  assert (UB : U E SRXBL_Bx = SHADOW_OFF).
  { unfold U, SRXBL_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, SRXBL_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ SRXBL_Bx 20 (SRX_S + 168) 48 SRX_S 168 216 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. rewrite CS in Hx. unfold SHADOW_OFF. lia.
Qed.

Lemma srxbl_lost : @srxb_lost_stmt fx rc B MT.
Proof.
unfold srxb_lost_stmt. intros TICK. unfold srxb_lost_at, srxb_arm_at.
intros LAWS0 HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' Bx pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HRD HFRD HFB HTW HGF HINV HPRE HST HAFT HCMD HREGS.
pose proof LAWS0 as (HSM & HCELLS & HSC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HCALLS as (_ & _ & _ & _ & _ & _ & _ & HSSC & _).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & H13 & Hsp16 & Hlo & Hhi & Hnow & Hbuf0 & Hgb0 &
  Hsrc0 & Hoffb & Hbg & Htw0 & Hgf0 & Hm & HTF0 & Htfg & Hrom0 & Hap & Hinv0 & Hnd & Hc1 & Hc4 & Hc5 & Hc0 & Hc2 & Hev &
  Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HRD as (Hgb2 & Hsrc2 & HTF2 & Hrom2 & _).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22).
pose proof HCMD as (HCMD1 & HCMD2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (He0 : e = 0) by (rewrite srx_ev_zero in He; lia). subst e.
destruct (srxbk_sp1 (spZ regs) sp1 Hsp16 Esp1) as (Hsp1 & Hsp1m).
destruct (srxbk_ceil B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [Hce H47].
pose proof srxbk_stk_le as (HS176 & _ & HSA & _).
assert (EVA : SSTATE_EV = 0) by reflexivity.
unfold SRXB_FBYTES in HFc, HFapp.
assert (HLEN : length (srx_w1 Bx now) = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ HTW).
(* the model: the switch is the inlined session_lost, set_state at slost_w1 of the switch's world *)
destruct (TSS.set_state_m timg_B TF (slost_w1 (srx_w1 Bx now)) TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_DISCONNECT)
  as [[B2 []]|] eqn:EOA;
  pose proof (eq_trans (srxb_sw_lost timg_B TF (srx_w1 Bx now) b now HCMD1 HCMD2) EOA) as ESW;
  [| exfalso; rewrite (srxbk_after_none _ _ _ _ _ ESW) in HAFT; discriminate HAFT].
assert (HTM : TSS.diginet_session_tick_m timg_B TF B2 now = Some (Bw', r))
  by (rewrite <- (srxbk_after _ _ _ _ _ _ ESW); exact HAFT).
(* +0x448 .. +0x484: the checked stores of 0 at s + 212 and s + 168, a2 = 7, a0 = s, a1 = 0, `jal set_state` *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
destruct (srxbl_entry ly2 S2 W2 regs2 mem2 md2 HSC HAR2 R20 R27) as [HS SHOK].
set (E0 := Eimg (PI := PI_transportb) (Ereg regs2 [])) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = YK11.getr regs2 rr)
  by (intros n rr Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U20 : bv_unsigned (ew E0 20) = SRX_S)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; unfold SRX_S, TB_g_s; lia).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof HJ2 as HJ.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20 in Ha;
    apply srxbl_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20 in Ha;
    apply srxbl_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in *; clearbody md1 end.
lazymatch type of HS with context [restrict _ ?mz] => rename mz into ms1 end.
lazymatch type of HS with OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ _ =>
  set (E5 := EF) in * end.
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew E0 n)
  by (intros n Hn; unfold E5; first [reflexivity | rewrite !ew_ewset_other by lia; reflexivity]).
(* run 1 wrote g_s's fields at s + 168 and s + 212 only *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ srxbl_Z a ->
  aview segs (w_H W2) (ms_mem ms1) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ srxbl_Z HFr); [| exact Ha | exact Hn].
  intros bb wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U20 in Hx;
    unfold srxbl_Z; first [left; lia | right; lia] |]).
  destruct Hin. }
assert (GR1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
(* the two stores left 0 *)
srxbl_region HS 0%nat HRd. srxbl_region HS 1%nat HRi.
assert (U20f : bv_unsigned (ew E5 20) = SRX_S) by (rewrite E5lo by lia; exact U20).
assert (ZD : forall j, 0 <= j < 4 -> aview segs (w_H W2) (ms_mem ms1) (SRX_S + 168 + j) = Some 0).
{ apply (srxbl_aview_of_val0 (w_H W2) (ms_mem ms1) (SRX_S + 168) 4).
  exact (can_field_of_region E5 _ 20 SRX_S _ 168 172 168 172 168 4%N (SLit 0) 0 HRd U20f
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (ZI : forall j, 0 <= j < 4 -> aview segs (w_H W2) (ms_mem ms1) (SRX_S + 212 + j) = Some 0).
{ apply (srxbl_aview_of_val0 (w_H W2) (ms_mem ms1) (SRX_S + 212) 4).
  exact (can_field_of_region E5 _ 20 SRX_S _ 212 216 212 216 212 4%N (SLit 0) 0 HRi U20f
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
clear HRd HRi HF HFr HG.
(* the registers at `jal set_state` *)
srxbl_reg HS (Z_to_bv 5 10) (w64 SRX_S) Q10
  ltac:(cbn [sv_denot]; rewrite (E5lo 20%nat ltac:(lia)), (EE 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact R20).
srxbl_reg HS (Z_to_bv 5 11) (w64 TS0.DIGINET_S_IDLE) Q11 ltac:(reflexivity).
srxbl_reg HS (Z_to_bv 5 12) (w64 TS0.DIGINET_R_DESK_DISCONNECT) Q12 ltac:(reflexivity).
srxbl_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 26988)) Q1
  ltac:(apply codeptr_val; lazymatch goal with Hx : img_env _ _ E5 |- _ => exact Hx end).
srxbl_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (E5lo 2%nat ltac:(lia)), (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact R2).
srxbl_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (E5lo 3%nat ltac:(lia)), (EE 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
srxbl_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (E5lo 4%nat ltac:(lia)), (EE 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
srxbl_keep1 HS E5lo EE regs2 8%nat 8 Q8. srxbl_keep1 HS E5lo EE regs2 9%nat 9 Q9.
srxbl_keep1 HS E5lo EE regs2 18%nat 18 Q18. srxbl_keep1 HS E5lo EE regs2 19%nat 19 Q19.
srxbl_keep1 HS E5lo EE regs2 20%nat 20 Q20. srxbl_keep1 HS E5lo EE regs2 21%nat 21 Q21.
srxbl_keep1 HS E5lo EE regs2 22%nat 22 Q22. srxbl_keep1 HS E5lo EE regs2 25%nat 25 Q25.
srxbl_keep1 HS E5lo EE regs2 26%nat 26 Q26. srxbl_keep1 HS E5lo EE regs2 27%nat 27 Q27.
pmkst HS.
set (m1 := ms_mem ms1) in *.
set (regsC := ms_regs ms1) in *.
assert (USPC : spZ regsC = sp1)
  by (change (bv_unsigned (YK11.getr regsC (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
assert (EBN : BASE + 26988 = 0x87c0c) by (vm_compute; reflexivity).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_set_state) rg mm mdx) Qx) end.
(* the facts set_state's contract asks, at the call *)
assert (HWL : spZ regs - SRX_STK <= sp1 - SSTATE_STK) by lia.
assert (HTW1 : tw_at TMAP_B (aview segs (w_H W2) m1) (slost_w1 (srx_w1 Bx now))).
{ apply (srxbl_tw_w1 (aview segs (w_H W2) mem2) (aview segs (w_H W2) m1) (srx_w1 Bx now) HTW ZI ZD).
  intros x Hx H1 H2. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply K1; [lia|]. intros [X | X]; [exact (H2 X) | exact (H1 X)]. }
assert (HGF1 : TW.g_fail_next (slost_w1 (srx_w1 Bx now)) <= 1) by (rewrite (srxbl_w1_gfn _ HLEN); exact HGF).
assert (HTF1 : trans_tframe_at B ly2 S2 W2 m1 regs SRX_STK TF)
  by exact (srxbk_tf_step B LAWS HGX ly2 S2 W2 mem2 md2 m1 regs regs SRX_STK SRX_STK srxbl_Z TF HAR2 K1 srxbl_Z_G Htfg
    ltac:(lia) ltac:(lia) HTF2).
assert (HROM1 : trans_rom_view_rd W2 m1) by exact (srxbk_rom_step W2 mem2 m1 srxbl_Z K1 srxbl_Z_G Hrom2).
assert (HCUR1 : srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 m1 md1 0)
  by exact (srxbk_cur_step B MT LAWS HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF
    Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 m1 md1 srxbl_Z HFIX HCUR HJ K1 GR1 (srxbl_Z_wr b)).
assert (HAPS : sstate_apart TF (slost_w1 (srx_w1 Bx now)) TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_DISCONNECT).
{ intros x Hx fr Hfr. apply (Hap x); [|exact Hfr]. do 10 right. left. exists (srx_w1 Bx now). exact Hx. }
assert (HCNT : count_cid SSTATE_CID (frames S2) < fs_frames SSTATE_CID).
{ rewrite Hfrs, srxbk_count by (vm_compute; discriminate). change SSTATE_CID with ONDATA_CID. lia. }
(* the call of set_state (G form, the same journal) *)
eapply SRr_bind.
{ exact (HSSC fx STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 m1 md1 (k + 0) regsC
    TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_DISCONNECT TF (slost_w1 (srx_w1 Bx now)) B2 HJ
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, EBN; rewrite unsigned_lit_small by lia; lia)
    Q3 Q4 Q10 Q11 Q12
    ltac:(rewrite USPC; exact (srxbk_al16 sp1 Hsp1m))
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    HTW1 HGF1 EOA ltac:(unfold TS0.DIGINET_S_IDLE; lia) ltac:(unfold TS0.DIGINET_R_DESK_DISCONNECT; lia)
    (srxbk_tf_win B ly2 S2 W2 m1 regs regsC SRX_STK SSTATE_STK TF ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
       HTF1)
    HROM1 HAPS HCNT
    ltac:(rewrite EVA; rewrite srx_ev_zero in Hev; lia)). }
intros W3 c3 _ HPOST.
unfold transport_sstate_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3 &
  Hgf3).
assert (He30 : e3 = 0) by (rewrite EVA in He3; lia). subst e3.
rewrite USPC in HK3.
assert (HEw : forall a, sstate_wr (slost_w1 (srx_w1 Bx now)) TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_DISCONNECT a ->
  srx_wr b a /\ inG TG.G_HARNESS_B a).
{ intros a Ha. split; [|exact (srxbk_sstate_wr_G _ _ _ _ Ha)].
  do 10 right. left. exists (srx_w1 Bx now). exact Ha. }
(* +0x488: `j` to the tick cut *)
rewrite Q1.
pose proof (srxbk_entry W3 regs3 mem3 26988) as HS3.
set (E3 := Eimg (PI := PI_transportb) (Ereg regs3 [])) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E3 n = YK11.getr regs3 rr)
  by (intros n rr Hn; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof HJ3 as HJ4.
paj_run_to_tok RUNTO HS3 HJ4 SHOK3 (0, 0) SRXB_TICK.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md4 := mdx) in *; clearbody md4 end.
lazymatch type of HS3 with context [restrict _ ?mz] => rename mz into ms4 end.
pose proof (srxbk_mem_eq _ _ _ HF) as EM4.
clear HF HFr HG.
srxbl_keep HS3 EE3 regs3 2%nat 2 T2. srxbl_keep HS3 EE3 regs3 3%nat 3 T3. srxbl_keep HS3 EE3 regs3 4%nat 4 T4.
srxbl_keep HS3 EE3 regs3 8%nat 8 T8. srxbl_keep HS3 EE3 regs3 9%nat 9 T9.
srxbl_keep HS3 EE3 regs3 18%nat 18 T18. srxbl_keep HS3 EE3 regs3 19%nat 19 T19.
srxbl_keep HS3 EE3 regs3 20%nat 20 T20. srxbl_keep HS3 EE3 regs3 21%nat 21 T21.
srxbl_keep HS3 EE3 regs3 22%nat 22 T22. srxbl_keep HS3 EE3 regs3 25%nat 25 T25.
srxbl_keep HS3 EE3 regs3 26%nat 26 T26. srxbl_keep HS3 EE3 regs3 27%nat 27 T27.
pmkst HS3.
rewrite EM4 in HJ4 |- *.
replace (k + 0 + 0) with (k + 0) in HJ4 by lia.
(* the tick cut's facts *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
destruct (srxbk_ly B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (ELF2 & ELO2 & EHI2).
destruct (srxbk_ly B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as (ELF4 & ELO4 & EHI4).
assert (HCUR4 : srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly3 S3 W3 mem3 md4 0)
  by exact (srxbk_cur_call B MT LAWS FFL MTL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF
    Bw Bw' pos sp1 F ly2 S2 W2 m1 md1 ly3 S3 W3 mem3 md4 (sp1 - SSTATE_STK) sp1
    (sstate_wr (slost_w1 (srx_w1 Bx now)) TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_DISCONNECT)
    HFIX HCUR1 HJ4 Hfr3 Hperm3 HK3 Hmo3 HEw ltac:(lia) ltac:(unfold SRX_FRAME; lia)).
assert (HTF4 : trans_tframe_at B ly3 S3 W3 mem3 regs SRX_STK TF)
  by exact (srxbk_tf_kept B LAWS HGX HRU HRE ly2 S2 W2 m1 md1 ly3 S3 W3 mem3 md4 regs SRX_STK (sp1 - SSTATE_STK) sp1
    (sstate_wr (slost_w1 (srx_w1 Bx now)) TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_DISCONNECT) TF HAR1 HAR4 Hperm3 Hfr3
    ltac:(rewrite ELF4, ELF2; reflexivity) ltac:(rewrite ELO4, ELO2; reflexivity)
    ltac:(rewrite EHI4, EHI2; reflexivity) HK3
    (fun a Ha => proj2 (HEw a Ha)) (fun x Hx => Hap x (proj1 (HEw x Hx))) Htfg ltac:(lia) ltac:(lia) HTF1).
assert (HROM4 : trans_rom_view_rd W3 mem3) by exact (srxbk_rom_kept B HRU HRE _ _ _ _ _ _ _ _ _ HK3 HROM1).
assert (CH : forall n, acallee_saved n -> YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr regsC (Z_to_bv 5 n))
  by (intros n Hn; exact (HP3 n Hn)).
assert (HREGS4 : srxb_regs_base regs (ms_regs ms4) now sp1 F).
{ unfold srxb_regs_base, srxb_regs_core. split; [split|].
  - exact (eq_trans T2 (eq_trans (CH 2 ltac:(hnf; lia)) (eq_trans Q2 eq_refl))).
  - split; [exact (eq_trans T3 (eq_trans (CH 3 ltac:(hnf; lia)) (eq_trans Q3 (eq_sym Hgp))))|].
    split; [exact (eq_trans T4 (eq_trans (CH 4 ltac:(hnf; lia)) (eq_trans Q4 (eq_sym Htp))))|].
    split; [exact (eq_trans T8 (eq_trans (CH 8 ltac:(hnf; lia)) (eq_trans Q8 R8)))|].
    split; [exact (eq_trans T9 (eq_trans (CH 9 ltac:(hnf; lia)) (eq_trans Q9 R9)))|].
    split; [exact (eq_trans T18 (eq_trans (CH 18 ltac:(hnf; lia)) (eq_trans Q18 R18)))|].
    split; [exact (eq_trans T19 (eq_trans (CH 19 ltac:(hnf; lia)) (eq_trans Q19 R19)))|].
    split; [exact (eq_trans T20 (eq_trans (CH 20 ltac:(hnf; lia)) (eq_trans Q20 R20)))|].
    split; [exact (eq_trans T25 (eq_trans (CH 25 ltac:(hnf; lia)) (eq_trans Q25 R25)))|].
    split; [exact (eq_trans T26 (eq_trans (CH 26 ltac:(hnf; lia)) (eq_trans Q26 R26)))|].
    exact (eq_trans T27 (eq_trans (CH 27 ltac:(hnf; lia)) (eq_trans Q27 R27))).
  - split; [exact (eq_trans T21 (eq_trans (CH 21 ltac:(hnf; lia)) (eq_trans Q21 R21)))|].
    exact (eq_trans T22 (eq_trans (CH 22 ltac:(hnf; lia)) (eq_trans Q22 R22))). }
exact (TICK LAWS0 HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw'
  (srx_w1 Bx now) B2 pos sp1 F ly3 S3 W3 mem3 md4 0 (ms_regs ms4) HFIX HCUR4 HTF4 HROM4 Htw3 Hgf3 HLEN HINV ESW HTM
  HREGS4).
Qed.

End l.

Theorem srxb_lost_ok : forall fx rc B MT, @srxb_lost_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@srxbl_lost fx rc B MT). Qed.
