(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 418 of its 499 lines of code are new or changed and 684 lines of the source are left out. *)
(* on_announce_seg_sl2: Lemma onann_sl2_piece : onann_sl2_stmt (lib/B/Prog/OnannCutB.v), the second inlined
   session_lost of the walk of on_announce on fuzz_transport.asan-ubsan, offsets +0x5b4 .. +0x5f0 of the listing
   lib/B/Prog/DgnTransportBList.v (AF_on_announce = 0x6a28; 0x8827c .. 0x882b8), then the release cut ONANN_FNREL
   (+0x5f4, 0x882bc), which the onann_fnrel_at it is given closes.

   What the code does (diginet_session.c:220, session_lost's :162-164 inlined). +0x5b4 `addi a0, s4, 212`,
   +0x5b8 `srli a1, a0, 3`, +0x5bc `add a1, a1, s8`, +0x5c0 `lb a1, 0(a1)`: the shadow byte of the 4-byte store at
   s + 212 (g_s.inflight); +0x5c4 `bne a1, zero, +0x874`: not taken, that shadow byte is 0 (g_s's payload lies in
   the record's zero shadow, on_announce_cg.v trans_onann_cells, read by DgnTransportBCg.v decode_zshadow_rd);
   +0x5c8 `sw zero, 212(s4)` (:162). +0x5cc .. +0x5d8 the same check for s + 168 (g_s.desk_counter_valid) and
   +0x5e0 `sw zero, 168(s4)` (:163). The world after the two stores is diginet_session_tick_cg.v slost_w1 B3.
   +0x5e4 `li a2, 5` (DIGINET_R_FOREIGN), +0x5e8 `mv a0, s4` (s), +0x5ec `li a1, 0` (DIGINET_S_IDLE),
   +0x5f0 `jal set_state` (0x872cc = transportb_sigma TB_set_state), return address 0x882bc = ONANN_FNREL (:164).

   One run of the token engine over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_x), stopped at the
   call. The symbolic state at +0x5b4: the registers as atoms 0 .. 31 (s4 = atom 20, pinned to ONANN_S with
   alignment 2 ^ 6, so the shifted shadow addresses are the record's; s8 = atom 24, the shadow base); two written
   regions over s4, [s + 212, s + 216) and [s + 168, s + 172); the shadow entries of the two checks. The bytes the
   run writes are bytes of G (W_journalG.v awr_ok_x_cons_g).

   At the call, premise by premise (set_state_cg.v transport_set_state_cg, a G-form callee in this same journal;
   on_announce_cg.v's header, the set_state paragraph): the journal at the run's memory (the own frame owned);
   ra = ONANN_FNREL (DgnTransportBPaLib.v ret_ok_codeptr_v); gp, tp, sp and the callee-saved registers kept by the
   run; a0 = s = SSTATE_S, a1 = 0 = DIGINET_S_IDLE, a2 = 5 = DIGINET_R_FOREIGN; sp = sp1, 32-aligned, and
   ONANN_STK >= 208 + SSTATE_STK places set_state's window inside on_announce's; tw_at at slost_w1 B3 (TWorldG.v
   tw_write of the two stores, through the intermediate reader sl2_V1); g_fail_next of it (the kit's onann_gfn_upd,
   twice); the model premise by diginet_session_tick_cg.v slost_model_sstate from the cut's session_lost_m;
   trans_tframe_at and trans_rom_view_rd at the run's memory (the kit's onann_tf_cur / onann_rom_cur at the cut's
   facts carried over the run); sstate_apart from onann_apart (the kit's onann_apart_sstate: sstate_wr reads its
   world through S_state and GOT.n only, and B3 has Bw's, by the kit's onann_same chain Bw -> onann_w1 ->
   set_GOT_desk -> set_S_foreign -> set_GOT_foreign); count_cid SSTATE_CID at the call state = count_cid
   SENDCTL_CID (frames Sc) < fs_frames SENDCTL_CID (the own frame is of class 3); no event (SSTATE_EV = 0).

   Its post folds into onann_cur by TransportGCg.v dk_kept_trans_nf_g (its written range sstate_wr (slost_w1 B3)
   S_IDLE R_FOREIGN lies in onann_wr Bw b: the kit's onann_wr_slost), the saved words and the frame's last word by
   its kept clauses, and the walk falls into onann_fnrel_at at +0x5f4 with the model's world Bw' and
   g_fail_next Bw' <= 1 from set_state's X.

   Trap and error paths on this piece: the slow paths of the two checks (`bne a1, zero` at +0x5c4 to +0x874 and at
   +0x5dc to +0x884): their shadow bytes are 0 (trans_onann_cells). This piece passes no UBSan trap word. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x5b4                                     *)
(* ------------------------------------------------------------------ *)

(* The two 4-byte stores of 0, over s4 (atom 20): g_s.inflight at s + 212, g_s.desk_counter_valid at s + 168.
   Neither range is read, so neither region carries a chunk at the entry. *)
Definition sl2_rg_in : YP09.region := YP09.mkRegion (Some 20%nat) 212 216 212 216 [].
Definition sl2_rg_dcv : YP09.region := YP09.mkRegion (Some 20%nat) 168 172 168 172 [].
(* s4 = s (64-aligned) and s8 = the shadow base. *)
Definition sl2_facts : facts :=
  mkFacts [(20%nat, mkAF ONANN_S ONANN_S 6); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_sl2 : sstate := mkSS ONANN_SL2 sr_atoms [sl2_rg_in; sl2_rg_dcv] None sl2_facts.
(* The shadow entries of the run's two checks, and the shadow base s8. *)
Definition SL2_SH : list shent := [mkSHE 20 212 216; mkSHE 20 168 172].
Definition SL2_Bx : sv := SOff 24 0.

(* ------------------------------------------------------------------ *)
(* 2. The world after the two stores                                   *)
(* ------------------------------------------------------------------ *)

(* diginet_session_tick_cg.v slost_w1 at the numeral offsets of the two fields (OFF_g_s + 212, OFF_g_s + 168). *)
Lemma sl2_w1_eq : forall X,
  slost_w1 X = TW.upd (TW.upd X (TW.OFF_g_s + 212) (TW.put 4 0)) (TW.OFF_g_s + 168) (TW.put 4 0).
Proof. intros X. reflexivity. Qed.

(* The length of a world the relation holds of, as the kit's lemmas ask for it. *)
Lemma sl2_wlen : forall rd Bw, tw_at TMAP_B rd Bw -> length Bw = Z.to_nat TW.W_LEN.
Proof. intros rd Bw H. exact (tw_len _ _ _ H). Qed.

(* The bytes of a value in memory, read byte by byte through the view. *)
Lemma sl2_aview_of_val : forall (segsx : list Segment) H (m : word -> option byte) a (n : nat) v,
  val_mem segsx (mrestrict H m) a n v -> forall j, (j < n)%nat ->
  aview segsx H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros segsx H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* The register and region readers of a symbolic state (on_announce_seg_ign.v's), also in the form a run leaves at a
   call (st_ok at the callee's pc; on_ack_seg_aft.v's oaf_reg / oaf_region). *)
Ltac sl2_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Register r of the machine state of HS, whose symbolic value is atom n, the start value of register rn (Q its
   value): the run's valuation agrees with the start valuation below atom 1024 (Elo), which reads the registers. *)
Ltac sl2_kreg_of HS Elo EE r n rn Q H :=
  lazymatch type of Q with _ = ?v =>
    sl2_reg HS r v H
      ltac:(cbn [sv_denot]; try rewrite (Elo n ltac:(lia)); rewrite (EE n rn eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
            exact Q) end.
Ltac sl2_kreg HS Elo EE r n Q H := sl2_kreg_of HS Elo EE r n r Q H.
Ltac sl2_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac sl2_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac sl2_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The model of the goal, named. *)
Ltac sl2_name_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md := m) in *; clearbody md end.

Section sl. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* g_s's payload bytes are bytes of G. *)
Lemma sl2_inG : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, ONANN_S, TB_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* A 4-byte range of g_s's payload is addressable at every AR state: its granules lie in the record's zero
   shadow. *)
Lemma sl2_ra : forall ly S (W : world segs) mem md d,
  trans_onann_cells B -> @AR rc segs B ly S W mem md -> 0 <= d -> d + 4 <= TW.SZ_g_s ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (ONANN_S + d) 4.
Proof.
intros ly S W mem md d HZ HAR Hd0 Hd1 x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : ONANN_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= ONANN_S + TW.SZ_g_s)
  by (unfold ONANN_S, TB_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The run's valuation: the 32 registers at +0x5b4 (the run reads no world byte). *)
Definition sl2_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

(* The symbolic state at +0x5b4 holds of the machine state there, and the run's two shadow entries hold. *)
Lemma sl2_entry : forall ly S (W : world segs) regs mem md,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (sl2_E regs) ss_sl2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_SL2)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SL2_Bx SL2_SH (sl2_E regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md HSC HAR R20 R24.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (sl2_E regs) n = YK11.getr regs r)
  by (intros n r Hn; unfold sl2_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (U20 : bv_unsigned (ew (sl2_E regs) 20) = ONANN_S)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew (sl2_E regs) 24) = SHADOW_OFF)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_sl2.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold sl2_rg_in, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (ONANN_S + o) G_HARNESS_B_rw).
      apply sl2_inG. unfold TW.SZ_g_s. lia.
    * unfold sl2_rg_dcv, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (ONANN_S + o) G_HARNESS_B_rw).
      apply sl2_inG. unfold TW.SZ_g_s. lia.
  + apply pairwise_disjoint_of_extents.
    unfold sl2_rg_in, sl2_rg_dcv, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U20. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + unfold sl2_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U24.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- assert (UB : U (sl2_E regs) SL2_Bx = SHADOW_OFF).
  { unfold U, SL2_Bx. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  assert (U20u : U (sl2_E regs) (SOff 20 0) = ONANN_S)
    by (unfold U; cbn [sv_denot]; rewrite U20, Z.add_0_r; apply unsigned_lit_small; lia).
  unfold sh_ok, SL2_SH. constructor; [|constructor; [|constructor]].
  + pose proof (sl2_ra ly S W mem md 212 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as HRA.
    apply (shent_ok_of_range segs (w_H W) mem _ SL2_Bx 20 (ONANN_S + 212) 4 ONANN_S 212 216 HRA UB U20u);
      [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
  + pose proof (sl2_ra ly S W mem md 168 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as HRA.
    apply (shent_ok_of_range segs (w_H W) mem _ SL2_Bx 20 (ONANN_S + 168) 4 ONANN_S 168 172 HRA UB U20u);
      [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Lemma onann_sl2_holds : @onann_sl2_stmt fx rc B MT.
Proof.
unfold onann_sl2_stmt, onann_sl2_at.
intros FNREL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  B2 B3 ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof HLAWS as (_ & _ & HSC & _ & _ & HROU & HRNE & LAWS & MTL & _ & _ & _ & FFL & HGX & _).
pose proof HCALL as (_ & _ & _ & _ & _ & _ & HSS & _).
pose proof HFIX as (HJe & _ & _ & Hgp & Htp & _ & _ & _ & Hsp16 & Hlo & Hhi & _ & _ & Htw0 & _ & _ & _ & _ & _ &
  Hapart & _ & _ & _ & Hcnt2 & Hnev & Esp1 & HFa & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HCUR0 & Htw3 & Hb2 & Hcn3 & Hfg & _ & Hmod & Hgf3).
pose proof HCUR0 as (HJ & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25) & R20 & R24).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct He as [_ HEV].
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (CS' : ONANN_S = TB_g_s) by reflexivity.
assert (EVS : SSTATE_EV = 0) by reflexivity.
assert (ESTK : 208 + SSTATE_STK <= ONANN_STK) by (vm_compute; discriminate).
assert (EFN : ONANN_FNREL = 28700) by reflexivity.
unfold ONANN_FBYTES in HFc, HFapp, HFL.
(* the call's window lies above alloc_ceiling, below 2 ^ 47 *)
pose proof HJe as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyc & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4304 <= ONANN_STK).
{ unfold ONANN_STK, ONANN_FRAME, ONANN_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
assert (Hspc : alloc_ceiling <= spZ regs - ONANN_STK) by lia.
assert (Hsp47 : spZ regs <= 2 ^ 47) by lia.
(* the realigned sp1 *)
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold ONANN_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult. }
destruct Hsp1 as [Hsp1 Hsp132].
assert (Hsp116 : sp1 mod 16 = 0).
{ pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp132, Z.add_0_r in D. rewrite D.
  replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
(* the states, the own frame *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (Hin2 : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFAll : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite HlyF; reflexivity).
assert (EFA2 : frame_addr ly2 ONANN_CID pos = F) by (rewrite EFAll; symmetry; exact HFa).
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (TransportGFrame.dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F
  (flag_addr lyc ONANN_CID pos) HAR2 Hfrs Hbl2 HlyF HFa eq_refl FFL) as (N1 & N2 & N3 & N4).
assert (FNG : forall a, F <= a < F + 512 -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha HGa. destruct (HGX a HGa) as [HiG _].
  exact (frm_img segs B LAWS _ _ _ _ _ ONANN_CID pos a HAR2 Hin2
    ltac:(rewrite EFA2, onann_fbytes; unfold ONANN_FBYTES; lia) HiG). }
(* the worlds: B3 has Bw's state and GOT.n (the kit's onann_same chain) *)
pose proof (sl2_wlen _ _ Htw0) as HLw.
pose proof (sl2_wlen _ _ Htw3) as HL3.
destruct Hb2 as (_ & d2 & EB2).
destruct Hfg as (d3 & EB3).
assert (S1 : onann_same Bw (onann_w1 timg_B Bw b)) by exact (onann_same_w1 timg_B Bw b HLw).
assert (L1 : length (onann_w1 timg_B Bw b) = Z.to_nat TW.W_LEN) by exact (onann_w1_len timg_B Bw b HLw).
assert (S2w : onann_same (onann_w1 timg_B Bw b) B2) by (rewrite EB2; exact (onann_same_desk _ d2 L1)).
assert (L2 : length B2 = Z.to_nat TW.W_LEN) by (destruct S2w as (Eq & _); rewrite Eq; exact L1).
assert (S3w : onann_same B2 (TW.set_S_foreign B2 1)) by exact (onann_same_foreign B2 1 L2).
assert (L3f : length (TW.set_S_foreign B2 1) = Z.to_nat TW.W_LEN)
  by (destruct S3w as (Eq & _); rewrite Eq; exact L2).
assert (S4w : onann_same (TW.set_S_foreign B2 1) B3) by (rewrite EB3; exact (onann_same_gforeign _ d3 L3f)).
assert (SW : onann_same Bw B3)
  by exact (onann_same_trans _ _ _ S1 (onann_same_trans _ _ _ S2w (onann_same_trans _ _ _ S3w S4w))).
destruct SW as (_ & Est & _ & _ & _ & _ & Egn & _ & _).
clear S1 S2w S3w S4w.
(* the model: session_lost_m is set_state_m at slost_w1 B3 *)
rewrite slost_model_sstate in Hmod.
(* +0x5b4 .. +0x5f0: the two checked stores of 0, then the call of set_state *)
destruct (sl2_entry ly2 S2 W2 regs2 mem2 md2 HSC HAR2 R20 R24) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (sl2_E regs2)) by (unfold sl2_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (sl2_E regs2) n = YK11.getr regs2 r)
  by (intros n r Hn; unfold sl2_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U20c : bv_unsigned (ew (sl2_E regs2) 20) = ONANN_S)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ sl2_awr_rs.
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20c in Ha;
    apply sl2_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20c in Ha;
    apply sl2_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_nil. }
sl2_name_md mdW.
rename HF into HF1, HFr into HFr1, HG into HG1.
lazymatch type of HS with
| st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E5 := EF) in HS; rename mf into msW
| OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ (restrict _ ?mf) =>
    set (E5 := EF) in HS; rename mf into msW
end.
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew (sl2_E regs2) n)
  by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
(* the registers at set_state's entry *)
sl2_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 28700)) W1 ltac:(apply codeptr_val; assumption).
sl2_reg HS (11%bv : bv 5) (Z_to_bv 64 0) W11 ltac:(reflexivity).
sl2_reg HS (12%bv : bv 5) (Z_to_bv 64 5) W12 ltac:(reflexivity).
sl2_kreg_of HS E5lo EE (10%bv : bv 5) 20%nat (20%bv : bv 5) R20 W10.
sl2_kreg HS E5lo EE (2%bv : bv 5) 2%nat R2 W2'. sl2_kreg HS E5lo EE (3%bv : bv 5) 3%nat R3 W3'.
sl2_kreg HS E5lo EE (4%bv : bv 5) 4%nat R4 W4'. sl2_kreg HS E5lo EE (8%bv : bv 5) 8%nat R8 W8'.
sl2_kreg HS E5lo EE (9%bv : bv 5) 9%nat R9 W9'. sl2_kreg HS E5lo EE (18%bv : bv 5) 18%nat R18 W18'.
sl2_kreg HS E5lo EE (19%bv : bv 5) 19%nat R19 W19'. sl2_kreg HS E5lo EE (25%bv : bv 5) 25%nat R25 W25'.
(* the run wrote [s + 212, s + 216) and [s + 168, s + 172) only *)
assert (KF : forall a, 0 <= a < 2 ^ 64 ->
  ~ (ONANN_S + 212 <= a < ONANN_S + 216) -> ~ (ONANN_S + 168 <= a < ONANN_S + 172) ->
  aview segs (w_H W2) (ms_mem msW) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn1 Hn2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (ONANN_S + 212 <= x < ONANN_S + 216) \/
                                           (ONANN_S + 168 <= x < ONANN_S + 172)) HFr1);
    [| exact Ha | intros [Hx | Hx]; [exact (Hn1 Hx) | exact (Hn2 Hx)]].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin];
          [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U20c in Hx;
           first [left; lia | right; lia] |]).
  destruct Hin. }
assert (GR : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msW) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG1 Ha)).
assert (KFb : forall a, 0 <= a < 2 ^ 64 ->
  ~ (TB_g_s + 212 <= a < TB_g_s + 216) -> ~ (TB_g_s + 168 <= a < TB_g_s + 172) ->
  aview segs (w_H W2) (ms_mem msW) a = aview segs (w_H W2) mem2 a) by (rewrite <- CS'; exact KF).
(* the two stored values *)
assert (U20f : bv_unsigned (ew E5 20) = ONANN_S) by (rewrite E5lo by lia; exact U20c).
sl2_region HS 0%nat HR0.
lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ [YP09.mkChunk _ (CVal _ ?ev)]) =>
  assert (DEN0 : sv_denot E5 ev = Z_to_bv 64 0) by (cbn [sv_denot]; reflexivity);
  pose proof (can_field_of_region E5 _ 20 ONANN_S _ 212 216 212 216 212 4%N ev 0 HR0 U20f ltac:(sl2_in) DEN0
    ltac:(cbn; lia) ltac:(cbn; lia)) as VB212
end.
sl2_region HS 1%nat HR1.
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ [YP09.mkChunk _ (CVal _ ?ev)]) =>
  assert (DEN1 : sv_denot E5 ev = Z_to_bv 64 0) by (cbn [sv_denot]; reflexivity);
  pose proof (can_field_of_region E5 _ 20 ONANN_S _ 168 172 168 172 168 4%N ev 0 HR1 U20f ltac:(sl2_in) DEN1
    ltac:(cbn; lia) ltac:(cbn; lia)) as VB168
end.
change (N.to_nat 4) with 4%nat in VB212, VB168.
clear HR0 HR1 DEN0 DEN1.
set (mW := ms_mem msW) in *. set (rW := ms_regs msW) in *.
(* the world relation at slost_w1 B3, through the reader that keeps [s + 168, s + 172) at the cut's memory *)
pose (V1 := fun a : Z => if ((TB_g_s + 168 <=? a) && (a <? TB_g_s + 172))%bool
                         then aview segs (w_H W2) mem2 a else aview segs (w_H W2) mW a).
assert (V1out : forall x, ~ (TB_g_s + 168 <= x < TB_g_s + 172) -> V1 x = aview segs (w_H W2) mW x).
{ intros x Hx. unfold V1.
  destruct (Z.leb_spec (TB_g_s + 168) x) as [H1|H1]; destruct (Z.ltb_spec x (TB_g_s + 172)) as [H2|H2];
    cbn [andb]; first [reflexivity | exfalso; apply Hx; lia]. }
assert (V1in : forall x, TB_g_s + 168 <= x < TB_g_s + 172 -> V1 x = aview segs (w_H W2) mem2 x).
{ intros x Hx. unfold V1.
  destruct (Z.leb_spec (TB_g_s + 168) x) as [H1|H1]; destruct (Z.ltb_spec x (TB_g_s + 172)) as [H2|H2];
    cbn [andb]; first [reflexivity | exfalso; lia]. }
assert (TW1 : tw_at TMAP_B V1 (TW.upd B3 (TW.OFF_g_s + 212) (TW.put 4 0))).
{ apply (tw_write TMAP_B (aview segs (w_H W2) mem2) V1 B3 TW.OFF_g_s TB_g_s TW.SZ_g_s 212 4 0
    TMAP_B_ok Htw3 TMAP_B_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  - intros j Hj. rewrite V1out by lia. rewrite <- CS'.
    exact (sl2_aview_of_val segs _ _ _ 4 _ VB212 j Hj).
  - intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh.
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    destruct (Z_le_gt_dec (TB_g_s + 168) x) as [H1|H1]; [destruct (Z_lt_ge_dec x (TB_g_s + 172)) as [H2|H2]|].
    + rewrite V1in by lia. reflexivity.
    + rewrite V1out by lia. apply KFb; lia.
    + rewrite V1out by lia. apply KFb; lia. }
assert (TWw : tw_at TMAP_B (aview segs (w_H W2) mW) (slost_w1 B3)).
{ rewrite sl2_w1_eq.
  apply (tw_write TMAP_B V1 (aview segs (w_H W2) mW) (TW.upd B3 (TW.OFF_g_s + 212) (TW.put 4 0))
    TW.OFF_g_s TB_g_s TW.SZ_g_s 168 4 0 TMAP_B_ok TW1 TMAP_B_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  - intros j Hj. rewrite <- CS'. exact (sl2_aview_of_val segs _ _ _ 4 _ VB168 j Hj).
  - intros x Hx Hn. rewrite V1out by lia. reflexivity. }
(* onann_cur at the call's memory *)
assert (KG : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mW (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (TransportGFrame.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2
    mW (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)
    (fun x => (ONANN_S + 212 <= x < ONANN_S + 216) \/ (ONANN_S + 168 <= x < ONANN_S + 172)) HARc HK).
  - intros a Ha Hn. apply KF;
      [exact Ha | intros Hx; apply Hn; left; exact Hx | intros Hx; apply Hn; right; exact Hx].
  - exact GR.
  - intros a Hz Hc. cbv beta in Hz. exfalso. destruct Hz as [Hz|Hz]; lia.
  - intros b0 m i _ _ Hz. cbv beta in Hz. destruct Hz as [Hz|Hz].
    + apply onann_wr_inflight. unfold twb_fld, TW.A_S_inflight, TW.OFF_g_s. unfold ONANN_S in Hz. lia.
    + apply onann_wr_dcv. unfold twb_fld, TW.A_S_desk_counter_valid, TW.OFF_g_s. unfold ONANN_S in Hz. lia.
  - intros a Hz _ HnG _ _. cbv beta in Hz. exfalso. apply HnG. apply sl2_inG.
    destruct Hz as [Hz|Hz]; unfold TW.SZ_g_s; lia.
  - intros c p a _ _ Hz. cbv beta in Hz. destruct Hz as [Hz|Hz].
    + apply onann_wr_inflight. unfold twb_fld, TW.A_S_inflight, TW.OFF_g_s. unfold ONANN_S in Hz. lia.
    + apply onann_wr_dcv. unfold twb_fld, TW.A_S_desk_counter_valid, TW.OFF_g_s. unfold ONANN_S in Hz. lia. }
assert (HSVw : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mW) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSV o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KF; lia. }
assert (HFLw : rdword (aview segs (w_H W2) mW) (F + 512 - 8) = Some (flag_addr lyc ONANN_CID pos)).
{ rewrite <- HFL. apply YCbq.rdword_ext. intros i Hi. apply KF; [lia| |]; intros X;
    [ apply (FNG (F + 512 - 8 + i)); [lia | apply sl2_inG; unfold TW.SZ_g_s; lia]
    | apply (FNG (F + 512 - 8 + i)); [lia | apply sl2_inG; unfold TW.SZ_g_s; lia] ]. }
assert (CURW : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F
  ly2 S2 W2 mW mdW 0).
{ unfold onann_cur.
  refine (conj HJ (conj (conj (Z.le_refl 0) HEV) (conj Hfrs (conj Hperm (conj HlyF (conj HMO (conj KG
    (conj HSVw _)))))))).
  unfold ONANN_FBYTES. exact HFLw. }
(* set_state's premises *)
assert (NSP : spZ rW = sp1) by (unfold spZ; rewrite W2'; unfold w64; apply unsigned_lit_small; lia).
assert (EBR : BASE + 28700 = 0x882bc) by (vm_compute; reflexivity).
assert (Pret : YK0s.ret_ok (YK11.getr rW 1))
  by (rewrite W1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity]).
assert (Pra4 : 4096 <= raZ rW) by (unfold raZ; rewrite W1, EBR, unsigned_lit_small by lia; lia).
assert (Pgp : YK11.getr rW 3 = w64 (as_gp B)) by (rewrite W3'; exact Hgp).
assert (Ptp : YK11.getr rW 4 = w64 (as_tp B)) by (rewrite W4'; exact Htp).
assert (Pa0 : YK11.getr rW 10 = w64 SSTATE_S) by (rewrite W10; reflexivity).
assert (Pa1 : YK11.getr rW 11 = w64 TS0.DIGINET_S_IDLE) by (rewrite W11; reflexivity).
assert (Pa2 : YK11.getr rW 12 = w64 TS0.DIGINET_R_FOREIGN) by (rewrite W12; reflexivity).
assert (Psp16 : spZ rW mod 16 = 0) by (rewrite NSP; exact Hsp116).
assert (Pwin1 : sp0 - STK <= spZ rW - SSTATE_STK) by (rewrite NSP; lia).
assert (Pwin2 : spZ rW <= sp0) by (rewrite NSP; lia).
assert (Pgf : TW.g_fail_next (slost_w1 B3) <= 1).
{ rewrite sl2_w1_eq.
  rewrite (onann_gfn_upd (TW.upd B3 (TW.OFF_g_s + 212) (TW.put 4 0)) (TW.OFF_g_s + 168) 4 0
    (onann_upd_len B3 (TW.OFF_g_s + 212) 4 0 HL3 ltac:(unfold TW.OFF_g_s; lia)
       ltac:(unfold TW.OFF_g_s, TW.W_LEN; lia))
    ltac:(left; split; [unfold TW.OFF_g_s; lia | unfold TW.SZ_g_s; lia])).
  rewrite (onann_gfn_upd B3 (TW.OFF_g_s + 212) 4 0 HL3
    ltac:(left; split; [unfold TW.OFF_g_s; lia | unfold TW.SZ_g_s; lia])).
  exact Hgf3. }
assert (Pst : 0 <= TS0.DIGINET_S_IDLE < 2 ^ 31) by (unfold TS0.DIGINET_S_IDLE; lia).
assert (Pwhy : 0 <= TS0.DIGINET_R_FOREIGN < 2 ^ 31) by (unfold TS0.DIGINET_R_FOREIGN; lia).
assert (Ptf : trans_tframe_at B ly2 S2 W2 mW rW SSTATE_STK TF).
{ exact (onann_tf_cur B MT HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF
    Bw Bw' pos sp1 F ly2 S2 W2 mW mdW 0 rW SSTATE_STK HFIX CURW ltac:(rewrite NSP; lia) ltac:(rewrite NSP; lia)). }
assert (Prom : trans_rom_view_rd W2 mW).
{ exact (onann_rom_cur B MT HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF
    Bw Bw' pos sp1 F ly2 S2 W2 mW mdW 0 HFIX CURW). }
assert (Pap : sstate_apart TF (slost_w1 B3) TS0.DIGINET_S_IDLE TS0.DIGINET_R_FOREIGN)
  by exact (onann_apart_sstate TF Bw b B3 TS0.DIGINET_R_FOREIGN HL3 HLw Egn Est Hapart).
assert (Pcnt : count_cid SSTATE_CID (frames S2) < fs_frames SSTATE_CID).
{ pose proof onann_cid_callees as (_ & ESC & ESS & _ & _ & _).
  rewrite Hfrs, ESS, ESC. rewrite ESC in Hcnt2.
  replace (count_cid 2 ((ONANN_CID, pos) :: frames Sc)) with (count_cid 2 (frames Sc))
    by (unfold ONANN_CID; reflexivity).
  lia. }
assert (Pnev : st_nev S + (k + 0) + SSTATE_EV <= EV_MAX) by (rewrite EVS; lia).
(* +0x5f0: the call of set_state, in the same G journal *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sg (transportb_sigma TB_set_state) rg mm mdx) Q) end.
eapply SRr_bind.
{ exact (HSS fx STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mW mdW (k + 0) rW
    TS0.DIGINET_S_IDLE TS0.DIGINET_R_FOREIGN TF (slost_w1 B3) Bw'
    (proj1 CURW) Pret Pra4 Pgp Ptp Pa0 Pa1 Pa2 Psp16 Pwin1 Pwin2 TWw Pgf Hmod Pst Pwhy Ptf Prom Pap Pcnt Pnev). }
intros W3 c3 _ HPOST.
unfold transport_sstate_post, transport_cg_post in HPOST.
destruct HPOST as (ly3 & S3 & regs5 & mem5 & md6 & e' & -> & He' & HJ6 & HP6 & Hfr6 & Hperm6 & HK6 & Hmo6 & Htw6 &
  Hgf6).
rewrite NSP in HK6.
(* the state set_state returned: the cut's facts there *)
assert (ELF3 : ly_F ly3 = ly_F lyc).
{ pose proof HJ6 as (_ & _ & (memS6 & HJ6i & _) & _). pose proof HJ6i as (_ & Hly3 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & E3 & _). pose proof Hlyc as (_ & _ & _ & _ & _ & Ec & _).
  rewrite E3, Ec. reflexivity. }
assert (K5 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem5 (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 mW W3 mem5
    (spZ regs - ONANN_STK) (spZ regs) (sp1 - SSTATE_STK) sp1 (onann_wr Bw b)
    (sstate_wr (slost_w1 B3) TS0.DIGINET_S_IDLE TS0.DIGINET_R_FOREIGN)
    (dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos))
    Hspc ltac:(lia) EFAll ltac:(intros f Hf; rewrite Hfrs; right; exact Hf) Hbl2 N1 N3 KG HK6).
  - lia.
  - lia.
  - intros a Ha. left. exact (onann_wr_slost Bw b B3 TS0.DIGINET_R_FOREIGN a HL3 HLw Egn Est Ha). }
assert (HSV5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem5) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSVw o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. destruct HK6 as (L1' & _). apply L1'; lia. }
assert (HFL5 : rdword (aview segs (w_H W3) mem5) (F + 512 - 8) = Some (flag_addr lyc ONANN_CID pos)).
{ rewrite <- HFLw. apply YCbq.rdword_ext. intros i Hi. destruct HK6 as (_ & _ & _ & L4 & _).
  apply (L4 ONANN_CID pos (F + 512 - 8 + i) Hin2).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA2, onann_fbytes. unfold ONANN_FBYTES. lia.
  - intros Hw. exact (FNG (F + 512 - 8 + i) ltac:(lia) (onann_sstate_wr_G _ _ _ _ Hw)). }
(* the release cut +0x5f4 *)
rewrite W1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_FNREL)) mm rom) mdx) Q) end.
apply (FNREL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly3 S3 W3 mem5 md6 (0 + e') regs5 HFIX).
- unfold onann_rel_cur, onann_cur.
  refine (conj (conj _ (conj _ (conj _ (conj _ (conj ELF3 (conj _ (conj K5 (conj HSV5 _))))))))
    (conj Htw6 Hgf6)).
  + replace (k + (0 + e')) with (k + 0 + e') by lia. exact HJ6.
  + rewrite EVS in He'. lia.
  + rewrite Hfr6. exact Hfrs.
  + exact (Permutation_trans Hperm6 Hperm).
  + exact (mo_le_trans MT MTL Sc S2 S3 0 0 HMO Hmo6).
  + unfold ONANN_FBYTES. exact HFL5.
- unfold onann_regs_rel.
  split; [exact (eq_trans (HP6 2 ltac:(hnf; lia)) W2')|].
  split; [exact (eq_trans (HP6 3 ltac:(hnf; lia)) W3')|].
  split; [exact (eq_trans (HP6 4 ltac:(hnf; lia)) W4')|].
  split; [exact (eq_trans (HP6 8 ltac:(hnf; lia)) W8')|].
  split; [exact (eq_trans (HP6 9 ltac:(hnf; lia)) W9')|].
  split; [exact (eq_trans (HP6 18 ltac:(hnf; lia)) W18')|].
  split; [exact (eq_trans (HP6 19 ltac:(hnf; lia)) W19')|].
  exact (eq_trans (HP6 25 ltac:(hnf; lia)) W25').
Qed.
End sl.

(* The second inlined session_lost of the walk of on_announce (OnannCutB.v onann_sl2_stmt), at every machine, run
   ceiling, record and meter. *)
Lemma onann_sl2_piece : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT, @onann_sl2_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@onann_sl2_holds fx rc B MT). Qed.

Print Assumptions onann_sl2_piece.
