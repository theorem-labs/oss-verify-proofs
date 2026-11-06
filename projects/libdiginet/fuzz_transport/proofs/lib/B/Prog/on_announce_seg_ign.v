(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1441 of its 1599 lines of code are new or changed and 981 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/on_ack_seg_head.v, with its module names and numbers changed; 202 of its 322 lines of code are new or changed and 1479 lines of the source are left out. *)
(* on_announce_seg_ign: Lemma onann_ign_piece : onann_ign_stmt (lib/B/Prog/OnannCutB.v), the ignore path of the walk
   of on_announce on fuzz_transport.asan-ubsan, offsets +0x1ac .. +0x1dc of the listing lib/B/Prog/DgnTransportBList.v
   (AF_on_announce = 0x6a28; 0x87e74 .. 0x87ea4), then the release cut ONANN_AREL (+0x644, 0x8830c), which the
   onann_arel_at it is given closes.

   What the code does (diginet_session.c:188-189, the parse's code is not DIGINET_OK). +0x1ac `andi a0, s4, 7`,
   +0x1b0 `bne a0, zero, +0x774`: UBSan's alignment check of s; s4 = s = ONANN_S = 0x5df640 is 64-aligned (the run's
   atom fact of s4), so the trap word +0x774 is not reached. +0x1b4 `lui a0, 4`, +0x1b8 `addiw a0, a0, 1800`,
   +0x1bc `add a0, s4, a0`: a0 = s + 18184, g_s.stats.rx_ignored; +0x1c0 `srli a1, a0, 3`, +0x1c4 `add a1, a1, s8`,
   +0x1c8 `lbu a1, 0(a1)`: the shadow byte of the 8-byte access; +0x1cc `bne a1, zero, +0x894`: not taken, the shadow
   byte is 0 (g_s's payload lies in the record's zero shadow, on_announce_cg.v trans_onann_cells, read by
   DgnTransportBCg.v decode_zshadow_rd); +0x1d0 `ld a1, 0(a0)`, +0x1d4 `addi a1, a1, 1`, +0x1d8 `sd a1, 0(a0)`: the
   8-byte read-modify-write; +0x1dc `j +0x644`: the release cut.

   One run of the token engine over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_to_x, stopped at
   ONANN_AREL). The symbolic state: the registers at +0x1ac as atoms 0 .. 31 (s4 = atom 20, pinned to ONANN_S with
   alignment 2 ^ 6; s8 = atom 24, the shadow base), atom 32 the shadow base, atom 33 the 8 bytes at s + 18184
   (S_stats_rx_ignored Bw, by the world relation at the cut: TWorldG.v tw_read_val); one region over s4 covering
   [s + 18184, s + 18192), read and written; the shadow entry of that range. The bytes the run writes are bytes of G
   (W_journalG.v awr_ok_x_cons_g).

   At the release cut: the stored bytes are u64 (S_stats_rx_ignored Bw + 1), so the world relation holds at the
   model's world on this path, set_S_stats_rx_ignored Bw (u64 (S_stats_rx_ignored Bw + 1)) (on_announce_cg.v
   onann_model with onann_ign b = true), by TWorldG.v tw_write; g_fail_next lies outside the stored field
   (oni_fail_next). onann_cur is carried to the run's memory at e = 0: the run changed only [s + 18184, s + 18192),
   bytes of G in onann_wr Bw b (its first row, twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_rx_ignored 8), so the cut's
   acall_kept_g goes over the run by lib/A/Prog/TransportGFrame.v dk_kept_step_gw; the 13 saved words (in the stack,
   above alloc_ceiling) and the frame's last word (in the frame, not in the image: YCbq.v frm_img) are unchanged. The
   registers the release reads (onann_regs_rel) are the cut's: the run writes a0 and a1 only. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x1ac                                     *)
(* ------------------------------------------------------------------ *)

(* The 8 bytes of g_s.stats.rx_ignored at s + 18184 (s4, atom 20), read (atom 33) and written. *)
Definition oni_rg : YP09.region :=
  YP09.mkRegion (Some 20%nat) 18184 18192 18184 18192 [YP09.mkChunk 18184 (YP09.CVal 8 (SOff 33 0))].
(* s4 = s (64-aligned: UBSan's `andi a0, s4, 7` is 0) and s8 = the shadow base. *)
Definition oni_facts : facts :=
  mkFacts [(20%nat, mkAF ONANN_S ONANN_S 6); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_oni : sstate := mkSS ONANN_IGN sr_atoms [oni_rg] None oni_facts.
(* The shadow entry of the run's one check ([s + 18184, s + 18192)), and the shadow base s8. *)
Definition ONI_SH : list shent := [mkSHE 20 18184 18192].
Definition ONI_Bx : sv := SOff 24 0.

(* ------------------------------------------------------------------ *)
(* 2. The model's world after the store                                *)
(* ------------------------------------------------------------------ *)

(* The model's world on the ignore path (on_announce_cg.v onann_model). *)
Lemma oni_model : forall I Fr Bw b now Bw', onann_ign b = true ->
  TSS.on_announce_m I Fr Bw b now = Some (Bw', tt) ->
  Bw' = TW.set_S_stats_rx_ignored Bw (TS0.u64 (TW.S_stats_rx_ignored Bw + 1)).
Proof.
intros I Fr Bw b now Bw' Hi Hm. rewrite onann_model, Hi in Hm. symmetry. exact (onann_some_inv _ _ Hm).
Qed.

(* That world at the numeral offset of the field (OFF_g_s + 18152 + 32). *)
Lemma oni_wign_eq : forall Bw, TW.set_S_stats_rx_ignored Bw (TS0.u64 (TW.S_stats_rx_ignored Bw + 1)) =
  TW.upd Bw (TW.OFF_g_s + 18184) (TW.put 8 (TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8 + 1))).
Proof.
intros Bw. unfold TW.set_S_stats_rx_ignored, TW.S_stats_rx_ignored.
replace TW.A_S_stats_rx_ignored with (TW.OFF_g_s + 18184) by reflexivity. reflexivity.
Qed.

(* The store keeps g_fail_next (world offset 0xfdc8, outside [OFF_g_s + 18184, + 8)). *)
Lemma oni_fail_next : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  TW.g_fail_next (TW.set_S_stats_rx_ignored Bw (TS0.u64 (TW.S_stats_rx_ignored Bw + 1))) = TW.g_fail_next Bw.
Proof.
intros Bw HL. rewrite oni_wign_eq. unfold TW.g_fail_next.
apply TWL.u_at_upd_out; [unfold TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia | |].
- right. rewrite TWL.length_put. unfold TW.OFF_g_s, TW.OFF_g_fail_next. lia.
- rewrite TWL.length_put, HL. unfold TW.OFF_g_s, TW.W_LEN. lia.
Qed.

(* The length of a world the relation holds of. *)
Lemma oni_wlen : forall rd Bw, tw_at TMAP_B rd Bw -> Z.of_nat (length Bw) = TW.W_LEN.
Proof. intros rd Bw H. rewrite (tw_len _ _ _ H). unfold TW.W_LEN. lia. Qed.

(* A 64-bit literal is the literal of its wrap. *)
Lemma oni_bv_u64 : forall x, Z_to_bv 64 x = Z_to_bv 64 (TS0.u64 x).
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, TS0.u64.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia; reflexivity.
Qed.

(* The register and region readers of a symbolic state, as lib/B/Prog/DgnTransportBPaLib.v states them. *)
Ltac oni_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* A register the run does not write, at the run's end, from the equation Q of its value at the run's start: the
   run's valuation agrees with the start valuation below atom 1024 (Elo), which reads the registers (EE). *)
Ltac oni_kreg HS Elo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    oni_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (Elo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac oni_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac oni_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac oni_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.

Section ig. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* g_s's payload bytes are bytes of G. *)
Lemma oni_inG : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, ONANN_S, TB_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* g_s's bytes [s + 18184, s + 18192) are addressable at every AR state: a whole granule of the record's zero
   shadow. *)
Lemma oni_ra : forall ly S (W : world segs) mem md,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (ONANN_S + 18184) 8.
Proof.
intros ly S W mem md HZ HAR x Hx.
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

(* The run's valuation: the 32 registers at +0x1ac, the shadow base (atom 32) and the 8 bytes of
   g_s.stats.rx_ignored (atom 33). *)
Definition oni_E (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8)]).

(* The symbolic state at +0x1ac holds of the machine state there, and the run's shadow entry holds. *)
Lemma oni_entry : forall ly S (W : world segs) regs mem md Bw,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (oni_E regs Bw) ss_oni
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_IGN)) mem (YK11.seg_rom segs))) /\
  sh_ok segs ONI_Bx ONI_SH (oni_E regs Bw) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md Bw HSC HAR Htw R20 R24.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oni_E regs Bw) n = YK11.getr regs r)
  by (intros n r Hn; unfold oni_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew (oni_E regs Bw) 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8))
  by (unfold oni_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (U20 : bv_unsigned (ew (oni_E regs Bw) 20) = ONANN_S)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew (oni_E regs Bw) 24) = SHADOW_OFF)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R33 : 0 <= TW.u_at Bw (TW.OFF_g_s + 18184) 8 < 2 ^ 64) by exact (TWL.u_at_range Bw _ 8).
assert (U33 : bv_unsigned (ew (oni_E regs Bw) 33) = TW.u_at Bw (TW.OFF_g_s + 18184) 8)
  by (rewrite E33; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_oni.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold oni_rg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (ONANN_S + o) G_HARNESS_B_rw).
      apply oni_inG. unfold TW.SZ_g_s. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val segs _ _ ONANN_S 18184 8 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 18184) 8));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 18184 8 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold oni_rg, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold oni_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U24.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (oni_ra ly S W mem md HSC HAR) as HRA.
  assert (UB : U (oni_E regs Bw) ONI_Bx = SHADOW_OFF).
  { unfold U, ONI_Bx. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, ONI_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ ONI_Bx 20 (ONANN_S + 18184) 8 ONANN_S 18184 18192 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The bytes of a value in memory, read byte by byte through the view. *)
Lemma oni_aview_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v -> forall j, (j < n)%nat ->
  aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma onann_ign_piece : @onann_ign_stmt fx rc B MT.
Proof.
unfold onann_ign_stmt, onann_ign_at.
intros REL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof HLAWS as (_ & _ & HSC & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & _ & HGX & _).
pose proof HFIX as (HJe & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _ & _ & _ & Hfn & Hm & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & HFa & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL) & Htw2 & Hig).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25) & R20 & R24).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (CS' : ONANN_S = TB_g_s) by reflexivity.
unfold ONANN_FBYTES in HFc, HFapp, HFL.
(* the call's window lies above alloc_ceiling, below 2 ^ 47 *)
pose proof HJe as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4304 <= ONANN_STK).
{ unfold ONANN_STK, ONANN_FRAME, ONANN_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
assert (Hsp : alloc_ceiling <= spZ regs - 104 /\ spZ regs <= 2 ^ 47) by lia.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (Hin2 : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof (oni_model _ _ _ _ _ _ Hig Hm) as EBw'.
pose proof (oni_wlen _ _ Htw2) as HWL.
(* +0x1ac .. +0x1dc: s & 7 (not the trap word), the check of s + 18184, the load, + 1, the store, `j`; the run stops
   at the release cut. *)
destruct (oni_entry ly2 S2 W2 regs2 mem2 md2 Bw HSC HAR2 Htw2 R20 R24) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (oni_E regs2 Bw)) by (unfold oni_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oni_E regs2 Bw) n = YK11.getr regs2 r)
  by (intros n r Hn; unfold oni_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U20c : bv_unsigned (ew (oni_E regs2 Bw) 20) = ONANN_S)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (E33 : ew (oni_E regs2 Bw) 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8))
  by (unfold oni_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (R33 : 0 <= TW.u_at Bw (TW.OFF_g_s + 18184) 8 < 2 ^ 64) by exact (TWL.u_at_range Bw _ 8).
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan ONANN_AREL.
{ oni_awr_rs.
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20c in Ha;
    apply oni_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E5 := EF) in HS; rename mf into msF end.
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew (oni_E regs2 Bw) n)
  by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
(* the registers the release reads, at the cut *)
oni_kreg HS E5lo EE (2%bv : bv 5) 2%nat R2 X2. oni_kreg HS E5lo EE (3%bv : bv 5) 3%nat R3 X3.
oni_kreg HS E5lo EE (4%bv : bv 5) 4%nat R4 X4. oni_kreg HS E5lo EE (8%bv : bv 5) 8%nat R8 X8.
oni_kreg HS E5lo EE (9%bv : bv 5) 9%nat R9 X9. oni_kreg HS E5lo EE (18%bv : bv 5) 18%nat R18 X18.
oni_kreg HS E5lo EE (19%bv : bv 5) 19%nat R19 X19. oni_kreg HS E5lo EE (25%bv : bv 5) 25%nat R25 X25.
(* the run wrote [s + 18184, s + 18192) only *)
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (ONANN_S + 18184 <= a < ONANN_S + 18192) ->
  aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => ONANN_S + 18184 <= x < ONANN_S + 18192) HFr1);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U20c in Hx; lia |]).
  destruct Hin. }
assert (GR : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msF) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG1 Ha)).
(* the stored bytes: u64 (S_stats_rx_ignored Bw + 1) *)
oni_region HS 0%nat HR.
assert (U20f : bv_unsigned (ew E5 20) = ONANN_S) by (rewrite E5lo by lia; exact U20c).
assert (E33f : ew E5 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8)) by (rewrite E5lo by lia; exact E33).
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ [YP09.mkChunk _ (CVal _ ?e)]) =>
  assert (DEN : sv_denot E5 e = Z_to_bv 64 (TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8 + 1)));
  [ cbn [sv_denot]; rewrite E33f, unsigned_lit_small by lia; apply oni_bv_u64
  | pose proof (can_field_of_region E5 _ 20 ONANN_S _ 18184 18192 18184 18192 18184 8%N e
      (TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8 + 1)) HR U20f ltac:(oni_in) DEN
      ltac:(unfold TS0.u64; change (8 * Z.of_N 8) with 64; apply Z.mod_pos_bound; lia) ltac:(cbn; lia)) as VB ]
end.
change (N.to_nat 8) with 8%nat in VB.
clear HR DEN.
(* the world relation at the model's world *)
assert (TWn : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msF))
  (TW.set_S_stats_rx_ignored Bw (TS0.u64 (TW.S_stats_rx_ignored Bw + 1)))).
{ rewrite oni_wign_eq.
  apply (tw_write TMAP_B (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem msF)) Bw TW.OFF_g_s TB_g_s
    TW.SZ_g_s 18184 8 _ TMAP_B_ok Htw2 TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. rewrite <- CS'. exact (oni_aview_of_val _ _ _ 8 _ VB j Hj).
  - intros x Hx Hn.
    assert (Hg : inG TG.G_HARNESS_B x).
    { destruct Hx as (o & b0 & n & Hin & Hb). pose proof (TMAP_B_in_G o b0 n Hin) as HG0.
      unfold inG. apply Exists_exists. exists (b0, n). split; [exact HG0 | unfold in_zr; cbn [fst snd]; lia]. }
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX Hg) as Hl. unfold kLowMemEnd in Hl.
    apply KF; [lia|]. intros X. apply Hn. lia. }
(* what the call keeps, over the run *)
assert (KG : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (ms_mem msF) (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (TransportGFrame.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2
    (ms_mem msF) (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)
    (fun x => ONANN_S + 18184 <= x < ONANN_S + 18192) HARc HK KF GR).
  - intros a Hz Hc. cbv beta in Hz. exfalso. lia.
  - intros b0 m i _ _ Hz. cbv beta in Hz. left. unfold twb_fld, TW.A_S_stats_rx_ignored, TW.OFF_g_s. lia.
  - intros a Hz _ HnG _ _. cbv beta in Hz. exfalso. apply HnG. apply oni_inG. unfold TW.SZ_g_s. lia.
  - intros c p a _ _ Hz. cbv beta in Hz. left. unfold twb_fld, TW.A_S_stats_rx_ignored, TW.OFF_g_s. lia. }
(* the thirteen saved words, at the run's memory *)
assert (HSVn : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) (ms_mem msF)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSV o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KF; lia. }
(* the frame's last word, at the run's memory *)
assert (HFLn : rdword (aview segs (w_H W2) (ms_mem msF)) (F + 512 - 8) = Some (flag_addr lyc ONANN_CID pos)).
{ rewrite <- HFL. apply YCbq.rdword_ext. intros i Hi. apply KF; [lia|]. intros X.
  assert (Hg : inG TG.G_HARNESS_B (F + 512 - 8 + i)) by (apply oni_inG; unfold TW.SZ_g_s; lia).
  destruct (HGX _ Hg) as [HiG _].
  apply (frm_img segs B LAWS _ _ _ _ _ ONANN_CID pos (F + 512 - 8 + i) HAR2 Hin2); [|exact HiG].
  replace (frame_addr ly2 ONANN_CID pos) with F by (rewrite HFa; unfold frame_addr; rewrite HlyF; reflexivity).
  rewrite onann_fbytes. unfold ONANN_FBYTES. lia. }
(* the release cut *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_AREL)) mm rom) mdx) Q) end.
apply (REL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 (ms_mem msF) _ 0 (ms_regs msF) HFIX).
- unfold onann_rel_cur, onann_cur.
  refine (conj (conj HJ (conj He (conj Hfrs (conj Hperm (conj HlyF (conj HMO (conj KG (conj HSVn _))))))))
    (conj _ _)).
  + unfold ONANN_FBYTES. exact HFLn.
  + rewrite EBw'. exact TWn.
  + rewrite EBw', (oni_fail_next Bw HWL). exact Hfn.
- exact (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X19 X25))))))).
Qed.
End ig.

Print Assumptions onann_ign_piece.
