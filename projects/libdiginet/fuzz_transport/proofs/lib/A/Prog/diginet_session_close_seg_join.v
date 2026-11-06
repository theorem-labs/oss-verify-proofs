(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths and module names changed; 522 of its 576 lines of code are new or changed and 1085 lines of the source are left out. *)
(* diginet_session_close_seg_join: Lemma close_join : close_join_stmt (lib/A/Prog/diginet_session_close_segs.v), the
   join piece of diginet_session_close, offsets +0x18c .. +0x1bc of the listing lib/A/Prog/DgnTransportList.v
   (fuzz_transport.asan 0x872c8 .. 0x872f8), reached from the head (close_go Bw false, a3 = 0) and from the send
   piece (a3 = the result of send_control).

   What the code does. +0x18c `addi a0, s3, 212` and the instrumented check of the 4-byte store at s + 212 (its
   shadow byte is 0: trans_close_cells), +0x1a0 `sw zero, 212(s3)`: g_s.inflight := 0, so the world is close_w1 B1;
   +0x1a4 `srli s10, s5, 3` / `add s10, s10, s9`: s10 = the shadow address of s + 112; the check of the 4-byte load
   there, +0x1b4 `lw s11, 0(s5)`: s11 = S_state (close_w1 B1), sign-extended; +0x1b8 `li s4, 3`;
   +0x1bc `beq s11, s4`: S_CLOSED goes to the release cut (close_rel_at, where the model's world is close_w1 B1:
   close_rel_model), any other state to the notice cut (close_ntc_at).

   One run of the token engine (lib/A/Prog/TransportGRunA.v paj_run_x) covers +0x18c .. +0x1b8 and stops at the
   branch, which lib/A/Prog/TransportGRunA.v paj_branch takes from a state with no region; each arm then runs one
   instruction to its cut (paj_run_to_x). The only byte the piece writes is g_s.inflight, a byte of G inside
   close_wr TF Bw, so what the call keeps carries over the run by lib/A/Prog/TransportGFrame.v dk_kept_nfz_gw. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_close_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_close_segs diginet_session_close_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The branch at +0x1bc, and the two symbolic states: at the cut (the two g_s fields as regions of s3) and at the
   branch (every register an atom, no region). *)
Definition CLOSE_JBR : Z := AF_diginet_session_close + 0x1bc.
Definition cj_rg_inf : YP09.region := YP09.mkRegion (Some 19%nat) 212 216 212 216 [].
Definition cj_rg_st : YP09.region :=
  YP09.mkRegion (Some 21%nat) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 33 0))].
Definition cj_facts : facts :=
  mkFacts [(19%nat, mkAF CLOSE_S CLOSE_S 6); (21%nat, mkAF (CLOSE_S + 112) (CLOSE_S + 112) 4);
           (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition cj_ss : sstate := mkSS CLOSE_JOIN sr_atoms [cj_rg_inf; cj_rg_st] None cj_facts.
Definition cj_ss_br : sstate := mkSS CLOSE_JBR sr_atoms [] None (mkFacts [] [] []).
Definition CJ_SH : list shent := [mkSHE 19 112 216; mkSHE 21 0 4].
Definition CJ_Bx : sv := SOff 25 0.
Definition CJ_B0 : Z * Z := (0, 0).

(* Two 32-bit signed values are equal as 64-bit words exactly when they are equal. *)
Lemma cj_eqb : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= w < 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
intros v w Hv Hw. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64).
assert (Em : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> x mod 2 ^ 64 = if x <? 0 then x + 2 ^ 64 else x).
{ intros x Hx. destruct (Z.ltb_spec x 0) as [Hn | Hn].
  - symmetry. apply (Z.mod_unique x (2 ^ 64) (-1) (x + 2 ^ 64)); lia.
  - apply Z.mod_small. lia. }
rewrite (Em v Hv), (Em w Hw).
destruct (Z.ltb_spec v 0) as [V | V]; destruct (Z.ltb_spec w 0) as [Wq | Wq];
  apply Bool.eq_iff_eq_true; rewrite !Z.eqb_eq; split; intros HH; lia.
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma cj_inG : forall a, CLOSE_S <= a < CLOSE_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. apply (close_inG_row TA_g_s TW.SZ_g_s a).
- exact (TMAP_A_in_G _ _ _ TMAP_A_g_s).
- unfold CLOSE_S in Ha. exact Ha.
Qed.

(* The world after the store of 0 at s + 212. *)
Lemma cj_tw_w1 : forall (rd rd' : Z -> option Z) B1,
  tw_at TMAP_A rd B1 ->
  (forall j, 0 <= j < 4 -> rd' (CLOSE_S + 212 + j) = Some 0) ->
  (forall x, tw_in TMAP_A x -> ~ (CLOSE_S + 212 <= x < CLOSE_S + 216) -> rd' x = rd x) ->
  tw_at TMAP_A rd' (close_w1 B1).
Proof.
intros rd rd' B1 Hat HI HO.
assert (CS : CLOSE_S = TA_g_s) by reflexivity.
rewrite close_w1_eq.
apply (tw_write TMAP_A rd rd' B1 TW.OFF_g_s TA_g_s TW.SZ_g_s 212 4 0 TMAP_A_ok Hat TMAP_A_g_s);
  [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. rewrite <- CS, (HI (Z.of_nat j) ltac:(lia)).
  destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
- intros x Hx Hn. rewrite <- CS in Hn. apply HO; [exact Hx | lia].
Qed.

(* g_s's state is not the field the store writes. *)
Lemma cj_state_eq : forall B1, length B1 = Z.to_nat TW.W_LEN ->
  TW.S_state (close_w1 B1) = TW.S_state B1 /\
  TW.u_at (close_w1 B1) (TW.OFF_g_s + 112) 4 = TW.u_at B1 (TW.OFF_g_s + 112) 4.
Proof.
intros B1 L. unfold close_w1, TW.set_S_inflight, TW.S_state, TW.s32_at, TW.A_S_state.
rewrite !(rd_upd_W B1 (TW.put 4 0) TW.A_S_inflight) by wside. split; reflexivity.
Qed.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac cj_reg HS r v H tac :=
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

Section join. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition cj_E (regs : bvmap 5 word) (B1 : list byte) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at B1 (TW.OFF_g_s + 112) 4)]).
Definition cj_E0 (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).

Lemma cj_ew_reg : forall regs B1 n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cj_E regs B1) n = YK11.getr regs r.
Proof. intros regs B1 n r Hn. unfold cj_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma cj_ew_reg0 : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cj_E0 regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold cj_E0. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma cj_env_img : forall regs B1, img_env VAL A_LIM (cj_E regs B1).
Proof. intros regs B1. unfold cj_E. apply Eimg_env. Qed.
Lemma cj_env_img0 : forall regs, img_env VAL A_LIM (cj_E0 regs).
Proof. intros regs. unfold cj_E0. apply Eimg_env. Qed.

(* g_s's bytes [s + 112, s + 216) are addressable at every AR state: whole granules of the record's zero shadow. *)
Lemma cj_ra : forall ly S (W : world segs) mem md,
  trans_close_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (CLOSE_S + 112) 104.
Proof.
intros ly S W mem md HZ HAR x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : CLOSE_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= CLOSE_S + TW.SZ_g_s)
  by (unfold CLOSE_S, TA_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md CLOSE_S (CLOSE_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The symbolic state at the cut holds of the machine state there. *)
Lemma cj_entry : forall ly S (W : world segs) regs mem md B1,
  trans_close_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) B1 ->
  YK11.getr regs 19 = w64 CLOSE_S -> YK11.getr regs 21 = w64 (CLOSE_S + 112) ->
  YK11.getr regs 25 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (cj_E regs B1) cj_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CLOSE_JOIN)) mem (YK11.seg_rom segs))) /\
  sh_ok segs CJ_Bx CJ_SH (cj_E regs B1) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md B1 HSC HAR Htw R19 R21 R25.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cj_E regs B1) n = YK11.getr regs r)
  by (intros n r Hn; apply cj_ew_reg; exact Hn).
assert (E32 : ew (cj_E regs B1) 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold cj_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (cj_E regs B1) 33 = Z_to_bv 64 (TW.u_at B1 (TW.OFF_g_s + 112) 4))
  by (unfold cj_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (CS : CLOSE_S = 6158784) by reflexivity.
assert (U19 : bv_unsigned (ew (cj_E regs B1) 19) = CLOSE_S)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew (cj_E regs B1) 21) = CLOSE_S + 112)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew (cj_E regs B1) 25) = SHADOW_OFF)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R33 : 0 <= TW.u_at B1 (TW.OFF_g_s + 112) 4 < 2 ^ 32) by exact (TWL.u_at_range B1 _ 4).
assert (U33 : bv_unsigned (ew (cj_E regs B1) 33) = TW.u_at B1 (TW.OFF_g_s + 112) 4)
  by (rewrite E33; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew (cj_E regs B1) 32) = SHADOW_OFF)
  by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold cj_ss.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [cj_rg_inf cj_rg_st YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (CLOSE_S + o) G_HARNESS_rw).
      apply cj_inG. unfold TW.SZ_g_s. lia.
    * rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ (CLOSE_S + 112) 0 4 (SOff 33 0) (TW.u_at B1 (TW.OFF_g_s + 112) 4));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
      exact (tw_read_val segs _ TMAP_A B1 TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold cj_rg_inf, cj_rg_st, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U19, U21. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + unfold cj_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U21, U25, U33.
    change (2 ^ 6) with 64. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (cj_ra ly S W mem md HSC HAR) as HRA.
  assert (UB : U (cj_E regs B1) CJ_Bx = SHADOW_OFF).
  { unfold U, CJ_Bx. cbn [sv_denot]. rewrite U25, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, CJ_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range segs (w_H W) mem _ CJ_Bx 19 (CLOSE_S + 112) 104 CLOSE_S 112 216 HRA UB).
    * unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range segs (w_H W) mem _ CJ_Bx 21 (CLOSE_S + 112) 104 (CLOSE_S + 112) 0 4 HRA UB).
    * unfold U. cbn [sv_denot]. rewrite U21, Z.add_0_r. apply unsigned_lit_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* A symbolic state with no region holds of any machine state at its pc. *)
Lemma cj_entry0 : forall (W : world segs) regs mem (pc : Z),
  st_ok_pi segs VAL (cj_E0 regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

Lemma close_join : @close_join_stmt fx rc B MT.
Proof.
unfold close_join_stmt. intros NTC REL. unfold close_join_at.
intros LAWS0 HMS HN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' B1 pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HSCELLS & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE & HGU & HGN).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTF &
  Hrom & Hapart & Htfg & Hinv1 & Hinv4 & Hcnt & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & HS1 & Htw1 & Hgf1).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R21 & R25) & R13).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold CLOSE_FBYTES in HFc, HFapp, HFLw.
assert (ECE : CLOSE_EV = 0) by reflexivity.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof (bv_unsigned_in_range 64 (YK11.getr regs 2)) as HspR.
change (bv_modulus 64) with (2 ^ 64) in HspR. change (bv_unsigned (YK11.getr regs 2)) with (spZ regs) in HspR.
assert (HBS : 4272 <= CLOSE_STK).
{ unfold CLOSE_STK, CLOSE_FRAME, CLOSE_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hmx; assert (Hax : a = 4096) by reflexivity end.
  lia. }
assert (Hin : In (CLOSE_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
set (FL := flag_addr lyc CLOSE_CID pos) in *.
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
(* the lengths and the state the load reads *)
assert (HLB : length B1 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw1).
destruct (cj_state_eq B1 HLB) as [EST EU].
assert (Hrange : - 2 ^ 31 <= TW.S_state B1 < 2 ^ 31) by (unfold TW.S_state; apply TWL.s32_range).
(* ---- +0x18c .. +0x1b8: the checked store, the checked load, s4 = 3 ---- *)
destruct (cj_entry ly2 S2 W2 regs2 mem2 md2 B1 HSCELLS HAR2 Htw1 R19 R21 R25) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (cj_E regs2 B1)) by apply cj_env_img.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
assert (U19c : bv_unsigned (ew (cj_E regs2 B1) 19) = CLOSE_S)
  by (rewrite (cj_ew_reg regs2 B1 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small;
      unfold CLOSE_S, TA_g_s; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CLOSE_JOIN)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
paj_run_tok RUN HS HJ1 SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19c in Ha;
    apply cj_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
(* the run wrote g_s.inflight only *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (CLOSE_S + 212 <= a < CLOSE_S + 216) ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => CLOSE_S + 212 <= x < CLOSE_S + 216) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin' Hx.
  lazymatch type of Hin' with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin' end.
  cbn [In] in Hin'.
  repeat (destruct Hin' as [Hin' | Hin']; [injection Hin' as <- <- <-; cbn [base_val] in Hx;
    rewrite ?U19c in Hx; lia |]).
  destruct Hin'. }
assert (GRo : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the store left 0 *)
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in * end.
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew (cj_E regs2 B1) n)
  by (intros n Hn; unfold E1; rewrite !ew_ewset_other by lia; reflexivity).
assert (U19f : bv_unsigned (ew E1 19) = CLOSE_S) by (rewrite E1lo by lia; exact U19c).
assert (ZI : forall j, 0 <= j < 4 -> aview segs (w_H W2) (ms_mem ms) (CLOSE_S + 212 + j) = Some 0).
{ intros j Hj.
  assert (HV : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (CLOSE_S + 212) 4 0)
    by exact (can_field_of_region E1 _ 19 CLOSE_S _ 212 216 212 216 212 4%N (SLit 0) 0 RG0 U19f
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  pose proof (HV (Z.to_nat j) ltac:(lia)) as H0. rewrite Z2Nat.id in H0 by lia.
  unfold aview. rewrite H0. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  lazymatch goal with |- context [?f 0 4%nat (Z.to_nat j)] => unfold f end.
  rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity. }
clear RG0.
(* the world at the memory of the branch *)
assert (TW1 : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms)) (close_w1 B1)).
{ apply (cj_tw_w1 (aview segs (w_H W2) mem2) _ B1 Htw1 ZI).
  intros x Hx Hn. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR; [lia | exact Hn]. }
(* the registers at the branch *)
cj_reg HS (2%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 2)) P2
  ltac:(cbn [sv_denot]; rewrite (E1lo 2%nat ltac:(lia)), (cj_ew_reg regs2 B1 2%nat (Z_to_bv 5 2) eq_refl),
        Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HS (3%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 3)) P3
  ltac:(cbn [sv_denot]; rewrite (E1lo 3%nat ltac:(lia)), (cj_ew_reg regs2 B1 3%nat (Z_to_bv 5 3) eq_refl),
        Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HS (4%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 4)) P4
  ltac:(cbn [sv_denot]; rewrite (E1lo 4%nat ltac:(lia)), (cj_ew_reg regs2 B1 4%nat (Z_to_bv 5 4) eq_refl),
        Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HS (8%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 8)) P8
  ltac:(cbn [sv_denot]; rewrite (E1lo 8%nat ltac:(lia)), (cj_ew_reg regs2 B1 8%nat (Z_to_bv 5 8) eq_refl),
        Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HS (9%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 9)) P9
  ltac:(cbn [sv_denot]; rewrite (E1lo 9%nat ltac:(lia)), (cj_ew_reg regs2 B1 9%nat (Z_to_bv 5 9) eq_refl),
        Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HS (13%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 13)) P13
  ltac:(cbn [sv_denot]; rewrite (E1lo 13%nat ltac:(lia)), (cj_ew_reg regs2 B1 13%nat (Z_to_bv 5 13) eq_refl),
        Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HS (18%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 18)) P18
  ltac:(cbn [sv_denot]; rewrite (E1lo 18%nat ltac:(lia)), (cj_ew_reg regs2 B1 18%nat (Z_to_bv 5 18) eq_refl),
        Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HS (19%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 19)) P19
  ltac:(cbn [sv_denot]; rewrite (E1lo 19%nat ltac:(lia)), (cj_ew_reg regs2 B1 19%nat (Z_to_bv 5 19) eq_refl),
        Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HS (23%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 23)) P23
  ltac:(cbn [sv_denot]; rewrite (E1lo 23%nat ltac:(lia)), (cj_ew_reg regs2 B1 23%nat (Z_to_bv 5 23) eq_refl),
        Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HS (24%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 24)) P24
  ltac:(cbn [sv_denot]; rewrite (E1lo 24%nat ltac:(lia)), (cj_ew_reg regs2 B1 24%nat (Z_to_bv 5 24) eq_refl),
        Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HS (25%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 25)) P25
  ltac:(cbn [sv_denot]; rewrite (E1lo 25%nat ltac:(lia)), (cj_ew_reg regs2 B1 25%nat (Z_to_bv 5 25) eq_refl),
        Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HS (20%bv : bv 5) (w64 3) P20 ltac:(reflexivity).
cj_reg HS (26%bv : bv 5) (w64 (SHADOW_OFF + (CLOSE_S + 112) / 8)) P26
  ltac:(cbn [sv_denot]; rewrite (E1lo 21%nat ltac:(lia)), (E1lo 25%nat ltac:(lia)),
        (cj_ew_reg regs2 B1 21%nat 21%bv eq_refl), (cj_ew_reg regs2 B1 25%nat 25%bv eq_refl),
        R21, R25; unfold w64, CLOSE_S, TA_g_s, SHADOW_OFF; vm_compute; reflexivity).
assert (E33f : ew E1 33 = Z_to_bv 64 (TW.u_at B1 (TW.OFF_g_s + 112) 4)).
{ rewrite E1lo by lia. unfold cj_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ _ 1). }
cj_reg HS (27%bv : bv 5) (Z_to_bv 64 (TW.S_state B1)) P27
  ltac:(cbn [sv_denot]; rewrite E33f;
        pose proof (TWL.u_at_range B1 (TW.OFF_g_s + 112) 4) as Rr;
        rewrite unsigned_lit_small by (cbn in Rr |- *; lia); rewrite Z.add_0_r;
        rewrite LMem.sext_small, LMem.signed_of_extract by (cbn in Rr |- *; lia);
        rewrite unsigned_lit_small by (cbn in Rr |- *; lia); reflexivity).
(* what the call keeps, at the memory of the branch *)
assert (KCJ : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem ms) (spZ regs - CLOSE_STK) (spZ regs)
  (close_wr TF Bw)).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2
    (ms_mem ms) (spZ regs - CLOSE_STK) (spZ regs) CLOSE_CID pos F FL (close_wr TF Bw)
    (fun x => CLOSE_S + 212 <= x < CLOSE_S + 216)
    HGX HARc HAR2 Hfrs Hbl HlyF EF eq_refl FFL ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; right; right; apply cj_inG; unfold TW.SZ_g_s in *; lia) HK
    ltac:(intros a Ha Hn; exact (KR a Ha Hn)) GRo). }
(* the saved words and the frame's last word, at that memory *)
assert (HSo : forall o, In o CLOSE_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold CLOSE_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
assert (HFWj : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) (ms_mem ms)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) CLOSE_SAVED).
{ rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
  pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KR; [lia | unfold CLOSE_S, TA_g_s; lia]. }
assert (HFLj : rdword (aview segs (w_H W2) (ms_mem ms)) (F + CLOSE_FBYTES - 8) = Some FL).
{ rewrite <- HFLw. apply rdword_ext. intros i Hi. apply KR; [unfold CLOSE_FBYTES in *; lia|].
  intros Hx. destruct Hx as [Hx1 Hx2].
  apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 CLOSE_CID pos (F + CLOSE_FBYTES - 8 + i) HAR2 Hin);
    [replace (frame_addr ly2 CLOSE_CID pos) with F
       by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity);
     change (fs_frame_bytes CLOSE_CID) with 256; unfold CLOSE_FBYTES in *; lia|].
  apply trans_g_img. apply cj_inG. unfold TW.SZ_g_s, CLOSE_FBYTES in *. lia. }
(* the state both arms carry *)
assert (CURJ : close_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F ly2 S2 W2
  (ms_mem ms) md1 e).
{ refine (conj _ (conj He0 (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj KCJ (conj HFWj HFLj)))))))).
  exact HJ1. }
set (m1 := ms_mem ms) in *.

(* +0x1bc: the branch, from a state with no region *)
pmkst HS.
clear HS SHOK.
pose proof (cj_entry0 W2 (ms_regs ms) m1 CLOSE_JBR) as HS.
change (mkSS CLOSE_JBR sr_atoms [] None (mkFacts [] [] [])) with cj_ss_br in HS.
assert (SHOKb : sh_ok segs CJ_Bx (@nil shent) (cj_E0 (ms_regs ms)) (mrestrict (w_H W2) m1)) by constructor.
assert (HEIb : img_env VAL A_LIM (cj_E0 (ms_regs ms))) by apply cj_env_img0.
clear HEI.
assert (D27 : sv_denot (cj_E0 (ms_regs ms)) (SOff 27 0) = Z_to_bv 64 (TW.S_state B1))
  by (cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r,
      Z_to_bv_bv_unsigned; exact P27).
assert (D20 : sv_denot (cj_E0 (ms_regs ms)) (SOff 20 0) = Z_to_bv 64 3)
  by (cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r,
      Z_to_bv_bv_unsigned; exact P20).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_JBR)) mm rom) mdx) Q) end.
psrr_branch_tok RUN BR HS SHOKb CJ_B0.
- (* S_state (close_w1 B1) = S_CLOSED: the release cut *)
  cbn [branch_taken] in Hc. rewrite D27, D20 in Hc.
  rewrite (cj_eqb (TW.S_state B1) 3 Hrange ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
  assert (HCl : TW.S_state (close_w1 B1) = TS0.DIGINET_S_CLOSED) by (rewrite EST, Hc; reflexivity).
  pose proof (close_rel_model timg_A TF Bw now Bw' B1 r r Hm HS1 HCl) as EBw'.
  paj_run_to_tok RUNTO HS HJ1 SHOKb CJ_B0 CLOSE_REL.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_nil. }
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms0) a = aview segs (w_H W2) m1 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin' Hx.
    lazymatch type of Hin' with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin' end.
    cbn [In] in Hin'. destruct Hin'. }
  assert (GB : forall a, apresent (w_H W2) m1 a -> apresent (w_H W2) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  cj_reg HS (2%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) Q2
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (3%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 3)) Q3
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (4%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 4)) Q4
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (8%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 8)) Q8
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (9%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 9)) Q9
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (13%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 13)) Q13
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 13%nat (Z_to_bv 5 13) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (18%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 18)) Q18
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (23%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 23)) Q23
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (24%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 24)) Q24
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_REL)) mm rom) mdx) Q) end.
  apply (REL LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F
    ly2 S2 W2 (ms_mem ms0) _ e (ms_regs ms0) HFIX).
  + split; [|split].
    * destruct CURJ as (J1 & E1' & F1 & P1 & L1 & M1 & K1 & S1' & FL1).
      refine (conj _ (conj E1' (conj F1 (conj P1 (conj L1 (conj M1 (conj _ (conj _ _)))))))).
      -- exact HJ1.
      -- apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly2 S2 W memc mdc W2 mem2 md2 m1
           (ms_mem ms0) (spZ regs - CLOSE_STK) (spZ regs) CLOSE_CID pos F FL (close_wr TF Bw) (fun _ : Z => False)
           HGX HARc HAR2 Hfrs Hbl HlyF EF eq_refl FFL ltac:(lia) ltac:(lia) ltac:(intros a []) K1
           ltac:(intros a Ha _; exact (KB a Ha)) GB).
      -- rewrite Forall_forall in S1' |- *. intros o Ho. rewrite <- (S1' o Ho).
         pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KB. lia.
      -- rewrite <- FL1. apply rdword_ext. intros i Hi. apply KB. unfold CLOSE_FBYTES in *. lia.
    * rewrite EBw'. apply (tw_kept TMAP_A (aview segs (w_H W2) m1)); [exact TW1|].
      intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      apply KB. lia.
    * rewrite EBw', (close_gfn1 B1 HLB). exact Hgf1.
  + unfold close_regs_rel, close_regs_base.
    refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))) _).
    * exact (eq_trans Q2 (eq_trans P2 R2)).
    * exact (eq_trans Q3 (eq_trans P3 R3)).
    * exact (eq_trans Q4 (eq_trans P4 R4)).
    * exact (eq_trans Q8 (eq_trans P8 R8)).
    * exact (eq_trans Q9 (eq_trans P9 R9)).
    * exact (eq_trans Q18 (eq_trans P18 R18)).
    * exact (eq_trans Q23 (eq_trans P23 R23)).
    * exact (eq_trans Q24 (eq_trans P24 R24)).
    * exact (eq_trans Q13 (eq_trans P13 R13)).
- (* any other state: the notice cut *)
  cbn [branch_taken] in Hc. rewrite D27, D20 in Hc.
  rewrite (cj_eqb (TW.S_state B1) 3 Hrange ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
  assert (HNc : TW.S_state (close_w1 B1) <> TS0.DIGINET_S_CLOSED) by (rewrite EST; exact Hc).
  paj_run_to_tok RUNTO HS HJ1 SHOKb CJ_B0 CLOSE_NTC.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_nil. }
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms0) a = aview segs (w_H W2) m1 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin' Hx.
    lazymatch type of Hin' with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin' end.
    cbn [In] in Hin'. destruct Hin'. }
  assert (GB : forall a, apresent (w_H W2) m1 a -> apresent (w_H W2) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  cj_reg HS (2%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) Q2
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (3%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 3)) Q3
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (4%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 4)) Q4
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (8%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 8)) Q8
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (9%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 9)) Q9
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (13%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 13)) Q13
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 13%nat (Z_to_bv 5 13) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (18%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 18)) Q18
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (19%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 19)) Q19
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (20%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 20)) Q20
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (23%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 23)) Q23
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (24%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 24)) Q24
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (25%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 25)) Q25
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (26%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 26)) Q26
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  cj_reg HS (27%bv : bv 5) (YK11.getr (ms_regs ms) (Z_to_bv 5 27)) Q27
    ltac:(cbn [sv_denot]; rewrite (cj_ew_reg0 (ms_regs ms) 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_NTC)) mm rom) mdx) Q) end.
  apply (NTC LAWS0 HMS HN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' B1 pos sp1 F
    ly2 S2 W2 (ms_mem ms0) _ e (ms_regs ms0) HFIX).
  + unfold close_ntc_cur. split; [|split; [exact HS1 | split; [|split; [exact Hgf1 | exact HNc]]]].
    * destruct CURJ as (J1 & E1' & F1 & P1 & L1 & M1 & K1 & S1' & FL1).
      refine (conj _ (conj E1' (conj F1 (conj P1 (conj L1 (conj M1 (conj _ (conj _ _)))))))).
      -- exact HJ1.
      -- apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly2 S2 W memc mdc W2 mem2 md2 m1
           (ms_mem ms0) (spZ regs - CLOSE_STK) (spZ regs) CLOSE_CID pos F FL (close_wr TF Bw) (fun _ : Z => False)
           HGX HARc HAR2 Hfrs Hbl HlyF EF eq_refl FFL ltac:(lia) ltac:(lia) ltac:(intros a []) K1
           ltac:(intros a Ha _; exact (KB a Ha)) GB).
      -- rewrite Forall_forall in S1' |- *. intros o Ho. rewrite <- (S1' o Ho).
         pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KB. lia.
      -- rewrite <- FL1. apply rdword_ext. intros i Hi. apply KB. unfold CLOSE_FBYTES in *. lia.
    * apply (tw_kept TMAP_A (aview segs (w_H W2) m1)); [exact TW1|].
      intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      apply KB. lia.
  + unfold close_regs_ntc, close_regs_rel, close_regs_base.
    refine (conj (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))) _)
      (conj _ (conj _ (conj _ (conj _ _))))).
    * exact (eq_trans Q2 (eq_trans P2 R2)).
    * exact (eq_trans Q3 (eq_trans P3 R3)).
    * exact (eq_trans Q4 (eq_trans P4 R4)).
    * exact (eq_trans Q8 (eq_trans P8 R8)).
    * exact (eq_trans Q9 (eq_trans P9 R9)).
    * exact (eq_trans Q18 (eq_trans P18 R18)).
    * exact (eq_trans Q23 (eq_trans P23 R23)).
    * exact (eq_trans Q24 (eq_trans P24 R24)).
    * exact (eq_trans Q13 (eq_trans P13 R13)).
    * exact (eq_trans Q19 (eq_trans P19 R19)).
    * exact (eq_trans Q20 P20).
    * exact (eq_trans Q25 (eq_trans P25 R25)).
    * exact (eq_trans Q26 P26).
    * rewrite EST. exact (eq_trans Q27 P27).
Qed.

End join.
