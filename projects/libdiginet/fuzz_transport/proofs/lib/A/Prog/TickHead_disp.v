(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 902 of its 1078 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SlostHead.v, with its numbers changed; 417 of its 567 lines of code are new or changed and 928 lines of the source are left out. *)
(* TickHead_disp: Lemma tkh_disp : tick_wake_at -> tick_online_at -> tick_step_at -> tick_epi_at -> tkh_ret_at. The walk
   of diginet_session_tick on fuzz_transport.asan (AF_diginet_session_tick = 0x8054 of lib/A/Prog/DgnTransportList.v)
   from the return of its call of __asan_set_shadow_f8 (+0x1b0, the head's own cut tkh_ret_at of
   lib/A/Prog/TickHead_mid.v) to the cuts of lib/A/Prog/TickCut.v it dispatches to. The runs are the position-abstract
   runs of lib/A/Prog/TransportGRunA.v over the caller's G journal:
     run 3a  +0x1b0 .. +0x1f8  the frame's shadow bytes 234 .. 251 (the right guard; a run to +0x1fc);
     run 3b  +0x1fc .. +0x21c  `beqz s4` (not taken: s4 = s), s7 = s + 112, s9 = its shadow address, the checked
                               `lw s5` of S_state Bw (the shadow byte 0 of g_s's payload, trans_tick_cells), a0 = 1,
                               s10 = 0, up to `blt a0, s5` (+0x220);
     +0x220 .. +0x22c, +0x370 .. +0x380  the dispatch, taken up from a state with no region: `blt a0, s5` (1 < s5 to
                               +0x370), `beqz s5` (S_IDLE to epi), `bne s5, 1` (s5 < 0 to step; S_WAKING falls through to
                               wake), `beq s5, 2` (S_ONLINE to online), `bne s5, 3` (s5 >= 4 to step; S_CLOSED `j` to epi).
   The facts the cuts carry are proved once at +0x220 (tick_pre_cur at that memory) and moved along each arm, whose runs
   write no byte (tkh_pre_move). The model's branch: S_IDLE and S_CLOSED return (Bw, 0) (tkh_model_ret); a state
   outside 0 .. 3 is tick_go (tkh_model_go). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg session_lost_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg TickCut TickHead_mid.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import SlostCut SlostHead TickHead_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Definition TKH_B0 : Z * Z := (0, 0).

(* run 3a, +0x1b0 .. +0x1fc: s3 (atom 19) is the frame's shadow address; the run writes its shadow bytes 234 .. 251. *)
Definition TKH_C5 : Z := AF_diginet_session_tick + 0x1fc.
Definition tkh_rg_rg : YP09.region := YP09.mkRegion (Some 19%nat) 234 252 234 252 [].
Definition tkh_facts5 : facts := mkFacts [(19%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_tkh5 : sstate := mkSS TKH_RET sr_atoms [tkh_rg_rg] None tkh_facts5.

(* run 3b, +0x1fc .. +0x220: s4 (atom 20) is s, s8 (atom 24) the shadow base; the run reads the 4 bytes of g_s's state
   (atom 33) after their check. *)
Definition tkh_rg_st : YP09.region :=
  YP09.mkRegion (Some 20%nat) 112 116 0 0 [YP09.mkChunk 112 (YP09.CVal 4 (SOff 33 0))].
Definition tkh_facts6 : facts :=
  mkFacts [(20%nat, mkAF TICK_S TICK_S 6); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_tkh6 : sstate := mkSS TKH_C5 sr_atoms [tkh_rg_st] None tkh_facts6.
Definition TKH_SH : list shent := [mkSHE 20 112 116].
Definition TKH_Bx : sv := SOff 24 0.

(* +0x220, `blt a0, s5`, taken up from a state with no region. *)
Definition TKH_C6 : Z := AF_diginet_session_tick + 0x220.
Definition ss_tkh7 : sstate := mkSS TKH_C6 sr_atoms [] None (mkFacts [] [] []).

(* ---- the model's branches at the dispatch ---- *)

(* S_IDLE and S_CLOSED return at once with the world unchanged (TSess.v :418-419). *)
Lemma tkh_model_ret : forall I Fr Bw now,
  TW.S_state Bw = TS0.DIGINET_S_IDLE \/ TW.S_state Bw = TS0.DIGINET_S_CLOSED ->
  TSS.diginet_session_tick_m I Fr Bw now = Some (Bw, DLib.DIGINET_OK).
Proof. intros I Fr Bw now Hs. rewrite tick_model. cbv zeta. destruct Hs as [Hs | Hs]; rewrite Hs; reflexivity. Qed.

(* Any state outside 0 .. 3 is neither returned nor lost: the model is tick_go (TickCut.v). *)
Lemma tkh_model_go : forall I Fr Bw now,
  TW.S_state Bw <> TS0.DIGINET_S_IDLE -> TW.S_state Bw <> TS0.DIGINET_S_WAKING ->
  TW.S_state Bw <> TS0.DIGINET_S_ONLINE -> TW.S_state Bw <> TS0.DIGINET_S_CLOSED ->
  TSS.diginet_session_tick_m I Fr Bw now = tick_go I Fr Bw now.
Proof.
intros I Fr Bw now H0 H1 H2 H3. rewrite tick_model. cbv zeta.
rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2),
  (proj2 (Z.eqb_neq _ _) H3).
cbn [orb andb]. unfold tick_go. reflexivity.
Qed.

(* `blt` on 1 and the sign-extended state; `beq` / `bne` of the state and a small literal. *)
Lemma tkh_blt1 : forall v, - 2 ^ 31 <= v < 2 ^ 31 ->
  branch_taken BC_LT (Z_to_bv 64 1) (Z_to_bv 64 v) = (1 <? v).
Proof.
intros v Hv. cbn [branch_taken]. unfold bv_lts. rewrite !Z_to_bv_signed.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
change (2 ^ 64 / 2) with (2 ^ 63).
rewrite (Z.mod_small (1 + 2 ^ 63) (2 ^ 64)) by lia.
rewrite (Z.mod_small (v + 2 ^ 63) (2 ^ 64)) by lia.
replace (1 + 2 ^ 63 - 2 ^ 63) with 1 by lia. replace (v + 2 ^ 63 - 2 ^ 63) with v by lia. reflexivity.
Qed.

Lemma tkh_beq : forall v c, - 2 ^ 31 <= v < 2 ^ 31 -> 0 <= c < 2 ^ 31 ->
  branch_taken BC_EQ (Z_to_bv 64 v) (Z_to_bv 64 c) = (v =? c).
Proof.
intros v c Hv Hc. cbn [branch_taken]. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small c (2 ^ 64)) by lia.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) by lia.
  destruct (Z.eqb_spec (v + 2 ^ 64) c); destruct (Z.eqb_spec v c); try reflexivity; lia.
- rewrite (Z.mod_small v (2 ^ 64)) by lia. reflexivity.
Qed.

Lemma tkh_bne : forall v c, - 2 ^ 31 <= v < 2 ^ 31 -> 0 <= c < 2 ^ 31 ->
  branch_taken BC_NE (Z_to_bv 64 v) (Z_to_bv 64 c) = negb (v =? c).
Proof.
intros v c Hv Hc. rewrite <- (tkh_beq v c Hv Hc). cbn [branch_taken]. reflexivity.
Qed.

(* The epilogue cut's model facts: S_IDLE or S_CLOSED returns (Bw, 0). *)
Lemma tkh_ret_model : forall I Fr Bw now Bw' r,
  TW.S_state Bw = TS0.DIGINET_S_IDLE \/ TW.S_state Bw = TS0.DIGINET_S_CLOSED ->
  TSS.diginet_session_tick_m I Fr Bw now = Some (Bw', r) -> Bw' = Bw /\ r = 0.
Proof.
intros I Fr Bw now Bw' r Hs Hm. rewrite (tkh_model_ret I Fr Bw now Hs) in Hm.
destruct (tick_some_inv _ _ _ _ Hm) as [E1 E2]. split; [symmetry; exact E1 | rewrite <- E2; reflexivity].
Qed.

(* The step cut's model fact: a state below 0 or above 3 is tick_go. *)
Lemma tkh_step_model : forall I Fr Bw now Bw' r,
  TW.S_state Bw < 0 \/ 4 <= TW.S_state Bw ->
  TSS.diginet_session_tick_m I Fr Bw now = Some (Bw', r) -> tick_go I Fr Bw now = Some (Bw', r).
Proof.
intros I Fr Bw now Bw' r Hs Hm. rewrite <- (tkh_model_go I Fr Bw now); [exact Hm | | | |];
unfold TS0.DIGINET_S_IDLE, TS0.DIGINET_S_WAKING, TS0.DIGINET_S_ONLINE, TS0.DIGINET_S_CLOSED; lia.
Qed.

Section td. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The entry state of run 3a: the frame's shadow bytes 234 .. 251. *)
Lemma tkh_entry5 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 19 = w64 SH -> SHADOW_OFF <= SH -> SH + 256 <= 2 ^ 46 ->
  (forall a, SH + 234 <= a < SH + 252 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (slh_E regs) ss_tkh5
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TKH_RET)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R19 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_tkh5.
  assert (U19 : bv_unsigned (ew (slh_E regs) 19) = SH)
    by (rewrite (slh_ew_reg regs 19 19%bv eq_refl), R19; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold tkh_rg_rg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold tkh_rg_rg, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold tkh_facts5, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* The entry state of run 3b and its shadow entry: g_s's state field, read through the world relation, and its shadow
   byte 0 (trans_tick_cells). *)
Lemma tkh_entry6 : forall ly S (W : world segs) regs mem md Bw,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (slh_E4 regs Bw) ss_tkh6
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TKH_C5)) mem (YK11.seg_rom segs))) /\
  sh_ok segs TKH_Bx TKH_SH (slh_E4 regs Bw) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md Bw HTC HAR Htw R20 R24.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (slh_E4 regs Bw) n = YK11.getr regs r)
  by (intros n r Hn; unfold slh_E4; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew (slh_E4 regs Bw) 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 112) 4))
  by (unfold slh_E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (CS : TICK_S = 6158784) by reflexivity.
assert (CS' : SLOST_S = 6158784) by reflexivity.
assert (U20 : bv_unsigned (ew (slh_E4 regs Bw) 20) = TICK_S)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew (slh_E4 regs Bw) 24) = SHADOW_OFF)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R33 : 0 <= TW.u_at Bw (TW.OFF_g_s + 112) 4 < 2 ^ 32) by exact (TWorldLemmas.u_at_range Bw _ 4).
assert (U33 : bv_unsigned (ew (slh_E4 regs Bw) 33) = TW.u_at Bw (TW.OFF_g_s + 112) 4)
  by (rewrite E33; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_tkh6.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold tkh_rg_st, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ TICK_S 112 4 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 112) 4));
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
    exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw TMAP_A_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold tkh_rg_st, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold tkh_facts6, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U24, U33.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (slh_ra B ly S W mem md HTC HAR) as HRA.
  assert (UB : U (slh_E4 regs Bw) TKH_Bx = SHADOW_OFF).
  { unfold U, TKH_Bx. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, TKH_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ TKH_Bx 20 (SLOST_S + 112) 104 TICK_S 112 116 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The state at +0x220 with no region. *)
Lemma tkh_entry7 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (slh_E regs) ss_tkh7
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TKH_C6)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_tkh7.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The facts the pre-callee cuts carry move to a later memory whose view is the same at every address. *)
Lemma tkh_pre_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2
    (m : word -> option byte) md m' md',
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 m md ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((TICK_CID, pos) :: own) lyc S2 W m' md' k ->
  (forall a, aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 m' md'.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 m md m' md'
  (((_ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) & HNW) & Eab & HGX & HTW) HJ3 KD GR.
refine (conj (conj (conj _ (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))) _)
  (conj Eab (conj _ _))).
- rewrite Z.add_0_r. exact HJ3.
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b mm i Hb Hi Hn. rewrite KD. exact (K2 b mm i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HNW.
- intros a Hg. rewrite KD. exact (HGX a Hg).
- apply (tw_kept TMAP_A (aview segs (w_H W) m)); [exact HTW | intros x _; exact (KD x)].
Qed.

(* The epilogue cut's facts from the pre-callee cut's, with the model's world Bw'. *)
Lemma tkh_epi_of_pre : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw Bw' pos sp1 F S2
    (m : word -> option byte) md,
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 m md ->
  tw_at TMAP_A (aview segs (w_H W) m) Bw' -> TW.g_fail_next Bw' <= 1 ->
  tick_epi_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' pos F lyc S2 W m md 0.
Proof. intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw Bw' pos sp1 F S2 m md
  ((C & _) & _) H1 H2. exact (conj C (conj H1 H2)). Qed.

(* The registers of the dispatch cuts and of the epilogue cut, from the registers at +0x220 a run keeps. *)
Definition tkh_kept : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].

Lemma tkh_regs_disp_keep : forall regs rg rg' Bw sp1 F,
  (forall r, In r tkh_kept -> YK11.getr rg' r = YK11.getr rg r) ->
  tick_regs_disp regs rg Bw sp1 F -> tick_regs_disp regs rg' Bw sp1 F.
Proof.
intros regs rg rg' Bw sp1 F K (((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R22 & R23 & R24 & R25) & R21).
unfold tick_regs_disp, tick_regs_run, tick_regs_base.
rewrite !K by (unfold tkh_kept; tkh_in).
repeat split; assumption.
Qed.

Lemma tkh_regs_epi_keep : forall regs rg rg' sp1 F r,
  (forall r, In r tkh_kept -> YK11.getr rg' r = YK11.getr rg r) ->
  tick_regs_epi regs rg sp1 F r -> tick_regs_epi regs rg' sp1 F r.
Proof.
intros regs rg rg' sp1 F r K ((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R26).
unfold tick_regs_epi, tick_regs_base.
rewrite !K by (unfold tkh_kept; tkh_in).
repeat split; assumption.
Qed.

(* The valuation of a state taken up from the registers: its register atoms are those registers. *)
Lemma tkh_agree : forall regs, env_agree 32 (Ereg regs [w64 SHADOW_OFF]) (slh_E regs).
Proof.
intros regs. split.
- intros n Hn. unfold slh_E. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity.
- reflexivity.
Qed.

(* One arm step: a run from a state with no region wrote no byte, so the facts the cuts carry move to its memory. *)
Ltac tkh_move CUR HS HJ W :=
  lazymatch type of CUR with tick_pre_cur _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m _ =>
    let msN := fresh "msN" in let KD := fresh "KD" in let GR := fresh "GR" in
    tkh_after_cut HS W KD GR m msN;
    let C2 := fresh "CUR" in
    pose proof (tkh_pre_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CUR HJ KD GR) as C2;
    clear CUR KD GR; rename C2 into CUR;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
    repeat match goal with H : mem_grows _ _ |- _ => clear H end
  end.
(* The exit to a pre-callee cut CUTH at offset pc, with the cut's own fact EXTRA. *)
Ltac tkh_exit_pre HS CUTH pc EXTRA HL HC HFX CUR RD rg :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    let KR := fresh "KR" in
    pose proof (regs_kept_of_st_ok_pi (PI := PI_transport) _ _ _ rg [w64 SHADOW_OFF] tkh_kept HS (tkh_agree rg)
      ltac:(vm_compute; reflexivity)) as KR;
    cbn [ms_regs restrict] in KR;
    pmkst HS;
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rgx _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rgx (Z_to_bv 64 (BASE + pc)) mm rom) mdx) Q) end;
    eapply (CUTH HL HC); [exact HFX | exact (conj CUR EXTRA) | exact (tkh_regs_disp_keep _ _ _ _ _ _ KR RD)]
  end.
(* The exit to the epilogue cut EPI (the model's world and result already substituted). *)
Ltac tkh_exit_epi HS EPI HL HC HFX CUR FN RE rg :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    let KR := fresh "KR" in
    pose proof (regs_kept_of_st_ok_pi (PI := PI_transport) _ _ _ rg [w64 SHADOW_OFF] tkh_kept HS (tkh_agree rg)
      ltac:(vm_compute; reflexivity)) as KR;
    cbn [ms_regs restrict] in KR;
    pmkst HS;
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rgx _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rgx (Z_to_bv 64 (BASE + TICK_EPI)) mm rom) mdx) Q) end;
    eapply (EPI HL HC);
    [ exact HFX
    | exact (tkh_epi_of_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CUR (proj2 (proj2 (proj2 CUR))) FN)
    | exact (tkh_regs_epi_keep _ _ _ _ _ _ KR RE) ]
  end.

(* The walk from the return of __asan_set_shadow_f8 to the four cuts. *)
Lemma tkh_disp : tick_wake_at B MT -> tick_online_at B MT -> tick_step_at B MT -> tick_epi_at B MT ->
  tkh_ret_at B MT.
Proof.
intros WAKE ONLINE STEP EPI HLAWS HCALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw'
  pos sp1 F S2 M MD rg HFIX MID.
pose proof HLAWS as (HPCS & HCELLS & HTC & HGU & HGNE0 & HROU & HRNE & LAWS & MTL & MTF & SMP & FFL & HGX & HGNE).
pose proof HFIX as (HJe & Hra & Hra4 & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw & Hfn & Hm & HTF & HROM
  & HAP & HRI & Hcnt & Hcnt0 & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof MID as (HJ & Hfrs & Eab & HMO & KG & GX & HFW & HFL & HNOW & HRG).
pose proof HRG as ((G2 & G3 & G4 & G8 & G9 & G18 & G27) & G19 & G20 & G22 & G24).
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : TICK_STK = 8880) by reflexivity.
assert (CS : TICK_S = 6158784) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (can_sp1_facts (spZ regs - TICK_FRAME) ltac:(unfold TICK_FRAME; lia)
  ltac:(rewrite Zminus_mod, Hsp16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16. unfold TICK_FRAME in Hsp1r.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARM.
assert (Hin2 : In (TICK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ TICK_CID pos HARM Hin2) as (HFal & HFapp2 & HFb & HFsh).
change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh.
change (fs_frame_bytes TICK_CID) with 2048 in HFb, HFsh.
rewrite <- EF in HFsh, HFb.
unfold TICK_FBYTES in HFc, HFapp.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
(* run 3a, +0x1b0 .. +0x1fc: the right guard *)
pose proof (tkh_entry5 W rg M (SHADOW_OFF + F / 8) G19 ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
assert (HEI : img_env VAL A_LIM (slh_E rg)) by apply slh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (slh_E rg) (mrestrict (w_H W) M)) by constructor.
assert (U19 : bv_unsigned (ew (slh_E rg) 19) = SHADOW_OFF + F / 8)
  by (rewrite (slh_ew_reg rg 19 19%bv eq_refl), G19; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
paj_run_to_tok RUNTO HS HJ SHOK TKH_B0 TKH_C5.
{ tkh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ TICK_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes TICK_CID / 8) with 256.
  rewrite <- EF. unfold shadow_addr. lia. }
rename HF into HF3a, HFr into HFr3a, HG into HG3a.
lazymatch type of HS with context [restrict _ ?m] => set (ms3a := m) in *; clearbody ms3a end.
(* run 3a wrote the right guard only *)
assert (K3a : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 234 <= a < SHADOW_OFF + F / 8 + 252) ->
  aview segs (w_H W) (ms_mem ms3a) a = aview segs (w_H W) M a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 234 <= x < SHADOW_OFF + F / 8 + 252) HFr3a);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U19 in Hx; lia |]).
  destruct Hin. }
pose proof HG3a as G3a. clear HF3a HFr3a HG3a.
tkh_kreg HS rg (2%bv : bv 5) 2%nat G2 W2. tkh_kreg HS rg (3%bv : bv 5) 3%nat G3 W3.
tkh_kreg HS rg (4%bv : bv 5) 4%nat G4 W4. tkh_kreg HS rg (8%bv : bv 5) 8%nat G8 W8.
tkh_kreg HS rg (9%bv : bv 5) 9%nat G9 W9. tkh_kreg HS rg (18%bv : bv 5) 18%nat G18 W18.
tkh_kreg HS rg (19%bv : bv 5) 19%nat G19 W19. tkh_kreg HS rg (20%bv : bv 5) 20%nat G20 W20.
tkh_kreg HS rg (22%bv : bv 5) 22%nat G22 W22. tkh_kreg HS rg (24%bv : bv 5) 24%nat G24 W24.
tkh_kreg HS rg (27%bv : bv 5) 27%nat G27 W27.
assert (NGH : forall a, SHADOW_OFF <= a -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Hg) as Hl.
  unfold kLowMemEnd, SHADOW_OFF in *. lia. }
assert (Htw3 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms3a)) Bw).
{ apply (tw_kept_GA (aview segs (w_H W) memc)); [exact Htw|]. intros b n i Hin Hi.
  assert (Hg : inG TG.G_HARNESS (b + i)).
  { unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (K3a (b + i) ltac:(lia) ltac:(unfold SHADOW_OFF; lia)).
  exact (GX (b + i) Hg). }
(* run 3b, +0x1fc .. +0x220: `beqz s4`, the checked load of S_state, a0 = 1, s10 = 0 *)
pmkst HS.
clear HS SHOK.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR3.
destruct (tkh_entry6 lyc S2 W (ms_regs ms3a) (ms_mem ms3a) _ Bw HTC HAR3 Htw3 W20 W24) as [HS SHOK].
clear HEI.
assert (HEI : img_env VAL A_LIM (slh_E4 (ms_regs ms3a) Bw)) by (unfold slh_E4; apply Eimg_env).
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (slh_E4 (ms_regs ms3a) Bw) n = YK11.getr (ms_regs ms3a) r)
  by (intros n r0 Hn; unfold slh_E4; apply can_ew_Eimg_Ereg_nat; exact Hn).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TKH_C5)) mm rom) mdx) Q) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ tkh_awr_rs.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
rename HF into HF3b, HFr into HFr3b, HG into HG3b.
lazymatch type of HS with context [restrict _ ?m] => set (ms3b := m) in *; clearbody ms3b end.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E6 := EF) in * end.
assert (E6lo : forall n, (n < 1024)%nat -> ew E6 n = ew (slh_E4 (ms_regs ms3a) Bw) n)
  by (intros n Hn; unfold E6; rewrite !ew_ewset_other by lia; reflexivity).
(* run 3b wrote no byte *)
assert (K3b : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms3b) a = aview segs (w_H W) (ms_mem ms3a) a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr3b); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]).
  destruct Hin. }
pose proof HG3b as G3b. clear HF3b HFr3b HG3b.
(* the registers at +0x220 *)
tkh_kreg5 HS E6lo EE4 (2%bv : bv 5) 2%nat W2 X2. tkh_kreg5 HS E6lo EE4 (3%bv : bv 5) 3%nat W3 X3.
tkh_kreg5 HS E6lo EE4 (4%bv : bv 5) 4%nat W4 X4. tkh_kreg5 HS E6lo EE4 (8%bv : bv 5) 8%nat W8 X8.
tkh_kreg5 HS E6lo EE4 (9%bv : bv 5) 9%nat W9 X9. tkh_kreg5 HS E6lo EE4 (18%bv : bv 5) 18%nat W18 X18.
tkh_kreg5 HS E6lo EE4 (19%bv : bv 5) 19%nat W19 X19. tkh_kreg5 HS E6lo EE4 (20%bv : bv 5) 20%nat W20 X20.
tkh_kreg5 HS E6lo EE4 (22%bv : bv 5) 22%nat W22 X22. tkh_kreg5 HS E6lo EE4 (24%bv : bv 5) 24%nat W24 X24.
tkh_kreg5 HS E6lo EE4 (27%bv : bv 5) 27%nat W27 X27.
assert (E33' : ew E6 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 112) 4)).
{ rewrite E6lo by lia. unfold slh_E4. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ _ 1). }
tkh_reg HS (21%bv : bv 5) (Z_to_bv 64 (TW.S_state Bw)) X21 ltac:(exact (slh_sext E6 Bw E33')).
tkh_reg HS (23%bv : bv 5) (w64 (TICK_S + 112)) X23
  ltac:(cbn [sv_denot]; rewrite (E6lo 20%nat ltac:(lia)), (EE4 20%nat 20%bv eq_refl), W20;
        unfold w64, TICK_S, TA_g_s; vm_compute; reflexivity).
tkh_reg HS (25%bv : bv 5) (w64 (SHADOW_OFF + (TICK_S + 112) / 8)) X25
  ltac:(cbn [sv_denot]; rewrite (E6lo 20%nat ltac:(lia)), (E6lo 24%nat ltac:(lia)), (EE4 20%nat 20%bv eq_refl),
        (EE4 24%nat 24%bv eq_refl), W20, W24; unfold w64, TICK_S, TA_g_s, SHADOW_OFF; vm_compute; reflexivity).
tkh_reg HS (26%bv : bv 5) (w64 0) X26 ltac:(reflexivity).
tkh_reg HS (10%bv : bv 5) (w64 1) X10 ltac:(reflexivity).
assert (RD6 : tick_regs_disp regs (ms_regs ms3b) Bw sp1 F)
  by exact (conj (conj (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 X27))))))
    (conj X19 (conj X20 (conj X22 (conj X23 (conj X24 X25)))))) X21).
assert (RE6 : tick_regs_epi regs (ms_regs ms3b) sp1 F 0)
  by exact (conj (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 X27)))))) X26).
(* ---- the facts the cuts carry, at the memory of +0x220 ---- *)
set (m6 := ms_mem ms3b) in *.
assert (KF6 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 234 <= a < SHADOW_OFF + F / 8 + 252) ->
  aview segs (w_H W) m6 a = aview segs (w_H W) M a).
{ intros a Ha Hn. rewrite (K3b a Ha). exact (K3a a Ha Hn). }
assert (GF6 : forall a, apresent (w_H W) M a -> apresent (w_H W) m6 a).
{ intros a Ha. apply (apresent_grows _ _ _ a G3b). exact (apresent_grows _ _ _ a G3a Ha). }
assert (KG6 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W m6 (spZ regs - TICK_STK) (spZ regs) (tick_wr Bw)).
{ apply (acall_kept_g_weaken segs B TG.G_HARNESS lyc Sc W memc W m6 (spZ regs - TICK_STK) (spZ regs)
    (fun _ => False) (tick_wr Bw)); [tauto|].
  apply (dk_kept_own_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc S2 W memc mdc M MD M m6
    (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F (flag_addr lyc TICK_CID pos) (fun _ => False)
    (fun a => SHADOW_OFF + F / 8 + 234 <= a < SHADOW_OFF + F / 8 + 252)
    HGX HAR HARM Hfrs Eab EF eq_refl FFL); [lia | lia | intros a [] | | exact KG | exact KF6 | exact GF6].
  intros a X. right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes TICK_CID / 8) with 256. lia. }
assert (GX6 : gx_kept segs TG.G_HARNESS W memc W m6).
{ intros a Hg. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (KF6 a ltac:(lia) ltac:(intros X; exact (NGH a ltac:(unfold SHADOW_OFF in *; lia) Hg))).
  exact (GX a Hg). }
assert (TW6 : tw_at TMAP_A (aview segs (w_H W) m6) Bw).
{ apply (tw_kept_GA (aview segs (w_H W) memc)); [exact Htw|]. intros b n i Hin Hi.
  apply GX6. unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
assert (HFW6 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) m6) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) TICK_SAVED).
{ apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HFW o Ho) as Hv. rewrite <- Hv.
  assert (Hob : 8 <= fst o <= 104).
  { unfold TICK_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [Ho | Ho]; [subst o; cbn [fst]; lia |]). destruct Ho. }
  apply rdword_ext. intros i Hi. apply KF6; [lia | unfold SHADOW_OFF in *; lia]. }
assert (HFL6 : rdword (aview segs (w_H W) m6) (F + TICK_FBYTES - 8) = Some (flag_addr lyc TICK_CID pos)).
{ rewrite <- HFL. unfold TICK_FBYTES. apply rdword_ext. intros i Hi. apply KF6; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HNOW6 : rdword (aview segs (w_H W) m6) (sp1 + 56) = Some now).
{ rewrite <- HNOW. apply rdword_ext. intros i Hi. apply KF6; [lia | unfold SHADOW_OFF in *; lia]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md6 := mdx) in * end.
assert (CUR : tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 m6 md6).
{ refine (conj (conj (conj _ (conj _ (conj Hfrs (conj _ (conj eq_refl (conj HMO (conj KG6 (conj HFW6 HFL6))))))))
    HNOW6) (conj Eab (conj GX6 TW6))).
  - rewrite Z.add_0_r. exact HJ.
  - unfold TICK_EV. lia.
  - rewrite Eab. apply Permutation_refl. }
clear KG GX HFW HFL HNOW KF6 GF6 KG6 GX6 HFW6 HFL6 HNOW6 K3a K3b.
(* ---- +0x220: the dispatch, from a state with no region ---- *)
pmkst HS.
clear HS SHOK HEI.
set (rg6 := ms_regs ms3b) in *.
pose proof (tkh_entry7 W rg6 m6) as HS.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (slh_E rg6) (mrestrict (w_H W) m6)) by constructor.
assert (HEI : img_env VAL A_LIM (slh_E rg6)) by apply slh_env_img.
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TKH_C6)) mm rom) mdx) Q) end.
assert (D10 : sv_denot (slh_E rg6) (SOff 10 0) = Z_to_bv 64 1)
  by (cbn [sv_denot]; rewrite (slh_ew_reg rg6 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X10).
assert (D21 : sv_denot (slh_E rg6) (SOff 21 0) = Z_to_bv 64 (TW.S_state Bw))
  by (cbn [sv_denot]; rewrite (slh_ew_reg rg6 21 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X21).
pose proof (slh_state_range Bw) as HSR.
clear X2 X3 X4 X8 X9 X18 X19 X20 X22 X23 X24 X25 X26 X27 X10 X21.
psrr_branch_tok RUN BR HS SHOK TKH_B0.
- (* 1 < s5: to +0x370 *)
  rewrite D10, D21, (tkh_blt1 _ HSR) in Hc. apply Z.ltb_lt in Hc. rename Hc into Hgt1.
  paj_run_tok RUN HS HJ SHOK TKH_B0.
  { tkh_awr_rs. apply awr_ok_x_nil. }
  tkh_move CUR HS HJ W.
  psrr_branch_tok RUN BR HS SHOK TKH_B0.
  + (* s5 = 2, S_ONLINE: to the online cut +0x384 *)
    rewrite D21 in Hc. change (sv_denot (slh_E rg6) (SLit 2)) with (Z_to_bv 64 2) in Hc.
    rewrite (tkh_beq _ 2 HSR ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK TKH_B0 TICK_ONLINE.
    { tkh_awr_rs. apply awr_ok_x_nil. }
    tkh_move CUR HS HJ W.
    tkh_exit_pre HS ONLINE TICK_ONLINE Hc HLAWS HCALLEES HFIX CUR RD6 rg6.
  + rewrite D21 in Hc. change (sv_denot (slh_E rg6) (SLit 2)) with (Z_to_bv 64 2) in Hc.
    rewrite (tkh_beq _ 2 HSR ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hne2.
    paj_run_tok RUN HS HJ SHOK TKH_B0.
    { tkh_awr_rs. apply awr_ok_x_nil. }
    tkh_move CUR HS HJ W.
    psrr_branch_tok RUN BR HS SHOK TKH_B0.
    * (* s5 >= 4: to the step cut +0x3c8 *)
      rewrite D21 in Hc. change (sv_denot (slh_E rg6) (SLit 3)) with (Z_to_bv 64 3) in Hc.
      rewrite (tkh_bne _ 3 HSR ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
      assert (HGO : tick_go timg_A TF Bw now = Some (Bw', r)) by (apply tkh_step_model; [lia | exact Hm]).
      paj_run_to_tok RUNTO HS HJ SHOK TKH_B0 TICK_STEP.
      { tkh_awr_rs. apply awr_ok_x_nil. }
      tkh_move CUR HS HJ W.
      tkh_exit_pre HS STEP TICK_STEP HGO HLAWS HCALLEES HFIX CUR RD6 rg6.
    * (* s5 = 3, S_CLOSED: to the epilogue cut +0x7cc *)
      rewrite D21 in Hc. change (sv_denot (slh_E rg6) (SLit 3)) with (Z_to_bv 64 3) in Hc.
      rewrite (tkh_bne _ 3 HSR ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
      destruct (tkh_ret_model _ _ _ _ _ _ (or_intror Hc) Hm) as [EB ER]. subst Bw' r.
      paj_run_to_tok RUNTO HS HJ SHOK TKH_B0 TICK_EPI.
      { tkh_awr_rs. apply awr_ok_x_nil. }
      tkh_move CUR HS HJ W.
      tkh_exit_epi HS EPI HLAWS HCALLEES HFIX CUR Hfn RE6 rg6.
- (* s5 <= 1: to +0x224 *)
  rewrite D10, D21, (tkh_blt1 _ HSR) in Hc. apply Z.ltb_ge in Hc. rename Hc into Hle1.
  paj_run_tok RUN HS HJ SHOK TKH_B0.
  { tkh_awr_rs. apply awr_ok_x_nil. }
  tkh_move CUR HS HJ W.
  psrr_branch_tok RUN BR HS SHOK TKH_B0.
  + (* s5 = 0, S_IDLE: to the epilogue cut +0x7cc *)
    rewrite D21 in Hc. change (sv_denot (slh_E rg6) (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (tkh_beq _ 0 HSR ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    destruct (tkh_ret_model _ _ _ _ _ _ (or_introl Hc) Hm) as [EB ER]. subst Bw' r.
    paj_run_to_tok RUNTO HS HJ SHOK TKH_B0 TICK_EPI.
    { tkh_awr_rs. apply awr_ok_x_nil. }
    tkh_move CUR HS HJ W.
    tkh_exit_epi HS EPI HLAWS HCALLEES HFIX CUR Hfn RE6 rg6.
  + rewrite D21 in Hc. change (sv_denot (slh_E rg6) (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (tkh_beq _ 0 HSR ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hne0.
    paj_run_tok RUN HS HJ SHOK TKH_B0.
    { tkh_awr_rs. apply awr_ok_x_nil. }
    tkh_move CUR HS HJ W.
    psrr_branch_tok RUN BR HS SHOK TKH_B0.
    * (* s5 < 0: to the step cut +0x3c8 *)
      rewrite D21 in Hc. change (sv_denot (slh_E rg6) (SLit 1)) with (Z_to_bv 64 1) in Hc.
      rewrite (tkh_bne _ 1 HSR ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
      assert (HGO : tick_go timg_A TF Bw now = Some (Bw', r)) by (apply tkh_step_model; [lia | exact Hm]).
      paj_run_to_tok RUNTO HS HJ SHOK TKH_B0 TICK_STEP.
      { tkh_awr_rs. apply awr_ok_x_nil. }
      tkh_move CUR HS HJ W.
      tkh_exit_pre HS STEP TICK_STEP HGO HLAWS HCALLEES HFIX CUR RD6 rg6.
    * (* s5 = 1, S_WAKING: to the wake cut +0x230 *)
      rewrite D21 in Hc. change (sv_denot (slh_E rg6) (SLit 1)) with (Z_to_bv 64 1) in Hc.
      rewrite (tkh_bne _ 1 HSR ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK TKH_B0 TICK_WAKE.
      { tkh_awr_rs. apply awr_ok_x_nil. }
      tkh_move CUR HS HJ W.
      tkh_exit_pre HS WAKE TICK_WAKE Hc HLAWS HCALLEES HFIX CUR RD6 rg6.
Qed.
End td.
