(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module names and numbers changed; 373 of its 446 lines of code are new or changed and 692 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickQueue_body.v, with its numbers changed; 192 of its 303 lines of code are new or changed and 335 lines of the source are left out. *)
(* TickQueue_sd: the send_data segment of the queue piece of diginet_session_tick's image-A walk, tq_sd : tq_f8_at ->
   tq_sd_at (TickQueue_kit.v), code +0x9dc .. +0x9f4 (0x89c94 .. 0x89cac): a2 = the 8-byte load of body_len at sp1 + 80,
   a0 = s, a1 = s9 (the body), a4 = now (sp1 + 56), `jal send_data` (+0x9ec) with a3 = n (the bundle's
   transport_send_data_cg; a G-form callee in the same G journal), then s10 = its result and `j` to +0x9fc
   (tq_f8_at). The run to the call reads the two words of the walk's own window (one region at s1); send_data's
   premises: the body's first body_len bytes are take's (garr8 of X), the body's range is a range of the walk's own
   side-stack frame (TickSrcKit.v trans_src_ok_fake with decode_rd_ok: the shadow bytes the fill and the store at
   byte 233 left, TickQueue_kit.v tq_ra_body), the world relation, the model and the run invariants (1), (4) at the
   world the code hands it. Its post folds into tick_cur by TickQueue_kit.v tq_cur_call (no out cell). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg session_lost_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGNotice TickSrcKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg TickCut TickQueue_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The run to `jal send_data` reads now (atom 32, s1 + 56) and body_len (atom 33, s1 + 80) from the walk's window. *)
Definition TQ_SD_R : YP09.region := YP09.mkRegion (Some 9%nat) 56 88 0 0
  [YP09.mkChunk 56 (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk 80 (YP09.CVal 8 (SOff 33 0))].
Definition TQ_SD_FACTS : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition ss_tq_sd : sstate := mkSS TQ_SD sr_atoms [TQ_SD_R] None TQ_SD_FACTS.

Section sd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition tq_sd_E (regs : bvmap 5 word) (now len : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 now; Z_to_bv 64 len]).

Lemma tq_sd_entry : forall (W : world segs) regs mem now len sp1,
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  0 <= now < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  rdword (aview segs (w_H W) mem) (sp1 + 80) = Some len ->
  st_ok_pi segs VAL (tq_sd_E regs now len) ss_tq_sd
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TQ_SD)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem now len sp1 R9 Hsp Hsp32 Hn Hl Hrn Hrl.
  set (E := tq_sd_E regs now len).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn'; unfold E, tq_sd_E; apply ew_Eimg_Ereg_nat; exact Hn').
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 now)
    by (unfold E, tq_sd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 len)
    by (unfold E, tq_sd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  rewrite restrict_mkst_fx. unfold ss_tq_sd.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, TQ_SD_R.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val segs E _ sp1 56 8 (SOff 32 0) now);
        [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | exact Hn | lia |].
      exact (val_mem_of_rdword segs (w_H W) mem _ _ Hrn).
    + apply (chunk_ok_val segs E _ sp1 80 8 (SOff 33 0) len);
        [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity | exact Hl | lia |].
      exact (val_mem_of_rdword segs (w_H W) mem _ _ Hrl).
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold TQ_SD_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma tq_sd_holds : @tq_f8_at fx rc B MT -> @tq_sd_at fx rc B MT.
Proof.
unfold tq_sd_at. intros F8 LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw'
  pos sp1 F Bs body X len n ly2 S2 W2 mem2 md2 e regs2 HFIX HRC Htws Hgfs Hinv1 Hinv4 Hm Hlen Hn HXL HXF HGX8 Hrlen
  HZ48 HZ233 HREGS R25 R13.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGNE).
pose proof CALLEES as (_ & _ & _ & _ & _ & _ & CSD & _).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm0 & HTF &
  Hrom & Hap & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HRC as (HC & Hnow56).
pose proof HC as (HJ1 & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R21 & R22 & R24).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (tq_fix_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F HFIX)
  as (Hce0 & Hwin0 & Hspz & H47 & Hsp0a & Hsp1 & Hsp1a & HTS & HSDE & HSDT & HES).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
unfold TICK_FBYTES in HFc, HFapp, HFL.
assert (He0 : e = 0) by (unfold TICK_EV in He; lia). subst e.
assert (Hin2 : In (TICK_CID, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
assert (EF2 : frame_addr ly2 TICK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 TICK_CID pos HAR2 Hin2) as (_ & _ & HFb & HFsh).
rewrite EF2 in HFb, HFsh. change (fs_frame_bytes TICK_CID) with 2048 in HFb.
change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity. rewrite ESH in HFsh.
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (NGF : forall a, F <= a < F + 2048 -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 TICK_CID pos a HAR2 Hin2); [|exact Hi].
  rewrite EF2. change (fs_frame_bytes TICK_CID) with 2048. lia. }
(* the body's length and bytes *)
assert (HLEN : Z.of_nat (length (firstn (Z.to_nat len) body)) = len).
{ rewrite <- HXF. rewrite length_firstn, HXL. unfold TAKE_BODY in *. lia. }
set (body' := firstn (Z.to_nat len) body) in *.
assert (HG8' : garr8 segs (mrestrict (w_H W2) mem2) (F + 384) (TW.zs body')).
{ rewrite <- HXF. exact (tq_garr8_firstn _ _ X _ HGX8). }
(* +0x9dc .. +0x9ec: a2 = body_len, a0 = s, a1 = body, a4 = now, `jal send_data` *)
pose proof (tq_sd_entry W2 regs2 mem2 now len sp1 R9 ltac:(lia) Hsp1a Hnow ltac:(unfold TAKE_BODY in *; lia) Hnow56
  Hrlen) as HS.
set (E0 := tq_sd_E regs2 now len) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, tq_sd_E; apply Eimg_env).
assert (EE : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E0 n0 = YK11.getr regs2 r0)
  by (intros n0 r0 Hn0; unfold E0, tq_sd_E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew E0 32 = Z_to_bv 64 now)
  by (unfold E0, tq_sd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 len)
  by (unfold E0, tq_sd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_tok RUN HS HJ1 SHOK TQ_B0.
{ tq_awr_rs. apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
  intros b wlo whi x Hiw Hx. cbv beta.
  lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end.
  cbn [In] in Hiw. repeat (destruct Hiw as [Hiw | Hiw]; [injection Hiw as <- <- <-; cbn [base_val] in Hx; lia |]).
  destruct Hiw. }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
pmkst HS.
tq_reg HS (Z_to_bv 5 10) (w64 TICK_S) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20).
tq_reg HS (Z_to_bv 5 11) (w64 (F + 384)) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R25).
tq_reg HS (Z_to_bv 5 12) (w64 len) Q12 ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
tq_kreg HS EE (Z_to_bv 5 13) 13%nat R13 Q13.
tq_reg HS (Z_to_bv 5 14) (w64 now) Q14 ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
tq_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 35396)) Q1 ltac:(apply codeptr_val; exact HEI).
tq_kreg HS EE (Z_to_bv 5 2) 2%nat R2 Q2.
tq_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
tq_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
tq_kreg HS EE (Z_to_bv 5 8) 8%nat R8 Q8. tq_kreg HS EE (Z_to_bv 5 9) 9%nat R9 Q9.
tq_kreg HS EE (Z_to_bv 5 18) 18%nat R18 Q18. tq_kreg HS EE (Z_to_bv 5 22) 22%nat R22 Q22.
tq_kreg HS EE (Z_to_bv 5 27) 27%nat R27 Q27.
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* what the walk has at the call *)
assert (HC1 : tick_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 (ms_mem ms) md1 0).
{ apply (tq_cur_step B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 mem2 md2
    (ms_mem ms) md1 0 (fun _ => False) LAWS HGX FFL HARc ltac:(lia) ltac:(lia) HC HJ1 EF); [intros a [] | | exact GA1].
  intros a Ha _. exact (KR1 a Ha). }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (HRD : decode_rd_ok W2 (ms_mem ms) (F + 384) len).
{ apply (trans_rd_ok_sub W2 (ms_mem ms) (F + 384) TAKE_BODY); [| lia | unfold TAKE_BODY in *; lia | lia].
  unfold decode_rd_ok. split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. unfold TAKE_BODY in Ha. rewrite KR1 by lia. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
  - apply tq_ra_body; [lia | exact DFm8 | |].
    + intros i Hi. rewrite KR1 by (unfold SHADOW_OFF; lia). exact (HZ48 i Hi).
    + rewrite KR1 by (unfold SHADOW_OFF; lia). exact HZ233.
  - apply (frame_hull_vis _ F 2048 (F + 384) TAKE_BODY); [lia | exact HF64 | reflexivity | lia | unfold TAKE_BODY; lia |
      unfold TAKE_BODY; lia |].
    intros i Hi. change (2048 / 8) with 256 in Hi.
    lazymatch goal with |- ?rd (_ + i) <> None => change (rd (SHADOW_OFF + F / 8 + i) <> None) end.
    rewrite KR1 by (unfold SHADOW_OFF; lia).
    apply can_aview_vis. exact (proj1 (HFsh i Hi)).
  - apply (amem_range_sub_app F 2048); [exact HFapp | lia | lia | unfold TAKE_BODY; lia | unfold TAKE_BODY; lia].
  - lia.
  - unfold TAKE_BODY. lia. }
assert (HSD0 : SENDDATA_EV = 0) by reflexivity.
(* +0x9ec: send_data (s, body, body_len, n, now) *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_send_data) rg mm mdx) Qx) end.
assert (EBR : BASE + 35396 = 0x89ca8) by (vm_compute; reflexivity).
eapply SRr_bind.
{ exact (CSD fx STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) ly2 S2 W2 (ms_mem ms) md1 (k + 0) (ms_regs ms)
    (F + 384) n now r body' TF Bs Bw' HJ1
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, EBR; rewrite unsigned_lit_small by lia; lia)
    Q3 Q4 Q10 Q11 ltac:(rewrite HLEN; exact Q12) Q13 Q14
    ltac:(rewrite QSP; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; rewrite Hsp1a, Z.add_0_r in D1; rewrite D1;
          replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring; apply Z.mod_mul; lia)
    ltac:(rewrite QSP; lia) ltac:(rewrite QSP; lia) Hn Hnow ltac:(lia)
    ltac:(eapply garr8_frame; [exact HG8'|]; intros a Ha; unfold TW.zs in Ha; rewrite length_map, HLEN in Ha;
          apply (mbyte_of_aview segs); apply KR1; unfold TAKE_BODY in *; lia)
    ltac:(rewrite HLEN; apply (trans_src_ok_fake B); [|exact HRD];
          exists TICK_CID, pos; split; [exact Hin2|]; rewrite EF2; change (fs_frame_bytes TICK_CID) with 2048;
          unfold TAKE_BODY in *; lia)
    ltac:(rewrite HLEN; unfold decode_off_win; rewrite QSP; left; unfold TAKE_BODY in *; lia)
    ltac:(rewrite HLEN; intros x Hx; apply NGF; unfold TAKE_BODY in *; lia)
    ltac:(apply NGF; lia)
    ltac:(apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact Htws|]; intros x Hx;
          pose proof (TMAP_A_hull x Hx) as Hh; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh; apply KR1; lia)
    Hgfs Hm
    ltac:(intros a Ha; rewrite KR1 by (pose proof (trans_ro_rd_bounds a Ha); lia);
          rewrite <- (Hrom a Ha); pose proof HK as (_ & _ & K3 & _);
          destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He'];
          apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He'];
          intro Ga; pose proof (inG_G_HARNESS_hull a Ga) as Gh; pose proof (trans_ro_rd_bounds a Ha) as Rb;
          unfold TG.G_HARNESS_LO in Gh; lia)
    Hinv1 Hinv4
    ltac:(rewrite Hfr, (tq_count_top SENDDATA_CID pos (frames Sc)) by discriminate; exact Hc0)
    ltac:(rewrite Hfr, (tq_count_top TRANS_BC_CID pos (frames Sc)) by discriminate; exact Hc2)
    ltac:(unfold TICK_EV in Hev; rewrite HSD0; lia)). }
intros W3 c3 _ HPOST.
unfold transport_senddata_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
  (X10 & Xtw & Xgf)).
rewrite HSD0 in He3.
(* tick_cur at send_data's return *)
destruct (tq_cur_call B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 (ms_mem ms) md1 0
  ly3 S3 W3 mem3 md3 e3 sp1 SENDDATA_STK [] senddata_wr LAWS MTL FFL HARc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) EF HC1 HJ3 He3 Hfr3 Hperm3
  ltac:(rewrite <- QSP; exact (acall_kept_g_mem_ext segs B TG.G_HARNESS ly2 S2 W2 (ms_mem ms) W3 mem3
        (gover [] mem3 (ms_mem ms)) _ _ senddata_wr (fun x => gover_nil_mem mem3 (ms_mem ms) x) HK3))
  Hmo3 ltac:(intros a Ha; exfalso; exact (inG_nil a Ha)) ltac:(intros a Ha; exfalso; exact (inG_nil a Ha))
  ltac:(intros a Ha; left; unfold tick_wr; do 19 right; exact Ha)
  ltac:(intros a Ha Hr; pose proof (tq_sdwr_G a Ha) as Ga; exact (NGF a ltac:(unfold TICK_FBYTES in Hr; lia) Ga)))
  as [HC3 KW3].
replace (0 + e3) with e3 in HC3 by lia. rewrite Z.add_0_r in HJ3.
(* the registers send_data keeps *)
rewrite Q1.
assert (P2 : YK11.getr regs3 (Z_to_bv 5 2) = w64 sp1) by exact (eq_trans (HP3 2 ltac:(hnf; lia)) Q2).
assert (P3 : YK11.getr regs3 (Z_to_bv 5 3) = w64 (as_gp B)) by exact (eq_trans (HP3 3 ltac:(hnf; lia)) Q3).
assert (P4 : YK11.getr regs3 (Z_to_bv 5 4) = w64 (as_tp B)) by exact (eq_trans (HP3 4 ltac:(hnf; lia)) Q4).
assert (P8 : YK11.getr regs3 (Z_to_bv 5 8) = w64 (spZ regs)) by exact (eq_trans (HP3 8 ltac:(hnf; lia)) Q8).
assert (P9 : YK11.getr regs3 (Z_to_bv 5 9) = w64 sp1) by exact (eq_trans (HP3 9 ltac:(hnf; lia)) Q9).
assert (P18 : YK11.getr regs3 (Z_to_bv 5 18) = w64 F) by exact (eq_trans (HP3 18 ltac:(hnf; lia)) Q18).
assert (P22 : YK11.getr regs3 (Z_to_bv 5 22) = w64 (SHADOW_OFF + F / 8 + 48))
  by exact (eq_trans (HP3 22 ltac:(hnf; lia)) Q22).
assert (P27 : YK11.getr regs3 (Z_to_bv 5 27) = w64 F) by exact (eq_trans (HP3 27 ltac:(hnf; lia)) Q27).
clear dependent ms.
(* 0x89ca8 .. +0x9f4: s10 = a0, `j` to +0x9fc *)
change (Z_to_bv 64 (BASE + 35396)) with (Z_to_bv 64 (BASE + TQ_RSD)).
pose proof (tq_entry_nr TQ_RSD W3 regs3 mem3) as HS.
set (E3 := Eimg (PI := PI_transport) (Ereg regs3 [])) in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E3 n0 = YK11.getr regs3 r0)
  by (intros n0 r0 Hn0; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
paj_run_to_tok RUNTO HS HJ3 SHOK3 TQ_B0 TQ_F8.
{ tq_awr_rs. apply awr_ok_x_nil. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W3) mem3 a)
  by exact (tq_nr_kept _ (w_H W3) mem3 (ms_mem ms) HFr).
assert (GA4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
tq_reg HS (Z_to_bv 5 26) (w64 r) F26
  ltac:(cbn [sv_denot]; rewrite (EE3 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X10).
tq_kreg HS EE3 (Z_to_bv 5 2) 2%nat P2 F2. tq_kreg HS EE3 (Z_to_bv 5 3) 3%nat P3 F3.
tq_kreg HS EE3 (Z_to_bv 5 4) 4%nat P4 F4. tq_kreg HS EE3 (Z_to_bv 5 8) 8%nat P8 F8'.
tq_kreg HS EE3 (Z_to_bv 5 9) 9%nat P9 F9. tq_kreg HS EE3 (Z_to_bv 5 18) 18%nat P18 F18.
tq_kreg HS EE3 (Z_to_bv 5 22) 22%nat P22 F22. tq_kreg HS EE3 (Z_to_bv 5 27) 27%nat P27 F27.
pmkst HS.
apply (F8 LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ly3 S3 W3
  (ms_mem ms) md4 e3 (ms_regs ms) HFIX).
- pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR4.
  split; [|split].
  + apply (tq_cur_step B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly3 S3 W3 mem3 md3
      (ms_mem ms) md4 e3 (fun _ => False) LAWS HGX FFL HARc ltac:(lia) ltac:(lia) HC3 HJ3 EF);
      [intros a [] | | exact GA4].
    intros a Ha _. exact (KR4 a Ha).
  + apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Xtw|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR4. lia.
  + exact Xgf.
- refine (conj (conj F2 (conj _ (conj _ (conj F8' (conj F9 (conj F18 F27)))))) F26).
  + exact (eq_trans F3 (eq_sym Hgp)).
  + exact (eq_trans F4 (eq_sym Htp)).
- exact F22.
Qed.
End sd.
