(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module names and numbers changed; 373 of its 446 lines of code are new or changed and 692 lines of the source are left out. *)
(* TickQueue_body: the take segment of the queue piece of diginet_session_tick's image-A walk, tq_body : tq_tk_at ->
   tq_body_at (TickQueue_kit.v), code +0x970 .. +0x99c (0x89c28 .. 0x89c54):
     +0x970 .. +0x97c  s9 = frame + 384 (the body), a1 = 185, a0 = s6 (the body's shadow address), `jal
                       __asan_set_shadow_00` (the bundle's aset_shadow_realizes .. 0 through TransportGRt.v
                       gx_set_shadow_at: the body's first 185 shadow bytes 0);
     +0x980 .. +0x99c  the plain store of 4 at the frame's shadow byte 233 (the last 4 of the 1484 bytes usable), a2 =
                       s1 + 80 (body_len), a4 = s1 + 76 (has_display), a0 = s, a1 = the body, a3 = s10 (allow), `jal
                       take` (the bundle's transport_take_cg; a G-form callee in the same G journal, with the out cells
                       [(s1 + 80, 8); (s1 + 76, 4)] in the walk's own window);
   then tq_tk_at at take's return (+0x9a0). take's premises: the body is a range of the walk's own frame, writable
   (in_frames) and addressable (TickQueue_kit.v tq_ra_body), the two cells are bytes of the walk's window, addressable
   as machine-stack bytes (DgnTransportCg.v stack_zshadow_ra); the world relation, the model, the queue-length
   invariant (2) and the cfg bounds (5) at B0. Its post folds into tick_cur by TickQueue_kit.v tq_cur_call (the out
   cells as NF beside the own frame, then tq_kept_ungover). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame TransportGRt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg session_lost_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGNotice.
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
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The state at +0x980: the frame's shadow byte 233 (s3 = atom 19), stored. *)
Definition TQ_BD_R : YP09.region := YP09.mkRegion (Some 19%nat) 233 234 233 234 [].
Definition TQ_BD_FACTS : facts := mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] [].
Definition ss_tq_bd : sstate := mkSS TQ_R00 sr_atoms [TQ_BD_R] None TQ_BD_FACTS.

Section bd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma tq_bd_entry : forall (W : world segs) regs mem F,
  YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> 4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 ->
  apresent (w_H W) mem (SHADOW_OFF + F / 8 + 233) ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) ss_tq_bd
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TQ_R00)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F R19 HF0 HF64 HFc Hp.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  set (E := Eimg (PI := PI_transport) (Ereg regs [])).
  assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
    by (unfold E; rewrite (ew_Eimg_Ereg_nat regs [] 19 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small;
        unfold SHADOW_OFF; lia).
  rewrite restrict_mkst_fx. unfold ss_tq_bd.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TQ_BD_R base_val]. rewrite U19.
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). replace (SHADOW_OFF + F / 8 + o) with (SHADOW_OFF + F / 8 + 233) by lia.
    exact Hp.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold TQ_BD_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19. change (2 ^ 3) with 8.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma tq_body_holds : @tq_tk_at fx rc B MT -> @tq_body_at fx rc B MT.
Proof.
unfold tq_body_at. intros TK LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw'
  pos sp1 F B0 allow ly2 S2 W2 mem2 md2 e regs2 HFIX HRC H48 Htw0' Hgf0' HINV Hal Hm HREGS R26.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGNE).
pose proof CALLEES as (_ & _ & _ & _ & _ & C00 & _ & CTK).
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
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (HSHF : SHADOW_OFF + F / 8 + 256 <= F \/ F + 2048 <= SHADOW_OFF + F / 8).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite DFm8, Z.add_0_r in D8.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
assert (NGF : forall a, F <= a < F + 2048 -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 TICK_CID pos a HAR2 Hin2); [|exact Hi].
  rewrite EF2. change (fs_frame_bytes TICK_CID) with 2048. lia. }
assert (NGW : forall a, alloc_ceiling <= a -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. pose proof (inG_low segs B transport_segs_low _ a HGX Hg) as Hl. unfold kLowMemEnd in Hl. lia. }
pose proof HJ1 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & _).
pose proof Hlyle2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ESLO & ESHI & _).
clear HJi memS.
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 TICK_CID pos HAR2 Hin2) as (_ & _ & HFb & HFsh).
rewrite EF2 in HFb, HFsh. change (fs_frame_bytes TICK_CID) with 2048 in HFb.
change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity. rewrite ESH in HFsh.
pose proof HINV as (I1 & I2 & I4 & I5a & I5b).
(* the model at the call of take *)
unfold tq_take_cont in Hm.
destruct (TS0.take_m B0 allow) as [[B1 [[[body len] hd] taken]]|] eqn:HT; [|discriminate Hm].
assert (HL0 : length B0 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0').
(* +0x970 .. +0x97c: s9 = body, a1 = 185, a0 = s6, `jal __asan_set_shadow_00` *)
pose proof (tq_entry_nr TQ_BODY W2 regs2 mem2) as HS.
set (E0 := Eimg (PI := PI_transport) (Ereg regs2 [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E0 n = YK11.getr regs2 r0)
  by (intros n r0 Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U27 : bv_unsigned (ew E0 27) = F)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ1 SHOK TQ_B0.
{ tq_awr_rs. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a)
  by exact (tq_nr_kept _ (w_H W2) mem2 (ms_mem ms) HFr).
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
pmkst HS.
tq_reg HS (Z_to_bv 5 10) (w64 (SHADOW_OFF + F / 8 + 48)) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
tq_reg HS (Z_to_bv 5 11) (w64 185) Q11 ltac:(reflexivity).
tq_reg HS (Z_to_bv 5 25) (w64 (F + 384)) Q25 ltac:(cbn [sv_denot]; rewrite U27; reflexivity).
tq_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 35284)) Q1 ltac:(apply codeptr_val; exact HEI).
tq_kreg HS EE (Z_to_bv 5 2) 2%nat R2 Q2.
tq_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
tq_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
tq_kreg HS EE (Z_to_bv 5 8) 8%nat R8 Q8. tq_kreg HS EE (Z_to_bv 5 9) 9%nat R9 Q9.
tq_kreg HS EE (Z_to_bv 5 18) 18%nat R18 Q18. tq_kreg HS EE (Z_to_bv 5 27) 27%nat R27 Q27.
tq_kreg HS EE (Z_to_bv 5 19) 19%nat R19 Q19. tq_kreg HS EE (Z_to_bv 5 20) 20%nat R20 Q20.
tq_kreg HS EE (Z_to_bv 5 21) 21%nat R21 Q21. tq_kreg HS EE (Z_to_bv 5 22) 22%nat R22 Q22.
tq_kreg HS EE (Z_to_bv 5 24) 24%nat R24 Q24. tq_kreg HS EE (Z_to_bv 5 26) 26%nat R26 Q26.
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x97c: __asan_set_shadow_00 (s6, 185) *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_set_shadow_00)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ apply (gx_set_shadow_at (SK := tfib_sink_head) segs B LAWS transport_segs_low
    (transport_sigma TS___asan_set_shadow_00) 0 (C00 fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S
    W0 mem0 md0 ((TICK_CID, pos) :: own) ly2 S2 md1 (k + 0) TICK_CID pos (SHADOW_OFF + F / 8 + 48) 185 (sp1 - sp0)
    (Z_to_bv 64 (BASE + 35284)) HJ1 (or_introl eq_refl) Q10 Q11).
  - lia.
  - rewrite EF2. unfold shadow_addr. lia.
  - rewrite EF2. unfold shadow_addr. change (fs_frame_bytes TICK_CID / 8) with 256. lia.
  - rewrite QSP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite Hsp1a, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hset3 & Hkeep3 & Hgr3).
assert (KZ3 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 48 <= a < SHADOW_OFF + F / 8 + 48 + 185) ->
  aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; rewrite (Hkeep3 a Ha Hn); exact (KR1 a Ha)).
assert (GZ3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) by (intros a Ha; exact (Hgr3 a (GA1 a Ha))).
assert (P2 : YK11.getr regs3 (Z_to_bv 5 2) = w64 sp1) by exact (eq_trans (HP3 2 ltac:(hnf; lia)) Q2).
assert (P3 : YK11.getr regs3 (Z_to_bv 5 3) = w64 (as_gp B)) by exact (eq_trans (HP3 3 ltac:(hnf; lia)) Q3).
assert (P4 : YK11.getr regs3 (Z_to_bv 5 4) = w64 (as_tp B)) by exact (eq_trans (HP3 4 ltac:(hnf; lia)) Q4).
assert (P8 : YK11.getr regs3 (Z_to_bv 5 8) = w64 (spZ regs)) by exact (eq_trans (HP3 8 ltac:(hnf; lia)) Q8).
assert (P9 : YK11.getr regs3 (Z_to_bv 5 9) = w64 sp1) by exact (eq_trans (HP3 9 ltac:(hnf; lia)) Q9).
assert (P18 : YK11.getr regs3 (Z_to_bv 5 18) = w64 F) by exact (eq_trans (HP3 18 ltac:(hnf; lia)) Q18).
assert (P19 : YK11.getr regs3 (Z_to_bv 5 19) = w64 (SHADOW_OFF + F / 8))
  by exact (eq_trans (HP3 19 ltac:(hnf; lia)) Q19).
assert (P20 : YK11.getr regs3 (Z_to_bv 5 20) = w64 TICK_S) by exact (eq_trans (HP3 20 ltac:(hnf; lia)) Q20).
assert (P21 : YK11.getr regs3 (Z_to_bv 5 21) = w64 (SHADOW_OFF + (TICK_S + 208) / 8))
  by exact (eq_trans (HP3 21 ltac:(hnf; lia)) Q21).
assert (P22 : YK11.getr regs3 (Z_to_bv 5 22) = w64 (SHADOW_OFF + F / 8 + 48))
  by exact (eq_trans (HP3 22 ltac:(hnf; lia)) Q22).
assert (P24 : YK11.getr regs3 (Z_to_bv 5 24) = w64 SHADOW_OFF) by exact (eq_trans (HP3 24 ltac:(hnf; lia)) Q24).
assert (P25 : YK11.getr regs3 (Z_to_bv 5 25) = w64 (F + 384)) by exact (eq_trans (HP3 25 ltac:(hnf; lia)) Q25).
assert (P26 : YK11.getr regs3 (Z_to_bv 5 26) = w64 allow) by exact (eq_trans (HP3 26 ltac:(hnf; lia)) Q26).
assert (P27 : YK11.getr regs3 (Z_to_bv 5 27) = w64 F) by exact (eq_trans (HP3 27 ltac:(hnf; lia)) Q27).
clear dependent ms.
(* +0x980 .. +0x99c: the shadow byte 233 = 4, a2 = s1 + 80, a4 = s1 + 76, a0 = s, a1 = body, a3 = allow, `jal take` *)
change (Z_to_bv 64 (BASE + 35284)) with (Z_to_bv 64 (BASE + TQ_R00)).
pose proof (tq_bd_entry W2 regs3 mem3 F P19 HF0 HF64 ltac:(lia)
  ltac:(apply GZ3; exact (proj1 (HFsh 233 ltac:(lia))))) as HS.
set (E3 := Eimg (PI := PI_transport) (Ereg regs3 [])) in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E3 n = YK11.getr regs3 r0)
  by (intros n r0 Hn; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U19 : bv_unsigned (ew E3 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE3 19%nat (Z_to_bv 5 19) eq_refl), P19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E3 9) = sp1)
  by (rewrite (EE3 9%nat (Z_to_bv 5 9) eq_refl), P9; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) E3 (mrestrict (w_H W2) mem3)) by constructor.
paj_run_tok RUN HS HJ3 SHOK3 TQ_B0.
{ tq_awr_rs. eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19 in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF2. change (fs_frame_bytes TICK_CID / 8) with 256. lia.
  - apply awr_ok_x_nil. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
lazymatch type of HS with context [restrict _ ?m] => rename m into msT end.
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> a <> SHADOW_OFF + F / 8 + 233 ->
  aview segs (w_H W2) (ms_mem msT) a = aview segs (w_H W2) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => x = SHADOW_OFF + F / 8 + 233) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end.
  cbn [In] in Hiw.
  repeat (destruct Hiw as [Hiw | Hiw]; [injection Hiw as <- <- <-; cbn [base_val] in Hx; rewrite ?U19 in Hx; lia |]).
  destruct Hiw. }
assert (GA4 : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem msT) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR4.
(* the shadow byte 233 the run stored *)
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
pose proof (tq_chunk_val E3 (w_H W2) (ms_mem msT) _ _ _ _ _ _ 233 1 (SLit 4) RG
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as V4.
cbn [base_val] in V4. rewrite U19 in V4.
change (bv_unsigned (sv_denot E3 (SLit 4)) mod 2 ^ (8 * Z.of_N 1)) with 4 in V4. change (N.to_nat 1) with 1%nat in V4.
pose proof (tq_aview_of_val _ _ _ 1 4 0 V4 ltac:(lia)) as HZ233'. cbn [Z.of_nat] in HZ233'.
rewrite Z.add_0_r in HZ233'. change (YO0f.le_byte 4 1 0) with 4 in HZ233'.
assert (HZ48' : forall i, 48 <= i < 233 -> aview segs (w_H W2) (ms_mem msT) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite KR4 by (unfold SHADOW_OFF; lia).
  replace (SHADOW_OFF + F / 8 + i) with (SHADOW_OFF + F / 8 + 48 + (i - 48)) by lia. apply Hset3. lia. }
assert (KB : forall a, F <= a < F + 2048 -> aview segs (w_H W2) (ms_mem msT) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite KR4 by (unfold SHADOW_OFF in *; lia). apply KZ3; [lia|]. unfold SHADOW_OFF in *. lia. }
assert (KS : forall a, alloc_ceiling <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msT) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite KR4 by (unfold SHADOW_OFF in *; lia). apply KZ3; [lia|]. unfold SHADOW_OFF in *. lia. }
assert (HSHV : forall i, 0 <= i < 256 -> aview segs (w_H W2) (ms_mem msT) (SHADOW_OFF + F / 8 + i) <> None).
{ intros i Hi. destruct (Z.eq_dec i 233) as [-> | N]; [rewrite HZ233'; discriminate|].
  destruct (Z_lt_le_dec i 48) as [L | L]; [| destruct (Z_lt_le_dec i 233) as [L2 | L2]].
  - rewrite KR4 by (unfold SHADOW_OFF; lia). rewrite KZ3 by (unfold SHADOW_OFF; lia).
    apply can_aview_vis. exact (proj1 (HFsh i Hi)).
  - rewrite HZ48' by lia. discriminate.
  - rewrite KR4 by (unfold SHADOW_OFF; lia). rewrite KZ3 by (unfold SHADOW_OFF; lia).
    apply can_aview_vis. exact (proj1 (HFsh i Hi)). }
(* the registers at the call of take *)
pmkst HS.
tq_reg HS (Z_to_bv 5 10) (w64 TICK_S) T10
  ltac:(cbn [sv_denot]; rewrite (EE3 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P20).
tq_reg HS (Z_to_bv 5 11) (w64 (F + 384)) T11
  ltac:(cbn [sv_denot]; rewrite (EE3 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P25).
tq_reg HS (Z_to_bv 5 12) (w64 (sp1 + 80)) T12
  ltac:(cbn [sv_denot]; rewrite U9; reflexivity).
tq_reg HS (Z_to_bv 5 13) (w64 allow) T13
  ltac:(cbn [sv_denot]; rewrite (EE3 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P26).
tq_reg HS (Z_to_bv 5 14) (w64 (sp1 + 76)) T14
  ltac:(cbn [sv_denot]; rewrite U9; reflexivity).
tq_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 35316)) T1 ltac:(apply codeptr_val; exact HEI3).
tq_kreg HS EE3 (Z_to_bv 5 2) 2%nat P2 T2. tq_kreg HS EE3 (Z_to_bv 5 3) 3%nat P3 T3.
tq_kreg HS EE3 (Z_to_bv 5 4) 4%nat P4 T4. tq_kreg HS EE3 (Z_to_bv 5 8) 8%nat P8 T8.
tq_kreg HS EE3 (Z_to_bv 5 9) 9%nat P9 T9. tq_kreg HS EE3 (Z_to_bv 5 18) 18%nat P18 T18.
tq_kreg HS EE3 (Z_to_bv 5 19) 19%nat P19 T19. tq_kreg HS EE3 (Z_to_bv 5 20) 20%nat P20 T20.
tq_kreg HS EE3 (Z_to_bv 5 21) 21%nat P21 T21. tq_kreg HS EE3 (Z_to_bv 5 22) 22%nat P22 T22.
tq_kreg HS EE3 (Z_to_bv 5 24) 24%nat P24 T24. tq_kreg HS EE3 (Z_to_bv 5 25) 25%nat P25 T25.
tq_kreg HS EE3 (Z_to_bv 5 27) 27%nat P27 T27.
assert (TSP : spZ (ms_regs msT) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs msT) (Z_to_bv 5 2)) = sp1); rewrite T2; unfold w64;
      apply unsigned_lit_small; lia).
(* what the walk has at the call *)
assert (HC4 : tick_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 (ms_mem msT) md4 0).
{ apply (tq_cur_step B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 mem2 md2
    (ms_mem msT) md4 0 (fun a => SHADOW_OFF + F / 8 + 48 <= a < SHADOW_OFF + F / 8 + 48 + 186) LAWS HGX FFL HARc
    ltac:(lia) ltac:(lia) HC HJ3 EF).
  - intros a Ha. right. left. split.
    + unfold dkg_nf. right. left. change (fs_frame_bytes TICK_CID / 8) with 256. lia.
    + unfold TICK_FBYTES, SHADOW_OFF in *. destruct HSHF; lia.
  - intros a Ha Hn. rewrite KR4 by (unfold SHADOW_OFF in *; lia). apply KZ3; [lia | lia].
  - intros a Ha. exact (GA4 a (GZ3 a Ha)). }
destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 TICK_CID pos HAR2 Hin2) as (F4096 & Fce & _).
rewrite EF2 in F4096, Fce. change (fs_frame_bytes TICK_CID) with 2048 in Fce.
assert (HRD : decode_rd_ok W2 (ms_mem msT) (F + 384) TAKE_BODY).
{ split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. unfold TAKE_BODY in Ha. rewrite KB by lia. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
  - apply tq_ra_body; [lia | exact DFm8 | exact HZ48' | exact HZ233'].
  - apply (frame_hull_vis _ F 2048 (F + 384) TAKE_BODY); [lia | exact HF64 | reflexivity | lia |
      unfold TAKE_BODY; lia | unfold TAKE_BODY; lia |].
    intros i Hi. change (2048 / 8) with 256 in Hi.
    lazymatch goal with |- ?rd (_ + i) <> None => change (rd (SHADOW_OFF + F / 8 + i) <> None) end.
    exact (HSHV i Hi).
  - apply (amem_range_sub_app F 2048); [exact HFapp | lia | lia | unfold TAKE_BODY; lia | unfold TAKE_BODY; lia].
  - lia.
  - unfold TAKE_BODY. lia. }
assert (HRDS : forall q n, sp1 <= q -> q + n <= sp1 + 88 -> 0 < n -> decode_rd_ok W2 (ms_mem msT) q n).
{ intros q n H1 H2 H3.
  destruct (stack_zshadow_ra B ly2 S2 W2 (ms_mem msT) md4 q n HAR4 H3 ltac:(rewrite ESLO; lia)
    ltac:(rewrite ESHI; lia)) as [RA HV].
  split; [|split; [exact RA | split; [exact HV | split; [| split; lia]]]].
  - intros a Ha. eapply aview_some_of_apresent. apply GA4, GZ3, Hpres2. lia.
  - right. unfold kHighMemBeg, kHighMemEnd in *. lia. }
assert (TWO : forall q n, sp1 <= q -> q + n <= sp1 + 88 ->
  transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly S ly2 S2 ((TICK_CID, pos) :: own) W2 (ms_mem msT)
    (spZ (ms_regs msT)) q n).
{ intros q n H1 H2. eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ3|]. intros a Ha. left. rewrite TSP.
  split; [left; lia | lia]. }
(* +0x99c: take (s, body, &body_len, allow, &has_display) *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_take) rg mm mdx) Qx) end.
assert (EBR : BASE + 35316 = 0x89c58) by (vm_compute; reflexivity).
eapply SRr_bind.
{ exact (CTK fx STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) ly2 S2 W2 (ms_mem msT) md4 (k + 0) (ms_regs msT)
    (F + 384) (sp1 + 80) (sp1 + 76) allow len hd taken body B0 B1 HJ3
    ltac:(rewrite T1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite T1, EBR; rewrite unsigned_lit_small by lia; lia)
    T3 T4 T10 T11 T12 T13 T14
    ltac:(rewrite TSP; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; rewrite Hsp1a, Z.add_0_r in D1; rewrite D1;
          replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring; apply Z.mod_mul; lia)
    ltac:(rewrite TSP; lia) ltac:(rewrite TSP; lia) ltac:(lia) ltac:(lia)
    ltac:(exists TICK_CID, pos; split; [exact Hin2|]; rewrite EF2; change (fs_frame_bytes TICK_CID) with 2048;
          unfold TAKE_BODY; lia)
    ltac:(eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ3|]; intros a Ha; left; rewrite TSP; split;
          [right; right; right; exists TICK_CID, pos; split; [left; reflexivity|]; left; unfold in_zr;
           cbn [fst snd]; rewrite EF2; change (fs_frame_bytes TICK_CID) with 2048; unfold TAKE_BODY in Ha; lia |
           unfold TAKE_BODY in Ha; lia])
    HRD
    ltac:(unfold decode_off_win; rewrite TSP; left; unfold TAKE_BODY; lia)
    ltac:(intros x Hx; apply NGF; unfold TAKE_BODY in Hx; lia)
    ltac:(pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; rewrite Hsp1a, Z.add_0_r in D1; rewrite D1;
          replace (32 * (sp1 / 32) + 80) with ((4 * (sp1 / 32) + 10) * 8) by ring; apply Z.mod_mul; lia)
    (TWO (sp1 + 80) 8 ltac:(lia) ltac:(lia)) (HRDS (sp1 + 80) 8 ltac:(lia) ltac:(lia) ltac:(lia))
    ltac:(unfold decode_off_win; rewrite TSP; right; lia)
    ltac:(intros x Hx; apply NGW; lia)
    ltac:(pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; rewrite Hsp1a, Z.add_0_r in D1; rewrite D1;
          replace (32 * (sp1 / 32) + 76) with ((8 * (sp1 / 32) + 19) * 4) by ring; apply Z.mod_mul; lia)
    (TWO (sp1 + 76) 4 ltac:(lia) ltac:(lia)) (HRDS (sp1 + 76) 4 ltac:(lia) ltac:(lia) ltac:(lia))
    ltac:(unfold decode_off_win; rewrite TSP; right; lia)
    ltac:(intros x Hx; apply NGW; lia)
    ltac:(left; unfold TAKE_BODY; lia) ltac:(left; unfold TAKE_BODY; lia) ltac:(right; lia)
    ltac:(apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact Htw0'|]; intros x Hx;
          pose proof (TMAP_A_hull x Hx) as Hh; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh;
          rewrite KR4 by (unfold SHADOW_OFF; lia); apply KZ3; unfold SHADOW_OFF; lia)
    Hgf0' HT I2 I5a I5b
    ltac:(rewrite Hfr, (tq_count_top TRANS_BC_CID pos (frames Sc)) by discriminate; exact Hc2)
    ltac:(unfold TICK_EV in Hev; unfold TAKE_EV; lia)). }
intros W3 c3 _ HPOST.
unfold transport_take_post, transport_cg_post_out in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs5 & mem5 & md5 & e3 & -> & He3 & HJ5 & HP5 & Hfr3 & Hperm3 & HK3 & Hmo3 &
  (X10 & Xtw & Xgf & (X & HXL & HXG & HXF) & XL & XH)).
unfold TAKE_EV in He3.
pose proof HJ5 as (_ & _ & (memS5 & HJi5 & _) & _).
pose proof HJi5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
clear HJi5 memS5.
rewrite TSP in HK3.
fold (tq_outs sp1) in HK3.
(* the take_wr bytes *)
assert (HE : forall a, take_wr B0 (F + 384) (sp1 + 80) (sp1 + 76) a ->
  tick_wr Bw a \/ dkg_nf TICK_CID F (flag_addr lyc TICK_CID pos) a \/ inG (tq_outs sp1) a).
{ intros a Ha. destruct (tq_take_wr_cases _ _ _ _ a Ha) as [Hg | [Hb | [Hl | Hh]]].
  - left. apply (tq_take_wr_tick B0 Bw (F + 384) (sp1 + 80) (sp1 + 76) a Ha).
    + intros Hb'. exact (NGF a ltac:(unfold TAKE_BODY in *; lia) (tq_gs_inG a Hg)).
    + unfold TA_g_s, TW.SZ_g_s in *. lia.
    + unfold TA_g_s, TW.SZ_g_s in *. lia.
  - right. left. unfold dkg_nf. left. change (fs_frame_bytes TICK_CID) with 2048. unfold TAKE_BODY in Hb. lia.
  - right. right. apply tq_outs_in. lia.
  - right. right. apply tq_outs_in. lia. }
assert (HEf : forall a, take_wr B0 (F + 384) (sp1 + 80) (sp1 + 76) a -> ~ (F + TICK_FBYTES - 8 <= a < F + TICK_FBYTES)).
{ intros a Ha Hr. unfold TICK_FBYTES in Hr. destruct (tq_take_wr_cases _ _ _ _ a Ha) as [Hg | [Hb | [Hl | Hh]]].
  - exact (NGF a ltac:(lia) (tq_gs_inG a Hg)).
  - unfold TAKE_BODY in Hb. lia.
  - lia.
  - lia. }
destruct (tq_cur_call B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 (ms_mem msT) md4 0
  ly3 S3 W3 mem5 md5 e3 sp1 TAKE_STK (tq_outs sp1) (take_wr B0 (F + 384) (sp1 + 80) (sp1 + 76)) LAWS MTL FFL HARc
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite (proj2 take_stk_eq); lia) EF HC4 HJ5 He3 Hfr3 Hperm3 HK3 Hmo3
  ltac:(intros a Ha; pose proof (tq_outs_bounds sp1 a Ha); lia)
  ltac:(intros a Ha; pose proof (tq_outs_bounds sp1 a Ha); apply Hpres5; lia)
  HE HEf) as [HC5 KW5].
(* the frame's shadow at take's return *)
pose proof HK3 as (_ & _ & _ & L4 & _).
assert (KF5 : forall i, 0 <= i < 256 ->
  aview segs (w_H W3) mem5 (SHADOW_OFF + F / 8 + i) = aview segs (w_H W2) (ms_mem msT) (SHADOW_OFF + F / 8 + i)).
{ intros i Hi.
  assert (Hno : ~ inG (tq_outs sp1) (SHADOW_OFF + F / 8 + i))
    by (intros Ho; pose proof (tq_outs_bounds sp1 _ Ho); unfold SHADOW_OFF in *; lia).
  rewrite <- (gover_out_aview segs (tq_outs sp1) (w_H W3) mem5 (ms_mem msT) (SHADOW_OFF + F / 8 + i)
    ltac:(unfold SHADOW_OFF; lia) Hno).
  apply (L4 TICK_CID pos _ Hin2).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF2. unfold shadow_addr. change (fs_frame_bytes TICK_CID / 8) with 256.
    lia.
  - intros Hw. destruct (tq_take_wr_cases _ _ _ _ _ Hw) as [Hg | [Hb | [Hl | Hh]]];
      unfold TAKE_BODY, TA_g_s, TW.SZ_g_s, SHADOW_OFF in *; lia. }
(* tq_tk_at at take's return *)
rewrite T1. change (Z_to_bv 64 (BASE + 35316)) with (Z_to_bv 64 (BASE + TQ_TK)).
assert (KW : forall a, sp1 <= a < sp1 + 76 -> aview segs (w_H W3) mem5 a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite KW5 by (lia || (intros Ho; pose proof (tq_outs_bounds sp1 a Ho); lia)). apply KS. lia. }
apply (TK LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F B0 B1 body X
  allow len hd taken ly3 S3 W3 mem5 md5 (0 + e3) regs5 HFIX).
- split; [exact HC5|]. rewrite <- Hnow56. apply rdword_ext. intros i Hi. apply KW. lia.
- rewrite <- H48. apply rdword_ext. intros i Hi. apply KW. lia.
- exact Xtw.
- exact Xgf.
- exact HINV.
- exact HL0.
- exact HT.
- exact Hm.
- exact HXL.
- exact HXF.
- exact HXG.
- exact XL.
- exact XH.
- intros i Hi. rewrite KF5 by lia. exact (HZ48' i Hi).
- rewrite KF5 by lia. exact HZ233'.
- refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))) (conj _ (conj _ (conj _ (conj _ _))))).
  + exact (eq_trans (HP5 2 ltac:(hnf; lia)) T2).
  + exact (eq_trans (HP5 3 ltac:(hnf; lia)) (eq_trans T3 (eq_sym Hgp))).
  + exact (eq_trans (HP5 4 ltac:(hnf; lia)) (eq_trans T4 (eq_sym Htp))).
  + exact (eq_trans (HP5 8 ltac:(hnf; lia)) T8).
  + exact (eq_trans (HP5 9 ltac:(hnf; lia)) T9).
  + exact (eq_trans (HP5 18 ltac:(hnf; lia)) T18).
  + exact (eq_trans (HP5 27 ltac:(hnf; lia)) T27).
  + exact (eq_trans (HP5 19 ltac:(hnf; lia)) T19).
  + exact (eq_trans (HP5 20 ltac:(hnf; lia)) T20).
  + exact (eq_trans (HP5 21 ltac:(hnf; lia)) T21).
  + exact (eq_trans (HP5 22 ltac:(hnf; lia)) T22).
  + exact (eq_trans (HP5 24 ltac:(hnf; lia)) T24).
- exact (eq_trans (HP5 25 ltac:(hnf; lia)) T25).
- exact X10.
Qed.
End bd.
