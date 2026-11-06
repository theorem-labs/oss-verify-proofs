(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths, module names and numbers changed; 569 of its 656 lines of code are new or changed and 678 lines of the source are left out. *)
(* on_announce_seg_fn: Lemma onann_fn_piece : onann_fn_stmt (lib/B/Prog/OnannCutB.v), the foreign-notice piece of
   on_announce's image-B walk: code +0x4e4 .. +0x5b0 of the listing lib/B/Prog/DgnTransportBList.v
   (fuzz_transport.asan-ubsan 0x881ac .. 0x88278; diginet_session.c:216-219), ending at the second inlined session_lost
   cut onann_sl2_at (+0x5b4) or at the release cut onann_fnrel_at (+0x5f4), which it is given.

   What the code does. +0x4e4 `lb a1, 0(a1)` / `bne a1, zero`: the check of the store at s + 136 (its shadow byte, 0:
   g_s's payload lies in the record's zero shadow, on_announce_cg.v trans_onann_cells); s5 = fn = F + 224; the store of
   1 at s + 136 (:216, the world is Bf = set_S_foreign B2 1); fn's shadow bytes 28 .. 36 := 0; the store of 6
   (N_FOREIGN) at fn; through the spill slots sp1 + 32 / sp1 + 40 the checked load of the state; the stores at fn + 4
   (the state), fn + 8 (8 zero bytes), fn + 16 (fp); the check of the store at fn + 24 (fn's shadow byte 31, zeroed
   above); a (from sp1 + 16) at fn + 24; `jal __asan_memset` (+0x568; fn + 32, 0, 40); the checks of the loads at
   s + 96 and s + 104 through sp1 + 8 / sp1 + 0; a2 = notify, a0 = ctx, a1 = fn; `jalr a2` (+0x590): notice
   (notice_cg.v transport_notice_cg) with onann_fntc Bf b; after it the checked load of the state of notice's world B3
   through sp1 + 32 / sp1 + 40, `addiw a0, a0, -1`, `li a1, 1` and `bltu a1, a0` (+0x5b0).
   The runs (the token engine over the caller's G journal, lib/B/Prog/TransportGRunB.v), from the states of
   on_announce_seg_fnb.v:
     run 1   +0x4e4 .. +0x568  from ss_ofn; it stops at the memset's call, which TransportGCg.v gx_intrin_at takes;
     run 2   +0x56c .. +0x590  the regions kept over the memset (YC1h.v jafter_call_keep_hi); through `jalr a2`, whose
                               register holds notice's code pointer (the 8 bytes at s + 96), to notice's entry;
     run 3   +0x594 .. +0x5b0  from ss_ofn3 at notice's return; it stops at the `bltu`, which is split from a state with
                               no region (DgnTransportBPaLib.v psrr_branch_tok); each arm runs one instruction to its
                               cut.
   notice's premises: the journal at the call state (the own frame owned); ra = +0x594; trans_ntc_at
   (on_announce_seg_fnb.v ofn_ntc_at: the 72 bytes at fn, the announce at a = F + 32 as onann_a_ok gives it, kept by
   the runs); trans_tframe_at and trans_rom_view_rd from the cut's facts at the call memory (on_announce_seg_kit.v
   onann_tf_cur / onann_rom_cur over on_announce_seg_fnb.v ofn_cur_step); tw_at at Bf (TWorldG.v tw_write of the
   store at s + 136); notice_m from onann_k_fn (ofn_model); notice_apart (ofn_apart); the N_DATA premise is vacuous;
   no event. Its post folds into the cut's facts by TransportGCg.v dk_kept_trans_nf_g (its written range is
   onann_wr's foreign-notice row: on_announce_seg_kit.v onann_wr_fntc); B3 = set_GOT_foreign Bf d
   (onann_fg_world), so g_fail_next B3 = g_fail_next B2 (onann_same_foreign, onann_same_gforeign).
   The branch (on_announce_seg_fnb.v ofn_bltu): taken (neither S_WAKING nor S_ONLINE) to onann_fnrel_at with the
   model's world Bw' = B3 (OnannCutB.v onann_k_fs); not taken to onann_sl2_at with session_lost_m at B3.
   Trap and error paths on this piece: the slow paths of the checks of s + 136, s + 112 (twice), s + 96, s + 104 (the
   shadow bytes of g_s's payload are 0) and of fn + 24 (fn's shadow byte 31 is 0 since +0x518). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_seg_kit on_announce_seg_fnb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TGNA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ofn_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ofn_reg: no match for" T; fail
  end.
(* Register n (a callee-saved register the runs left as its atom) of HS is the start valuation's, i.e. the start
   register's (Elo: the run's valuation agrees below atom 1024; EE: the start valuation reads the registers). *)
Ltac ofn_kreg HS Elo EE n Q H :=
  let rz := eval vm_compute in (Z.of_nat n) in
  lazymatch type of Q with _ = ?v =>
    ofn_reg HS (Z_to_bv 5 rz) v H
      ltac:(cbn [sv_denot]; try rewrite (Elo n ltac:(lia)); rewrite (EE n (Z_to_bv 5 rz) eq_refl),
            Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac ofn_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac ofn_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case closed
   by tac. *)
Ltac ofn_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.
Ltac ofn_name_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md := m) in *; clearbody md end.
Ltac ofn_lo HS E0 Hlo m :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  end.

(* The write rights of runs 1 and 2 (from the five regions of ss_ofn): fn's shadow bytes and fn's bytes are the own
   frame's (TransportGFrame.v awr_ok_x_cons_own), s + 136 .. s + 140 a byte range of G; the other two regions write
   nothing. *)
Ltac ofn_awr U18 U19 EFA2 :=
  ofn_awr_rs;
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA2; change (fs_frame_bytes ONANN_CID / 8) with 64; lia
  |];
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite EFA2; change (fs_frame_bytes ONANN_CID) with 512; lia |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    apply ofn_inG_gs; unfold ONANN_S, TB_g_s, TW.SZ_g_s in *; lia |];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

Section ofn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The bytes the piece may change between the cut and the call of notice: fn's shadow bytes 28 .. 36, fn's 72
   bytes, g_s.foreign, and the stack window of __asan_memset below sp1. *)
Definition ofn_Z (F sp1 : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 28 <= x < SHADOW_OFF + F / 8 + 37) \/ (F + 224 <= x < F + 296) \/
  (ONANN_S + 136 <= x < ONANN_S + 140) \/ (sp1 - ESTACK <= x < sp1).

(* The 10 bytes of a field the parse left (TSess.v ann_field). *)
Lemma ofn_annf_len : forall src, (length (TSS.ann_field src) <= 10)%nat.
Proof.
  intros src. unfold TSS.ann_field. rewrite length_app, length_firstn. cbn [length].
  rewrite DSpec.copy_len_strz. pose proof (DSpec.strz_len_le src). lia.
Qed.

Lemma ofn_holds : @onann_fn_stmt fx rc B MT.
Proof.
unfold onann_fn_stmt. intros SL2 FNREL. unfold onann_fn_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F B2
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HOC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof CALLEES as (HSMR & HANP & HPFN & HBCMP & HMS & HN & HSS & HWK & HMO & HSH).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hgf &
  Hm & HTF & HTFG & Hrom & Hapart & Hri & Hc3 & Hc1 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HCUR0 & Htw2 & Hb2 & Hk & Hgf2 & Haok & Harm & Hntf & Hsl16).
pose proof HCUR0 as (HJ1 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof Haok as (HAv & HAn & HA24 & HA32 & HAsh).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25) & R20 & R24) & R10 & R11 & R22 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (onann_cur_ar B MT LAWS HFIX HCUR0) as (HARc & HAR2 & Elo & Ehi & Efa & Efl & Hin2 & EFA2 & HFb & HFsh &
  HFnG & HF4096 & HF64' & HFce & HFapp' & Hceil & Hlo2 & Hhi2 & H47 & HFLp & HFLo & HFLr & HFLs1 & HFLs2 & Hsp1 &
  Hsp132 & Hsp146).
pose proof HJ0 as (HSTKJ & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil0 & Hslo & Hshi & H47' & _).
clear HJi memS.
(* the windows *)
assert (EST : ESTACK = 4096) by reflexivity.
assert (HSTK : ONANN_STK = 208 + WAKE_STK) by reflexivity.
assert (HWN : NOTICE_STK <= WAKE_STK) by (vm_compute; discriminate).
assert (HWE : 4096 <= WAKE_STK) by (vm_compute; discriminate).
assert (HEVN : NOTICE_EV = 0) by reflexivity.
assert (HEV0 : 0 <= ONANN_EV) by (vm_compute; discriminate).
assert (Hsp116 : sp1 mod 16 = 0).
{ pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp132, Z.add_0_r in D. rewrite D.
  replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the frame *)
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
assert (HFG : F + 512 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 512) ONANN_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (ONANN_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso. destruct (Z_le_gt_dec F ONANN_S) as [h3|h3].
  - apply (HFnG ONANN_S ltac:(lia)). apply ofn_inG_gs. unfold TW.SZ_g_s in *. lia.
  - apply (HFnG F ltac:(lia)). apply ofn_inG_gs. unfold TW.SZ_g_s in *. lia. }
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64', Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (HSHF : SHADOW_OFF + F / 8 + 64 <= F \/ F + 512 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp'. destruct HFapp' as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
assert (HFSG : F + 512 <= OFN_SH96 \/ OFN_SH96 + 6 <= F).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp'. destruct HFapp' as (_ & [HL | (HH1 & HH2)]);
  [left | right]; unfold OFN_SH96; lia. }
(* the model *)
assert (HL2 : length B2 = Z.to_nat TW.W_LEN) by exact (proj1 Htw2).
destruct (onann_same_foreign B2 1 HL2) as (EBfL & EBfS & EBfN & _ & _ & _ & _ & EBfG & _).
set (Bf := TW.set_S_foreign B2 1) in *.
destruct (ofn_model TF Bf b Bw' Hk) as (B3 & HCN & HNT & HNM & HFS).
assert (HNT2 : TW.S_notify B2 = TI.ti_notice timg_B) by (rewrite <- EBfN; exact HNT).
destruct (onann_fg_world TF Bf b B3 HCN) as (d3 & EB3).
destruct (onann_same_gforeign Bf d3 ltac:(rewrite EBfL; exact HL2)) as (_ & _ & _ & _ & _ & _ & _ & EB3G & _).
rewrite <- EB3 in EB3G.
assert (Hgf3 : TW.g_fail_next B3 <= 1) by (rewrite EB3G, EBfG; exact Hgf2).
(* +0x4e4 .. +0x568: run 1, up to `jal __asan_memset` *)
pose proof (ofn_entry (fx := fx) B ly2 S2 W2 regs2 mem2 md2 B2 F sp1 HOC HAR2 Htw2 HNT2 R18 R19 R9 R24 R10 R11 R26 R27
  HF4096 HF64' ltac:(lia) HFapp' HFG Hsp146 ltac:(lia) Hsp132 ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))
  Hntf Harm Hsl16) as HS.
set (E0 := ofn_E regs2 B2) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ofn_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; exact (ofn_ew regs2 B2 n r Hn)).
assert (U18 : bv_unsigned (ew E0 18) = SHADOW_OFF + F / 8)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U19 : bv_unsigned (ew E0 19) = F)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E0 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs OFN_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
paj_run_tok RUN HS HJ1 SHOK OFN_B0.
{ ofn_awr U18 U19 EFA2. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ ofn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (ofn_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  ofn_win Hiw Hx ltac:(rewrite ?U18, ?U19 in Hx; unfold ofn_Z, ONANN_S, TB_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia]). }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (ZS1 : forall i, 28 <= i < 37 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U18.
  assert (Hi' : i = 28 \/ i = 29 \/ i = 30 \/ i = 31 \/ i = 32 \/ i = 33 \/ i = 34 \/ i = 35 \/ i = 36) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (ofn_chunk0 E0 (w_H W2) (ms_mem ms) (Some 18%nat) _ _ _ _ _ _ RG0); ofn_in. }
clear HF HFr HG RG0.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem ms) md1 ONANN_CID pos HAR1 Hin2) as (_ & _ & HFb1 & HFsh1).
rewrite EFA2 in HFb1, HFsh1. change (fs_frame_bytes ONANN_CID / 8) with 64 in HFsh1.
pmkst HS.
ofn_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 256)) Q10 ltac:(cbn [sv_denot]; rewrite U19; reflexivity).
ofn_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
ofn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 40) Q12 ltac:(reflexivity).
ofn_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
ofn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 28564)) Q1 ltac:(apply codeptr_val; exact HEI).
ofn_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
ofn_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x568: __asan_memset (fn + 32, 0, 40), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OSet (transportb_sigma TB___asan_memset)
    (HMS fx) TG.G_HARNESS_B W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 md1
    (k + 0) (F + 256) 0 40 (sp1 - sp0) (Z_to_bv 64 (BASE + 28564)) HGX G_HARNESS_B_rw HJ1 Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite QSP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite Hsp132, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|]. intros a Ha. left. rewrite QSP. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists ONANN_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EFA2. change (fs_frame_bytes ONANN_CID) with 512. lia.
    + lia.
  - apply (amem_range_sub_app F 512); [exact HFapp' | lia | lia | lia | lia].
  - apply (TGNA.frame_ra_zero _ F (F + 256) 40 32 37); [lia | exact DFm8 | lia | lia |].
    intros i Hi. exact (ZS1 i ltac:(lia)).
  - intros _. apply (TGNA.frame_hull_vis _ F 512 (F + 256) 40); [lia | exact HF64' | reflexivity | lia | lia | lia |].
    intros i Hi. apply can_aview_vis. exact (proj1 (HFsh1 i Hi)).
  - exact I. }
cbv beta. intros Wm c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ ofn_Z F sp1 a ->
  aview segs (w_H W2) memM a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite HeffM; [exact (KR1 a Ha Hn) | exact Ha | |].
  - intros Hd. apply Hn. right. left. lia.
  - intros Hd. apply Hn. right. right. right. lia. }
assert (GAM : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memM a) by (intros a Ha; exact (HgrM a (GA1 a Ha))).
jafter_call_keep_hi HS 1024%nat regsM (mrestrict (w_H W2) memM) HPM [0%nat; 1%nat; 2%nat; 3%nat; 4%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 18%nat (SHADOW_OFF + F / 8)); [exact U18 | | exact HgrM].
    intros a Ha. unfold SHADOW_OFF in *. apply HeffM; [lia | destruct HSHF; lia | lia].
  - apply (region_kept_aview _ _ _ _ 19%nat F); [exact U19 | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply ofn_rk_none; [| exact HgrM]. intros a Ha. unfold ONANN_S, TB_g_s in *.
    apply HeffM; [lia | destruct HFG; unfold ONANN_S, TB_g_s, TW.SZ_g_s in *; lia | lia].
  - apply (region_kept_aview _ _ _ _ 9%nat sp1); [exact U9 | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply ofn_rk_none; [| exact HgrM]. intros a Ha. unfold OFN_SH96 in *.
    apply HeffM; [lia | destruct HFSG; lia | lia]. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regsM) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U18b : bv_unsigned (ew E1 18) = SHADOW_OFF + F / 8) by (rewrite E1lo by lia; exact U18).
assert (U19b : bv_unsigned (ew E1 19) = F) by (rewrite E1lo by lia; exact U19).
assert (SHOK1 : sh_ok segs OFN_Bx (@nil shent) E1 (mrestrict (w_H W2) memM)) by constructor.
assert (ZMM : forall a, F + 256 <= a < F + 296 -> aview segs (w_H W2) memM a = Some 0).
{ intros a Ha. replace a with ((F + 256) + (a - (F + 256))) by lia.
  rewrite (HsetM (a - (F + 256)) ltac:(lia)). reflexivity. }
clear dependent ms.
(* +0x56c .. +0x590: run 2, through `jalr a2` to notice's entry *)
paj_run_to_tok RUNTO HS HJ2 SHOK1 OFN_B0 AF_notice.
{ ofn_awr U18b U19b EFA2. }
set (md3 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md3. clear mat.
assert (KRN : forall a, 0 <= a < 2 ^ 64 -> ~ ofn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) memM a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (ofn_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  ofn_win Hiw Hx ltac:(rewrite ?U18b, ?U19b in Hx; unfold ofn_Z, ONANN_S, TB_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia]). }
assert (ZMN : forall a, F + 256 <= a < F + 296 -> aview segs (w_H W2) (ms_mem ms) a = Some 0).
{ intros a Ha. rewrite <- (ZMM a Ha).
  apply (kept_of_frame _ _ _ _ _ (fun x => (SHADOW_OFF + F / 8 + 28 <= x < SHADOW_OFF + F / 8 + 37) \/
    (F + 224 <= x < F + 256) \/ (ONANN_S + 136 <= x < ONANN_S + 140)) HFr); [| lia |].
  - intros b0 wlo whi x Hiw Hx. cbv beta.
    ofn_win Hiw Hx ltac:(rewrite ?U18b, ?U19b in Hx; unfold ONANN_S, TB_g_s;
      first [lia | left; lia | right; left; lia | right; right; lia]).
  - cbv beta. unfold ONANN_S, TB_g_s, SHADOW_OFF, TW.SZ_g_s in *.
    intros [Hx | [Hx | Hx]]; [destruct HSHF as [Hg | Hg]; lia | lia | destruct HFG as [Hg | Hg]; lia]. }
assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ ofn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; rewrite (KRN a Ha Hn); exact (KAM a Ha Hn)).
assert (GAN : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAM a Ha))).
clear HF HFr HG.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS2.
cbn [ms_mem restrict] in RS0, RS1, RS2.
assert (ZSN : forall i, 28 <= i < 37 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U18b.
  assert (Hi' : i = 28 \/ i = 29 \/ i = 30 \/ i = 31 \/ i = 32 \/ i = 33 \/ i = 34 \/ i = 35 \/ i = 36) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (ofn_chunk0 E1 (w_H W2) (ms_mem ms) (Some 18%nat) _ _ _ _ _ _ RS0); ofn_in. }
assert (ZAN : forall i, 4 <= i < 9 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite KAN; [exact (HAsh i Hi) | unfold SHADOW_OFF; lia |].
  unfold ofn_Z, ONANN_S, TB_g_s, SHADOW_OFF. intros [Hx | [Hx | [Hx | Hx]]]; [lia | destruct HSHF as [Hg | Hg];
    unfold SHADOW_OFF in Hg; lia | lia | lia]. }
(* the notice's bytes at the call *)
assert (E32 : ew E1 32 = Z_to_bv 64 (TW.u_at B2 (TW.OFF_g_s + 112) 4))
  by (rewrite E1lo by lia; exact (ofn_ew32 regs2 B2)).
pose proof (ofn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 224 4 (SLit 6) RS1 ltac:(ofn_in) ltac:(lia)) as VP0.
pose proof (ofn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 228 4 (SExt true 32 (SOff 32 0)) RS1
  ltac:(ofn_in) ltac:(lia)) as VP4.
pose proof (ofn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 232 8 (SLit 0) RS1 ltac:(ofn_in) ltac:(lia)) as VP8.
pose proof (ofn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 240 8 (SOff 22 0) RS1 ltac:(ofn_in) ltac:(lia)) as VP16.
pose proof (ofn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 248 8 (SOff 19 32) RS1 ltac:(ofn_in) ltac:(lia)) as VP24.
pose proof (ofn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 6158024 4 (SLit 1) RS2 ltac:(ofn_in) ltac:(lia)) as VG.
cbn [base_val] in VP0, VP4, VP8, VP16, VP24, VG.
rewrite U19b in VP0, VP4, VP8, VP16, VP24.
rewrite (ofn_sext32 E1 B2 E32) in VP4.
assert (D19 : sv_denot E1 (SOff 19 32) = Z_to_bv 64 (F + 32)) by (cbn [sv_denot]; rewrite U19b; reflexivity).
rewrite D19, unsigned_lit_small in VP24 by lia.
change (8 * Z.of_N 8) with 64 in VP24. rewrite Z.mod_small in VP24 by lia.
change (N.to_nat 8) with 8%nat in VP8, VP16, VP24. change (N.to_nat 4) with 4%nat in VP0, VP4, VG.
change (bv_unsigned (sv_denot E1 (SLit 6)) mod 2 ^ (8 * Z.of_N 4)) with 6 in VP0.
change (bv_unsigned (sv_denot E1 (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in VP8.
change (bv_unsigned (sv_denot E1 (SLit 1)) mod 2 ^ (8 * Z.of_N 4)) with 1 in VG.
apply (ofn_vm_w _ _ 4 (TW.S_state B2) ltac:(lia)) in VP4.
change (N.to_nat 4) with 4%nat in VP4.
set (fpz := bv_unsigned (sv_denot E1 (SOff 22 0)) mod 2 ^ (8 * Z.of_N 8)) in VP16.
pose proof (ofn_nb (w_H W2) (ms_mem ms) F (TW.S_state B2) fpz (F + 32) VP0 VP4 VP8 VP16 VP24 ZMN) as HNB.
(* the announce at a = F + 32, kept by the runs *)
assert (HAvN : garr8 segs (mrestrict (w_H W2) (ms_mem ms)) (F + ONANN_A)
  (map DSpec.bz (TSS.ann_field (skipn 15 (DSpec.fr_body b))))).
{ eapply garr8_frame; [exact HAv|]. intros a Ha. rewrite length_map in Ha.
  pose proof (ofn_annf_len (skipn 15 (DSpec.fr_body b))). unfold ONANN_A in Ha.
  apply (mbyte_of_aview segs). apply KAN; [lia|].
  unfold ofn_Z, ONANN_S, TB_g_s, SHADOW_OFF. intros [Hx | [Hx | [Hx | Hx]]];
    [destruct HSHF as [Hg | Hg]; unfold SHADOW_OFF in Hg; lia | lia | destruct HFG as [Hg | Hg];
     unfold ONANN_S, TB_g_s, TW.SZ_g_s in Hg; lia | lia]. }
assert (HAnN : garr8 segs (mrestrict (w_H W2) (ms_mem ms)) (F + ONANN_A + 10)
  (map DSpec.bz (TSS.ann_field (skipn 24 (DSpec.fr_body b))))).
{ eapply garr8_frame; [exact HAn|]. intros a Ha. rewrite length_map in Ha.
  pose proof (ofn_annf_len (skipn 24 (DSpec.fr_body b))). unfold ONANN_A in Ha.
  apply (mbyte_of_aview segs). apply KAN; [lia|].
  unfold ofn_Z, ONANN_S, TB_g_s, SHADOW_OFF. intros [Hx | [Hx | [Hx | Hx]]];
    [destruct HSHF as [Hg | Hg]; unfold SHADOW_OFF in Hg; lia | lia | destruct HFG as [Hg | Hg];
     unfold ONANN_S, TB_g_s, TW.SZ_g_s in Hg; lia | lia]. }
(* the registers at notice's entry *)
ofn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 28604)) T1 ltac:(apply codeptr_val; exact HEI1).
ofn_reg HS (Z_to_bv 5 11) (w64 (F + 224)) T11 ltac:(cbn [sv_denot]; rewrite U19b; reflexivity).
ofn_kreg HS E1lo EE 2%nat (eq_refl (YK11.getr regs2 (Z_to_bv 5 2))) T2.
ofn_kreg HS E1lo EE 3%nat (eq_refl (YK11.getr regs2 (Z_to_bv 5 3))) T3.
ofn_kreg HS E1lo EE 4%nat (eq_refl (YK11.getr regs2 (Z_to_bv 5 4))) T4.
ofn_kreg HS E1lo EE 8%nat (eq_refl (YK11.getr regs2 (Z_to_bv 5 8))) T8.
ofn_kreg HS E1lo EE 9%nat (eq_refl (YK11.getr regs2 (Z_to_bv 5 9))) T9.
ofn_kreg HS E1lo EE 18%nat (eq_refl (YK11.getr regs2 (Z_to_bv 5 18))) T18.
ofn_kreg HS E1lo EE 19%nat (eq_refl (YK11.getr regs2 (Z_to_bv 5 19))) T19.
ofn_kreg HS E1lo EE 20%nat (eq_refl (YK11.getr regs2 (Z_to_bv 5 20))) T20.
ofn_kreg HS E1lo EE 24%nat (eq_refl (YK11.getr regs2 (Z_to_bv 5 24))) T24.
ofn_kreg HS E1lo EE 25%nat (eq_refl (YK11.getr regs2 (Z_to_bv 5 25))) T25.
pmkst HS.
set (regsC := ms_regs ms) in *. set (memN := ms_mem ms) in *.
assert (USPC : spZ regsC = sp1)
  by (change (bv_unsigned (YK11.getr regsC (Z_to_bv 5 2)) = sp1); rewrite T2; exact USP).
assert (EBR : BASE + 28604 = 0x8825c) by reflexivity.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_B) regsC memN md3) Qx) end.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARN.
(* the cut's facts at the call memory *)
assert (CURN : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 memN md3 0).
{ apply (ofn_cur_step B MT LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F ly2 S2 W2 mem2 memN md2 md3 0 (ofn_Z F sp1) HFIX HCUR0 HJ2).
  - intros a [Hz | [Hz | [Hz | Hz]]].
    + right; left; right; left. change (fs_frame_bytes ONANN_CID / 8) with 64. lia.
    + right; left; left. change (fs_frame_bytes ONANN_CID) with 512. lia.
    + right; right. apply ofn_inG_gs. unfold TW.SZ_g_s. lia.
    + left; lia.
  - intros a [Hz | [Hz | [Hz | Hz]]] Hf.
    + destruct HSHF; lia.
    + lia.
    + destruct HFG as [Hg | Hg]; unfold ONANN_S, TB_g_s, TW.SZ_g_s in *; lia.
    + lia.
  - exact KAN.
  - exact GAN. }
pose proof (onann_tf_cur B MT LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F ly2 S2 W2 memN md3 0 regsC NOTICE_STK HFIX CURN ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)) as TFN.
pose proof (onann_rom_cur B MT LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F ly2 S2 W2 memN md3 0 HFIX CURN) as ROMN.
(* the world relation at the call: the store of :216, every other byte of G kept *)
assert (PTW : tw_at TMAP_B (aview segs (w_H W2) memN) Bf).
{ unfold Bf. rewrite onann_st_foreign.
  apply (tw_write TMAP_B (aview segs (w_H W2) mem2) _ B2 TW.OFF_g_s TB_g_s TW.SZ_g_s 136 4 1 TMAP_B_ok Htw2
    TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. replace (TB_g_s + 136 + Z.of_nat j) with (0 + 6158024 + Z.of_nat j) by (unfold TB_g_s; lia).
    exact (ofn_aview_of_val _ _ _ 4 1 VG j Hj).
  - intros x Hx Hn. destruct Hx as (o & b0 & n0 & Hin3 & Hx).
    assert (HxG : inG TG.G_HARNESS_B x) by exact (ofn_inG b0 n0 x (TMAP_B_in_G o b0 n0 Hin3) Hx).
    pose proof (inG_low segs B transportb_segs_low _ x HGX HxG) as Hl. unfold kLowMemEnd in Hl.
    apply KAN; [lia|]. unfold ofn_Z. intros [Hz | [Hz | [Hz | Hz]]].
    + unfold SHADOW_OFF in Hz. lia.
    + exact (HFnG x ltac:(lia) HxG).
    + apply Hn. unfold ONANN_S in Hz. lia.
    + lia. }
(* +0x590: notice, at TI.ti_notice timg_B, with ra = +0x594 *)
eapply SRr_bind.
{ exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 memN md3 (k + 0) regsC
    (F + 224) (onann_fntc Bf b) TF Bf B3
    HJ2
    ltac:(rewrite T1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite T1, EBR; rewrite unsigned_lit_small by lia; lia)
    (eq_trans T3 (eq_trans R3 Hgp)) (eq_trans T4 (eq_trans R4 Htp)) T11
    ltac:(rewrite USPC; exact Hsp116)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    (ofn_ntc_at B ly2 S2 W2 memN md3 regsC Bf b (TW.S_state B2) fpz F pos LAWS HARN Hin2 EFA2 HF4096 HF64' HFce
       HFapp' ltac:(rewrite USPC; lia) ZSN ZAN (eq_sym EBfS) HNB HAvN HAnN)
    TFN ROMN PTW HNM
    (ofn_apart B ly2 S2 W2 mem2 md2 W2 memN TF Bw b Bf (TW.S_state B2) fpz F pos LAWS HGX HAR2 Hin2 EFA2
       ltac:(lia) ltac:(lia) Hapart HNB)
    ltac:(intros HD; exfalso; unfold onann_fntc in HD; cbn [TI.n_kind] in HD;
          unfold TS0.DIGINET_N_FOREIGN, TC.N_DATA in HD; discriminate HD)
    ltac:(lia)). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3).
assert (He30 : e3 = 0) by (unfold NOTICE_EV in He3; lia). subst e3.
replace (k + 0 + 0) with (k + 0) in HJ3 by lia.
assert (ELF3 : ly_F ly3 = ly_F lyc).
{ pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
  pose proof HJi3 as (_ & Hly3 & _). pose proof Hly3 as (_ & _ & _ & _ & _ & E3 & _).
  pose proof Hlyle as (_ & _ & _ & _ & _ & Ec & _). rewrite E3, Ec. reflexivity. }
(* what the call kept, from its entry to notice's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ pose proof CURN as (_ & _ & _ & _ & _ & _ & KCN & _ & _).
  destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 memN md3 ONANN_CID pos F
    (flag_addr lyc ONANN_CID pos) HARN Hfrs Hbl2 HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
  apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 memN W3 mem3
    (spZ regs - ONANN_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (onann_wr Bw b)
    (notice_wr Bf (onann_fntc Bf b)) (dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos))).
  - lia.
  - lia.
  - exact Efa.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - exact Hbl2.
  - exact N1.
  - exact N3.
  - exact KCN.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. exact (onann_wr_fntc Bf Bf Bw b a Ha). }
pose proof HK3 as (K31 & _ & _ & K34 & _).
assert (KSTK : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) memN a).
{ intros a Ha. rewrite USPC in K31. apply K31; lia. }
assert (KFL : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) mem3 (F + 504 + i) = aview segs (w_H W2) memN (F + 504 + i)).
{ intros i Hi. apply (K34 ONANN_CID pos (F + 504 + i) Hin2).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA2. change (fs_frame_bytes ONANN_CID) with 512. lia.
  - intros Hw. exact (HFnG (F + 504 + i) ltac:(lia) (notice_wr_G _ _ _ Hw)). }
(* the cut's facts at notice's return *)
assert (CUR3 : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mem3 md4 0).
{ pose proof CURN as (_ & _ & _ & _ & _ & HmoN & _ & HSVN & HFLN).
  refine (conj HJ3 (conj _ (conj _ (conj _ (conj ELF3 (conj _ (conj KC3 (conj _ _)))))))).
  - lia.
  - rewrite Hfr3. exact Hfrs.
  - exact (Permutation_trans Hperm3 Hperm).
  - exact (mo_le_trans MT MTL Sc S2 S3 0 0 HmoN Hmo3).
  - rewrite Forall_forall in HSVN |- *. intros o Ho. rewrite <- (HSVN o Ho).
    assert (Hob : 8 <= fst o <= 104).
    { unfold ONANN_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
    apply YCbq.rdword_ext. intros i Hi. apply KSTK. lia.
  - unfold ONANN_FBYTES in HFLN |- *. rewrite <- HFLN. replace (F + 512 - 8) with (F + 504) by lia.
    apply YCbq.rdword_ext. intros i Hi. exact (KFL i Hi). }
(* the spill slots run 3 reads, at notice's return *)
assert (Harm3 : onann_slots_arm W3 mem3 sp1).
{ destruct Harm as (Hs32 & Hs40). unfold onann_slots_arm, onann_slot in *. split.
  - rewrite <- Hs32. apply YCbq.rdword_ext. intros i Hi. rewrite KSTK by lia. apply KAN; [lia|].
    unfold ofn_Z, ONANN_S, TB_g_s, SHADOW_OFF. intros [Hx | [Hx | [Hx | Hx]]]; lia.
  - rewrite <- Hs40. apply YCbq.rdword_ext. intros i Hi. rewrite KSTK by lia. apply KAN; [lia|].
    unfold ofn_Z, ONANN_S, TB_g_s, SHADOW_OFF. intros [Hx | [Hx | [Hx | Hx]]]; lia. }
(* the registers notice keeps *)
assert (CH : forall n, acallee_saved n -> YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr regsC (Z_to_bv 5 n))
  by (intros n Hn; exact (HP3 n Hn)).
assert (Y2 : YK11.getr regs3 (Z_to_bv 5 2) = YK11.getr regs2 (Z_to_bv 5 2)) by exact (eq_trans (CH 2 ltac:(hnf; lia)) T2).
assert (Y3 : YK11.getr regs3 (Z_to_bv 5 3) = YK11.getr regs2 (Z_to_bv 5 3)) by exact (eq_trans (CH 3 ltac:(hnf; lia)) T3).
assert (Y4 : YK11.getr regs3 (Z_to_bv 5 4) = YK11.getr regs2 (Z_to_bv 5 4)) by exact (eq_trans (CH 4 ltac:(hnf; lia)) T4).
assert (Y8 : YK11.getr regs3 (Z_to_bv 5 8) = YK11.getr regs2 (Z_to_bv 5 8)) by exact (eq_trans (CH 8 ltac:(hnf; lia)) T8).
assert (Y9 : YK11.getr regs3 (Z_to_bv 5 9) = YK11.getr regs2 (Z_to_bv 5 9)) by exact (eq_trans (CH 9 ltac:(hnf; lia)) T9).
assert (Y18 : YK11.getr regs3 (Z_to_bv 5 18) = YK11.getr regs2 (Z_to_bv 5 18))
  by exact (eq_trans (CH 18 ltac:(hnf; lia)) T18).
assert (Y19 : YK11.getr regs3 (Z_to_bv 5 19) = YK11.getr regs2 (Z_to_bv 5 19))
  by exact (eq_trans (CH 19 ltac:(hnf; lia)) T19).
assert (Y20 : YK11.getr regs3 (Z_to_bv 5 20) = YK11.getr regs2 (Z_to_bv 5 20))
  by exact (eq_trans (CH 20 ltac:(hnf; lia)) T20).
assert (Y24 : YK11.getr regs3 (Z_to_bv 5 24) = YK11.getr regs2 (Z_to_bv 5 24))
  by exact (eq_trans (CH 24 ltac:(hnf; lia)) T24).
assert (Y25 : YK11.getr regs3 (Z_to_bv 5 25) = YK11.getr regs2 (Z_to_bv 5 25))
  by exact (eq_trans (CH 25 ltac:(hnf; lia)) T25).
rewrite T1.
change (Z_to_bv 64 (BASE + 28604)) with (Z_to_bv 64 (BASE + ONFN_AFT)).
clear dependent ms.
(* +0x594 .. +0x5b0: run 3, the check of s + 112, the load of the state, `addiw`, `li a1, 1`; it stops at the
   `bltu` *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
assert (R9C : YK11.getr regs3 9 = w64 sp1) by exact (eq_trans Y9 R9).
pose proof (ofn_entry3 (fx := fx) B ly3 S3 W3 regs3 mem3 md4 B3 sp1 HOC HAR3 Htw3 R9C Hsp146 ltac:(lia) Hsp132 Harm3)
  as HS.
assert (SHOK : sh_ok segs OFN_Bx [] (ofn_E3 regs3 B3) (mrestrict (w_H W3) mem3)) by constructor.
assert (HEI3 : img_env VAL A_LIM (ofn_E3 regs3 B3)) by (unfold ofn_E3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ofn_E3 regs3 B3) n = YK11.getr regs3 r)
  by (intros n r Hn; exact (ofn_ew3 regs3 B3 n r Hn)).
pose proof HJ3 as HJ.
paj_run_tok RUN HS HJ SHOK OFN_B0.
{ ofn_awr_rs.
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
ofn_name_md mdA.
ofn_lo HS (ofn_E3 regs3 B3) EAlo msA.
ofn_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (zalu32 ALU_ADD (TW.S_state B3) (-1))) XA10
  ltac:(apply ofn_a0; try rewrite (EAlo 32%nat ltac:(lia)); exact (ofn_ew3_32 regs3 B3)).
ofn_reg HS (Z_to_bv 5 11) (Z_to_bv 64 1) XA11 ltac:(reflexivity).
ofn_kreg HS EAlo EE3 2%nat Y2 XA2. ofn_kreg HS EAlo EE3 3%nat Y3 XA3. ofn_kreg HS EAlo EE3 4%nat Y4 XA4.
ofn_kreg HS EAlo EE3 8%nat Y8 XA8. ofn_kreg HS EAlo EE3 9%nat Y9 XA9. ofn_kreg HS EAlo EE3 18%nat Y18 XA18.
ofn_kreg HS EAlo EE3 19%nat Y19 XA19. ofn_kreg HS EAlo EE3 20%nat Y20 XA20. ofn_kreg HS EAlo EE3 24%nat Y24 XA24.
ofn_kreg HS EAlo EE3 25%nat Y25 XA25.
(* run 3 wrote no byte *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msA) a = aview segs (w_H W3) mem3 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
  intros b0 wlo whi x Hin Hx. cbv beta. ofn_win Hin Hx ltac:(lia). }
assert (GAa : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msA) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* +0x5b0: `bltu a1, a0`, taken up again from a state with no region *)
pmkst HS.
clear HS SHOK.
set (rA := ms_regs msA) in *. set (mA := ms_mem msA) in *. clearbody rA mA.
pose proof (ofn_entry0b (fx := fx) W3 rA mA ONFN_BR) as HS.
assert (SHOK : sh_ok segs OFN_Bx [] (ofn_Eb rA) (mrestrict (w_H W3) mA)) by constructor.
assert (HEIb : img_env VAL A_LIM (ofn_Eb rA)) by (unfold ofn_Eb; apply Eimg_env).
assert (EEb : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ofn_Eb rA) n = YK11.getr rA r)
  by (intros n r Hn; exact (ofn_ewb rA n r Hn)).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONFN_BR)) mm rom) mdx) Q) end.
assert (D10 : sv_denot (ofn_Eb rA) (SOff 10 0) = Z_to_bv 64 (zalu32 ALU_ADD (TW.S_state B3) (-1)))
  by (cbn [sv_denot]; rewrite (EEb 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact XA10).
assert (D11 : sv_denot (ofn_Eb rA) (SOff 11 0) = Z_to_bv 64 1)
  by (cbn [sv_denot]; rewrite (EEb 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact XA11).
assert (HSR : - 2 ^ 31 <= TW.S_state B3 < 2 ^ 31) by (rewrite onann_rd_state; apply TWL.s32_range).
psrr_branch_tok RUN BR HS SHOK OFN_B0.
- (* neither S_WAKING nor S_ONLINE: to the release cut +0x5f4; the model's world is B3 *)
  rewrite D11, D10, (ofn_bltu _ HSR) in Hc.
  apply negb_true_iff, orb_false_iff in Hc. destruct Hc as [Hq1 Hq2].
  apply Z.eqb_neq in Hq1. apply Z.eqb_neq in Hq2.
  assert (EBw' : B3 = Bw').
  { unfold onann_k_fs in HFS.
    replace ((TW.S_state B3 =? TS0.DIGINET_S_ONLINE) || (TW.S_state B3 =? TS0.DIGINET_S_WAKING)) with false in HFS
      by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; unfold TS0.DIGINET_S_ONLINE, TS0.DIGINET_S_WAKING;
          lia).
    cbv beta iota in HFS. exact (onann_some_inv _ _ HFS). }
  paj_run_to_tok RUNTO HS HJ SHOK OFN_B0 ONANN_FNREL.
  { ofn_awr_rs. apply awr_ok_x_nil. }
  ofn_name_md mdB.
  ofn_lo HS (ofn_Eb rA) EBlo msB.
  ofn_kreg HS EBlo EEb 2%nat XA2 Z2. ofn_kreg HS EBlo EEb 3%nat XA3 Z3. ofn_kreg HS EBlo EEb 4%nat XA4 Z4.
  ofn_kreg HS EBlo EEb 8%nat XA8 Z8. ofn_kreg HS EBlo EEb 9%nat XA9 Z9. ofn_kreg HS EBlo EEb 18%nat XA18 Z18.
  ofn_kreg HS EBlo EEb 19%nat XA19 Z19. ofn_kreg HS EBlo EEb 25%nat XA25 Z25.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msB) a = aview segs (w_H W3) mem3 a).
  { intros a Ha. rewrite <- (KA a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta. ofn_win Hin Hx ltac:(lia). }
  assert (GB : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAa a Ha))).
  pose proof (ofn_cur_step B MT LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F ly3 S3 W3 mem3 (ms_mem msB) md4 mdB 0 (fun _ => False) HFIX CUR3 HJ
    ltac:(intros a Ha; destruct Ha) ltac:(intros a Ha; destruct Ha) ltac:(intros a Ha _; exact (KB a Ha)) GB) as CURF.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_FNREL)) mm rom) mdx) Q) end.
  apply (FNREL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1
    F ly3 S3 W3 (ms_mem msB) mdB 0 (ms_regs msB) HFIX).
  + refine (conj CURF (conj _ _)).
    * rewrite <- EBw'. apply (tw_kept_GB (aview segs (w_H W3) mem3)); [exact Htw3|]. intros b0 n i Hbn Hi.
      assert (Hg : inG TG.G_HARNESS_B (b0 + i)) by exact (ofn_inG b0 n (b0 + i) Hbn ltac:(lia)).
      pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
      apply KB. lia.
    * rewrite <- EBw'. exact Hgf3.
  + unfold onann_regs_rel.
    refine (conj (eq_trans Z2 R2) (conj (eq_trans Z3 R3) (conj (eq_trans Z4 R4) (conj (eq_trans Z8 R8)
      (conj (eq_trans Z9 R9) (conj (eq_trans Z18 R18) (conj (eq_trans Z19 R19) (eq_trans Z25 R25)))))))).
- (* S_WAKING or S_ONLINE: to the second inlined session_lost +0x5b4 *)
  rewrite D11, D10, (ofn_bltu _ HSR) in Hc.
  apply negb_false_iff in Hc.
  assert (HST : TW.S_state B3 = TS0.DIGINET_S_ONLINE \/ TW.S_state B3 = TS0.DIGINET_S_WAKING).
  { apply orb_true_iff in Hc. unfold TS0.DIGINET_S_ONLINE, TS0.DIGINET_S_WAKING.
    destruct Hc as [Hc | Hc]; apply Z.eqb_eq in Hc; [right | left]; exact Hc. }
  assert (HSLm : TSS.session_lost_m timg_B TF B3 TS0.DIGINET_R_FOREIGN = Some (Bw', tt)).
  { unfold onann_k_fs in HFS.
    replace ((TW.S_state B3 =? TS0.DIGINET_S_ONLINE) || (TW.S_state B3 =? TS0.DIGINET_S_WAKING)) with true in HFS
      by (symmetry; apply orb_true_iff; destruct HST as [HS1 | HS1]; [left | right]; apply Z.eqb_eq; exact HS1).
    exact HFS. }
  paj_run_to_tok RUNTO HS HJ SHOK OFN_B0 ONANN_SL2.
  { ofn_awr_rs. apply awr_ok_x_nil. }
  ofn_name_md mdB.
  ofn_lo HS (ofn_Eb rA) EBlo msB.
  ofn_kreg HS EBlo EEb 2%nat XA2 Z2. ofn_kreg HS EBlo EEb 3%nat XA3 Z3. ofn_kreg HS EBlo EEb 4%nat XA4 Z4.
  ofn_kreg HS EBlo EEb 8%nat XA8 Z8. ofn_kreg HS EBlo EEb 9%nat XA9 Z9. ofn_kreg HS EBlo EEb 18%nat XA18 Z18.
  ofn_kreg HS EBlo EEb 19%nat XA19 Z19. ofn_kreg HS EBlo EEb 25%nat XA25 Z25.
  ofn_kreg HS EBlo EEb 20%nat XA20 Z20. ofn_kreg HS EBlo EEb 24%nat XA24 Z24.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msB) a = aview segs (w_H W3) mem3 a).
  { intros a Ha. rewrite <- (KA a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta. ofn_win Hin Hx ltac:(lia). }
  assert (GB : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAa a Ha))).
  pose proof (ofn_cur_step B MT LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F ly3 S3 W3 mem3 (ms_mem msB) md4 mdB 0 (fun _ => False) HFIX CUR3 HJ
    ltac:(intros a Ha; destruct Ha) ltac:(intros a Ha; destruct Ha) ltac:(intros a Ha _; exact (KB a Ha)) GB) as CURF.
  assert (TWF : tw_at TMAP_B (aview segs (w_H W3) (ms_mem msB)) B3).
  { apply (tw_kept_GB (aview segs (w_H W3) mem3)); [exact Htw3|]. intros b0 n i Hbn Hi.
    assert (Hg : inG TG.G_HARNESS_B (b0 + i)) by exact (ofn_inG b0 n (b0 + i) Hbn ltac:(lia)).
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
    apply KB. lia. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_SL2)) mm rom) mdx) Q) end.
  apply (SL2 LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1
    F B2 B3 ly3 S3 W3 (ms_mem msB) mdB (ms_regs msB) HFIX).
  + exact (conj CURF (conj TWF (conj Hb2 (conj HCN (conj (ex_intro _ d3 EB3) (conj HST (conj HSLm Hgf3))))))).
  + unfold onann_regs_ign, onann_regs_rel.
    refine (conj (conj (eq_trans Z2 R2) (conj (eq_trans Z3 R3) (conj (eq_trans Z4 R4) (conj (eq_trans Z8 R8)
      (conj (eq_trans Z9 R9) (conj (eq_trans Z18 R18) (conj (eq_trans Z19 R19) (eq_trans Z25 R25))))))))
      (conj (eq_trans Z20 R20) (eq_trans Z24 R24))).
Qed.

End ofn.

(* The foreign-notice piece of the walk of on_announce (OnannCutB.v onann_fn_stmt), at every machine, run ceiling,
   record and meter. *)
Lemma onann_fn_piece : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT, @onann_fn_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ofn_holds fx rc B MT). Qed.

Print Assumptions onann_fn_piece.
