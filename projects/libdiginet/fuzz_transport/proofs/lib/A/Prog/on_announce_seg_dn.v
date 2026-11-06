(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module names changed; 717 of its 819 lines of code are new or changed and 663 lines of the source are left out. *)
(* on_announce_seg_dn: the desk notice piece of on_announce's image-A walk, onann_piece_dn : onann_dn_stmt
   (lib/A/Prog/OnannCut.v), code +0x308 .. +0x3f0 (0x87d7c .. 0x87e64), from the cut onann_dn_at to the cuts
   onann_e0_at (+0x3f4, cmd 0xe0) and onann_e1_at (+0x548, cmd 0xe1).
   - Run 1 (+0x308 .. +0x394; PaRun token engine over the G journal, TransportGRunA.v paj_run_x): n's shadow bytes
     42 .. 50 := 0, the 4-byte store of 1 (N_DESK) at n, the checked load of g_s.state (s + 112), s + 112 at sp1 + 48,
     the stores of state, 8 zeros, fp, a (from sp1 + 56), p (s9) and off (a3) at n + 4 .. n + 40 (the check of the
     8-byte store at n + 24 reads shadow byte 45 through the alias s3 = (s2 >> 3) + SHADOW_OFF), s7 = off; then
     __asan_memset (n + 44, 0, 28) through TransportGCg.v gx_intrin_at.
   - Run 2 (+0x398 .. +0x3d4): s + 96 at sp1 + 24, the checks of the 8-byte loads at s + 96 and s + 104 (their shadow
     bytes' addresses at sp1 + 8 and sp1 + 16), a2 = g_s.notify, a0 = notify_ctx, a1 = n; `jalr a2` (+0x3d4) calls notice
     at TI.ti_notice timg_A (DgnTransportPaLib.v SRr_jalr_call_pi, notice_cg.v transport_notice_cg in the same G
     journal) with n read as onann_dntc (on_announce_seg_dnb.v dn_ntc_at), notice_apart (dn_apart), the current heap
     frame and the read-only bytes at the call (on_announce_seg_kit.v onann_tf_call, onann_rom_call); the call's kept
     facts fold by TransportGCg.v dk_kept_trans_nf_g.
   - Run 3 (+0x3d8 .. +0x3f0): the checked load of f + 30 (its shadow byte's address from sp1 + 32; the byte and its
     shadow byte 0 at notice's return from on_announce_seg_kitf.v onann_f30, f being 8-aligned), a1 = fr_cmd b,
     a2 = 0xe0, a0 = s + 136; `bne a1, a2` is taken up again from a
     state with no region (on_announce_seg_dnb.v ss_dnb) and runs one instruction to either cut.
   The world after notice is B2 = set_GOT_desk (onann_w1 ..) d (on_announce_seg_kit.v onann_dn_world), whose
   g_fail_next and run invariants are Bw's (on_announce_seg_dnb.v dn_w1, dn_desk_ri). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg SlostCut SlostNtcKit SlostNtc.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_seg_kit on_announce_seg_dnb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_seg_kitf.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The bytes the piece may change between the cut and the call of notice: n's shadow bytes 42 .. 50, n's 72 bytes, the
   stack window of __asan_memset below sp1 and the slots sp1 + 8 .. sp1 + 32 and sp1 + 48 .. sp1 + 56. *)
Definition dn_Z (F sp1 : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 42 <= x < SHADOW_OFF + F / 8 + 51) \/ (F + 336 <= x < F + 408) \/
  (sp1 - ESTACK <= x < sp1) \/ (sp1 + 8 <= x < sp1 + 32) \/ (sp1 + 48 <= x < sp1 + 56).

(* The write rights of runs 1 and 2: n's shadow bytes and n's bytes are the own frame's, the slots are in the
   journal's window, the g_s regions are read only. *)
Ltac dn_awr U9 U18 U19 EF2 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19 in Ha;
    right; unfold in_zr; cbn [fst snd]; rewrite EF2; unfold shadow_addr;
    change (fs_frame_bytes ONANN_CID / 8) with 128; lia |];
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite EF2; change (fs_frame_bytes ONANN_CID) with 1024; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha; left; split; [left; lia | lia] |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha; left; split; [left; lia | lia] |];
  apply awr_ok_x_nil.

(* A run's windows: every one inside dn_Z. *)
Ltac dn_win U9 U18 U19 :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hiw := fresh "Hiw" in let Hx := fresh "Hx" in
  intros b wlo whi x Hiw Hx; cbv beta;
  sn_win Hiw Hx ltac:(rewrite ?U9, ?U18, ?U19 in Hx; unfold dn_Z;
    first [lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; left; lia
          | right; right; right; right; lia]).

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac
   (SlostNtc.v sn_reg, which its section keeps local). *)
Local Ltac sn_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "sn_reg: no match for" T; fail
  end.

(* A register the run kept as its atom n: its value Q at the run's entry (E1lo: the atom below the havoc). *)
Local Ltac dn_kreg HS E1lo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    sn_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (E1lo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Local Ltac dn_kreg0 HS EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    sn_reg HS r v H ltac:(cbn [sv_denot]; rewrite (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.

(* A slot sp1 + o holding the literal v (a chunk of the region RS, base sp1). *)
Local Ltac dn_slot RS U9b v :=
  apply AF0x.val_mem_rdword; [unfold DN_SH, ONANN_S, TA_g_s; lia|];
  lazymatch goal with |- val_mem _ _ (_ + ?o) _ _ =>
    let V := fresh "V" in
    pose proof (sn_chunk_val _ _ _ _ _ _ _ _ _ o 8 (SLit v) RS
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as V;
    cbn [base_val] in V; rewrite U9b in V; change (N.to_nat 8) with 8%nat in V;
    apply (sn_vm_w _ _ 8 v ltac:(unfold DN_SH, ONANN_S, TA_g_s; lia)) in V; exact V end.

Section dn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The facts every cut carries move to a later memory whose view is the same at every address. *)
Lemma dn_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2
    (W2 : world segs) mem2 md2 mem3 md3 e,
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONANN_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 KD GR.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b0 m i Hb Hi Hn. rewrite KD. exact (K2 b0 m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. exact (AF0x.rdword_ext _ _ _ _ (fun i _ => KD _) Ho).
- exact (AF0x.rdword_ext _ _ _ _ (fun i _ => KD _) HFL).
Qed.

Lemma dn_aok_move : forall (W2 : world segs) mem2 mem3 F buf b,
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  onann_a_ok W2 mem2 F buf b -> onann_a_ok W2 mem3 F buf b.
Proof.
intros W2 mem2 mem3 F buf b KD (A1 & A2 & A3 & A4 & A5).
refine (conj _ (conj _ (conj _ (conj _ _)))).
- eapply garr8_frame; [exact A1|]. intros a _. apply (YCbq.mbyte_of_aview segs). apply KD.
- eapply garr8_frame; [exact A2|]. intros a _. apply (YCbq.mbyte_of_aview segs). apply KD.
- exact (AF0x.rdword_ext _ _ _ _ (fun i _ => KD _) A3).
- exact (AF0x.rdword_ext _ _ _ _ (fun i _ => KD _) A4).
- intros i Hi. rewrite KD. exact (A5 i Hi).
Qed.

Lemma dn_slot_move : forall (W2 : world segs) mem2 mem3 sp1 o v,
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  onann_slot W2 mem2 sp1 o v -> onann_slot W2 mem3 sp1 o v.
Proof. intros W2 mem2 mem3 sp1 o v KD H. unfold onann_slot in *. exact (AF0x.rdword_ext _ _ _ _ (fun i _ => KD _) H). Qed.

Lemma onann_piece_dn_holds : @onann_dn_stmt fx rc B MT.
Proof.
unfold onann_dn_stmt. intros E0AT E1AT. unfold onann_dn_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HZC & HGU & HGNE & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof CALLEES as (HSMR & HLEAF & HPF & HBCMP & HMS & HN & HWKC & HMOC & HF5).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & Hdf & Htw0 & Hgf0 & Hm &
  HTF & Htfg & Hrom & Hap & Hri0 & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Htw1 & Hign & Haok & Hslots).
pose proof Hslots as (S56 & S0 & S32 & S40).
pose proof Haok as (HAV & HAN & HA24 & HA32 & HASH).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R20 & R21 & R22 & R24 & R25 & R27) & R13).
destruct (onann_cur_ar B MT LAWS HFIX (proj1 HCUR)) as (HARc & HAR2 & ELO & EHI & EFA & EFL & Hin & EF2 & HFb & HFsh &
  HFnG & _ & _ & _ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as HCV.
(* f: 8-aligned, in a side-stack frame (cf, pf) of the entry's frames *)
pose proof Hdf as (_ & _ & _ & _ & _ & _ & Hfp0 & Hfp8 & _ & _ & (cf & pf & Hinf & Hf1 & Hf2) & _ & Hfwin).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cf pf HARc Hinf) as (_ & Hfapp & _ & _).
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cf pf HARc Hinf) as (Hf4096 & Hfce & _).
unfold FRAME_F_SIZE in Hf2.
unfold ONANN_FBYTES in HFc, HFapp, HFLw.
assert (HSTKv : ONANN_STK = 8992) by reflexivity.
assert (HNSv : NOTICE_STK = 8240) by reflexivity.
assert (HEST : ESTACK = 4096) by reflexivity.
assert (HFR : ONANN_FRAME = 192) by reflexivity.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1, HFR.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
set (FL := flag_addr lyc ONANN_CID pos) in *.
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F FL HAR2 Hfrs Hbl HlyF EF
  eq_refl FFL) as (N1 & N2 & N3 & N4).
assert (HF8 : F / 8 = 8 * (F / 64)).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D at 1.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.div_mul. lia. }
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (DF8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)) as D; rewrite DFm8, Z.add_0_r in D; exact D).
assert (HSHF : SHADOW_OFF + F / 8 + 128 <= F \/ F + 1024 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
assert (HFG : F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 1024) ONANN_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (ONANN_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso. assert (Hx : exists x, F <= x < F + 1024 /\ ONANN_S <= x < ONANN_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F ONANN_S) as [h3|h3]; [exists ONANN_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2). apply (HFnG x Hx1). unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, ONANN_S in *; cbn [fst snd]; lia]. }
assert (HACE : alloc_ceiling <= sp1 - NOTICE_STK) by lia.
assert (Hsp46 : 2 ^ 46 <= sp1) by lia.
(* a G byte is none of the bytes the piece changes *)
assert (NZG : forall x, inG TG.G_HARNESS x -> ~ dn_Z F sp1 x).
{ intros x Hx Hz. pose proof (inG_low segs B transport_segs_low _ x HGX Hx) as Hl. unfold kLowMemEnd in Hl.
  destruct Hz as [Hz | [Hz | Hz]]; [unfold SHADOW_OFF in Hz; lia | exact (HFnG x ltac:(lia) Hx) | lia]. }
(* ---- the model ---- *)
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
destruct (dn_w1 Bw b HLB) as (HL1 & HG1 & HR1).
destruct (dn_split TF Bw b now Bw' Hign Hm) as (B2 & HCN & HK2).
set (W1 := onann_w1 timg_A Bw b) in *.
destruct (dn_cn TF W1 _ B2 HCN) as (HNT & HNM).
destruct (onann_dn_world TF W1 b B2 HCN) as (d & EB2).
destruct (dn_desk_ri W1 d HL1) as (HG2 & HR2).
assert (HGB2 : TW.g_fail_next B2 <= 1) by (rewrite EB2, HG2, HG1; exact Hgf0).
assert (HRB2 : onann_ri B2) by (rewrite EB2; exact (HR2 (HR1 Hri0))).
assert (Hb2 : onann_b2 TF Bw b B2) by (split; [exact HCN | exists d; exact EB2]).
pose proof (dn_cmd b Hign) as Hcmd. pose proof (dn_cmd_range b) as Rcmd.
(* ---- run 1, +0x308 .. +0x394: n's shadow, n's first 44 bytes, `jal __asan_memset` ---- *)
assert (Hpsl : forall a, sp1 + 8 <= a < sp1 + 56 -> apresent (w_H W2) mem2 a).
{ pose proof HJ1 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). intros a Ha. apply Hp. lia. }
pose proof (dn_entry B ly2 S2 W2 regs2 mem2 md2 W1 sp1 F HZC HAR2 Htw1 R9 R18 R19 R20 R21 R24 HF0 HF64 HFapp HFG
  Hsp46 (proj2 Hsp1) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))
  Hpsl S56) as HS.
set (E0 := dn_E regs2 W1) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, dn_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, dn_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E0 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E0 18) = F)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E0 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs DN_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ1 SHOK DN_B0.
{ dn_awr U9 U18 U19 EF2. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ dn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (dn_Z F sp1) HFr); [dn_win U9 U18 U19 | exact Ha | exact Hn]. }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (ZS1 : forall i, 42 <= i < 51 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U19.
  assert (Hi' : i = 42 \/ i = 43 \/ i = 44 \/ i = 45 \/ i = 46 \/ i = 47 \/ i = 48 \/ i = 49 \/ i = 50) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (sn_chunk0 E0 (w_H W2) (ms_mem ms) (Some 19%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
clear HF HFr HG RG0.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem ms) md1 ONANN_CID pos HAR1 Hin) as (_ & _ & _ & HFsh1).
rewrite EF2 in HFsh1. change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh1.
change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh1.
pmkst HS.
sn_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 380)) Q10 ltac:(cbn [sv_denot]; rewrite U18; reflexivity).
sn_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
sn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 28) Q12 ltac:(reflexivity).
sn_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
sn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 27560)) Q1 ltac:(apply codeptr_val; exact HEI).
sn_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
sn_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x394: __asan_memset (n + 44, 0, 28), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (HMS fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 md1
    (k + 0) (F + 380) 0 28 (sp1 - sp0) (Z_to_bv 64 (BASE + 27560)) HGX G_HARNESS_rw HJ1 Q10 Q11 Q12).
  - lia.
  - lia.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia.
  - rewrite QSP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
    destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0a & _) & _).
    destruct Hsp1 as (_ & M1). rewrite M1, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|]. intros a Ha. left. rewrite QSP. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists ONANN_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EF2. change (fs_frame_bytes ONANN_CID) with 1024. lia.
    + lia.
  - apply (amem_range_sub_app F 1024); [exact HFapp | lia | lia | lia | lia].
  - apply (TransportGNotice.frame_ra_zero _ F (F + 380) 28 47 51); [lia | exact DFm8 | lia | lia |].
    intros i Hi. exact (ZS1 i ltac:(lia)).
  - intros _. apply (TransportGNotice.frame_hull_vis _ F 1024 (F + 380) 28);
      [lia | exact HF64 | reflexivity | lia | lia | lia |].
    intros i Hi. apply can_aview_vis. exact (proj1 (HFsh1 i Hi)).
  - exact I. }
cbv beta. intros W2x c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ dn_Z F sp1 a ->
  aview segs (w_H W2) memM a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite HeffM; [exact (KR1 a Ha Hn) | exact Ha | |].
  - intros Hd. apply Hn. right. left. lia.
  - intros Hd. apply Hn. right. right. left. lia. }
assert (GAM : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memM a)
  by (intros a Ha; exact (HgrM a (GA1 a Ha))).
jafter_call_keep_hi HS 1024%nat regsM (mrestrict (w_H W2) memM) HPM [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 19%nat (SHADOW_OFF + F / 8)); [exact U19 | | exact HgrM].
    intros a Ha. unfold SHADOW_OFF in *. apply HeffM; [lia | destruct HSHF; lia | lia].
  - apply (region_kept_aview _ _ _ _ 18%nat F); [exact U18 | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply sn_rk_none; [| exact HgrM]. intros a Ha. unfold ONANN_S, TA_g_s in *.
    apply HeffM; [lia | destruct HFG; unfold ONANN_S, TA_g_s, TW.SZ_g_s in *; lia | lia].
  - apply sn_rk_none; [| exact HgrM]. intros a Ha. unfold DN_SH in *.
    apply HeffM; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
      destruct HFapp as (_ & [HL | (HH1 & HH2)]); lia | lia].
  - apply (region_kept_aview _ _ _ _ 9%nat sp1); [exact U9 | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply (region_kept_aview _ _ _ _ 9%nat sp1); [exact U9 | | exact HgrM].
    intros a Ha. apply HeffM; lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regsM) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U9b : bv_unsigned (ew E1 9) = sp1) by (rewrite E1lo by lia; exact U9).
assert (U18b : bv_unsigned (ew E1 18) = F) by (rewrite E1lo by lia; exact U18).
assert (U19b : bv_unsigned (ew E1 19) = SHADOW_OFF + F / 8) by (rewrite E1lo by lia; exact U19).
assert (SHOK1 : sh_ok segs DN_Bx (@nil shent) E1 (mrestrict (w_H W2) memM)) by constructor.
assert (ZMM : forall a, F + 380 <= a < F + 408 -> aview segs (w_H W2) memM a = Some 0).
{ intros a Ha. replace a with ((F + 380) + (a - (F + 380))) by lia. rewrite (HsetM (a - (F + 380)) ltac:(lia)).
  reflexivity. }
clear dependent ms.
(* ---- run 2, +0x398 .. +0x3d4: the checked loads of s + 96 and s + 104, up to `jalr a2` ---- *)
paj_run_tok RUN HS HJ2 SHOK1 DN_B0.
{ dn_awr U9b U18b U19b EF2. }
set (md3 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md3. clear mat.
set (memN := ms_mem ms) in *.
assert (KRN : forall a, 0 <= a < 2 ^ 64 -> ~ dn_Z F sp1 a ->
  aview segs (w_H W2) memN a = aview segs (w_H W2) memM a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (dn_Z F sp1) HFr); [dn_win U9b U18b U19b | exact Ha | exact Hn]. }
assert (ZMN : forall a, F + 380 <= a < F + 408 -> aview segs (w_H W2) memN a = Some 0).
{ intros a Ha. rewrite <- (ZMM a Ha).
  apply (kept_of_frame _ _ _ _ _ (fun x => (SHADOW_OFF + F / 8 + 42 <= x < SHADOW_OFF + F / 8 + 51) \/
    (F + 336 <= x < F + 380) \/ (sp1 + 8 <= x < sp1 + 32) \/ (sp1 + 48 <= x < sp1 + 56)) HFr);
    [| unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia |].
  - intros b0 wlo whi x Hiw Hx. cbv beta.
    sn_win Hiw Hx ltac:(rewrite ?U9b, ?U18b, ?U19b in Hx;
      first [lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; lia]).
  - cbv beta. unfold SHADOW_OFF in *.
    intros [Hx | [Hx | [Hx | Hx]]]; [destruct HSHF; lia | lia | lia | lia]. }
assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ dn_Z F sp1 a ->
  aview segs (w_H W2) memN a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; rewrite (KRN a Ha Hn); exact (KAM a Ha Hn)).
assert (GAN : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memN a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAM a Ha))).
clear HF HFr HG.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS1.
pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RS4.
pose proof (st_ok_pi_region_nth _ _ _ 5 _ HS eq_refl) as RS5.
cbn [ms_mem restrict] in RS0, RS1, RS4, RS5.
assert (ZSN : forall i, 42 <= i < 51 -> aview segs (w_H W2) memN (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U19b.
  assert (Hi' : i = 42 \/ i = 43 \/ i = 44 \/ i = 45 \/ i = 46 \/ i = 47 \/ i = 48 \/ i = 49 \/ i = 50) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (sn_chunk0 E1 (w_H W2) memN (Some 19%nat) _ _ _ _ _ _ RS0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
(* n's 44 bytes *)
assert (EX : forall j, (j < 3)%nat -> ew E1 (32 + j) = nth j (dn_vals W1) (Z_to_bv 64 0))
  by (intros j Hj; rewrite E1lo by lia; unfold E0, dn_E; rewrite Eimg_low by (unfold A_TEXT; lia);
      apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth dn_vals] in E32, E33, E34.
pose proof (TWL.u_at_range W1 (TW.OFF_g_s + 112) 4) as R34. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R34.
assert (DK : forall n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> YK11.getr regs2 r = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E1 (SOff n 0) = Z_to_bv 64 v).
{ intros n r v Hn Hr Hv. cbn [sv_denot]. rewrite E1lo by (pose proof (bv_unsigned_in_range 5 r) as Hb;
    change (bv_modulus 5) with 32 in Hb; lia).
  rewrite (EE n r Hn), Hr. unfold w64. rewrite unsigned_lit_small, Z.add_0_r by exact Hv. reflexivity. }
pose proof (dn_pv_range b) as Hpv. pose proof (dn_off_range W1 b) as Hoff. pose proof (dn_state_range W1) as Hst.
pose proof (sn_chunk_val E1 (w_H W2) memN _ _ _ _ _ _ 336 4 (SLit 1) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VN0.
pose proof (sn_chunk_val E1 (w_H W2) memN _ _ _ _ _ _ 340 4 (SExt true 32 (SOff 34 0)) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VN4.
pose proof (sn_chunk_val E1 (w_H W2) memN _ _ _ _ _ _ 344 8 (SLit 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VN8.
pose proof (sn_chunk_val E1 (w_H W2) memN _ _ _ _ _ _ 352 8 (SOff 22 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VN16.
pose proof (sn_chunk_val E1 (w_H W2) memN _ _ _ _ _ _ 360 8 (SOff 18 256) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VN24.
pose proof (sn_chunk_val E1 (w_H W2) memN _ _ _ _ _ _ 368 8 (SOff 25 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VN32.
pose proof (sn_chunk_val E1 (w_H W2) memN _ _ _ _ _ _ 376 4 (SOff 13 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VN40.
cbn [base_val] in VN0, VN4, VN8, VN16, VN24, VN32, VN40.
rewrite U18b in VN0, VN4, VN8, VN16, VN24, VN32, VN40.
change (N.to_nat 4) with 4%nat in VN0, VN4, VN40. change (N.to_nat 8) with 8%nat in VN8, VN16, VN24, VN32.
change (bv_unsigned (sv_denot E1 (SLit 1)) mod 2 ^ (8 * Z.of_N 4)) with 1 in VN0.
change (bv_unsigned (sv_denot E1 (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in VN8.
rewrite (dn_sext32 E1 34 _ E34 R34), <- dn_state_eq in VN4.
rewrite (DK 22%nat 22%bv fp eq_refl R22 ltac:(lia)) in VN16.
assert (D18 : sv_denot E1 (SOff 18 256) = Z_to_bv 64 (F + 256))
  by (cbn [sv_denot]; rewrite U18b; reflexivity).
rewrite D18 in VN24.
rewrite (DK 25%nat 25%bv (onann_pv timg_A b) eq_refl R25 ltac:(lia)) in VN32.
assert (D13 : sv_denot E1 (SOff 13 0) = Z_to_bv 64 (onann_off W1 b)).
{ cbn [sv_denot]. rewrite E1lo by lia. rewrite (EE 13%nat 13%bv eq_refl), R13. unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
rewrite D13 in VN40.
apply (sn_vm_w _ _ 4 (TW.S_state W1) ltac:(lia)) in VN4. apply (sn_vm_w _ _ 8 fp ltac:(lia)) in VN16.
apply (sn_vm_w _ _ 8 (F + 256) ltac:(lia)) in VN24. apply (sn_vm_w _ _ 8 (onann_pv timg_A b) ltac:(lia)) in VN32.
apply (sn_vm_w _ _ 4 (onann_off W1 b) ltac:(lia)) in VN40.
change (N.to_nat 4) with 4%nat in VN4, VN40. change (N.to_nat 8) with 8%nat in VN16, VN24, VN32.
pose proof (dn_nb (w_H W2) memN (F + 336) (TW.S_state W1) fp (F + 256) (onann_pv timg_A b) (onann_off W1 b)
  ltac:(replace (F + 336) with (F + 336) by lia; exact VN0)
  ltac:(replace (F + 336 + 4) with (F + 340) by lia; exact VN4)
  ltac:(replace (F + 336 + 8) with (F + 344) by lia; exact VN8)
  ltac:(replace (F + 336 + 16) with (F + 352) by lia; exact VN16)
  ltac:(replace (F + 336 + 24) with (F + 360) by lia; exact VN24)
  ltac:(replace (F + 336 + 32) with (F + 368) by lia; exact VN32)
  ltac:(replace (F + 336 + 40) with (F + 376) by lia; exact VN40)
  ltac:(intros a Ha; exact (ZMN a ltac:(lia)))) as HNBg.
destruct (dn_NB_fields (TW.S_state W1) fp (F + 256) (onann_pv timg_A b) (onann_off W1 b) Hst ltac:(lia)
  ltac:(lia) ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F24).
(* the slots at memN *)
assert (SN8 : rdword (aview segs (w_H W2) memN) (sp1 + 8) = Some DN_SH) by dn_slot RS4 U9b DN_SH.
assert (SN16 : rdword (aview segs (w_H W2) memN) (sp1 + 16) = Some (DN_SH + 1)) by dn_slot RS4 U9b (DN_SH + 1).
assert (SN24 : rdword (aview segs (w_H W2) memN) (sp1 + 24) = Some (ONANN_S + 96)) by dn_slot RS4 U9b (ONANN_S + 96).
assert (SN48 : rdword (aview segs (w_H W2) memN) (sp1 + 48) = Some (ONANN_S + 112)) by dn_slot RS5 U9b (ONANN_S + 112).
clear RS0 RS1 RS4 RS5.
(* what the call kept, from its entry to the call of notice *)
assert (KCN : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 memN (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2 memN
    (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F FL (onann_wr Bw b) (dn_Z F sp1) HGX HARc HAR2 Hfrs Hbl HlyF EF
    eq_refl FFL); [lia | lia | | exact HK | exact KAN | exact GAN].
  intros a Hz. destruct Hz as [Hz | [Hz | [Hz | [Hz | Hz]]]].
  - right; left. right; left. change (fs_frame_bytes ONANN_CID / 8) with 128. lia.
  - right; left. left. change (fs_frame_bytes ONANN_CID) with 1024. lia.
  - left. lia.
  - left. lia.
  - left. lia. }
assert (TWN : tw_at TMAP_A (aview segs (w_H W2) memN) W1).
{ apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact Htw1|].
  intros x (o & bx & n & Hin3 & Hx).
  assert (HxG : inG TG.G_HARNESS x).
  { unfold inG. apply Exists_exists. exists (bx, n). split; [exact (TMAP_A_in_G o bx n Hin3) | unfold in_zr; cbn [fst snd]; lia]. }
  apply KAN; [pose proof (inG_low segs B transport_segs_low _ x HGX HxG); unfold kLowMemEnd in *; lia|].
  exact (NZG x HxG). }
assert (KNa : forall a, F + 256 <= a < F + 296 -> aview segs (w_H W2) memN a = aview segs (w_H W2) mem2 a)
  by (intros a Ha; apply KAN; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia |
      unfold dn_Z, SHADOW_OFF in *; destruct HSHF; lia]).
assert (HVN : garr8 segs (mrestrict (w_H W2) memN) (F + ONANN_A)
  (map DSpec.bz (TSS.ann_field (skipn 15 (DSpec.fr_body b))))).
{ eapply garr8_frame; [exact HAV|]. intros a Ha. rewrite length_map in Ha.
  pose proof (dn_ann_len (skipn 15 (DSpec.fr_body b))). apply (YCbq.mbyte_of_aview segs). apply KNa.
  unfold ONANN_A in Ha. lia. }
assert (HNN : garr8 segs (mrestrict (w_H W2) memN) (F + ONANN_A + 10)
  (map DSpec.bz (TSS.ann_field (skipn 24 (DSpec.fr_body b))))).
{ eapply garr8_frame; [exact HAN|]. intros a Ha. rewrite length_map in Ha.
  pose proof (dn_ann_len (skipn 24 (DSpec.fr_body b))). apply (YCbq.mbyte_of_aview segs). apply KNa.
  unfold ONANN_A in Ha. lia. }
assert (ZSaN : forall i, 32 <= i < 37 -> aview segs (w_H W2) memN (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite KAN; [exact (HASH i Hi) | unfold SHADOW_OFF; lia |].
  unfold dn_Z, SHADOW_OFF in *. destruct HSHF; lia. }
(* the registers at `jalr a2` *)
assert (E32' : ew E1 32 = Z_to_bv 64 (TI.ti_notice timg_A)) by (rewrite E32, <- dn_notify_eq, HNT; reflexivity).
sn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (TI.ti_notice timg_A)) T12
  ltac:(cbn [sv_denot]; rewrite E32', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sn_reg HS (Z_to_bv 5 11) (w64 (F + 336)) T11 ltac:(cbn [sv_denot]; rewrite U18b; reflexivity).
dn_kreg HS E1lo EE (Z_to_bv 5 2) 2%nat R2 T2. dn_kreg HS E1lo EE (Z_to_bv 5 8) 8%nat R8 T8.
dn_kreg HS E1lo EE (Z_to_bv 5 9) 9%nat R9 T9. dn_kreg HS E1lo EE (Z_to_bv 5 18) 18%nat R18 T18.
dn_kreg HS E1lo EE (Z_to_bv 5 19) 19%nat R19 T19. dn_kreg HS E1lo EE (Z_to_bv 5 22) 22%nat R22 T22.
dn_kreg HS E1lo EE (Z_to_bv 5 27) 27%nat R27 T27.
sn_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) T3
  ltac:(cbn [sv_denot]; rewrite (E1lo 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
sn_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) T4
  ltac:(cbn [sv_denot]; rewrite (E1lo 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
sn_reg HS (Z_to_bv 5 20) (w64 ONANN_S) T20 ltac:(reflexivity).
sn_reg HS (Z_to_bv 5 23) (w64 (onann_off W1 b)) T23 ltac:(exact D13).
sn_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) T24 ltac:(reflexivity).
sn_reg HS (Z_to_bv 5 25) (w64 (ONANN_S + 104)) T25 ltac:(reflexivity).
sn_reg HS (Z_to_bv 5 26) (w64 (SHADOW_OFF + (ONANN_S + 112) / 8)) T26 ltac:(reflexivity).
(* +0x3d4: `jalr a2`, a2 = notice *)
assert (P4 : 0 <= TI.ti_notice timg_A < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
assert (P5 : TI.ti_notice timg_A mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
eapply (SRr_jalr_call_pi (PL := PL_transport) (PI := PI_transport) W2 E1 _ _ _ _ 0x600e7 (1%bv : bv 5) (12%bv : bv 5)
  (TI.ti_notice timg_A) HEI1 HS eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T12 | exact P4 | exact P5 |].
intros matC ms1 Ems1 _. subst ms1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_A) regsC memN mdC) Qx) end.
assert (EBN : BASE + (27620 + 4) = 0x87e4c) by (vm_compute; reflexivity).
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (27620 + 4)))
  by (unfold regsC; rewrite YK11.getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc;
      discriminate Hc); reflexivity).
assert (RCK : forall r : bv 5, bv_unsigned r <> 1 -> YK11.getr regsC r = YK11.getr (ms_regs ms) r)
  by (intros r Hr; unfold regsC; apply YK11.getr_other; intros Ex; apply Hr; rewrite Ex; reflexivity).
assert (RC2 : YK11.getr regsC 2%bv = w64 sp1) by (rewrite RCK by (vm_compute; discriminate); exact T2).
assert (RC3 : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite RCK by (vm_compute; discriminate); exact T3).
assert (RC4 : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite RCK by (vm_compute; discriminate); exact T4).
assert (RC11 : YK11.getr regsC 11%bv = w64 (F + 336)) by (rewrite RCK by (vm_compute; discriminate); exact T11).
assert (USPC : spZ regsC = sp1) by (unfold spZ; rewrite RC2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARN.
eapply SRr_bind.
{ exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 memN mdC (k + 0) regsC
    (F + 336) (onann_dntc timg_A W1 b) TF W1 B2
    ltac:(apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ2)
    ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia)
    RC3 RC4 RC11
    ltac:(rewrite USPC; destruct Hsp1 as (_ & M1); pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1;
          rewrite M1, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
          apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    (dn_ntc_at B ly2 S2 W2 memN md3 regsC W1 b F pos fp LAWS HARN Hin EF2 HF0 HF64 HFc HFapp
       ltac:(rewrite USPC; lia) ZSaN ZSN HNBg HVN HNN)
    (onann_tf_call B LAWS HROU HRNE lyc Sc W memc mdc ly2 S2 W2 memN md3 pos regs regsC NOTICE_STK TF Bw b HARc HARN
       Hfrs Hperm EFA ELO EHI KCN Htfg ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HTF)
    (onann_rom_call B HROU HRNE lyc Sc W memc W2 memN (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) Hrom KCN)
    TWN HNM
    (dn_apart B ly2 S2 W2 mem2 md2 W2 memN TF Bw b F pos _ LAWS HAR2 Hin EF2 Hap HNBg (dn_NB_len _ _ _ _ _) F24)
    ltac:(intros HD; exfalso; unfold onann_dntc in HD; cbn [TI.n_kind] in HD;
          unfold TS0.DIGINET_N_DESK, TC.N_DATA in HD; discriminate HD)
    ltac:(assert (ONANN_EV = 0) by reflexivity; assert (NOTICE_EV = 0) by reflexivity; lia)). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3).
assert (He30 : e3 = 0) by (unfold NOTICE_EV in He3; lia). subst e3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _ & _ & _ & ELO3 & EHI3 & _).
clear HJi3 memS3.
pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). rewrite !Z.add_0_r in HJi0.
pose proof HJi0 as (_ & Hlyle0 & _). pose proof Hlyle0 as (_ & _ & _ & _ & _ & ELF0 & _ & _ & _ & ELO0 & EHI0 & _).
clear HJi0 memS0.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF0; reflexivity).
assert (EFA3 : forall c p, frame_addr ly3 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite ELF3c; reflexivity).
assert (Hfrs3 : frames S3 = (ONANN_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hperm3c : Permutation (ablocks B ly3 S3) (ablocks B lyc Sc)) by exact (Permutation_trans Hperm3 Hperm).
assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm3c) Hbm)).
(* what the call kept, from its entry to notice's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 memN W3 mem3
    (spZ regs - ONANN_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (onann_wr Bw b)
    (notice_wr W1 (onann_dntc timg_A W1 b)) (dkg_nf ONANN_CID F FL)).
  - lia.
  - lia.
  - exact EFA.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - exact Hbl.
  - exact N1.
  - exact N3.
  - exact KCN.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. exact (onann_wr_dntc _ _ Bw b a Ha). }
(* the bytes of the own frame and of the stack above sp1 at notice's return *)
assert (KF3 : forall a, (F <= a < F + 1024 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 128) -> ~ dn_Z F sp1 a ->
  aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hz. pose proof HK3 as (_ & _ & _ & K34 & _).
  rewrite (K34 ONANN_CID pos a Hin).
  - apply KAN; [unfold SHADOW_OFF in *; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia | exact Hz].
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF2. change (shadow_addr F) with (SHADOW_OFF + F / 8).
    change (fs_frame_bytes ONANN_CID / 8) with 128. change (fs_frame_bytes ONANN_CID) with 1024.
    destruct Ha as [Ha | Ha]; [left | right]; lia.
  - intros Hw. pose proof (onann_ntc_wr_G _ _ a Hw) as HG3.
    pose proof (inG_low segs B transport_segs_low _ a HGX HG3) as Hl. unfold kLowMemEnd in Hl.
    destruct Ha as [Ha | Ha]; [exact (HFnG a Ha HG3) | unfold SHADOW_OFF in Ha; lia]. }
assert (KS3 : forall a, sp1 <= a < spZ regs -> ~ dn_Z F sp1 a ->
  aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hz. pose proof HK3 as (K31 & _). rewrite USPC in K31. rewrite K31 by lia. apply KAN; [lia | exact Hz]. }
assert (KN3 : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) memN a).
{ intros a Ha. pose proof HK3 as (K31 & _). rewrite USPC in K31. apply K31; lia. }
(* f's bytes at notice's return (on_announce_seg_kitf.v onann_f30): the byte at f + 30 is the cmd, its shadow byte 0
   (f is 8-aligned, so the granule of f + 30 holds f + 31, whose shadow test allows only 0) *)
destruct (onann_f30 B LAWS lyc Sc W memc mdc W3 mem3 (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) regs ONANN_STK
  fp buf b fj HARc KC3 (onann_wr_G Bw b) Hdf) as (_ & (_ & HRA3 & _) & Hf30 & _).
assert (Hfsh : aview segs (w_H W3) mem3 (SHADOW_OFF + (fp + 30) / 8) = Some 0).
{ destruct (HRA3 (fp + 31) ltac:(lia)) as (s & Hs & Hok).
  assert (ESA : shadow_of_addr SHADOW_OFF (fp + 31) = SHADOW_OFF + (fp + 30) / 8).
  { unfold shadow_of_addr. f_equal. pose proof (Z.div_mod fp 8 ltac:(lia)) as D. rewrite Hfp8, Z.add_0_r in D.
    rewrite D. replace (8 * (fp / 8) + 31) with (fp / 8 * 8 + 31) by ring.
    replace (8 * (fp / 8) + 30) with (fp / 8 * 8 + 30) by ring. rewrite !Z.div_add_l by lia. reflexivity. }
  rewrite ESA in Hs.
  destruct Hok as [-> | (Hlt & Hlt2)]; [exact Hs|]. exfalso.
  assert (M : (fp + 31) mod 8 = 7) by (rewrite Z.add_mod, Hfp8 by lia; reflexivity). lia. }
(* ---- the facts both cuts carry, at notice's return ---- *)
assert (HSo : forall o, In o ONANN_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold ONANN_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
assert (NZS : forall a, sp1 + 32 <= a < sp1 + 48 \/ sp1 <= a < sp1 + 8 \/ sp1 + 56 <= a < spZ regs -> ~ dn_Z F sp1 a).
{ intros a Ha. unfold dn_Z, SHADOW_OFF in *. lia. }
assert (NZF : forall a, F + 256 <= a < F + 336 \/ F + 408 <= a < F + 1024 \/
    SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 42 \/ SHADOW_OFF + F / 8 + 51 <= a < SHADOW_OFF + F / 8 + 128 ->
    ~ dn_Z F sp1 a).
{ intros a Ha. unfold dn_Z, SHADOW_OFF in *. destruct HSHF; lia. }
assert (HSV3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem3) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ rewrite Forall_forall in Hsaved |- *. intros o Ho. pose proof (HSo o Ho) as Hob.
  refine (AF0x.rdword_ext _ _ _ _ _ (Hsaved o Ho)). intros i Hi. apply KS3; [lia | apply NZS; lia]. }
assert (HFL3 : rdword (aview segs (w_H W3) mem3) (F + 1024 - 8) = Some FL).
{ refine (AF0x.rdword_ext _ _ _ _ _ HFLw). intros i Hi. apply KF3; [lia | apply NZF; lia]. }
assert (CUR3 : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mem3 md4 0).
{ refine (conj _ (conj _ (conj Hfrs3 (conj Hperm3c (conj ELF3c (conj _ (conj KC3 (conj HSV3 _)))))))).
  - replace (k + 0) with (k + 0 + 0) by lia. exact HJ3.
  - assert (ONANN_EV = 0) by reflexivity. lia.
  - exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3).
  - unfold ONANN_FBYTES. exact HFL3. }
assert (SL3 : forall o v, (o = 0 \/ o = 32 \/ o = 40 \/ o = 56) -> onann_slot W2 mem2 sp1 o v ->
  onann_slot W3 mem3 sp1 o v).
{ intros o v Ho Hs. unfold onann_slot in *.
  refine (AF0x.rdword_ext _ _ _ _ _ Hs). intros i Hi. apply KS3; [lia | apply NZS; lia]. }
assert (SN3 : forall o v, 8 <= o <= 48 -> rdword (aview segs (w_H W2) memN) (sp1 + o) = Some v ->
  onann_slot W3 mem3 sp1 o v).
{ intros o v Ho Hs. unfold onann_slot. refine (AF0x.rdword_ext _ _ _ _ _ Hs). intros i Hi. apply KN3. lia. }
assert (HAOK3 : onann_a_ok W3 mem3 F buf b).
{ refine (conj _ (conj _ (conj _ (conj _ _)))).
  - eapply garr8_frame; [exact HAV|]. intros a Ha. rewrite length_map in Ha.
    pose proof (dn_ann_len (skipn 15 (DSpec.fr_body b))). apply (YCbq.mbyte_of_aview segs).
    unfold ONANN_A in Ha. apply KF3; [lia | apply NZF; lia].
  - eapply garr8_frame; [exact HAN|]. intros a Ha. rewrite length_map in Ha.
    pose proof (dn_ann_len (skipn 24 (DSpec.fr_body b))). apply (YCbq.mbyte_of_aview segs).
    unfold ONANN_A in Ha. apply KF3; [lia | apply NZF; lia].
  - refine (AF0x.rdword_ext _ _ _ _ _ HA24). intros i Hi. unfold ONANN_A. apply KF3; [lia | apply NZF; lia].
  - refine (AF0x.rdword_ext _ _ _ _ _ HA32). intros i Hi. unfold ONANN_A. apply KF3; [lia | apply NZF; lia].
  - intros i Hi. rewrite KF3; [exact (HASH i Hi) | lia | apply NZF; lia]. }
assert (S32_3 : rdword (aview segs (w_H W3) mem3) (sp1 + 32) = Some (SHADOW_OFF + (fp + 30) / 8))
  by exact (SL3 32 _ ltac:(lia) S32).
(* ---- run 3, +0x3d8 .. +0x3f0: the checked load of f + 30, a1 = cmd, up to `bne a1, a2` ---- *)
assert (X3 : forall n v, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) <> 1 ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 n) = v -> YK11.getr regs3 (Z_to_bv 5 n) = v)
  by (intros n v Hn H1 Hv; rewrite (HP3 n Hn), (RCK _ H1); exact Hv).
pose proof (X3 2 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T2) as R3_2.
pose proof (X3 3 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T3) as R3_3.
pose proof (X3 4 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T4) as R3_4.
pose proof (X3 8 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T8) as R3_8.
pose proof (X3 9 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T9) as R3_9.
pose proof (X3 18 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T18) as R3_18.
pose proof (X3 19 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T19) as R3_19.
pose proof (X3 20 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T20) as R3_20.
pose proof (X3 22 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T22) as R3_22.
pose proof (X3 23 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T23) as R3_23.
pose proof (X3 24 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T24) as R3_24.
pose proof (X3 25 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T25) as R3_25.
pose proof (X3 26 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T26) as R3_26.
pose proof (X3 27 _ ltac:(hnf; lia) ltac:(vm_compute; discriminate) T27) as R3_27.
clear X3.
assert (Hfpapp : in_app fp 64)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, FRAME_F_SIZE in *; lia).
rewrite RC1. change (Z_to_bv 64 (BASE + (27620 + 4))) with (Z_to_bv 64 (BASE + DN_RET)).
pose proof (dn_entry3 W3 regs3 mem3 sp1 fp (DSpec.fr_cmd b) R3_9 R3_27 R3_20 Hsp46 ltac:(lia)
  ltac:(unfold FRAME_F_SIZE in *; lia) ltac:(unfold FRAME_F_SIZE in *; lia) Hfpapp Rcmd S32_3 Hfsh Hf30) as HS3.
set (E3 := dn_E3 regs3 fp (DSpec.fr_cmd b)) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3, dn_E3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs3 r)
  by (intros n r Hn; unfold E3, dn_E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E3c : ew E3 33 = Z_to_bv 64 (DSpec.fr_cmd b))
  by (unfold E3, dn_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (SHOK3 : sh_ok segs DN_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
clear HS. rename ms into ms2.
paj_run_tok RUN HS3 HJ3 SHOK3 DN_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  repeat (apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
set (m5 := ms_mem ms) in *.
assert (KD3 : forall a, aview segs (w_H W3) m5 a = aview segs (w_H W3) mem3 a).
{ intros a. rewrite (aview_wrap64 tfibsegs _ m5 a), (aview_wrap64 tfibsegs _ mem3 a).
  pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
  apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
  intros b0 wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(lia). }
assert (GA3 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) m5 a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
pose proof (dn_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mem3 md4 m5 md5 0
  CUR3 ltac:(replace (k + 0) with (k + 0 + 0) by lia; exact HJ3) KD3 GA3) as CUR5.
pmkst HS3.
sn_reg HS3 (Z_to_bv 5 11) (Z_to_bv 64 (DSpec.fr_cmd b)) X11 ltac:(exact (dn_zext8 E3 33 _ E3c Rcmd)).
sn_reg HS3 (Z_to_bv 5 12) (Z_to_bv 64 224) X12 ltac:(reflexivity).
sn_reg HS3 (Z_to_bv 5 10) (w64 (ONANN_S + 136)) X10 ltac:(reflexivity).
sn_reg HS3 (Z_to_bv 5 20) (w64 ONANN_S) X20 ltac:(reflexivity).
dn_kreg0 HS3 EE3 (Z_to_bv 5 2) 2%nat R3_2 X2. dn_kreg0 HS3 EE3 (Z_to_bv 5 3) 3%nat R3_3 X3.
dn_kreg0 HS3 EE3 (Z_to_bv 5 4) 4%nat R3_4 X4. dn_kreg0 HS3 EE3 (Z_to_bv 5 8) 8%nat R3_8 X8.
dn_kreg0 HS3 EE3 (Z_to_bv 5 9) 9%nat R3_9 X9. dn_kreg0 HS3 EE3 (Z_to_bv 5 18) 18%nat R3_18 X18.
dn_kreg0 HS3 EE3 (Z_to_bv 5 19) 19%nat R3_19 X19. dn_kreg0 HS3 EE3 (Z_to_bv 5 22) 22%nat R3_22 X22.
dn_kreg0 HS3 EE3 (Z_to_bv 5 23) 23%nat R3_23 X23. dn_kreg0 HS3 EE3 (Z_to_bv 5 24) 24%nat R3_24 X24.
dn_kreg0 HS3 EE3 (Z_to_bv 5 25) 25%nat R3_25 X25. dn_kreg0 HS3 EE3 (Z_to_bv 5 26) 26%nat R3_26 X26.
(* ---- +0x3f0: `bne a1, a2`, from a state with no region ---- *)
clear HS3 SHOK3.
pose proof (dn_entryb W3 (ms_regs ms) m5) as HS.
set (Eb := Eimg (PI := PI_transport) (Ereg (ms_regs ms) [])) in HS.
assert (SHOK : sh_ok segs DN_Bx (@nil shent) Eb (mrestrict (w_H W3) m5)) by constructor.
assert (HEIb : img_env VAL A_LIM Eb) by (unfold Eb; apply Eimg_env).
assert (EEb : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Eb n = YK11.getr (ms_regs ms) r)
  by (intros n r Hn; unfold Eb; apply ew_Eimg_Ereg_nat; exact Hn).
assert (D11 : sv_denot Eb (SOff 11 0) = Z_to_bv 64 (DSpec.fr_cmd b))
  by (cbn [sv_denot]; rewrite (EEb 11%nat (Z_to_bv 5 11) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X11).
assert (D12 : sv_denot Eb (SOff 12 0) = Z_to_bv 64 224)
  by (cbn [sv_denot]; rewrite (EEb 12%nat (Z_to_bv 5 12) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X12).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + DN_BR)) mm rom) mdx) Q) end.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
assert (TW5 : tw_at TMAP_A (aview segs (w_H W3) m5) B2)
  by (apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw3 | intros x _; exact (KD3 x)]).
assert (HAOK5 : onann_a_ok W3 m5 F buf b) by exact (dn_aok_move W3 mem3 m5 F buf b KD3 HAOK3).
assert (SA5 : onann_slots_arm W3 m5 sp1).
{ refine (conj _ (conj _ (conj _ _))); apply (dn_slot_move W3 mem3 m5 sp1 _ _ KD3); apply SN3;
    first [lia | exact SN8 | exact SN16 | exact SN24 | exact SN48]. }
assert (S40_5 : onann_slot W3 m5 sp1 40 F)
  by (apply (dn_slot_move W3 mem3 m5 sp1 _ _ KD3); exact (SL3 40 F ltac:(lia) S40)).
psrr_branch_tok RUN BR HS SHOK DN_B0.
- (* taken: cmd <> 0xe0 (so 0xe1), to the e1 cut +0x548 *)
  cbn [branch_taken] in Hc. rewrite D11, D12, (dn_eqb_byte _ 224 Rcmd ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hc1 : DSpec.fr_cmd b = 225) by (destruct Hcmd as [Hx | Hx]; [exfalso; apply Hc; exact Hx | exact Hx]).
  assert (HK1 : onann_k_e1 timg_A TF B2 (onann_off W1 b) b = Some (Bw', tt)) by (rewrite Hc1 in HK2; exact HK2).
  paj_run_to_tok RUNTO HS HJ3 SHOK DN_B0 ONANN_E1.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_nil. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end.
  assert (KDF : forall a, aview segs (w_H W3) (ms_mem msF) a = aview segs (w_H W3) m5 a).
  { intros a. rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m5 a).
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b0 wlo whi x Hiw. vm_compute in Hiw. destruct Hiw. }
  assert (GAF : forall a, apresent (w_H W3) m5 a -> apresent (w_H W3) (ms_mem msF) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  dn_kreg0 HS EEb (Z_to_bv 5 2) 2%nat X2 Y2. dn_kreg0 HS EEb (Z_to_bv 5 3) 3%nat X3 Y3.
  dn_kreg0 HS EEb (Z_to_bv 5 4) 4%nat X4 Y4. dn_kreg0 HS EEb (Z_to_bv 5 8) 8%nat X8 Y8.
  dn_kreg0 HS EEb (Z_to_bv 5 9) 9%nat X9 Y9. dn_kreg0 HS EEb (Z_to_bv 5 18) 18%nat X18 Y18.
  dn_kreg0 HS EEb (Z_to_bv 5 19) 19%nat X19 Y19. dn_kreg0 HS EEb (Z_to_bv 5 20) 20%nat X20 Y20.
  dn_kreg0 HS EEb (Z_to_bv 5 22) 22%nat X22 Y22. dn_kreg0 HS EEb (Z_to_bv 5 23) 23%nat X23 Y23.
  dn_kreg0 HS EEb (Z_to_bv 5 24) 24%nat X24 Y24. dn_kreg0 HS EEb (Z_to_bv 5 25) 25%nat X25 Y25.
  dn_kreg0 HS EEb (Z_to_bv 5 26) 26%nat X26 Y26. dn_kreg0 HS EEb (Z_to_bv 5 10) 10%nat X10 Y10.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_E1)) mm rom) mdx) Q) end.
  apply (E1AT LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1
    F B2 ly3 S3 W3 (ms_mem msF) _ (ms_regs msF) HFIX).
  + unfold onann_e1_cur.
    refine (conj (dn_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 m5 md5
      (ms_mem msF) _ 0 CUR5 ltac:(replace (k + 0) with (k + 0 + 0) by lia; exact HJ3) KDF GAF)
      (conj _ (conj Hb2 (conj Hc1 (conj HK1 (conj HGB2 (conj _ (conj _ (conj _ _))))))))).
    * apply (tw_kept TMAP_A (aview segs (w_H W3) m5)); [exact TW5 | intros x _; exact (KDF x)].
    * exact (dn_aok_move W3 m5 (ms_mem msF) F buf b KDF HAOK5).
    * destruct SA5 as (A8 & A16 & A24 & A48).
      refine (conj _ (conj _ (conj _ _))); apply (dn_slot_move W3 m5 (ms_mem msF) sp1 _ _ KDF); assumption.
    * exact (dn_slot_move W3 m5 (ms_mem msF) sp1 _ _ KDF S40_5).
    * apply (dn_slot_move W3 m5 (ms_mem msF) sp1 _ _ KDF). apply (dn_slot_move W3 mem3 m5 sp1 _ _ KD3).
      exact (SL3 56 _ ltac:(lia) S56).
  + unfold onann_regs_e1, onann_regs_e0, onann_regs_arm, onann_regs_base.
    refine (conj (conj (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 Y19))))))
      (conj Y20 (conj Y24 (conj Y25 Y26)))) Y10) (conj Y22 Y23)).
    * exact (eq_trans Y3 (eq_sym Hgp)).
    * exact (eq_trans Y4 (eq_sym Htp)).
- (* not taken: cmd = 0xe0, to the e0 cut +0x3f4 *)
  cbn [branch_taken] in Hc. rewrite D11, D12, (dn_eqb_byte _ 224 Rcmd ltac:(lia)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Heq.
  assert (HK0 : onann_k_e0 timg_A TF B2 now = Some (Bw', tt)) by (rewrite Heq in HK2; exact HK2).
  paj_run_to_tok RUNTO HS HJ3 SHOK DN_B0 ONANN_E0.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_nil. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end.
  assert (KDF : forall a, aview segs (w_H W3) (ms_mem msF) a = aview segs (w_H W3) m5 a).
  { intros a. rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m5 a).
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros b0 wlo whi x Hiw. vm_compute in Hiw. destruct Hiw. }
  assert (GAF : forall a, apresent (w_H W3) m5 a -> apresent (w_H W3) (ms_mem msF) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  dn_kreg0 HS EEb (Z_to_bv 5 2) 2%nat X2 Y2. dn_kreg0 HS EEb (Z_to_bv 5 3) 3%nat X3 Y3.
  dn_kreg0 HS EEb (Z_to_bv 5 4) 4%nat X4 Y4. dn_kreg0 HS EEb (Z_to_bv 5 8) 8%nat X8 Y8.
  dn_kreg0 HS EEb (Z_to_bv 5 9) 9%nat X9 Y9. dn_kreg0 HS EEb (Z_to_bv 5 18) 18%nat X18 Y18.
  dn_kreg0 HS EEb (Z_to_bv 5 19) 19%nat X19 Y19. dn_kreg0 HS EEb (Z_to_bv 5 20) 20%nat X20 Y20.
  dn_kreg0 HS EEb (Z_to_bv 5 24) 24%nat X24 Y24. dn_kreg0 HS EEb (Z_to_bv 5 25) 25%nat X25 Y25.
  dn_kreg0 HS EEb (Z_to_bv 5 26) 26%nat X26 Y26. dn_kreg0 HS EEb (Z_to_bv 5 10) 10%nat X10 Y10.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_E0)) mm rom) mdx) Q) end.
  apply (E0AT LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1
    F B2 ly3 S3 W3 (ms_mem msF) _ (ms_regs msF) HFIX).
  + unfold onann_e0_cur.
    refine (conj (dn_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 m5 md5
      (ms_mem msF) _ 0 CUR5 ltac:(replace (k + 0) with (k + 0 + 0) by lia; exact HJ3) KDF GAF)
      (conj _ (conj Hb2 (conj Heq (conj HK0 (conj HGB2 (conj HRB2 (conj _ (conj _ _))))))))).
    * apply (tw_kept TMAP_A (aview segs (w_H W3) m5)); [exact TW5 | intros x _; exact (KDF x)].
    * destruct SA5 as (A8 & A16 & A24 & A48).
      refine (conj _ (conj _ (conj _ _))); apply (dn_slot_move W3 m5 (ms_mem msF) sp1 _ _ KDF); assumption.
    * apply (dn_slot_move W3 m5 (ms_mem msF) sp1 _ _ KDF). apply (dn_slot_move W3 mem3 m5 sp1 _ _ KD3).
      exact (SL3 0 _ ltac:(lia) S0).
    * exact (dn_slot_move W3 m5 (ms_mem msF) sp1 _ _ KDF S40_5).
  + unfold onann_regs_e0, onann_regs_arm, onann_regs_base.
    refine (conj (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 Y19))))))
      (conj Y20 (conj Y24 (conj Y25 Y26)))) Y10).
    * exact (eq_trans Y3 (eq_sym Hgp)).
    * exact (eq_trans Y4 (eq_sym Htp)).
Qed.
End dn.

Theorem onann_piece_dn : forall fx rc B MT, @onann_dn_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@onann_piece_dn_holds fx rc B MT). Qed.
