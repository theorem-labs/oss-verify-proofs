(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 297 of its 377 lines of code are new or changed and 950 lines of the source are left out. *)
(* m_rx_seg_host: the HOST segment of the image-B walk of m_rx (statement lib/B/Prog/m_rx_cg.v, kit
   lib/B/Prog/m_rx_seg_kit.v): cmd e1 with body_len >= 33, the call of host_offset.

   mrx_seg_host: from the cut HOST (MRX_PC OFF_HOST, R_HOST) the run reaches the cut ANNT (MRX_PC OFF_ANNT, R_ANNT),
   so the continuation of ANNT gives the continuation of HOST.
   - +0x144 `ld a0, 0x30(sp)` (f.body of the struct spec_read_frame filled at sp1 - 112: fa + 30, the kit's
     mrx_sf_body and mrx_sf_ptr) and +0x148 `jal host_offset` (return address +0x14c): one run of the PA engine from a
     state with one read-only region (the 8 bytes of f.body, atom 32 = fa + 30), so the run keeps the memory.
   - host_offset: a donor-form callee lifted to the walk's G journal by TransportGCg.v gx_call_cg (gx_ok, gx_noerrno),
     at host_offset_cg.v transport_host_offset_cg: p = fa + 30, body = the frame's bytes from 30 on (TCb.v m_rx_m's
     body, sf_body = 30 at SPEC_OK), garr8 of them and trans_src_ok of [p, + length body) (sub-ranges of the frame's,
     mrx_frs), decode_off_win at HOFF_STK below sp1 - 112 (mrx_static's off-window, MRX_STK = 112 + HOFF_STK), the
     read-only view, host_offset_m at the cut's world (mr_ann at cmd e1: UMR.mr_ho_off gives the world unchanged and
     -1 <= off < 10). Its post: a0 = off, every byte of G kept (gx_kept: the world relation, TWorldB.v tw_kept_GB), the
     saved slots and the struct kept (above its stack window, acall_kept_g), the frame's bytes, placement and the
     read-only view at the state after the call (DgnTransportBCg.v trans_src_ok_acall_g_ge0, the image clause for
     TRANS_RO_RD), the callee-saved registers (s1 = &M, sp, gp, tp, s3 .. s11) and the frames, blocks and meter
     composed with the cut's (kit mrx_next).
   - +0x14c `mv s0, a0` and +0x150 `j 0x1c4`: a run from a state with no region to +0x314 = ANNT, s0 = off; the model
     there is UMR.mr_ann2 off at the same world. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg m_wake_cg m_maybe_online_cg m_tick_cg spec_read_frame_cg host_offset_cg desk_named_cg check_state_data_cg
  m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRunB TransportGFrameB CanKit
  YC1g YC1h m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require m_rx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module UMR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.m_rx.
Module AK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_kit.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- the symbolic states ---- *)

(* +0x144: f.body (8 bytes at sp + 48, read-only), atom 32. *)
Definition host_rg : YP09.region :=
  YP09.mkRegion (Some 2%nat) 48 56 0 0 [YP09.mkChunk 48 (YP09.CVal 8 (SOff 32 0))].
Definition host_ss1 : sstate := mkSS (AF_m_rx + OFF_HOST) sr_atoms [host_rg] None (mkFacts [] [] []).
(* +0x14c (the return address of host_offset, AF_m_rx + 0x14c = 15048): no region. *)
Definition HOST_RET : Z := 15048.
Definition host_ss2 : sstate := mkSS HOST_RET sr_atoms [] None (mkFacts [] [] []).
(* +0x314 = ANNT, the run's stop. *)
Definition HOST_ANNT : Z := 15504.

(* ---- small lemmas ---- *)

(* A run whose regions have no write window keeps every byte. *)
Lemma host_ro_frame : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun rg => YP09.r_whi rg <=? YP09.r_wlo rg) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' H Hro x. apply H. intros (rg & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) Hro rg Hr) as Hw. cbv beta in Hw. apply Z.leb_le in Hw. lia.
Qed.

Lemma host_aview_ext : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a Hm. apply aview_eq_of. unfold mrestrict. rewrite Hm. reflexivity. Qed.

(* garr8 of a suffix, at image B's segments (lib/A/Prog/m_rx_seg_annt.v annt_garr8_skipn is stated at image A's
   tfibsegs, lib/A/AB1v.v, another segment list). *)
Lemma host_garr8_skipn : forall mem base (l : list Z) k, (k <= length l)%nat ->
  garr8 tfibsegs mem base l -> garr8 tfibsegs mem (base + Z.of_nat k) (skipn k l).
Proof.
intros mem base l k Hk HG. rewrite <- (firstn_skipn k l) in HG. apply (garr8_app tfibsegs) in HG as [_ HG].
rewrite length_firstn in HG. replace (Nat.min k (length l)) with k in HG by lia. exact HG.
Qed.

(* ---- tactics ---- *)

(* The value of register q in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac host_reg HS q v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) q) in
      assert (H : YK11.getr (ms_regs msx) q = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx q HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) q) in
      assert (H : YK11.getr (ms_regs msx) q = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx q HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "host_reg: no match for" T; fail
  end.

(* A register the run keeps: its value is the cut's (EE reads the valuation's atoms). *)
Ltac host_keep HS EE regsx nn zn H :=
  host_reg HS (Z_to_bv 5 zn) (YK11.getr regsx (Z_to_bv 5 zn)) H
    ltac:(cbn [sv_denot]; rewrite (EE nn (Z_to_bv 5 zn) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).

(* The write rights of a run whose regions are all read-only. *)
Ltac host_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HMRX : trans_mrx_cells B.
Hypothesis HRO : trans_ro_rd_unowned B.
Hypothesis HNE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS_B.
Hypothesis HGNE : gx_noerrno B TG.G_HARNESS_B.
Hypothesis HSRF : forall fx' : YK11.FPState, @transport_spec_read_frame_cg fx' rc B MT (transportb_sigma TB_spec_read_frame).
Hypothesis HBCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc tfibsegs B (transportb_sigma TB___interceptor_trampoline_bcmp).
Hypothesis HMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (transportb_sigma TB___asan_memcpy).
Hypothesis HHOFF : forall fx' : YK11.FPState, @transport_host_offset_cg fx' rc B MT (transportb_sigma TB_host_offset).
Hypothesis HMSET : forall fx' : YK11.FPState, @transport_m_set_cg fx' rc B MT (transportb_sigma TB_m_set).
Hypothesis HDN : forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transportb_sigma TB_desk_named).
Hypothesis HMW : forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transportb_sigma TB_m_wake).
Hypothesis HMO : forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transportb_sigma TB_m_maybe_online).
Hypothesis HMT : forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transportb_sigma TB_m_tick).
Variable sp1 : Z.
Variable regs0 : bvmap 5 word.
Variable lyc : alayout.
Variable Sc : astate.
Variable W : world tfibsegs.
Variable memc : word -> option byte.
Variable mdc : Model.
Variable fr : TI.tframe.
Variable n : Z.
Variable Bw' : list byte.
Variable r : Z.
Hypothesis HST : mrx_static B sp1 regs0 lyc Sc W memc mdc fr n.
Local Notation K := (@mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).

Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The walk's inner journal at a state: the layout's frame base and machine stack as at its start (YG0f.v layout_le);
   AR there is W_journalG.v ajournal_gx_AR. *)
Lemma host_ly : forall stk lyc0 Sc0 (W0 : world segs) mem0 md0 ly2 S2 (W2 : world segs) mem2 md2 k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] stk sp1 [] lyc0 Sc0 W0 mem0 md0 [] ly2 S2 W2
    mem2 md2 k ->
  ly_F ly2 = ly_F lyc0 /\ ly_stk_lo ly2 = ly_stk_lo lyc0 /\ ly_stk_hi ly2 = ly_stk_hi lyc0.
Proof.
intros stk lyc0 Sc0 W0 mem0 md0 ly2 S2 W2 mem2 md2 k HJ.
destruct HJ as (_ & _ & (memS & HJi & _) & _).
destruct HJi as (_ & Hl & _). destruct Hl as (_ & _ & _ & _ & _ & EF & _ & _ & _ & ELo & EHi & _).
split; [exact EF|]. split; [exact ELo | exact EHi].
Qed.

(* The registers s3 .. s11 kept from regsA to regsB keep mrx_hi. *)
Lemma host_hi_step : forall (regsA regsB : bvmap 5 word),
  mrx_hi regs0 regsA ->
  (forall q, 19 <= q <= 27 -> YK11.getr regsB (Z_to_bv 5 q) = YK11.getr regsA (Z_to_bv 5 q)) ->
  mrx_hi regs0 regsB.
Proof. intros regsA regsB HA HK q Hq. rewrite (HK q Hq). exact (HA q Hq). Qed.

Lemma host_pc_host : MRX_PC OFF_HOST = BASE + (AF_m_rx + OFF_HOST).
Proof. exact (mrx_pcv OFF_HOST). Qed.

Lemma mrx_seg_host : K (MRX_PC OFF_ANNT) (R_ANNT B fr n sp1 Bw' r) -> K (MRX_PC OFF_HOST) (R_HOST B fr n sp1 Bw' r).
Proof using All.
intros KA. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hhi & Hsaved & Htw &
  HR).
destruct HR as (Hcur & Hcmd & Hblen & H9 & B3 & Hann & Htk & Hr1).
pose proof HST as (Hspz0 & Hsp16 & Hceil & H46 & H47 & Hra0 & Hra40 & Hgp0 & Htp0 & H100 & H110 & Hfa0 & Hfan & Hfam &
  Hsrc0 & Hoffw & Hapart & Hnev & HAR0).
destruct Hcur as (Hok & Hfrs & Hsf).
pose proof Hok as (Hn & _).
destruct (mrx_ok_fields fr n Hok) as (Fdst & Fsrc & Fbody & F30 & Fbl0 & Fbl & Fcmd & Fretry & Fsend & Fack).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FR : MRX_FRAME = 112) by reflexivity.
assert (EM : MRX_STK = 8384) by reflexivity.
assert (EH : HOFF_STK = 8272) by reflexivity.
assert (BSV : BASE = 0x84c1c - 0x397c) by exact mrx_bval.
unfold AK.mlen in *.
(* ---- the model: mr_ann at cmd e1, body_len >= 33 is host_offset, then mr_ann2 off at the same world ---- *)
set (body := skipn 30 (TI.tf_bytes fr)).
assert (LBD : Z.of_nat (length body) = Z.of_nat (length (TI.tf_bytes fr)) - 30)
  by (unfold body; rewrite length_skipn; lia).
assert (HM : exists off, TC.host_offset_m Bwc body = Some (Bwc, off) /\ -1 <= off < 10 /\
  UMR.mr_ann2 timg_B fr n off Bwc = Some (B3, tt)).
{ unfold UMR.mr_ann in Hann. cbv zeta in Hann.
  lazymatch type of Hann with
  | (if ?c1 then _ else _) = _ => replace c1 with false in Hann by (symmetry; apply Z.ltb_ge; exact Hblen)
  end.
  cbv beta iota in Hann.
  lazymatch type of Hann with
  | context [if ?c2 then _ else _] => replace c2 with true in Hann by (symmetry; apply Z.eqb_eq; exact Hcmd)
  end.
  cbv beta iota in Hann.
  lazymatch type of Hann with
  | context [TC.host_offset_m Bwc ?bd] =>
      replace bd with body in Hann by (unfold body; rewrite Fbody; reflexivity)
  end.
  destruct (TC.host_offset_m Bwc body) as [[Bh off]|] eqn:Hho; [|discriminate Hann].
  destruct (UMR.mr_ho_off _ _ _ _ Hho) as [EBh Hoff]. subst Bh.
  exists off. split; [reflexivity|]. split; [exact Hoff | exact Hann]. }
destruct HM as (off & Hho & Hoff & Hann2). clear Hann.
(* ---- run 1, +0x144 .. +0x148: a0 = f.body (fa + 30), `jal host_offset` ---- *)
assert (USP : spZ regs2 = sp1 - 112).
{ change (spZ regs2) with (bv_unsigned (YK11.getr regs2 2)). rewrite Hsp. apply unsigned_lit_small. lia. }
pose proof (mrx_sf_body (mrestrict (w_H Wc) mem2) (sp1 - MRX_FRAME) (TI.tf_addr fr) (mrx_f fr n) Hsf) as V48.
rewrite Fbody, (mrx_sf_ptr fr n 30 Hok), FR in V48.
set (E1 := Eimg (PI := PI_transportb) (Ereg regs2 [w64 (TI.tf_addr fr + 30)])).
assert (HEI : img_env VAL A_LIM E1) by (unfold E1; apply Eimg_env).
assert (EE1 : forall n0 (rr : bv 5), Z.of_nat n0 = bv_unsigned rr -> ew E1 n0 = YK11.getr regs2 rr)
  by (intros n0 rr Hn0; unfold E1; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (X32 : ew E1 32 = Z_to_bv 64 (TI.tf_addr fr + 30))
  by (unfold E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0%nat)).
assert (U2 : bv_unsigned (ew E1 2) = sp1 - 112) by (rewrite (EE1 2%nat (Z_to_bv 5 2) eq_refl); exact USP).
assert (HS : st_ok_pi segs VAL E1 host_ss1
  (restrict (w_H Wc) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + OFF_HOST))) mem2 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold host_ss1.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - unfold E1. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold host_rg, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs _ _ (sp1 - 112) 48 8 (SOff 32 0) (TI.tf_addr fr + 30));
      [cbn [sv_denot]; rewrite X32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V48].
  - exact (conj I I).
  - exact (conj I (conj I I)). }
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E1 (mrestrict (w_H Wc) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUNTO.
rewrite host_pc_host.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ host_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in *; clearbody md1 end.
lazymatch type of HS with context [restrict _ ?mz] => rename mz into ms1 end.
pose proof (host_ro_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm1.
clear HF HFr HG.
assert (KV1 : forall a, aview segs (w_H Wc) (ms_mem ms1) a = aview segs (w_H Wc) mem2 a)
  by (intros a; apply host_aview_ext; exact Hm1).
host_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + HOST_RET)) R1 ltac:(apply codeptr_val; exact HEI).
host_reg HS (Z_to_bv 5 10) (w64 (TI.tf_addr fr + 30)) R10
  ltac:(cbn [sv_denot]; rewrite X32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
host_keep HS EE1 regs2 2%nat 2 K2. host_keep HS EE1 regs2 3%nat 3 K3. host_keep HS EE1 regs2 4%nat 4 K4.
host_keep HS EE1 regs2 9%nat 9 K9.
host_keep HS EE1 regs2 19%nat 19 K19. host_keep HS EE1 regs2 20%nat 20 K20. host_keep HS EE1 regs2 21%nat 21 K21.
host_keep HS EE1 regs2 22%nat 22 K22. host_keep HS EE1 regs2 23%nat 23 K23. host_keep HS EE1 regs2 24%nat 24 K24.
host_keep HS EE1 regs2 25%nat 25 K25. host_keep HS EE1 regs2 26%nat 26 K26. host_keep HS EE1 regs2 27%nat 27 K27.
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_host_offset) rg mm mdx) Qx) end.
(* the facts host_offset's contract takes at the call *)
assert (R2 : YK11.getr (ms_regs ms1) 2 = Z_to_bv 64 (sp1 - MRX_FRAME)) by exact (eq_trans K2 Hsp).
assert (R3' : YK11.getr (ms_regs ms1) 3 = YK11.getr regs0 3) by exact (eq_trans K3 Hgp).
assert (R4' : YK11.getr (ms_regs ms1) 4 = YK11.getr regs0 4) by exact (eq_trans K4 Htp).
assert (R3 : YK11.getr (ms_regs ms1) 3 = w64 (as_gp B)) by exact (eq_trans R3' Hgp0).
assert (R4 : YK11.getr (ms_regs ms1) 4 = w64 (as_tp B)) by exact (eq_trans R4' Htp0).
assert (Hhi1 : mrx_hi regs0 (ms_regs ms1)).
{ apply (host_hi_step regs2 (ms_regs ms1) Hhi). intros q Hq.
  assert (Eq : q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
  destruct Eq as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    first [exact K19 | exact K20 | exact K21 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26 | exact K27]. }
destruct (mrx_pre sp1 (ms_regs ms1) HOST_RET Hsp16 Hceil H47 ltac:(unfold HOST_RET; lia) ltac:(reflexivity) R1 R2)
  as (HRO1 & HRA4 & HSP1 & HM16 & HLO & HHI).
destruct Hfrs as (Hg8 & Hsrc2 & Hrom2).
assert (Hg81 : garr8 segs (mrestrict (w_H Wc) (ms_mem ms1)) (TI.tf_addr fr) (map DSpec.bz (TI.tf_bytes fr))).
{ apply (garr8_frame segs _ _ _ _ Hg8). intros a _. apply (mbyte_of_aview segs). exact (KV1 a). }
assert (Hsrc1 : trans_src_ok B ly2 S2 Wc (ms_mem ms1) (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))))
  by (apply (trans_src_ok_view B ly2 S2 Wc Wc mem2 (ms_mem ms1) _ _ Hsrc2); intros a _; exact (KV1 a)).
assert (Hrom1 : trans_rom_view_rd Wc (ms_mem ms1)) by (intros a Ha; rewrite (KV1 a); exact (Hrom2 a Ha)).
assert (Hsf1 : mrx_sf Wc (ms_mem ms1) sp1 fr n)
  by (apply (mrx_sf_kept Wc Wc mem2 (ms_mem ms1) sp1 fr n Hsf); intros a _; exact (KV1 a)).
assert (Hsaved1 : mrx_saved Wc (ms_mem ms1) sp1 regs0)
  by (apply (mrx_saved_kept Wc Wc mem2 (ms_mem ms1) sp1 regs0 Hsaved); intros a _; exact (KV1 a)).
assert (Htw1 : tw_at TMAP_B (aview segs (w_H Wc) (ms_mem ms1)) Bwc)
  by (apply (tw_kept TMAP_B (aview segs (w_H Wc) mem2) _ Bwc Htw); intros x _; exact (KV1 x)).
assert (Hg8b : garr8 segs (mrestrict (w_H Wc) (ms_mem ms1)) (TI.tf_addr fr + 30) (map DSpec.bz body)).
{ unfold body. rewrite <- skipn_map.
  change (TI.tf_addr fr + 30) with (TI.tf_addr fr + Z.of_nat 30).
  apply host_garr8_skipn; [rewrite length_map; lia | exact Hg81]. }
assert (Hsrcb : trans_src_ok B ly2 S2 Wc (ms_mem ms1) (TI.tf_addr fr + 30) (Z.of_nat (length body)))
  by (apply (trans_src_ok_sub_ge0 B ly2 S2 Wc (ms_mem ms1) (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))));
      [exact Hsrc1 | lia | lia | lia]).
assert (Hwin : decode_off_win (ms_regs ms1) HOFF_STK (TI.tf_addr fr + 30) (Z.of_nat (length body)))
  by (unfold decode_off_win; rewrite HSP1, LBD; destruct Hoffw as [Hw | Hw]; [left | right]; lia).
(* +0x148: host_offset (fa + 30), a donor-form callee through gx_call_cg *)
eapply SRr_bind.
{ apply (@gx_call_cg fx rc tfib_sink_head segs B MT TG.G_HARNESS_B MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc
    (ms_mem ms1) md1 0 _ (ms_regs ms1) HOFF_STK HOFF_EV 0 (fun _ => False)
    (fun regs3 _ _ => YK11.getr regs3 10 = w64 off /\ Bwc = Bwc) HGX HGNE HJ).
  intros memS HJS.
  eapply SRr_mono.
  { exact (HHOFF fx MRX_STK sp1 [] lyc Sc W memS mdc [] ly2 S2 Wc (ms_mem ms1) md1 0 (ms_regs ms1)
      (TI.tf_addr fr + 30) off body Bwc Bwc HJS HRO1 HRA4 R3 R4 R10 HM16 HLO HHI ltac:(lia) Hg8b Hsrcb Hwin Hrom1
      Hho ltac:(unfold HOFF_EV; lia)). }
  intros W2 c2 _ HP. apply decode_cg_post_dcg. exact HP. }
intros W3 c3 _ HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e & -> & He & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & HMO3 &
  [[Q10 _] HGK]).
assert (e = 0) by (unfold HOFF_EV in He; lia). subst e. rewrite Z.add_0_r in HJ3.
rewrite R1.
(* what the call kept: the saved slots and the struct (above its window), G (the world relation), the frame *)
pose proof HK3 as (K31 & _ & K33 & _).
assert (KS3 : forall a, sp1 - 32 <= a < sp1 -> aview segs (w_H W3) mem3 a = aview segs (w_H Wc) (ms_mem ms1) a)
  by (intros a Ha; apply K31; [lia | rewrite HSP1; lia]).
destruct (mrx_next B MT MTL sp1 regs0 lyc Sc Wc W3 (ms_mem ms1) mem3 (ms_regs ms1) regs3 S2 S3 ly2 ly3 HOFF_STK
  ltac:(lia) ltac:(lia) HSP1 Hsaved1 KS3 HP3 R2 R3' R4' Hhi1 Hfr Hfr3 Hperm Hperm3 Hmo HMO3)
  as (Hsaved3 & Q2 & Q3 & Q4 & Qhi & F3 & P3 & M3).
destruct (host_ly _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (EF1 & ELo1 & EHi1).
destruct (host_ly _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (EF3 & ELo3 & EHi3).
assert (HAR1 : @AR rc segs B ly2 S2 Wc (ms_mem ms1) md1) by (eapply ajournal_gx_AR; exact HJ).
assert (HAR3 : @AR rc segs B ly3 S3 W3 mem3 md3) by (eapply ajournal_gx_AR; exact HJ3).
assert (Hfa3 : forall cid pos, frame_addr ly3 cid pos = frame_addr ly2 cid pos)
  by (intros cid pos; unfold frame_addr; rewrite EF3, EF1; reflexivity).
destruct (trans_src_ok_acall_g_ge0 B LAWS HRO HNE ly2 S2 Wc (ms_mem ms1) md1 ly3 S3 W3 mem3 md3
  (spZ (ms_regs ms1) - HOFF_STK) (spZ (ms_regs ms1)) (fun _ => False) (TI.tf_addr fr)
  (Z.of_nat (length (TI.tf_bytes fr))) HAR1 HAR3 Hperm3 Hfr3 Hfa3
  (eq_trans ELo3 (eq_sym ELo1)) (eq_trans EHi3 (eq_sym EHi1)) HK3 HGK
  (fun a _ Hx => Hx) (fun a _ Hx => Hx)
  ltac:(rewrite HSP1; destruct Hoffw as [Hw | Hw]; [left | right]; lia)
  Hsrc1 ltac:(lia)) as (Hsrc3 & KF3).
assert (Hg83 : garr8 segs (mrestrict (w_H W3) mem3) (TI.tf_addr fr) (map DSpec.bz (TI.tf_bytes fr))).
{ apply (garr8_frame segs _ _ _ _ Hg81). intros a Ha. apply (mbyte_of_aview segs). apply KF3.
  rewrite length_map in Ha. exact Ha. }
assert (Hrom3 : trans_rom_view_rd W3 mem3).
{ intros a Ha. refine (eq_trans _ (Hrom1 a Ha)).
  destruct (trans_ro_rd_scoped B HRO HNE a Ha) as [Ho Hne].
  apply (K33 a (trans_ro_img a Ha)); [| exact Ho | exact Hne].
  intros Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_B_LO in Gh. lia. }
assert (Hsf3 : mrx_sf W3 mem3 sp1 fr n).
{ apply (mrx_sf_kept Wc W3 (ms_mem ms1) mem3 sp1 fr n Hsf1). intros a Ha. apply K31; [lia | rewrite HSP1; lia]. }
assert (Htw3 : tw_at TMAP_B (aview segs (w_H W3) mem3) Bwc)
  by exact (tw_kept_GB _ _ _ Htw1 (gx_kept_rows segs TG.G_HARNESS_B Wc (ms_mem ms1) W3 mem3 HGK)).
(* run 2, +0x14c .. +0x150: s0 = a0 (off), `j` to ANNT *)
set (E3 := Eimg (PI := PI_transportb) (Ereg regs3 [])).
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n0 (rr : bv 5), Z.of_nat n0 = bv_unsigned rr -> ew E3 n0 = YK11.getr regs3 rr)
  by (intros n0 rr Hn0; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HS3 : st_ok_pi segs VAL E3 host_ss2
  (restrict (w_H W3) (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + HOST_RET)) mem3 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold host_ss2.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - unfold E3. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - exact (conj I (conj I I)). }
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof HJ3 as HJ4.
paj_run_to_tok RUNTO HS3 HJ4 SHOK3 YC4b.Bspan HOST_ANNT.
{ host_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md4 := mdx) in *; clearbody md4 end.
lazymatch type of HS3 with context [restrict _ ?mz] => rename mz into ms4 end.
pose proof (host_ro_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm4.
clear HF HFr HG.
assert (KV4 : forall a, aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a)
  by (intros a; apply host_aview_ext; exact Hm4).
host_keep HS3 EE3 regs3 2%nat 2 T2. host_keep HS3 EE3 regs3 3%nat 3 T3. host_keep HS3 EE3 regs3 4%nat 4 T4.
host_keep HS3 EE3 regs3 9%nat 9 T9.
host_keep HS3 EE3 regs3 19%nat 19 T19. host_keep HS3 EE3 regs3 20%nat 20 T20. host_keep HS3 EE3 regs3 21%nat 21 T21.
host_keep HS3 EE3 regs3 22%nat 22 T22. host_keep HS3 EE3 regs3 23%nat 23 T23. host_keep HS3 EE3 regs3 24%nat 24 T24.
host_keep HS3 EE3 regs3 25%nat 25 T25. host_keep HS3 EE3 regs3 26%nat 26 T26. host_keep HS3 EE3 regs3 27%nat 27 T27.
host_reg HS3 (Z_to_bv 5 8) (w64 off) T8
  ltac:(cbn [sv_denot]; rewrite (EE3 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q10).
pmkst HS3.
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 ?pcx) _ _) _) _ =>
  replace pcx with (MRX_PC OFF_ANNT) by (vm_compute; reflexivity) end.
(* the cut ANNT *)
apply (KA W3 Bwc).
apply (@mrx_at_intro fx rc B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_ANNT) (R_ANNT B fr n sp1 Bw' r) W3 Bwc ly3 S3
  (ms_regs ms4) (ms_mem ms4) md4 HJ4 F3 P3 M3 (eq_trans T2 Q2) (eq_trans T3 Q3) (eq_trans T4 Q4)).
- apply (host_hi_step regs3 (ms_regs ms4) Qhi). intros q Hq.
  assert (Eq : q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
  destruct Eq as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    first [exact T19 | exact T20 | exact T21 | exact T22 | exact T23 | exact T24 | exact T25 | exact T26 | exact T27].
- apply (mrx_saved_kept W3 W3 mem3 (ms_mem ms4) sp1 regs0 Hsaved3). intros a _. exact (KV4 a).
- apply (tw_kept TMAP_B (aview segs (w_H W3) mem3) _ Bwc Htw3). intros x _. exact (KV4 x).
- exists off.
  split.
  { split; [exact Hok|]. split.
    - apply (mrx_frs_view B fr ly3 S3 W3 W3 mem3 (ms_mem ms4) (conj Hg83 (conj Hsrc3 Hrom3)));
        intros a _; exact (KV4 a).
    - apply (mrx_sf_kept W3 W3 mem3 (ms_mem ms4) sp1 fr n Hsf3). intros a _. exact (KV4 a). }
  split; [right; exact Hcmd|].
  split; [exact Hblen|].
  split; [exact Hoff|].
  split; [intros He0; rewrite Hcmd in He0; unfold TC.SPEC_CMD_E1, TC.SPEC_CMD_E0 in He0; lia|].
  split; [exact T8|].
  split; [exact (eq_trans T9 (eq_trans (HP3 9 ltac:(unfold acallee_saved; lia)) (eq_trans K9 H9)))|].
  exists B3. split; [exact Hann2|]. split; [exact Htk | exact Hr1].
Qed.

End seg.
