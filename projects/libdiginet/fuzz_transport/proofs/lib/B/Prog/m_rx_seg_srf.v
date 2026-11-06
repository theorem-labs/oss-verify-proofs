(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths, module names and numbers changed; 416 of its 500 lines of code are new or changed and 946 lines of the source are left out. *)
(* m_rx_seg_srf: the SRF segment of the image-B walk of m_rx (statement lib/B/Prog/m_rx_cg.v, kit
   lib/B/Prog/m_rx_seg_kit.v): from the cut SRF (+0x024, the `jal spec_read_frame`) to the cut MAC (+0x048) when the
   callee's code is SPEC_OK, and to the cut EPI (+0x030, a0 = 0) when it is not.

   The code:
     +0x024  `jal spec_read_frame` (a0 = fa, a1 = n, a2 = sp = sp1 - 112), return address +0x028;
     +0x028  `beqz a0, 0x20`: a0 = 0 goes to +0x048 (MAC); else
     +0x02c  `mv a0, zero`, +0x030 the epilogue (EPI).
   No instrumented check, no branch to the trap word and no error path is on this stretch; the two runs read and
   write no memory.

   The call applies spec_read_frame_cg.v transport_spec_read_frame_cg (the segment's premise HSRF) on the walk's own
   inner G journal, with b = fa, len = n, fp = sp1 - 112 and frame = TI.tf_bytes fr. Its premises: 0 < fa and the
   frame's bytes and placement (mrx_static, the cut's mrx_frs), 0 <= n <= mlen (the model's range, mrx_m_n), the
   frame apart from srf_wr fp and outside this call's stack window (the frame lies outside m_rx's window,
   mrx_static's disjunction), fp mod 8 = 0 (sp1 mod 16 = 0), the struct's write right (TransportGCg.v
   transport_twr_ok_g_intro: a byte of m_rx's own window), decode_rd_ok (the window's bytes are present by the
   journal; the machine stack's shadow is 0: DgnTransportBCg.v stack_zshadow_ra) and decode_off_win of the struct,
   and the struct outside G (the stack lies above G's hull).

   Its post (TransportGCg.v transport_cg_post_out with the out cell [(sp1 - 112, 80)]) gives the next cut: the
   callee's kept fact is folded into the walk's own by TransportGCg.v dk_kept_trans_out_g (the struct lies in m_rx's
   own window, where the walk's post keeps nothing), the four saved slots are kept (they lie above the struct and
   above the callee's window), the frame's bytes and placement by DgnTransportBCg.v trans_src_ok_acall_g_ge0, the
   read-only bytes by the kept fact's image clause, the world relation by the post's gx_kept (TWorldB.v tw_kept_GB),
   and the struct at sp1 - 112 is the post's X (srf_f (tf_bytes fr) n = mrx_f fr n). The branch: a0 is the code,
   which lies in [-4, 0] (UMR.mr_srf_code), so a0 = 0 exactly at SPEC_OK; there the model is mrxb_mac (mrxb_top),
   and at another code it is (Bwc, 0) (mrxb_err), which the walk's model premise makes (Bw', r). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg m_wake_cg m_maybe_online_cg m_tick_cg spec_read_frame_cg host_offset_cg desk_named_cg check_state_data_cg
  m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require m_rx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_kit m_rx_seg_mac SlostHead.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
TransportGRunB TransportGFrameB CanKit YC1g YC1h m_rx_seg_kit.
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
Module AMAC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_mac.
Module ASLH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.SlostHead.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The valuation, the fresh symbolic state, small facts                *)
(* ------------------------------------------------------------------ *)

(* A fresh state at a pc of the listing: the registers as atoms, no region, no fact (the segment's runs read and
   write no memory). *)
Definition srf_E {rc : YM05.RunCeil} (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac srf_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "srf_reg: no match for" T; fail
  end.

(* The write rights of a run from a state with no region. *)
Ltac srf_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.

(* Such a run wrote nothing: every byte's view is the one it started from. *)
Ltac srf_kept HFr :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr);
  [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; exfalso;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia |]);
    destruct Hin
  | exact Ha
  | let Hf := fresh "Hf" in intros Hf; destruct Hf ].

(* One out cell, read as a range. *)
Lemma srf_inG1 : forall b m a, inG [(b, m)] a -> b <= a < b + m.
Proof.
intros b m a H. unfold inG in H. apply Exists_exists in H as (q & Hq & Hz).
cbn [In] in Hq. destruct Hq as [Hq | Hq]; [subst q | destruct Hq].
unfold in_zr in Hz. cbn [fst snd] in Hz. exact Hz.
Qed.
Lemma srf_inG1' : forall b m a, b <= a < b + m -> inG [(b, m)] a.
Proof.
intros b m a H. unfold inG. apply Exists_exists. exists (b, m).
split; [left; reflexivity | unfold in_zr; cbn [fst snd]; exact H].
Qed.

(* spec_read_frame's code, as the register holds it: 0 exactly at SPEC_OK (-4 <= code <= 0). The two steps are
   image-free lemmas of image A's walks: lib/A/Prog/m_rx_seg_mac.v mac_eqb0 and lib/A/Prog/SlostHead.v slh_eqb0. *)
Lemma srf_code0 : forall z, -4 <= z <= 0 -> (w64 z = w64 0 <-> z = 0).
Proof.
intros z Hz. split; [|intros ->; reflexivity].
intros H. apply (proj2 (AMAC.mac_eqb0 (Z_to_bv 64 z))) in H.
rewrite (ASLH.slh_eqb0 z ltac:(lia)) in H. apply Z.eqb_eq. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

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
Local Abbreviation IPOST := (@mrx_ipost fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Local Abbreviation fa := (TI.tf_addr fr).

(* The three pcs of the segment: SRF +0x024, EPI +0x030, MAC +0x048, as listing offsets from BASE. *)
Lemma srf_pc_srf : BASE + 14752 = MRX_PC OFF_SRF.
Proof. rewrite (mrx_pcv OFF_SRF). f_equal; vm_compute; reflexivity. Qed.
Lemma srf_pc_epi : BASE + 14764 = MRX_PC OFF_EPI.
Proof. rewrite (mrx_pcv OFF_EPI). f_equal; vm_compute; reflexivity. Qed.
Lemma srf_pc_mac : BASE + 14788 = MRX_PC OFF_MAC.
Proof. rewrite (mrx_pcv OFF_MAC). f_equal; vm_compute; reflexivity. Qed.

(* The fresh state at the listing offset pc. *)
Lemma srf_entry : forall (Wx : world segs) regs mem pc,
  st_ok_pi segs VAL (srf_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros Wx regs mem pc. rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split.
Qed.

Lemma srf_img : forall regs, img_env VAL A_LIM (srf_E regs).
Proof. intros regs. unfold srf_E. apply Eimg_env. Qed.
Lemma srf_agree : forall regs, env_agree 32 (Ereg regs []) (srf_E regs).
Proof. intros regs. split; [intros m Hm; unfold srf_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma srf_ewr : forall regs (q : bv 5) m, Z.of_nat m = bv_unsigned q -> ew (srf_E regs) m = YK11.getr regs q.
Proof. intros regs q m Hm. unfold srf_E. apply ew_Eimg_Ereg_nat. exact Hm. Qed.
Lemma srf_sv_a0 : forall regs, sv_denot (srf_E regs) (SOff 10 0) = YK11.getr regs (Z_to_bv 5 10).
Proof.
intros regs. cbn [sv_denot]. rewrite (srf_ewr regs (Z_to_bv 5 10) 10%nat ltac:(vm_compute; reflexivity)).
rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(* The branch on a0 (beqz). *)
Lemma srf_br_eq : forall regs,
  branch_taken BC_EQ (sv_denot (srf_E regs) (SOff 10 0)) (sv_denot (srf_E regs) (SLit 0)) = true <->
  YK11.getr regs 10 = w64 0.
Proof. intros regs. cbn [branch_taken]. rewrite srf_sv_a0. cbn [sv_denot]. exact (AMAC.mac_eqb0 _). Qed.
Lemma srf_br_eq_f : forall regs,
  branch_taken BC_EQ (sv_denot (srf_E regs) (SOff 10 0)) (sv_denot (srf_E regs) (SLit 0)) = false ->
  YK11.getr regs 10 <> w64 0.
Proof. intros regs H E. apply (proj2 (srf_br_eq regs)) in E. rewrite E in H. discriminate H. Qed.

(* A byte of a garr8 array is visible. *)
Lemma srf_garr8_vis : forall (Hh : word -> bool) m base (l : list Z) a,
  garr8 segs (mrestrict Hh m) base l -> base <= a < base + Z.of_nat (length l) ->
  aview segs Hh m a <> None.
Proof.
intros Hh m base l a HG Ha.
assert (Hj : (Z.to_nat (a - base) < length l)%nat) by lia.
pose proof (garr8_mbyte segs (mrestrict Hh m) base l (Z.to_nat (a - base)) HG Hj) as Hm.
replace (base + Z.of_nat (Z.to_nat (a - base))) with a in Hm by lia.
unfold aview. rewrite Hm. discriminate.
Qed.

(* A garr8 array at a memory that keeps its bytes. *)
Lemma srf_garr8_kept : forall (H1 H2 : word -> bool) m1 m2 base (l : list Z),
  garr8 segs (mrestrict H1 m1) base l ->
  (forall a, base <= a < base + Z.of_nat (length l) -> aview segs H2 m2 a = aview segs H1 m1 a) ->
  garr8 segs (mrestrict H2 m2) base l.
Proof.
intros H1 H2 m1 m2 base l HG K1. apply (garr8_frame segs _ _ _ _ HG).
intros a Ha. apply (mbyte_of_aview segs). exact (K1 a Ha).
Qed.

(* The read-only bytes after a G-form callee: each lies in the image, outside G, outside the owned statics and
   errno, so acall_kept_g's image clause keeps it. *)
Lemma srf_rom_kept : forall ly2 S2 (W2 W3 : world segs) mem2 mem3 slo shi (E : Z -> Prop),
  acall_kept_g segs B TG.G_HARNESS_B ly2 S2 W2 mem2 W3 mem3 slo shi E ->
  trans_rom_view_rd W2 mem2 -> trans_rom_view_rd W3 mem3.
Proof.
intros ly2 S2 W2 W3 mem2 mem3 slo shi E (_ & _ & K3 & _) Hrom a Ha.
rewrite <- (Hrom a Ha). destruct (trans_ro_rd_scoped B HRO HNE a Ha) as [Ho He].
apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
unfold TG.G_HARNESS_B_LO in Gh. lia.
Qed.

(* What a state of the walk's journal says: its AR, its layout (the same side-stack base and machine stack as the
   call state's), the window's bytes present, and the window's placement. *)
Lemma srf_jfacts : forall (ly' : alayout) (S' : astate) (Wx : world segs) memx mdx kx,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc []
    ly' S' Wx memx mdx kx ->
  @AR rc segs B ly' S' Wx memx mdx /\
  (forall cid pos, frame_addr ly' cid pos = frame_addr lyc cid pos) /\
  ly_stk_lo ly' = ly_stk_lo lyc /\ ly_stk_hi ly' = ly_stk_hi lyc /\
  (forall a, sp1 - MRX_STK <= a < sp1 -> apresent (w_H Wx) memx a) /\
  alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc + MRX_STK <= sp1 /\ sp1 <= ly_stk_hi lyc /\
  ly_stk_hi lyc <= 2 ^ 47.
Proof.
intros ly' S' Wx memx mdx kx HJx.
pose proof HJx as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARx & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct HLE as (_ & _ & _ & _ & _ & HF & _ & _ & _ & Elo & Ehi & _).
destruct Hstk as (_ & _ & Hce & Hslo & Hshi & H47x & _).
split; [exact HARx|].
split; [intros cid pos; unfold frame_addr; rewrite HF; reflexivity|].
split; [exact Elo|]. split; [exact Ehi|]. split; [exact Hpres|].
split; [exact Hce|]. split; [exact Hslo|]. split; [exact Hshi | exact H47x].
Qed.

Lemma mrx_seg_srf : K (MRX_PC OFF_EPI) (R_EPI Bw' r) -> K (MRX_PC OFF_MAC) (R_MAC B fr n sp1 Bw' r) ->
  K (MRX_PC OFF_SRF) (R_SRF B fr n sp1 lyc Sc Bw' r).
Proof using All.
intros KE KM. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hcfg & HJ & Hfrm & Hperm & Hmo & Hsp2 & Hgp2 & Htp2 & HHI & HSV
  & HTW & HR).
destruct HR as (Ely & ES & HFRS & Qa0 & Qa1 & Qa2 & Qs2 & HM).
subst ly2. subst S2. subst c.
pose proof HST as (Hsp1 & Hsp16 & Hceil & H46 & H47 & Hrao & Hra4 & Hgp0 & Htp0 & Ha00 & Ha10 & Hfa0 & Hfan & Hfaml
  & Hsrc0 & Hdisj & Hapart & Hnev & HAR).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MRX_STK = 8384) by reflexivity.
assert (FF : MRX_FRAME = 112) by reflexivity.
assert (ESR : SRF_STK = 4144) by reflexivity.
assert (ESZ : SRF_SIZE = 80) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
pose proof (mrx_m_n timg_B fr Bwc n Bw' r HM) as Hn.
assert (Hnl : 0 <= n <= Z.of_nat (length (TI.tf_bytes fr))) by (unfold AK.mlen in Hn; lia).
assert (Hml : AK.mlen fr = Z.of_nat (length (TI.tf_bytes fr))) by reflexivity.
(* ---- run 1: the `jal spec_read_frame` at +0x024 ---- *)
rewrite <- srf_pc_srf.
pose proof (srf_entry Wc regs2 mem2 14752) as HS.
set (E0 := srf_E regs2) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply srf_img).
assert (EE : forall m (q : bv 5), Z.of_nat m = bv_unsigned q -> ew E0 m = YK11.getr regs2 q)
  by (intros m q Hm; unfold E0; apply srf_ewr; exact Hm).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H Wc) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
paj_run_tok RUN HS HJ SHOK (0, 0).
{ srf_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in *; clearbody md1 end.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem2 a)
  by (srf_kept HFr).
clear HF HFr HG.
pmkst HS.
(* the registers at the call *)
srf_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14756)) R1 ltac:(apply codeptr_val; exact HEI).
srf_reg HS (Z_to_bv 5 10) (w64 fa) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 10%nat (Z_to_bv 5 10) ltac:(vm_compute; reflexivity)), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Qa0).
srf_reg HS (Z_to_bv 5 11) (w64 n) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 11%nat (Z_to_bv 5 11) ltac:(vm_compute; reflexivity)), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Qa1).
srf_reg HS (Z_to_bv 5 12) (w64 (sp1 - MRX_FRAME)) Q12
  ltac:(cbn [sv_denot]; rewrite (EE 12%nat (Z_to_bv 5 12) ltac:(vm_compute; reflexivity)), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Qa2).
assert (HP0 : aregs_preserved regs2 (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok segs (w_H Wc) E0 _ ms regs2 [] HS);
      [apply srf_agree | vm_compute; reflexivity]).
assert (R2 : YK11.getr (ms_regs ms) 2 = Z_to_bv 64 (sp1 - MRX_FRAME))
  by (rewrite <- Hsp2; exact (HP0 2 ltac:(unfold acallee_saved; lia))).
assert (R3' : YK11.getr (ms_regs ms) 3 = YK11.getr regs0 3)
  by (rewrite <- Hgp2; exact (HP0 3 ltac:(unfold acallee_saved; lia))).
assert (R4' : YK11.getr (ms_regs ms) 4 = YK11.getr regs0 4)
  by (rewrite <- Htp2; exact (HP0 4 ltac:(unfold acallee_saved; lia))).
assert (R3 : YK11.getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite R3'; exact Hgp0).
assert (R4 : YK11.getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite R4'; exact Htp0).
assert (RHI1 : mrx_hi regs0 (ms_regs ms))
  by (intros q Hq; rewrite <- (HHI q Hq); exact (HP0 q ltac:(unfold acallee_saved; lia))).
assert (R18 : YK11.getr (ms_regs ms) 18 = w64 SHADOW_OFF)
  by (rewrite <- Qs2; exact (HP0 18 ltac:(unfold acallee_saved; lia))).
destruct (mrx_pre sp1 (ms_regs ms) 14756 Hsp16 Hceil H47 ltac:(lia) ltac:(reflexivity) R1 R2)
  as (HRO1 & HRA4 & HSP1 & HM16 & HLO & HHI2).
(* the state of the walk at the call *)
destruct (srf_jfacts lyc Sc Wc (ms_mem ms) md1 0 HJ) as (HARa & FAa & Loa & Hia & HPRa & Hgce & Hgslo & Hgshi & Hg47).
assert (HSV1 : mrx_saved Wc (ms_mem ms) sp1 regs0)
  by (apply (mrx_saved_kept Wc Wc mem2 (ms_mem ms) sp1 regs0 HSV); intros a Ha; apply KA1; lia).
assert (HTW1 : tw_at TMAP_B (aview segs (w_H Wc) (ms_mem ms)) Bwc).
{ apply (tw_kept TMAP_B (aview segs (w_H Wc) mem2) _ Bwc HTW).
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KA1. lia. }
assert (HFRS1 : mrx_frs B fr lyc Sc Wc (ms_mem ms)).
{ apply (mrx_frs_view B fr lyc Sc Wc Wc mem2 (ms_mem ms) HFRS).
  - intros a Ha. apply KA1. unfold AK.mlen in Ha. lia.
  - intros s Hs. apply KA1. lia.
  - intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Rb. apply KA1. lia. }
destruct HFRS1 as (HGA1 & HSRC1 & HROM1).
(* the facts spec_read_frame's contract asks of the struct at sp1 - 112 *)
assert (HFPAL : (sp1 - MRX_FRAME) mod 8 = 0).
{ rewrite FF. replace (sp1 - 112) with ((sp1 / 16 * 2 - 14) * 8)
    by (pose proof (Z.div_mod sp1 16 ltac:(lia)); lia).
  apply Z_mod_mult. }
assert (HTWR : transport_twr_ok_g segs B TG.G_HARNESS_B MRX_STK sp1 [] lyc Sc lyc Sc [] Wc (ms_mem ms)
                 (spZ (ms_regs ms)) (sp1 - MRX_FRAME) SRF_SIZE).
{ apply (transport_twr_ok_g_intro segs B LAWS TG.G_HARNESS_B MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc
    (ms_mem ms) md1 0 (spZ (ms_regs ms)) (sp1 - MRX_FRAME) SRF_SIZE HJ).
  intros a Ha. rewrite ESZ in Ha. left. split; [unfold awr_byte; left; lia | rewrite HSP1; lia]. }
assert (HRDOK : decode_rd_ok Wc (ms_mem ms) (sp1 - MRX_FRAME) SRF_SIZE).
{ split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. rewrite ESZ in Ha. apply aview_some_of_apresent. apply HPRa. lia.
  - destruct (stack_zshadow_ra B lyc Sc Wc (ms_mem ms) md1 (sp1 - MRX_FRAME) SRF_SIZE HARa
      ltac:(lia) ltac:(lia) ltac:(lia)) as [HRA _]. exact HRA.
  - destruct (stack_zshadow_ra B lyc Sc Wc (ms_mem ms) md1 (sp1 - MRX_FRAME) SRF_SIZE HARa
      ltac:(lia) ltac:(lia) ltac:(lia)) as [_ HHL]. exact HHL.
  - unfold amem_range. right. lia.
  - lia.
  - lia. }
assert (HAPART : forall x, fa <= x < fa + n -> ~ srf_wr (sp1 - MRX_FRAME) x)
  by (intros x Hx; unfold srf_wr; unfold AK.mlen in Hdisj; lia).
assert (HAPARTM : forall x, fa <= x < fa + AK.mlen fr -> ~ srf_wr (sp1 - MRX_FRAME) x)
  by (intros x Hx; unfold srf_wr; unfold AK.mlen in Hdisj, Hx; lia).
assert (HAPARTS : forall x, kLowMemEnd <= x < kHighShadowEnd -> ~ srf_wr (sp1 - MRX_FRAME) x)
  by (intros x Hx; unfold srf_wr; lia).
(* +0x024: the call of spec_read_frame, a G-form callee on the walk's own journal *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?mdx) ?mdy) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_spec_read_frame) rg mm mdy) Qx) end.
eapply SRr_bind.
{ apply (HSRF fx MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc (ms_mem ms) md1 0 (ms_regs ms) fa n
    (sp1 - MRX_FRAME) (TI.tf_bytes fr) HJ).
  - exact HRO1.
  - exact HRA4.
  - exact R3.
  - exact R4.
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - exact HM16.
  - rewrite HSP1. lia.
  - rewrite HSP1. lia.
  - exact Hfa0.
  - exact Hnl.
  - exact HGA1.
  - exact (trans_src_ok_sub_ge0 B lyc Sc Wc (ms_mem ms) fa (AK.mlen fr) fa n HSRC1 (Z.le_refl _) (proj1 Hn)
             ltac:(unfold AK.mlen in *; lia)).
  - unfold decode_off_win. rewrite HSP1. unfold AK.mlen in Hdisj. lia.
  - exact HAPART.
  - exact HFPAL.
  - exact HTWR.
  - exact HRDOK.
  - unfold decode_off_win. rewrite HSP1. rewrite ESZ. lia.
  - intros x Hx Hg. rewrite ESZ in Hx. pose proof (inG_G_HARNESS_hull x Hg) as Gh.
    unfold TG.G_HARNESS_B_HI in Gh. lia.
  - unfold SRF_EV. lia. }
cbv beta. intros W2 c2 _ HQ.
unfold transport_srf_post, transport_cg_post_out in HQ. cbv beta in HQ.
destruct HQ as (ly3 & S3 & regs3 & mem3 & md3 & e & Hc3 & He3 & HJ3 & HP3 & Hfrm3 & Hperm3 & HKc & Hmo3 & HA0 & HSB
  & HGK).
assert (He0 : e = 0) by (unfold SRF_EV in He3; lia). subst e.
rewrite Z.add_0_r in HJ3. rewrite R1 in Hc3. subst c2.
destruct (srf_jfacts ly3 S3 W2 mem3 md3 0 HJ3) as (HAR3 & FA3 & Lo3 & Hi3 & HPR3 & _).
(* the struct's bytes are present at the returned memory *)
assert (HPo : forall a, inG [(sp1 - MRX_FRAME, SRF_SIZE)] a -> apresent (w_H W2) mem3 a).
{ intros a Ha. pose proof (srf_inG1 _ _ _ Ha) as Hr. rewrite ESZ in Hr.
  apply (apresent_of_aview segs (w_H W2) mem3 a ltac:(lia)).
  - intros Him. pose proof (transportb_segs_low a Him). unfold kLowMemEnd in *. lia.
  - apply (srf_garr8_vis (w_H W2) mem3 (sp1 - MRX_FRAME) _ a HSB).
    unfold TW.zs. rewrite length_map.
    change (length (TCt.sf_bytes fa (srf_f (TI.tf_bytes fr) n))) with 80%nat. lia. }
(* the callee's kept fact, folded into the walk's own window *)
assert (RK : acall_kept_g segs B TG.G_HARNESS_B lyc Sc Wc (ms_mem ms) W2 mem3 (sp1 - MRX_STK) sp1
               (srf_wr (sp1 - MRX_FRAME))).
{ apply (dk_kept_trans_out_g segs B LAWS transportb_segs_low TG.G_HARNESS_B [(sp1 - MRX_FRAME, SRF_SIZE)]
    lyc Sc Wc (ms_mem ms) md1 Wc (ms_mem ms) W2 mem3 (sp1 - MRX_STK) sp1
    (spZ (ms_regs ms) - SRF_STK) (spZ (ms_regs ms)) (srf_wr (sp1 - MRX_FRAME)) (srf_wr (sp1 - MRX_FRAME)) HARa).
  - lia.
  - lia.
  - intros a Ha. pose proof (srf_inG1 _ _ _ Ha) as Hr. rewrite ESZ in Hr. lia.
  - exact HPo.
  - apply (dk_kept_refl_g segs B TG.G_HARNESS_B lyc Sc Wc (ms_mem ms) (sp1 - MRX_STK) sp1
             (srf_wr (sp1 - MRX_FRAME))). exact HPRa.
  - exact HKc.
  - rewrite HSP1. lia.
  - rewrite HSP1. lia.
  - intros a Ha. exact Ha. }
(* the saved slots, the registers, the frames and the meter after the call *)
assert (KSAV : forall a, sp1 - 32 <= a < sp1 -> aview segs (w_H W2) mem3 a = aview segs (w_H Wc) (ms_mem ms) a).
{ intros a Ha.
  assert (Hng : ~ inG [(sp1 - MRX_FRAME, SRF_SIZE)] a)
    by (intros Hg; pose proof (srf_inG1 _ _ _ Hg) as Hr; rewrite ESZ in Hr; lia).
  refine (eq_trans (eq_sym (gover_out_aview segs _ (w_H W2) mem3 (ms_mem ms) a ltac:(lia) Hng)) _).
  pose proof HKc as (K1 & _). apply K1; [lia | rewrite HSP1; lia]. }
destruct (mrx_next B MT MTL sp1 regs0 lyc Sc Wc W2 (ms_mem ms) mem3 (ms_regs ms) regs3 Sc S3 lyc ly3 SRF_STK
  ltac:(lia) ltac:(lia) HSP1 HSV1 KSAV HP3 R2 R3' R4' RHI1 eq_refl Hfrm3 (Permutation_refl _) Hperm3 Hmo Hmo3)
  as (HSV3 & Q2 & Q3 & Q4 & QHI & F3 & P3 & M3).
assert (Q18 : YK11.getr regs3 18 = w64 SHADOW_OFF)
  by (rewrite <- R18; exact (HP3 18 ltac:(unfold acallee_saved; lia))).
(* the frame, the read-only bytes, the struct and the world after the call *)
destruct (trans_src_ok_acall_g_ge0 B LAWS HRO HNE lyc Sc Wc (ms_mem ms) md1 ly3 S3 W2 mem3 md3
  (sp1 - MRX_STK) sp1 (srf_wr (sp1 - MRX_FRAME)) fa (AK.mlen fr) HARa HAR3 Hperm3 Hfrm3 FA3 Lo3 Hi3 RK HGK
  HAPARTM HAPARTS ltac:(unfold AK.mlen in Hdisj; lia) HSRC1 ltac:(unfold AK.mlen; lia)) as (HSRC3 & KV3).
assert (HGA3 : garr8 segs (mrestrict (w_H W2) mem3) fa (map DSpec.bz (TI.tf_bytes fr))).
{ apply (srf_garr8_kept (w_H Wc) (w_H W2) (ms_mem ms) mem3 fa _ HGA1).
  intros a Ha. rewrite length_map in Ha. apply KV3. unfold AK.mlen. exact Ha. }
assert (HROM3 : trans_rom_view_rd W2 mem3) by exact (srf_rom_kept lyc Sc Wc W2 (ms_mem ms) mem3 _ _ _ RK HROM1).
assert (HTW3 : tw_at TMAP_B (aview segs (w_H W2) mem3) Bwc).
{ apply (tw_kept_GB _ _ _ HTW1). intros b m i Hin Hi. exact (gx_kept_rows segs _ _ _ _ _ HGK b m i Hin Hi). }
assert (HSF3 : mrx_sf W2 mem3 sp1 fr n) by exact HSB.
(* the code the callee returned, and the branch at +0x028 *)
pose proof (UMR.mr_srf_code (TW.zs (TI.tf_bytes fr)) n) as HCB.
pose proof (srf_code0 (DSpec.sf_code (srf_f (TI.tf_bytes fr) n)) HCB) as HC0.
pose proof (srf_entry W2 regs3 mem3 14756) as HS3.
set (E3 := srf_E regs3) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply srf_img).
assert (EE3 : forall m (q : bv 5), Z.of_nat m = bv_unsigned q -> ew E3 m = YK11.getr regs3 q)
  by (intros m q Hm; unfold E3; apply srf_ewr; exact Hm).
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) E3 (mrestrict (w_H W2) mem3)) by constructor.
pose proof HJ3 as HJ4.
clear HS HJ SHOK HEI EE.
psrr_branch_tok RUN BR HS3 SHOK3 (0, 0).
- (* a0 = 0: the code is SPEC_OK; the MAC cut *)
  apply (proj1 (srf_br_eq regs3)) in Hc.
  assert (HOK : mrx_ok fr n).
  { split; [exact Hn|]. apply HC0. rewrite HA0 in Hc. exact Hc. }
  pose proof (mrxb_top timg_B fr Bwc n HOK) as HTOP. rewrite HTOP in HM.
  paj_run_to_tok RUNTO HS3 HJ4 SHOK3 (0, 0) 14788.
  { srf_awr. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md4 := mdx) in *; clearbody md4 end.
  lazymatch type of HS3 with context [restrict _ ?mz] => rename mz into msB end.
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) mem3 a)
    by (srf_kept HFr).
  clear HF HFr HG.
  srf_reg HS3 (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) T2
    ltac:(cbn [sv_denot]; rewrite (EE3 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q2).
  srf_reg HS3 (Z_to_bv 5 3) (YK11.getr regs0 3) T3
    ltac:(cbn [sv_denot]; rewrite (EE3 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q3).
  srf_reg HS3 (Z_to_bv 5 4) (YK11.getr regs0 4) T4
    ltac:(cbn [sv_denot]; rewrite (EE3 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q4).
  srf_reg HS3 (Z_to_bv 5 18) (w64 SHADOW_OFF) T18
    ltac:(cbn [sv_denot]; rewrite (EE3 18%nat (Z_to_bv 5 18) ltac:(vm_compute; reflexivity)), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact Q18).
  assert (HPB : aregs_preserved regs3 (ms_regs msB))
    by (apply (aregs_preserved_of_st_ok segs (w_H W2) E3 _ msB regs3 [] HS3);
        [apply srf_agree | vm_compute; reflexivity]).
  assert (THI : mrx_hi regs0 (ms_regs msB))
    by (intros q Hq; rewrite <- (QHI q Hq); exact (HPB q ltac:(unfold acallee_saved; lia))).
  pmkst HS3. rewrite srf_pc_mac.
  apply (KM W2 Bwc).
  apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_MAC) (R_MAC B fr n sp1 Bw' r) W2 Bwc ly3 S3
    (ms_regs msB) (ms_mem msB) md4 HJ4 F3 P3 M3 T2 T3 T4 THI).
  + apply (mrx_saved_kept W2 W2 mem3 (ms_mem msB) sp1 regs0 HSV3). intros a Ha. apply KA2. lia.
  + apply (tw_kept TMAP_B (aview segs (w_H W2) mem3) _ Bwc HTW3).
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KA2. lia.
  + unfold R_MAC. split; [|split; [exact T18 | exact HM]].
    unfold mrx_cur. split; [exact HOK|]. split.
    * apply (mrx_frs_view B fr ly3 S3 W2 W2 mem3 (ms_mem msB)
               ltac:(unfold mrx_frs; split; [exact HGA3 | split; [exact HSRC3 | exact HROM3]])).
      -- intros a Ha. apply KA2. unfold AK.mlen in Ha. lia.
      -- intros s Hs. apply KA2. lia.
      -- intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Rb. apply KA2. lia.
    * apply (mrx_sf_kept W2 W2 mem3 (ms_mem msB) sp1 fr n HSF3). intros a Ha. apply KA2. lia.
- (* a0 <> 0: the code is not SPEC_OK; a0 = 0 and the epilogue *)
  apply srf_br_eq_f in Hc.
  assert (HNOK : DSpec.sf_code (mrx_f fr n) <> DSpec.SPEC_OK).
  { intros Hq. apply Hc. rewrite HA0. change (mrx_f fr n) with (srf_f (TI.tf_bytes fr) n) in Hq.
    rewrite Hq. reflexivity. }
  pose proof (mrxb_err timg_B fr Bwc n Hn HNOK) as HERR. rewrite HERR in HM.
  destruct (mrx_some_inv _ _ _ _ _ _ HM) as [EBw Er].
  paj_run_to_tok RUNTO HS3 HJ4 SHOK3 (0, 0) 14764.
  { srf_awr. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md4 := mdx) in *; clearbody md4 end.
  lazymatch type of HS3 with context [restrict _ ?mz] => rename mz into msB end.
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) mem3 a)
    by (srf_kept HFr).
  clear HF HFr HG.
  srf_reg HS3 (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) T2
    ltac:(cbn [sv_denot]; rewrite (EE3 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q2).
  srf_reg HS3 (Z_to_bv 5 3) (YK11.getr regs0 3) T3
    ltac:(cbn [sv_denot]; rewrite (EE3 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q3).
  srf_reg HS3 (Z_to_bv 5 4) (YK11.getr regs0 4) T4
    ltac:(cbn [sv_denot]; rewrite (EE3 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q4).
  srf_reg HS3 (Z_to_bv 5 10) (w64 0) T10 ltac:(reflexivity).
  assert (HPB : aregs_preserved regs3 (ms_regs msB))
    by (apply (aregs_preserved_of_st_ok segs (w_H W2) E3 _ msB regs3 [] HS3);
        [apply srf_agree | vm_compute; reflexivity]).
  assert (THI : mrx_hi regs0 (ms_regs msB))
    by (intros q Hq; rewrite <- (QHI q Hq); exact (HPB q ltac:(unfold acallee_saved; lia))).
  pmkst HS3. rewrite srf_pc_epi.
  apply (KE W2 Bwc).
  apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_EPI) (R_EPI Bw' r) W2 Bwc ly3 S3
    (ms_regs msB) (ms_mem msB) md4 HJ4 F3 P3 M3 T2 T3 T4 THI).
  + apply (mrx_saved_kept W2 W2 mem3 (ms_mem msB) sp1 regs0 HSV3). intros a Ha. apply KA2. lia.
  + apply (tw_kept TMAP_B (aview segs (w_H W2) mem3) _ Bwc HTW3).
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KA2. lia.
  + unfold R_EPI. split; [exact EBw|]. rewrite <- Er. exact T10.
Qed.

End seg.
