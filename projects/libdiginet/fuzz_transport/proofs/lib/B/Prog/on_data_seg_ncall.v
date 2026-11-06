(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths, module names and numbers changed; 378 of its 444 lines of code are new or changed and 699 lines of the source are left out. *)
(* on_data_seg_ncall: the notice-call piece of on_data's image-B walk, od_ncall : od_ncall_stmt
   (lib/B/Prog/on_data_seg_cut.v), code +0x3e0 .. +0x408 (0x88e28 .. 0x88e50). At the cut od_nc_at, `jalr a2`
   (a2 = S_notify of the world ondata_w3 (ondata_w2 B1 b r now) b, which the model's call_notify finds equal to
   TI.ti_notice timg_B = 0x8341c) calls notice through the premise transport_notice_cg (lib/B/Prog/notice_cg.v) in the
   same G journal, with p = F + 32 the notice in the own class-2 frame, n the data notice ondata_ntc of that world and
   Fr the current heap frame TF. notice's post folds into the walk's kept facts (TransportGCg.v dk_kept_trans_nf_g:
   its written range, GOT.ndata, is a byte of ondata_wr); the run +0x3e4 .. +0x408 (return address 0x88e2c) stores
   0xf8 into the own frame's shadow bytes 4 .. 12 and stops at the release cut od_rel_at (+0x40c), with the world
   relation at notice's world Bw' and g_fail_next Bw' = g_fail_next B1 <= 1. Image B's twin of image A's
   on_data_seg_ncall.v (+0x3cc .. +0x3f4): the same instructions 0x14 bytes later. *)
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
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
on_data_cg on_data_seg_cut on_data_seg_ncallkit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas TOpsKeep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOpsKeep.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The symbolic state at the `jalr a2` (+0x3e0): the registers as atoms, no region. *)
Definition ss_odnc : sstate := mkSS OD_NC sr_atoms [] None (mkFacts [] [] []).
(* The symbolic state after notice returns (+0x3e4): the registers as atoms, the own frame's shadow bytes 4 .. 12
   through s9. *)
Definition ODNC_R_sh : YP09.region := YP09.mkRegion (Some 25%nat) 4 13 4 13 [].
Definition ss_odnc3 : sstate := mkSS (OD_NC + 4) sr_atoms [ODNC_R_sh] None
  (mkFacts [(25%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] []).
Definition ODNC_Bx : sv := SLit 0.
Definition ODNC_B0 : Z * Z := (0, 0).

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac odnc_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac odnc_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "odnc_reg: no match for" T; fail
  end.

Section nc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma odnc_entry : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) ss_odnc
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OD_NC)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_odnc.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - exact (conj I (conj I I)).
Qed.

Lemma odnc_entry3 : forall (W : world segs) regs mem F,
  YK11.getr regs 25 = w64 (SHADOW_OFF + F / 8) -> 4096 <= F -> F mod 64 = 0 -> F + 256 <= 2 ^ 47 ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) ss_odnc3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (OD_NC + 4))) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F R25 HF0 HF64 HFc Hpsh.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  set (E := Eimg (PI := PI_transportb) (Ereg regs [])).
  assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF + F / 8)
    by (unfold E; rewrite (ew_Eimg_Ereg_nat regs [] 25 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small;
        unfold SHADOW_OFF; lia).
  rewrite restrict_mkst_fx. unfold ss_odnc3.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ODNC_R_sh base_val]. rewrite U25.
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25. change (2 ^ 3) with 8.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma odnc_main : @od_ncall_stmt fx rc B MT.
Proof.
unfold od_ncall_stmt. intros REL. unfold od_nc_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  B1 r f ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HODC & HGU & HGNE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof CALLEES as (HMAL & HSCC & HKAC & HMS & HN).
pose proof HFIX as (HPRE & HTFG & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HPRE as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hgf0 & Hm &
  HTF & Hrom & Hapart & Hinv1 & Hinv4 & Hinv3 & Hcnt & Hev).
pose proof HCUR as ((HJ1 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & H24 & Hscm & Htw1 & Hgf1 & Hdup &
  Hka & HZS & NB & HNB & HNBl & N0 & N4 & N8 & N12 & N24 & N32 & N40 & N48 & N56 & N64 & N68).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R25 & R26) & R11 & R12).
pose proof HDF as (HFC & Hbuf0 & HBg8 & HBsrc & HBoff & HBnoG & Hfp0 & Hfp8 & Hfj & Hfpg8 & Hfpfake & Hfprd & Hfpoff).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold OD_FBYTES in HFc, HFapp, HFLw.
(* the record and the layouts *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ESLO & ESHI & _).
clear HJi memS.
pose proof HJ1 as (_ & _ & (memS1 & HJi1 & _) & _).
pose proof HJi1 as (_ & Hlyle1 & _).
pose proof Hlyle1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ESLO1 & ESHI1 & _).
clear HJi1 memS1.
assert (Elo2 : ly_stk_lo ly2 = ly_stk_lo lyc) by (rewrite ESLO1, ESLO; reflexivity).
assert (Ehi2 : ly_stk_hi ly2 = ly_stk_hi lyc) by (rewrite ESHI1, ESHI; reflexivity).
assert (Hfa : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite HlyF; reflexivity).
assert (EF2 : frame_addr ly2 ONDATA_CID pos = F) by (rewrite Hfa; exact (eq_sym EF)).
assert (Hin2 : In (ONDATA_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hfin : forall f0, In f0 (frames Sc) -> In f0 (frames S2)) by (intros f0 Hf0; rewrite Hfrs; right; exact Hf0).
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
set (FL := flag_addr lyc ONDATA_CID pos) in *.
(* the stack *)
assert (HSTKS : NOTICE_STK + 176 <= ONDATA_STK) by (vm_compute; congruence).
assert (HNS0 : 0 <= NOTICE_STK) by (vm_compute; congruence).
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold ONDATA_FRAME.
  pose proof (Z.div_mod (spZ regs - 160) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 160) / 32) in *. set (r0 := (spZ regs - 160) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (Hrg : spZ regs < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (YK11.getr regs 2)) as R; change (bv_modulus 64) with (2 ^ 64) in R;
      unfold spZ; lia).
assert (Hceil1 : alloc_ceiling <= spZ regs - ONDATA_STK) by lia.
assert (USP2 : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the model on this path *)
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
assert (HL1 : length B1 = Z.to_nat TW.W_LEN)
  by exact (proj1 (TOK.send_control_m_keep timg_B TF Bw TS0.DIGINET_CMD_ACK (DSpec.fr_send b) B1 (r, f) HLB Hscm)).
destruct (TOK.send_control_m_keeps timg_B TF Bw TS0.DIGINET_CMD_ACK (DSpec.fr_send b) B1 (r, f) HLB Hscm)
  as (_ & _ & Knd & Kdc & Kdcv & _ & Kow).
destruct (odnc_w2 B1 b r now HL1) as ((L2 & G2 & O2 & FN2) & D2 & V2).
destruct (odnc_w3 (ondata_w2 B1 b r now) b L2) as (L3 & G3 & O3 & FN3).
destruct (odnc_call TF Bw b now Bw' B1 r f Hm Hscm Hdup Hka) as [HNT HNM].
destruct (odnc_notice_data timg_B TF (ondata_w3 (ondata_w2 B1 b r now) b)
  (ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b) Bw' eq_refl L3 HNM) as [Hgf' Hnd0].
assert (Hdup0 : ondata_dup Bw b = false).
{ unfold ondata_dup in Hdup |- *. rewrite D2, V2, Kdc, Kdcv in Hdup. exact Hdup. }
destruct (Hinv3 Hdup0 Hka) as [HOWsrc HOWoff].
assert (Hnd : 0 <= TW.GOT_ndata Bw) by (rewrite G3, G2, Knd in Hnd0; exact Hnd0).
assert (HOWeq : TC.OW_dn_body (ondata_w3 (ondata_w2 B1 b r now) b) (TW.GOT_ndata (ondata_w3 (ondata_w2 B1 b r now) b))
  = TC.OW_dn_body Bw (TW.GOT_ndata Bw)).
{ rewrite G3, G2, Knd, (O3 _ Hnd), (O2 _ Hnd), (Kow _ Hnd). reflexivity. }
destruct (odnc_body b HFC) as (HBL0 & HBL & HBLb).
(* what the walk kept at the cut, for ranges placed at entry *)
assert (HEG : forall a, ondata_wr Bw b a -> inG TG.G_HARNESS_B a) by exact (odnc_wr_G Bw b).
pose proof (odnc_ks B LAWS lyc Sc W memc mdc W2 mem2 _ _ (ondata_wr Bw b) HARc HK HEG) as KS.
(* the buffer and its body *)
assert (KVbuf : forall a, buf <= a < buf + Z.of_nat (length b) -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a Ha. destruct (odnc_kv B LAWS HRU HRE lyc Sc W memc mdc W2 mem2 _ _ (ondata_wr Bw b) buf (Z.of_nat (length b))
    HARc HK HEG HBoff HBsrc a Ha) as [E1 | G1]; [exact E1|]. exfalso. exact (HBnoG a Ha G1). }
assert (HBsub : trans_src_ok B lyc Sc W memc (buf + 30) (DSpec.fr_body_len b))
  by exact (trans_src_ok_sub_ge0 B lyc Sc W memc buf (Z.of_nat (length b)) (buf + 30) (DSpec.fr_body_len b) HBsrc
              ltac:(lia) ltac:(lia) ltac:(lia)).
assert (HBoffs : decode_off_win regs ONDATA_STK (buf + 30) (DSpec.fr_body_len b))
  by exact (decode_off_win_sub regs ONDATA_STK buf (Z.of_nat (length b)) (buf + 30) (DSpec.fr_body_len b) HBoff
              ltac:(lia) ltac:(lia) ltac:(lia)).
assert (HBODY : garr8 segs (mrestrict (w_H W2) mem2) (buf + 30) (map DSpec.bz (DSpec.fr_body b))).
{ eapply garr8_frame; [exact (odnc_garr8_body segs _ buf b HFC HBg8)|]. intros a Ha. rewrite length_map, HBL in Ha.
  apply (mbyte_of_aview segs). apply KVbuf. lia. }
assert (HBSRC2 : trans_src_ok B ly2 S2 W2 mem2 (buf + 30) (DSpec.fr_body_len b)).
{ apply (odnc_src_carry B LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 _ _ HARc HAR2 Hbl2 Hfin Hfa Elo2 Ehi2);
    [ | exact KS | exact HBsub | lia].
  intros a Ha. left. apply KVbuf. lia. }
(* the `jalr a2` *)
assert (T12 : YK11.getr regs2 12 = Z_to_bv 64 (TI.ti_notice timg_B)) by (rewrite R12, HNT; reflexivity).
pose proof (odnc_entry W2 regs2 mem2) as HS0.
assert (HEI0 : img_env VAL A_LIM (Eimg (PI := PI_transportb) (Ereg regs2 []))) by apply Eimg_env.
assert (P4 : 0 <= TI.ti_notice timg_B < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
assert (P5 : TI.ti_notice timg_B mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
eapply (SRr_jalr_call_pi (PL := PL_transportb) (PI := PI_transportb) W2 _ _ _ _ _ 0x600e7 (1%bv : bv 5) (12%bv : bv 5)
  (TI.ti_notice timg_B) HEI0 HS0 eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc ss_odnc]; unfold OD_NC, AF_on_data; lia
  | exact T12 | exact P4 | exact P5 |].
intros matC ms1 Ems1 _. subst ms1. clear HS0 HEI0.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_B) regsC mem2 mdC) Qx) end.
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (OD_NC + 4)))
  by (unfold regsC; rewrite YK11.getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc;
      discriminate Hc); reflexivity).
assert (RCK : forall r0 : bv 5, bv_unsigned r0 <> 1 -> YK11.getr regsC r0 = YK11.getr regs2 r0)
  by (intros r0 Hr0; unfold regsC; apply YK11.getr_other; intros E0; apply Hr0; rewrite E0; reflexivity).
assert (RC2 : YK11.getr regsC 2%bv = w64 sp1) by (rewrite RCK by (vm_compute; discriminate); exact R2).
assert (RC3 : YK11.getr regsC 3%bv = w64 (as_gp B))
  by (rewrite RCK by (vm_compute; discriminate); exact (eq_trans R3 Hgp)).
assert (RC4 : YK11.getr regsC 4%bv = w64 (as_tp B))
  by (rewrite RCK by (vm_compute; discriminate); exact (eq_trans R4 Htp)).
assert (RC11 : YK11.getr regsC 11%bv = w64 (F + 32)) by (rewrite RCK by (vm_compute; discriminate); exact R11).
assert (USPC : spZ regsC = sp1) by (unfold spZ; rewrite RC2; unfold w64; apply unsigned_lit_small; lia).
assert (Hwin1 : spZ regs - ONDATA_STK <= spZ regsC - NOTICE_STK) by (rewrite USPC; lia).
assert (Hwin2 : spZ regsC <= spZ regs) by (rewrite USPC; lia).
(* notice's premises *)
assert (HJC : @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
  ((ONDATA_CID, pos) :: own) ly2 S2 W2 mem2 mdC (k + e))
  by (apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ1).
assert (HRC1 : YK0s.ret_ok (YK11.getr regsC 1))
  by (rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold OD_NC, AF_on_data; lia | reflexivity]).
assert (EBN : BASE + (OD_NC + 4) = 0x88e2c) by (vm_compute; reflexivity).
assert (HRA : 4096 <= raZ regsC)
  by (unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia).
assert (HSPM : spZ regsC mod 16 = 0).
{ rewrite USPC. destruct Hsp1 as (_ & M1). pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1.
  rewrite M1, Z.add_0_r in D1. rewrite D1. replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring.
  apply Z.mod_mul. lia. }
assert (HROM2 : trans_rom_view_rd W2 mem2).
{ intros a Ha. rewrite <- (Hrom a Ha). pose proof HK as (_ & _ & K3 & _).
  destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho Hen].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact Hen].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_B_LO in Gh. lia. }
assert (HTFC : trans_tframe_at B ly2 S2 W2 mem2 regsC NOTICE_STK TF)
  by exact (odnc_tframe B LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 regs regsC ONDATA_STK NOTICE_STK
              (ondata_wr Bw b) TF HARc HAR2 Hbl2 Hfin Hfa Elo2 Ehi2 HK HEG Hwin1 Hwin2 HTFG HTF).
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (DF8 : F = 8 * (F / 8))
  by (pose proof (Z.div_mod F 8 ltac:(lia)) as D; rewrite DFm8, Z.add_0_r in D; exact D).
assert (HF8b : 512 <= F / 8 <= 17592186044416) by lia.
assert (HNTC : trans_ntc_at B ly2 S2 W2 mem2 regsC NOTICE_STK (F + 32)
  (ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b)).
{ unfold trans_ntc_at.
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split; [exact (odnc_ntc_src B LAWS ly2 S2 W2 mem2 md2 F pos HAR2 Hin2 EF2 HF0 HF64 HFc HFapp HZS)|].
  split; [left; unfold NTC_SIZE; lia|].
  exists NB. split; [exact HNB|]. split; [exact HNBl|].
  unfold ondata_ntc.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
    TI.n_body TI.n_ann].
  rewrite N48, HBL.
  split; [exact N0|]. split; [exact N4|]. split; [exact N8|]. split; [exact N12|]. split; [exact N32|].
  split; [exact N40|]. split; [exact N56|]. split; [exact N64|]. split; [exact N68|].
  split; [exact HBODY|]. split; [exact HBSRC2|].
  split; [exact (odnc_off_win regs regsC ONDATA_STK NOTICE_STK _ _ HBoffs Hwin1 Hwin2)|].
  exact N24. }
assert (HAPART : notice_apart W2 mem2 (F + 32) (ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b) TF
  (ondata_w3 (ondata_w2 B1 b r now) b))
  by exact (odnc_apart B LAWS ly2 S2 W2 mem2 md2 TF Bw b _ F pos buf NB HAR2 Hin2 EF2 Hapart HNB HNBl N48 HBnoG
              ltac:(rewrite HBL; lia)).
assert (HND : TI.n_kind (ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b) = TC.N_DATA ->
  trans_src_ok B ly2 S2 W2 mem2
    (TC.OW_dn_body (ondata_w3 (ondata_w2 B1 b r now) b) (TW.GOT_ndata (ondata_w3 (ondata_w2 B1 b r now) b)))
    (TI.n_body_len (ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b)) /\
  decode_off_win regsC NOTICE_STK
    (TC.OW_dn_body (ondata_w3 (ondata_w2 B1 b r now) b) (TW.GOT_ndata (ondata_w3 (ondata_w2 B1 b r now) b)))
    (TI.n_body_len (ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b)) /\
  TI.n_body_len (ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b) < 2 ^ 32).
{ intros _. change (TI.n_body_len (ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b)) with (DSpec.fr_body_len b).
  rewrite HOWeq. split; [|split; [|lia]].
  - apply (odnc_src_carry B LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 _ _ HARc HAR2 Hbl2 Hfin Hfa Elo2 Ehi2);
      [ | exact KS | exact HOWsrc | lia].
    exact (odnc_kv B LAWS HRU HRE lyc Sc W memc mdc W2 mem2 _ _ (ondata_wr Bw b) _ _ HARc HK HEG HOWoff HOWsrc).
  - exact (odnc_off_win regs regsC ONDATA_STK NOTICE_STK _ _ HOWoff Hwin1 Hwin2). }
assert (HNEV : st_nev S + (k + e) + NOTICE_EV <= EV_MAX) by (unfold NOTICE_EV; lia).
(* the call of notice *)
eapply SRr_bind.
{ exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((ONDATA_CID, pos) :: own) ly2 S2 W2 mem2 mdC (k + e) regsC
    (F + 32) (ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b) TF (ondata_w3 (ondata_w2 B1 b r now) b) Bw'
    HJC HRC1 HRA RC3 RC4 RC11 HSPM ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HNTC HTFC HROM2 Htw1 HNM
    HAPART HND HNEV). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX3).
assert (He30 : e3 = 0) by (unfold NOTICE_EV in He3; lia). subst e3.
rewrite Z.add_0_r in HJ3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _).
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
assert (EF3 : frame_addr ly3 ONDATA_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF3c; reflexivity).
assert (Hfrs3 : frames S3 = (ONDATA_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hin3 : In (ONDATA_CID, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 ONDATA_CID pos HAR3 Hin3) as (_ & _ & _ & HFsh3).
rewrite EF3 in HFsh3. change (fs_frame_bytes ONDATA_CID / 8) with 32 in HFsh3.
change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh3.
assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym (Permutation_trans Hperm3 Hperm)) Hbm)).
assert (R3_25 : YK11.getr regs3 (Z_to_bv 5 25) = w64 (SHADOW_OFF + F / 8)).
{ rewrite (HP3 25 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). exact R25. }
(* what the call kept, from its entry to notice's return *)
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONDATA_CID pos F FL HAR2 Hfrs Hbl2
  HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4').
assert (KC3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - ONDATA_STK) (spZ regs)
  (ondata_wr Bw b)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 mem2 W3 mem3
    (spZ regs - ONDATA_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (ondata_wr Bw b)
    (notice_wr (ondata_w3 (ondata_w2 B1 b r now) b) (ondata_ntc (ondata_w3 (ondata_w2 B1 b r now) b) b))
    (dkg_nf ONDATA_CID F FL)).
  - exact Hceil1.
  - lia.
  - exact Hfa.
  - exact Hfin.
  - exact Hbl2.
  - exact N1.
  - exact N3.
  - exact HK.
  - exact HK3.
  - exact Hwin1.
  - exact Hwin2.
  - intros a Ha. left. unfold ondata_wr. do 9 right. exact (odnc_nwr_in _ Bw b a Ha). }
(* +0x3e4 .. +0x408: shadow bytes 4 .. 12 := 0xf8, to the release cut *)
rewrite RC1.
pose proof (odnc_entry3 W3 regs3 mem3 F R3_25 HF0 HF64 ltac:(lia)
  ltac:(intros i Hi; exact (proj1 (HFsh3 i ltac:(lia))))) as HS3.
set (E3 := Eimg (PI := PI_transportb) (Ereg regs3 [])) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E3 n0 = YK11.getr regs3 r0)
  by (intros n0 r0 Hn0; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (U25c : bv_unsigned (ew E3 25) = SHADOW_OFF + F / 8)
  by (rewrite (EE3 25%nat (Z_to_bv 5 25) eq_refl), R3_25; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK3 : sh_ok segs ODNC_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUNTO.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 ODNC_B0 OD_REL.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply awr_ok_x_cons_own with (cid := ONDATA_CID); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U25c in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF3. change (fs_frame_bytes ONDATA_CID / 8) with 32. lia.
  - apply awr_ok_x_nil. }
set (md5 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md5. clear mat.
lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms4 end.
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 13) ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HFr);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta. odnc_win Hiw Hx ltac:(rewrite ?U25c in Hx; lia). }
assert (GA4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KC4 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 (ms_mem ms4) (spZ regs - ONDATA_STK) (spZ regs)
  (ondata_wr Bw b)).
{ apply (odnc_kept_w B LAWS HGX FFL lyc Sc ly3 S3 W W3 memc mdc mem3 md3 mem3 (ms_mem ms4) (spZ regs - ONDATA_STK)
    (spZ regs) pos F FL (ondata_wr Bw b) (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HARc HAR3
    Hfrs3 Hbl3 ELF3c EF eq_refl Hceil1 ltac:(lia)); [| exact KC3 | exact KR4 | exact GA4].
  intros a Ha. right. left. right. left. change (fs_frame_bytes ONDATA_CID / 8) with 32. cbv beta in Ha. lia. }
pmkst HS3.
(* the registers the release reads *)
odnc_reg HS3 (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) F2
  ltac:(cbn [sv_denot]; rewrite (EE3 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
odnc_reg HS3 (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) F3
  ltac:(cbn [sv_denot]; rewrite (EE3 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
odnc_reg HS3 (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) F4
  ltac:(cbn [sv_denot]; rewrite (EE3 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
odnc_reg HS3 (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) F8
  ltac:(cbn [sv_denot]; rewrite (EE3 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
odnc_reg HS3 (Z_to_bv 5 9) (YK11.getr regs3 (Z_to_bv 5 9)) F9
  ltac:(cbn [sv_denot]; rewrite (EE3 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
odnc_reg HS3 (Z_to_bv 5 25) (YK11.getr regs3 (Z_to_bv 5 25)) F25
  ltac:(cbn [sv_denot]; rewrite (EE3 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
odnc_reg HS3 (Z_to_bv 5 26) (YK11.getr regs3 (Z_to_bv 5 26)) F26
  ltac:(cbn [sv_denot]; rewrite (EE3 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* the bytes the release reads: the saved words and s1 + 24 above sp1, the frame's last word *)
pose proof HK3 as (K31 & _ & _ & K34 & _).
assert (KSTK : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite KR4 by (unfold SHADOW_OFF; lia). rewrite USPC in K31. rewrite K31 by lia. reflexivity. }
assert (HSHF : SHADOW_OFF + F / 8 + 32 <= F \/ F + 256 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
assert (KFL : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) (ms_mem ms4) (F + 248 + i) = aview segs (w_H W2) mem2 (F + 248 + i)).
{ intros i Hi. rewrite KR4 by (unfold SHADOW_OFF in *; destruct HSHF; lia).
  apply (K34 ONDATA_CID pos (F + 248 + i) Hin2).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF2. change (fs_frame_bytes ONDATA_CID) with 256. lia.
  - intros Hw. apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONDATA_CID pos (F + 248 + i) HAR2 Hin2);
      [rewrite EF2; change (fs_frame_bytes ONDATA_CID) with 256; lia|].
    exact (trans_g_img _ (notice_wr_G _ _ _ Hw)). }
assert (HSo : forall o, In o OD_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold OD_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OD_REL)) mm rom) mdx) Qx) end.
apply (REL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly3 S3 W3 (ms_mem ms4) md5 e (ms_regs ms4) HFIX).
- split; [|split; [|split]].
  + split; [exact HJ3|].
    split; [exact He|].
    split; [exact Hfrs3|].
    split; [exact (Permutation_trans Hperm3 Hperm)|].
    split; [exact ELF3c|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
    split; [exact KC4|].
    split.
    * rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia.
    * unfold OD_FBYTES. change (flag_addr lyc ONDATA_CID pos) with FL. rewrite <- HFLw.
      apply rdword_ext. intros i Hi. replace (F + 256 - 8 + i) with (F + 248 + i) by lia. exact (KFL i Hi).
  + rewrite <- H24. apply rdword_ext. intros i Hi. apply KSTK. lia.
  + apply (tw_kept TMAP_B (aview segs (w_H W3) mem3)); [exact HX3|].
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KR4; [lia | unfold SHADOW_OFF; lia].
  + rewrite Hgf', FN3, FN2. exact Hgf1.
- assert (CH : forall n0, acallee_saved n0 -> bv_unsigned (Z_to_bv 5 n0) <> 1 ->
    YK11.getr regs3 (Z_to_bv 5 n0) = YK11.getr regs2 (Z_to_bv 5 n0))
    by (intros n0 Hn0 H1; rewrite (HP3 n0 Hn0); exact (RCK _ H1)).
  split; [exact (eq_trans F2 (eq_trans (CH 2 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) R2))|].
  split; [exact (eq_trans F3 (eq_trans (CH 3 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) R3))|].
  split; [exact (eq_trans F4 (eq_trans (CH 4 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) R4))|].
  split; [exact (eq_trans F8 (eq_trans (CH 8 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) R8))|].
  split; [exact (eq_trans F9 (eq_trans (CH 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) R9))|].
  split; [exact (eq_trans F25 (eq_trans (CH 25 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) R25))|].
  exact (eq_trans F26 (eq_trans (CH 26 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) R26)).
Qed.

End nc.

Theorem od_ncall : forall fx rc B MT, @od_ncall_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@odnc_main fx rc B MT). Qed.

Print Assumptions od_ncall.
