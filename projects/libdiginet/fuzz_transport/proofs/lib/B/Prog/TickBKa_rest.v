(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths and module names changed; 376 of its 462 lines of code are new or changed and 1124 lines of the source are left out. *)
(* TickBKa_rest: the keepalive piece of the image-B walk of diginet_session_tick from +0x758 (0x897f4, the join after
   the keepalive test) to the epilogue cut, tka_rest. rule 24: proves no function (a part of a piece of a walk; the walk
   is composed at TickCutB.v tick_holds_of). Image B's twin of lib/A/Prog/TickKa_rest.v.
   Run C (+0x758 .. +0x794, PaRun token engine) checks and stores a4 at s + 184 (g_s.next_keepalive_us := tka_vk),
   checks, loads, increments and stores g_s.stats.tx_keepalives (s + 18216), sets a2 = a3 = 1, a0 = s, a4 = now (from
   s1 + 56) and calls send_data (0x89830; a1 = ka = frame + 144); send_data's contract (send_data_cg.v
   transport_send_data_cg, the ninth of TickCutB.v tick_callees) is taken in the same G journal, its premises from the
   cut's facts and the run (TickBKa_kit.v tka_w_eq: the memory relates to TickCutB.v tick_ka_w; ka's trans_src_ok by
   TickBKit.v trans_src_ok_fake); run D (+0x798 .. +0x7a4) moves send_data's result to s10, re-poisons ka's shadow
   byte (18) and jumps to the epilogue, whose cut (TickCutB.v tick_epi_at) closes the walk. The caller's kept memory
   is carried with TransportGFrame.v dk_kept_nfz_gw (the own frame and G) and TransportGCg.v dk_kept_trans_nf_g
   (send_data's acall_kept_g, written range senddata_wr, a row of tick_wr). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k YE2y AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg TickCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TickBKit TickBKa_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
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

(* The write rights of run C: the two words of g_s (G), the other regions read-only. *)
Ltac tka_awrC :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat first
  [ apply awr_ok_x_nil
  | apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]
  | apply awr_ok_x_cons_g;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      unfold inG; apply Exists_exists; exists (TB_g_s, TW.SZ_g_s);
      split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, TB_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia] |] ].

(* The write right of run D: ka's shadow byte, a shadow byte of the own frame. *)
Ltac tka_awrD U19 EF :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EF; change (fs_frame_bytes TICK_CID / 8) with 256; lia |];
  apply awr_ok_x_nil.

(* The value of an unchanged register of the run's valuation: its value at the run's entry. *)
Ltac tka_rv EE R :=
  cbn [sv_denot];
  lazymatch goal with |- context [ew _ ?n] => rewrite (EE n (Z_to_bv 5 (Z.of_nat n)) eq_refl) end;
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma tka_rest : tick_laws B MT -> tick_callees B MT -> tick_epi_at B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
    (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (B0 : list byte) (ly2 : alayout) (S2 : astate)
    (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
    (memR : word -> option byte) (mdR : Model) (regsR : bvmap 5 word),
  tick_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
  tick_ka_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now r TF Bw Bw' B0 pos sp1 F
    ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((TICK_CID, pos) :: own) ly2 S2 W2 memR mdR (k + e) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ tka_Z F a -> aview segs (w_H W2) memR a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memR a) ->
  aview segs (w_H W2) memR (SHADOW_OFF + F / 8 + 18) = Some 1 ->
  aview segs (w_H W2) memR (F + 144) = Some 0 ->
  tick_regs_run regs regsR sp1 F ->
  YK11.getr regsR 11 = w64 (F + 144) ->
  YK11.getr regsR 13 = w64 TKA_SH184 ->
  YK11.getr regsR 14 = w64 (tka_vk B0 now) ->
  YK11.getr regsR 17 = w64 (TICK_S + 18144) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsR (Z_to_bv 64 (BASE + TKA_C)) memR (YK11.seg_rom segs)) mdR)
    (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).
Proof.
intros LAWS0 CALLS EPI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F B0 ly2 S2
  W2 mem2 md2 e memR mdR regsR HFIX HCUR HJR KR GR SH18 KA0 HRR R11 R13 R14 R17.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGN).
pose proof CALLS as (_ & _ & _ & _ & _ & _ & _ & _ & HSD & _).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw & Hgf & Hm & HTF & Hrom &
  Hap & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (((HJ1 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hnw) & Htw0 & Hgf0 & Hinv0 & Hm0).
pose proof HRR as ((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R21 & R22 & R23 & R24).
pose proof YE2y.asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TCK.TICK_FBYTES in HFc, HFapp, HFLw.
assert (He0 : e = 0) by (unfold TICK_EV in He; lia). subst e.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJR) as HARR.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite ?Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _).
assert (HSS : TICK_STK = 208 + SENDDATA_STK) by reflexivity.
assert (HSE : SENDDATA_EV = 0) by reflexivity.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold TICK_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r0 := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (HACE : alloc_ceiling <= sp1 - SENDDATA_STK) by lia.
assert (HSD0 : 0 <= SENDDATA_STK <= 2 ^ 20) by (split; vm_compute; congruence).
assert (Hsp47 : 2 ^ 46 <= sp1 /\ sp1 + 64 <= 2 ^ 47) by lia.
assert (HLB0 : length B0 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
(* the own frame *)
assert (Hin : In (TICK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EF2 : frame_addr ly2 TICK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
set (FL := flag_addr lyc TICK_CID pos) in *.
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 TICK_CID pos F FL HAR2 Hfrs Hbl2
  HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
destruct (al_frames _ _ LAWS ly2 S2 W2 memR mdR TICK_CID pos HARR Hin) as (_ & _ & HFb & HFsh).
rewrite EF2 in HFb, HFsh.
change (fs_frame_bytes TICK_CID) with 2048 in HFb. change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity. rewrite ESH in HFsh.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (HF8 : F / 8 = 8 * (F / 64))
  by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (DFm8 : F mod 8 = 0).
{ rewrite DF. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (HFG : F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 2048) TICK_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (TICK_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 2048 /\ TICK_S <= x < TICK_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F TICK_S) as [h3|h3]; [exists TICK_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 TICK_CID pos x HAR2 Hin);
    [rewrite EF2; change (fs_frame_bytes TICK_CID) with 2048; lia|].
  apply trans_g_img. unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, TICK_S in *; cbn [fst snd]; lia]. }
assert (ZNF : forall a, tka_Z F a -> dkg_nf TICK_CID F FL a).
{ intros a [-> | ->]; unfold dkg_nf; change (fs_frame_bytes TICK_CID) with 2048; change (2048 / 8) with 256;
    [right; left | left]; lia. }
assert (ZCG : forall a, tka_Zc a -> inG TG.G_HARNESS_B a).
{ intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
  split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold tka_Zc, in_zr, TICK_S, TB_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia]. }
(* the world relation at B0 and now at s1 + 56, at memR *)
assert (KTW : tw_at TMAP_B (aview segs (w_H W2) memR) B0).
{ apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact Htw0|].
  intros x (o & b & n & Hrow & Hx).
  assert (HxG : inG TG.G_HARNESS_B x).
  { unfold inG. apply Exists_exists. exists (b, n). split; [exact (TMAP_B_in_G o b n Hrow) | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transportb_segs_low _ x HGX HxG) as Hl. unfold kLowMemEnd in Hl.
  apply KR; [lia|]. intros Hz. exact (N2 x (ZNF x Hz) (trans_g_img x HxG)). }
assert (KNOW : rdword (aview segs (w_H W2) memR) (sp1 + 56) = Some now).
{ rewrite <- Hnw. apply rdword_ext. intros i Hi. apply KR; [lia|].
  unfold tka_Z, SHADOW_OFF in *. lia. }
(* run C, +0x758 .. +0x794: the stores at s + 184 and s + 18216, send_data's arguments, `jal send_data` *)
pose proof (tka_entryC B ly2 S2 W2 regsR memR mdR B0 now sp1 HTC HARR KTW R9 R13 R17 R20 R24 (proj1 Hsp47)
  (proj2 Hsp47)
  (proj2 Hsp1) Hnow KNOW) as HS.
set (E0 := tka_E regsR (tka_valsC B0 now)) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, tka_E; apply Eimg_env).
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E0 n = YK11.getr regsR q)
  by (intros n q Hn; unfold E0, tka_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 2)%nat -> ew E0 (32 + j) = nth j (tka_valsC B0 now) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, tka_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
cbn [Nat.add nth tka_valsC] in E32, E33.
assert (SHOK : sh_ok segs TKA_Bx (@nil shent) E0 (mrestrict (w_H W2) memR)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
paj_run_tok RUN HS HJR SHOK TKA_B0.
{ tka_awrC. }
set (mdC := with_vm_backing (m_vm_lazy mdR) mat mdR) in *. clearbody mdC. clear mat.
(* what run C kept and stored *)
assert (KRC : forall a, 0 <= a < 2 ^ 64 -> ~ tka_Zc a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) memR a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ tka_Zc HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  sn_winB Hiw Hx ltac:(unfold tka_Zc, TICK_S, TB_g_s; first [lia | left; lia | right; lia]). }
assert (GAC : forall a, apresent (w_H W2) memR a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (RVK : 0 <= tka_vk B0 now < 2 ^ 64)
  by (unfold tka_vk, tka_v1, TS0.u64; destruct (_ <=? now); apply Z.mod_pos_bound; lia).
assert (Rx : 0 <= TW.S_stats_tx_keepalives B0 < 2 ^ 64)
  by exact (TWL.u_at_range B0 TW.A_S_stats_tx_keepalives 8).
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RG1.
pose proof (st_ok_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
cbn [ms_mem restrict] in RG1, RG3.
pose proof (sn_chunk_valB E0 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 6158072 8 (SOff 14 0) RG1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VNK.
pose proof (sn_chunk_valB E0 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 6176104 8 (SOff 32 1) RG3
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VTX.
clear RG1 RG3.
assert (D14 : sv_denot E0 (SOff 14 0) = Z_to_bv 64 (tka_vk B0 now)).
{ cbn [sv_denot]. rewrite (EE 14%nat 14%bv eq_refl), R14. unfold w64.
  rewrite unsigned_lit_small by exact RVK. rewrite Z.add_0_r. reflexivity. }
assert (DTX : bv_unsigned (sv_denot E0 (SOff 32 1)) = TS0.u64 (TW.S_stats_tx_keepalives B0 + 1)).
{ cbn [sv_denot]. rewrite E32. rewrite (unsigned_lit_small (TW.S_stats_tx_keepalives B0)) by exact Rx.
  rewrite Z_to_bv_unsigned. reflexivity. }
rewrite D14, unsigned_lit_small in VNK by exact RVK.
rewrite DTX in VTX.
change (8 * Z.of_N 8) with 64 in VNK, VTX. change (N.to_nat 8) with 8%nat in VNK, VTX.
rewrite (Z.mod_small (tka_vk B0 now)) in VNK by exact RVK.
rewrite (Z.mod_small (TS0.u64 (TW.S_stats_tx_keepalives B0 + 1))) in VTX
  by (unfold TS0.u64; apply Z.mod_pos_bound; lia).
(* the world relation at tick_ka_w B0 now *)
assert (PTW : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms)) (tick_ka_w B0 now)).
{ rewrite (tka_w_eq B0 now HLB0).
  apply (tka_tw_two (aview segs (w_H W2) memR)); [exact KTW | | |].
  - intros j Hj. replace (TB_g_s + 184 + Z.of_nat j) with (0 + 6158072 + Z.of_nat j) by (unfold TB_g_s; lia).
    exact (tka_vm_rd _ _ _ 8 _ j VNK Hj).
  - intros j Hj. replace (TB_g_s + 18216 + Z.of_nat j) with (0 + 6176104 + Z.of_nat j) by (unfold TB_g_s; lia).
    exact (tka_vm_rd _ _ _ 8 _ j VTX Hj).
  - intros x (o & b & n & Hrow & Hx) Hn.
    assert (HxG : inG TG.G_HARNESS_B x).
    { unfold inG. apply Exists_exists. exists (b, n).
      split; [exact (TMAP_B_in_G o b n Hrow) | unfold in_zr; cbn [fst snd]; lia]. }
    pose proof (inG_low segs B transportb_segs_low _ x HGX HxG) as Hl. unfold kLowMemEnd in Hl.
    apply KRC; [lia | exact Hn]. }
(* what the call kept, from its entry to the call of send_data *)
assert (KC : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (ms_mem ms) (spZ regs - TICK_STK) (spZ regs)
  (tick_wr Bw)).
{ apply (dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2
    (ms_mem ms) (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F FL (tick_wr Bw) (fun a => tka_Z F a \/ tka_Zc a) HGX
    HARc HAR2 Hfrs Hbl2 HlyF EF eq_refl FFL ltac:(lia) ltac:(lia)); [| exact HK | |].
  - intros a [Hz | Hz]; [right; left; exact (ZNF a Hz) | right; right; exact (ZCG a Hz)].
  - intros a Ha Hn. rewrite (KRC a Ha (fun Hz => Hn (or_intror Hz))). exact (KR a Ha (fun Hz => Hn (or_introl Hz))).
  - intros a Ha. exact (GAC a (GR a Ha)). }
(* the registers at the call *)
pmkst HS.
sn_regB HS (Z_to_bv 5 10) (w64 SENDDATA_S) Q10 ltac:(reflexivity).
sn_regB HS (Z_to_bv 5 11) (w64 (F + 144)) Q11 ltac:(tka_rv EE R11).
sn_regB HS (Z_to_bv 5 12) (w64 (Z.of_nat (length [DSpec.b8 0]))) Q12 ltac:(reflexivity).
sn_regB HS (Z_to_bv 5 13) (w64 (bv_swrap 32 1)) Q13 ltac:(reflexivity).
sn_regB HS (Z_to_bv 5 14) (w64 now) Q14
  ltac:(cbn [sv_denot]; rewrite E33; rewrite unsigned_lit_small by exact Hnow; rewrite Z.add_0_r; reflexivity).
sn_regB HS (1%bv : bv 5) (Z_to_bv 64 (BASE + TKA_R)) Q1 ltac:(apply codeptr_val; exact HEI).
sn_regB HS (Z_to_bv 5 2) (w64 sp1) Q2 ltac:(tka_rv EE R2).
sn_regB HS (Z_to_bv 5 3) (w64 (as_gp B)) Q3 ltac:(tka_rv EE (eq_trans R3 Hgp)).
sn_regB HS (Z_to_bv 5 4) (w64 (as_tp B)) Q4 ltac:(tka_rv EE (eq_trans R4 Htp)).
sn_regB HS (Z_to_bv 5 8) (w64 (spZ regs)) Q8 ltac:(tka_rv EE R8).
sn_regB HS (Z_to_bv 5 9) (w64 sp1) Q9 ltac:(tka_rv EE R9).
sn_regB HS (Z_to_bv 5 18) (w64 F) Q18 ltac:(tka_rv EE R18).
sn_regB HS (Z_to_bv 5 19) (w64 (SHADOW_OFF + F / 8)) Q19 ltac:(tka_rv EE R19).
sn_regB HS (Z_to_bv 5 27) (w64 F) Q27 ltac:(tka_rv EE R27).
assert (USPC : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
assert (EBR : BASE + TKA_R = 0x89834) by (vm_compute; reflexivity).
(* +0x794: send_data (s, ka, 1, 1, now), through its contract in the same G journal *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_send_data) rg mm mdx) Qx) end.
assert (KA1 : aview segs (w_H W2) (ms_mem ms) (F + 144) = Some 0).
{ rewrite KRC; [exact KA0 | lia |]. unfold tka_Zc, TICK_S, TB_g_s, TW.SZ_g_s in *. lia. }
assert (SH1 : aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + (F + 144) / 8) = Some 1).
{ assert (E8 : (F + 144) / 8 = F / 8 + 18)
    by (replace (F + 144) with (18 * 8 + F) by ring; rewrite Z.div_add_l by lia; ring).
  rewrite E8, Z.add_assoc.
  rewrite KRC; [exact SH18 | unfold SHADOW_OFF; lia |]. unfold tka_Zc, TICK_S, TB_g_s, SHADOW_OFF. lia. }
assert (NGK : forall x, F + 144 <= x < F + 144 + Z.of_nat (length [DSpec.b8 0]) -> ~ inG TG.G_HARNESS_B x).
{ intros x Hx Hg. cbn [length Z.of_nat Pos.of_succ_nat] in Hx.
  apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 TICK_CID pos x HAR2 Hin);
    [rewrite EF2; change (fs_frame_bytes TICK_CID) with 2048; lia | exact (trans_g_img x Hg)]. }
pose proof (tka_inv B0 now HLB0 Hinv0) as (I1 & I4).
eapply SRr_bind.
{ exact (HSD fx STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) ly2 S2 W2 (ms_mem ms) mdC (k + 0) (ms_regs ms)
    (F + 144) 1 now r [DSpec.b8 0] TF (tick_ka_w B0 now) Bw' HJR
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold TKA_R, AF_diginet_session_tick; lia |
      reflexivity])
    ltac:(unfold raZ; rewrite Q1, EBR; rewrite unsigned_lit_small by lia; lia)
    Q3 Q4 Q10 Q11 Q12 Q13 Q14
    ltac:(rewrite USPC; destruct Hsp1 as (_ & M1); pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1;
          rewrite M1, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
          apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) ltac:(lia) Hnow ltac:(lia)
    ltac:(change (TW.zs [DSpec.b8 0]) with [0]; intros j Hj; cbn [length] in Hj;
          assert (Ej : j = 0%nat) by lia; subst j; cbn [nth Z.of_nat]; rewrite Z.add_0_r;
          split; [exact (YE2y.val_mem1_of_aview _ _ _ _ KA1) | lia])
    (trans_src_ok_fake B ly2 S2 W2 (ms_mem ms) (F + 144) (Z.of_nat (length [DSpec.b8 0]))
      ltac:(exists TICK_CID, pos; split; [exact Hin|]; rewrite EF2; change (fs_frame_bytes TICK_CID) with 2048;
            cbn [length Z.of_nat Pos.of_succ_nat]; lia)
      ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; unfold decode_rd_ok;
            split; [intros a Ha; apply can_aview_vis; apply GAC; exact (proj1 (HFb a ltac:(lia)))|];
            split; [apply tka_ra_one; [rewrite Z.add_mod, DFm8 by lia; reflexivity | exact SH1]|];
            split; [apply (TransportGNotice.frame_hull_vis _ F 2048 (F + 144) 1);
                      [lia | exact HF64 | reflexivity | lia | lia | lia |];
                    intros i Hi; lazymatch goal with |- _ (?x + i) <> None => change x with (SHADOW_OFF + F / 8) end;
                    apply can_aview_vis; apply GAC; exact (proj1 (HFsh i Hi))|];
            split; [apply (amem_range_sub_app F 2048); [exact HFapp | lia | lia | lia | lia]|];
            split; lia))
    ltac:(unfold decode_off_win; left; rewrite USPC; cbn [length Z.of_nat Pos.of_succ_nat]; lia)
    NGK
    ltac:(apply NGK; cbn [length Z.of_nat Pos.of_succ_nat]; lia)
    PTW
    ltac:(rewrite (tka_gfn B0 now HLB0); exact Hgf0)
    Hm0
    ltac:(intros a Ha; rewrite <- (Hrom a Ha); pose proof KC as (_ & _ & K3 & _);
          destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho Hen];
          apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact Hen];
          intro Ga; pose proof (inG_G_HARNESS_hull a Ga) as Gh; pose proof (trans_ro_rd_bounds a Ha) as Rb;
          unfold TG.G_HARNESS_B_LO in Gh; lia)
    I1 I4
    ltac:(rewrite Hfrs; change (count_cid SENDDATA_CID ((TICK_CID, pos) :: frames Sc)) with
            (0 + count_cid SENDDATA_CID (frames Sc)); lia)
    ltac:(rewrite Hfrs; change (count_cid TRANS_BC_CID ((TICK_CID, pos) :: frames Sc)) with
            (0 + count_cid TRANS_BC_CID (frames Sc)); lia)
    ltac:(rewrite HSE; unfold TICK_EV in *; lia)). }
intros W3 c3 _ HPOST.
unfold transport_senddata_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & X0 & Xtw &
  Xgf).
assert (He30 : e3 = 0) by (rewrite HSE in He3; lia). subst e3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite ?Z.add_0_r in HJi3.
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
assert (EF3 : frame_addr ly3 TICK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF3c; reflexivity).
assert (Hfrs3 : frames S3 = (TICK_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hin3 : In (TICK_CID, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3)).
{ intros bm Hbm. apply Hbl2 in Hbm. exact (Permutation_in _ (Permutation_sym Hperm3) Hbm). }
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 TICK_CID pos HAR3 Hin3) as (_ & _ & _ & HFsh3).
rewrite EF3 in HFsh3. change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh3. rewrite ESH in HFsh3.
assert (R3_19 : YK11.getr regs3 (Z_to_bv 5 19) = w64 (SHADOW_OFF + F / 8))
  by (rewrite (HP3 19 ltac:(hnf; lia)); exact Q19).
(* what the call kept, from its entry to send_data's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - TICK_STK) (spZ regs) (tick_wr Bw)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 (ms_mem ms) W3 mem3
    (spZ regs - TICK_STK) (spZ regs) (spZ (ms_regs ms) - SENDDATA_STK) (spZ (ms_regs ms)) (tick_wr Bw)
    senddata_wr (dkg_nf TICK_CID F FL)).
  - lia.
  - lia.
  - intros c p. unfold frame_addr. rewrite HlyF. reflexivity.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - exact Hbl2.
  - exact N1.
  - exact N3.
  - exact KC.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. exact (tka_sdwr_tick Bw a Ha). }
(* run D, +0x798 .. +0x7a4: s10 = a0, ka's shadow byte := 0xf8, `j` to the epilogue cut *)
rewrite Q1.
pose proof (tka_entryD W3 regs3 mem3 F R3_19 HF0 HF64 ltac:(lia) (proj1 (HFsh3 18 ltac:(lia)))) as HS3.
set (E3 := tka_E regs3 []) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3, tka_E; apply Eimg_env).
assert (EE3 : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E3 n = YK11.getr regs3 q)
  by (intros n q Hn; unfold E3, tka_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U19c : bv_unsigned (ew E3 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE3 19%nat (Z_to_bv 5 19) eq_refl), R3_19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK3 : sh_ok segs TKA_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 TKA_B0 TICK_EPI.
{ tka_awrD U19c EF3. }
set (md5 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md5. clear mat.
lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms4 end.
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> a <> SHADOW_OFF + F / 8 + 18 ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => x = SHADOW_OFF + F / 8 + 18) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta. sn_winB Hiw Hx ltac:(rewrite ?U19c in Hx; lia). }
assert (GA4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (KC4 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 (ms_mem ms4) (spZ regs - TICK_STK) (spZ regs)
  (tick_wr Bw)).
{ apply (dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc ly3 S3 W memc mdc W3 mem3 md3 mem3
    (ms_mem ms4) (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F FL (tick_wr Bw)
    (fun x => x = SHADOW_OFF + F / 8 + 18)
    HGX HARc HAR3 Hfrs3 Hbl3 ELF3c EF eq_refl FFL ltac:(lia) ltac:(lia)); [| exact KC3 | exact KR4 | exact GA4].
  intros a Ha. right. left. cbv beta in Ha. subst a. unfold dkg_nf. right. left.
  change (fs_frame_bytes TICK_CID / 8) with 256. lia. }
pmkst HS3.
sn_regB HS3 (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) F2 ltac:(tka_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 2)))).
sn_regB HS3 (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) F3 ltac:(tka_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 3)))).
sn_regB HS3 (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) F4 ltac:(tka_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 4)))).
sn_regB HS3 (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) F8 ltac:(tka_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 8)))).
sn_regB HS3 (Z_to_bv 5 9) (YK11.getr regs3 (Z_to_bv 5 9)) F9 ltac:(tka_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 9)))).
sn_regB HS3 (Z_to_bv 5 18) (YK11.getr regs3 (Z_to_bv 5 18)) F18
  ltac:(tka_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 18)))).
sn_regB HS3 (Z_to_bv 5 27) (YK11.getr regs3 (Z_to_bv 5 27)) F27
  ltac:(tka_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 27)))).
sn_regB HS3 (Z_to_bv 5 26) (YK11.getr regs3 (Z_to_bv 5 10)) F26
  ltac:(tka_rv EE3 (@eq_refl _ (YK11.getr regs3 (Z_to_bv 5 10)))).
(* the bytes the epilogue reads: the saved words above sp1 and the frame's last word *)
pose proof HK3 as (K31 & _ & _ & K34 & _).
assert (KSTK : forall a, sp1 + 64 <= a < spZ regs ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite KR4 by (unfold SHADOW_OFF in *; lia). rewrite USPC in K31. rewrite K31 by lia.
  rewrite KRC by (unfold tka_Zc, TICK_S, TB_g_s in *; lia). apply KR; [lia|]. unfold tka_Z, SHADOW_OFF in *. lia. }
assert (KFL : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) (ms_mem ms4) (F + 2040 + i) = aview segs (w_H W2) mem2 (F + 2040 + i)).
{ intros i Hi. assert (HSHF : SHADOW_OFF + F / 8 + 256 <= F \/ F + 2048 <= SHADOW_OFF + F / 8).
  { unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
      [right | left]; unfold SHADOW_OFF; lia. }
  rewrite KR4 by (unfold SHADOW_OFF in *; lia).
  transitivity (aview segs (w_H W2) (ms_mem ms) (F + 2040 + i)).
  { apply (K34 TICK_CID pos (F + 2040 + i) Hin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF2. change (fs_frame_bytes TICK_CID) with 2048. lia.
    - intros Hw. apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 TICK_CID pos (F + 2040 + i) HAR2 Hin);
        [rewrite EF2; change (fs_frame_bytes TICK_CID) with 2048; lia|].
      exact (trans_g_img _ (tick_wr_G Bw _ (tka_sdwr_tick Bw _ Hw))). }
  rewrite KRC by (unfold tka_Zc, TICK_S, TB_g_s, TW.SZ_g_s in *; lia). apply KR; [lia|].
  unfold tka_Z, SHADOW_OFF in *. lia. }
assert (HSo : forall o, In o TICK_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold TCK.TICK_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
apply (EPI LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ly3 S3 W3
  (ms_mem ms4) md5 0 (ms_regs ms4) HFIX).
- split; [|split].
  + split; [replace (k + 0) with (k + 0 + 0) by lia; exact HJ3|].
    split; [unfold TICK_EV; lia|].
    split; [exact Hfrs3|].
    split; [exact (Permutation_trans Hperm3 Hperm)|].
    split; [exact ELF3c|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
    split; [exact KC4|].
    split.
    * rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia.
    * transitivity (rdword (aview segs (w_H W2) mem2) (F + 2048 - 8)); [|exact HFLw].
      unfold TCK.TICK_FBYTES. replace (F + 2048 - 8) with (F + 2040) by lia.
      apply rdword_ext. intros i Hi. exact (KFL i Hi).
  + apply (tw_kept TMAP_B (aview segs (w_H W3) mem3)); [exact Xtw|].
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KR4; [lia | unfold SHADOW_OFF; lia].
  + exact Xgf.
- assert (CH : forall n, acallee_saved n -> YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms) (Z_to_bv 5 n))
    by (intros n Hn; exact (HP3 n Hn)).
  split; [|exact (eq_trans F26 X0)].
  split; [exact (eq_trans F2 (eq_trans (CH 2 ltac:(hnf; lia)) Q2))|].
  split; [exact (eq_trans F3 (eq_trans (CH 3 ltac:(hnf; lia)) (eq_trans Q3 (eq_sym Hgp))))|].
  split; [exact (eq_trans F4 (eq_trans (CH 4 ltac:(hnf; lia)) (eq_trans Q4 (eq_sym Htp))))|].
  split; [exact (eq_trans F8 (eq_trans (CH 8 ltac:(hnf; lia)) Q8))|].
  split; [exact (eq_trans F9 (eq_trans (CH 9 ltac:(hnf; lia)) Q9))|].
  split; [exact (eq_trans F18 (eq_trans (CH 18 ltac:(hnf; lia)) Q18))|].
  exact (eq_trans F27 (eq_trans (CH 27 ltac:(hnf; lia)) Q27)).
Qed.
End r.
