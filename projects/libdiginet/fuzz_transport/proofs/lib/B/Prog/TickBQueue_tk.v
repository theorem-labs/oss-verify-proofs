(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths and module names changed; 418 of its 500 lines of code are new or changed and 1128 lines of the source are left out. *)
(* TickBQueue_tk: the segment of the queue piece of diginet_session_tick's image-B walk (fuzz_transport.asan-ubsan
   0x8909c) after take returns, tq_tk : tq_f8_at -> tq_sd_at -> tq_tk_at (TickBQueue_kit.v), code +0x7dc .. +0x810 and
   +0x830 (0x89878 .. 0x898ac, 0x898cc):
     `beqz a0` +0x7dc   take's result (the 32-bit taken, sign-extended) 0 goes to +0x830 (s10 = 0) and on to +0x834
                        (tq_f8_at; the model returns DIGINET_OK at take's world);
     +0x7e0 .. +0x7e8   a3 = the result, the 4-byte load of has_display at s1 + 76 (the out cell take wrote), `beqz`:
                        0 goes to +0x814 (tq_sd_at at take's world);
     +0x7ec .. +0x810   the checked store of 1 at s + 208 (display_sent; s5 holds its shadow address, the store is
                        through s4) and the checked store of now at s + 200 (last_display_us; its address in s7, set at
                        +0x6c8), to +0x814 (tq_sd_at at the world TickBQueue_kit.v tq_dw gives; TickBQueue_kit.v
                        tq_tw_dw).
   The first two runs are from a state with one region (the word at s1 + 76); the third from a state with the word at
   s1 + 56 (now), the 12 bytes of g_s it stores and their two shadow bytes (g_s's zero shadow, trans_tick_cells). The
   run invariants (1), (4) and g_fail_next reach send_data's world by TickBQueue_kit.v tq_take_keep, tq_dw_keep and
   tq_keep_inv14. Image A's template: lib/A/Prog/TickQueue_tk.v (image A reloads s + 200 from s1 + 48; image B keeps
   it in s7).
   rule 24: proves no function (one segment of the walk of diginet_session_tick; the walk is composed at TickCutB.v
   tick_holds_of). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k YE2y AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg TickCutB TickBKit TickBQueue_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The fall-through of the has_display test (+0x7ec). *)
Definition TQ_HD : Z := AF_diginet_session_tick + 0x7ec.
(* The shadow byte of g_s's first granule; s + 200 and s + 208 have the bytes 25 and 26 after it. *)
Definition TQ_SHG : Z := 2148220616.
Lemma TQ_SHG_eq : TQ_SHG = SHADOW_OFF + TICK_S / 8.
Proof. reflexivity. Qed.

(* The state at +0x7dc: has_display (atom 32) at s1 + 76. *)
Definition TQ_TK_R : YP09.region := YP09.mkRegion (Some 9%nat) 76 80 0 0 [YP09.mkChunk 76 (YP09.CVal 4 (SOff 32 0))].
Definition TQ_TK_FACTS : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition ss_tq_tk : sstate := mkSS TQ_TK sr_atoms [TQ_TK_R] None TQ_TK_FACTS.
(* The state at +0x7ec: the word at s1 + 56 (now, atom 32), g_s's display fields (stored) and their shadow bytes;
   s4 = s, s5 = the shadow address of s + 208, s7 = s + 200, s8 = the shadow base. *)
Definition TQ_HD_W : YP09.region := YP09.mkRegion (Some 9%nat) 56 64 0 0
  [YP09.mkChunk 56 (YP09.CVal 8 (SOff 32 0))].
Definition TQ_HD_G : YP09.region :=
  YP09.mkRegion None (TICK_S + 200) (TICK_S + 212) (TICK_S + 200) (TICK_S + 212) [].
Definition TQ_HD_SH : YP09.region :=
  YP09.mkRegion None (TQ_SHG + 25) (TQ_SHG + 27) 0 0
    [YP09.mkChunk (TQ_SHG + 25) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TQ_SHG + 26) (YP09.CVal 1 (SLit 0))].
Definition TQ_HD_REGS : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF))
    (Z_to_bv 5 21) (SLit (TQ_SHG + 26))) (Z_to_bv 5 23) (SLit (TICK_S + 200)).
Definition ss_tq_hd : sstate := mkSS TQ_HD TQ_HD_REGS [TQ_HD_W; TQ_HD_G; TQ_HD_SH] None TQ_TK_FACTS.

Lemma tq_swrap32_id : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* The sign-extended 4-byte load of a value below 2 ^ 31 is the value. *)
Lemma tq_sext_small : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 v.
Proof.
  intros E n v H Hv. cbn [sv_denot]. rewrite H.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
  rewrite LMem.sext_small, LMem.signed_of_extract by lia.
  rewrite unsigned_lit_small by lia. f_equal. apply tq_swrap32_id. lia.
Qed.

Section tk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition tq_tk_E (regs : bvmap 5 word) (v : Z) : env := Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 v]).

Lemma tq_tk_entry : forall (W : world segs) regs mem hd sp1,
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 0 <= hd < 256 ->
  garr8 segs (mrestrict (w_H W) mem) (sp1 + 76) (TW.zs (TW.put 4 hd)) ->
  st_ok_pi segs VAL (tq_tk_E regs hd) ss_tq_tk
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TQ_TK)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem hd sp1 R9 Hsp Hsp32 Hhd Hg.
  set (E := tq_tk_E regs hd).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn'; unfold E, tq_tk_E; apply ew_Eimg_Ereg_nat; exact Hn').
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 hd)
    by (unfold E, tq_tk_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  rewrite restrict_mkst_fx. unfold ss_tq_tk.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, TQ_TK_R.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp1 76 4 (SOff 32 0) hd);
      [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | lia |].
    exact (tq_val_of_garr8_put _ _ 4 hd Hg).
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold TQ_TK_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma tq_hd_entry0 : forall ly S (W : world segs) regs mem md now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 0 <= now < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  st_ok_pi segs VAL (tq_tk_E regs now) (mkSS TQ_HD sr_atoms [TQ_HD_W; TQ_HD_G; TQ_HD_SH] None TQ_TK_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TQ_HD)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md now sp1 HSC HAR R9 Hsp Hsp32 Hn H56.
  set (E := tq_tk_E regs now).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn'; unfold E, tq_tk_E; apply ew_Eimg_Ereg_nat; exact Hn').
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 now)
    by (unfold E, tq_tk_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (ZSH : forall j, 25 <= j < 27 -> val_mem segs (mrestrict (w_H W) mem) (TQ_SHG + j) 1 0).
  { intros j Hj. apply YE2y.val_mem1_of_aview.
    replace (TQ_SHG + j) with (FCells.shadow_addr (TICK_S + 8 * j)).
    - apply (decode_zshadow_rd B ly S W mem md TICK_S (TICK_S + TW.SZ_g_s) _ HAR); [| | | exact HSC].
      + unfold TICK_S, TB_g_s. rewrite Z.add_mod, (Z.mul_comm 8 j), Z.mod_mul by lia. reflexivity.
      + lia.
      + unfold TW.SZ_g_s. lia.
    - unfold FCells.shadow_addr, FCells.ASAN_K, TQ_SHG, TICK_S, TB_g_s.
      replace (6157888 + 8 * j) with ((769736 + j) * 8) by lia.
      rewrite Z.div_mul by lia. lia. }
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TQ_HD_W TQ_HD_G TQ_HD_SH base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 56 8 (SOff 32 0) now);
        [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | exact Hn | lia |].
      exact (val_mem_of_rdword segs (w_H W) mem _ _ H56).
    + split; [unfold TICK_S, TB_g_s; lia|]. split; [unfold TICK_S, TB_g_s; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (0 + o) G_HARNESS_B_rw).
      unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
      split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, TICK_S, TB_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
    + split; [unfold TQ_SHG; lia|]. split; [unfold TQ_SHG; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ 0 (TQ_SHG + 25) 1 (SLit 0) 0); [reflexivity | lia | unfold TQ_SHG; lia |].
        rewrite Z.add_0_l. exact (ZSH 25 ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (TQ_SHG + 26) 1 (SLit 0) 0); [reflexivity | lia | unfold TQ_SHG; lia |].
        rewrite Z.add_0_l. exact (ZSH 26 ltac:(lia)).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, TQ_HD_W, TQ_HD_G, TQ_HD_SH.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TQ_SHG, TICK_S, TB_g_s. repeat split; first [exact I | lia].
  - unfold TQ_TK_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma tq_hd_entry : forall ly S (W : world segs) regs mem md now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 0 <= now < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  YK11.getr regs 21 = w64 (TQ_SHG + 26) -> YK11.getr regs 23 = w64 (TICK_S + 200) ->
  st_ok_pi segs VAL (tq_tk_E regs now) ss_tq_hd
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TQ_HD)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md now sp1 HSC HAR R9 Hsp Hsp32 Hn H56 R20 R24 R21 R23.
  rewrite restrict_mkst_fx.
  pose proof (tq_hd_entry0 ly S W regs mem md now sp1 HSC HAR R9 Hsp Hsp32 Hn H56) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 21) (TQ_SHG + 26) H2 R21 eq_refl) as H3.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 23) (TICK_S + 200) H3 R23 eq_refl) as H4.
  exact H4.
Qed.

(* The state at +0x814 is tq_sd_at's when every byte but g_s's display fields is the one at take's return: the frame,
   the body's bytes and shadow, the window words and the saved words are not bytes of G. *)
Lemma tq_tk_to_sd : @tq_sd_at fx rc B MT -> tick_laws B MT -> tick_callees B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (Bs body X : list byte) (len n : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 memF : word -> option byte) (md2 mdF : Model) (e : Z)
         (regsF : bvmap 5 word),
    tick_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_run_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F ly2 S2 W2 mem2 md2 e ->
    @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
      ((TICK_CID, pos) :: own) ly2 S2 W2 memF mdF (k + e) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (TICK_S + 200 <= a < TICK_S + 212) ->
       aview segs (w_H W2) memF a = aview segs (w_H W2) mem2 a) ->
    (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memF a) ->
    tw_at TMAP_B (aview segs (w_H W2) memF) Bs -> TW.g_fail_next Bs <= 1 ->
    (TW.M_fly_on Bs <> 0 -> TW.M_fly_len Bs <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bs -> TW.Cmd_st Bs s = TC.PENDING -> TW.Cmd_len Bs s <= DSpec.SPEC_CMD_MAX) ->
    TSS.send_data_m timg_B TF Bs (firstn (Z.to_nat len) body) n now = Some (Bw', r) ->
    0 <= len <= TAKE_BODY -> 0 <= n < 2 ^ 32 ->
    length X = Z.to_nat TAKE_BODY -> firstn (Z.to_nat len) X = firstn (Z.to_nat len) body ->
    garr8 segs (mrestrict (w_H W2) mem2) (F + 160) (TW.zs X) ->
    rdword (aview segs (w_H W2) mem2) (sp1 + 80) = Some len ->
    (forall i, 20 <= i < 205 -> aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + i) = Some 0) ->
    aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + 205) = Some 4 ->
    tq_regs regs regsF sp1 F -> YK11.getr regsF 25 = w64 (F + 160) -> YK11.getr regsF 13 = w64 (bv_swrap 32 n) ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 (BASE + TQ_SD)) memF (YK11.seg_rom segs)) mdF)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).
Proof.
  intros SD LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F Bs body
    X len n ly2 S2 W2 mem2 memF md2 mdF e regsF HFIX HRC HJF KF GF Htw Hgf H1 H4 Hm Hlen Hn HXL HXF HG8 H80 HZ20 HZ205
    HREGS R25 R13.
  pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGNE).
  pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & EF & HF0 & HF64 & HFc & HFapp).
  pose proof HRC as (HC & Hnow56).
  pose proof HC as (HJ1 & _ & Hfr & _ & HlyF & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (tq_fix_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F HFIX)
    as (Hce0 & Hwin0 & Hspz & H47 & Hsp0a & Hsp1 & Hsp1a & HTS & HSDE & HSDT & HES).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
  unfold TICK_FBYTES in HFc, HFapp.
  assert (Hin2 : In (TICK_CID, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
  assert (EF2 : frame_addr ly2 TICK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  assert (NG : forall a, TICK_S + 200 <= a < TICK_S + 212 -> inG TG.G_HARNESS_B a).
  { intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
    split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, TICK_S, TB_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia]. }
  assert (NGF : forall a, F <= a < F + 2048 -> ~ (TICK_S + 200 <= a < TICK_S + 212)).
  { intros a Ha Hd. destruct (HGX a (NG a Hd)) as [Hi _].
    apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 TICK_CID pos a HAR2 Hin2); [|exact Hi].
    rewrite EF2. change (fs_frame_bytes TICK_CID) with 2048. lia. }
  refine (SD LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F Bs body X
    len n ly2 S2 W2 memF mdF e regsF HFIX _ Htw Hgf H1 H4 Hm Hlen Hn HXL HXF _ _ _ _ HREGS R25 R13).
  - split.
    + apply (tq_cur_step B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 mem2 md2 memF
        mdF e (fun a => TICK_S + 200 <= a < TICK_S + 212) LAWS HGX FFL HARc ltac:(lia) ltac:(lia) HC HJF EF);
        [| exact KF | exact GF].
      intros a Ha. right. right. exact (NG a Ha).
    + rewrite <- Hnow56. apply rdword_ext. intros i Hi. apply KF; [lia | unfold TICK_S, TB_g_s; lia].
  - eapply garr8_frame; [exact HG8|]. intros a Ha. unfold TW.zs in Ha. rewrite length_map, HXL in Ha.
    unfold TAKE_BODY in Ha. change (Z.of_nat (Z.to_nat 1484)) with 1484 in Ha.
    apply (mbyte_of_aview segs). apply KF; [lia | apply NGF; lia].
  - rewrite <- H80. apply rdword_ext. intros i Hi. apply KF; [lia | unfold TICK_S, TB_g_s; lia].
  - intros i Hi. rewrite KF by (unfold SHADOW_OFF, TICK_S, TB_g_s; lia). exact (HZ20 i Hi).
  - rewrite KF by (unfold SHADOW_OFF, TICK_S, TB_g_s; lia). exact HZ205.
Qed.

Lemma tq_tk_holds : @tq_f8_at fx rc B MT -> @tq_sd_at fx rc B MT -> @tq_tk_at fx rc B MT.
Proof.
unfold tq_tk_at. intros F8 SD LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw'
  pos sp1 F B0 B1 body X allow len hd n ly2 S2 W2 mem2 md2 e regs2 HFIX HRC Htw1 Hgf1 HINV HL0 HT Hm HXL HXF
  HGX8 HGL HGH HZ20 HZ205 HREGS R25 R10.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGNE).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm0 & HTF &
  Hrom & Hap & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HRC as (HC & Hnow56).
pose proof HC as (HJ1 & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R21 & R22 & R23 & R24).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (tq_fix_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F HFIX)
  as (Hce0 & Hwin0 & Hspz & H47 & Hsp0a & Hsp1 & Hsp1a & HTS & HSDE & HSDT & HES).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
unfold TICK_FBYTES in HFc, HFapp, HFL.
destruct (tq_take_out B0 allow B1 body len hd n HT) as (Rn & Rlen & Rhd).
pose proof (tq_take_keep B0 allow B1 body len hd n HL0 HT) as KT.
pose proof (tq_keep_len _ _ _ _ KT HL0) as HL1.
pose proof HINV as (I1 & _ & I4 & _).
assert (Hlen8 : rdword (aview segs (w_H W2) mem2) (sp1 + 80) = Some len)
  by (apply YF0x.val_mem_rdword; [lia | exact (tq_val_of_garr8_put _ _ 8 len HGL)]).
(* +0x7dc: `beqz a0` on take's result *)
pose proof (tq_tk_entry W2 regs2 mem2 hd sp1 R9 ltac:(lia) Hsp1a Rhd HGH) as HS.
set (E0 := tq_tk_E regs2 hd) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, tq_tk_E; apply Eimg_env).
assert (EE : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E0 n0 = YK11.getr regs2 r0)
  by (intros n0 r0 Hn0; unfold E0, tq_tk_E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew E0 32 = Z_to_bv 64 hd)
  by (unfold E0, tq_tk_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
assert (D10 : sv_denot E0 (SOff 10 0) = Z_to_bv 64 (bv_swrap 32 n))
  by (cbn [sv_denot]; rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R10).
psrr_branch_tok RUN BR HS SHOK TQ_B0.
- (* nothing taken: s10 = 0, to +0x834 *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc. change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (tq_br_eqb_s (bv_swrap 32 n) 0 ltac:(pose proof (tq_swrap32_range n); lia) ltac:(lia)) in Hc.
  rewrite (tq_swrap32_eq0 n Rn) in Hc. apply Z.eqb_eq in Hc. subst n.
  unfold tq_after_take in Hm. cbn [Z.eqb] in Hm. destruct (tick_some_inv _ _ _ _ Hm) as [<- <-].
  paj_run_to_tok RUNTO HS HJ1 SHOK TQ_B0 TQ_F8.
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
  sn_regB HS (Z_to_bv 5 26) (w64 0) Q26 ltac:(reflexivity).
  tq_kreg HS EE (Z_to_bv 5 2) 2%nat R2 Q2. tq_kreg HS EE (Z_to_bv 5 3) 3%nat R3 Q3.
  tq_kreg HS EE (Z_to_bv 5 4) 4%nat R4 Q4. tq_kreg HS EE (Z_to_bv 5 8) 8%nat R8 Q8.
  tq_kreg HS EE (Z_to_bv 5 9) 9%nat R9 Q9. tq_kreg HS EE (Z_to_bv 5 18) 18%nat R18 Q18.
  tq_kreg HS EE (Z_to_bv 5 22) 22%nat R22 Q22. tq_kreg HS EE (Z_to_bv 5 27) 27%nat R27 Q27.
  pmkst HS.
  apply (F8 LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now DLib.DIGINET_OK TF Bw B1 pos
    sp1 F ly2 S2 W2 (ms_mem ms) md1 e (ms_regs ms) HFIX).
  + split; [|split].
    * apply (tq_cur_step B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 mem2 md2
        (ms_mem ms) md1 e (fun _ => False) LAWS HGX FFL HARc ltac:(lia) ltac:(lia) HC HJ1 EF); [intros a [] | | exact GA1].
      intros a Ha _. exact (KR1 a Ha).
    * apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact Htw1|].
      intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply KR1. lia.
    * exact Hgf1.
  + refine (conj (conj Q2 (conj Q3 (conj Q4 (conj Q8 (conj Q9
      (conj Q18 Q27)))))) Q26).
  + exact Q22.
- (* something taken *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc. change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (tq_br_eqb_s (bv_swrap 32 n) 0 ltac:(pose proof (tq_swrap32_range n); lia) ltac:(lia)) in Hc.
  rewrite (tq_swrap32_eq0 n Rn) in Hc. rename Hc into Hn0.
  unfold tq_after_take in Hm. rewrite Hn0 in Hm. cbv iota in Hm.
  assert (I1' : TW.M_fly_on B1 <> 0 -> TW.M_fly_len B1 <= TC.SPEC_MAX_FRAME) by
    exact (proj1 (tq_keep_inv14 _ _ B0 B1 KT ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) I1 I4)).
  assert (I4' : forall s, 0 <= s < TW.g_ncmd B1 -> TW.Cmd_st B1 s = TC.PENDING -> TW.Cmd_len B1 s <= DSpec.SPEC_CMD_MAX) by
    exact (proj2 (tq_keep_inv14 _ _ B0 B1 KT ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) I1 I4)).
  (* +0x7e0 .. +0x7e8: a3 = the result, has_display, `beqz` *)
  paj_run_tok RUN HS HJ1 SHOK TQ_B0.
  { tq_awr_rs. apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_nil. }
  set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms1) a = aview segs (w_H W2) mem2 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b wlo whi x Hiw Hx. cbv beta.
    lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end.
    cbn [In] in Hiw. repeat (destruct Hiw as [Hiw | Hiw]; [injection Hiw as <- <- <-; cbn [base_val] in Hx; lia |]).
    destruct Hiw. }
  assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (D32 : sv_denot E0 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 hd) by (apply tq_sext_small; [exact E32 | lia]).
  psrr_branch_tok RUN BR HS SHOK TQ_B0.
  + (* has_display = 0: to +0x814 at take's world *)
    cbn [branch_taken] in Hc. rewrite D32 in Hc. change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (tq_br_eqb_s hd 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. subst hd.
    change (tq_dw B1 0 now) with B1 in Hm.
    paj_run_to_tok RUNTO HS HJ1 SHOK TQ_B0 TQ_SD.
    { tq_awr_rs. apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_nil. }
    set (md3 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md3. clear mat.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms2 end.
    assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) mem2 a).
    { intros a Ha. rewrite <- (KR1 a Ha). apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
      intros b wlo whi x Hiw Hx. cbv beta.
      lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end.
      cbn [In] in Hiw. repeat (destruct Hiw as [Hiw | Hiw]; [injection Hiw as <- <- <-; cbn [base_val] in Hx; lia |]).
      destruct Hiw. }
    assert (GA2 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
    clear HF HFr HG.
    sn_regB HS (Z_to_bv 5 13) (w64 (bv_swrap 32 n)) Q13
      ltac:(cbn [sv_denot]; rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R10).
    tq_kreg HS EE (Z_to_bv 5 2) 2%nat R2 Q2. tq_kreg HS EE (Z_to_bv 5 3) 3%nat R3 Q3.
    tq_kreg HS EE (Z_to_bv 5 4) 4%nat R4 Q4. tq_kreg HS EE (Z_to_bv 5 8) 8%nat R8 Q8.
    tq_kreg HS EE (Z_to_bv 5 9) 9%nat R9 Q9. tq_kreg HS EE (Z_to_bv 5 18) 18%nat R18 Q18.
    tq_kreg HS EE (Z_to_bv 5 27) 27%nat R27 Q27. tq_kreg HS EE (Z_to_bv 5 19) 19%nat R19 Q19.
    tq_kreg HS EE (Z_to_bv 5 20) 20%nat R20 Q20. tq_kreg HS EE (Z_to_bv 5 21) 21%nat R21 Q21.
    tq_kreg HS EE (Z_to_bv 5 22) 22%nat R22 Q22. tq_kreg HS EE (Z_to_bv 5 23) 23%nat R23 Q23.
    tq_kreg HS EE (Z_to_bv 5 24) 24%nat R24 Q24. tq_kreg HS EE (Z_to_bv 5 25) 25%nat R25 Q25.
    pmkst HS.
    apply (tq_tk_to_sd SD LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos
      sp1 F B1 body X len n ly2 S2 W2 mem2 (ms_mem ms2) md2 md3 e (ms_regs ms2) HFIX HRC HJ1
      ltac:(intros a Ha _; exact (KR2 a Ha)) GA2
      ltac:(apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact Htw1|]; intros x Hx;
            pose proof (TMAP_B_hull x Hx) as Hh; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh; apply KR2; lia)
      Hgf1 I1' I4' Hm ltac:(unfold TAKE_BODY; lia) Rn HXL HXF HGX8 Hlen8 HZ20 HZ205
      (conj (conj Q2 (conj Q3 (conj Q4 (conj Q8 (conj Q9 (conj Q18 Q27)))))) (conj Q19 (conj Q20 (conj Q21
        (conj Q22 (conj Q23 Q24)))))) Q25 Q13).
  + (* has_display <> 0: the two display stores *)
    cbn [branch_taken] in Hc. rewrite D32 in Hc. change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (tq_br_eqb_s hd 0 ltac:(lia) ltac:(lia)) in Hc. rename Hc into Hh0.
    paj_run_to_tok RUNTO HS HJ1 SHOK TQ_B0 TQ_HD.
    { tq_awr_rs. apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_nil. }
    set (md3 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md3. clear mat.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms2 end.
    assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) mem2 a).
    { intros a Ha. rewrite <- (KR1 a Ha). apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
      intros b wlo whi x Hiw Hx. cbv beta.
      lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end.
      cbn [In] in Hiw. repeat (destruct Hiw as [Hiw | Hiw]; [injection Hiw as <- <- <-; cbn [base_val] in Hx; lia |]).
      destruct Hiw. }
    assert (GA2 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
    clear HF HFr HG.
    sn_regB HS (Z_to_bv 5 13) (w64 (bv_swrap 32 n)) Q13
      ltac:(cbn [sv_denot]; rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R10).
    tq_kreg HS EE (Z_to_bv 5 2) 2%nat R2 Q2. tq_kreg HS EE (Z_to_bv 5 3) 3%nat R3 Q3.
    tq_kreg HS EE (Z_to_bv 5 4) 4%nat R4 Q4. tq_kreg HS EE (Z_to_bv 5 8) 8%nat R8 Q8.
    tq_kreg HS EE (Z_to_bv 5 9) 9%nat R9 Q9. tq_kreg HS EE (Z_to_bv 5 18) 18%nat R18 Q18.
    tq_kreg HS EE (Z_to_bv 5 27) 27%nat R27 Q27. tq_kreg HS EE (Z_to_bv 5 19) 19%nat R19 Q19.
    tq_kreg HS EE (Z_to_bv 5 20) 20%nat R20 Q20. tq_kreg HS EE (Z_to_bv 5 21) 21%nat R21 Q21.
    tq_kreg HS EE (Z_to_bv 5 22) 22%nat R22 Q22. tq_kreg HS EE (Z_to_bv 5 23) 23%nat R23 Q23.
    tq_kreg HS EE (Z_to_bv 5 24) 24%nat R24 Q24. tq_kreg HS EE (Z_to_bv 5 25) 25%nat R25 Q25.
    pmkst HS.
    clear dependent ms1. clear HS SHOK.
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR3.
    pose proof (tq_hd_entry ly2 S2 W2 (ms_regs ms2) (ms_mem ms2) md3 now sp1 HTC HAR3 Q9 ltac:(lia) Hsp1a Hnow
      ltac:(rewrite <- Hnow56; apply rdword_ext; intros i Hi; apply KR2; lia)
      Q20 Q24 Q21 Q23) as HS.
    set (E1 := tq_tk_E (ms_regs ms2) now) in HS.
    assert (HEIh : img_env VAL A_LIM E1) by (unfold E1, tq_tk_E; apply Eimg_env).
    assert (EE1 : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E1 n0 = YK11.getr (ms_regs ms2) r0)
      by (intros nn rr Hnn; unfold E1, tq_tk_E; apply ew_Eimg_Ereg_nat; exact Hnn).
    assert (E132 : ew E1 32 = Z_to_bv 64 now)
      by (unfold E1, tq_tk_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
    assert (SHOK1 : sh_ok segs (SLit 0) (@nil shent) E1 (mrestrict (w_H W2) (ms_mem ms2))) by constructor.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TQ_HD)) mm rom) mdx) Qx) end.
    (* +0x7ec .. +0x810: the checked store of 1 at s + 208, the checked store of now at s + 200 *)
    paj_run_to_tok RUNTO HS HJ1 SHOK1 TQ_B0 TQ_SD.
    { tq_awr_rs.
      apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_cons_g;
        [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
         unfold inG; apply Exists_exists; exists (TB_g_s, TW.SZ_g_s);
         split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, TICK_S, TB_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia] |].
      apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_nil. }
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms3 end.
    assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (TICK_S + 200 <= a < TICK_S + 212) ->
      aview segs (w_H W2) (ms_mem ms3) a = aview segs (w_H W2) mem2 a).
    { intros a Ha Hn. rewrite <- (KR2 a Ha).
      apply (kept_of_frame _ _ _ _ _ (fun x => TICK_S + 200 <= x < TICK_S + 212) HFr); [| exact Ha | exact Hn].
      intros b wlo whi x Hiw Hx. cbv beta.
      lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end.
      cbn [In] in Hiw.
      repeat (destruct Hiw as [Hiw | Hiw];
        [injection Hiw as <- <- <-; cbn [base_val] in Hx; unfold TICK_S, TB_g_s; first [lia | idtac] |]).
      destruct Hiw. }
    assert (GA3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms3) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
    pose proof (sn_chunk_valB E1 (w_H W2) (ms_mem ms3) _ _ _ _ _ _ (TICK_S + 208) 4 (SLit 1) RG
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VD.
    pose proof (sn_chunk_valB E1 (w_H W2) (ms_mem ms3) _ _ _ _ _ _ (TICK_S + 200) 8 (SOff 32 0) RG
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VL.
    cbn [base_val] in VD, VL. rewrite Z.add_0_l in VD, VL.
    change (bv_unsigned (sv_denot E1 (SLit 1)) mod 2 ^ (8 * Z.of_N 4)) with 1 in VD.
    assert (DN : sv_denot E1 (SOff 32 0) = Z_to_bv 64 now)
      by (cbn [sv_denot]; rewrite E132, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
    rewrite DN, unsigned_lit_small, (Z.mod_small now) in VL by (cbn; lia).
    change (N.to_nat 4) with 4%nat in VD. change (N.to_nat 8) with 8%nat in VL.
    assert (HtwD : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms3)) (tq_dw B1 hd now)).
    { unfold tq_dw. rewrite Hh0.
      apply (tq_tw_dw (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms3)) B1 now Htw1).
      - intros j Hj. exact (tq_aview_of_val _ _ _ 4 1 j VD Hj).
      - intros j Hj. exact (tq_aview_of_val _ _ _ 8 now j VL Hj).
      - intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
        apply KR3; [lia | exact Hn]. }
    pose proof (tq_dw_keep B1 hd now HL1) as KD.
    tq_kreg HS EE1 (Z_to_bv 5 2) 2%nat Q2 T2. tq_kreg HS EE1 (Z_to_bv 5 3) 3%nat Q3 T3.
    tq_kreg HS EE1 (Z_to_bv 5 4) 4%nat Q4 T4. tq_kreg HS EE1 (Z_to_bv 5 8) 8%nat Q8 T8.
    tq_kreg HS EE1 (Z_to_bv 5 9) 9%nat Q9 T9. tq_kreg HS EE1 (Z_to_bv 5 18) 18%nat Q18 T18.
    tq_kreg HS EE1 (Z_to_bv 5 27) 27%nat Q27 T27. tq_kreg HS EE1 (Z_to_bv 5 19) 19%nat Q19 T19.
    sn_regB HS (Z_to_bv 5 20) (w64 TICK_S) T20 ltac:(reflexivity).
    sn_regB HS (Z_to_bv 5 21) (w64 (SHADOW_OFF + (TICK_S + 208) / 8)) T21 ltac:(reflexivity).
    tq_kreg HS EE1 (Z_to_bv 5 22) 22%nat Q22 T22.
    sn_regB HS (Z_to_bv 5 23) (w64 (TICK_S + 200)) T23 ltac:(reflexivity).
    sn_regB HS (Z_to_bv 5 24) (w64 SHADOW_OFF) T24 ltac:(reflexivity).
    tq_kreg HS EE1 (Z_to_bv 5 25) 25%nat Q25 T25. tq_kreg HS EE1 (Z_to_bv 5 13) 13%nat Q13 T13.
    pmkst HS.
    apply (tq_tk_to_sd SD LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos
      sp1 F (tq_dw B1 hd now) body X len n ly2 S2 W2 mem2 (ms_mem ms3) md2 md4 e (ms_regs ms3) HFIX HRC HJ1 KR3 GA3
      HtwD ltac:(rewrite (tq_keep_gfn _ _ _ _ KD ltac:(vm_compute; discriminate)); exact Hgf1)
      (proj1 (tq_keep_inv14 _ _ B1 _ KD ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) I1' I4'))
      (proj2 (tq_keep_inv14 _ _ B1 _ KD ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) I1' I4'))
      Hm ltac:(unfold TAKE_BODY; lia) Rn HXL HXF HGX8 Hlen8 HZ20 HZ205
      (conj (conj T2 (conj T3 (conj T4 (conj T8 (conj T9 (conj T18 T27)))))) (conj T19 (conj T20 (conj T21
        (conj T22 (conj T23 T24)))))) T25 T13).
Qed.
End tk.
