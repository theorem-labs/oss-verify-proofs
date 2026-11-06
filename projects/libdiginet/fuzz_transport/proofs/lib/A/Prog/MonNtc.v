(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1878 of its 1989 lines of code are new or changed and 815 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/io_send_seg_tail.v, with its module names changed; 697 of its 784 lines of code are new or changed and 1902 lines of the source are left out. *)
(* MonNtc: Lemma mon_ntc : mon_ntc_stmt (lib/A/Prog/MonCut.v), the notice piece of the image-A walk of maybe_online,
   offsets +0x1d4 .. +0x28c of the listing lib/A/Prog/DgnTransportList.v (fuzz_transport.asan 0x8b344 .. 0x8b3fc), then
   the release cut (mon_rel_at, a premise).

   What the code does. +0x1d4 .. +0x1f4: the frame's shadow bytes 4 .. 12 := 0 (s6 = SHADOW_OFF + F / 8, nine
   `sb zero`); a0 = p + 16, a2 = 56, a1 = 0 and `jal __asan_memset` at +0x204 (return +0x208): the notice's bytes
   16 .. 71 := 0. +0x208 .. +0x21c: the 8 bytes 0x0000000200000002 at p and 0x0000000200000001 at p + 8 (s5 = p =
   F + 32). +0x220 .. +0x230: the shadow byte of s + 112 (s9) read, 0, so `bnez` falls through; the store of 2 at
   s + 112 (s3 = s = &g_s): the world is maybeon_w2 Bw. +0x234 .. +0x254: the checks of the 8-byte loads at s + 96
   and s + 104; +0x258 .. +0x260: a2 = the notify pointer (S_notify, which the model's call_notify tests against
   TI.ti_notice timg_A), a0 = notify_ctx, a1 = p; +0x264 `jalr a2`: notice, return +0x268. +0x268 .. +0x28c: the
   shadow bytes 4 .. 12 := 0xf8; +0x290 is the release cut.

   Three runs of the token engine over the caller's G journal (lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x):
     run 1 (+0x1d4 .. the call of __asan_memset) and run 3 (+0x268 .. +0x290): one writable region, the frame's
       shadow bytes 4 .. 12 at s6 (no shadow token: the span (0, 0) and a fact placing s6 above 0);
     run 2 (+0x208 .. the `jalr`): the notice's first 16 bytes at s5 (writable), the shadow byte of s + 112 at s9
       (its value 0, decode_zshadow_rd from trans_maybeon_cells), g_s's bytes [s + 96, s + 116) at s3 (the two loaded
       words as atoms 32 and 33, read off the world maybeon_w1 Bw by TWorldG.v tw_read_val; [s + 112, s + 116)
       writable, bytes of G); the shadow entries [s + 96, s + 112) (the two 8-byte checks, decided by the record's zero
       shadow of g_s) and [p, p + 16) (its shadow bytes 4, 5 are 0 since run 1).
   __asan_memset: TransportGCg.v gx_intrin_at (the destination is the own frame, its shadow bytes 6 .. 12 are 0, its
   hull lies in the frame's shadow). The `jalr`: DgnTransportPaLib.v SRr_jalr_call_pi at the target TI.ti_notice
   timg_A. notice: notice_cg.v transport_notice_cg at TI.ti_notice timg_A (a premise), applied in the same G journal:
     the journal at the call (the own frame owned), ra = +0x268, gp, tp, a1 = p, sp = sp1 (32-aligned; MAYBEON_STK =
     112 + NOTICE_STK and sp1 >= sp - 112);
     trans_ntc_at p (maybeon_ntc Bw): FAKE (the 72 bytes lie in the own frame; decode_rd_ok from its presence, its
     shadow bytes 4 .. 12 = 0 and its present shadow), the bytes MON_NB (run 2's two words and the memset's zeros),
     whose fields are maybeon_ntc's (old = S_state (maybeon_w1 Bw) = S_WAKING), body NULL with length 0
     (trans_src_ok_null), announce NULL;
     trans_tframe_at TF at NOTICE_STK: the cut's facts carried (TransportGNotice.v trans_tframe_at_kept_gx: TF's bytes miss
     maybeon_wr Bw by maybeon_apart);
     trans_rom_view_rd: the TRANS_RO_RD bytes are kept (acall_kept_g's image clause; trans_ro_rd_unowned,
     trans_rom_no_errno);
     tw_at at maybeon_w2 Bw (TWorldG.v tw_write of the store at s + 112); notice_m ... = Some (Bw', tt) and S_notify =
     TI.ti_notice timg_A (maybe_online_cg.v maybeon_model, this path's branch: mon_model_ntc);
     notice_apart (notice_wr is G, the struct is in the own frame; maybeon_apart); the N_DATA premise vacuous (kind
     N_STATE); no event.
   The release cut's state (mon_rel_cur at notice's post state): the journal, frames and blocks of notice's post;
   ly_F from the journal's layout_le; the meter by mo_le_trans; acall_kept_g from the cut's by TransportGFrame.v
   dk_kept_nfz_gw (the runs and the memset change the window, the own frame and s + 112), TransportGCg.v
   dk_kept_trans_nf_g (notice's post: its written range notice_wr is in maybeon_wr Bw on this path) and dk_kept_nfz_gw
   again (run 3); the saved words and the frame's last word kept (they lie in maybe_online's window above notice's,
   and in the own frame outside notice_wr); tw_at at Bw' (notice's post, kept by run 3); g_fail_next Bw' <= 1
   (mon_gfn: notice and the two g_s stores leave the byte). The registers the release reads: callee-saved through the
   runs, the memset, the `jalr` (ra only) and notice. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AE2y AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg maybe_online_cg MonCut TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_config_default.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TSess TImg TWorldLemmas TSessFacts.
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
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model on this path                                           *)
(* ------------------------------------------------------------------ *)

(* The worlds after the two g_s stores, their lengths, the notify pointer of maybeon_w2 Bw, the model's notice on this
   path (maybeon_go Bw and the state S_WAKING, not S_ONLINE: maybeon_model's call_notify), and g_fail_next. *)
Lemma mon_w2_eq : forall Bw, maybeon_w2 Bw = TW.upd (maybeon_w1 Bw) (TW.OFF_g_s + 112) (TW.put 4 2).
Proof. intros Bw. reflexivity. Qed.
Lemma mon_w1_eq : forall Bw, maybeon_w1 Bw =
  TW.upd Bw (TW.OFF_g_s + 184) (TW.put 8 (TS0.u64 (TW.S_last_rx_us Bw + TS0.ms_m (TW.S_cfg_keepalive_ms Bw)))).
Proof. intros Bw. reflexivity. Qed.
Lemma mon_w1_len : forall Bw, length Bw = Z.to_nat TW.W_LEN -> length (maybeon_w1 Bw) = Z.to_nat TW.W_LEN.
Proof.
intros Bw HL. rewrite mon_w1_eq, TWL.length_upd_put; [exact HL | unfold TW.OFF_g_s; lia |].
rewrite HL. unfold TW.OFF_g_s, TW.W_LEN. lia.
Qed.
Lemma mon_w2_len : forall Bw, length Bw = Z.to_nat TW.W_LEN -> length (maybeon_w2 Bw) = Z.to_nat TW.W_LEN.
Proof.
intros Bw HL. pose proof (mon_w1_len Bw HL) as H1. rewrite mon_w2_eq, TWL.length_upd_put; [exact H1 | unfold TW.OFF_g_s; lia |].
rewrite H1. unfold TW.OFF_g_s, TW.W_LEN. lia.
Qed.
Lemma mon_notify_w2 : forall Bw, length Bw = Z.to_nat TW.W_LEN ->
  TW.S_notify (maybeon_w2 Bw) = TW.u_at (maybeon_w1 Bw) (TW.OFF_g_s + 96) 8.
Proof.
intros Bw HL. pose proof (mon_w1_len Bw HL) as H1. rewrite mon_w2_eq. unfold TW.S_notify, TW.A_S_notify.
apply TWL.u_at_upd_out; [unfold TW.OFF_g_s; lia | unfold TW.OFF_g_s; lia | |].
- rewrite TWL.length_put. left. unfold TW.OFF_g_s. lia.
- rewrite TWL.length_put, H1. unfold TW.OFF_g_s, TW.W_LEN. lia.
Qed.
Lemma mon_model_ntc : forall TF Bw Bw',
  maybeon_go Bw = true -> TW.S_state (maybeon_w1 Bw) = TS0.DIGINET_S_WAKING ->
  TSS.maybe_online_m timg_A TF Bw = Some (Bw', tt) ->
  TW.S_notify (maybeon_w2 Bw) = TI.ti_notice timg_A /\
  TC.notice_m timg_A TF (maybeon_w2 Bw) (maybeon_ntc Bw) = Some (Bw', tt).
Proof.
intros TF Bw Bw' Hgo Hst Hm. rewrite maybeon_model, Hgo, Hst in Hm. cbv beta iota in Hm.
change (TS0.DIGINET_S_WAKING =? TS0.DIGINET_S_ONLINE) with false in Hm. cbv beta iota in Hm.
unfold TSS.call_notify in Hm.
destruct (Z.eqb_spec (TW.S_notify (maybeon_w2 Bw)) (TI.ti_notice timg_A)) as [E|E];
  [split; [exact E | exact Hm] | discriminate Hm].
Qed.
Lemma mon_gfn : forall TF Bw Bw', length Bw = Z.to_nat TW.W_LEN -> TW.g_fail_next Bw <= 1 ->
  TC.notice_m timg_A TF (maybeon_w2 Bw) (maybeon_ntc Bw) = Some (Bw', tt) -> TW.g_fail_next Bw' <= 1.
Proof.
intros TF Bw Bw' HL Hg Hn.
assert (G1 : TSessFacts.tsf_gf (TW.g_fail_next Bw) (maybeon_w1 Bw)).
{ rewrite mon_w1_eq. apply TSessFacts.tsf_gf_upd; [split; [exact HL | reflexivity] | unfold TW.OFF_g_s; lia | |];
  rewrite TWL.length_put; unfold TW.OFF_g_s, TW.OFF_g_fail_next, TW.W_LEN; lia. }
assert (G2 : TSessFacts.tsf_gf (TW.g_fail_next Bw) (maybeon_w2 Bw)).
{ rewrite mon_w2_eq. apply TSessFacts.tsf_gf_upd; [exact G1 | unfold TW.OFF_g_s; lia | |];
  rewrite TWL.length_put; unfold TW.OFF_g_s, TW.OFF_g_fail_next, TW.W_LEN; lia. }
destruct G2 as [L2 E2].
rewrite (TSessFacts.notice_m_fail_next timg_A TF (maybeon_w2 Bw) (maybeon_ntc Bw) Bw' L2 Hn), E2. exact Hg.
Qed.

(* The notice's 72 bytes after run 2 (maybeon_ntc Bw on this path, as trans_ntc_at reads them). *)
Definition MON_NBZ : list Z := [2; 0; 0; 0; 2; 0; 0; 0; 1; 0; 0; 0; 2; 0; 0; 0] ++ repeat 0 56.
Definition MON_NB : list byte := map (Z_to_bv 8) MON_NBZ.


(* ------------------------------------------------------------------ *)
(* 2. The three symbolic states                                        *)
(* ------------------------------------------------------------------ *)

(* The return addresses of __asan_memset (+0x208) and of notice (+0x268). *)
Definition MON_RET1 : Z := AF_maybe_online + 0x208.
Definition MON_RET2 : Z := AF_maybe_online + 0x268.
(* Runs 1 and 3: no shadow token (the span (0, 0)); their region is the frame's shadow bytes 4 .. 12 at s6 = atom 22,
   placed above the span by a fact. *)
Definition mon_B0 : Z * Z := (0, 0).
Definition mon_rg_sh : YP09.region := YP09.mkRegion (Some 22%nat) 4 13 4 13 [].
Definition mon_facts_sh : facts := mkFacts [(22%nat, mkAF SHADOW_OFF (2 ^ 47) 0)] [] [].
(* Run 2: the notice's first 16 bytes at s5 = atom 21, the shadow byte of s + 112 at s9 = atom 25 (value 0), g_s's
   bytes [s + 96, s + 116) at s3 = atom 19 (the loaded words as atoms 32, 33; [s + 112, s + 116) written); the facts
   s3 = s, s5 in [4096, 2 ^ 47 - 64) 32-aligned, s8 = atom 24 = SHADOW_OFF (the shadow base of the tokens); the shadow
   entries [s + 96, s + 112) and [p, p + 16). *)
Definition mon_rg_p : YP09.region := YP09.mkRegion (Some 21%nat) 0 16 0 16 [].
Definition mon_rg_s9 : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition mon_rg_s : YP09.region := YP09.mkRegion (Some 19%nat) 96 116 112 116
  [YP09.mkChunk 96 (CVal 8 (SOff 32 0)); YP09.mkChunk 104 (CVal 8 (SOff 33 0))].
Definition mon_facts2 : facts :=
  mkFacts [(19%nat, mkAF MAYBEON_S MAYBEON_S 4); (21%nat, mkAF 4096 (2 ^ 47 - 64) 5);
           (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_n2 : sstate := mkSS MON_RET1 sr_atoms [mon_rg_p; mon_rg_s9; mon_rg_s] None mon_facts2.
Definition MON_SH2 : list shent := [mkSHE 19 96 112; mkSHE 21 0 16].
Definition MON_BX : sv := SOff 24 0.

Section ntc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition mon_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transport) (Ereg regs extra).

Lemma mon_ew : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (mon_E regs extra) n = YK11.getr regs r.
Proof. intros regs extra n r Hn. unfold mon_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma mon_ew_x : forall regs extra j, (j < 8)%nat -> ew (mon_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. unfold mon_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* The frame's shadow bytes 4 .. 12 as a writable region at s6 (runs 1 and 3). *)
Lemma mon_sh_entry : forall (W : world segs) regs mem F pc,
  YK11.getr regs 22 = w64 (SHADOW_OFF + F / 8) -> 0 <= F < 2 ^ 47 ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (mon_E regs []) (mkSS pc sr_atoms [mon_rg_sh] None mon_facts_sh)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F pc R22 HF Hp.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8.
pose proof (Z.div_lt_upper_bound F 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as HF8'.
assert (U22 : bv_unsigned (ew (mon_E regs []) 22) = SHADOW_OFF + F / 8).
{ rewrite (mon_ew regs [] 22 22%bv eq_refl), R22. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold mon_rg_sh, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U22.
  split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable segs). apply Hp. lia.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold mon_facts_sh, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.
End ntc.

Section ntc2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The symbolic state at +0x208 holds of the machine state there. *)
Lemma mon_n2_entry : forall (W : world segs) regs mem F v96 v104,
  YK11.getr regs 19 = w64 MAYBEON_S -> YK11.getr regs 21 = w64 (F + 32) -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  YK11.getr regs 25 = w64 (SHADOW_OFF + (MAYBEON_S + 112) / 8) ->
  4096 <= F + 32 <= 2 ^ 47 - 64 -> (F + 32) mod 32 = 0 ->
  (F + 48 <= MAYBEON_S + 96 \/ MAYBEON_S + 116 <= F + 32) ->
  (F + 48 <= SHADOW_OFF + (MAYBEON_S + 112) / 8 \/ SHADOW_OFF + (MAYBEON_S + 112) / 8 + 1 <= F + 32) ->
  (forall a, F + 32 <= a < F + 48 -> apresent (w_H W) mem a) ->
  aview segs (w_H W) mem (SHADOW_OFF + (MAYBEON_S + 112) / 8) = Some 0 ->
  val_mem segs (mrestrict (w_H W) mem) (MAYBEON_S + 96) 8 v96 -> 0 <= v96 < 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W) mem) (MAYBEON_S + 104) 8 v104 -> 0 <= v104 < 2 ^ 64 ->
  st_ok_pi segs VAL (mon_E regs [w64 v96; w64 v104]) ss_n2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + MON_RET1)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F v96 v104 R19 R21 R24 R25 HF HF32 HD1 HD2 Hpf Hs9 Hv96 Hr96 Hv104 Hr104.
set (E := mon_E regs [w64 v96; w64 v104]).
assert (ES : MAYBEON_S = 6158784) by reflexivity.
assert (E9 : SHADOW_OFF + (MAYBEON_S + 112) / 8 = 2148220742) by reflexivity.
rewrite E9 in R25, HD2, Hs9.
assert (U19 : bv_unsigned (ew E 19) = MAYBEON_S).
{ unfold E. rewrite (mon_ew regs _ 19 19%bv eq_refl), R19. unfold w64. apply unsigned_lit_small. rewrite ES. lia. }
assert (U21 : bv_unsigned (ew E 21) = F + 32).
{ unfold E. rewrite (mon_ew regs _ 21 21%bv eq_refl), R21. unfold w64. apply unsigned_lit_small. lia. }
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF).
{ unfold E. rewrite (mon_ew regs _ 24 24%bv eq_refl), R24. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (U25 : bv_unsigned (ew E 25) = 2148220742).
{ unfold E. rewrite (mon_ew regs _ 25 25%bv eq_refl), R25. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = w64 v96) by exact (mon_ew_x regs _ 0 ltac:(lia)).
assert (E33 : ew E 33 = w64 v104) by exact (mon_ew_x regs _ 1 ltac:(lia)).
rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks mon_rg_p mon_rg_s9 mon_rg_s base_val];
    rewrite ?U19, ?U21, ?U25.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ 2148220742 0 1 (SLit 0) 0); [reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (AE2y.val_mem1_of_aview _ _ _ _ Hs9).
  + rewrite ES in *. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS _ G_HARNESS_rw). unfold inG, TG.G_HARNESS.
      apply Exists_exists. exists (6158784, 18264). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia]. }
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val segs E _ 6158784 96 8 (SOff 32 0) v96);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | exact Hr96 | lia |].
      exact Hv96.
    * apply (chunk_ok_val segs E _ 6158784 104 8 (SOff 33 0) v104);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | exact Hr104 | lia |].
      exact Hv104.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, mon_rg_p, mon_rg_s9, mon_rg_s.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U19, U21, U25. rewrite ES in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold mon_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, U21, U24. rewrite Z.pow_0_r, Z.mod_1_r.
  change (2 ^ 4) with 16. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite ES; reflexivity | unfold SHADOW_OFF; lia].
Qed.
End ntc2.

Section ntc3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
(* Run 2's two shadow entries hold. *)
Lemma mon_n2_shok : forall (W : world segs) regs mem F extra,
  YK11.getr regs 19 = w64 MAYBEON_S -> YK11.getr regs 21 = w64 (F + 32) -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  4096 <= F + 32 -> F + 48 <= 2 ^ 47 -> (F + 48 <= SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= F + 32) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (MAYBEON_S + 96) 16 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (F + 32) 16 ->
  sh_ok segs MON_BX MON_SH2 (mon_E regs extra) (mrestrict (w_H W) mem).
Proof.
intros W regs mem F extra R19 R21 R24 HF1 HF2 HF3 HRA1 HRA2.
assert (ES : MAYBEON_S = 6158784) by reflexivity.
assert (UB : U (mon_E regs extra) MON_BX = SHADOW_OFF).
{ unfold U, MON_BX. cbn [sv_denot]. rewrite (mon_ew regs extra 24 24%bv eq_refl), R24, Z.add_0_r.
  unfold w64. rewrite Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
unfold sh_ok, MON_SH2. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range segs (w_H W) mem _ MON_BX 19 (MAYBEON_S + 96) 16 MAYBEON_S 96 112 HRA1 UB).
  + unfold U. cbn [sv_denot]. rewrite (mon_ew regs extra 19 19%bv eq_refl), R19, Z.add_0_r.
    unfold w64. rewrite Z_to_bv_bv_unsigned. apply unsigned_lit_small. rewrite ES. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. rewrite ES in Hx. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range segs (w_H W) mem _ MON_BX 21 (F + 32) 16 (F + 32) 0 16 HRA2 UB).
  + unfold U. cbn [sv_denot]. rewrite (mon_ew regs extra 21 21%bv eq_refl), R21, Z.add_0_r.
    unfold w64. rewrite Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. lia.
Qed.
End ntc3.

(* Every byte maybe_online stores into G is a byte of G. *)
Lemma mon_wr_G : forall Bw a, maybeon_wr Bw a -> inG TG.G_HARNESS a.
Proof.
intros Bw a (_ & [Ha | (_ & [Ha | Ha])]); [| | exact (notice_wr_G _ _ a Ha)];
  unfold twa_fld, TW.A_S_next_keepalive_us, TW.A_S_state, TW.OFF_g_s, TA_g_s in Ha;
  unfold inG, TG.G_HARNESS; apply Exists_exists; exists (6158784, 18264);
  (split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia]).
Qed.


(* ------------------------------------------------------------------ *)
(* 3. The piece                                                        *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac mon_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mon_reg: no match for" T; fail
  end.

Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma mon_ntc : @mon_ntc_stmt fx rc B MT.
Proof.
unfold mon_ntc_stmt, mon_ntc_at.
intros REL LAWS0 HAI HNTC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw Bw' pos sp1 F S2 mem2 md2
  regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (Hsm & HCELLS & HMBC & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & H10 & Hsp16 & Hwin1 & Hwin2 & Htw0 & Hgf & Hm & HTF & Hrom & Hapart &
  Hcnt & Hnev & Esp1 & EF & HF4096 & HF64 & HFce & HFapp).
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK1 & Hsaved & HFLw) & Ebl & HGK1 & Htw1 & Hgo & Hst).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R22 & R23 & R26 & R27) & R19 & R20 & R21 & R24 & R25).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold MON_FBYTES in HFce, HFapp, HFLw.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
assert (EST : ESTACK = 4096) by reflexivity.
assert (EMS : MAYBEON_STK = 8352) by reflexivity.
assert (ENS : NOTICE_STK = 8240) by reflexivity.
assert (ES : MAYBEON_S = 6158784) by reflexivity.
(* the realigned sp1 *)
assert (Hsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold MAYBEON_FRAME.
  pose proof (Z.div_mod (spZ regs - 96) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (spZ regs - 96) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 96) / 32) in *. set (r := (spZ regs - 96) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult. }
destruct Hsp1 as [Hsp1 Hsp132].
(* the own frame *)
assert (Hin2 : In (MAYBEON_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ MAYBEON_CID pos HAR2 Hin2) as (_ & _ & HFb & HFsh).
change (fs_frame_bytes MAYBEON_CID / 8) with 32 in HFsh. change (fs_frame_bytes MAYBEON_CID) with 256 in HFb.
rewrite <- EF in HFb, HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity. rewrite ESH in HFsh.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z_mod_mult. }
assert (HFlo : F + 256 <= kLowShadowBeg \/ kHighMemBeg <= F).
{ destruct HFapp as (_ & [HL | [HH _]]); [left; exact HL | right; exact HH]. }
unfold kLowShadowBeg, kHighMemBeg in HFlo.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8p.
pose proof (Z.div_lt_upper_bound F 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as HF8u.
set (s6 := SHADOW_OFF + F / 8) in *.
(* run 1, +0x1d4 .. +0x204: shadow bytes 4 .. 12 := 0, the memset's arguments, jal __asan_memset *)
pose proof (mon_sh_entry W regs2 mem2 F MON_NTC R22 ltac:(lia) ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia)))))
  as HS.
assert (SHOK : sh_ok segs MON_BX [] (mon_E regs2 []) (mrestrict (w_H W) mem2)) by constructor.
assert (HEI : img_env VAL A_LIM (mon_E regs2 [])) by (unfold mon_E; apply Eimg_env).
assert (U22 : bv_unsigned (ew (mon_E regs2 []) 22) = s6).
{ rewrite (mon_ew regs2 [] 22 22%bv eq_refl), R22. unfold w64. apply unsigned_lit_small. unfold s6, SHADOW_OFF. lia. }
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ1 SHOK mon_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ MAYBEON_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
  right. unfold in_zr. cbn [fst snd]. rewrite <- EF, ESH. change (fs_frame_bytes MAYBEON_CID / 8) with 32. unfold s6 in Ha. lia. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.

assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s6 + 4 <= a < s6 + 13) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ _ _ _ (fun x => s6 + 4 <= x < s6 + 13) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta.
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end.
  cbn [In] in Hin. destruct Hin as [Hin | []]. injection Hin as <- <- <-. cbn [base_val] in Hx. rewrite U22 in Hx. lia. }
assert (GA1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
destruct RG1 as (_ & _ & _ & HCH1). cbn [base_val YP09.r_base YP09.r_chunks] in HCH1. rewrite U22 in HCH1.
assert (Z1 : forall i, 4 <= i < 13 -> aview segs (w_H W) (ms_mem ms) (s6 + i) = Some 0).
{ intros i Hi. apply (chunks_zero_aview _ _ _ _ _ i HCH1).
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  repeat (destruct Hi' as [-> | Hi']; [cbn [In]; tauto |]). subst i. cbn [In]. tauto. }
clear HF HFr HG HCH1.
assert (HAG : env_agree 32 (Ereg regs2 []) (mon_E regs2 []))
  by (split; [intros n Hn; unfold mon_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HP1 : aregs_preserved regs2 (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok segs (w_H W) _ _ ms regs2 [] HS HAG); vm_compute; reflexivity).
pmkst HS.
mon_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 48)) Q10
  ltac:(cbn [sv_denot]; rewrite (mon_ew regs2 [] 21 21%bv eq_refl), R21; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia).
mon_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
mon_reg HS (Z_to_bv 5 12) (Z_to_bv 64 56) Q12 ltac:(reflexivity).
mon_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + MON_RET1)) Q1 ltac:(apply codeptr_val; exact HEI).
assert (Q2 : YK11.getr (ms_regs ms) 2 = w64 sp1) by exact (eq_trans (HP1 2 ltac:(hnf; lia)) R2).
assert (Q3 : YK11.getr (ms_regs ms) 3 = w64 (as_gp B)) by exact (eq_trans (eq_trans (HP1 3 ltac:(hnf; lia)) R3) Hgp).
assert (Q4 : YK11.getr (ms_regs ms) 4 = w64 (as_tp B)) by exact (eq_trans (eq_trans (HP1 4 ltac:(hnf; lia)) R4) Htp).
assert (Hspm : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
(* +0x204: __asan_memset (p + 16, 0, 56), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (HAI fx) TG.G_HARNESS W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 ((MAYBEON_CID, pos) :: own) lyc S2 md1
    (k + 0) (F + 48) 0 56 (sp1 - sp0) (Z_to_bv 64 (BASE + MON_RET1)) HGX G_HARNESS_rw HJ1 Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite Hspm. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. rewrite Hsp132, Z.add_0_r in D1.
    pose proof (Z.div_mod sp0 16 ltac:(lia)) as D0. rewrite Hsp0a, Z.add_0_r in D0.
    replace (sp1 - sp0) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - rewrite EST. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold MON_RET1, AF_maybe_online; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|]. intros a Ha. left. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists MAYBEON_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes MAYBEON_CID) with 256. lia.
    + rewrite Hspm, EST. lia.
  - unfold amem_range. destruct HFlo as [HL | HH]; [left; lia | right; lia].
  - apply (frame_ra_zero _ F (F + 48) 56 6 13); [lia | exact HF8 | lia | lia |].
    intros i Hi. exact (Z1 i ltac:(lia)).
  - intros _. apply (frame_hull_vis _ F 256 (F + 48) 56); [lia | exact HF64 | reflexivity | lia | lia | lia |].
    intros i Hi. change (256 / 8) with 32 in Hi. rewrite ESH. apply aview_some_of_apresent. apply GA1. exact (proj1 (HFsh i ltac:(lia))).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hset3 & Heff3 & Hgr3).

assert (Z3 : forall i, 4 <= i < 13 -> aview segs (w_H W) mem3 (s6 + i) = Some 0).
{ intros i Hi. rewrite Heff3; [exact (Z1 i Hi) | unfold s6, SHADOW_OFF; lia | unfold s6, SHADOW_OFF; lia |].
  rewrite EST. unfold s6, SHADOW_OFF. lia. }
assert (VK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (s6 + 4 <= a < s6 + 13) -> ~ (F + 48 <= a < F + 104) ->
  ~ (sp1 - ESTACK <= a < sp1) -> aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a).
{ intros a Ha H1 H2 H3. rewrite Heff3; [exact (KR1 a Ha H1) | exact Ha | lia | lia]. }
assert (GA3 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a) by (intros a Ha; exact (Hgr3 a (GA1 a Ha))).
clear KR1 GA1 Z1 Heff3 Hgr3.
assert (HP13 : aregs_preserved regs2 regs3) by exact (aregs_preserved_trans _ _ _ HP1 HP3).
assert (T19 : YK11.getr regs3 19 = w64 MAYBEON_S) by exact (eq_trans (HP13 19 ltac:(hnf; lia)) R19).
assert (T21 : YK11.getr regs3 21 = w64 (F + 32)) by exact (eq_trans (HP13 21 ltac:(hnf; lia)) R21).
assert (T24 : YK11.getr regs3 24 = w64 SHADOW_OFF) by exact (eq_trans (HP13 24 ltac:(hnf; lia)) R24).
assert (T25 : YK11.getr regs3 25 = w64 (SHADOW_OFF + (MAYBEON_S + 112) / 8)) by exact (eq_trans (HP13 25 ltac:(hnf; lia)) R25).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
(* the world at mem3 is maybeon_w1 Bw: a byte of the world table is a byte of G, below kLowMemEnd *)
assert (TWG : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x).
{ intros x (o & b & n & Hin & Hx).
  assert (HG : In (b, n) TG.G_HARNESS) by exact (TMAP_A_in_G o b n Hin).
  unfold inG. apply Exists_exists. exists (b, n). split; [exact HG | unfold in_zr; cbn [fst snd]; lia]. }
assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transport_segs_low a (proj1 (HGX a Ha)))).
assert (FNG : forall a, F <= a < F + 256 -> ~ inG TG.G_HARNESS a).
{ intros a Ha HGa. exact (frm_img segs B LAWS lyc S2 W mem2 md2 MAYBEON_CID pos a HAR2 Hin2
    ltac:(rewrite <- EF; change (fs_frame_bytes MAYBEON_CID) with 256; lia) (trans_g_img a HGa)). }
assert (Htw3 : tw_at TMAP_A (aview segs (w_H W) mem3) (maybeon_w1 Bw)).
{ apply (tw_kept TMAP_A (aview segs (w_H W) mem2)); [exact Htw1|]. intros x Hx.
  pose proof (TWG x Hx) as HGx. pose proof (GLOW x HGx) as Hl.
  apply VK3; [lia | unfold s6, SHADOW_OFF; lia | intros H; exact (FNG x ltac:(lia) HGx) | rewrite EST; lia]. }
assert (Hlen : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
pose proof (tw_read_val segs (mrestrict (w_H W) mem3) TMAP_A (maybeon_w1 Bw) TW.OFF_g_s TA_g_s TW.SZ_g_s 96 8
  TMAP_A_ok Htw3 TMAP_A_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as Hv96.
pose proof (tw_read_val segs (mrestrict (w_H W) mem3) TMAP_A (maybeon_w1 Bw) TW.OFF_g_s TA_g_s TW.SZ_g_s 104 8
  TMAP_A_ok Htw3 TMAP_A_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as Hv104.
set (v96 := TW.u_at (maybeon_w1 Bw) (TW.OFF_g_s + 96) 8) in *.
set (v104 := TW.u_at (maybeon_w1 Bw) (TW.OFF_g_s + 104) 8) in *.
assert (Rv96 : 0 <= v96 < 2 ^ 64) by exact (TWL.u_at_range (maybeon_w1 Bw) (TW.OFF_g_s + 96) 8).
assert (Rv104 : 0 <= v104 < 2 ^ 64) by exact (TWL.u_at_range (maybeon_w1 Bw) (TW.OFF_g_s + 104) 8).

assert (Hs9 : aview segs (w_H W) mem3 (SHADOW_OFF + (MAYBEON_S + 112) / 8) = Some 0).
{ pose proof (decode_zshadow_rd B lyc S2 W mem3 md3 MAYBEON_S (MAYBEON_S + TW.SZ_g_s) (MAYBEON_S + 112) HAR3
    ltac:(rewrite ES; reflexivity) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) HMBC) as H.
  replace (SHADOW_OFF + (MAYBEON_S + 112) / 8) with (DgnTransportCg.FCells.shadow_addr (MAYBEON_S + 112))
    by reflexivity. exact H. }
assert (HD1 : F + 48 <= MAYBEON_S + 96 \/ MAYBEON_S + 116 <= F + 32).
{ destruct (Z_le_gt_dec (F + 48) (MAYBEON_S + 96)) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (MAYBEON_S + 116) (F + 32)) as [h2|h2]; [right; exact h2|]. exfalso.
  apply (FNG (Z.max (F + 32) (MAYBEON_S + 96))); [lia|].
  unfold inG, TG.G_HARNESS. apply Exists_exists. exists (6158784, 18264).
  split; [cbn; tauto | unfold in_zr; cbn [fst snd]; rewrite ES in *; lia]. }
assert (HD2 : F + 48 <= SHADOW_OFF + (MAYBEON_S + 112) / 8 \/ SHADOW_OFF + (MAYBEON_S + 112) / 8 + 1 <= F + 32).
{ replace (SHADOW_OFF + (MAYBEON_S + 112) / 8) with 2148220742 by reflexivity. lia. }
clear HS SHOK HEI HEI0 Q10 Q11 Q12 Q1 Q2 Q3 Q4 Hspm.
assert (Hpf3 : forall a, F + 32 <= a < F + 48 -> apresent (w_H W) mem3 a)
  by (intros a Ha; apply GA3; exact (proj1 (HFb a ltac:(lia)))).
pose proof (@mon_n2_entry fx rc W regs3 mem3 F v96 v104 T19 T21 T24 T25 ltac:(lia)
  ltac:(replace (F + 32) with (F + 1 * 32) by lia; rewrite Z_mod_plus_full;
        pose proof (Z.div_mod F 64 ltac:(lia)) as D; rewrite HF64, Z.add_0_r in D; rewrite D;
        replace (64 * (F / 64)) with ((2 * (F / 64)) * 32) by lia; apply Z_mod_mult)
  HD1 HD2 Hpf3 Hs9 Hv96 Rv96 Hv104 Rv104) as HS.
assert (SHOK : sh_ok segs MON_BX MON_SH2 (mon_E regs3 [w64 v96; w64 v104]) (mrestrict (w_H W) mem3)).
{ apply (mon_n2_shok W regs3 mem3 F _ T19 T21 T24); [lia | lia | unfold SHADOW_OFF; lia | |].
  - assert (E1 : (MAYBEON_S + 96) / 64 * 64 = 6158848) by reflexivity.
    assert (E2 : (MAYBEON_S + 96 + 16 - 1) / 64 * 64 + 64 = 6158912) by reflexivity.
    exact (proj1 (decode_zshadow_ra B lyc S2 W mem3 md3 MAYBEON_S (MAYBEON_S + TW.SZ_g_s) (MAYBEON_S + 96) 16 HAR3 HMBC
      ltac:(lia) ltac:(rewrite E1, ES; lia) ltac:(rewrite E2; unfold TW.SZ_g_s; rewrite ES; lia))).
  - apply (frame_ra_zero _ F (F + 32) 16 4 6); [lia | exact HF8 | lia | lia |].
    intros i Hi. exact (Z3 i ltac:(lia)). }
assert (HEI : img_env VAL A_LIM (mon_E regs3 [w64 v96; w64 v104])) by (unfold mon_E; apply Eimg_env).
assert (U19 : bv_unsigned (ew (mon_E regs3 [w64 v96; w64 v104]) 19) = MAYBEON_S).
{ rewrite (mon_ew regs3 _ 19 19%bv eq_refl), T19. unfold w64. apply unsigned_lit_small. rewrite ES. lia. }
assert (U21 : bv_unsigned (ew (mon_E regs3 [w64 v96; w64 v104]) 21) = F + 32).
{ rewrite (mon_ew regs3 _ 21 21%bv eq_refl), T21. unfold w64. apply unsigned_lit_small. lia. }
assert (U25 : bv_unsigned (ew (mon_E regs3 [w64 v96; w64 v104]) 25) = SHADOW_OFF + (MAYBEON_S + 112) / 8).
{ rewrite (mon_ew regs3 _ 25 25%bv eq_refl), T25. unfold w64. apply unsigned_lit_small.
  replace (SHADOW_OFF + (MAYBEON_S + 112) / 8) with 2148220742 by reflexivity. lia. }
(* run 2, +0x208 .. +0x264: the notice's first 16 bytes, the checked store of 2 at s + 112, the checked loads of
   s + 96 and s + 104, a1 = p; the run stops at `jalr a2` *)
paj_run_tok RUN HS HJ3 SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ MAYBEON_CID pos); [left; reflexivity | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U21 in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes MAYBEON_CID) with 256. lia. }
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19 in Ha.
  unfold inG, TG.G_HARNESS. apply Exists_exists. exists (6158784, 18264).
  split; [cbn; tauto | unfold in_zr; cbn [fst snd]; rewrite ES in Ha; lia]. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.

lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms4 end.
clear HJ1 HAR1 HAG HP1 HP3 ms.
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 48) -> ~ (MAYBEON_S + 112 <= a < MAYBEON_S + 116) ->
  aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) mem3 a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 32 <= x < F + 48) \/ (MAYBEON_S + 112 <= x < MAYBEON_S + 116)) HFr);
    [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hin Hx. cbv beta.
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U19, ?U21, ?U25 in Hx;
    first [left; lia | right; lia | lia] |]).
  destruct Hin. }
assert (GA4 : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms4) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RGp. cbn [ms_mem restrict] in RGp.
destruct RGp as (_ & _ & _ & HCHp). cbn [base_val YP09.r_base YP09.r_chunks] in HCHp. rewrite U21 in HCHp.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RGs. cbn [ms_mem restrict] in RGs.
destruct RGs as (_ & _ & _ & HCHs). cbn [base_val YP09.r_base YP09.r_chunks] in HCHs. rewrite U19 in HCHs.
assert (P72 : forall j, (j < 72)%nat ->
  aview segs (w_H W) (ms_mem ms4) (F + 32 + Z.of_nat j) = Some (nth j MON_NBZ 0)).
{ intros j Hj. destruct (Nat.lt_ge_cases j 16) as [Hj16 | Hj16].
  - unfold aview. apply (scfg_cs_ok _ _ _ _ _ _ HCHp).
    do 16 (destruct j as [|j]; [vm_compute; reflexivity|]). exfalso; lia.
  - rewrite KR2; [| lia | lia | intros H; apply (FNG (F + 32 + Z.of_nat j)); [lia|];
      unfold inG, TG.G_HARNESS; apply Exists_exists; exists (6158784, 18264);
      split; [cbn; tauto | unfold in_zr; cbn [fst snd]; rewrite ES in H; lia]].
    replace (F + 32 + Z.of_nat j) with (F + 48 + (Z.of_nat j - 16)) by lia.
    rewrite (Hset3 (Z.of_nat j - 16) ltac:(lia)). f_equal.
    unfold MON_NBZ. rewrite app_nth2 by (cbn [length]; lia). cbn [length]. rewrite nth_repeat. reflexivity. }
assert (P112 : forall j, (j < 4)%nat ->
  aview segs (w_H W) (ms_mem ms4) (TA_g_s + 112 + Z.of_nat j) = Some (YO0f.le_byte 2 4 j)).
{ intros j Hj. unfold aview. replace (TA_g_s + 112 + Z.of_nat j) with (MAYBEON_S + (112 + Z.of_nat j)) by (unfold MAYBEON_S; lia).
  apply (scfg_cs_ok _ _ _ _ _ _ HCHs).
  do 4 (destruct j as [|j]; [vm_compute; reflexivity|]). exfalso; lia. }
clear HCHp HCHs HF HFr HG.
assert (Htw4 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms4)) (maybeon_w2 Bw)).
{ rewrite mon_w2_eq.
  apply (tw_write TMAP_A (aview segs (w_H W) mem3) _ (maybeon_w1 Bw) TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 2
    TMAP_A_ok Htw3 TMAP_A_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) P112).
  intros x Hx Hn. pose proof (TWG x Hx) as HGx.
  apply KR2; [pose proof (GLOW x HGx); lia | intros H; exact (FNG x ltac:(lia) HGx) | exact Hn]. }
destruct (mon_model_ntc TF Bw Bw' Hgo Hst Hm) as (Hnot & Hnm).
assert (Ev96 : v96 = TI.ti_notice timg_A) by (rewrite <- Hnot, (mon_notify_w2 Bw Hlen); reflexivity).
assert (E32 : ew (mon_E regs3 [w64 v96; w64 v104]) 32 = w64 v96) by exact (mon_ew_x regs3 _ 0 ltac:(lia)).
mon_reg HS (12%bv : bv 5) (Z_to_bv 64 (TI.ti_notice timg_A)) Q12
  ltac:(cbn [sv_denot]; rewrite E32; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Ev96; reflexivity).
(* +0x264: `jalr a2`: notice at TI.ti_notice timg_A *)
assert (JPC : plookup (@pl_tpi transport_listing PL_transport) 41328 = Some (PW 393447)) by (vm_compute; reflexivity).
assert (JDEC : decode_any (Z_to_bv 32 393447) = Some (Jalr (1%bv : bv 5) (12%bv : bv 5) (0%bv : bv 12), 4%Z)) by vm_refl_bv.
assert (JTG : 0 <= TI.ti_notice timg_A < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
assert (JEV : TI.ti_notice timg_A mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
eapply (SRr_jalr_call_pi (fx := fx) (PL := PL_transport) (PI := PI_transport) W _ _ ms4 md4 _ 393447 1%bv 12%bv
  (TI.ti_notice timg_A) HEI HS eq_refl JPC JDEC eq_refl ltac:(cbn [ss_pc]; lia) Q12 JTG JEV).

intros mat5 ms5 -> _.
set (regsN := YK11.regupd (ms_regs ms4) (1%bv : bv 5) (Z_to_bv 64 (BASE + MON_RET2))).
pose proof (ajournal_gx_materialize segs B LAWS transport_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat5 HJ3) as HJ5.
set (md5 := with_vm_backing (m_vm_lazy md4) mat5 md4) in *.
change (SRr segs W (@cfg_at fx segs (TI.ti_notice timg_A) regsN (ms_mem ms4) md5)
  (transport_maybeon_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw')).
clearbody md5. clear mat5.

(* what the walk changed from the cut to the call: the frame's shadow bytes 4 .. 12, the memset's destination and its
   ESTACK scratch, the notice's first 16 bytes, s + 112 *)
set (Zpre := fun a => (s6 + 4 <= a < s6 + 13) \/ (F + 48 <= a < F + 104) \/ (sp1 - ESTACK <= a < sp1) \/
  (F + 32 <= a < F + 48) \/ (MAYBEON_S + 112 <= a < MAYBEON_S + 116)).
assert (VK4 : forall a, 0 <= a < 2 ^ 64 -> ~ Zpre a -> aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. unfold Zpre in Hn. rewrite KR2 by (exact Ha || tauto). apply VK3; [exact Ha | tauto | tauto | tauto]. }
assert (GA4' : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms4) a) by (intros a Ha; exact (GA4 a (GA3 a Ha))).
assert (Z4 : forall i, 4 <= i < 13 -> aview segs (w_H W) (ms_mem ms4) (s6 + i) = Some 0).
{ intros i Hi. rewrite KR2; [exact (Z3 i Hi) | unfold s6, SHADOW_OFF; lia | unfold s6, SHADOW_OFF; lia |].
  rewrite ES. unfold s6, SHADOW_OFF. lia. }
assert (Hce1 : alloc_ceiling <= spZ regs - MAYBEON_STK) by lia.
assert (Hlo1 : spZ regs <= 2 ^ 64) by lia.
assert (HZpre : forall a, Zpre a ->
  (spZ regs - MAYBEON_STK <= a < spZ regs) \/ dkg_nf MAYBEON_CID F (flag_addr lyc MAYBEON_CID pos) a \/ inG TG.G_HARNESS a).
{ intros a [H | [H | [H | [H | H]]]].
  - right; left. unfold dkg_nf. right; left. change (fs_frame_bytes MAYBEON_CID / 8) with 32. unfold s6 in H. lia.
  - right; left. unfold dkg_nf. left. change (fs_frame_bytes MAYBEON_CID) with 256. lia.
  - left. rewrite EST in H. lia.
  - right; left. unfold dkg_nf. left. change (fs_frame_bytes MAYBEON_CID) with 256. lia.
  - right; right. unfold inG, TG.G_HARNESS. apply Exists_exists. exists (6158784, 18264).
    split; [cbn; tauto | unfold in_zr; cbn [fst snd]; rewrite ES in H; lia]. }
assert (K4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W (ms_mem ms4) (spZ regs - MAYBEON_STK) (spZ regs)
  (maybeon_wr Bw)).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc lyc S2 W memc mdc W mem2 md2 mem2 (ms_mem ms4)
    (spZ regs - MAYBEON_STK) (spZ regs) MAYBEON_CID pos F (flag_addr lyc MAYBEON_CID pos) (maybeon_wr Bw) Zpre
    HGX HARc HAR2 Hfrs ltac:(intros bm Hbm; rewrite Ebl; exact Hbm) eq_refl EF eq_refl FFL Hce1 Hlo1 HZpre HK1 VK4 GA4'). }
assert (GK4 : gx_kept_ex segs TG.G_HARNESS (maybeon_wr Bw) W memc W (ms_mem ms4)).
{ apply (gx_kept_ex_step segs B transport_segs_low TG.G_HARNESS (maybeon_wr Bw) W memc mem2 (ms_mem ms4) Zpre HGX);
    [| exact VK4 | exact HGK1].
  intros a HZ HGa. destruct HZ as [H | [H | [H | [H | H]]]].
  - pose proof (GLOW a HGa). unfold s6, SHADOW_OFF in H. lia.
  - exfalso. exact (FNG a ltac:(lia) HGa).
  - pose proof (GLOW a HGa). rewrite EST in H. lia.
  - exfalso. exact (FNG a ltac:(lia) HGa).
  - split; [exact Hgo|]. right. split; [rewrite Hst; discriminate|]. left.
    unfold twa_fld, TW.A_S_state, TW.OFF_g_s. unfold MAYBEON_S in H. lia. }
(* the registers at notice's entry *)
assert (HAG4 : env_agree 32 (Ereg regs3 [w64 v96; w64 v104]) (mon_E regs3 [w64 v96; w64 v104]))
  by (split; [intros n Hn; unfold mon_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HP4 : aregs_preserved regs3 (ms_regs ms4))
  by (apply (aregs_preserved_of_st_ok segs (w_H W) _ _ ms4 regs3 _ HS HAG4); vm_compute; reflexivity).
assert (HP24 : aregs_preserved regs2 (ms_regs ms4)) by exact (aregs_preserved_trans _ _ _ HP13 HP4).
assert (NK : forall r, r <> 1 -> 0 <= r < 32 -> YK11.getr regsN (Z_to_bv 5 r) = YK11.getr (ms_regs ms4) (Z_to_bv 5 r)).
{ intros r Hr Hr32. unfold regsN. apply YK11.getr_other. intros E. apply Hr.
  apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 5) with 32 in E. rewrite Z.mod_small in E by lia. exact E. }
assert (HPN : aregs_preserved regs2 regsN).
{ intros r Hr. rewrite NK by (hnf in Hr; lia). exact (HP24 r Hr). }
assert (N1 : YK11.getr regsN 1 = Z_to_bv 64 (BASE + MON_RET2)) by (unfold regsN; apply YK11.getr_same; discriminate).
assert (EBR : BASE + MON_RET2 = 570328) by (vm_compute; reflexivity).
assert (N2 : YK11.getr regsN 2 = w64 sp1) by exact (eq_trans (HPN 2 ltac:(hnf; lia)) R2).
assert (N3 : YK11.getr regsN 3 = w64 (as_gp B)) by exact (eq_trans (eq_trans (HPN 3 ltac:(hnf; lia)) R3) Hgp).
assert (N4 : YK11.getr regsN 4 = w64 (as_tp B)) by exact (eq_trans (eq_trans (HPN 4 ltac:(hnf; lia)) R4) Htp).
mon_reg HS (11%bv : bv 5) (w64 (F + 32)) Q11
  ltac:(cbn [sv_denot]; rewrite (mon_ew regs3 _ 21 21%bv eq_refl), T21; unfold w64;
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (N11 : YK11.getr regsN 11 = w64 (F + 32)) by exact (eq_trans (NK 11 ltac:(lia) ltac:(lia)) Q11).
assert (NSP : spZ regsN = sp1) by (unfold spZ; rewrite N2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HAR5.
assert (Hstklt : ly_stk_lo lyc < ly_stk_hi lyc).
{ pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E1 & E2 & _). rewrite E1, E2. lia. }

assert (Hsp116 : sp1 mod 16 = 0).
{ pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp132, Z.add_0_r in D. rewrite D.
  replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
assert (PNTC : trans_ntc_at B lyc S2 W (ms_mem ms4) regsN NOTICE_STK (F + 32) (maybeon_ntc Bw)).
{ unfold trans_ntc_at.
  split; [lia|].
  split.
  { replace (F + 32) with (F + 4 * 8) by lia. rewrite Z_mod_plus_full. exact HF8. }
  split.
  { right. split.
    - left. exists MAYBEON_CID, pos. split; [exact Hin2|]. rewrite <- EF. change (fs_frame_bytes MAYBEON_CID) with 256.
      unfold NTC_SIZE. lia.
    - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
      + intros a Ha. replace a with (F + 32 + Z.of_nat (Z.to_nat (a - (F + 32)))) by lia.
        rewrite (P72 (Z.to_nat (a - (F + 32))) ltac:(lia)). discriminate.
      + apply (frame_ra_zero _ F (F + 32) 72 4 13); [lia | exact HF8 | lia | lia |]. intros i Hi. exact (Z4 i Hi).
      + apply (frame_hull_vis _ F 256 (F + 32) 72); [lia | exact HF64 | reflexivity | lia | lia | lia |].
        intros i Hi. change (256 / 8) with 32 in Hi. rewrite ESH. apply aview_some_of_apresent. apply GA4'.
        exact (proj1 (HFsh i ltac:(lia))).
      + unfold amem_range. destruct HFlo as [HL | HH]; [left; lia | right; lia].
      + lia.
      + lia. }
  split; [left; rewrite NSP, ENS; unfold NTC_SIZE; lia|].
  exists MON_NB. split.
  { replace (map DSpec.bz MON_NB) with MON_NBZ by (vm_compute; reflexivity).
    apply garr8_of_aview. intros j Hj. change (length MON_NBZ) with 72%nat in Hj. exact (P72 j Hj). }
  split; [reflexivity|].
  unfold maybeon_ntc. cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len
    TI.n_counter TI.n_retry TI.n_body TI.n_ann].
  rewrite Hst.
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  replace (TW.u_at MON_NB 48 8) with 0 by (vm_compute; reflexivity).
  split; [apply garr8_nil|]. split; [apply trans_src_ok_null|]. split; [left; rewrite NSP, ENS; cbn; lia|].
  vm_compute. reflexivity. }
assert (PTF : trans_tframe_at B lyc S2 W (ms_mem ms4) regsN NOTICE_STK TF).
{ apply (trans_tframe_at_kept_gx B LAWS HROU HRNE lyc Sc W memc mdc lyc S2 W (ms_mem ms4) md5 (maybeon_wr Bw)
    regs regsN MAYBEON_STK NOTICE_STK TF HARc HAR5 ltac:(intros bm Hbm; rewrite Ebl; exact Hbm)
    ltac:(intros f Hf; rewrite Hfrs; right; exact Hf) ltac:(intros; reflexivity) eq_refl eq_refl Hstklt K4 GK4).
  - intros fr Efr a Ha Hw. exact (Hapart a Hw fr Efr Ha).
  - intros a Ha Hw. pose proof (GLOW a (mon_wr_G Bw a Hw)). lia.
  - rewrite NSP, EMS, ENS. lia.
  - rewrite NSP. lia.
  - exact HTF. }
assert (PROM : trans_rom_view_rd W (ms_mem ms4)).
{ intros a Ha. destruct K4 as (_ & _ & K43 & _). rewrite (K43 a (trans_ro_img a Ha)).
  - exact (Hrom a Ha).
  - intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
    unfold TransportG.G_HARNESS_LO in Gh. lia.
  - exact (proj1 (trans_ro_rd_scoped B HROU HRNE a Ha)).
  - exact (proj2 (trans_ro_rd_scoped B HROU HRNE a Ha)). }
assert (PAP : notice_apart W (ms_mem ms4) (F + 32) (maybeon_ntc Bw) TF (maybeon_w2 Bw)).
{ intros x Hx.
  assert (Hw : maybeon_wr Bw x) by (split; [exact Hgo | right; split; [rewrite Hst; discriminate | right; exact Hx]]).
  pose proof (notice_wr_G _ _ x Hx) as HGx.
  split; [intros H; unfold NTC_SIZE in H; exact (FNG x ltac:(lia) HGx)|].
  split.
  - intros NB _ _. unfold maybeon_ntc. cbn [TI.n_body TI.n_ann length Z.of_nat].
    split; [lia | intros H; exfalso; apply H; reflexivity].
  - intros fr Efr. exact (Hapart x Hw fr Efr). }
assert (PND : TI.n_kind (maybeon_ntc Bw) = TC.N_DATA ->
  trans_src_ok B lyc S2 W (ms_mem ms4) (TC.OW_dn_body (maybeon_w2 Bw) (TW.GOT_ndata (maybeon_w2 Bw)))
    (TI.n_body_len (maybeon_ntc Bw)) /\
  decode_off_win regsN NOTICE_STK (TC.OW_dn_body (maybeon_w2 Bw) (TW.GOT_ndata (maybeon_w2 Bw)))
    (TI.n_body_len (maybeon_ntc Bw)) /\
  TI.n_body_len (maybeon_ntc Bw) < 2 ^ 32).
{ intros H. exfalso. unfold maybeon_ntc in H. cbn [TI.n_kind] in H. discriminate H. }
assert (PNEV : st_nev S + (k + 0) + NOTICE_EV <= EV_MAX) by (unfold MAYBEON_EV in Hnev; lia).
(* +0x264: notice, in the same G journal *)
eapply SRr_bind.
{ apply (HNTC fx STK sp0 FP ly S W0 mem0 md0 ((MAYBEON_CID, pos) :: own) lyc S2 W (ms_mem ms4) md5 (k + 0) regsN
    (F + 32) (maybeon_ntc Bw) TF (maybeon_w2 Bw) Bw' HJ5
    ltac:(rewrite N1; apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold MON_RET2, AF_maybe_online; lia | reflexivity])
    ltac:(unfold raZ; rewrite N1, EBR, unsigned_lit_small by lia; lia)
    N3 N4 N11 ltac:(rewrite NSP; exact Hsp116) ltac:(rewrite NSP, ENS; rewrite EMS in Hwin1; lia) ltac:(rewrite NSP; lia)
    PNTC PTF PROM Htw4 Hnm PAP PND PNEV). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST.
destruct HPOST as (ly3 & S3 & regs5 & mem5 & md6 & e & -> & He & HJ6 & HP6 & Hfr6 & Hperm6 & HK6 & Hmo6 & Htw6).

pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as HAR6.
assert (ELF3 : ly_F ly3 = ly_F lyc).
{ pose proof HJ6 as (_ & _ & (memS6 & HJ6i & _) & _). pose proof HJ6i as (_ & Hly3 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & E3 & _). pose proof Hlyc as (_ & _ & _ & _ & _ & Ec & _).
  rewrite E3, Ec. reflexivity. }
assert (EFA3 : frame_addr ly3 MAYBEON_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF3; reflexivity).
assert (Hin3 : In (MAYBEON_CID, pos) (frames S3)) by (rewrite Hfr6; exact Hin2).
destruct (al_frames _ _ LAWS _ _ _ _ _ MAYBEON_CID pos HAR6 Hin3) as (_ & _ & _ & HFsh3).
change (fs_frame_bytes MAYBEON_CID / 8) with 32 in HFsh3. rewrite EFA3, ESH in HFsh3.
assert (HP25 : aregs_preserved regs2 regs5) by exact (aregs_preserved_trans _ _ _ HPN HP6).
assert (R22' : YK11.getr regs5 22 = w64 (SHADOW_OFF + F / 8)) by exact (eq_trans (HP25 22 ltac:(hnf; lia)) R22).
rewrite N1.
clear HS SHOK HEI.
(* run 3, +0x268 .. +0x28c: shadow bytes 4 .. 12 := 0xf8, to the release cut *)
pose proof (mon_sh_entry W3 regs5 mem5 F MON_RET2 R22' ltac:(lia) ltac:(intros i Hi; exact (proj1 (HFsh3 i ltac:(lia)))))
  as HS.
assert (SHOK : sh_ok segs MON_BX [] (mon_E regs5 []) (mrestrict (w_H W3) mem5)) by constructor.
assert (HEI : img_env VAL A_LIM (mon_E regs5 [])) by (unfold mon_E; apply Eimg_env).
assert (U22' : bv_unsigned (ew (mon_E regs5 []) 22) = s6).
{ rewrite (mon_ew regs5 [] 22 22%bv eq_refl), R22'. unfold w64. apply unsigned_lit_small. unfold s6, SHADOW_OFF. lia. }
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS HJ6 SHOK mon_B0 MON_REL.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ MAYBEON_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22' in Ha.
  right. unfold in_zr. cbn [fst snd]. rewrite EFA3, ESH. change (fs_frame_bytes MAYBEON_CID / 8) with 32. unfold s6 in Ha. lia. }
set (md7 := with_vm_backing (m_vm_lazy md6) mat md6) in *. clearbody md7. clear mat.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms6 end.
assert (KR6 : forall a, 0 <= a < 2 ^ 64 -> ~ (s6 + 4 <= a < s6 + 13) ->
  aview segs (w_H W3) (ms_mem ms6) a = aview segs (w_H W3) mem5 a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ _ _ _ (fun x => s6 + 4 <= x < s6 + 13) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta.
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end.
  cbn [In] in Hin. destruct Hin as [Hin | []]. injection Hin as <- <- <-. cbn [base_val] in Hx. rewrite U22' in Hx. lia. }
assert (GA6 : forall a, apresent (w_H W3) mem5 a -> apresent (w_H W3) (ms_mem ms6) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (HAG6 : env_agree 32 (Ereg regs5 []) (mon_E regs5 []))
  by (split; [intros n Hn; unfold mon_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HP56 : aregs_preserved regs5 (ms_regs ms6))
  by (apply (aregs_preserved_of_st_ok segs (w_H W3) _ _ ms6 regs5 [] HS HAG6); vm_compute; reflexivity).
assert (HP26 : aregs_preserved regs2 (ms_regs ms6)) by exact (aregs_preserved_trans _ _ _ HP25 HP56).
pmkst HS.

(* the frame's own bytes and shadow, apart from the call's blocks, image and frames *)
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc lyc S2 W mem2 md2 MAYBEON_CID pos F
  (flag_addr lyc MAYBEON_CID pos) HAR2 Hfrs ltac:(intros bm Hbm; rewrite Ebl; exact Hbm) eq_refl EF eq_refl FFL)
  as (NS1 & NS2 & NS3 & NS4).
rewrite NSP in HK6.
assert (K5 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem5 (spZ regs - MAYBEON_STK) (spZ regs)
  (maybeon_wr Bw)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc lyc S2 W memc W (ms_mem ms4) W3 mem5
    (spZ regs - MAYBEON_STK) (spZ regs) (sp1 - NOTICE_STK) sp1 (maybeon_wr Bw)
    (notice_wr (maybeon_w2 Bw) (maybeon_ntc Bw)) (dkg_nf MAYBEON_CID F (flag_addr lyc MAYBEON_CID pos))
    Hce1 Hlo1 ltac:(intros; reflexivity) ltac:(intros f Hf; rewrite Hfrs; right; exact Hf)
    ltac:(intros bm Hbm; rewrite Ebl; exact Hbm) NS1 NS3 K4 HK6).
  - rewrite ENS, EMS. lia.
  - lia.
  - intros a Ha. left. split; [exact Hgo | right; split; [rewrite Hst; discriminate | right; exact Ha]]. }
assert (K6 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (ms_mem ms6) (spZ regs - MAYBEON_STK) (spZ regs)
  (maybeon_wr Bw)).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly3 S3 W memc mdc W3 mem5 md6 mem5
    (ms_mem ms6) (spZ regs - MAYBEON_STK) (spZ regs) MAYBEON_CID pos F (flag_addr lyc MAYBEON_CID pos) (maybeon_wr Bw)
    (fun a => s6 + 4 <= a < s6 + 13) HGX HARc HAR6 ltac:(rewrite Hfr6; exact Hfrs)
    ltac:(intros bm Hbm; rewrite <- Ebl in Hbm; exact (Permutation_in _ (Permutation_sym Hperm6) Hbm))
    ELF3 EF eq_refl FFL Hce1 Hlo1).
  - intros a Ha. right; left. unfold dkg_nf. right; left. change (fs_frame_bytes MAYBEON_CID / 8) with 32.
    unfold s6 in Ha. lia.
  - exact K5.
  - exact KR6.
  - exact GA6. }
(* the release cut *)
apply (REL LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw Bw' pos sp1 F ly3 S3 W3 (ms_mem ms6)
  md7 e (ms_regs ms6) HFIX).
- unfold mon_rel_cur, mon_cur.
  split; [split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]|split].
  + replace (k + e) with (k + 0 + e) by lia. exact HJ6.
  + unfold MAYBEON_EV. exact He.
  + rewrite Hfr6. exact Hfrs.
  + rewrite <- Ebl. exact Hperm6.
  + exact ELF3.
  + exact (mo_le_trans MT MTL Sc S2 S3 0 0 Hmo Hmo6).
  + exact K6.
  + rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
    assert (Hob : 8 <= fst o <= 88).
    { unfold MON_SAVED in Ho. cbn [In] in Ho. repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
    apply rdword_ext. intros i Hi.
    rewrite KR6 by (unfold s6, SHADOW_OFF; lia).
    destruct HK6 as (L1 & _).
    rewrite L1 by lia.
    apply VK4; [lia|]. intros [H | [H | [H | [H | H]]]]; [unfold s6, SHADOW_OFF in H; lia | lia | rewrite EST in H; lia | lia |].
    rewrite ES in H. lia.
  + rewrite <- HFLw. apply rdword_ext. intros i Hi.
    rewrite KR6 by (unfold s6, SHADOW_OFF; lia).
    destruct HK6 as (_ & _ & _ & L4 & _).
    rewrite (L4 MAYBEON_CID pos (F + 256 - 8 + i) Hin2).
    * apply VK4; [lia|]. intros [H | [H | [H | [H | H]]]]; [unfold s6, SHADOW_OFF in H; lia | lia | rewrite EST in H; lia | lia |].
      exfalso. apply (FNG (F + 256 - 8 + i)); [lia|]. unfold inG, TG.G_HARNESS. apply Exists_exists.
      exists (6158784, 18264). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; rewrite ES in H; lia].
    * left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes MAYBEON_CID) with 256. lia.
    * intros Hw. exact (FNG (F + 256 - 8 + i) ltac:(lia) (notice_wr_G _ _ _ Hw)).
  + apply (tw_kept TMAP_A (aview segs (w_H W3) mem5)); [exact Htw6|]. intros x Hx.
    pose proof (GLOW x (TWG x Hx)) as Hl. apply KR6; [lia | unfold s6, SHADOW_OFF; lia].
  + exact (mon_gfn TF Bw Bw' Hlen Hgf Hnm).
- unfold mon_regs_rel.
  split; [exact (eq_trans (HP26 2 ltac:(hnf; lia)) R2)|].
  split; [exact (eq_trans (HP26 3 ltac:(hnf; lia)) R3)|].
  split; [exact (eq_trans (HP26 4 ltac:(hnf; lia)) R4)|].
  split; [exact (eq_trans (HP26 8 ltac:(hnf; lia)) R8)|].
  split; [exact (eq_trans (HP26 9 ltac:(hnf; lia)) R9)|].
  split; [exact (eq_trans (HP26 18 ltac:(hnf; lia)) R18)|].
  split; [exact (eq_trans (HP26 22 ltac:(hnf; lia)) R22)|].
  split; [exact (eq_trans (HP26 23 ltac:(hnf; lia)) R23)|].
  split; [exact (eq_trans (HP26 26 ltac:(hnf; lia)) R26)|].
  exact (eq_trans (HP26 27 ltac:(hnf; lia)) R27).
Qed.
End main.
