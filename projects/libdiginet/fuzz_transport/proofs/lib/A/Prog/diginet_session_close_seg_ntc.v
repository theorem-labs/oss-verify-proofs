(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 783 of its 853 lines of code are new or changed and 960 lines of the source are left out. *)
(* diginet_session_close_seg_ntc: Lemma close_ntc : close_ntc_stmt (lib/A/Prog/diginet_session_close_segs.v), the
   notice piece of diginet_session_close's image-A G-form walk, offsets +0x1c0 .. +0x28c of the listing
   lib/A/Prog/DgnTransportList.v (fuzz_transport.asan 0x872fc .. 0x873c8), then the release cut (close_rel_at, a
   premise).

   What the code does. +0x1c0 `sd a3, 24(s1)`: the result r in the function's own machine frame (a3 does not survive
   the calls); +0x1c4 s6 = p = frame + 32; the notice's shadow bytes 4 .. 12 := 0; a0 = p + 16, a2 = 56, a1 = 0 and
   `jal __asan_memset` at +0x1f8 (return +0x1fc): the notice's bytes 16 .. 71 := 0. +0x1fc .. +0x210: s4 = 3 << 32 + 2
   and the 8 bytes 0x0000000300000002 at p (kind N_STATE, state S_CLOSED), s11 (the state the join loaded) at p + 8, 8
   (reason R_CLOSED) at p + 12. +0x214 .. +0x224: the shadow byte of s + 112 (s10) read, 0, and the store of 3 at
   s + 112: the world is close_w2 B1. +0x228 .. +0x248: the checks of the 8-byte loads at s + 96 and s + 104; +0x24c
   .. +0x254: a2 = the notify pointer (S_notify, which the model's call_notify tests against TI.ti_notice timg_A),
   a0 = notify_ctx, a1 = p; +0x258 `jalr a2`: notice, return +0x25c. +0x25c .. +0x280: the shadow bytes 4 .. 12 :=
   0xf8; +0x284 a3 = the 8 bytes at s1 + 24 (r again); +0x288 `j` to the release cut +0x290.

   The state at the cut is the one after the join (close_ntc_cur): the layout ly2 and the world W2 are those
   send_control returned (or the call's), so every step keeps the caller's memory by the W1 / ly2 forms of the frame
   kit (lib/A/Prog/TransportGFrame.v dk_kept_nfz_gw, dkg_nf_sep_gw; TransportGCg.v dk_kept_trans_nf_g for notice).
   Three runs of the token engine over the caller's G journal (lib/A/Prog/TransportGRunA.v paj_run_x /
   paj_run_to_x):
     run 1 (+0x1c0 .. the call of __asan_memset) and run 2 (+0x1fc .. the `jalr`), one symbolic state across the
       memset (YC1h.v jafter_call_keep_hi): the notice's shadow bytes 4 .. 12 at s7, the notice's first 16 bytes at
       s8 + 32, g_s's bytes [s + 96, s + 116) (the two loaded words as atoms 32, 33, read off the world close_w1 B1;
       [s + 112, s + 116) written, bytes of G), the shadow bytes of s + 96 .. s + 112 (the record's zero shadow of
       g_s), and the slot s1 + 24 .. s1 + 32 of the machine frame (written by run 1, a byte of the call's stack
       window); s3, s4, s9 and s10 are pinned to their values, so the engine folds s4 << 32 + 2;
     run 3 (+0x25c .. +0x290): the shadow bytes at s7 again, and the slot read: its 8 bytes still hold r (the
       memset's, run 2's and notice's kept facts: the slot lies above both callee windows and outside notice's written
       range), as atom 32.
   __asan_memset: TransportGCg.v gx_intrin_at. The `jalr`: DgnTransportPaLib.v SRr_jalr_call_pi at the target
   TI.ti_notice timg_A. notice: notice_cg.v transport_notice_cg at TI.ti_notice timg_A (a premise), in the same G
   journal: trans_ntc_at (diginet_session_close_seg_ntckit.v close_trans_ntc), trans_tframe_at (TransportGNotice.v
   trans_tframe_at_kept_gx over the written range widened by G, TransportGCg.v acall_kept_g_weaken: G outside it is
   then no byte, and trans_tf_off_g with close_apart puts TF outside it), trans_rom_view_rd (the image clause of the
   running acall_kept_g), tw_at at close_w2 B1 (TWorldG.v tw_write of the store at s + 112), the model's notice
   (diginet_session_close_seg_kit.v close_ntc_model), notice_apart (close_ntc_apart), the N_DATA premise vacuous, no
   event (CLOSE_EV = 0). The release
   cut's state: notice's post journal, frames and blocks, the meter by mo_le_trans, acall_kept_g by dk_kept_trans_nf_g
   and dk_kept_nfz_gw, the saved words and the frame's last word kept, tw_at at Bw' (run 3 keeps G), g_fail_next Bw' =
   g_fail_next B1 (close_gfn'), and the registers the release reads, a3 = r among them. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_close_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_close_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_close_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_close_seg_ntckit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGNotice SlostNtc.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The shadow byte of g_s.notify (s + 96); s + 104 and s + 112 have the next two. *)
Definition CN_SH : Z := 2148220740.
Lemma CN_SH_eq : CN_SH = SHADOW_OFF + (CLOSE_S + 96) / 8.
Proof. reflexivity. Qed.
(* Runs 1 and 2: the notice's shadow bytes 4 .. 12 at s7 = atom 23; its first 16 bytes at s8 = atom 24 (offsets
   32 .. 48); g_s's bytes [s + 96, s + 116) (the loaded words as atoms 32 and 33; [s + 112, s + 116) written); the
   three shadow bytes of s + 96 .. s + 112 (0); the slot s1 + 24 .. s1 + 32 of the machine frame at s1 = atom 9. *)
Definition CN_R_sh : YP09.region := YP09.mkRegion (Some 23%nat) 4 13 4 13 [].
Definition CN_R_p : YP09.region := YP09.mkRegion (Some 24%nat) 32 48 32 48 [].
Definition CN_R_gs : YP09.region :=
  YP09.mkRegion None (CLOSE_S + 96) (CLOSE_S + 116) (CLOSE_S + 112) (CLOSE_S + 116)
    [YP09.mkChunk (CLOSE_S + 96) (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk (CLOSE_S + 104) (YP09.CVal 8 (SOff 33 0))].
Definition CN_R_shg : YP09.region :=
  YP09.mkRegion None CN_SH (CN_SH + 3) 0 0
    [YP09.mkChunk CN_SH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (CN_SH + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (CN_SH + 2) (YP09.CVal 1 (SLit 0))].
Definition CN_R_sl : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
Definition CN_FACTS : facts :=
  mkFacts [(23%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3); (24%nat, mkAF 4096 (2 ^ 47) 6);
           (9%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
(* s3 = s, s4 = 3, s9 = the shadow base, s10 = the shadow address of s + 112. *)
Definition CN_REGS : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 19) (SLit CLOSE_S)) (Z_to_bv 5 20) (SLit 3))
    (Z_to_bv 5 25) (SLit SHADOW_OFF)) (Z_to_bv 5 26) (SLit (CN_SH + 2)).
Definition ss_cn : sstate := mkSS CLOSE_NTC CN_REGS [CN_R_sh; CN_R_p; CN_R_gs; CN_R_shg; CN_R_sl] None CN_FACTS.
Definition CN_Bx : sv := SLit 0.
Definition CN_B0 : Z * Z := (0, 0).
(* Run 3: the shadow bytes at s7, and the slot read: its 8 bytes are r (atom 32). *)
Definition CN_R_sl3 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (YP09.CVal 8 (SOff 32 0))].
Definition ss_cn3 : sstate := mkSS (CLOSE_NTC + 0x9c) sr_atoms [CN_R_sh; CN_R_sl3] None
  (mkFacts [(23%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3); (9%nat, mkAF 4096 (2 ^ 47) 5)] [] []).

(* The bytes the piece may change between the cut and the call of notice: the notice's shadow bytes 4 .. 12, the
   notice's 72 bytes, g_s.state, the stack window of __asan_memset below sp1, and the slot s1 + 24 .. s1 + 32. *)
Definition cn_Z (F sp1 : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) \/ (F + 32 <= x < F + 104) \/
  (CLOSE_S + 112 <= x < CLOSE_S + 116) \/ (sp1 - ESTACK <= x < sp1) \/ (sp1 + 24 <= x < sp1 + 32).

(* The write rights of runs 1 and 2 (U23 / U24 / U9: the bases' values; EFA: the frame's address at the current
   layout). *)
Ltac close_awr U23 U24 U9 EFA :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := CLOSE_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U23 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes CLOSE_CID / 8) with 32; lia |];
  eapply awr_ok_x_cons_own with (cid := CLOSE_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U24 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes CLOSE_CID) with 256; lia |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    unfold inG; apply Exists_exists; exists (TA_g_s, TW.SZ_g_s);
    split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, CLOSE_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia] |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
    left; split; [left; lia | lia] |];
  apply awr_ok_x_nil.

(* The windows a run wrote lie in cn_Z (U23 / U24 / U9: the bases' values). *)
Ltac cn_wtac U23 U24 U9 Hx :=
  rewrite ?U23, ?U24, ?U9 in Hx; unfold cn_Z, CLOSE_S, TA_g_s;
  first [ lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; left; lia
        | right; right; right; right; lia ].

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac cn_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "cn_reg: no match for" T; fail
  end.

Section n. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation of runs 1 and 2: the registers at the cut, then g_s.notify and g_s.notify_ctx of the world. *)
Definition cn_vals (B1 : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at (close_w1 B1) (TW.OFF_g_s + 96) 8); Z_to_bv 64 (TW.u_at (close_w1 B1) (TW.OFF_g_s + 104) 8)].
Definition cn_E (regs : bvmap 5 word) (B1 : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (cn_vals B1)).

Lemma cn_entry0 : forall ly S (W : world segs) regs mem md B1 F sp1,
  trans_close_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) (close_w1 B1) ->
  YK11.getr regs 23 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 24 = w64 F -> YK11.getr regs 9 = w64 sp1 ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  (F + 256 <= CLOSE_S \/ CLOSE_S + TW.SZ_g_s <= F) ->
  alloc_ceiling <= sp1 -> sp1 + 32 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall a, F + 32 <= a < F + 48 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  (forall a, sp1 + 24 <= a < sp1 + 32 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (cn_E regs B1)
    (mkSS CLOSE_NTC sr_atoms [CN_R_sh; CN_R_p; CN_R_gs; CN_R_shg; CN_R_sl] None CN_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CLOSE_NTC)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md B1 F sp1 HSC HAR Htw R23 R24 R9 HF0 HF64 HFc HFapp HFG Hs0 Hs1 Hs2 Hpf Hpsh Hpsl.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (Hg : 64 <= F / 64 * 64) by lia.
  set (E := cn_E regs B1).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, cn_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF + F / 8)
    by (rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U24 : bv_unsigned (ew E 24) = F)
    by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (cn_vals B1) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, cn_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  cbn [Nat.add nth cn_vals] in E32, E33.
  pose proof (TWL.u_at_range (close_w1 B1) (TW.OFF_g_s + 96) 8) as R32.
  pose proof (TWL.u_at_range (close_w1 B1) (TW.OFF_g_s + 104) 8) as R33.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32, R33.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall j, (j < 3)%nat -> val_mem segs (mrestrict (w_H W) mem) (CN_SH + Z.of_nat j) 1 0).
  { intros j Hj. apply AE2y.val_mem1_of_aview.
    replace (CN_SH + Z.of_nat j) with (FCells.shadow_addr (CLOSE_S + 96 + 8 * Z.of_nat j)).
    - apply (decode_zshadow_rd B ly S W mem md CLOSE_S (CLOSE_S + TW.SZ_g_s) _ HAR); [| | | exact HSC].
      + unfold CLOSE_S, TA_g_s. rewrite Z.add_mod, Z.mul_comm, Z.mod_mul by lia. reflexivity.
      + lia.
      + unfold TW.SZ_g_s. lia.
    - unfold FCells.shadow_addr, FCells.ASAN_K, CN_SH, CLOSE_S, TA_g_s.
      replace (6158784 + 96 + 8 * Z.of_nat j) with ((769860 + Z.of_nat j) * 8) by lia.
      rewrite Z.div_mul by lia. lia. }
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks CN_R_sh CN_R_p CN_R_gs CN_R_shg
        CN_R_sl base_val]; rewrite ?U23, ?U24, ?U9.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
    + split; [unfold CLOSE_S, TA_g_s; lia|]. split; [unfold CLOSE_S, TA_g_s; lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
        unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
        split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, CLOSE_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val segs E _ 0 (CLOSE_S + 96) 8 (SOff 32 0) (TW.u_at (close_w1 B1) (TW.OFF_g_s + 96) 8));
             [apply DEN; [exact E32 | exact R32] | exact R32 | unfold CLOSE_S, TA_g_s; lia |].
           replace (0 + (CLOSE_S + 96)) with (TA_g_s + 96) by (unfold CLOSE_S; lia).
           exact (tw_read_val segs _ TMAP_A (close_w1 B1) TW.OFF_g_s TA_g_s TW.SZ_g_s 96 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ 0 (CLOSE_S + 104) 8 (SOff 33 0) (TW.u_at (close_w1 B1) (TW.OFF_g_s + 104) 8));
             [apply DEN; [exact E33 | exact R33] | exact R33 | unfold CLOSE_S, TA_g_s; lia |].
           replace (0 + (CLOSE_S + 104)) with (TA_g_s + 104) by (unfold CLOSE_S; lia).
           exact (tw_read_val segs _ TMAP_A (close_w1 B1) TW.OFF_g_s TA_g_s TW.SZ_g_s 104 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold CN_SH, SHADOW_OFF, CLOSE_S, TA_g_s; lia|].
      split; [unfold CN_SH, SHADOW_OFF, CLOSE_S, TA_g_s; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 CN_SH 1 (SLit 0) 0);
          [reflexivity | lia | unfold CN_SH, SHADOW_OFF, CLOSE_S, TA_g_s; lia |].
        rewrite Z.add_0_l. pose proof (ZSH 0%nat ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
      * apply (chunk_ok_val segs E _ 0 (CN_SH + 1) 1 (SLit 0) 0);
          [reflexivity | lia | unfold CN_SH, SHADOW_OFF, CLOSE_S, TA_g_s; lia |].
        rewrite Z.add_0_l. exact (ZSH 1%nat ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (CN_SH + 2) 1 (SLit 0) 0);
          [reflexivity | lia | unfold CN_SH, SHADOW_OFF, CLOSE_S, TA_g_s; lia |].
        rewrite Z.add_0_l. exact (ZSH 2%nat ltac:(lia)).
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsl. lia.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, CN_R_sh, CN_R_p, CN_R_gs, CN_R_shg, CN_R_sl.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U23, U24, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, CN_SH, SHADOW_OFF, CLOSE_S, TA_g_s, TW.SZ_g_s in *.
    rewrite HF8. repeat split; first [exact I | lia].
  - unfold CN_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23, U24, U9.
    change (2 ^ 3) with 8. change (2 ^ 6) with 64. change (2 ^ 5) with 32.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma cn_entry : forall ly S (W : world segs) regs mem md B1 F sp1,
  trans_close_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) (close_w1 B1) ->
  YK11.getr regs 23 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 24 = w64 F -> YK11.getr regs 9 = w64 sp1 ->
  YK11.getr regs 19 = w64 CLOSE_S -> YK11.getr regs 20 = w64 3 -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  YK11.getr regs 26 = w64 (CN_SH + 2) ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  (F + 256 <= CLOSE_S \/ CLOSE_S + TW.SZ_g_s <= F) ->
  alloc_ceiling <= sp1 -> sp1 + 32 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall a, F + 32 <= a < F + 48 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  (forall a, sp1 + 24 <= a < sp1 + 32 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (cn_E regs B1) ss_cn
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CLOSE_NTC)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md B1 F sp1 HSC HAR Htw R23 R24 R9 R19 R20 R25 R26 HF0 HF64 HFc HFapp HFG Hs0 Hs1 Hs2
    Hpf Hpsh Hpsl.
  rewrite restrict_mkst_fx.
  pose proof (cn_entry0 ly S W regs mem md B1 F sp1 HSC HAR Htw R23 R24 R9 HF0 HF64 HFc HFapp HFG Hs0 Hs1 Hs2
    Hpf Hpsh Hpsl) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 19) CLOSE_S H0 R19 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) 3 H1 R20 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 25) SHADOW_OFF H2 R25 eq_refl) as H3.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 26) (CN_SH + 2) H3 R26 eq_refl) as H4.
  exact H4.
Qed.

(* The symbolic state at +0x25c (after notice returns): the registers as atoms, r as atom 32, the notice's shadow
   bytes 4 .. 12, the slot s1 + 24 .. s1 + 32 holding r. *)
Lemma cn_entry3 : forall (W : world segs) regs mem F sp1 r,
  YK11.getr regs 23 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 9 = w64 sp1 ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= alloc_ceiling ->
  alloc_ceiling <= sp1 -> sp1 + 32 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 24) 8 (bv_unsigned (w64 r)) ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [w64 r])) ss_cn3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (CLOSE_NTC + 0x9c))) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F sp1 r R23 R9 HF0 HF64 HFc Hs0 Hs1 Hs2 Hpsh VS.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  set (E := Eimg (PI := PI_transport) (Ereg regs [w64 r])).
  assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF + F / 8)
    by (unfold E; rewrite (ew_Eimg_Ereg_nat regs [w64 r] 23 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small;
        unfold SHADOW_OFF; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (unfold E; rewrite (ew_Eimg_Ereg_nat regs [w64 r] 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small;
        lia).
  assert (E32 : ew E 32 = w64 r)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [w64 r] 0)).
  pose proof (bv_unsigned_in_range 64 (w64 r)) as Hr64. change (bv_modulus 64) with (2 ^ 64) in Hr64.
  rewrite restrict_mkst_fx. unfold ss_cn3.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks CN_R_sh CN_R_sl3 base_val];
      rewrite ?U23, ?U9.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ sp1 24 8 (SOff 32 0) (bv_unsigned (w64 r)));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; reflexivity | exact Hr64 | lia | exact VS].
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, CN_R_sh, CN_R_sl3.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U23, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF in *. repeat split; first [exact I | lia].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23, U9. change (2 ^ 3) with 8. change (2 ^ 5) with 32.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Lemma close_ntc : @close_ntc_stmt fx rc B MT.
Proof.
unfold close_ntc_stmt. intros REL. unfold close_ntc_at.
intros LAWS0 HMS HN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' B1 pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HSC & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE & HGU & HGNE).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTF &
  Hrom & Hapart & Hoffg & Hfly & Hcmd & Hcnt & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hsent & Htw1 & Hgf1 & Hst).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R13) & R19 & R20 & R25 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold CLOSE_FBYTES in HFc, HFapp, HFLw.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof HJ1 as (_ & _ & (memS1 & HJi1 & _) & _).
rewrite !Z.add_0_r in HJi1.
pose proof HJi1 as (_ & Hlyle2 & _).
clear HJi1 memS1.
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ESLO & ESHI & _).
pose proof Hlyle2 as (_ & _ & _ & _ & _ & ELF2 & _ & _ & _ & ESLO2 & ESHI2 & _).
assert (Elo2 : ly_stk_lo ly2 = ly_stk_lo lyc) by (rewrite ESLO2, ESLO; reflexivity).
assert (Ehi2 : ly_stk_hi ly2 = ly_stk_hi lyc) by (rewrite ESHI2, ESHI; reflexivity).
assert (EST : ESTACK = 4096) by reflexivity.
assert (HCS : CLOSE_STK = 176 + SENDCTL_STK) by reflexivity.
assert (HSS1 : NOTICE_STK <= SENDCTL_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSS2 : ESTACK <= SENDCTL_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HNS0 : ESTACK <= NOTICE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HCE : CLOSE_EV = 0) by reflexivity.
assert (HNE : NOTICE_EV = 0) by reflexivity.
(* the realigned sp1 *)
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold CLOSE_FRAME.
  pose proof (Z.div_mod (spZ regs - 160) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 160) / 32) in *. set (rr := (spZ regs - 160) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (HACE : alloc_ceiling <= sp1 - SENDCTL_STK) by lia.
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the own frame at the current layout *)
assert (Hin : In (CLOSE_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hfa2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite HlyF; reflexivity).
assert (EFA : frame_addr ly2 CLOSE_CID pos = F) by (rewrite Hfa2; exact (eq_sym EF)).
assert (Hfr2 : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf; rewrite Hfrs; right; exact Hf).
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
set (FL := flag_addr lyc CLOSE_CID pos) in *.
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 CLOSE_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
rewrite EFA in HFb, HFsh.
change (fs_frame_bytes CLOSE_CID) with 256 in HFb. change (fs_frame_bytes CLOSE_CID / 8) with 32 in HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (HFG : F + 256 <= CLOSE_S \/ CLOSE_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 256) CLOSE_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (CLOSE_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 256 /\ CLOSE_S <= x < CLOSE_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F CLOSE_S) as [h3|h3]; [exists CLOSE_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 CLOSE_CID pos x HAR2 Hin);
    [rewrite EFA; change (fs_frame_bytes CLOSE_CID) with 256; lia|].
  apply trans_g_img. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, CLOSE_S in *; cbn [fst snd]; lia]. }
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 CLOSE_CID pos F FL HAR2 Hfrs Hbl2
  HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
(* the model's facts on this path *)
assert (HLB1 : length B1 = Z.to_nat TW.W_LEN) by exact (close_len1_inv B1 (tw_len _ _ _ Htw1)).
destruct (close_ntc_model timg_A TF Bw now Bw' B1 r r Hm Hsent Hst) as (HNT & HNM).
(* +0x1c0 .. +0x1f8: the slot store, s6 = p, shadow bytes 4 .. 12 := 0, the memset's arguments, `jal __asan_memset` *)
pose proof (cn_entry ly2 S2 W2 regs2 mem2 md2 B1 F sp1 HSC HAR2 Htw1 R23 R24 R9 R19 R20 R25 R26 HF0 HF64 HFc HFapp HFG
  ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))
  ltac:(intros a Ha; pose proof HK as (_ & _ & _ & _ & _ & K6); apply K6; lia)) as HS.
set (E0 := cn_E regs2 B1) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, cn_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r0 Hn; unfold E0, cn_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (U23 : bv_unsigned (ew E0 23) = SHADOW_OFF + F / 8)
  by (rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U24 : bv_unsigned (ew E0 24) = F)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E0 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs CN_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ1 SHOK CN_B0.
{ close_awr U23 U24 U9 EFA. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ cn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (cn_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  sn_win Hiw Hx ltac:(cn_wtac U23 U24 U9 Hx). }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (ZS1 : forall i, 4 <= i < 13 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U23.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (sn_chunk0 E0 (w_H W2) (ms_mem ms) (Some 23%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
clear HF HFr HG RG0.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem ms) md1 CLOSE_CID pos HAR1 Hin) as (_ & _ & HFb1 & HFsh1).
rewrite EFA, ESH in HFsh1. change (fs_frame_bytes CLOSE_CID / 8) with 32 in HFsh1.
pmkst HS.
cn_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 48)) Q10 ltac:(cbn [sv_denot]; rewrite U24; reflexivity).
cn_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
cn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 56) Q12 ltac:(reflexivity).
cn_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
cn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 24788)) Q1 ltac:(apply codeptr_val; exact HEI).
cn_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
cn_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x1f8: __asan_memset (p + 16, 0, 56), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (HMS fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 ((CLOSE_CID, pos) :: own) ly2 S2
    md1 (k + e) (F + 48) 0 56 (sp1 - sp0) (Z_to_bv 64 (BASE + 24788)) HGX G_HARNESS_rw HJ1 Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite QSP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
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
    + unfold awr_byte. right; right; right. unfold in_frames. exists CLOSE_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes CLOSE_CID) with 256. lia.
    + lia.
  - apply (amem_range_sub_app F 256); [exact HFapp | lia | lia | lia | lia].
  - apply (frame_ra_zero _ F (F + 48) 56 6 13); [lia | exact DFm8 | lia | lia |].
    intros i Hi. exact (ZS1 i ltac:(lia)).
  - intros _. apply (frame_hull_vis _ F 256 (F + 48) 56); [lia | exact HF64 | reflexivity | lia | lia | lia |].
    intros i Hi. apply can_aview_vis. exact (proj1 (HFsh1 i Hi)).
  - exact I. }
cbv beta. intros Wm c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
assert (DF8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)) as D; rewrite DFm8, Z.add_0_r in D; exact D).
assert (HSHF : SHADOW_OFF + F / 8 + 32 <= F \/ F + 256 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ cn_Z F sp1 a ->
  aview segs (w_H W2) memM a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite HeffM; [exact (KR1 a Ha Hn) | exact Ha | |].
  - intros Hd. apply Hn. right. left. lia.
  - intros Hd. apply Hn. right. right. right. left. lia. }
assert (GAM : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memM a)
  by (intros a Ha; exact (HgrM a (GA1 a Ha))).
jafter_call_keep_hi HS 1024%nat regsM (mrestrict (w_H W2) memM) HPM [0%nat; 1%nat; 2%nat; 3%nat; 4%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 23%nat (SHADOW_OFF + F / 8)); [exact U23 | | exact HgrM].
    intros a Ha. unfold SHADOW_OFF in *. apply HeffM; [lia | destruct HSHF; lia | lia].
  - apply (region_kept_aview _ _ _ _ 24%nat F); [exact U24 | | exact HgrM].
    intros a Ha. apply HeffM; lia.
  - apply sn_rk_none; [| exact HgrM]. intros a Ha. unfold CLOSE_S, TA_g_s in *.
    apply HeffM; [lia | destruct HFG; unfold CLOSE_S, TA_g_s, TW.SZ_g_s in *; lia | lia].
  - apply sn_rk_none; [| exact HgrM]. intros a Ha. unfold CN_SH in *.
    apply HeffM; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
      destruct HFapp as (_ & [HL | (HH1 & HH2)]); lia | lia].
  - apply (region_kept_aview _ _ _ _ 9%nat sp1); [exact U9 | | exact HgrM].
    intros a Ha. apply HeffM; lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regsM) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U23b : bv_unsigned (ew E1 23) = SHADOW_OFF + F / 8) by (rewrite E1lo by lia; exact U23).
assert (U24b : bv_unsigned (ew E1 24) = F) by (rewrite E1lo by lia; exact U24).
assert (U9b : bv_unsigned (ew E1 9) = sp1) by (rewrite E1lo by lia; exact U9).
assert (SHOK1 : sh_ok segs CN_Bx (@nil shent) E1 (mrestrict (w_H W2) memM)) by constructor.
assert (ZMM : forall a, F + 48 <= a < F + 104 -> aview segs (w_H W2) memM a = Some 0).
{ intros a Ha. replace a with ((F + 48) + (a - (F + 48))) by lia. rewrite (HsetM (a - (F + 48)) ltac:(lia)).
  reflexivity. }
clear dependent ms.
(* +0x1fc .. +0x254: the notice's first 16 bytes, the checked store of 3 at s + 112, the checked loads at s + 96 and
   s + 104, up to `jalr a2` *)
paj_run_tok RUN HS HJ2 SHOK1 CN_B0.
{ close_awr U23b U24b U9b EFA. }
set (md3 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md3. clear mat.
assert (KRN : forall a, 0 <= a < 2 ^ 64 -> ~ cn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) memM a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (cn_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  sn_win Hiw Hx ltac:(cn_wtac U23b U24b U9b Hx). }
assert (ZMN : forall a, F + 48 <= a < F + 104 -> aview segs (w_H W2) (ms_mem ms) a = Some 0).
{ intros a Ha. rewrite <- (ZMM a Ha).
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 32 <= x < F + 48) \/ (CLOSE_S + 112 <= x < CLOSE_S + 116) \/
    (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) \/ (sp1 + 24 <= x < sp1 + 32)) HFr); [| lia |].
  - intros b wlo whi x Hiw Hx. cbv beta.
    sn_win Hiw Hx ltac:(rewrite ?U23b, ?U24b, ?U9b in Hx; unfold CLOSE_S, TA_g_s;
      first [lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; lia]).
  - cbv beta. unfold CLOSE_S, TA_g_s, SHADOW_OFF, TW.SZ_g_s in *.
    intros [Hx | [Hx | [Hx | Hx]]]; [lia | destruct HFG as [Hg | Hg]; lia | destruct HSHF as [Hg | Hg]; lia | lia]. }
assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ cn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; rewrite (KRN a Ha Hn); exact (KAM a Ha Hn)).
assert (GAN : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAM a Ha))).
clear HF HFr HG.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS2.
pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RS4.
cbn [ms_mem restrict] in RS0, RS1, RS2, RS4.
assert (ZSN : forall i, 4 <= i < 13 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U23b.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (sn_chunk0 E1 (w_H W2) (ms_mem ms) (Some 23%nat) _ _ _ _ _ _ RS0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
set (old := TW.S_state (close_w1 B1)) in *.
assert (Hold : - 2 ^ 31 <= old < 2 ^ 31) by (unfold old, TW.S_state; apply TWL.s32_range).
assert (D27 : sv_denot E1 (SOff 27 0) = Z_to_bv 64 old).
{ cbn [sv_denot]. rewrite E1lo by lia. rewrite (EE 27%nat 27%bv eq_refl), R27. unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (D13 : sv_denot E1 (SOff 13 0) = w64 r).
{ cbn [sv_denot]. rewrite E1lo by lia. rewrite (EE 13%nat 13%bv eq_refl), R13. unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (sn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 32 8 (SLit 12884901890) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP0.
pose proof (sn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 40 4 (SOff 27 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP8.
pose proof (sn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 44 4 (SLit 8) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP12.
pose proof (sn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 6158896 4 (SLit 3) RS2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG.
pose proof (sn_chunk_val E1 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 24 8 (SOff 13 0) RS4
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VS2.
cbn [base_val] in VP0, VP8, VP12, VG, VS2. rewrite U24b in VP0, VP8, VP12. rewrite U9b in VS2.
rewrite D27 in VP8. rewrite D13 in VS2.
change (N.to_nat 8) with 8%nat in VP0, VS2. change (N.to_nat 4) with 4%nat in VP8, VP12, VG.
change (bv_unsigned (sv_denot E1 (SLit 12884901890)) mod 2 ^ (8 * Z.of_N 8)) with 12884901890 in VP0.
change (bv_unsigned (sv_denot E1 (SLit 8)) mod 2 ^ (8 * Z.of_N 4)) with 8 in VP12.
change (bv_unsigned (sv_denot E1 (SLit 3)) mod 2 ^ (8 * Z.of_N 4)) with 3 in VG.
pose proof (bv_unsigned_in_range 64 (w64 r)) as Hr64. change (bv_modulus 64) with (2 ^ 64) in Hr64.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in VS2. rewrite Z.mod_small in VS2 by exact Hr64.
apply (sn_vm_w _ _ 4 old ltac:(lia)) in VP8.
change (N.to_nat 4) with 4%nat in VP8.
pose proof (close_nb (w_H W2) (ms_mem ms) F old VP0 VP8 VP12 ZMN) as HNB.
(* what the call kept, from its entry to the call of notice *)
assert (NZG : forall x, inG TG.G_HARNESS x -> ~ (CLOSE_S + 112 <= x < CLOSE_S + 116) -> ~ cn_Z F sp1 x).
{ intros x Hx Hn Hz. pose proof (inG_low segs B transport_segs_low _ x HGX Hx) as Hl. unfold kLowMemEnd in Hl.
  destruct Hz as [Hz | [Hz | [Hz | [Hz | Hz]]]].
  - unfold SHADOW_OFF in Hz. lia.
  - apply (N2 x); [left; change (fs_frame_bytes CLOSE_CID) with 256; lia | exact (trans_g_img x Hx)].
  - exact (Hn Hz).
  - lia.
  - lia. }
assert (HSZ : forall a, cn_Z F sp1 a ->
  (spZ regs - CLOSE_STK <= a < spZ regs) \/ dkg_nf CLOSE_CID F FL a \/ inG TG.G_HARNESS a).
{ intros a [Hz | [Hz | [Hz | [Hz | Hz]]]].
  - right; left; right; left. change (fs_frame_bytes CLOSE_CID / 8) with 32. lia.
  - right; left; left. change (fs_frame_bytes CLOSE_CID) with 256. lia.
  - right; right. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
    split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, CLOSE_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
  - left; lia.
  - left; lia. }
pose proof (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2
  (ms_mem ms) (spZ regs - CLOSE_STK) (spZ regs) CLOSE_CID pos F FL (close_wr TF Bw) (cn_Z F sp1) HGX HARc HAR2 Hfrs
  Hbl2 HlyF EF eq_refl FFL ltac:(lia) ltac:(lia) HSZ HK KAN GAN) as KCN.
(* the registers at `jalr a2` *)
assert (E32 : ew E1 32 = Z_to_bv 64 (TI.ti_notice timg_A)).
{ rewrite E1lo by lia. unfold E0, cn_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  pose proof (ew_Ereg_extra regs2 (cn_vals B1) 0) as X. cbn [Nat.add nth cn_vals] in X. rewrite X.
  rewrite <- (close_notify B1 HLB1), HNT. reflexivity. }
cn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (TI.ti_notice timg_A)) T12
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cn_reg HS (Z_to_bv 5 11) (w64 (F + 32)) T11 ltac:(cbn [sv_denot]; rewrite U24b; reflexivity).
cn_reg HS (Z_to_bv 5 2) (w64 sp1) T2
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
cn_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) T3
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
cn_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) T4
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
cn_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 8)) T8
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cn_reg HS (Z_to_bv 5 9) (YK11.getr regs2 (Z_to_bv 5 9)) T9
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cn_reg HS (Z_to_bv 5 18) (YK11.getr regs2 (Z_to_bv 5 18)) T18
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cn_reg HS (Z_to_bv 5 23) (YK11.getr regs2 (Z_to_bv 5 23)) T23
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cn_reg HS (Z_to_bv 5 24) (YK11.getr regs2 (Z_to_bv 5 24)) T24
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
(* +0x258: `jalr a2`, a2 = notice *)
assert (P4 : 0 <= TI.ti_notice timg_A < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
assert (P5 : TI.ti_notice timg_A mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
eapply (SRr_jalr_call_pi (PL := PL_transport) (PI := PI_transport) W2 E1 _ _ _ _ 0x600e7 (1%bv : bv 5) (12%bv : bv 5)
  (TI.ti_notice timg_A) HEI1 HS eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T12 | exact P4 | exact P5 |].
intros matC ms1 Ems1 _. subst ms1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_A) regsC (ms_mem ms) mdC) Qx) end.
assert (EBN : BASE + (24880 + 4) = 0x87398) by (vm_compute; reflexivity).
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (24880 + 4)))
  by (unfold regsC; rewrite YK11.getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc;
      discriminate Hc); reflexivity).
assert (RCK : forall r0 : bv 5, bv_unsigned r0 <> 1 -> YK11.getr regsC r0 = YK11.getr (ms_regs ms) r0)
  by (intros r0 Hr; unfold regsC; apply YK11.getr_other; intros E; apply Hr; rewrite E; reflexivity).
assert (RC2 : YK11.getr regsC 2%bv = w64 sp1) by (rewrite RCK by (vm_compute; discriminate); exact T2).
assert (RC3 : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite RCK by (vm_compute; discriminate); exact T3).
assert (RC4 : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite RCK by (vm_compute; discriminate); exact T4).
assert (RC11 : YK11.getr regsC 11%bv = w64 (F + 32)) by (rewrite RCK by (vm_compute; discriminate); exact T11).
assert (USPC : spZ regsC = sp1) by (unfold spZ; rewrite RC2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARN.
(* notice's premises *)
assert (PTW : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms)) (close_w2 B1)).
{ rewrite close_w2_eq.
  apply (tw_write TMAP_A (aview segs (w_H W2) mem2) _ (close_w1 B1) TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 3 TMAP_A_ok Htw1
    TMAP_A_g_s); [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. unfold aview. replace (TA_g_s + 112 + Z.of_nat j) with (0 + 6158896 + Z.of_nat j)
      by (unfold TA_g_s; lia).
    rewrite (VG j Hj). cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 8) with 256. apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
  - intros x Hx Hn. destruct Hx as (o & b & n & Hin3 & Hx).
    assert (HxG : inG TG.G_HARNESS x).
    { unfold inG. apply Exists_exists. exists (b, n). split; [exact (TMAP_A_in_G o b n Hin3) | unfold in_zr; cbn [fst snd]; lia]. }
    apply KAN; [pose proof (inG_low segs B transport_segs_low _ x HGX HxG); unfold kLowMemEnd in *; lia|].
    apply NZG; [exact HxG | unfold CLOSE_S; cbn [Z.of_nat Pos.of_succ_nat] in Hn; lia]. }
assert (PNTC : trans_ntc_at B ly2 S2 W2 (ms_mem ms) regsC NOTICE_STK (F + 32) (close_ntc B1))
  by exact (close_trans_ntc B ly2 S2 W2 (ms_mem ms) md3 regsC B1 F pos LAWS HARN Hin (eq_sym EFA) HF0 HF64 HFc HFapp
    ltac:(rewrite USPC; lia) ZSN HNB).
assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by (rewrite ESLO, ESHI; lia).
assert (PTF : trans_tframe_at B ly2 S2 W2 (ms_mem ms) regsC NOTICE_STK TF).
{ apply (trans_tframe_at_kept_gx B LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 (ms_mem ms) md3
    (fun a => close_wr TF Bw a \/ inG TG.G_HARNESS a) regs regsC CLOSE_STK NOTICE_STK TF HARc HARN Hbl2 Hfr2 Hfa2
    Elo2 Ehi2 HSTKLT).
  - eapply acall_kept_g_weaken; [|exact KCN]. intros a Ha. left. exact Ha.
  - unfold gx_kept_ex. intros a HaG HnE. exfalso. exact (HnE (or_intror HaG)).
  - intros fr Efr a Ha [Hw | HaG]; [exact (Hapart a Hw fr Efr Ha) | exact (Hoffg fr Efr a Ha HaG)].
  - intros a Ha [Hw | HaG].
    + pose proof (inG_low segs B transport_segs_low _ a HGX (close_wr_G TF Bw a Hw)) as Hl.
      unfold kLowMemEnd in *. lia.
    + pose proof (inG_low segs B transport_segs_low _ a HGX HaG) as Hl. unfold kLowMemEnd in *. lia.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - exact HTF. }
assert (PROM : trans_rom_view_rd W2 (ms_mem ms)).
{ intros a Ha. rewrite <- (Hrom a Ha). pose proof KCN as (_ & _ & K3 & _).
  destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_LO in Gh. lia. }
pose proof (close_ntc_apart B ly2 S2 W2 mem2 md2 W2 (ms_mem ms) TF Bw B1 r F pos LAWS HAR2 Hin (eq_sym EFA) Hapart
  Hsent Hst) as PAP.
assert (PND : TI.n_kind (close_ntc B1) = TC.N_DATA ->
  trans_src_ok B ly2 S2 W2 (ms_mem ms) (TC.OW_dn_body (close_w2 B1) (TW.GOT_ndata (close_w2 B1)))
    (TI.n_body_len (close_ntc B1)) /\
  decode_off_win regsC NOTICE_STK (TC.OW_dn_body (close_w2 B1) (TW.GOT_ndata (close_w2 B1)))
    (TI.n_body_len (close_ntc B1)) /\
  TI.n_body_len (close_ntc B1) < 2 ^ 32).
{ intros HD. exfalso. unfold close_ntc in HD. cbn [TI.n_kind] in HD.
  unfold TS0.DIGINET_N_STATE, TC.N_DATA in HD. discriminate HD. }
assert (PNEV : st_nev S + (k + e) + NOTICE_EV <= EV_MAX) by lia.
eapply SRr_bind.
{ exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((CLOSE_CID, pos) :: own) ly2 S2 W2 (ms_mem ms) mdC (k + e) regsC
    (F + 32) (close_ntc B1) TF (close_w2 B1) Bw'
    ltac:(apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ2)
    ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia)
    RC3 RC4 RC11
    ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; destruct Hsp1 as (_ & M1);
          rewrite M1, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
          apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    PNTC PTF PROM PTW HNM PAP PND PNEV). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3).
assert (He30 : e3 = 0) by lia. subst e3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
assert (EF3 : frame_addr ly3 CLOSE_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF3c; reflexivity).
assert (Hin3 : In (CLOSE_CID, pos) (frames S3)) by (rewrite Hfr3; exact Hin).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md4 CLOSE_CID pos HAR3 Hin3) as (_ & _ & _ & HFsh3).
rewrite EF3 in HFsh3. change (fs_frame_bytes CLOSE_CID / 8) with 32 in HFsh3. rewrite ESH in HFsh3.
assert (Hfrs3 : frames S3 = (CLOSE_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3))
  by (intros bm Hbm; eapply Permutation_in; [apply Permutation_sym; exact Hperm3 | exact (Hbl2 bm Hbm)]).
assert (R3_23 : YK11.getr regs3 (Z_to_bv 5 23) = w64 (SHADOW_OFF + F / 8)).
{ rewrite (HP3 23 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). rewrite T23. exact R23. }
assert (R3_9 : YK11.getr regs3 (Z_to_bv 5 9) = w64 sp1).
{ rewrite (HP3 9 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). rewrite T9. exact R9. }
(* what the call kept, from its entry to notice's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - CLOSE_STK) (spZ regs)
  (close_wr TF Bw)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 (ms_mem ms) W3 mem3
    (spZ regs - CLOSE_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (close_wr TF Bw)
    (notice_wr (close_w2 B1) (close_ntc B1)) (dkg_nf CLOSE_CID F FL)).
  - lia.
  - lia.
  - exact Hfa2.
  - exact Hfr2.
  - exact Hbl2.
  - exact N1.
  - exact N3.
  - exact KCN.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. right. right. exists B1, r. split; [exact Hsent|]. split; [exact Hst | right; exact Ha]. }
(* the slot still holds r at notice's return: it lies above notice's window *)
pose proof HK3 as (K31 & _ & _ & K34 & _).
rewrite USPC in K31.
assert (VS3 : val_mem segs (mrestrict (w_H W3) mem3) (sp1 + 24) 8 (bv_unsigned (w64 r))).
{ apply (close_vm_kept (w_H W2) (w_H W3) (ms_mem ms) mem3 (sp1 + 24) 8 _); [|exact VS2].
  intros j Hj. apply K31; lia. }
(* +0x25c .. +0x28c: shadow bytes 4 .. 12 := 0xf8, a3 = r from the slot, to the release cut *)
rewrite RC1. change (Z_to_bv 64 (BASE + (24880 + 4))) with (Z_to_bv 64 (BASE + (CLOSE_NTC + 0x9c))).
pose proof (cn_entry3 W3 regs3 mem3 F sp1 r R3_23 R3_9 HF0 HF64 HFc ltac:(lia) ltac:(lia) ltac:(destruct Hsp1; lia)
  ltac:(intros i Hi; exact (proj1 (HFsh3 i ltac:(lia)))) VS3) as HS3.
set (E3 := Eimg (PI := PI_transport) (Ereg regs3 [w64 r])) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (EE3 : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E3 n = YK11.getr regs3 r0)
  by (intros n r0 Hn; unfold E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U23c : bv_unsigned (ew E3 23) = SHADOW_OFF + F / 8)
  by (rewrite (EE3 23%nat (Z_to_bv 5 23) eq_refl), R3_23; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U9c : bv_unsigned (ew E3 9) = sp1)
  by (rewrite (EE3 9%nat (Z_to_bv 5 9) eq_refl), R3_9; unfold w64; apply unsigned_lit_small; lia).
assert (E32c : ew E3 32 = w64 r)
  by (unfold E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 [w64 r] 0)).
assert (SHOK3 : sh_ok segs CN_Bx (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 CN_B0 CLOSE_REL.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply awr_ok_x_cons_own with (cid := CLOSE_CID); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23c in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF3. change (fs_frame_bytes CLOSE_CID / 8) with 32. lia.
  - apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms4 end.
assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 13) ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(rewrite ?U23c, ?U9c in Hx; lia). }
assert (GA4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KC4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (ms_mem ms4) (spZ regs - CLOSE_STK) (spZ regs)
  (close_wr TF Bw)).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly3 S3 W memc mdc W3 mem3 md4 mem3
    (ms_mem ms4) (spZ regs - CLOSE_STK) (spZ regs) CLOSE_CID pos F FL (close_wr TF Bw)
    (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) HGX HARc HAR3 Hfrs3 Hbl3 ELF3c EF eq_refl FFL
    ltac:(lia) ltac:(lia)); [| exact KC3 | exact KR4 | exact GA4].
  intros a Ha. right. left. right. left. change (fs_frame_bytes CLOSE_CID / 8) with 32. cbv beta in Ha. lia. }
pmkst HS3.
(* the registers the release reads *)
cn_reg HS3 (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) F2
  ltac:(cbn [sv_denot]; rewrite (EE3 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cn_reg HS3 (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) F3
  ltac:(cbn [sv_denot]; rewrite (EE3 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cn_reg HS3 (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) F4
  ltac:(cbn [sv_denot]; rewrite (EE3 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cn_reg HS3 (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) F8
  ltac:(cbn [sv_denot]; rewrite (EE3 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cn_reg HS3 (Z_to_bv 5 9) (YK11.getr regs3 (Z_to_bv 5 9)) F9
  ltac:(cbn [sv_denot]; rewrite (EE3 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cn_reg HS3 (Z_to_bv 5 18) (YK11.getr regs3 (Z_to_bv 5 18)) F18
  ltac:(cbn [sv_denot]; rewrite (EE3 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cn_reg HS3 (Z_to_bv 5 23) (YK11.getr regs3 (Z_to_bv 5 23)) F23
  ltac:(cbn [sv_denot]; rewrite (EE3 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cn_reg HS3 (Z_to_bv 5 24) (YK11.getr regs3 (Z_to_bv 5 24)) F24
  ltac:(cbn [sv_denot]; rewrite (EE3 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cn_reg HS3 (Z_to_bv 5 13) (w64 r) F13
  ltac:(cbn [sv_denot]; rewrite E32c, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
(* the bytes the release reads: the saved words above sp1 and the frame's last word *)
assert (KSTK : forall a, sp1 + 32 <= a < spZ regs -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite KR4 by (unfold SHADOW_OFF; lia). rewrite K31 by lia.
  apply KAN; [lia|]. unfold cn_Z, CLOSE_S, TA_g_s, SHADOW_OFF. lia. }
assert (KFL : forall i, 0 <= i < 8 ->
  aview segs (w_H W3) (ms_mem ms4) (F + 248 + i) = aview segs (w_H W2) mem2 (F + 248 + i)).
{ intros i Hi. rewrite KR4 by (unfold SHADOW_OFF in *; destruct HSHF; lia).
  rewrite (K34 CLOSE_CID pos (F + 248 + i) Hin).
  - apply KAN; [lia|]. unfold cn_Z, CLOSE_S, TA_g_s, SHADOW_OFF in *.
    intros [Hz | [Hz | [Hz | [Hz | Hz]]]];
      [destruct HSHF; lia | lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia | lia | lia].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes CLOSE_CID) with 256. lia.
  - intros Hw. pose proof (close_nwr_G (close_w2 B1) (close_ntc B1) (F + 248 + i) eq_refl Hw) as Hg.
    apply (N2 (F + 248 + i)); [left; change (fs_frame_bytes CLOSE_CID) with 256; lia | exact (trans_g_img _ Hg)]. }
assert (HSo : forall o, In o CLOSE_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold CLOSE_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
apply (REL LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ly3 S3 W3
  (ms_mem ms4) md5 e (ms_regs ms4) HFIX).
- split; [|split].
  + split; [replace (k + e) with (k + e + 0) by lia; exact HJ3|].
    split; [exact He0|].
    split; [exact Hfrs3|].
    split; [eapply Permutation_trans; [exact Hperm3 | exact Hperm]|].
    split; [exact ELF3c|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
    split; [exact KC4|].
    split.
    * rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia.
    * unfold CLOSE_FBYTES. change (flag_addr lyc CLOSE_CID pos) with FL. rewrite <- HFLw.
      replace (F + 256 - 8) with (F + 248) by lia.
      apply rdword_ext. intros i Hi. exact (KFL i Hi).
  + apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw3|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR4; [lia | unfold SHADOW_OFF; lia].
  + rewrite (close_gfn' TF B1 Bw' HLB1 HNM). exact Hgf1.
- assert (CH : forall n, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) <> 1 ->
    YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms) (Z_to_bv 5 n))
    by (intros n Hn H1; rewrite (HP3 n Hn); exact (RCK _ H1)).
  split; [|exact F13].
  split; [exact (eq_trans F2 (eq_trans (CH 2 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T2))|].
  split; [exact (eq_trans F3 (eq_trans (CH 3 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T3 (eq_sym Hgp))))|].
  split; [exact (eq_trans F4 (eq_trans (CH 4 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T4 (eq_sym Htp))))|].
  split; [exact (eq_trans F8 (eq_trans (CH 8 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T8 R8)))|].
  split; [exact (eq_trans F9 (eq_trans (CH 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T9 R9)))|].
  split; [exact (eq_trans F18 (eq_trans (CH 18 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T18 R18)))|].
  split; [exact (eq_trans F23 (eq_trans (CH 23 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T23 R23)))|].
  exact (eq_trans F24 (eq_trans (CH 24 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T24 R24))).
Qed.

End n.
