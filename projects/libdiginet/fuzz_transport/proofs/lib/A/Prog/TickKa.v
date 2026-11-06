(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v; 239 of its 325 lines of code are new or changed and 1124 lines of the source are left out. *)
(* TickKa: the keepalive piece of the image-A walk of diginet_session_tick, tick_ka : tick_ka_stmt (TickCut.v), code
   +0x8d8 .. +0x968 (0x89b90 .. 0x89c20), from the keepalive cut tick_ka_at to the epilogue cut tick_epi_at.
   Run A (PaRun token engine, from TickKa_kit.v tka_entryA) marks ka usable (shadow byte 46 := 1), stores 0 at ka
   (frame + 368), checks and loads g_s.cfg.keepalive_ms (s + 24), forms a4 = next_keepalive_us + ms and loads now from
   s1 + 56; it stops at the keepalive test `bltu a5, a4` (+0x910), which is split (DgnTransportPaLib.v paj_branch):
   taken, a4 is the first sum (tka_br1); not taken, run B (+0x914 .. +0x918) makes it ms + now (tka_br2); either way
   a4 is TickKa_kit.v tka_vk, the value the model's two stores of :451-453 leave. At the join (+0x91c) the bytes the
   runs wrote (ka's shadow byte and ka) and the registers are handed to TickKa_rest.v tka_rest, which stores
   next_keepalive_us and stats.tx_keepalives, calls send_data and ends at the epilogue cut. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg session_lost_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg TickCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import SlostNtcKit SlostNtc TickKa_kit TickKa_rest.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
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

(* The write rights of a run from a state with the regions of ss_tkaA: ka's shadow byte and ka (own frame), the
   others read-only. *)
Ltac tka_awrA U19 U27 EF2 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EF2; change (fs_frame_bytes TICK_CID / 8) with 256; lia |];
  eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U27 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite EF2; change (fs_frame_bytes TICK_CID) with 2048; lia |];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* A register of a computed symbolic state, its symbolic value computed. *)
Ltac tka_sr :=
  cbv beta;
  lazymatch goal with |- sv_denot ?E (sr_get ?l ?q) = ?v =>
    let e := eval vm_compute in (sr_get l q) in change (sv_denot E e = v) end.
(* An unchanged register: its value at the run's entry. *)
Ltac tka_ru EE :=
  cbn [sv_denot];
  lazymatch goal with |- context [ew _ ?n] => rewrite (EE n (Z_to_bv 5 (Z.of_nat n)) eq_refl) end;
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity.

(* The two sums the code forms in a4 (+0x908: next_keepalive_us + ms; +0x918: ms + now), modulo 2 ^ 64: the model's
   u64 of the sum, with ms_m of the 4-byte load (atom 32). *)
Lemma tka_sumA : forall E nk ka, ew E 32 = Z_to_bv 64 ka -> ew E 14 = Z_to_bv 64 nk ->
  0 <= ka < 2 ^ 32 -> 0 <= nk < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 14 0) (SMd M_MUL (SOff 32 0) (SLit 1000)))) =
  TS0.u64 (nk + TS0.ms_m ka).
Proof.
  intros E nk ka H32 H14 Rk Rn. cbn [sv_denot alu64 alu mul_div].
  rewrite H32, H14. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
  rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned.
  unfold TS0.ms_m, bv_wrap, TS0.u64. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small nk (2 ^ 64)), (Z.mod_small ka (2 ^ 64)), (Z.mod_small 1000 (2 ^ 64)) by lia.
  rewrite (Z.mod_small (ka * 1000) (2 ^ 64)) by lia. reflexivity.
Qed.

Lemma tka_sumB : forall E now ka, ew E 32 = Z_to_bv 64 ka -> ew E 33 = Z_to_bv 64 now ->
  0 <= ka < 2 ^ 32 -> 0 <= now < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit 1000)) (SOff 33 0))) =
  TS0.u64 (now + TS0.ms_m ka).
Proof.
  intros E now ka H32 H33 Rk Rn. cbn [sv_denot alu64 alu mul_div].
  rewrite H32, H33. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
  rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned.
  unfold TS0.ms_m, bv_wrap, TS0.u64. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small now (2 ^ 64)), (Z.mod_small ka (2 ^ 64)), (Z.mod_small 1000 (2 ^ 64)) by lia.
  rewrite (Z.mod_small (ka * 1000) (2 ^ 64)) by lia. rewrite (Z.add_comm (ka * 1000) now). reflexivity.
Qed.

(* The keepalive test `bltu a5, a4` (+0x910, a5 = now) taken: now is below the first sum, which a4 keeps, and which is
   the model's tka_vk. *)
Lemma tka_br1 : forall E B0 now, ew E 32 = Z_to_bv 64 (TW.S_cfg_keepalive_ms B0) ->
  ew E 14 = Z_to_bv 64 (TW.S_next_keepalive_us B0) -> ew E 33 = Z_to_bv 64 now -> 0 <= now < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff 33 0))
    (sv_denot E (SAlu ALU_ADD (SOff 14 0) (SMd M_MUL (SOff 32 0) (SLit 1000)))) = true ->
  sv_denot E (SAlu ALU_ADD (SOff 14 0) (SMd M_MUL (SOff 32 0) (SLit 1000))) = w64 (tka_vk B0 now).
Proof.
  intros E B0 now H32 H14 H33 Rn Hc.
  pose proof (TWL.u_at_range B0 TW.A_S_cfg_keepalive_ms 4) as Rk. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Rk.
  pose proof (TWL.u_at_range B0 TW.A_S_next_keepalive_us 8) as Rx. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rx.
  pose proof (tka_sumA E (TW.S_next_keepalive_us B0) (TW.S_cfg_keepalive_ms B0) H32 H14 Rk Rx) as U.
  assert (U33 : bv_unsigned (sv_denot E (SOff 33 0)) = now)
    by (cbn [sv_denot]; rewrite H33, (unsigned_lit_small now) by exact Rn; rewrite Z.add_0_r;
        apply unsigned_lit_small; exact Rn).
  cbn [branch_taken] in Hc. unfold bv_ltu in Hc. rewrite U33, U in Hc. apply Z.ltb_lt in Hc.
  unfold tka_vk. rewrite (proj2 (Z.leb_gt (tka_v1 B0) now) Hc).
  apply bv_eq. unfold w64. rewrite U, unsigned_lit_small; [reflexivity|].
  unfold tka_v1, TS0.u64. apply Z.mod_pos_bound. lia.
Qed.

(* Not taken: the first sum is at most now, and a4 is the second sum (+0x914 .. +0x918), the model's tka_vk. *)
Lemma tka_br2 : forall E B0 now, ew E 32 = Z_to_bv 64 (TW.S_cfg_keepalive_ms B0) ->
  ew E 14 = Z_to_bv 64 (TW.S_next_keepalive_us B0) -> ew E 33 = Z_to_bv 64 now -> 0 <= now < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff 33 0))
    (sv_denot E (SAlu ALU_ADD (SOff 14 0) (SMd M_MUL (SOff 32 0) (SLit 1000)))) = false ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit 1000)) (SOff 33 0)) = w64 (tka_vk B0 now).
Proof.
  intros E B0 now H32 H14 H33 Rn Hc.
  pose proof (TWL.u_at_range B0 TW.A_S_cfg_keepalive_ms 4) as Rk. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Rk.
  pose proof (TWL.u_at_range B0 TW.A_S_next_keepalive_us 8) as Rx. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rx.
  pose proof (tka_sumA E (TW.S_next_keepalive_us B0) (TW.S_cfg_keepalive_ms B0) H32 H14 Rk Rx) as U.
  pose proof (tka_sumB E now (TW.S_cfg_keepalive_ms B0) H32 H33 Rk Rn) as U2.
  assert (U33 : bv_unsigned (sv_denot E (SOff 33 0)) = now)
    by (cbn [sv_denot]; rewrite H33, (unsigned_lit_small now) by exact Rn; rewrite Z.add_0_r;
        apply unsigned_lit_small; exact Rn).
  cbn [branch_taken] in Hc. unfold bv_ltu in Hc. rewrite U33, U in Hc. apply Z.ltb_ge in Hc.
  unfold tka_vk. rewrite (proj2 (Z.leb_le (tka_v1 B0) now) Hc).
  apply bv_eq. unfold w64. rewrite U2, unsigned_lit_small; [reflexivity|].
  unfold TS0.u64. apply Z.mod_pos_bound. lia.
Qed.

Section ka. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma tka_main : @tick_ka_stmt fx rc B MT.
Proof.
unfold tick_ka_stmt. intros EPI. unfold tick_ka_at.
intros LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F B0 ly2 S2 W2
  mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGN).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw & Hgf & Hm & HTF & Hrom &
  Hap & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (((HJ1 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hnw) & Htw0 & Hgf0 & Hinv0 & Hm0).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R22 & R23 & R24 & R25) & R13 & R14 & R17).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TICK_FBYTES in HFc, HFapp, HFLw.
assert (He0 : e = 0) by (unfold TICK_EV in He; lia). subst e.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite ?Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HSS : TICK_STK = 208 + SENDDATA_STK) by reflexivity.
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
assert (Hin : In (TICK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EF2 : frame_addr ly2 TICK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 TICK_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
rewrite EF2 in HFb, HFsh.
change (fs_frame_bytes TICK_CID) with 2048 in HFb. change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity. rewrite ESH in HFsh.
assert (HFG : F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 2048) TICK_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (TICK_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 2048 /\ TICK_S <= x < TICK_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F TICK_S) as [h3|h3]; [exists TICK_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 TICK_CID pos x HAR2 Hin);
    [rewrite EF2; change (fs_frame_bytes TICK_CID) with 2048; lia|].
  apply trans_g_img. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, TICK_S in *; cbn [fst snd]; lia]. }
(* run A, +0x8d8 .. +0x90c: ka's shadow byte := 1, ka := 0, the check of s + 24, a4 = ms + next_keepalive_us, a5 =
   now; it stops at the keepalive test `bltu a5, a4` (+0x910) *)
pose proof (tka_entryA B ly2 S2 W2 regs2 mem2 md2 B0 now sp1 F HTC HAR2 Htw0 R9 R19 R27 R20 R24 (proj1 Hsp47)
  (proj2 Hsp47)
  (proj2 Hsp1) HF0 HF64 ltac:(lia) HFapp HFG ltac:(lia) (proj1 (HFb (F + 368) ltac:(lia)))
  (proj1 (HFsh 46 ltac:(lia))) Hnow Hnw) as HS.
set (E0 := tka_E regs2 (tka_valsA B0 now)) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, tka_E; apply Eimg_env).
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E0 n = YK11.getr regs2 q)
  by (intros n q Hn; unfold E0, tka_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U19 : bv_unsigned (ew E0 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small;
      pose proof (Z.div_le_upper_bound F 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E0 27) = F)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs TKA_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
paj_run_tok RUN HS HJ1 SHOK TKA_B0.
{ tka_awrA U19 U27 EF2. }
set (mdA := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdA. clear mat.
rename ms into msA.
assert (KRA : forall a, 0 <= a < 2 ^ 64 -> ~ tka_Z F a ->
  aview segs (w_H W2) (ms_mem msA) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (tka_Z F) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hiw Hx. cbv beta.
  sn_win Hiw Hx ltac:(rewrite ?U19, ?U27 in Hx; unfold tka_Z; first [lia | left; lia | right; lia]). }
assert (GAA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msA) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
pose proof (TWL.u_at_range B0 TW.A_S_cfg_keepalive_ms 4) as Rk. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Rk.
assert (EX : forall j, (j < 2)%nat -> ew E0 (32 + j) = nth j (tka_valsA B0 now) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, tka_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
cbn [Nat.add nth tka_valsA] in E32, E33.
assert (E14 : ew E0 14 = Z_to_bv 64 (TW.S_next_keepalive_us B0))
  by (rewrite (EE 14%nat 14%bv eq_refl), R14; reflexivity).
(* At +0x91c, from a run that started at msA (run B: the branch, and on its fall-through the second sum): the bytes
   the runs from the cut wrote, the registers tka_rest reads, then tka_rest. a4 is V14's. *)
assert (JOIN : forall ss ms mdB, sv_denot E0 (sr_get (ss_regs ss) (Z_to_bv 5 14)) = w64 (tka_vk B0 now) ->
  ss_pc ss = TKA_C -> ss_resv ss = None ->
  st_ok_pi segs VAL E0 ss (restrict (w_H W2) ms) ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 19%nat) 46 47 46 47 [YP09.mkChunk 46 (YP09.CVal 1 (SLit 1))]) ->
  nth_error (ss_mem ss) 1 = Some (YP09.mkRegion (Some 27%nat) 368 369 368 369 [YP09.mkChunk 368 (YP09.CVal 1 (SLit 0))]) ->
  Forall (fun n : Z => sv_denot E0 (sr_get (ss_regs ss) (Z_to_bv 5 n)) = YK11.getr regs2 (Z_to_bv 5 n))
    [2; 3; 4; 8; 9; 13; 17; 18; 19; 22; 23; 25; 27] ->
  sv_denot E0 (sr_get (ss_regs ss) (Z_to_bv 5 11)) = w64 (F + 368) ->
  sv_denot E0 (sr_get (ss_regs ss) (Z_to_bv 5 20)) = w64 TICK_S ->
  sv_denot E0 (sr_get (ss_regs ss) (Z_to_bv 5 24)) = w64 SHADOW_OFF ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((TICK_CID, pos) :: own) ly2 S2 W2 (ms_mem ms) mdB (k + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ tka_Z F a -> aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a) ->
  SRr segs W2 (mkCfg ms mdB) (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r)).
{ intros ss ms mdB V14 Hpc Hrv HSx R0 R1 RU R11 R20' R24' HJx KRx GAx.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HSx R0) as RS0.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HSx R1) as RS1.
  cbn [ms_mem restrict] in RS0, RS1.
  pose proof (sn_chunk_val E0 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 46 1 (SLit 1) RS0
    ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as V46.
  cbn [base_val] in V46. rewrite U19 in V46.
  change (bv_unsigned (sv_denot E0 (SLit 1)) mod 2 ^ (8 * Z.of_N 1)) with 1 in V46.
  change (N.to_nat 1) with 1%nat in V46.
  pose proof (tka_vm_aview _ _ _ 1 V46 ltac:(lia)) as SH46.
  pose proof (sn_chunk0 E0 (w_H W2) (ms_mem ms) (Some 27%nat) _ _ _ _ _ _ RS1 ltac:(cbn [In]; left; reflexivity)) as KA0.
  cbn [base_val] in KA0. rewrite U27 in KA0.
  assert (RG : forall q, YK11.getr (ms_regs ms) q = sv_denot E0 (sr_get (ss_regs ss) q))
    by (intros q; exact (st_ok_pi_restrict_reg (w_H W2) E0 ss ms q HSx)).
  assert (RK : forall n, In n [2; 3; 4; 8; 9; 13; 17; 18; 19; 22; 23; 25; 27] ->
    YK11.getr (ms_regs ms) (Z_to_bv 5 n) = YK11.getr regs2 (Z_to_bv 5 n))
    by (intros n Hn; rewrite RG; exact (proj1 (Forall_forall _ _) RU n Hn)).
  assert (HRR : tick_regs_run regs (ms_regs ms) sp1 F).
  { split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|split; [|split; [|split; [|split; [|split]]]]].
    - exact (eq_trans (RK 2 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R2).
    - exact (eq_trans (RK 3 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R3).
    - exact (eq_trans (RK 4 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R4).
    - exact (eq_trans (RK 8 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R8).
    - exact (eq_trans (RK 9 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R9).
    - exact (eq_trans (RK 18 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R18).
    - exact (eq_trans (RK 27 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R27).
    - exact (eq_trans (RK 19 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R19).
    - exact (eq_trans (RG _) R20').
    - exact (eq_trans (RK 22 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R22).
    - exact (eq_trans (RK 23 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R23).
    - exact (eq_trans (RG _) R24').
    - exact (eq_trans (RK 25 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R25). }
  pose proof (st_ok_pi_restrict_mkst (w_H W2) E0 ss ms HSx Hrv) as Hms. rewrite Hpc in Hms. rewrite Hms.
  exact (tka_rest B MT LAWS0 CALLS EPI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos
    sp1 F B0 ly2 S2 W2 mem2 md2 0 (ms_mem ms) mdB (ms_regs ms) HFIX HCUR HJx KRx GAx SH46 KA0 HRR
    (eq_trans (RG _) R11) (eq_trans (RK 13 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R13)
    (eq_trans (RG _) V14) (eq_trans (RK 17 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R17)). }
psrr_branch_tok RUN BR HS SHOK TKA_B0.
- (* now < next_keepalive_us + ms: a4 keeps the first sum; `bltu` to +0x91c *)
  pose proof (tka_br1 E0 B0 now E32 E14 E33 Hnow Hc) as V14. clear Hc.
  paj_run_to_tok RUNTO HS HJ1 SHOK TKA_B0 TKA_C.
  { tka_awrA U19 U27 EF2. }
  set (mdB := with_vm_backing (m_vm_lazy mdA) mat mdA) in *. clearbody mdB. clear mat.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => apply (JOIN ssx ms mdB) end.
  + tka_sr. exact V14.
  + reflexivity.
  + reflexivity.
  + exact HS.
  + reflexivity.
  + reflexivity.
  + repeat (apply Forall_cons; [tka_sr; tka_ru EE|]). apply Forall_nil.
  + tka_sr. cbn [sv_denot]. rewrite U27. reflexivity.
  + tka_sr. reflexivity.
  + tka_sr. reflexivity.
  + exact HJ1.
  + intros a Ha Hn. rewrite <- (KRA a Ha Hn). apply (kept_of_frame _ _ _ _ _ (tka_Z F) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hiw Hx. cbv beta.
    sn_win Hiw Hx ltac:(rewrite ?U19, ?U27 in Hx; unfold tka_Z; first [lia | left; lia | right; lia]).
  + intros a Ha. exact (apresent_grows _ _ _ a HG (GAA a Ha)).
- (* else: a4 = now + ms (+0x914 .. +0x918) *)
  pose proof (tka_br2 E0 B0 now E32 E14 E33 Hnow Hc) as V14. clear Hc.
  paj_run_to_tok RUNTO HS HJ1 SHOK TKA_B0 TKA_C.
  { tka_awrA U19 U27 EF2. }
  set (mdB := with_vm_backing (m_vm_lazy mdA) mat mdA) in *. clearbody mdB. clear mat.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => apply (JOIN ssx ms mdB) end.
  + tka_sr. exact V14.
  + reflexivity.
  + reflexivity.
  + exact HS.
  + reflexivity.
  + reflexivity.
  + repeat (apply Forall_cons; [tka_sr; tka_ru EE|]). apply Forall_nil.
  + tka_sr. cbn [sv_denot]. rewrite U27. reflexivity.
  + tka_sr. reflexivity.
  + tka_sr. reflexivity.
  + exact HJ1.
  + intros a Ha Hn. rewrite <- (KRA a Ha Hn). apply (kept_of_frame _ _ _ _ _ (tka_Z F) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hiw Hx. cbv beta.
    sn_win Hiw Hx ltac:(rewrite ?U19, ?U27 in Hx; unfold tka_Z; first [lia | left; lia | right; lia]).
  + intros a Ha. exact (apresent_grows _ _ _ a HG (GAA a Ha)).
Qed.
End ka.

(* The keepalive piece of the walk (TickCut.v tick_ka_stmt). *)
Theorem tick_ka : forall fx rc B MT, @tick_ka_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@tka_main fx rc B MT). Qed.

Print Assumptions tick_ka.
