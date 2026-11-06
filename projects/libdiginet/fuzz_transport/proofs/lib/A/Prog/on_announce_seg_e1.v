(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 629 of its 718 lines of code are new or changed and 676 lines of the source are left out. *)
(* on_announce_seg_e1: Theorem onann_piece_e1 : forall fx rc B MT, @onann_e1_stmt fx rc B MT (lib/A/Prog/OnannCut.v
   section 8), the e1 piece of the image-A walk of on_announce: code +0x548 .. +0x588 of the listing
   lib/A/Prog/DgnTransportList.v (fuzz_transport.asan 0x87fbc .. 0x87ffc), from the e1 cut (onann_e1_at, +0x548) to
   the foreign cut onann_fn_at (+0x58c) or to the release cut onann_nrel_at (+0x764), the two cut statements the piece
   is given.

   What the code does (diginet_session.c:209-214). +0x548 `srli a1, a0, 3`, +0x54c `add a1, a1, s8`: a1 = the shadow
   byte of s + 136 (a0 = s + 136, s8 = the shadow base, onann_regs_e1); +0x550 `bltz s7`: s7 = off, find_mac's
   result, sign-extended (-1 <= off < 11, oe1_off_range).
     off < 0: the branch goes to the foreign cut +0x58c with a1 = the shadow byte of s + 136; the model is the else
       branch of onann_k_e1 (onann_k_fn at set_S_foreign B2 1, oe1_k_neg); world B2, a and the spill slots unchanged.
     0 <= off: +0x554 `lb a1, 0(a1)`, `bnez a1` (g_s's payload lies in the record's zero shadow, on_announce_cg.v
       trans_onann_cells, read by DgnTransportCg.v decode_zshadow_rd), +0x55c `sw zero, 136(s4)` (:211,
       set_S_foreign B2 0), +0x560 .. +0x574 the check of s + 140 (the same shadow byte: g_s is 8-aligned) and
       `ld s7, 40(s1)` (the frame F, onann_slot sp1 40), +0x578 / +0x57c the store of 1 at s + 140 (:212,
       set_S_e1_named_us), +0x580 `mv a0, s4`, +0x584 `jal maybe_online` (:213), +0x588 `j +0x764`.
   Three runs of the engine over the caller's G journal (lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x):
     run A (+0x548 .. the `bltz`, a0 and s8 pinned, no region): DgnTransportPaLib.v paj_branch splits on
       bv_lts off 0 (oe1_lts); each arm runs the branch, to +0x58c or to +0x554, and writes nothing;
     run B (+0x554 .. `jal maybe_online`, a1, s4 and s8 pinned): the shadow byte of [s + 136, s + 144), read (0); the
       eight bytes [s + 136, s + 144), written (bytes of G, W_journalG.v awr_ok_x_cons_g); the spill slot sp1 + 40 at
       s1, read (s2's value, the frame);
     run C (+0x588 `j`, no region), after maybe_online, to the release cut.
   maybe_online: maybe_online_cg.v transport_maybe_online_cg at transport_sigma TS_maybe_online (onann_callees), in the
   same G journal: ra = +0x588, a0 = s, sp = sp1 (32-aligned, sp1 >= sp - 208, ONANN_STK = 208 + WAKE_STK and
   MAYBEON_STK <= WAKE_STK); tw_at at set_S_e1_named_us (set_S_foreign B2 0) 1 (two TWorldG.v tw_write, through a view
   that holds the first store only); g_fail_next (oe1_gfn); the model premise (oe1_k_pos); trans_tframe_at TF at
   MAYBEON_STK and trans_rom_view_rd from on_announce's at its entry across what the walk kept
   (on_announce_seg_kit.v onann_tf_call, onann_rom_call); maybeon_apart (on_announce_seg_kit.v onann_apart_mo: the
   desk notice's store of GOT.desk changes none of the fields maybeon_wr reads, so its range is row 8 of onann_wr);
   count_cid 2 at the call state (the own frame is of class 4) from onann_fix's + 2 premise; no event.
   The release cut's state: the journal, frames, blocks and meter of maybe_online's post; what the call keeps: the
   cut's acall_kept_g over run B (TransportGFrame.v dk_kept_step_gw: [s + 136, s + 144) are rows 4 and 7 of onann_wr,
   oe1_st_wr), then maybe_online's (TransportGCg.v dk_kept_trans_nf_g, its written range inside onann_wr,
   on_announce_seg_kit.v onann_wr_mo); the saved words (above maybe_online's window) and the frame's last word (a
   frame byte, not a byte of G) kept; tw_at at Bw' and g_fail_next Bw' <= 1 from maybe_online's post; s7 = F (loaded
   before the call, kept by it). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model on this path                                           *)
(* ------------------------------------------------------------------ *)

(* find_mac's loop answers -1 or an index below i + fuel (as lib/TSim/RxAnn1.v ann1_find_mac_loop_range). *)
Lemma oe1_fml_range : forall u mac fuel i, 0 <= i ->
  -1 <= TSS.find_mac_loop u mac i fuel < i + Z.of_nat fuel + 1.
Proof.
intros u mac fuel. induction fuel as [|f IH]; intros i Hi; cbn [TSS.find_mac_loop].
- lia.
- match goal with |- context [if ?c then _ else _] => destruct c end; [lia|].
  specialize (IH (i + 1) ltac:(lia)). lia.
Qed.

(* off, find_mac's result or -1, lies in [-1, 11): `bltz s7` on its 64-bit sign extension is off < 0. *)
Lemma oe1_off_range : forall Bx b, -1 <= onann_off Bx b < 11.
Proof.
intros Bx b. unfold onann_off.
match goal with |- context [if ?c then _ else _] => destruct c end; [|lia].
unfold TSS.find_mac_m.
match goal with |- context [TSS.find_mac_loop ?u ?m 0 ?f] =>
  pose proof (oe1_fml_range u m f 0 (Z.le_refl 0)) as H;
  assert (Hf : Z.of_nat f = 10) by (vm_compute; reflexivity) end.
lia.
Qed.

(* `bltz`: the signed comparison of two values in the 64-bit signed range. *)
Lemma oe1_lts : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
rewrite !bv_swrap_small; [reflexivity | change (bv_half_modulus 64) with (2^63); lia
                          | change (bv_half_modulus 64) with (2^63); lia].
Qed.

(* The two arms of :209 (OnannCut.v onann_k_e1). *)
Lemma oe1_k_pos : forall (I : TI.timg) (Fr : option TI.tframe) B2 off b Bw', 0 <= off ->
  onann_k_e1 I Fr B2 off b = Some (Bw', tt) ->
  TSS.maybe_online_m I Fr (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1) = Some (Bw', tt).
Proof.
intros I Fr B2 off b Bw' Ho H. unfold onann_k_e1 in H. rewrite (proj2 (Z.leb_le 0 off) Ho) in H. exact H.
Qed.

Lemma oe1_k_neg : forall (I : TI.timg) (Fr : option TI.tframe) B2 off b Bw', off < 0 ->
  onann_k_e1 I Fr B2 off b = Some (Bw', tt) -> onann_k_fn I Fr (TW.set_S_foreign B2 1) b = Some (Bw', tt).
Proof.
intros I Fr B2 off b Bw' Ho H. unfold onann_k_e1 in H. rewrite (proj2 (Z.leb_gt 0 off) Ho) in H. exact H.
Qed.

(* The stores of :211 and :212 at their numeral offsets. *)
Lemma oe1_fg_eq : forall Bx v, TW.set_S_foreign Bx v = TW.upd Bx (TW.OFF_g_s + 136) (TW.put 4 v).
Proof. intros Bx v. reflexivity. Qed.
Lemma oe1_e1_eq : forall Bx v, TW.set_S_e1_named_us Bx v = TW.upd Bx (TW.OFF_g_s + 140) (TW.put 4 v).
Proof. intros Bx v. reflexivity. Qed.

(* g_fail_next is neither of the two fields. *)
Lemma oe1_gfn : forall Bx, length Bx = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (TW.set_S_e1_named_us (TW.set_S_foreign Bx 0) 1) = TW.g_fail_next Bx.
Proof.
intros Bx L. unfold TW.g_fail_next, TW.set_S_e1_named_us, TW.set_S_foreign.
rewrite !rd_upd_W by wside. reflexivity.
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma oe1_inG : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s). split.
- exact (TMAP_A_in_G _ _ _ TMAP_A_g_s).
- unfold in_zr, ONANN_S in *. cbn [fst snd]. lia.
Qed.

(* The eight bytes the run stores, g_s.foreign and g_s.e1_named_us, are rows 4 and 7 of onann_wr. *)
Lemma oe1_st_wr : forall Bw b a, ONANN_S + 136 <= a < ONANN_S + 144 -> onann_wr Bw b a.
Proof.
intros Bw b a Ha. destruct (Z_lt_le_dec a (ONANN_S + 140)) as [H|H].
- right; right; right; left. unfold twa_fld, TW.A_S_foreign, TW.OFF_g_s, ONANN_S in *. lia.
- right; right; right; right; right; right; left. unfold twa_fld, TW.A_S_e1_named_us, TW.OFF_g_s, ONANN_S in *. lia.
Qed.

(* A view equal on [0, 2 ^ 64) is equal everywhere (aview reads the address modulo 2 ^ 64). *)
Lemma oe1_kd_all : forall (W : world tfibsegs) (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  forall a, aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.
Proof.
intros W m m' H a. rewrite (aview_wrap64 tfibsegs _ m' a), (aview_wrap64 tfibsegs _ m a).
apply H. apply Z.mod_pos_bound. lia.
Qed.

(* The bytes of a value in memory, read byte by byte through the view. *)
Lemma oe1_aview_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v -> forall j, (j < n)%nat ->
  aview tfibsegs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* A chunk of w bytes of the value e reads, byte k, the k-th little-endian byte of e (SlostNtc.v sn_chunk_val). *)
Lemma oe1_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* +0x554, the fall-through of `bltz s7` (0 <= off); +0x588, the return of maybe_online. *)
Definition ONANN_E1B : Z := AF_on_announce + 0x554.
Definition ONANN_E1R : Z := AF_on_announce + 0x588.
(* The shadow byte of s + 136 and of s + 140 (g_s is 8-aligned: one granule). *)
Definition OE1_SH : Z := 2148220745.
Lemma OE1_SH_eq : OE1_SH = SHADOW_OFF + (ONANN_S + 136) / 8 /\ OE1_SH = SHADOW_OFF + (ONANN_S + 140) / 8.
Proof. split; reflexivity. Qed.
(* No shadow token: every shadow byte the runs read is a region's. *)
Definition OE1_B0 : Z * Z := (0, 0).
Definition OE1_Bx : sv := SLit 0.
(* Run A, +0x548 .. `bltz s7` at +0x550: a0 = s + 136 and s8 = the shadow base pinned, no region. *)
Definition OE1_REGSA : list sv :=
  sr_set (sr_set sr_atoms (Z_to_bv 5 10) (SLit (ONANN_S + 136))) (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_oe1A : sstate := mkSS ONANN_E1 OE1_REGSA [] None (mkFacts [] [] []).
(* Run B, +0x554 .. `jal maybe_online` at +0x584: a1 = the shadow byte, s4 = s, s8 = the shadow base pinned; the
   eight bytes [s + 136, s + 144), written; the shadow byte, read (0); the spill slot sp1 + 40 at s1 (atom 9), read
   (the frame, s2's value: atom 18). *)
Definition OE1_REGSB : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 11) (SLit OE1_SH)) (Z_to_bv 5 20) (SLit ONANN_S))
    (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition OE1_R_gs : YP09.region :=
  YP09.mkRegion None (ONANN_S + 136) (ONANN_S + 144) (ONANN_S + 136) (ONANN_S + 144) [].
Definition OE1_R_sh : YP09.region :=
  YP09.mkRegion None OE1_SH (OE1_SH + 1) 0 0 [YP09.mkChunk OE1_SH (YP09.CVal 1 (SLit 0))].
Definition OE1_R_sl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 40 48 0 0 [YP09.mkChunk 40 (YP09.CVal 8 (SOff 18 0))].
Definition ss_oe1B : sstate := mkSS ONANN_E1B OE1_REGSB [OE1_R_gs; OE1_R_sh; OE1_R_sl] None (mkFacts [] [] []).
(* Run C, +0x588 `j +0x764`: no region. *)
Definition ss_oe1C : sstate := mkSS ONANN_E1R sr_atoms [] None (mkFacts [] [] []).

(* The register and region readers of a symbolic state, as lib/A/Prog/DgnTransportPaLib.v states them. *)
Ltac oe1_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* A register the run does not write, at the run's end, from the equation Q of its value at the run's start: the
   run's valuation agrees with the start valuation below atom 1024 (Elo), which reads the registers (EE). *)
Ltac oe1_kreg HS Elo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    oe1_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (Elo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac oe1_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac oe1_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* The write rights of a run: a region with an empty window, or [s + 136, s + 144), bytes of G. *)
Ltac oe1_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat first
    [ apply awr_ok_x_nil
    | apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; exfalso; lia |]
    | apply awr_ok_x_cons_g;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; apply oe1_inG;
          unfold ONANN_S, TA_g_s, TW.SZ_g_s; lia |] ].
(* The windows a run's regions leave, as the frame_of of its end state reads them: every byte outside Zs kept. *)
Ltac oe1_kept HFr Zs :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
  intros a Ha Hn; apply (kept_of_frame _ _ _ _ _ Zs HFr); [| exact Ha | exact Hn];
  let b0 := fresh "b0" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b0 wlo whi x Hin Hx; cbv beta;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as <- <- <-; cbn [base_val] in Hx; unfold ONANN_S, TA_g_s in *; lia |]);
  destruct Hin.

(* ------------------------------------------------------------------ *)
(* 3. The walk                                                          *)
(* ------------------------------------------------------------------ *)

Section e1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The runs' valuation: the 32 registers. *)
Definition oe1_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).

(* Run A's state at +0x548 holds of the machine state there. *)
Lemma oe1_entryA : forall (W : world segs) regs mem,
  YK11.getr regs 10 = w64 (ONANN_S + 136) -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (oe1_E regs) ss_oe1A
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_E1)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem R10 R24.
rewrite restrict_mkst_fx.
assert (H0 : st_ok_pi segs VAL (oe1_E regs) (mkSS ONANN_E1 sr_atoms [] None (mkFacts [] [] []))
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_E1)) (mrestrict (w_H W) mem) (YK11.seg_rom segs))).
{ apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I. }
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 10) (ONANN_S + 136) H0 R10 eq_refl) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
exact H2.
Qed.

(* Run B's state at +0x554 holds of the machine state there. *)
Lemma oe1_entryB : forall ly S (W : world segs) regs mem md sp1 F,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 11 = w64 OE1_SH -> YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F ->
  4096 <= F < 2 ^ 47 -> 2 ^ 32 <= sp1 -> sp1 + 48 <= 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 40) = Some F ->
  st_ok_pi segs VAL (oe1_E regs) ss_oe1B
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_E1B)) mem (YK11.seg_rom segs))).
Proof.
intros ly S W regs mem md sp1 F HZ HAR R11 R20 R24 R9 R18 HF Hsp1 Hsp2 Hsl.
rewrite restrict_mkst_fx.
set (E := oe1_E regs).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, oe1_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = F)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (ZSH : val_mem segs (mrestrict (w_H W) mem) OE1_SH 1 0).
{ apply AE2y.val_mem1_of_aview.
  replace OE1_SH with (FCells.shadow_addr (ONANN_S + 136)) by reflexivity.
  apply (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) _ HAR); [| | | exact HZ].
  - reflexivity.
  - lia.
  - unfold TW.SZ_g_s. lia. }
assert (H0 : st_ok_pi segs VAL E (mkSS ONANN_E1B sr_atoms [OE1_R_gs; OE1_R_sh; OE1_R_sl] None (mkFacts [] [] []))
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_E1B)) (mrestrict (w_H W) mem) (YK11.seg_rom segs))).
{ apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks OE1_R_gs OE1_R_sh OE1_R_sl base_val];
      rewrite ?U9.
    + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
      apply oe1_inG. unfold TW.SZ_g_s. lia.
    + split; [unfold OE1_SH; lia|]. split; [unfold OE1_SH; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 OE1_SH 1 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_l. exact ZSH.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 40 8 (SOff 18 0) F); [| lia | lia |].
      * cbn [sv_denot]. rewrite U18, Z.add_0_r. reflexivity.
      * exact (AE2y.val_mem_of_rdword _ _ _ _ Hsl).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, OE1_R_gs, OE1_R_sh, OE1_R_sl.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold OE1_SH, ONANN_S, TA_g_s. repeat split; first [exact I | lia].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I. }
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 11) OE1_SH H0 R11 eq_refl) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) ONANN_S H1 R20 eq_refl) as H2.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H2 R24 eq_refl) as H3.
exact H3.
Qed.

(* Run C's state at +0x588 holds of the machine state there. *)
Lemma oe1_entryC : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (oe1_E regs) ss_oe1C
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_E1R)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold ss_oe1C.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

Lemma oe1_holds : @onann_e1_stmt fx rc B MT.
Proof.
unfold onann_e1_stmt, onann_e1_at.
intros FN NREL LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F B2 ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HZ & HGU & HGNE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof CALLS as (_ & _ & _ & _ & _ & _ & _ & HMON & _).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hgf0 &
  Hm & HTF & Htfoff & Hrom & Hapart & Hri & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HC0 & Htw2 & Hb2 & Hcmd & Hk & Hgf2 & Haok & Hsl & Hs40 & Hs56).
pose proof HC0 as (HJ & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof HREGS as ((((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R20 & R24 & R25 & R26) & R10) & R22 & R23).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (oe1_off_range (onann_w1 timg_A Bw b) b) as Hoffr.
set (off := onann_off (onann_w1 timg_A Bw b) b) in *.
unfold ONANN_FBYTES in HFc, HFapp.
(* the entry's and the cut's layouts: the same stack bounds and frame addresses *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS Hstk0.
pose proof HJ as (_ & _ & (memS2 & HJ2i & _) & _).
pose proof HJ2i as (_ & Hly2 & _).
clear HJ2i memS2.
pose proof Hlyc as (_ & _ & _ & _ & _ & ELFc & _ & _ & _ & ESLOc & ESHIc & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ESLO2 & ESHI2 & _).
clear Hly2.
assert (ESLO : ly_stk_lo ly2 = ly_stk_lo lyc) by (rewrite ESLO2, ESLOc; reflexivity).
assert (ESHI : ly_stk_hi ly2 = ly_stk_hi lyc) by (rewrite ESHI2, ESHIc; reflexivity).
assert (Hfa2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite HlyF; reflexivity).
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
(* the stack: sp1 is 32-aligned, at most 208 below the entry sp; maybe_online's window lies inside on_announce's *)
assert (HSTKE : ONANN_STK = 208 + WAKE_STK) by reflexivity.
assert (HMW : MAYBEON_STK <= WAKE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HMS0 : 0 <= MAYBEON_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold ONANN_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult. }
destruct Hsp1 as [Hsp1 Hsp132].
assert (Hsp116 : sp1 mod 16 = 0).
{ pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp132, Z.add_0_r in D. rewrite D.
  replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
assert (Hce0 : alloc_ceiling <= spZ regs - ONANN_STK) by lia.
assert (Hsp1c : alloc_ceiling <= sp1 - MAYBEON_STK) by lia.
assert (Hsph : spZ regs <= 2 ^ 47) by lia.
assert (HFhi : F + 1024 <= alloc_ceiling) by exact HFc.
assert (USP2 : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (HLBw : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
assert (HLB2 : length B2 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw2).
destruct Hb2 as (HN2 & d & EB2).
(* +0x548 .. +0x550: a1 = the shadow byte of s + 136, `bltz s7` *)
pose proof (oe1_entryA W2 regs2 mem2 R10 R24) as HS.
set (EA := oe1_E regs2) in HS.
assert (SHOK : sh_ok segs OE1_Bx [] EA (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI : img_env VAL A_LIM EA) by (unfold EA, oe1_E; apply Eimg_env).
assert (EEA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EA n = YK11.getr regs2 r)
  by (intros n r Hn; unfold EA, oe1_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (D23 : sv_denot EA (SOff 23 0) = Z_to_bv 64 off).
{ cbn [sv_denot]. rewrite (EEA 23%nat 23%bv eq_refl), R23. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  reflexivity. }
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_E1)) mm rom) mdx) Q) end.
paj_run_tok RUN HS HJ SHOK OE1_B0.
{ oe1_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdA := mdx) in * end. clearbody mdA.
rename ms into msA.
(* run A writes nothing *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msA) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
  intros b0 wlo whi x Hin Hx. cbv beta.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin. destruct Hin. }
assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msA) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK OE1_B0.
- (* off < 0: the branch is taken, to the foreign cut +0x58c *)
  cbn [branch_taken] in Hc. rewrite D23 in Hc. change (sv_denot EA (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (oe1_lts off 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_lt in Hc.
  pose proof (oe1_k_neg timg_A TF B2 off b Bw' Hc Hk) as Hkn.
  paj_run_to_tok RUNTO HS HJ SHOK OE1_B0 ONANN_FN.
  { oe1_awr. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdF := mdx) in * end. clearbody mdF.
  rename ms into msF.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ _) => set (E1 := EF) in HS end.
  assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew EA n)
    by (intros n Hn; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
  oe1_kreg HS E1lo EEA (2%bv : bv 5) 2%nat R2 Y2. oe1_kreg HS E1lo EEA (3%bv : bv 5) 3%nat R3 Y3.
  oe1_kreg HS E1lo EEA (4%bv : bv 5) 4%nat R4 Y4. oe1_kreg HS E1lo EEA (8%bv : bv 5) 8%nat R8 Y8.
  oe1_kreg HS E1lo EEA (9%bv : bv 5) 9%nat R9 Y9. oe1_kreg HS E1lo EEA (18%bv : bv 5) 18%nat R18 Y18.
  oe1_kreg HS E1lo EEA (19%bv : bv 5) 19%nat R19 Y19. oe1_kreg HS E1lo EEA (20%bv : bv 5) 20%nat R20 Y20.
  oe1_kreg HS E1lo EEA (22%bv : bv 5) 22%nat R22 Y22. oe1_kreg HS E1lo EEA (25%bv : bv 5) 25%nat R25 Y25.
  oe1_kreg HS E1lo EEA (26%bv : bv 5) 26%nat R26 Y26.
  oe1_reg HS (10%bv : bv 5) (w64 (ONANN_S + 136)) Y10 ltac:(reflexivity).
  oe1_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) Y24 ltac:(reflexivity).
  oe1_reg HS (11%bv : bv 5) (w64 (SHADOW_OFF + (ONANN_S + 136) / 8)) Y11 ltac:(reflexivity).
  assert (K1 : forall a, aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem2 a).
  { apply oe1_kd_all. intros a Ha. rewrite <- (KA a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin. destruct Hin. }
  assert (G1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msF) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA a Ha))).
  assert (KG1 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem msF) (spZ regs - ONANN_STK) (spZ regs)
    (onann_wr Bw b)).
  { destruct HK as (L1 & L2 & L3 & L4 & L5 & L6).
    split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha Hw. rewrite K1. exact (L1 a Ha Hw).
    - intros b0 m i Hb Hi Hn. rewrite K1. exact (L2 b0 m i Hb Hi Hn).
    - intros a Hi HnG Hno Hne. rewrite K1. exact (L3 a Hi HnG Hno Hne).
    - intros cid pos0 a Hin Hr Hn. rewrite K1. exact (L4 cid pos0 a Hin Hr Hn).
    - intros a Ha Hw Hp. apply G1. exact (L5 a Ha Hw Hp).
    - intros a Ha. apply G1. exact (L6 a Ha). }
  assert (HSV1 : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) (ms_mem msF)) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
  { refine (Forall_impl _ _ HSV). intros o Ho. rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K1 _)). exact Ho. }
  assert (HFL1 : rdword (aview segs (w_H W2) (ms_mem msF)) (F + ONANN_FBYTES - 8) = Some (flag_addr lyc ONANN_CID pos))
    by (rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K1 _)); exact HFL).
  assert (Haok1 : onann_a_ok W2 (ms_mem msF) F buf b).
  { destruct Haok as (Ha1 & Ha2 & Ha3 & Ha4 & Ha5).
    split; [|split; [|split; [|split]]].
    - apply (garr8_frame segs _ _ _ _ Ha1). intros a _. apply (YCbq.mbyte_of_aview segs). exact (K1 a).
    - apply (garr8_frame segs _ _ _ _ Ha2). intros a _. apply (YCbq.mbyte_of_aview segs). exact (K1 a).
    - rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K1 _)). exact Ha3.
    - rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K1 _)). exact Ha4.
    - intros i Hi. rewrite K1. exact (Ha5 i Hi). }
  assert (Hsl1 : onann_slots_arm W2 (ms_mem msF) sp1).
  { unfold onann_slots_arm, onann_slot in *. destruct Hsl as (Q1 & Q2 & Q3 & Q4).
    split; [rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K1 _)); exact Q1|].
    split; [rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K1 _)); exact Q2|].
    split; [rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K1 _)); exact Q3|].
    rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K1 _)); exact Q4. }
  assert (Hs401 : onann_slot W2 (ms_mem msF) sp1 40 F)
    by (unfold onann_slot in *; rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K1 _)); exact Hs40).
  assert (Hs561 : onann_slot W2 (ms_mem msF) sp1 56 (F + ONANN_A))
    by (unfold onann_slot in *; rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K1 _)); exact Hs56).
  assert (Htw1 : tw_at TMAP_A (aview segs (w_H W2) (ms_mem msF)) B2)
    by (apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact Htw2 | intros x _; exact (K1 x)]).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_FN)) mm rom) mdx) Q) end.
  apply (FN LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    B2 ly2 S2 W2 (ms_mem msF) mdF (ms_regs msF) HFIX).
  + unfold onann_fn_cur, onann_cur.
    refine (conj (conj HJ (conj He (conj Hfrs (conj Hperm (conj HlyF (conj HMO (conj KG1 (conj HSV1 HFL1))))))))
      (conj Htw1 (conj (conj HN2 (ex_intro _ d EB2)) (conj Hkn (conj Hgf2 (conj Haok1 (conj Hsl1
        (conj Hs401 Hs561)))))))).
  + exact (conj (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y19))))))
      (conj Y20 (conj Y24 (conj Y25 Y26)))) Y10) (conj Y11 Y22)).
- (* 0 <= off: the branch falls through to +0x554 *)
  cbn [branch_taken] in Hc. rewrite D23 in Hc. change (sv_denot EA (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (oe1_lts off 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_ge in Hc.
  pose proof (oe1_k_pos timg_A TF B2 off b Bw' Hc Hk) as HMM.
  paj_run_to_tok RUNTO HS HJ SHOK OE1_B0 ONANN_E1B.
  { oe1_awr. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
  rename ms into ms1.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ _) => set (E1 := EF) in HS end.
  assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew EA n)
    by (intros n Hn; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
  oe1_kreg HS E1lo EEA (2%bv : bv 5) 2%nat R2 Z2. oe1_kreg HS E1lo EEA (3%bv : bv 5) 3%nat R3 Z3.
  oe1_kreg HS E1lo EEA (4%bv : bv 5) 4%nat R4 Z4. oe1_kreg HS E1lo EEA (8%bv : bv 5) 8%nat R8 Z8.
  oe1_kreg HS E1lo EEA (9%bv : bv 5) 9%nat R9 Z9. oe1_kreg HS E1lo EEA (18%bv : bv 5) 18%nat R18 Z18.
  oe1_kreg HS E1lo EEA (19%bv : bv 5) 19%nat R19 Z19. oe1_kreg HS E1lo EEA (20%bv : bv 5) 20%nat R20 Z20.
  oe1_reg HS (11%bv : bv 5) (w64 OE1_SH) Z11 ltac:(reflexivity).
  oe1_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) Z24 ltac:(reflexivity).
  assert (K1 : forall a, aview segs (w_H W2) (ms_mem ms1) a = aview segs (w_H W2) mem2 a).
  { apply oe1_kd_all. intros a Ha. rewrite <- (KA a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin. destruct Hin. }
  assert (G1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA a Ha))).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_E1B)) mm rom) mdx) Q) end.
  clear HS SHOK HF HFr HG E1lo E1 KA GA HEI.
  set (regsB := ms_regs ms1) in *. set (memB := ms_mem ms1) in *. clearbody regsB memB. clear ms1 msA.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARB.
  assert (Hs40B : rdword (aview segs (w_H W2) memB) (sp1 + 40) = Some F)
    by (rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K1 _)); exact Hs40).
  (* +0x554 .. +0x584: the checks of s + 136 and s + 140, the stores of :211 and :212, s7 = F, a0 = s, the call *)
  pose proof (oe1_entryB ly2 S2 W2 regsB memB md1 sp1 F HZ HARB Z11 Z20 Z24 Z9 Z18 ltac:(lia) ltac:(lia) ltac:(lia)
    Hs40B) as HS.
  set (EB := oe1_E regsB) in HS.
  assert (SHOK : sh_ok segs OE1_Bx [] EB (mrestrict (w_H W2) memB)) by constructor.
  assert (HEI : img_env VAL A_LIM EB) by (unfold EB, oe1_E; apply Eimg_env).
  assert (EEB : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EB n = YK11.getr regsB r)
    by (intros n r Hn; unfold EB, oe1_E; apply ew_Eimg_Ereg_nat; exact Hn).
  paj_run_tok RUN HS HJ SHOK OE1_B0.
  { oe1_awr. }
  lazymatch type of HS with
    OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ (restrict _ ?mf) =>
    set (E6 := EF) in HS; rename mf into msC end.
  assert (E6lo : forall n, (n < 1024)%nat -> ew E6 n = ew EB n)
    by (intros n Hn; unfold E6; rewrite ?ew_ewset_other by lia; reflexivity).
  oe1_kreg HS E6lo EEB (2%bv : bv 5) 2%nat Z2 Q2. oe1_kreg HS E6lo EEB (3%bv : bv 5) 3%nat Z3 Q3.
  oe1_kreg HS E6lo EEB (4%bv : bv 5) 4%nat Z4 Q4. oe1_kreg HS E6lo EEB (8%bv : bv 5) 8%nat Z8 Q8.
  oe1_kreg HS E6lo EEB (9%bv : bv 5) 9%nat Z9 Q9. oe1_kreg HS E6lo EEB (18%bv : bv 5) 18%nat Z18 Q18.
  oe1_kreg HS E6lo EEB (19%bv : bv 5) 19%nat Z19 Q19.
  oe1_reg HS (10%bv : bv 5) (w64 MAYBEON_S) Q10 ltac:(reflexivity).
  oe1_reg HS (23%bv : bv 5) (w64 F) Q23
    ltac:(cbn [sv_denot]; rewrite (E6lo 18%nat ltac:(lia)), (EEB 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact Z18).
  oe1_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + ONANN_E1R)) Q1
    ltac:(apply codeptr_val; unfold E6;
          lazymatch goal with H : img_env _ _ ?X |- img_env _ _ ?X => exact H end).
  (* the two stores: the four bytes at s + 136 hold 0, the four at s + 140 hold 1 *)
  oe1_region HS 0%nat HRw.
  pose proof (oe1_chunk_val E6 (w_H W2) (ms_mem msC) _ _ _ _ _ _ 6158920 4 (SLit 0) HRw ltac:(oe1_in)
    ltac:(lia)) as VG0.
  pose proof (oe1_chunk_val E6 (w_H W2) (ms_mem msC) _ _ _ _ _ _ 6158924 4 (SLit 1) HRw ltac:(oe1_in)
    ltac:(lia)) as VG1.
  cbn [base_val] in VG0, VG1.
  change (N.to_nat 4) with 4%nat in VG0, VG1.
  change (bv_unsigned (sv_denot E6 (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VG0.
  change (bv_unsigned (sv_denot E6 (SLit 1)) mod 2 ^ (8 * Z.of_N 4)) with 1 in VG1.
  clear HRw.
  (* run B wrote [s + 136, s + 144) only *)
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (ONANN_S + 136 <= a < ONANN_S + 144) ->
    aview segs (w_H W2) (ms_mem msC) a = aview segs (w_H W2) memB a).
  { oe1_kept HFr (fun x => ONANN_S + 136 <= x < ONANN_S + 144). }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdC := mdx) in * end. clearbody mdC.
  set (regsC := ms_regs msC) in *. set (memC := ms_mem msC) in *. clearbody regsC memC.
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (ONANN_S + 136 <= a < ONANN_S + 144) ->
    aview segs (w_H W2) memC a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn. rewrite (KB a Ha Hn). exact (K1 a). }
  assert (GC : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memC a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (G1 a Ha))).
  clear KB HF HFr HG.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARC.
  assert (HSPC : spZ regsC = sp1) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
  (* the world at the call: set_S_e1_named_us (set_S_foreign B2 0) 1, the stores of :211 and :212 *)
  assert (TWG : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x).
  { intros x (o & b0 & n & Hin & Hx).
    unfold inG. apply Exists_exists. exists (b0, n).
    split; [exact (TMAP_A_in_G o b0 n Hin) | unfold in_zr; cbn [fst snd]; lia]. }
  assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha)).
  set (v1 := fun a : Z => if (ONANN_S + 140 <=? a) && (a <? ONANN_S + 144) then aview segs (w_H W2) mem2 a
                          else aview segs (w_H W2) memC a).
  assert (HtwF : tw_at TMAP_A v1 (TW.set_S_foreign B2 0)).
  { rewrite oe1_fg_eq.
    apply (tw_write TMAP_A (aview segs (w_H W2) mem2) v1 B2 TW.OFF_g_s TA_g_s TW.SZ_g_s 136 4 0 TMAP_A_ok Htw2
      TMAP_A_g_s); [lia | unfold TW.SZ_g_s; lia | |].
    - intros j Hj. unfold v1. cbv beta.
      replace (ONANN_S + 140 <=? TA_g_s + 136 + Z.of_nat j) with false
        by (symmetry; apply Z.leb_gt; unfold ONANN_S; lia).
      cbn [andb].
      replace (TA_g_s + 136 + Z.of_nat j) with (0 + 6158920 + Z.of_nat j) by (unfold TA_g_s; lia).
      exact (oe1_aview_of_val _ _ _ 4 _ VG0 j Hj).
    - intros x Hx Hn. unfold v1. cbv beta.
      destruct ((ONANN_S + 140 <=? x) && (x <? ONANN_S + 144)) eqn:Ex; [reflexivity|].
      pose proof (GLOW x (TWG x Hx)) as Hl. unfold kLowMemEnd in Hl.
      apply KC; [lia|]. intros X. apply Hn.
      apply andb_false_iff in Ex.
      destruct Ex as [Ex | Ex]; [apply Z.leb_gt in Ex | apply Z.ltb_ge in Ex]; unfold ONANN_S in *; lia. }
  assert (HtwC : tw_at TMAP_A (aview segs (w_H W2) memC) (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1)).
  { rewrite (oe1_e1_eq (TW.set_S_foreign B2 0) 1).
    apply (tw_write TMAP_A v1 (aview segs (w_H W2) memC) (TW.set_S_foreign B2 0) TW.OFF_g_s TA_g_s TW.SZ_g_s 140 4 1
      TMAP_A_ok HtwF TMAP_A_g_s); [lia | unfold TW.SZ_g_s; lia | |].
    - intros j Hj. replace (TA_g_s + 140 + Z.of_nat j) with (0 + 6158924 + Z.of_nat j) by (unfold TA_g_s; lia).
      exact (oe1_aview_of_val _ _ _ 4 _ VG1 j Hj).
    - intros x Hx Hn. unfold v1. cbv beta.
      destruct ((ONANN_S + 140 <=? x) && (x <? ONANN_S + 144)) eqn:Ex; [|reflexivity].
      exfalso. apply andb_true_iff in Ex as [Ex1 Ex2]. apply Z.leb_le in Ex1. apply Z.ltb_lt in Ex2.
      apply Hn. unfold ONANN_S in *. lia. }
  assert (HgfC : TW.g_fail_next (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1) <= 1)
    by (rewrite (oe1_gfn B2 HLB2); exact Hgf2).
  (* what the walk kept at the call: the cut's, over run B ([s + 136, s + 144): rows 4 and 7 of onann_wr) *)
  assert (KGC : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 memC (spZ regs - ONANN_STK) (spZ regs)
    (onann_wr Bw b)).
  { apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W2 mem2 memC
      (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) (fun x => ONANN_S + 136 <= x < ONANN_S + 144) HARc HK KC GC).
    - intros a Hz Hc0. cbv beta in Hz. exfalso. unfold ONANN_S, TA_g_s in Hz. lia.
    - intros b0 m i _ _ Hz. exact (oe1_st_wr Bw b _ Hz).
    - intros a Hz _ HnG _ _. exfalso. apply HnG. apply oe1_inG. cbv beta in Hz. unfold TW.SZ_g_s. lia.
    - intros c p a _ _ Hz. exact (oe1_st_wr Bw b _ Hz). }
  (* maybe_online's premises *)
  assert (HTFC : trans_tframe_at B ly2 S2 W2 memC regsC MAYBEON_STK TF).
  { apply (onann_tf_call B LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 memC mdC pos regs regsC MAYBEON_STK TF Bw b
      HARc HARC Hfrs Hperm Hfa2 ESLO ESHI KGC Htfoff); [rewrite HSPC; lia | rewrite HSPC; lia | exact HTF]. }
  assert (HROMC : trans_rom_view_rd W2 memC)
    by exact (onann_rom_call B HRU HRE lyc Sc W memc W2 memC _ _ _ Hrom KGC).
  assert (HAPC : maybeon_apart TF (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1))
    by (rewrite EB2; exact (onann_apart_mo TF Bw b d HLBw Hapart)).
  assert (HCNTC : count_cid MAYBEON_CID (frames S2) < fs_frames MAYBEON_CID).
  { rewrite Hfrs.
    change (count_cid MAYBEON_CID ((ONANN_CID, pos) :: frames Sc)) with (count_cid WAKE_CID (frames Sc)).
    change (fs_frames MAYBEON_CID) with (fs_frames WAKE_CID). lia. }
  assert (HEV0 : MAYBEON_EV = 0) by reflexivity.
  assert (HOEV : 0 <= ONANN_EV) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (HNEVC : st_nev S + (k + 0) + MAYBEON_EV <= EV_MAX) by lia.
  assert (EBR : BASE + ONANN_E1R = 0x87ffc) by (vm_compute; reflexivity).
  (* +0x584: maybe_online, in the same G journal *)
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_maybe_online) rg mm mdx) Q) end.
  eapply SRr_bind.
  { apply (HMON fx STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 memC mdC (k + 0) regsC TF
      (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1) Bw' HJ
      ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold ONANN_E1R, AF_on_announce; lia
                                                                        | reflexivity])
      ltac:(unfold raZ; rewrite Q1, EBR, unsigned_lit_small by lia; lia)
      ltac:(rewrite Q3; exact Hgp) ltac:(rewrite Q4; exact Htp) Q10
      ltac:(rewrite HSPC; exact Hsp116) ltac:(rewrite HSPC; lia) ltac:(rewrite HSPC; lia)
      HtwC HgfC HMM HTFC HROMC HAPC HCNTC HNEVC). }
  intros W3 c3 _ HPOST.
  unfold transport_maybeon_post, transport_cg_post in HPOST.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
    Htw3 & Hgf3).
  assert (He30 : e3 = 0) by (rewrite HEV0 in He3; lia). subst e3.
  rewrite HSPC in HK3.
  assert (ELF3 : ly_F ly3 = ly_F lyc).
  { pose proof HJ3 as (_ & _ & (memS3 & HJ3i & _) & _). pose proof HJ3i as (_ & Hly3 & _).
    pose proof Hly3 as (_ & _ & _ & _ & _ & E3 & _). rewrite E3, ELFc. reflexivity. }
  destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F
    (flag_addr lyc ONANN_CID pos) HAR2 Hfrs Hbl HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
  (* what the walk kept: the cut's over run B, then maybe_online's *)
  assert (Hsh1 : spZ regs <= 2 ^ 64) by lia.
  assert (KG3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - ONANN_STK) (spZ regs)
    (onann_wr Bw b)).
  { apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 memC W3 mem3
      (spZ regs - ONANN_STK) (spZ regs) (sp1 - MAYBEON_STK) sp1 (onann_wr Bw b)
      (maybeon_wr (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1)) (dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos))
      Hce0 Hsh1 Hfa2 ltac:(intros f Hf; rewrite Hfrs; right; exact Hf) Hbl N1 N3 KGC HK3).
    - lia.
    - lia.
    - intros a Ha. left. rewrite EB2 in Ha. exact (onann_wr_mo Bw b d a HLBw Ha). }
  (* the thirteen saved words and the frame's last word, at the return *)
  destruct HK3 as (L1 & _ & _ & L4 & _).
  assert (HSV3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem3) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
  { apply Forall_forall. intros o Hino. cbv beta.
    pose proof (proj1 (Forall_forall _ _) HSV o Hino) as Hv. cbv beta in Hv.
    assert (Ho : 8 <= fst o <= 104).
    { unfold ONANN_SAVED in Hino. cbn [In] in Hino.
      repeat (destruct Hino as [Hino | Hino]; [subst o; cbn [fst]; lia |]). destruct Hino. }
    rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi.
    rewrite L1 by lia. apply KC; [lia|]. unfold ONANN_S, TA_g_s. lia. }
  assert (Hin2 : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  assert (EFA : frame_addr ly2 ONANN_CID pos = F) by (rewrite Hfa2; symmetry; exact EF).
  assert (HFL3 : rdword (aview segs (w_H W3) mem3) (F + ONANN_FBYTES - 8) = Some (flag_addr lyc ONANN_CID pos)).
  { rewrite <- HFL. unfold ONANN_FBYTES. apply YCbq.rdword_ext. intros i Hi.
    assert (HnI : ~ in_img segs (F + 1024 - 8 + i)).
    { apply (frm_img segs B LAWS _ _ _ _ _ ONANN_CID pos (F + 1024 - 8 + i) HAR2 Hin2).
      rewrite EFA, onann_fbytes. unfold ONANN_FBYTES. lia. }
    transitivity (aview segs (w_H W2) memC (F + 1024 - 8 + i)).
    - apply (L4 ONANN_CID pos (F + 1024 - 8 + i) Hin2).
      + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes ONANN_CID) with 1024. lia.
      + intros Hw. apply HnI. exact (proj1 (HGX _ (onann_mo_wr_G _ _ Hw))).
    - apply KC; [lia|]. intros X. apply HnI.
      apply (proj1 (HGX (F + 1024 - 8 + i) (oe1_inG (F + 1024 - 8 + i) ltac:(unfold TW.SZ_g_s; lia)))). }
  (* the registers the release reads, kept by the call *)
  assert (R3_2 : YK11.getr regs3 2 = w64 sp1) by exact (eq_trans (HP3 2 ltac:(hnf; lia)) Q2).
  assert (R3_3 : YK11.getr regs3 3 = YK11.getr regs 3) by exact (eq_trans (HP3 3 ltac:(hnf; lia)) Q3).
  assert (R3_4 : YK11.getr regs3 4 = YK11.getr regs 4) by exact (eq_trans (HP3 4 ltac:(hnf; lia)) Q4).
  assert (R3_8 : YK11.getr regs3 8 = w64 (spZ regs)) by exact (eq_trans (HP3 8 ltac:(hnf; lia)) Q8).
  assert (R3_9 : YK11.getr regs3 9 = w64 sp1) by exact (eq_trans (HP3 9 ltac:(hnf; lia)) Q9).
  assert (R3_18 : YK11.getr regs3 18 = w64 F) by exact (eq_trans (HP3 18 ltac:(hnf; lia)) Q18).
  assert (R3_19 : YK11.getr regs3 19 = w64 (SHADOW_OFF + F / 8)) by exact (eq_trans (HP3 19 ltac:(hnf; lia)) Q19).
  assert (R3_23 : YK11.getr regs3 23 = w64 F) by exact (eq_trans (HP3 23 ltac:(hnf; lia)) Q23).
  (* +0x588: `j +0x764`, to the release cut *)
  rewrite Q1.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_E1R)) mm rom) mdx) Q) end.
  pose proof (oe1_entryC W3 regs3 mem3) as HS3.
  set (E3 := oe1_E regs3) in HS3.
  assert (SHOK3 : sh_ok segs OE1_Bx [] E3 (mrestrict (w_H W3) mem3)) by constructor.
  assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3, oe1_E; apply Eimg_env).
  assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs3 r)
    by (intros n r Hn; unfold E3, oe1_E; apply ew_Eimg_Ereg_nat; exact Hn).
  paj_run_to_tok RUNTO HS3 HJ3 SHOK3 OE1_B0 ONANN_NREL.
  { oe1_awr. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md4 := mdx) in * end. clearbody md4.
  lazymatch type of HS3 with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E4 := EF) in HS3; rename mf into ms4 end.
  assert (E4lo : forall n, (n < 1024)%nat -> ew E4 n = ew E3 n)
    by (intros n Hn; unfold E4; rewrite ?ew_ewset_other by lia; reflexivity).
  oe1_kreg HS3 E4lo EE3 (2%bv : bv 5) 2%nat R3_2 X2. oe1_kreg HS3 E4lo EE3 (3%bv : bv 5) 3%nat R3_3 X3.
  oe1_kreg HS3 E4lo EE3 (4%bv : bv 5) 4%nat R3_4 X4. oe1_kreg HS3 E4lo EE3 (8%bv : bv 5) 8%nat R3_8 X8.
  oe1_kreg HS3 E4lo EE3 (9%bv : bv 5) 9%nat R3_9 X9. oe1_kreg HS3 E4lo EE3 (18%bv : bv 5) 18%nat R3_18 X18.
  oe1_kreg HS3 E4lo EE3 (19%bv : bv 5) 19%nat R3_19 X19. oe1_kreg HS3 E4lo EE3 (23%bv : bv 5) 23%nat R3_23 X23.
  (* run C writes nothing *)
  assert (K4 : forall a, aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
  { apply oe1_kd_all. intros a Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin. destruct Hin. }
  assert (G4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  assert (KG4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (ms_mem ms4) (spZ regs - ONANN_STK) (spZ regs)
    (onann_wr Bw b)).
  { destruct KG3 as (M1 & M2 & M3 & M4 & M5 & M6).
    split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha Hw. rewrite K4. exact (M1 a Ha Hw).
    - intros b0 m i Hb Hi Hn. rewrite K4. exact (M2 b0 m i Hb Hi Hn).
    - intros a Hi HnG Hno Hne. rewrite K4. exact (M3 a Hi HnG Hno Hne).
    - intros cid pos0 a Hin Hr Hn. rewrite K4. exact (M4 cid pos0 a Hin Hr Hn).
    - intros a Ha Hw Hp. apply G4. exact (M5 a Ha Hw Hp).
    - intros a Ha. apply G4. exact (M6 a Ha). }
  assert (HSV4 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) (ms_mem ms4)) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
  { refine (Forall_impl _ _ HSV3). intros o Ho. rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K4 _)). exact Ho. }
  assert (HFL4 : rdword (aview segs (w_H W3) (ms_mem ms4)) (F + ONANN_FBYTES - 8) = Some (flag_addr lyc ONANN_CID pos))
    by (rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => K4 _)); exact HFL3).
  assert (Htw4 : tw_at TMAP_A (aview segs (w_H W3) (ms_mem ms4)) Bw')
    by (apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw3 | intros x _; exact (K4 x)]).
  pmkst HS3.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_NREL)) mm rom) mdx) Q) end.
  apply (NREL LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly3 S3 W3 (ms_mem ms4) md4 0 (ms_regs ms4) HFIX).
  + unfold onann_rel_cur, onann_cur.
    refine (conj (conj _ (conj _ (conj _ (conj _ (conj ELF3 (conj _ (conj KG4 (conj HSV4 HFL4)))))))) (conj Htw4 Hgf3)).
    * replace (k + 0) with (k + 0 + 0) by lia. exact HJ3.
    * lia.
    * rewrite Hfr3. exact Hfrs.
    * exact (Permutation_trans Hperm3 Hperm).
    * exact (mo_le_trans MT MTL Sc S2 S3 0 0 HMO Hmo3).
  + exact (conj (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 X19)))))) X23).
Qed.
End e1.

(* The e1 piece of the walk of on_announce (OnannCut.v onann_e1_stmt), at every machine, run ceiling, record and
   meter. *)
Theorem onann_piece_e1 : forall fx rc B MT, @onann_e1_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@oe1_holds fx rc B MT). Qed.
