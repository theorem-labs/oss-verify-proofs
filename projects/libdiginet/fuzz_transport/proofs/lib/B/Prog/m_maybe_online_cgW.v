(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1111 of its 1210 lines of code are new or changed and 827 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/m_wake_cgW.v, with its module names changed; 581 of its 675 lines of code are new or changed and 1116 lines of the source are left out. *)
(* m_maybe_online: Theorem transport_m_maybe_online_cg_holds, the statement transport_m_maybe_online_cg_holds_stmt of
   lib/B/Prog/m_maybe_online_cg.v: the machine walk of m_maybe_online on fuzz_transport.asan-ubsan at 0x851d4
   (80 bytes, no frame), whose one call is a tail jump to m_set.

   The walk is a G-form walk, as lib/A/Prog/m_tick.v: it holds the caller's journal ajournal_gx G_HARNESS_B 0 []
   (lib/A/W_journalG.v) from the entry to the return or to the tail jump, and the runs are the symbolic runs of
   lib/A/Prog/PaShadow.v taken over that journal (lib/B/Prog/TransportGRunB.v paj_run_x).

   The run's regions are the world fields the code reads, each a region of its harness global whose bytes are the
   world's (TWorldG.v tw_read_val); each loaded value is an atom of the walk's valuation mo_E:
     atom 33  M.state (M + 12, 4 bytes)   atom 34  M.e2_acked (M + 16, 4)   atom 35  M.e1_us (M + 20, 4)
     atom 36  M.last_rx (M + 32, 8)       atom 37  g_cfg.keepalive_ms (4, object 31)
   No region has a writable byte at the entry; the 8 bytes of M.next_ka join the state as a writable region of G
   (mo_N) on the path that stores them.

   The paths (the three branches the run cannot decide are split with DgnTransportBPaLib.v paj_branch; each side is
   a test of the model, mo_br_ne / mo_br_eq):
     run 1 (+0x00 .. +0x10)  a2 = &M (object 8), a0 = M.state, a1 = 1, `bne a0, a1` at +0x10;
     path A1 (M.state <> 1)  +0x4c `ret`: the world is unchanged (mo_model_keep), nothing was written;
     run 2 (+0x14 .. +0x18)  M.e2_acked, `beqz` at +0x18;   path A2 (M.e2_acked = 0): as A1;
     run 3 (+0x1c .. +0x20)  M.e1_us, `beqz` at +0x20;      path A3 (M.e1_us = 0): as A1;
     path T (the three tests of :239 hold)
       run 4 (+0x24 .. +0x48)  g_cfg.keepalive_ms, M.last_rx, a3 = keepalive_ms * 1000 + last_rx, a0 = 2
                               (S_ONLINE), a1 = 2 (R_ONLINE), the 8-byte store of a3 at M + 48 (next_ka, :240), and
                               the tail jump `j m_set` at +0x48, where the run stops at m_set's entry.
   m_maybe_online stores nothing else, reads no runtime cell and has no instrumented check, so no shadow entry is
   needed (MO_SH = []) and no error or trap path is on its code.

   The close. A return closes with mo_close_ret: the model's world is Bw and every byte is the entry's. The tail
   jump enters m_set with m_maybe_online's ra, sp and callee-saved registers on the same journal and with a0 = 2,
   a1 = 2, at the world B1 = set_M_next_ka Bw (u64 (M.last_rx + h_ms_m keepalive_ms)) (mo_B1): the statement's
   premise transport_m_set_cg applies there (its model premise is mo_model_set), and its post gives
   m_maybe_online's post (mo_tail_post: m_set's written range mset_st_wr B1 S_ONLINE lies in monline_wr Bw, and the
   8 bytes of next_ka this walk wrote are in it too). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h YC1i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg m_maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TGB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module YO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YO0f.

(* ------------------------------------------------------------------ *)
(* The model                                                           *)
(* ------------------------------------------------------------------ *)

(* The value the code stores at M.next_ka (:240): keepalive_ms * 1000 + last_rx, in 64 bits. *)
Definition MO_KA (Bw : list byte) : Z := TS0.u64 (TW.M_last_rx Bw + TCB.h_ms_m (TW.Cfg_keepalive_ms Bw)).
(* The world m_set is entered at. *)
Definition mo_B1 (Bw : list byte) : list byte := TW.set_M_next_ka Bw (MO_KA Bw).

Lemma mo_some_inv : forall x y : list byte, Some (x, tt) = Some (y, tt) -> y = x.
Proof. intros x y H. injection H as H. symmetry. exact H. Qed.

(* The next_ka store (8 bytes at world offset 48) leaves M.state and OW.n alone. *)
Lemma mo_state_ka : forall (B0 : list byte) v, length B0 = Z.to_nat TW.W_LEN ->
  TW.M_state (TW.set_M_next_ka B0 v) = TW.M_state B0.
Proof.
  intros B0 v L. assert (LZ : Z.of_nat (length B0) = TW.W_LEN) by (rewrite L; reflexivity).
  unfold TW.M_state, TW.set_M_next_ka, TW.A_M_state, TW.A_M_next_ka, TW.OFF_M, TW.W_LEN in *.
  rewrite TWL.s32_at_upd_out; [reflexivity | lia | lia | rewrite TWL.length_put; lia | rewrite TWL.length_put; lia].
Qed.

Lemma mo_n_ka : forall (B0 : list byte) v, length B0 = Z.to_nat TW.W_LEN ->
  TW.OW_n (TW.set_M_next_ka B0 v) = TW.OW_n B0.
Proof.
  intros B0 v L. assert (LZ : Z.of_nat (length B0) = TW.W_LEN) by (rewrite L; reflexivity).
  unfold TW.OW_n, TW.set_M_next_ka, TW.A_OW_n, TW.A_M_next_ka, TW.OFF_OW, TW.OFF_M, TW.W_LEN in *.
  rewrite TWL.s32_at_upd_out; [reflexivity | lia | lia | rewrite TWL.length_put; lia | rewrite TWL.length_put; lia].
Qed.

(* One of the three tests of :239 fails: the model keeps the world. *)
Lemma mo_model_keep : forall Bw Bw',
  (TW.M_state Bw <> TCB.S_WAKING \/ TW.M_e2_acked Bw = 0 \/ TW.M_e1_us Bw = 0) ->
  TCB.m_maybe_online_m Bw = Some (Bw', tt) -> Bw' = Bw.
Proof.
  intros Bw Bw' Hc Hm. unfold TCB.m_maybe_online_m, TCB.truth in Hm.
  replace ((TW.M_state Bw =? TCB.S_WAKING) && negb (TW.M_e2_acked Bw =? 0) && negb (TW.M_e1_us Bw =? 0))%bool
    with false in Hm.
  - exact (mo_some_inv _ _ Hm).
  - symmetry. destruct Hc as [H | [H | H]].
    + replace (TW.M_state Bw =? TCB.S_WAKING) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity.
    + rewrite H, Z.eqb_refl. cbn [negb]. rewrite andb_false_r, andb_false_l. reflexivity.
    + rewrite H, Z.eqb_refl. cbn [negb]. rewrite andb_false_r. reflexivity.
Qed.

(* The three tests hold: the model runs m_set at the world with next_ka set, with st = S_ONLINE, why = R_ONLINE. *)
Lemma mo_model_set : forall Bw Bw',
  TW.M_state Bw = TCB.S_WAKING -> TW.M_e2_acked Bw <> 0 -> TW.M_e1_us Bw <> 0 ->
  TCB.m_maybe_online_m Bw = Some (Bw', tt) ->
  TCB.m_set_m (mo_B1 Bw) TCB.S_ONLINE TCB.R_ONLINE = Some (Bw', tt).
Proof.
  intros Bw Bw' H1 H2 H3 Hm. unfold TCB.m_maybe_online_m, TCB.truth in Hm.
  rewrite H1, Z.eqb_refl in Hm.
  replace (TW.M_e2_acked Bw =? 0) with false in Hm by (symmetry; apply Z.eqb_neq; exact H2).
  replace (TW.M_e1_us Bw =? 0) with false in Hm by (symmetry; apply Z.eqb_neq; exact H3).
  cbn [negb andb] in Hm. cbv beta iota in Hm. exact Hm.
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the entry                                     *)
(* ------------------------------------------------------------------ *)

(* The values of atoms 32 .. 37 at the world Bw. *)
Definition mo_vals (Bw : list byte) : list word :=
  [Z_to_bv 64 SHADOW_OFF;
   Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4); Z_to_bv 64 (TW.u_at Bw TW.A_M_e2_acked 4);
   Z_to_bv 64 (TW.u_at Bw TW.A_M_e1_us 4); Z_to_bv 64 (TW.M_last_rx Bw);
   Z_to_bv 64 (TW.Cfg_keepalive_ms Bw)].
(* The read-only bytes of M (object 8) and of g_cfg.keepalive_ms (object 31). *)
Definition mo_M : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 12 40 0 0
  [YP09.mkChunk 12 (CVal 4 (SOff 33 0)); YP09.mkChunk 16 (CVal 4 (SOff 34 0));
   YP09.mkChunk 20 (CVal 4 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 36 0))].
Definition mo_K : YP09.region := YP09.mkRegion (Some (A_OBJ 31)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 37 0))].
(* M.next_ka: the 8 bytes the store writes, added to the state on the path that stores them. *)
Definition mo_N : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 48 56 48 56 [].
Definition mo_regions : smem := [mo_M; mo_K].
Definition mo_facts : facts :=
  mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (37%nat, mkAF 0 (2 ^ 32 - 1) 0); (A_OBJ 8, mkAF TB_M TB_M 4)] [] [].
Definition ss_mo : sstate := mkSS AF_m_maybe_online sr_atoms mo_regions None mo_facts.
(* No instrumented check: no shadow entry. *)
Definition MO_SH : list shent := [].
Definition MO_Bx : sv := SOff 32 0.
(* The bytes this walk writes itself. *)
Definition mo_W (a : Z) : Prop := TB_M + 48 <= a < TB_M + 56.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac mo_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mo_reg: no match for" T; fail
  end.

Section mow. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma mo_vals_img : VAL (A_OBJ 8) = TB_M /\ VAL (A_OBJ 31) = TB_g_cfg + 24 /\
  BASE + AF_m_maybe_online = transportb_sigma TB_m_maybe_online /\
  BASE + AF_m_set = transportb_sigma TB_m_set.
Proof. vm_compute. repeat split. Qed.

(* ---- the valuation ---- *)

Definition mo_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transportb) (Ereg regs (mo_vals Bw)).

Lemma mo_agree : forall regs Bw, env_agree 32 (Ereg regs (mo_vals Bw)) (mo_E regs Bw).
Proof. intros regs Bw. split; [intros n Hn; unfold mo_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma mo_rng4 : forall Bw k, 0 <= TW.u_at Bw k 4 < 2 ^ 32.
Proof. intros Bw k. exact (TWL.u_at_range Bw k 4). Qed.
Lemma mo_rng8 : forall Bw k, 0 <= TW.u_at Bw k 8 < 2 ^ 64.
Proof. intros Bw k. exact (TWL.u_at_range Bw k 8). Qed.

(* ---- the branch conditions in the model's terms ---- *)

Lemma mo_sext_fld : forall E Bw n A, ew E n = Z_to_bv 64 (TW.u_at Bw A 4) ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (TW.s32_at Bw A).
Proof.
  intros E Bw n A H. pose proof (mo_rng4 Bw A) as R. cbn [sv_denot]. rewrite H.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
  rewrite LMem.sext_small, LMem.signed_of_extract by lia.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma mo_eqb_fld : forall E Bw n A c, ew E n = Z_to_bv 64 (TW.u_at Bw A 4) -> 0 <= c < 2 ^ 31 ->
  bv_eqb (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit c)) = (TW.s32_at Bw A =? c).
Proof.
  intros E Bw n A c H Hc. rewrite (mo_sext_fld E Bw n A H). cbn [sv_denot]. unfold bv_eqb.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (bv_swrap_in_range 32 (TW.u_at Bw A 4) ltac:(discriminate)) as R.
  change (bv_swrap 32 (TW.u_at Bw A 4)) with (TW.s32_at Bw A) in R.
  change (bv_half_modulus 32) with (2 ^ 31) in R.
  rewrite (Z.mod_small c (2 ^ 64)) by lia.
  destruct (Z.eqb_spec (TW.s32_at Bw A) c) as [Heq | Hne].
  - rewrite Heq. rewrite (Z.mod_small c (2 ^ 64)) by lia. apply Z.eqb_refl.
  - apply Z.eqb_neq. intros HH. apply Hne.
    destruct (Z_lt_le_dec (TW.s32_at Bw A) 0) as [Hneg | Hpos].
    + rewrite <- (Z.mod_unique (TW.s32_at Bw A) (2 ^ 64) (-1) (TW.s32_at Bw A + 2 ^ 64)) in HH by lia. lia.
    + rewrite (Z.mod_small (TW.s32_at Bw A) (2 ^ 64)) in HH by lia. exact HH.
Qed.

Lemma mo_br_eq : forall E Bw n A c, ew E n = Z_to_bv 64 (TW.u_at Bw A 4) -> 0 <= c < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit c)) = (TW.s32_at Bw A =? c).
Proof. intros E Bw n A c H Hc. cbn [branch_taken]. exact (mo_eqb_fld E Bw n A c H Hc). Qed.

Lemma mo_br_ne : forall E Bw n A c, ew E n = Z_to_bv 64 (TW.u_at Bw A 4) -> 0 <= c < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit c)) = negb (TW.s32_at Bw A =? c).
Proof. intros E Bw n A c H Hc. cbn [branch_taken]. rewrite (mo_eqb_fld E Bw n A c H Hc). reflexivity. Qed.

(* The 8-byte value the code stores at M.next_ka. *)
Lemma mo_d_ka : forall E Bw, ew E 36 = Z_to_bv 64 (TW.M_last_rx Bw) ->
  ew E 37 = Z_to_bv 64 (TW.Cfg_keepalive_ms Bw) ->
  sv_denot E (SAlu ALU_ADD (SOff 36 0) (SMd M_MUL (SOff 37 0) (SLit 1000))) = Z_to_bv 64 (MO_KA Bw).
Proof.
  intros E Bw H36 H37.
  pose proof (mo_rng4 Bw TW.A_Cfg_keepalive_ms) as RK.
  change (TW.u_at Bw TW.A_Cfg_keepalive_ms 4) with (TW.Cfg_keepalive_ms Bw) in RK.
  pose proof (mo_rng8 Bw TW.A_M_last_rx) as RL.
  change (TW.u_at Bw TW.A_M_last_rx 8) with (TW.M_last_rx Bw) in RL.
  cbn [sv_denot alu64 alu mul_div]. rewrite H36, H37.
  rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
  apply bv_eq.
  rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (TW.Cfg_keepalive_ms Bw) (2 ^ 64)) by lia.
  rewrite (Z.mod_small 1000 (2 ^ 64)) by lia.
  rewrite (Z.mod_small (TW.M_last_rx Bw) (2 ^ 64)) by lia.
  unfold MO_KA, TCB.h_ms_m, TS0.u64.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* ---- the entry state ---- *)

Lemma mo_entry : forall (W : world segs) regs mem Bw,
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  st_ok_pi segs VAL (mo_E regs Bw) ss_mo
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_maybe_online)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem Bw Htw.
  destruct mo_vals_img as (V8 & V31 & _ & _).
  set (E := mo_E regs Bw).
  assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, mo_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (B8 : base_val E (Some (A_OBJ 8)) = TB_M)
    by (apply VB; [rewrite (EOB 8%nat ltac:(lia)), V8; reflexivity | unfold TB_M; lia]).
  assert (B31 : base_val E (Some (A_OBJ 31)) = TB_g_cfg + 24)
    by (apply VB; [rewrite (EOB 31%nat ltac:(lia)), V31; reflexivity | unfold TB_g_cfg; lia]).
  assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (mo_vals Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, mo_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
  cbn [Nat.add nth mo_vals] in E32, E33, E34, E35, E36, E37.
  pose proof (mo_rng4 Bw TW.A_M_state) as R33. pose proof (mo_rng4 Bw TW.A_M_e2_acked) as R34.
  pose proof (mo_rng4 Bw TW.A_M_e1_us) as R35.
  pose proof (mo_rng8 Bw TW.A_M_last_rx) as R36.
  change (TW.u_at Bw TW.A_M_last_rx 8) with (TW.M_last_rx Bw) in R36.
  pose proof (mo_rng4 Bw TW.A_Cfg_keepalive_ms) as R37.
  change (TW.u_at Bw TW.A_Cfg_keepalive_ms 4) with (TW.Cfg_keepalive_ms Bw) in R37.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_mo.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold mo_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold mo_M, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B8.
      split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * apply (chunk_ok_val segs E _ TB_M 12 4 (SOff 33 0) (TW.u_at Bw TW.A_M_state 4));
          [apply DEN; [exact E33 | lia] | exact R33 | lia |].
        exact (tw_read_val segs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 12 4 TMAP_B_ok Htw TMAP_B_M
          ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
      * apply (chunk_ok_val segs E _ TB_M 16 4 (SOff 34 0) (TW.u_at Bw TW.A_M_e2_acked 4));
          [apply DEN; [exact E34 | lia] | exact R34 | lia |].
        exact (tw_read_val segs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 16 4 TMAP_B_ok Htw TMAP_B_M
          ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
      * apply (chunk_ok_val segs E _ TB_M 20 4 (SOff 35 0) (TW.u_at Bw TW.A_M_e1_us 4));
          [apply DEN; [exact E35 | lia] | exact R35 | lia |].
        exact (tw_read_val segs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 20 4 TMAP_B_ok Htw TMAP_B_M
          ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
      * apply (chunk_ok_val segs E _ TB_M 32 8 (SOff 36 0) (TW.M_last_rx Bw));
          [apply DEN; [exact E36 | exact R36] | exact R36 | lia |].
        exact (tw_read_val segs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 32 8 TMAP_B_ok Htw TMAP_B_M
          ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold mo_K, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B31.
      split; [unfold TB_g_cfg; lia|]. split; [unfold TB_g_cfg; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (TB_g_cfg + 24) 0 4 (SOff 37 0) (TW.Cfg_keepalive_ms Bw));
        [apply DEN; [exact E37 | lia] | exact R37 | lia |].
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 24 4 TMAP_B_ok Htw TMAP_B_g_cfg
        ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
  - unfold mo_regions, mo_M, mo_K.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B8, B31.
    unfold TB_M, TB_g_cfg. repeat split; lia.
  - unfold mo_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, E33, E34, E35, E37, (EOB 8%nat ltac:(lia)), V8.
    rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_state 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_e2_acked 4)) by lia.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_e1_us 4)) by lia.
    rewrite (unsigned_lit_small (TW.Cfg_keepalive_ms Bw)) by lia.
    rewrite (unsigned_lit_small TB_M) by (unfold TB_M; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 4) with 16.
    repeat match goal with |- _ /\ _ => split end.
    all: try exact I. all: try (unfold TB_M; lia). all: (unfold TB_M; reflexivity).
Qed.

(* ---- what the walk keeps ---- *)

Definition mo_KA (Zs : Z -> Prop) (W : world segs) (memc m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) m a = aview segs (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).

Lemma mo_KA_refl : forall Zs (W : world segs) memc, mo_KA Zs W memc memc.
Proof. intros Zs W memc. split; [intros; reflexivity | intros a Ha; exact Ha]. Qed.

Lemma mo_KA_mono : forall (Zs Zs' : Z -> Prop) (W : world segs) memc m,
  (forall a, Zs a -> Zs' a) -> mo_KA Zs W memc m -> mo_KA Zs' W memc m.
Proof.
  intros Zs Zs' W memc m HZ [K1 K2]. split; [|exact K2].
  intros a Ha Hn. apply K1; [exact Ha | intros HZa; exact (Hn (HZ a HZa))].
Qed.

(* A run from a state whose windows lie in Zs changes no byte outside Zs. *)
Lemma mo_KA_step : forall E Zs rs (W : world segs) memc (m m' : word -> option byte),
  (forall b wlo whi x, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= x < base_val E b + whi -> Zs x) ->
  mo_KA Zs W memc m ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mo_KA Zs W memc m'.
Proof.
  intros E Zs rs W memc m m' Hw [K1 K2] Hfr Hg. split.
  - intros a Ha Hn. rewrite (kept_of_frame E rs (w_H W) m m' Zs Hfr Hw a Ha Hn). exact (K1 a Ha Hn).
  - intros a Ha. exact (apresent_grows _ _ _ a Hg (K2 a Ha)).
Qed.

Lemma mo_tw_keep : forall (W : world segs) memc m Bw, mo_KA (fun _ => False) W memc m ->
  tw_at TMAP_B (aview segs (w_H W) memc) Bw -> tw_at TMAP_B (aview segs (w_H W) m) Bw.
Proof.
  intros W memc m Bw [KA _] H. apply (tw_kept TMAP_B (aview segs (w_H W) memc)); [exact H|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TGB.G_HARNESS_B_LO, TGB.G_HARNESS_B_HI in Hh.
  apply KA; [lia | intros []].
Qed.

(* ---- the two closes ---- *)

Lemma mo_inG_M : forall a, TB_M <= a < TB_M + TW.SZ_M -> inG TGB.G_HARNESS_B a.
Proof.
  intros a Ha. unfold inG. apply Exists_exists. exists (TB_M, TW.SZ_M).
  split; [exact (TMAP_B_in_G TW.OFF_M TB_M TW.SZ_M TMAP_B_M) | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma mo_gwr : forall a, inG TGB.G_HARNESS_B a -> forall m, writable_at segs m a.
Proof. intros a Ha m. exact (gx_rw_writable segs TGB.G_HARNESS_B a G_HARNESS_B_rw Ha m). Qed.

(* The post at the return: nothing changed, the model's world is Bw. *)
Lemma mo_close_ret : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw regsF mF mdF,
  AR_laws segs B -> ameter_laws MT ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MONLINE_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TGB.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mF mdF k ->
  mo_KA (fun _ => False) W memc mF ->
  tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 ->
  forall mat, @transport_monline_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw regsF mF mdF
    LAWS MTL HAR Hwin Hra HJF KAF Htw HP RF1 mat.
  pose proof KAF as [KA GA].
  unfold transport_monline_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
  split.
  { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [unfold MONLINE_EV, MSET_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transportb_segs_low TGB.G_HARNESS_B lyc Sc W memc mdc memc mF
      (spZ regs - MONLINE_STK) (spZ regs) (monline_wr Bw) (fun _ => False) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - intros a Ha _. exact (KA a Ha (fun x => x)).
    - exact GA.
    - intros a [].
    - intros b m i _ _ [].
    - intros a [].
    - intros cid pos a _ _ []. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  exact (mo_tw_keep W memc mF Bw KAF Htw).
Qed.

(* The 8 bytes this walk writes itself lie in the bytes this call may write. *)
Lemma mo_wr_next : forall Bw a,
  TW.M_state Bw = TCB.S_WAKING -> TCB.truth (TW.M_e2_acked Bw) = true -> TCB.truth (TW.M_e1_us Bw) = true ->
  mo_W a -> monline_wr Bw a.
Proof.
  intros Bw a H1 H2 H3 Hw.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. left.
  unfold twb_fld, TW.A_M_next_ka, TW.OFF_M, mo_W in *. lia.
Qed.

(* The bytes m_set may write lie in the bytes this call may write. *)
Lemma mo_wr_of_mset : forall Bw a, length Bw = Z.to_nat TW.W_LEN ->
  TW.M_state Bw = TCB.S_WAKING -> TCB.truth (TW.M_e2_acked Bw) = true -> TCB.truth (TW.M_e1_us Bw) = true ->
  mset_st_wr (mo_B1 Bw) TCB.S_ONLINE a -> monline_wr Bw a.
Proof.
  intros Bw a HL H1 H2 H3 [_ Hw].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. right.
  unfold mset_wr, mo_B1 in Hw. unfold mset_wr.
  rewrite (mo_n_ka Bw (MO_KA Bw) HL) in Hw. exact Hw.
Qed.

(* The post at the tail jump: m_set's post, entered with m_maybe_online's ra, sp and callee-saved registers on the
   same journal, is m_maybe_online's. *)
Lemma mo_tail_post : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw Bw' memT regsT,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MONLINE_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - MONLINE_STK -> spZ regs <= 2 ^ 47 ->
  length Bw = Z.to_nat TW.W_LEN ->
  TW.M_state Bw = TCB.S_WAKING -> TCB.truth (TW.M_e2_acked Bw) = true -> TCB.truth (TW.M_e1_us Bw) = true ->
  mo_KA mo_W W memc memT ->
  aregs_preserved regs regsT -> YK11.getr regsT 1 = YK11.getr regs 1 -> spZ regsT = spZ regs ->
  forall W2 c2,
  @transport_mset_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT k regsT (mo_B1 Bw) TCB.S_ONLINE Bw'
    W2 c2 ->
  @transport_monline_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' W2 c2.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' memT regsT
    LAWS HAR Hwin Hce H47 HL H1 H2 H3 KAT HP R1 Hsp W2 c2 HQ.
  pose proof KAT as [KA GA].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold transport_mset_post, transport_cg_post in HQ.
  destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e & Hc & He & HJ2 & HP2 & Hfr & Hperm & HK & HMO & HX).
  unfold transport_monline_post, transport_cg_post.
  exists ly2, S2, regs2, mem2, md2, e.
  split; [rewrite Hc, R1; reflexivity|].
  split; [unfold MONLINE_EV in *; exact He|].
  split; [exact HJ2|].
  split; [exact (aregs_preserved_trans regs regsT regs2 HP HP2)|].
  split; [exact Hfr|].
  split; [exact Hperm|].
  split.
  { rewrite Hsp in HK.
    eapply dk_kept_trans_g with (W1 := W) (memX := memT) (slo' := spZ regs - MSET_STK) (shi' := spZ regs)
      (Eo' := mset_st_wr (mo_B1 Bw) TCB.S_ONLINE).
    - exact Hce.
    - lia.
    - apply (dk_kept_step_g segs B LAWS transportb_segs_low TGB.G_HARNESS_B lyc Sc W memc mdc memc memT
        (spZ regs - MONLINE_STK) (spZ regs) (monline_wr Bw) mo_W HAR).
      + apply dk_kept_refl_g. exact Hwin.
      + intros a Ha Hn. exact (KA a Ha Hn).
      + exact GA.
      + intros a Hw Hcl. exfalso. unfold mo_W, TB_M in Hw. lia.
      + intros b m i Hb Hi Hw. exact (mo_wr_next Bw (b + i) H1 H2 H3 Hw).
      + intros a Hw _ HnG _ _. apply HnG. apply mo_inG_M. unfold mo_W, TW.SZ_M in *. lia.
      + intros cid pos a Hin Hr Hw. exact (mo_wr_next Bw a H1 H2 H3 Hw).
    - exact HK.
    - unfold MONLINE_STK. lia.
    - lia.
    - intros a Ha. exact (mo_wr_of_mset Bw a HL H1 H2 H3 Ha). }
  split; [exact HMO | exact HX].
Qed.

(* The bytes a literal chunk leaves in the final memory. *)
Lemma mo_cval : forall (W : world segs) mF (E : env) (base co : Z) (wd : N) (val : sv) (v : Z) (c : nat) (addr : Z) j,
  YP09.chunk_ok segs E (mrestrict (w_H W) mF) base (YP09.mkChunk co (CVal wd val)) ->
  Z.of_N wd = Z.of_nat c -> sv_denot E val = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_nat c) ->
  addr = base + co -> (j < c)%nat -> (c <= 8)%nat ->
  aview segs (w_H W) mF (addr + Z.of_nat j) = Some (YO.le_byte v c j).
Proof.
  intros W mF E base co wd val v c addr j Hch Hwd Hval Hv -> Hj Hc8.
  assert (Hv64 : 0 <= v < 2 ^ 64).
  { split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hv)|]. apply Z.pow_le_mono_r; lia. }
  destruct (Hch (Z.of_nat j) ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (bt & Hb & Hm).
  cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb. rewrite Hval in Hb.
  unfold YP09.byte_of_word in Hb. injection Hb as <-.
  unfold aview. cbn [YP09.c_off] in Hm. rewrite Hm. cbn [option_map]. f_equal.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small v (2 ^ 64)) by lia.
  unfold YO.le_byte. rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat c))) by lia. reflexivity.
Qed.

(* The world after the store at M.next_ka. *)
Lemma mo_world1 : forall (W : world segs) memc mT Bw,
  tw_at TMAP_B (aview segs (w_H W) memc) Bw -> mo_KA mo_W W memc mT ->
  (forall j, (j < 8)%nat -> aview segs (w_H W) mT (TB_M + 48 + Z.of_nat j) = Some (YO.le_byte (MO_KA Bw) 8 j)) ->
  tw_at TMAP_B (aview segs (w_H W) mT) (mo_B1 Bw).
Proof.
  intros W memc mT Bw Htw [KA _] HB.
  change (mo_B1 Bw) with (TW.upd Bw (TW.OFF_M + 48) (TW.put 8 (MO_KA Bw))).
  apply (tw_write TMAP_B (aview segs (w_H W) memc) _ Bw TW.OFF_M TB_M TW.SZ_M 48 8%nat (MO_KA Bw)
    TMAP_B_ok Htw TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_nat]; lia)).
  - exact HB.
  - intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh.
    unfold TGB.G_HARNESS_B_LO, TGB.G_HARNESS_B_HI in Hh.
    apply KA; [lia | unfold mo_W; lia].
Qed.

(* The region of M.next_ka is disjoint from the walk's two entry regions. *)
Lemma mo_N_disj : forall regs Bw, all_disjoint (mo_E regs Bw) mo_N mo_regions.
Proof.
  intros regs Bw.
  destruct mo_vals_img as (V8 & V31 & _ & _).
  assert (EOB : forall j, (j < 95)%nat -> ew (mo_E regs Bw) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold mo_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (B8 : base_val (mo_E regs Bw) (Some (A_OBJ 8)) = TB_M)
    by (cbn [base_val]; rewrite (EOB 8%nat ltac:(lia)), V8; apply unsigned_lit_small; unfold TB_M; lia).
  assert (B31 : base_val (mo_E regs Bw) (Some (A_OBJ 31)) = TB_g_cfg + 24)
    by (cbn [base_val]; rewrite (EOB 31%nat ltac:(lia)), V31; apply unsigned_lit_small; unfold TB_g_cfg; lia).
  unfold mo_regions, mo_N, mo_M, mo_K.
  cbn [all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B8, B31.
  unfold TB_M, TB_g_cfg. repeat split; lia.
Qed.

(* ---- the tactics of the walk ---- *)

(* The write right of a run: the entry regions have no writable byte; M.next_ka's window is bytes of G. *)
Ltac mo_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat first
  [ apply awr_ok_x_nil
  | apply awr_ok_x_cons_g;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      lazymatch goal with HU : bv_unsigned (ew _ 249) = TB_M |- _ => rewrite HU in Ha end;
      apply mo_inG_M; unfold TW.SZ_M; lia |]
  | apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; exfalso; lia |] ].

(* Every window of the state's regions lies in the walk's written set. *)
Ltac mo_cover :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in
  let xx := fresh "xx" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros bb wlo whi xx Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val] in Hx;
      try (lazymatch goal with HU : bv_unsigned (ew _ 249) = TB_M |- _ => rewrite HU in Hx end);
      first [ exfalso; lia | unfold mo_W; lia ] |]);
  destruct Hin.

(* After a run: the model generalized, the kept fact carried on, the old machine states dropped. *)
Ltac mo_after KAx :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt;
    try clear m0 end;
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    lazymatch type of KAx with
    | mo_KA ?Zs _ _ _ =>
      let KA' := fresh "KAn" in
      pose proof (mo_KA_step _ Zs rs _ _ _ _ ltac:(mo_cover) KAx HFr HG) as KA';
      clear KAx HFr HG; rename KA' into KA
    end end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  repeat match goal with old : machine_state |- _ => clear old end.

(* The split at a branch the run stopped on. *)
Ltac mo_branch HSx :=
  lazymatch type of HSx with
  | st_ok_pi ?sg ?vl ?Ex ?ss (restrict (w_H ?Wx) ?msx) =>
      let K := eval vm_compute in (run_K A_LIM MO_Bx MO_SH ss) in
      let why := psym_why_tok transportb_tpi transportb_tw K MO_Bx YC1i.Bspan MO_SH
                   (start K MO_Bx YC1i.Bspan MO_SH ss) in
      lazymatch why with
      | SR_branch ?c ?a ?b =>
          eapply (paj_branch _ Ex ss msx _ _ c a b HSx); clear HSx;
          let Hc := fresh "Hc" in intros Hc HSx
      | ?w => fail 1 "mo_branch: the run did not stop at a branch"
      end
  | ?T => fail 1 "mo_branch: bad state"
  end.

(* The tail of a path that returns at once: one run to the `ret`, then mo_close_ret. *)
Ltac mo_tailA RUNx HSx HJx SHOKx KAx EEx :=
  paj_run_tok RUNx HSx HJx SHOKx YC1i.Bspan;
  [ mo_awr
  | mo_after KAx;
    lazymatch goal with
    | |- SRr _ ?Wx (mkCfg ?msx _) (transport_monline_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?memcx _ ?regsx ?Bwx _) =>
      let RF1 := fresh "RF1" in let HPF := fresh "HPF" in
      mo_reg HSx (1%bv : bv 5) (YK11.getr regsx 1) RF1
        ltac:(cbn [sv_denot]; rewrite (EEx 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
      assert (HPF : aregs_preserved regsx (ms_regs msx))
        by (apply (aregs_preserved_of_st_ok segs (w_H Wx) (mo_E regsx Bwx) _ msx regsx (mo_vals Bwx) HSx);
            [exact (mo_agree regsx Bwx) | vm_compute; reflexivity]);
      eapply (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb) _ _ _ _ _ _ HSx eq_refl
                ltac:(vm_compute; reflexivity));
      let mat' := fresh "mat" in intros mat';
      eapply mo_close_ret; try eassumption
    end ].

Lemma mo_holds : @transport_m_maybe_online_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_m_maybe_online_cg_holds_stmt.
intros HCELLS LAWS MTL HGX HMS.
unfold transport_m_maybe_online_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw'
  HJ Hra Hra4 Hgp Htp Hsp16 Hlo Hhi Htw Hm Hev.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MONLINE_STK = 16) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - MONLINE_STK) by lia.
assert (Hwin : forall a, spZ regs - MONLINE_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw).
assert (HEI : img_env VAL A_LIM (mo_E regs Bw)) by (unfold mo_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (mo_E regs Bw) n = YK11.getr regs r)
  by (intros n r Hn; unfold mo_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 6)%nat -> ew (mo_E regs Bw) (32 + j) = nth j (mo_vals Bw) (Z_to_bv 64 0))
  by (intros j Hj; unfold mo_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth mo_vals] in E33, E34, E35, E36, E37.
clear EX.
destruct mo_vals_img as (V8 & V31 & VE & VS).
assert (U8 : bv_unsigned (ew (mo_E regs Bw) (A_OBJ 8)) = TB_M)
  by (unfold mo_E; rewrite (Eimg_img (Ereg regs (mo_vals Bw)) (A_OBJ 8) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V8;
      apply unsigned_lit_small; unfold TB_M; lia).
assert (U249 : bv_unsigned (ew (mo_E regs Bw) 249) = TB_M) by exact U8.
pose proof (mo_entry W regs memc Bw Htw) as HS.
assert (SHOK : sh_ok segs MO_Bx MO_SH (mo_E regs Bw) (mrestrict (w_H W) memc))
  by (unfold sh_ok, MO_SH; apply Forall_nil).
assert (KA : mo_KA (fun _ => False) W memc memc) by apply mo_KA_refl.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TGB.G_HARNESS_B HGX 0 []) as RUN.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_maybe_online)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x00 .. +0x10: a2 = &M, a0 = M.state, a1 = 1; it stops at `bne a0, a1`. *)
paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
{ mo_awr. }
mo_after KA.
mo_branch HS.
- (* path A1: M.state <> S_WAKING *)
  rewrite (mo_br_ne (mo_E regs Bw) Bw 33 TW.A_M_state 1 E33 ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (HST : TW.M_state Bw <> TCB.S_WAKING) by exact Hc. clear Hc.
  assert (HB0 : Bw' = Bw) by exact (mo_model_keep Bw Bw' (or_introl HST) Hm). subst Bw'.
  mo_tailA RUN HS HJ SHOK KA EE.
- rewrite (mo_br_ne (mo_E regs Bw) Bw 33 TW.A_M_state 1 E33 ltac:(lia)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (HST : TW.M_state Bw = TCB.S_WAKING) by exact Hc. clear Hc.
  (* run 2, +0x14 .. +0x18: M.e2_acked; it stops at `beqz`. *)
  paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
  { mo_awr. }
  mo_after KA.
  mo_branch HS.
  + (* path A2: M.e2_acked = 0 *)
    rewrite (mo_br_eq (mo_E regs Bw) Bw 34 TW.A_M_e2_acked 0 E34 ltac:(lia)) in Hc.
    apply Z.eqb_eq in Hc.
    assert (HE2z : TW.M_e2_acked Bw = 0) by exact Hc. clear Hc.
    assert (HB0 : Bw' = Bw) by exact (mo_model_keep Bw Bw' (or_intror (or_introl HE2z)) Hm). subst Bw'.
    mo_tailA RUN HS HJ SHOK KA EE.
  + rewrite (mo_br_eq (mo_E regs Bw) Bw 34 TW.A_M_e2_acked 0 E34 ltac:(lia)) in Hc.
    apply Z.eqb_neq in Hc.
    assert (HE2 : TW.M_e2_acked Bw <> 0) by exact Hc. clear Hc.
    (* run 3, +0x1c .. +0x20: M.e1_us; it stops at `beqz`. *)
    paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
    { mo_awr. }
    mo_after KA.
    mo_branch HS.
    * (* path A3: M.e1_us = 0 *)
      rewrite (mo_br_eq (mo_E regs Bw) Bw 35 TW.A_M_e1_us 0 E35 ltac:(lia)) in Hc.
      apply Z.eqb_eq in Hc.
      assert (HE1z : TW.M_e1_us Bw = 0) by exact Hc. clear Hc.
      assert (HB0 : Bw' = Bw) by exact (mo_model_keep Bw Bw' (or_intror (or_intror HE1z)) Hm). subst Bw'.
      mo_tailA RUN HS HJ SHOK KA EE.
    * (* path T: the three tests of :239 hold *)
      rewrite (mo_br_eq (mo_E regs Bw) Bw 35 TW.A_M_e1_us 0 E35 ltac:(lia)) in Hc.
      apply Z.eqb_neq in Hc.
      assert (HE1 : TW.M_e1_us Bw <> 0) by exact Hc. clear Hc.
      assert (HT2 : TCB.truth (TW.M_e2_acked Bw) = true) by (apply negb_true_iff, Z.eqb_neq; exact HE2).
      assert (HT1 : TCB.truth (TW.M_e1_us Bw) = true) by (apply negb_true_iff, Z.eqb_neq; exact HE1).
      pose proof (mo_model_set Bw Bw' HST HE2 HE1 Hm) as HMSET.
      (* the 8 bytes of M.next_ka join the state as a writable region of G *)
      pose proof (mo_KA_mono (fun _ => False) mo_W W memc _ ltac:(intros a []) KA) as KAw.
      clear KA. rename KAw into KA.
      lazymatch type of HS with
      | st_ok_pi _ _ ?Ey ?ssy (restrict (w_H ?Wy) ?msy) =>
        let ROK := fresh "ROK" in let RDJ := fresh "RDJ" in let HS3 := fresh "HSr" in
        assert (ROK : region_ok segs Ey (mrestrict (w_H Wy) (ms_mem msy)) mo_N)
          by (unfold mo_N, region_ok;
              cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
              rewrite U8; split; [unfold TB_M; lia|]; split; [unfold TB_M; lia|];
              split; [intros o Ho; apply mo_gwr; apply mo_inG_M; unfold TW.SZ_M; lia | apply Forall_nil]);
        assert (RDJ : all_disjoint Ey mo_N (ss_mem ssy))
          by (exact (all_disjoint_extents Ey mo_N mo_N mo_regions (ss_mem ssy) eq_refl
                       ltac:(vm_compute; reflexivity) (mo_N_disj regs Bw)));
        pose proof (st_ok_pi_add_region Ey ssy (restrict (w_H Wy) msy) mo_N HS
                      ltac:(vm_compute; reflexivity) ROK RDJ) as HS3;
        clear ROK RDJ; clear HS; rename HS3 into HS
      end.
      (* run 4, +0x24 .. +0x48: keepalive_ms, last_rx, the store at M + 48, a0 = 2, a1 = 2, the tail jump. *)
      paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
      { mo_awr. }
      mo_after KA.
      (* the world after the store *)
      lazymatch goal with
      | |- SRr _ ?Wx (mkCfg ?msx _) _ =>
        let RG := fresh "RG" in let HB := fresh "HB" in
        pose proof (st_ok_region_nth (mo_E regs Bw) _ (restrict (w_H Wx) msx) 0 _ HS eq_refl) as RG;
        cbn [ms_mem restrict] in RG;
        destruct RG as (_ & _ & _ & RG); apply Forall_inv in RG;
        cbn [YP09.r_base YP09.r_chunks base_val] in RG;
        try rewrite U249 in RG; try rewrite U8 in RG;
        assert (HB : forall j, (j < 8)%nat ->
          aview segs (w_H Wx) (ms_mem msx) (TB_M + 48 + Z.of_nat j) = Some (YO.le_byte (MO_KA Bw) 8 j))
          by (intros j Hj;
              exact (mo_cval Wx (ms_mem msx) (mo_E regs Bw) TB_M 48 8 _ (MO_KA Bw) 8%nat (TB_M + 48) j RG
                       eq_refl (mo_d_ka (mo_E regs Bw) Bw E36 E37)
                       ltac:(unfold MO_KA, TS0.u64; apply Z.mod_pos_bound; lia) eq_refl Hj ltac:(lia)));
        pose proof (mo_world1 Wx memc (ms_mem msx) Bw Htw KA HB) as HTW1
      end.
      (* m_set's contract at the jump's state, then mo_tail_post *)
      pmkst HS.
      mo_reg HS (1%bv : bv 5) (YK11.getr regs 1) R1
        ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      mo_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) R2
        ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      mo_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
        ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
      mo_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
        ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
      mo_reg HS (Z_to_bv 5 10) (w64 TCB.S_ONLINE) R10 ltac:(reflexivity).
      mo_reg HS (Z_to_bv 5 11) (w64 TCB.R_ONLINE) R11 ltac:(reflexivity).
      lazymatch goal with
      | |- SRr _ ?Wx (mkCfg ?msx _) _ =>
        let HPF := fresh "HPF" in let Hsp1 := fresh "Hsp1" in
        assert (HPF : aregs_preserved regs (ms_regs msx))
          by (apply (aregs_preserved_of_st_ok segs (w_H Wx) (mo_E regs Bw) _ _ regs (mo_vals Bw) HS);
              [exact (mo_agree regs Bw) | vm_compute; reflexivity]);
        assert (Hsp1 : spZ (ms_regs msx) = spZ regs) by exact (f_equal bv_unsigned R2);
        lazymatch goal with |- SRr ?sg ?Wy (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
          change (SRr sg Wy (@cfg_at fx segs (transportb_sigma TB_m_set) rg mm mdx) Q) end;
        eapply SRr_mono;
        [ exact (HMS fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msx) _ k (ms_regs msx)
                   TCB.S_ONLINE TCB.R_ONLINE (mo_B1 Bw) Bw' HJ
                   (eq_ind_r YK0s.ret_ok Hra R1) (eq_ind_r (fun w => 4096 <= bv_unsigned w) Hra4 R1) R3 R4 R10 R11
                   ltac:(rewrite Hsp1; exact Hsp16) ltac:(rewrite Hsp1; unfold MONLINE_STK, MSET_STK, MSET_FRAME in *; lia)
                   ltac:(rewrite Hsp1; exact Hhi) HTW1 HMSET
                   ltac:(unfold TCB.S_ONLINE; lia) ltac:(unfold TCB.R_ONLINE; lia)
                   ltac:(unfold MONLINE_EV, MSET_EV in *; lia))
        | intros W2 c2 _ HQ;
          exact (mo_tail_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' (ms_mem msx)
                   (ms_regs msx) LAWS HAR Hwin Hce ltac:(lia) HLB HST HT2 HT1 KA HPF R1 Hsp1 W2 c2 HQ) ]
      end.
Qed.

End mow.

Theorem transport_m_maybe_online_cg_holds :
  forall fx rc B MT, @transport_m_maybe_online_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@mo_holds fx rc B MT). Qed.
