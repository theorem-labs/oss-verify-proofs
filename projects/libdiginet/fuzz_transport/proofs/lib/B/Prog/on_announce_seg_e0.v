(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 551 of its 604 lines of code are new or changed and 1871 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SrxBRel.v, with its module paths and module names changed; 525 of its 597 lines of code are new or changed and 532 lines of the source are left out. *)
(* on_announce_seg_e0: Lemma onann_e0_piece : onann_e0_stmt (lib/B/Prog/OnannCutB.v), the e0 piece of the walk of
   on_announce on fuzz_transport.asan-ubsan (0x87cc8 = transportb_sigma TB_on_announce), code +0x3ec .. +0x420
   (0x880b4 .. 0x880e8), from the cut onann_e0_at to the cuts onann_sl1_at (+0x424) and onann_wk_at (+0x470).
   What the code does (:201-202; s4 = s, s8 = the shadow base, s1 = sp1):
     +0x3ec .. +0x3fc  a0 = s + 136, the check of the 4-byte store at s + 136: its shadow byte (g_s's zero shadow,
                       on_announce_cg.v trans_onann_cells, read by DgnTransportBCg.v decode_zshadow_rd) is 0, so
                       `bne a1, zero` is not taken;
     +0x400            `sw zero, 0(a0)`: g_s.foreign = 0 (:201), TW.set_S_foreign B2 0 (a range of G, of onann_wr);
     +0x404 .. +0x414  s10 = the shadow address of s + 112 (from sp1 + 32), its byte (0), s5 = now (from sp1 + 24),
                       s6 = s + 112 (from sp1 + 40), `bne a0, zero` not taken;
     +0x418 .. +0x41c  a0 = the 4-byte load at s + 112 (S_state, sign-extended), a1 = 2;
     +0x420            `bne a0, a1`: S_ONLINE falls through to +0x424 and concludes by onann_sl1_at; any other state
                       goes to +0x470 and concludes by onann_wk_at with B4 = set_S_foreign B2 0 and e = 0.
   One run (TransportGRunB.v paj_run_x) from a symbolic state whose regions are the three spill slots, g_s's state and
   foreign fields (absolute) and the two shadow bytes (literal 0), with s4 and s8 pinned to their literals; it stops
   at the `bne` of +0x420, which is taken up again from a state with no region (DgnTransportBPaLib.v
   psrr_branch_tok) and run one instruction to each cut. What the call keeps (acall_kept_g) crosses the store by
   TransportGFrame.v dk_kept_nfz_gw (the stored bytes are bytes of G); the world by TWorldG.v tw_write (oe0_fin);
   g_fail_next and onann_ri by oe0_gfn / oe0_ri (the store is inside g_s); the model by onann_k_e0's split on the
   state (oe0_st: the store keeps S_state). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The shadow bytes of s + 112 (g_s.state) and s + 136 (g_s.foreign). *)
Definition OE0_SH : Z := 2148220630.
Lemma oe0_sh_eq : OE0_SH = SHADOW_OFF + (ONANN_S + 112) / 8 /\ OE0_SH + 3 = SHADOW_OFF + (ONANN_S + 136) / 8.
Proof. split; reflexivity. Qed.
(* sp1 + 24 holds now (atom 33), sp1 + 32 the shadow address of s + 112, sp1 + 40 holds s + 112. *)
Definition OE0_R_slot : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 48 0 0
    [YP09.mkChunk 24 (YP09.CVal 8 (SOff 33 0)); YP09.mkChunk 32 (YP09.CVal 8 (SLit OE0_SH));
     YP09.mkChunk 40 (YP09.CVal 8 (SLit (ONANN_S + 112)))].
(* g_s.state, the 4 bytes of atom 32. *)
Definition OE0_R_st : YP09.region :=
  YP09.mkRegion None (ONANN_S + 112) (ONANN_S + 116) 0 0 [YP09.mkChunk (ONANN_S + 112) (YP09.CVal 4 (SOff 32 0))].
(* g_s.foreign, written. *)
Definition OE0_R_fg : YP09.region :=
  YP09.mkRegion None (ONANN_S + 136) (ONANN_S + 140) (ONANN_S + 136) (ONANN_S + 140) [].
(* The two shadow bytes, 0. *)
Definition OE0_R_sh : YP09.region :=
  YP09.mkRegion None OE0_SH (OE0_SH + 4) 0 0
    [YP09.mkChunk OE0_SH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (OE0_SH + 3) (YP09.CVal 1 (SLit 0))].
Definition OE0_FACTS : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
(* s4 = s and s8 = the shadow base, pinned to their literals. *)
Definition OE0_REGS : list sv :=
  sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit ONANN_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_oe0 : sstate := mkSS ONANN_E0 OE0_REGS [OE0_R_slot; OE0_R_st; OE0_R_fg; OE0_R_sh] None OE0_FACTS.
Definition OE0_Bx : sv := SLit 0.
Definition OE0_B0 : Z * Z := (0, 0).
(* +0x420, `bne a0, a1`, taken up again with no region. *)
Definition OE0_BR : Z := AF_on_announce + 0x420.
Definition ss_oe0b : sstate := mkSS OE0_BR sr_atoms [] None (mkFacts [] [] []).

(* ------------------------------------------------------------------ *)
(* 2. The model's facts                                                *)
(* ------------------------------------------------------------------ *)

Lemma oe0_fg_eq : forall Bx, TW.set_S_foreign Bx 0 = TW.upd Bx (TW.OFF_g_s + 136) (TW.put 4 0).
Proof. intros Bx. reflexivity. Qed.
Lemma oe0_state_at : forall X, TW.S_state X = bv_swrap 32 (TW.u_at X (TW.OFF_g_s + 112) 4).
Proof. intros X. reflexivity. Qed.

(* The store of g_s.foreign keeps g_s.state, g_fail_next and onann_ri. *)
Lemma oe0_st : forall Bx, length Bx = Z.to_nat TW.W_LEN ->
  TW.S_state (TW.set_S_foreign Bx 0) = TW.S_state Bx.
Proof.
intros Bx HL. assert (LZ : Z.of_nat (length Bx) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
unfold TW.set_S_foreign, TW.S_state.
rewrite TWL.s32_at_upd_out;
  [reflexivity | unfold TW.A_S_foreign, TW.OFF_g_s; lia | unfold TW.A_S_state, TW.OFF_g_s; lia
  | rewrite TWL.length_put; unfold TW.A_S_foreign, TW.A_S_state, TW.OFF_g_s; lia
  | rewrite TWL.length_put, LZ; unfold TW.A_S_foreign, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

Lemma oe0_gfn : forall Bx, length Bx = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (TW.set_S_foreign Bx 0) = TW.g_fail_next Bx.
Proof.
intros Bx HL. assert (LZ : Z.of_nat (length Bx) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
unfold TW.set_S_foreign, TW.g_fail_next.
rewrite TWL.u_at_upd_out;
  [reflexivity | unfold TW.A_S_foreign, TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia
  | rewrite TWL.length_put; unfold TW.A_S_foreign, TW.OFF_g_s, TW.OFF_g_fail_next; lia
  | rewrite TWL.length_put, LZ; unfold TW.A_S_foreign, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

Lemma oe0_ri : forall Bx, length Bx = Z.to_nat TW.W_LEN -> onann_ri Bx -> onann_ri (TW.set_S_foreign Bx 0).
Proof.
intros Bx HL (R1 & R2 & R3). assert (LZ : Z.of_nat (length Bx) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
assert (LV : TW.A_S_foreign + Z.of_nat (length (TW.put 4 0)) <= Z.of_nat (length Bx))
  by (rewrite TWL.length_put, LZ; unfold TW.A_S_foreign, TW.OFF_g_s, TW.W_LEN; lia).
assert (LP : Z.of_nat (length (TW.put 4 0)) = 4) by (rewrite TWL.length_put; reflexivity).
assert (EON : TW.M_fly_on (TW.set_S_foreign Bx 0) = TW.M_fly_on Bx).
{ unfold TW.set_S_foreign, TW.M_fly_on. rewrite TWL.s32_at_upd_out; [reflexivity | | | | exact LV];
  unfold TW.A_S_foreign, TW.A_M_fly_on, TW.OFF_g_s, TW.OFF_M; rewrite ?LP; lia. }
assert (ELN : TW.M_fly_len (TW.set_S_foreign Bx 0) = TW.M_fly_len Bx).
{ unfold TW.set_S_foreign, TW.M_fly_len. rewrite TWL.u_at_upd_out; [reflexivity | | | | exact LV];
  unfold TW.A_S_foreign, TW.A_M_fly_len, TW.OFF_g_s, TW.OFF_M; rewrite ?LP; lia. }
assert (ENC : TW.g_ncmd (TW.set_S_foreign Bx 0) = TW.g_ncmd Bx).
{ unfold TW.set_S_foreign, TW.g_ncmd. rewrite TWL.u_at_upd_out; [reflexivity | | | | exact LV];
  unfold TW.A_S_foreign, TW.OFF_g_s, TW.OFF_g_ncmd; rewrite ?LP; lia. }
assert (EST : forall s, 0 <= s -> TW.Cmd_st (TW.set_S_foreign Bx 0) s = TW.Cmd_st Bx s).
{ intros s Hs. unfold TW.set_S_foreign, TW.Cmd_st. rewrite TWL.s32_at_upd_out; [reflexivity | | | | exact LV];
  unfold TW.A_S_foreign, TW.A_Cmd_st, TW.OFF_g_s, TW.OFF_g_cmd; rewrite ?LP; lia. }
assert (ECL : forall s, 0 <= s -> TW.Cmd_len (TW.set_S_foreign Bx 0) s = TW.Cmd_len Bx s).
{ intros s Hs. unfold TW.set_S_foreign, TW.Cmd_len. rewrite TWL.u_at_upd_out; [reflexivity | | | | exact LV];
  unfold TW.A_S_foreign, TW.A_Cmd_len, TW.OFF_g_s, TW.OFF_g_cmd; rewrite ?LP; lia. }
split; [|split].
- rewrite EON, ELN. exact R1.
- intros s Hs Hp. rewrite ENC in Hs. rewrite (EST s ltac:(lia)) in Hp. rewrite (ECL s ltac:(lia)). exact (R2 s Hs Hp).
- rewrite ENC. exact R3.
Qed.

(* `bne a0, a1` on the sign-extended state and 2. *)
Lemma oe0_eqb2 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 2) = (v =? 2).
Proof.
intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 2 (2 ^ 64)) by lia.
destruct (Z.eqb_spec v 2) as [-> | Hne]; [reflexivity|].
apply Z.eqb_neq. intros HH. apply Hne.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

Lemma oe0_state_range : forall Bx, - 2 ^ 31 <= TW.S_state Bx < 2 ^ 31.
Proof. intros Bx. unfold TW.S_state. apply TWL.s32_range. Qed.

(* The sign-extended 4-byte load of g_s's state is the model's S_state. *)
Lemma oe0_sext : forall E X, ew E 32 = Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_state X).
Proof.
intros E X H.
assert (R : 0 <= TW.u_at X (TW.OFF_g_s + 112) 4 < 2 ^ 32) by exact (TWL.u_at_range X _ 4).
cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. rewrite oe0_state_at. reflexivity.
Qed.

(* A byte of the view read as 0 is a stored 0. *)
Lemma oe0_vm0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview tfibsegs H m a = Some 0 -> val_mem tfibsegs (mrestrict H m) a 1 0.
Proof.
intros H m a Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Hv].
cbn in Hv. injection Hv as Hb. change (YO0f.le_byte 0 1 0) with 0.
f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* A chunk of w bytes of the value e reads the little-endian bytes of e. *)
Lemma oe0_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* The bytes of a value in memory, read byte by byte through the view. *)
Lemma oe0_aview_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v -> forall j, (j < n)%nat ->
  aview tfibsegs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma oe0_inG : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, ONANN_S, TB_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Tactics                                                          *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac oe0_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Register r, whose symbolic value is atom n, the start value of register r (Q its value): the run's valuation
   agrees with the start valuation below atom 1024 (Elo), which reads the registers (EE). *)
Ltac oe0_kreg HS Elo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    oe0_reg HS r v H
      ltac:(cbn [sv_denot]; try rewrite (Elo n ltac:(lia)); rewrite (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
            exact Q) end.
Ltac oe0_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac oe0_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac oe0_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The write right of the run: every region but g_s.foreign writes nothing; g_s.foreign is a range of G. *)
Ltac oe0_awr :=
  oe0_awr_rs;
  repeat (first
    [ apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]
    | apply awr_ok_x_cons_g;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
        apply oe0_inG; unfold ONANN_S, TB_g_s, TW.SZ_g_s in *; lia |] ]);
  apply awr_ok_x_nil.
(* The windows of a run's start state, computed, against the bytes Zs a run may change. *)
Ltac oe0_win Hin Hx :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
          [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]);
  destruct Hin.
(* The model of the goal, named. *)
Ltac oe0_name_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md := m) in *; clearbody md end.
(* After a run: its valuation agrees with the start valuation E0 below atom 1024 (Hlo), and its machine state is
   named m. *)
Ltac oe0_lo HS E0 Hlo m :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  end.

(* ------------------------------------------------------------------ *)
(* 4. The entry states                                                 *)
(* ------------------------------------------------------------------ *)

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The valuation of the run: the registers at the cut, then the 4 bytes of g_s's state in B2 (atom 32) and now
   (atom 33). *)
Definition oe0_E (regs : bvmap 5 word) (Bx : list byte) (now : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4); Z_to_bv 64 now]).

Lemma oe0_entry0 : forall ly S (W : world segs) regs mem md Bx sp1 now,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 9 = w64 sp1 ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 0 <= now < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 24) = Some now ->
  rdword (aview segs (w_H W) mem) (sp1 + 32) = Some OE0_SH ->
  rdword (aview segs (w_H W) mem) (sp1 + 40) = Some (ONANN_S + 112) ->
  st_ok_pi segs VAL (oe0_E regs Bx now)
    (mkSS ONANN_E0 sr_atoms [OE0_R_slot; OE0_R_st; OE0_R_fg; OE0_R_sh] None OE0_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_E0)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
intros ly S W regs mem md Bx sp1 now HZC HAR Htw R9 Hsp Hsp32 Hnow S24 S32 S40.
set (E := oe0_E regs Bx now).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, oe0_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4))
  by (unfold E, oe0_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 now)
  by (unfold E, oe0_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 112) 4) as R32.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R32.
assert (U32 : bv_unsigned (ew E 32) = TW.u_at Bx (TW.OFF_g_s + 112) 4)
  by (rewrite E32; apply unsigned_lit_small; lia).
assert (ZSH : forall j, j = 0 \/ j = 3 -> val_mem segs (mrestrict (w_H W) mem) (OE0_SH + j) 1 0).
{ intros j Hj. apply oe0_vm0.
  replace (OE0_SH + j) with (FCells.shadow_addr (ONANN_S + 112 + 8 * j)).
  - apply (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) _ HAR); [| | | exact HZC].
    + unfold ONANN_S, TB_g_s. destruct Hj as [-> | ->]; reflexivity.
    + destruct Hj as [-> | ->]; lia.
    + unfold TW.SZ_g_s. destruct Hj as [-> | ->]; unfold ONANN_S, TB_g_s; lia.
  - unfold FCells.shadow_addr, FCells.ASAN_K, OE0_SH, ONANN_S, TB_g_s.
    destruct Hj as [-> | ->]; reflexivity. }
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks OE0_R_slot OE0_R_st OE0_R_fg OE0_R_sh
      base_val]; rewrite ?U9.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (chunk_ok_val segs E _ sp1 24 8 (SOff 33 0) now);
        [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      exact (YCbq.val_mem_of_rdword segs (w_H W) mem _ _ S24).
    * apply (chunk_ok_val segs E _ sp1 32 8 (SLit OE0_SH) OE0_SH);
        [reflexivity | unfold OE0_SH; lia | lia |].
      exact (YCbq.val_mem_of_rdword segs (w_H W) mem _ _ S32).
    * apply (chunk_ok_val segs E _ sp1 40 8 (SLit (ONANN_S + 112)) (ONANN_S + 112));
        [reflexivity | unfold ONANN_S, TB_g_s; lia | lia |].
      exact (YCbq.val_mem_of_rdword segs (w_H W) mem _ _ S40).
  + split; [unfold ONANN_S, TB_g_s; lia|]. split; [unfold ONANN_S, TB_g_s; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ 0 (ONANN_S + 112) 4 (SOff 32 0) (TW.u_at Bx (TW.OFF_g_s + 112) 4));
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | lia |].
    replace (0 + (ONANN_S + 112)) with (TB_g_s + 112) by (unfold ONANN_S; lia).
    exact (tw_read_val segs _ TMAP_B Bx TW.OFF_g_s TB_g_s TW.SZ_g_s 112 4 TMAP_B_ok Htw TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + split; [unfold ONANN_S, TB_g_s; lia|]. split; [unfold ONANN_S, TB_g_s; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (0 + o) G_HARNESS_B_rw).
    apply oe0_inG. unfold TW.SZ_g_s. lia.
  + split; [unfold OE0_SH; lia|]. split; [unfold OE0_SH; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val segs E _ 0 OE0_SH 1 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_l. pose proof (ZSH 0 ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
    * apply (chunk_ok_val segs E _ 0 (OE0_SH + 3) 1 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_l. exact (ZSH 3 ltac:(lia)).
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, OE0_R_slot, OE0_R_st, OE0_R_fg, OE0_R_sh.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold OE0_SH, ONANN_S, TB_g_s. repeat split; first [exact I | lia].
- unfold OE0_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U32.
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma oe0_entry : forall ly S (W : world segs) regs mem md Bx sp1 now,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 0 <= now < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 24) = Some now ->
  rdword (aview segs (w_H W) mem) (sp1 + 32) = Some OE0_SH ->
  rdword (aview segs (w_H W) mem) (sp1 + 40) = Some (ONANN_S + 112) ->
  st_ok_pi segs VAL (oe0_E regs Bx now) ss_oe0
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_E0)) mem (YK11.seg_rom segs))).
Proof.
intros ly S W regs mem md Bx sp1 now HZC HAR Htw R9 R20 R24 Hsp Hsp32 Hnow S24 S32 S40.
rewrite restrict_mkst_fx.
pose proof (oe0_entry0 ly S W regs mem md Bx sp1 now HZC HAR Htw R9 Hsp Hsp32 Hnow S24 S32 S40) as H0.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) ONANN_S H0 R20 eq_refl) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
exact H2.
Qed.

(* The state at +0x420 with no region. *)
Lemma oe0_entryb : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) ss_oe0b
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OE0_BR)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold ss_oe0b.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.
End ent.

(* ------------------------------------------------------------------ *)
(* 5. The facts both cuts carry, and the piece                          *)
(* ------------------------------------------------------------------ *)

Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* onann_cur and the world relation at a later memory mF of the same state whose view differs from the cut's at
   most at g_s.foreign [s + 136, s + 140), which holds 0 there: the world is set_S_foreign B2 0. *)
Lemma oe0_fin : AR_laws segs B -> frame_flag_lawP segs B -> gx_ok segs B TG.G_HARNESS_B ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bw b : list byte)
         (pos F : Z) (B2 : list byte) (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 mF : word -> option byte)
         (md2 mdF : Model),
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= spZ regs - ONANN_STK -> spZ regs <= sp0 ->
  F = frame_addr lyc ONANN_CID pos -> 4096 <= F -> F + ONANN_FBYTES <= alloc_ceiling ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 ->
  tw_at TMAP_B (aview segs (w_H W2) mem2) B2 ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mF mdF (k + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ONANN_S + 136 <= a < ONANN_S + 140) ->
     aview segs (w_H W2) mF a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mF a) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W2) mF (ONANN_S + 136 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mF mdF 0 /\
  tw_at TMAP_B (aview segs (w_H W2) mF) (TW.set_S_foreign B2 0).
Proof.
intros LAWS FFL HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw b pos F B2 ly2 S2 W2 mem2 mF md2 mdF
  HJe Hlo Hhi EF HF0 HFc HCUR Htw2 HJF KF GF VF.
pose proof HCUR as (HJ2 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CS : ONANN_S = 6157888) by reflexivity.
unfold ONANN_FBYTES in HFc, HFLw.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
pose proof HJe as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HSTKb : 4096 <= ONANN_STK) by (vm_compute; intros Hx; discriminate Hx).
assert (Hsp : alloc_ceiling <= spZ regs - ONANN_STK /\ spZ regs <= 2 ^ 47) by lia.
destruct Hsp as [Hspc Hsp47].
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F
  (flag_addr lyc ONANN_CID pos) HAR2 Hfrs Hbl HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
assert (NGS : forall a, ONANN_S + 136 <= a < ONANN_S + 140 -> inG TG.G_HARNESS_B a)
  by (intros a Ha; apply oe0_inG; unfold TW.SZ_g_s; lia).
split.
- refine (conj HJF (conj He0 (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj _ (conj _ _)))))))).
  + apply (dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2 mF
      (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F (flag_addr lyc ONANN_CID pos) (onann_wr Bw b)
      (fun x => ONANN_S + 136 <= x < ONANN_S + 140) HGX HARc HAR2 Hfrs Hbl HlyF EF eq_refl FFL);
      [lia | lia | | exact HK | exact KF | exact GF].
    intros a Ha. right; right. exact (NGS a Ha).
  + apply Forall_forall. intros o Hin. cbv beta.
    pose proof (proj1 (Forall_forall _ _) Hsaved o Hin) as Hv. cbv beta in Hv.
    assert (Ho : 8 <= fst o <= 104).
    { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
    rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KF; lia.
  + unfold ONANN_FBYTES. rewrite <- HFLw. apply YCbq.rdword_ext. intros i Hi. apply KF; [lia|].
    intros X. apply (N2 (F + 512 - 8 + i)).
    * left. rewrite onann_fbytes. unfold ONANN_FBYTES. lia.
    * destruct (HGX _ (NGS _ X)) as [Hi' _]. exact Hi'.
- rewrite oe0_fg_eq.
  apply (tw_write TMAP_B (aview segs (w_H W2) mem2) (aview segs (w_H W2) mF) B2 TW.OFF_g_s TB_g_s TW.SZ_g_s 136 4 0
    TMAP_B_ok Htw2 TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
  + intros j Hj. exact (VF j Hj).
  + intros x Hx Hn.
    assert (Hg : inG TG.G_HARNESS_B x).
    { destruct Hx as (o & b0 & n & Hin & Hb). pose proof (TMAP_B_in_G o b0 n Hin) as HG0.
      unfold inG. apply Exists_exists. exists (b0, n). split; [exact HG0 | unfold in_zr; cbn [fst snd]; lia]. }
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX Hg) as Hl. unfold kLowMemEnd in Hl.
    apply KF; [lia|]. intros X. apply Hn. unfold ONANN_S in X. lia.
Qed.

Lemma oe0_holds : @onann_e0_stmt fx rc B MT.
Proof.
unfold onann_e0_stmt. intros SL1 WK. unfold onann_e0_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F B2
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HZC & HGU & HGNE & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof HFIX as (HJe & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & Hdf & Htw0 & Hgf0 & Hm &
  HTF & Htfg & Hrom & Hap & Hri0 & Hcnt1 & Hcnt2 & Hcnt3 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (CUR0 & Htw2 & Hb2 & Hcmd & Hk0 & Hgf2 & Hri2 & (S32 & S40) & S24).
pose proof CUR0 as (HJ2 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25) & R20 & R24).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CS : ONANN_S = 6157888) by reflexivity.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
pose proof HJe as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HSTKb : 4096 <= ONANN_STK) by (vm_compute; intros Hx; discriminate Hx).
assert (HFR : ONANN_FRAME = 192) by reflexivity.
assert (Hsp1 : spZ regs - 224 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1, HFR.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  set (q := (spZ regs - 192) / 32) in *. set (rr := (spZ regs - 192) mod 32) in *.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult. }
destruct Hsp1 as [Hsp1 Hsp132].
assert (Hsp1r : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
assert (HLB2 : length B2 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw2).
assert (EST : TW.S_state (TW.set_S_foreign B2 0) = TW.S_state B2) by exact (oe0_st B2 HLB2).
assert (EGF : TW.g_fail_next (TW.set_S_foreign B2 0) <= 1) by (rewrite (oe0_gfn B2 HLB2); exact Hgf2).
assert (ERI : onann_ri (TW.set_S_foreign B2 0)) by exact (oe0_ri B2 HLB2 Hri2).
assert (HEV : 0 + WAKE_EV <= ONANN_EV) by (vm_compute; intros Hx; discriminate Hx).
(* +0x3ec .. +0x420: the run; it stops at the `bne` *)
pose proof (oe0_entry (fx := fx) B ly2 S2 W2 regs2 mem2 md2 B2 sp1 now HZC HAR2 Htw2 R9 R20 R24 Hsp1r Hsp132 Hnow S24
  ltac:(rewrite (proj1 oe0_sh_eq); exact S32) S40) as HS.
set (E0 := oe0_E regs2 B2 now) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, oe0_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, oe0_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E0 32 = Z_to_bv 64 (TW.u_at B2 (TW.OFF_g_s + 112) 4))
  by (unfold E0, oe0_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 now)
  by (unfold E0, oe0_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (SHOK : sh_ok segs OE0_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
pose proof HJ2 as HJ.
paj_run_tok RUN HS HJ SHOK OE0_B0.
{ oe0_awr. }
oe0_name_md md5.
oe0_lo HS E0 E1lo ms5.
(* the registers at +0x420 *)
oe0_reg HS (10%bv : bv 5) (Z_to_bv 64 (TW.S_state B2)) X10
  ltac:(apply oe0_sext; try rewrite (E1lo 32%nat ltac:(lia)); exact E32).
oe0_reg HS (11%bv : bv 5) (Z_to_bv 64 2) X11 ltac:(reflexivity).
oe0_reg HS (21%bv : bv 5) (w64 now) X21
  ltac:(cbn [sv_denot]; try rewrite (E1lo 33%nat ltac:(lia)); rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
oe0_reg HS (22%bv : bv 5) (w64 (ONANN_S + 112)) X22 ltac:(reflexivity).
oe0_reg HS (26%bv : bv 5) (w64 (SHADOW_OFF + (ONANN_S + 112) / 8)) X26 ltac:(reflexivity).
oe0_reg HS (20%bv : bv 5) (w64 ONANN_S) X20 ltac:(reflexivity).
oe0_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) X24 ltac:(reflexivity).
oe0_kreg HS E1lo EE (2%bv : bv 5) 2%nat R2 X2. oe0_kreg HS E1lo EE (3%bv : bv 5) 3%nat R3 X3.
oe0_kreg HS E1lo EE (4%bv : bv 5) 4%nat R4 X4. oe0_kreg HS E1lo EE (8%bv : bv 5) 8%nat R8 X8.
oe0_kreg HS E1lo EE (9%bv : bv 5) 9%nat R9 X9. oe0_kreg HS E1lo EE (18%bv : bv 5) 18%nat R18 X18.
oe0_kreg HS E1lo EE (19%bv : bv 5) 19%nat R19 X19. oe0_kreg HS E1lo EE (25%bv : bv 5) 25%nat R25 X25.
(* the run wrote g_s.foreign only, with 0 *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (ONANN_S + 136 <= a < ONANN_S + 140) ->
  aview segs (w_H W2) (ms_mem ms5) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => ONANN_S + 136 <= x < ONANN_S + 140) HFr);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. cbv beta. oe0_win Hin Hx. }
assert (GR5 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms5) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
oe0_region HS 2%nat HR2.
lazymatch type of HR2 with
| region_ok _ ?Ex _ (YP09.mkRegion ?bo ?lo ?hi ?wl ?wh [YP09.mkChunk ?off (CVal ?w ?ev)]) =>
    pose proof (oe0_chunk_val Ex (w_H W2) (ms_mem ms5) bo lo hi wl wh _ off w ev HR2 ltac:(oe0_in) ltac:(lia)) as VG;
    replace (bv_unsigned (sv_denot Ex ev) mod 2 ^ (8 * Z.of_N w)) with 0 in VG by reflexivity
end.
cbn [base_val] in VG. change (N.to_nat 4) with 4%nat in VG.
assert (VG5 : forall j, (j < 4)%nat ->
  aview segs (w_H W2) (ms_mem ms5) (ONANN_S + 136 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)).
{ intros j Hj. pose proof (oe0_aview_of_val _ _ _ 4 _ VG j Hj) as Hb.
  replace (ONANN_S + 136 + Z.of_nat j) with (0 + 6158024 + Z.of_nat j) by (rewrite CS; lia). exact Hb. }
clear HR2 VG HF HFr HG.
(* +0x420: `bne a0, a1`, taken up again from a state with no region *)
pmkst HS.
clear HS SHOK.
set (r5 := ms_regs ms5) in *. set (m5 := ms_mem ms5) in *. clearbody r5 m5.
pose proof (oe0_entryb (fx := fx) W2 r5 m5) as HS.
set (Eb := Eimg (PI := PI_transportb) (Ereg r5 [])) in HS.
assert (SHOK : sh_ok segs OE0_Bx (@nil shent) Eb (mrestrict (w_H W2) m5)) by constructor.
assert (HEIb : img_env VAL A_LIM Eb) by (unfold Eb; apply Eimg_env).
assert (EEb : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Eb n = YK11.getr r5 r)
  by (intros n r Hn; unfold Eb; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (D10 : sv_denot Eb (SOff 10 0) = Z_to_bv 64 (TW.S_state B2))
  by (cbn [sv_denot]; rewrite (EEb 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X10).
assert (D11 : sv_denot Eb (SOff 11 0) = Z_to_bv 64 2)
  by (cbn [sv_denot]; rewrite (EEb 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X11).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OE0_BR)) mm rom) mdx) Q) end.
pose proof (oe0_state_range B2) as HSR.
assert (HLAWS : onann_laws B MT) by exact LAWS0.
psrr_branch_tok RUN BR HS SHOK OE0_B0.
- (* taken: S_state <> S_ONLINE, to the wake test +0x470 *)
  cbn [branch_taken] in Hc. rewrite D10, D11, (oe0_eqb2 _ HSR) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (HK4 : onann_k_wk timg_B TF (TW.set_S_foreign B2 0) now = Some (Bw', tt)).
  { unfold onann_k_e0 in Hk0.
    replace (TW.S_state (TW.set_S_foreign B2 0) =? TS0.DIGINET_S_ONLINE) with false in Hk0
      by (symmetry; apply Z.eqb_neq; rewrite EST; exact Hc).
    exact Hk0. }
  paj_run_to_tok RUNTO HS HJ SHOK OE0_B0 ONANN_WK.
  { oe0_awr_rs. apply awr_ok_x_nil. }
  oe0_name_md mdF.
  oe0_lo HS Eb EFlo msF.
  oe0_kreg HS EFlo EEb (2%bv : bv 5) 2%nat X2 Y2. oe0_kreg HS EFlo EEb (3%bv : bv 5) 3%nat X3 Y3.
  oe0_kreg HS EFlo EEb (4%bv : bv 5) 4%nat X4 Y4. oe0_kreg HS EFlo EEb (8%bv : bv 5) 8%nat X8 Y8.
  oe0_kreg HS EFlo EEb (9%bv : bv 5) 9%nat X9 Y9. oe0_kreg HS EFlo EEb (18%bv : bv 5) 18%nat X18 Y18.
  oe0_kreg HS EFlo EEb (19%bv : bv 5) 19%nat X19 Y19. oe0_kreg HS EFlo EEb (25%bv : bv 5) 25%nat X25 Y25.
  oe0_kreg HS EFlo EEb (20%bv : bv 5) 20%nat X20 Y20. oe0_kreg HS EFlo EEb (24%bv : bv 5) 24%nat X24 Y24.
  oe0_kreg HS EFlo EEb (10%bv : bv 5) 10%nat X10 Y10. oe0_kreg HS EFlo EEb (21%bv : bv 5) 21%nat X21 Y21.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) m5 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta. oe0_win Hin Hx. }
  assert (GB : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msF) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GR5 a Ha))).
  destruct (oe0_fin LAWS FFL HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw b pos F B2 ly2 S2 W2
    mem2 (ms_mem msF) md2 mdF HJe Hlo Hhi EF HF0 HFc CUR0 Htw2 HJ
    ltac:(intros a Ha Hn; rewrite (KB a Ha); exact (KR a Ha Hn)) GB
    ltac:(intros j Hj; rewrite (KB (ONANN_S + 136 + Z.of_nat j) ltac:(rewrite CS; lia)); exact (VG5 j Hj)))
    as (CURF & TWF).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_WK)) mm rom) mdx) Q) end.
  apply (WK HLAWS CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    (TW.set_S_foreign B2 0) ly2 S2 W2 (ms_mem msF) mdF 0 (ms_regs msF) HFIX).
  + exact (conj CURF (conj HEV (conj TWF (conj HK4 (conj EGF ERI))))).
  + refine (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 (conj Y19 Y25))))))) (conj Y20 Y24))
      (conj _ Y21)).
    rewrite Y10, EST. reflexivity.
- (* not taken: S_state = S_ONLINE, to the first inlined session_lost +0x424 *)
  cbn [branch_taken] in Hc. rewrite D10, D11, (oe0_eqb2 _ HSR) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (HON : TW.S_state (TW.set_S_foreign B2 0) = TS0.DIGINET_S_ONLINE) by (rewrite EST; exact Hc).
  assert (HK1 : onann_k_sl1 timg_B TF (TW.set_S_foreign B2 0) now = Some (Bw', tt)).
  { unfold onann_k_e0 in Hk0.
    replace (TW.S_state (TW.set_S_foreign B2 0) =? TS0.DIGINET_S_ONLINE) with true in Hk0
      by (symmetry; apply Z.eqb_eq; exact HON).
    exact Hk0. }
  paj_run_to_tok RUNTO HS HJ SHOK OE0_B0 ONANN_SL1.
  { oe0_awr_rs. apply awr_ok_x_nil. }
  oe0_name_md mdF.
  oe0_lo HS Eb EFlo msF.
  oe0_kreg HS EFlo EEb (2%bv : bv 5) 2%nat X2 Y2. oe0_kreg HS EFlo EEb (3%bv : bv 5) 3%nat X3 Y3.
  oe0_kreg HS EFlo EEb (4%bv : bv 5) 4%nat X4 Y4. oe0_kreg HS EFlo EEb (8%bv : bv 5) 8%nat X8 Y8.
  oe0_kreg HS EFlo EEb (9%bv : bv 5) 9%nat X9 Y9. oe0_kreg HS EFlo EEb (18%bv : bv 5) 18%nat X18 Y18.
  oe0_kreg HS EFlo EEb (19%bv : bv 5) 19%nat X19 Y19. oe0_kreg HS EFlo EEb (25%bv : bv 5) 25%nat X25 Y25.
  oe0_kreg HS EFlo EEb (20%bv : bv 5) 20%nat X20 Y20. oe0_kreg HS EFlo EEb (24%bv : bv 5) 24%nat X24 Y24.
  oe0_kreg HS EFlo EEb (21%bv : bv 5) 21%nat X21 Y21. oe0_kreg HS EFlo EEb (22%bv : bv 5) 22%nat X22 Y22.
  oe0_kreg HS EFlo EEb (26%bv : bv 5) 26%nat X26 Y26.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) m5 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta. oe0_win Hin Hx. }
  assert (GB : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msF) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GR5 a Ha))).
  destruct (oe0_fin LAWS FFL HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw b pos F B2 ly2 S2 W2
    mem2 (ms_mem msF) md2 mdF HJe Hlo Hhi EF HF0 HFc CUR0 Htw2 HJ
    ltac:(intros a Ha Hn; rewrite (KB a Ha); exact (KR a Ha Hn)) GB
    ltac:(intros j Hj; rewrite (KB (ONANN_S + 136 + Z.of_nat j) ltac:(rewrite CS; lia)); exact (VG5 j Hj)))
    as (CURF & TWF).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_SL1)) mm rom) mdx) Q) end.
  apply (SL1 HLAWS CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    B2 ly2 S2 W2 (ms_mem msF) mdF (ms_regs msF) HFIX).
  + exact (conj CURF (conj TWF (conj Hb2 (conj HON (conj HK1 (conj EGF ERI)))))).
  + exact (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 (conj Y19 Y25))))))) (conj Y20 Y24))
      (conj Y21 (conj Y22 Y26))).
Qed.
End main.

(* The e0 piece of the walk of on_announce (OnannCutB.v onann_e0_stmt), at every machine, run ceiling, record and
   meter. *)
Lemma onann_e0_piece : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT, @onann_e0_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@oe0_holds fx rc B MT). Qed.
