(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 328 of its 383 lines of code are new or changed and 432 lines of the source are left out. *)
(* TickBRetx_ent: what the retransmit piece of diginet_session_tick's image-B G-form walk (TickBRetx.v, code +0x34c ..
   +0x440 = 0x893e8 .. 0x894dc and +0x594 .. +0x5bc = 0x89630 .. 0x89658 of fuzz_transport.asan-ubsan) needs besides
   the walk itself, none of it about a machine state: the code points and the shadow bytes of its checks; the symbolic
   states of its two runs (run 1 from the retx cut to `jalr a4` at +0x424, run 2 from io_send's return at +0x428; their
   entry proofs are TickBRetx.v's rx_entry1, rx_entry2z, rx_entry2n); the world after retransmit's five stores (rx_w,
   rx_w_eq) and the model on this path (rx_model: TSess.v retransmit_m, send_raw_m, call_send, io_send's result 0 or
   -EIO by TModel/TIoSendFail.v io_send_m_ret); the bytes the code stores, read as the model's (rx_tw_step, the byte
   lemmas); io_send's written range inside tick_wr's (rx_iosend_wr); and the tactics rx_awr, rx_atom. Image B's code
   differs from image A's retransmit block in its registers (the retries + 1 in a4, s + 216 in a1 from +0x358, the
   shadow addresses in a5, s + 18144 saved in s9) and in the two UBSan pointer-overflow checks at +0x364 (`bgeu a1,
   a2`, a2 = 2 ^ 64 - 26) and +0x388 (`bltu a6, a1`, a6 = 2 ^ 64 - 28), which the run decides on the literal
   s + 216 = 0x5df718. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0a YO0c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
io_send_cg set_state_cg take_cg send_data_cg diginet_session_tick_cg TickCutB TickBKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TickCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TIoSendFail TOpsKeep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
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
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TIF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TIoSendFail.
Module TOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOpsKeep.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module TCA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TickCut.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- the code points and the fixed addresses ---- *)

(* The return point of io_send (+0x428, `beqz a0`) and the r = 0 arm (+0x594). *)
Definition RX_RET : Z := AF_diginet_session_tick + 0x428.
(* The shadow bytes the run's checks read: of s + 64 (and s + 72 next to it), of s + 242 / s + 243, of s + 1736 (and
   s + 1748, s + 1752 after it), of s + 18232, and run 2's of s + 18192. *)
Definition RX_SH64 : Z := 2148220624.
Definition RX_SH242 : Z := 2148220646.
Definition RX_SH1736 : Z := 2148220833.
Definition RX_SH18232 : Z := 2148222895.
Definition RX_SH18192 : Z := 2148222890.
Lemma rx_sh_eq :
  RX_SH64 = SHADOW_OFF + (TICK_S + 64) / 8 /\ RX_SH64 + 1 = SHADOW_OFF + (TICK_S + 72) / 8 /\
  RX_SH242 = SHADOW_OFF + (TICK_S + 242) / 8 /\ RX_SH242 = SHADOW_OFF + (TICK_S + 243) / 8 /\
  RX_SH1736 = SHADOW_OFF + (TICK_S + 1736) / 8 /\ RX_SH1736 + 1 = SHADOW_OFF + (TICK_S + 1748) / 8 /\
  RX_SH1736 + 2 = SHADOW_OFF + (TICK_S + 1752) / 8 /\
  RX_SH18232 = SHADOW_OFF + (TICK_S + 18232) / 8 /\ RX_SH18192 = SHADOW_OFF + (TICK_S + 18192) / 8.
Proof. repeat split; reflexivity. Qed.

(* ---- run 1: from the retx cut to `jalr a4` ---- *)

(* The valuation of run 1: the registers at the cut, then now (atom 32), g_s.io.ctx (33), g_s.io.send (34), the
   inflight length (35) and stats.tx_retransmits (36) of the world Bw. *)
Definition rx_vals1 (Bw : list byte) (now : Z) : list word :=
  [Z_to_bv 64 now; Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 64) 8); Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 72) 8);
   Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 1736) 8); Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18232) 8)].

(* now at s1 + 56; g_s.io.ctx and g_s.io.send; the two retry bytes; the inflight length, retries and sent_us;
   stats.tx_retransmits; the shadow bytes of the checks (each 0). *)
Definition RX_R_now : YP09.region :=
  YP09.mkRegion (Some 9%nat) 56 64 0 0 [YP09.mkChunk 56 (YP09.CVal 8 (SOff 32 0))].
Definition RX_R_io : YP09.region :=
  YP09.mkRegion None (TICK_S + 64) (TICK_S + 80) 0 0
    [YP09.mkChunk (TICK_S + 64) (YP09.CVal 8 (SOff 33 0)); YP09.mkChunk (TICK_S + 72) (YP09.CVal 8 (SOff 34 0))].
Definition RX_R_fb : YP09.region := YP09.mkRegion None (TICK_S + 242) (TICK_S + 244) (TICK_S + 242) (TICK_S + 244) [].
Definition RX_R_ifl : YP09.region :=
  YP09.mkRegion None (TICK_S + 1736) (TICK_S + 1760) (TICK_S + 1748) (TICK_S + 1760)
    [YP09.mkChunk (TICK_S + 1736) (YP09.CVal 8 (SOff 35 0))].
Definition RX_R_txr : YP09.region :=
  YP09.mkRegion None (TICK_S + 18232) (TICK_S + 18240) (TICK_S + 18232) (TICK_S + 18240)
    [YP09.mkChunk (TICK_S + 18232) (YP09.CVal 8 (SOff 36 0))].
Definition RX_R_sh64 : YP09.region :=
  YP09.mkRegion None RX_SH64 (RX_SH64 + 2) 0 0
    [YP09.mkChunk RX_SH64 (YP09.CVal 1 (SLit 0)); YP09.mkChunk (RX_SH64 + 1) (YP09.CVal 1 (SLit 0))].
Definition RX_R_sh242 : YP09.region :=
  YP09.mkRegion None RX_SH242 (RX_SH242 + 1) 0 0 [YP09.mkChunk RX_SH242 (YP09.CVal 1 (SLit 0))].
Definition RX_R_sh1736 : YP09.region :=
  YP09.mkRegion None RX_SH1736 (RX_SH1736 + 3) 0 0
    [YP09.mkChunk RX_SH1736 (YP09.CVal 1 (SLit 0)); YP09.mkChunk (RX_SH1736 + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (RX_SH1736 + 2) (YP09.CVal 1 (SLit 0))].
Definition RX_R_sh18232 : YP09.region :=
  YP09.mkRegion None RX_SH18232 (RX_SH18232 + 1) 0 0 [YP09.mkChunk RX_SH18232 (YP09.CVal 1 (SLit 0))].
Definition RX_REGS1 : smem :=
  [RX_R_now; RX_R_io; RX_R_fb; RX_R_ifl; RX_R_txr; RX_R_sh64; RX_R_sh242; RX_R_sh1736; RX_R_sh18232].
(* s1 (atom 9) is the realigned stack pointer: 32-aligned, in [2 ^ 46, 2 ^ 47]. *)
Definition RX_FACTS : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
(* a3, a4: the shadow addresses step computed; a7 = s + 18144; s4 = s; s8 = the shadow base. *)
Definition RX_SR1 : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    (Z_to_bv 5 13) (SLit (SHADOW_OFF + (TICK_S + 1752) / 8)))
    (Z_to_bv 5 14) (SLit (SHADOW_OFF + (TICK_S + 1748) / 8)))
    (Z_to_bv 5 17) (SLit (TICK_S + 18144)))
    (Z_to_bv 5 20) (SLit TICK_S))
    (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_rx1 : sstate := mkSS TICK_RETX RX_SR1 RX_REGS1 None RX_FACTS.
Definition RX_Bx : sv := SLit 0.
Definition RX_B0 : Z * Z := (0, 0).

(* ---- run 2: from io_send's return ---- *)
Definition RX_R_t01 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 40 56 0 0
    [YP09.mkChunk 40 (YP09.CVal 8 (SLit (SHADOW_OFF + (TICK_S + 212) / 8)));
     YP09.mkChunk 48 (YP09.CVal 8 (SLit (TICK_S + 212)))].
Definition RX_R_txf : YP09.region :=
  YP09.mkRegion None (TICK_S + 18192) (TICK_S + 18200) (TICK_S + 18192) (TICK_S + 18200)
    [YP09.mkChunk (TICK_S + 18192) (YP09.CVal 8 (SOff 32 0))].
Definition RX_R_sh18192 : YP09.region :=
  YP09.mkRegion None RX_SH18192 (RX_SH18192 + 1) 0 0 [YP09.mkChunk RX_SH18192 (YP09.CVal 1 (SLit 0))].
(* a0 = io_send's result, s9 = s + 18144 (saved at +0x410), s8 = the shadow base. *)
Definition RX_SR2 (z : Z) : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 10) (SLit z)) (Z_to_bv 5 25) (SLit (TICK_S + 18144)))
    (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_rx2z : sstate := mkSS RX_RET (RX_SR2 0) [RX_R_t01; RX_R_txf; RX_R_sh18192] None RX_FACTS.
Definition ss_rx2n : sstate := mkSS RX_RET (RX_SR2 (- 5)) [RX_R_t01] None RX_FACTS.

(* ---- bytes, values and the world ---- *)

(* A byte of the shadow read as 0 is a stored 0. *)
Lemma rx_vm0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview tfibsegs H m a = Some 0 -> val_mem tfibsegs (mrestrict H m) a 1 0.
Proof.
  intros H m a Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Hv].
  cbn in Hv. injection Hv as Hb. change (YO0f.le_byte 0 1 0) with 0.
  f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* Byte j of a stored value, as the view reads it. *)
Lemma rx_vm_view : forall (H : word -> bool) (m : word -> option byte) a (n : nat) v j,
  val_mem tfibsegs (mrestrict H m) a n v -> (j < n)%nat ->
  aview tfibsegs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
  intros H m a n v j Hv Hj. unfold aview. rewrite (Hv j Hj). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256.
  unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* le_byte reads its value modulo 2 ^ (8 n). *)
Lemma rx_le_byte_cong : forall v w (n : nat) j, v mod 2 ^ (8 * Z.of_nat n) = w mod 2 ^ (8 * Z.of_nat n) ->
  YO0f.le_byte v n j = YO0f.le_byte w n j.
Proof. intros v w n j H. unfold YO0f.le_byte. rewrite H. reflexivity. Qed.

Lemma rx_mod_sub : forall x w, 0 <= w <= 64 -> (x mod 2 ^ 64) mod 2 ^ w = x mod 2 ^ w.
Proof.
  intros x w Hw.
  assert (Hd : (2 ^ w | 2 ^ 64)) by (exists (2 ^ (64 - w)); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  apply Z.mod_mod_divide; try exact Hd; try (apply Z.pow_nonzero; lia); try (apply Z.pow_pos_nonneg; lia).
Qed.

Lemma rx_swrap32_mod : forall x, bv_swrap 32 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

(* Lib/Mem.v shiftr_mod_mod8. *)
Lemma rx_shiftr_mod8 : forall z k w, 0 <= k -> k + 8 <= w -> Z.shiftr (z mod 2 ^ w) k mod 2 ^ 8 = Z.shiftr z k mod 2 ^ 8.
Proof.
  intros z k w Hk Hw. apply Z.bits_inj'. intros i Hi.
  rewrite <- !Z.land_ones by lia. rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  rewrite Z.land_spec.
  destruct (Z.ltb_spec0 i 8).
  - rewrite !Z.ones_spec_low by lia. rewrite !andb_true_r. reflexivity.
  - rewrite (Z.ones_spec_high 8) by lia. rewrite !andb_false_r. reflexivity.
Qed.

(* A range test that is false puts x outside the range. *)
Lemma rx_rng_false : forall a b x, ((a <=? x) && (x <? b)) = false -> ~ (a <= x < b).
Proof.
  intros a b x H [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. rewrite H1, H2 in H. discriminate H.
Qed.

(* A view built from two views: rdF where P holds, rd0 elsewhere. A run of stores is read into the world store by
   store, the stores already read taken from the final view. *)
Definition rx_mix (P : Z -> bool) (rdF rd0 : Z -> option Z) : Z -> option Z :=
  fun x => if P x then rdF x else rd0 x.

Lemma rx_tw_step : forall T rd0 rdF Bw o b n k (m : nat) v (P P' : Z -> bool),
  tw_ok T -> tw_at T (rx_mix P rdF rd0) Bw -> In (o, b, n) T -> 0 <= k -> k + Z.of_nat m <= n ->
  (forall x, P' x = P x || ((b + k <=? x) && (x <? b + k + Z.of_nat m))) ->
  (forall j, (j < m)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  tw_at T (rx_mix P' rdF rd0) (TW.upd Bw (o + k) (TW.put m v)).
Proof.
  intros T rd0 rdF Bw o b n k m v P P' Hok Hat Hin Hk Hkm HP Hv.
  apply (tw_write T (rx_mix P rdF rd0) (rx_mix P' rdF rd0) Bw o b n k m v Hok Hat Hin Hk Hkm).
  - intros j Hj. unfold rx_mix. rewrite HP.
    replace ((b + k <=? b + k + Z.of_nat j) && (b + k + Z.of_nat j <? b + k + Z.of_nat m)) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite orb_true_r. exact (Hv j Hj).
  - intros x _ Hx. unfold rx_mix. rewrite HP.
    replace ((b + k <=? x) && (x <? b + k + Z.of_nat m)) with false.
    + rewrite orb_false_r. reflexivity.
    + symmetry. apply andb_false_iff.
      destruct (Z_lt_le_dec x (b + k)); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

Lemma rx_tw_start : forall T rd0 rdF Bw, tw_at T rd0 Bw -> tw_at T (rx_mix (fun _ => false) rdF rd0) Bw.
Proof. intros T rd0 rdF Bw H. apply (tw_kept T rd0); [exact H|]. intros x _. reflexivity. Qed.

Lemma rx_tw_end : forall T rd0 rdF Bw (P : Z -> bool),
  tw_at T (rx_mix P rdF rd0) Bw -> (forall x, tw_in T x -> P x = false -> rdF x = rd0 x) -> tw_at T rdF Bw.
Proof.
  intros T rd0 rdF Bw P H HK. apply (tw_kept T (rx_mix P rdF rd0)); [exact H|]. intros x Hx. unfold rx_mix.
  destruct (P x) eqn:E; [reflexivity|]. exact (HK x Hx E).
Qed.

(* The bytes run 1 stores, store by store. *)
Definition rx_P1 (x : Z) : bool := (TICK_S + 1748 <=? x) && (x <? TICK_S + 1752).
Definition rx_P2 (x : Z) : bool := rx_P1 x || ((TICK_S + 242 <=? x) && (x <? TICK_S + 243)).
Definition rx_P3 (x : Z) : bool := rx_P2 x || ((TICK_S + 243 <=? x) && (x <? TICK_S + 244)).
Definition rx_P4 (x : Z) : bool := rx_P3 x || ((TICK_S + 1752 <=? x) && (x <? TICK_S + 1760)).
Definition rx_P5 (x : Z) : bool := rx_P4 x || ((TICK_S + 18232 <=? x) && (x <? TICK_S + 18240)).
(* The bytes run 1 may change: its three writable windows. *)
Definition rx_Z1 (x : Z) : Prop :=
  (TICK_S + 242 <= x < TICK_S + 244) \/ (TICK_S + 1748 <= x < TICK_S + 1760) \/ (TICK_S + 18232 <= x < TICK_S + 18240).
Lemma rx_P5_out : forall x, rx_P5 x = false -> ~ rx_Z1 x.
Proof.
  intros x H. unfold rx_P5, rx_P4, rx_P3, rx_P2, rx_P1 in H.
  apply orb_false_elim in H as [H H5]. apply orb_false_elim in H as [H H4]. apply orb_false_elim in H as [H H3].
  apply orb_false_elim in H as [H1 H2].
  apply rx_rng_false in H1, H2, H3, H4, H5. unfold rx_Z1. lia.
Qed.

(* io_send's written range for a frame of at most 1514 bytes lies in the one tick_wr names. *)
Lemma rx_iosend_wr : forall n a, n <= TC.SPEC_MAX_FRAME -> iosend_wr n a -> iosend_wr TC.SPEC_MAX_FRAME a.
Proof.
  intros n a Hn H. unfold iosend_wr in *.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]];
    [ left; exact H | do 1 right; left; exact H | do 2 right; left; exact H | do 3 right; left; exact H
    | do 4 right; left; exact H | do 5 right; left; exact H | do 6 right; left; exact H | do 7 right; left; exact H
    | do 8 right; left; exact H | do 9 right; left; exact H | do 10 right; left; exact H
    | do 11 right; left; exact H | do 12 right; left; exact H | do 13 right; left; exact H
    | do 14 right; left; exact H | do 15 right; left | do 16 right; left; exact H | do 17 right; left; exact H
    | do 18 right; exact H ].
  unfold twb_fld in *. change TC.SPEC_MAX_FRAME with 1514 in *. lia.
Qed.

(* ---- the model ---- *)

(* The world after retransmit's four stores (TSess.v retransmit_m, :405-410). *)
Definition rx_w (Bw : list byte) (now : Z) : list byte :=
  let B := TW.set_S_inflight_retries Bw (DSpec.u32 (TW.S_inflight_retries Bw + 1)) in
  let retry := DSpec.u16 (TW.S_inflight_retries B) in
  let B := TW.upd B (TW.A_S_inflight_frame + TS0.DIGINET_ETH_HDR_LEN + 12) (TW.put 1 (DSpec.u8 (Z.shiftr retry 8))) in
  let B := TW.upd B (TW.A_S_inflight_frame + TS0.DIGINET_ETH_HDR_LEN + 13) (TW.put 1 (DSpec.u8 retry)) in
  let B := TW.set_S_inflight_sent_us B now in
  TW.set_S_stats_tx_retransmits B (TS0.u64 (TW.S_stats_tx_retransmits B + 1)).

Lemma rx_ret : forall I F Bw now, TSS.retransmit_m I F Bw now =
  match TSS.inflight_bytes (rx_w Bw now) with None => None | Some fr => TSS.send_raw_m I F (rx_w Bw now) fr end.
Proof. reflexivity. Qed.

(* On the retx path: the inflight length fits the array, g_s.io.send is io_send, io_send answers (B1, r0), and r0 is
   0 (the tail at tx_frames + 1) or -EIO (returned). *)
Lemma rx_model : forall TF Bw now Bw' r,
  tick_retx_m timg_B TF Bw now = Some (Bw', r) ->
  TW.S_inflight_len (rx_w Bw now) <= 1514 /\
  TW.S_io_send (rx_w Bw now) = TI.ti_io_send timg_B /\
  exists B1 r0,
    TC.io_send_m timg_B (rx_w Bw now)
      (TW.sub (rx_w Bw now) TW.A_S_inflight_frame (Z.to_nat (TW.S_inflight_len (rx_w Bw now)))) = Some (B1, r0) /\
    ((r0 = 0 /\
      tick_tail timg_B TF (TW.set_S_stats_tx_frames B1 (TS0.u64 (TW.S_stats_tx_frames B1 + 1))) now = Some (Bw', r)) \/
     (r0 = - 5 /\ B1 = Bw' /\ - 5 = r)).
Proof.
  intros TF Bw now Bw' r H. unfold tick_retx_m in H. rewrite rx_ret in H.
  unfold TSS.inflight_bytes in H.
  destruct (1514 <? TW.S_inflight_len (rx_w Bw now)) eqn:Hl; [discriminate H|]. apply Z.ltb_ge in Hl.
  unfold TSS.send_raw_m, TSS.call_send in H.
  destruct (TW.S_io_send (rx_w Bw now) =? TI.ti_io_send timg_B) eqn:Hs; [|discriminate H]. apply Z.eqb_eq in Hs.
  destruct (TC.io_send_m timg_B (rx_w Bw now)
    (TW.sub (rx_w Bw now) TW.A_S_inflight_frame (Z.to_nat (TW.S_inflight_len (rx_w Bw now))))) as [[B1 r0]|] eqn:HIO;
    [|discriminate H].
  split; [exact Hl|]. split; [exact Hs|]. exists B1, r0. split; [reflexivity|].
  destruct (TIF.io_send_m_ret _ _ _ _ _ HIO) as [E0 | E5].
  - left. subst r0. split; [reflexivity|]. exact H.
  - right. assert (E5' : r0 = - 5) by (rewrite E5; reflexivity). subst r0. split; [reflexivity|].
    exact (tick_some_inv _ _ _ _ H).
Qed.

(* Lengths and reads across stores into a whole world. *)
Lemma rx_len_put : forall (bs : list byte) k n v, length bs = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat n <= TW.W_LEN -> length (TW.upd bs k (TW.put n v)) = Z.to_nat TW.W_LEN.
Proof.
  intros bs k n v L Hk Hn. rewrite TWL.length_upd_put; [exact L | exact Hk |]. rewrite L. unfold TW.W_LEN in *. lia.
Qed.

Lemma rx_rd_put : forall (bs : list byte) k m x k' n, length bs = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat m <= TW.W_LEN -> 0 <= k' -> (k' + Z.of_nat n <= k \/ k + Z.of_nat m <= k') ->
  TW.u_at (TW.upd bs k (TW.put m x)) k' n = TW.u_at bs k' n.
Proof.
  intros bs k m x k' n L Hk Hm Hk' Hd. apply TWL.u_at_upd_out; rewrite ?TWL.length_put; try lia;
    rewrite L; unfold TW.W_LEN in *; lia.
Qed.

Ltac rx_off := unfold TW.A_S_inflight_retries, TW.A_S_inflight_sent_us, TW.A_S_stats_tx_retransmits,
  TW.A_S_inflight_frame, TW.A_S_stats_tx_frames, TS0.DIGINET_ETH_HDR_LEN, TW.OFF_g_s, TW.W_LEN in *;
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia.
Ltac rx_len L := repeat (apply rx_len_put; [| rx_off | rx_off]); exact L.

Lemma rx_w_len : forall Bw now, length Bw = Z.to_nat TW.W_LEN -> length (rx_w Bw now) = Z.to_nat TW.W_LEN.
Proof.
  intros Bw now L. unfold rx_w, TW.set_S_inflight_retries, TW.set_S_inflight_sent_us, TW.set_S_stats_tx_retransmits.
  cbv zeta. rx_len L.
Qed.

(* A read of the world after retransmit's stores that misses the three stored spans is a read of Bw. *)
Lemma rx_w_rd : forall Bw now k' n, length Bw = Z.to_nat TW.W_LEN -> 0 <= k' ->
  (k' + Z.of_nat n <= TW.OFF_g_s + 242 \/ TW.OFF_g_s + 244 <= k') ->
  (k' + Z.of_nat n <= TW.OFF_g_s + 1748 \/ TW.OFF_g_s + 1760 <= k') ->
  (k' + Z.of_nat n <= TW.OFF_g_s + 18232 \/ TW.OFF_g_s + 18240 <= k') ->
  TW.u_at (rx_w Bw now) k' n = TW.u_at Bw k' n.
Proof.
  intros Bw now k' n L Hk' D1 D2 D3.
  unfold rx_w, TW.set_S_inflight_retries, TW.set_S_inflight_sent_us, TW.set_S_stats_tx_retransmits. cbv zeta.
  rewrite rx_rd_put; [| rx_len L | rx_off | rx_off | exact Hk' | rx_off].
  rewrite rx_rd_put; [| rx_len L | rx_off | rx_off | exact Hk' | rx_off].
  rewrite rx_rd_put; [| rx_len L | rx_off | rx_off | exact Hk' | rx_off].
  rewrite rx_rd_put; [| rx_len L | rx_off | rx_off | exact Hk' | rx_off].
  rewrite rx_rd_put; [reflexivity | exact L | rx_off | rx_off | exact Hk' | rx_off].
Qed.

Lemma rx_w_s32 : forall Bw now k', length Bw = Z.to_nat TW.W_LEN -> 0 <= k' ->
  (k' + 4 <= TW.OFF_g_s + 242 \/ TW.OFF_g_s + 244 <= k') ->
  (k' + 4 <= TW.OFF_g_s + 1748 \/ TW.OFF_g_s + 1760 <= k') ->
  (k' + 4 <= TW.OFF_g_s + 18232 \/ TW.OFF_g_s + 18240 <= k') ->
  TW.s32_at (rx_w Bw now) k' = TW.s32_at Bw k'.
Proof.
  intros Bw now k' L Hk' D1 D2 D3. unfold TW.s32_at.
  rewrite rx_w_rd; [reflexivity | exact L | exact Hk' | | |]; cbn [Z.of_nat Pos.of_succ_nat]; lia.
Qed.

(* The run invariants io_send asks, at the world it is handed: retransmit's stores miss M, g_ncmd and g_cmd. *)
Lemma rx_w_inv : forall Bw now, length Bw = Z.to_nat TW.W_LEN -> tick_runinv Bw ->
  (TW.M_fly_on (rx_w Bw now) <> 0 -> TW.M_fly_len (rx_w Bw now) <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd (rx_w Bw now) -> TW.Cmd_st (rx_w Bw now) s = TC.PENDING ->
     TW.Cmd_len (rx_w Bw now) s <= DSpec.SPEC_CMD_MAX).
Proof.
  intros Bw now L (I1 & _ & I4 & _ & _).
  assert (EO : TW.OFF_g_s = 1648) by reflexivity.
  split.
  - unfold TW.M_fly_on, TW.M_fly_len.
    rewrite rx_w_s32 by (try exact L; unfold TW.A_M_fly_on, TW.OFF_M; rewrite ?EO; lia).
    rewrite rx_w_rd by (try exact L; unfold TW.A_M_fly_len, TW.OFF_M; rewrite ?EO; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    exact I1.
  - intros s Hs Hst. unfold TW.g_ncmd, TW.Cmd_st, TW.Cmd_len in *.
    rewrite rx_w_rd in Hs by (try exact L; unfold TW.OFF_g_ncmd; rewrite ?EO; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    rewrite rx_w_s32 in Hst by (try exact L; unfold TW.A_Cmd_st, TW.OFF_g_cmd; rewrite ?EO; lia).
    rewrite rx_w_rd by (try exact L; unfold TW.A_Cmd_len, TW.OFF_g_cmd; rewrite ?EO; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    exact (I4 s Hs Hst).
Qed.

(* retries + 1 as the 32-bit field stores it. *)
Definition rx_q (Bw : list byte) : Z := DSpec.u32 (TW.S_inflight_retries Bw + 1).

(* The world after retransmit's stores as five stores at g_s's numeral offsets, in the code's order. *)
Lemma rx_w_eq : forall Bw now, length Bw = Z.to_nat TW.W_LEN ->
  rx_w Bw now =
  TW.upd (TW.upd (TW.upd (TW.upd (TW.upd Bw (TW.OFF_g_s + 1748) (TW.put 4 (rx_q Bw)))
     (TW.OFF_g_s + 242) (TW.put 1 (DSpec.u8 (Z.shiftr (DSpec.u16 (rx_q Bw)) 8))))
     (TW.OFF_g_s + 243) (TW.put 1 (DSpec.u8 (DSpec.u16 (rx_q Bw)))))
     (TW.OFF_g_s + 1752) (TW.put 8 now))
     (TW.OFF_g_s + 18232) (TW.put 8 (TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18232) 8 + 1))).
Proof.
  intros Bw now L.
  unfold rx_w, TW.set_S_inflight_retries, TW.set_S_inflight_sent_us, TW.set_S_stats_tx_retransmits,
    TW.S_stats_tx_retransmits. cbv zeta.
  assert (ER : TW.S_inflight_retries (TW.upd Bw TW.A_S_inflight_retries
    (TW.put 4 (DSpec.u32 (TW.S_inflight_retries Bw + 1)))) = rx_q Bw).
  { unfold TW.S_inflight_retries at 1. rewrite TWL.u_at_upd_put by (rewrite ?L; rx_off).
    unfold rx_q, DSpec.u32. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). apply Zmod_mod. }
  rewrite ER.
  rewrite rx_rd_put; [| rx_len L | rx_off | rx_off | rx_off | rx_off].
  rewrite rx_rd_put; [| rx_len L | rx_off | rx_off | rx_off | rx_off].
  rewrite rx_rd_put; [| rx_len L | rx_off | rx_off | rx_off | rx_off].
  rewrite rx_rd_put; [reflexivity | exact L | rx_off | rx_off | rx_off | rx_off].
Qed.

(* The 64-bit register a4 = t2 + 1, t2 the sign-extended retries: its low 32 bits are rx_q. *)
Lemma rx_t2_lo : forall x, ((bv_swrap 32 x mod 2 ^ 64 + 1) mod 2 ^ 64) mod 2 ^ 32 = DSpec.u32 (x + 1).
Proof.
  intros x. unfold DSpec.u32. rewrite rx_mod_sub by lia.
  rewrite Zplus_mod. rewrite rx_mod_sub by lia. rewrite rx_swrap32_mod. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma rx_mod8_32 : forall y, (y mod 2 ^ 32) mod 2 ^ 8 = y mod 2 ^ 8.
Proof.
  intros y. assert (Hd : (2 ^ 8 | 2 ^ 32)) by (exists (2 ^ 24); reflexivity).
  apply Z.mod_mod_divide; try exact Hd; try (apply Z.pow_nonzero; lia); try (apply Z.pow_pos_nonneg; lia).
Qed.

Lemma rx_mod8_16 : forall y, (y mod 65536) mod 2 ^ 8 = y mod 2 ^ 8.
Proof.
  intros y. assert (Hd : (2 ^ 8 | 65536)) by (exists 256; reflexivity).
  apply Z.mod_mod_divide; try exact Hd; try (apply Z.pow_nonzero; lia); try (apply Z.pow_pos_nonneg; lia); lia.
Qed.

(* The low byte the code stores at s + 243 (`sb a4`), and the high byte at s + 242 (`srliw a5, a4, 8; sb a5`). *)
Lemma rx_lo_byte : forall X q, X mod 2 ^ 32 = q -> X mod 2 ^ 8 = DSpec.u8 (DSpec.u16 q) mod 2 ^ 8.
Proof.
  intros X q H. unfold DSpec.u8, DSpec.u16. change 256 with (2 ^ 8). rewrite Zmod_mod, rx_mod8_16, <- H, rx_mod8_32.
  reflexivity.
Qed.

Lemma rx_hi_byte : forall X q, 0 <= X < 2 ^ 64 -> X mod 2 ^ 32 = q ->
  YO0a.srlw X 8 mod 2 ^ 8 = DSpec.u8 (Z.shiftr (DSpec.u16 q) 8) mod 2 ^ 8.
Proof.
  intros X q HX H. unfold YO0a.srlw, YO0a.sx32, YO0a.lo32, DSpec.u8, DSpec.u16. rewrite H.
  change (8 mod 32) with 8. change 256 with (2 ^ 8). change 65536 with (2 ^ 16).
  assert (Hq : 0 <= q < 2 ^ 32) by (rewrite <- H; apply Z.mod_pos_bound; lia).
  assert (Hs : 0 <= Z.shiftr q 8 < 2 ^ 24).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia. }
  rewrite (Z.mod_small (Z.shiftr q 8) (2 ^ 32)) by lia.
  replace (Z.shiftr q 8 <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite Zmod_mod. rewrite (rx_shiftr_mod8 q 8 16) by lia. reflexivity.
Qed.

(* ---- tactics of the walk ---- *)

(* The write rights of a run whose writable regions are bytes of g_s. *)
Ltac rx_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (first
    [ apply awr_ok_x_nil
    | apply awr_ok_x_cons_g;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
        first [ exfalso; clear - Ha; lia | apply slh_inGB; unfold TICK_S, TB_g_s, TW.SZ_g_s; clear - Ha; lia ] | ] ]).

(* A register the run kept as its atom holds the entry value R. *)
Ltac rx_atom EE n R :=
  cbn [sv_denot]; rewrite (EE n (Z_to_bv 5 (Z.of_nat n)) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R.
