(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 902 of its 1078 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SlostHead.v, with its module paths, module names and numbers changed; 768 of its 857 lines of code are new or changed and 989 lines of the source are left out. *)
(* m_set_cgW: Theorem transport_m_set_cg_holds : the statement transport_m_set_cg_holds_stmt of
   lib/B/Prog/m_set_cg.v, the machine walk of m_set (fuzz/fuzz_transport.c:196-207) on fuzz_transport.asan-ubsan at
   0x85224 = transportb_sigma TB_m_set (252 bytes, frame 16).

   The walk is a G-form walk, as the image-A walk of m_lost (lib/A/Prog/m_lost_cgW.v; image A inlines m_set's code
   there): it holds the caller's journal ajournal_gx G_HARNESS_B 0 [] (lib/A/W_journalG.v) from the entry to the
   return, and the runs are the symbolic runs of lib/A/Prog/PaShadow.v taken over that journal at image B's listing
   (lib/B/Prog/TransportGRunB.v paj_run_x); every store into M or OW is a byte of G, allowed by the run's write right
   awr_ok_x.
   The symbolic state (ms_regions): the 16-byte frame below sp, the shadow base's GOT word and cell (objects 1 and
   95), M.state and OW.n. The code loads M.state by `lw` at the listing's object 58 (M + 12) and stores it by
   `sw a0, -0x440(a4)`, a4 the auipc value hi 153 = M + 12 + 0x440; the facts hold that alias (ms_alias), so the load
   and the store reach the one region of M.state (atom 33, the world's 4 bytes as an unsigned int). OW.n is object
   12 (OW) at offset 0 (atom 34).
     run 1  (+0x00 .. +0x10)  the frame, ra saved, a7 = M.state; it stops at `beq a7, a0`.
     M.state = st:   run 2a (+0x10 .. +0xb8) the epilogue and `ret`; no byte of G is written.
     M.state <> st:  run 2b (+0x10 .. +0x24) a5 = &OW, a6 = OW.n, a2 = 15; it stops at `blt a2, a6`.
       15 < OW.n:   run 3a (+0x24 .. +0xa4) a1 = OW.n + 1 (addiw); it stops at `blt a1, a6`, the branch to the trap
                    word 0x852e0 (UBSan's signed-overflow check of OW.n++). The model premise gives OW.n <> INT_MAX
                    (int_inc is None there), so a1 = OW.n + 1 (DA1) and the branch is not taken. Run 4a
                    (+0xa4 .. +0xb8) stores OW.n + 1 and M.state = st, the epilogue, `ret`.
       OW.n <= 15:  the model premise gives 0 <= OW.n (m_set_m is None below 0), so OW.n is one of 0 .. 15. In each
                    case a6 is pinned to that literal i and the 12 bytes of OW.t[i] join the state as a writable region
                    of G (ms_tr_region). Run 3b (+0x24 .. +0x44): the index check `bgeu a6, 16` to the trap word is
                    decided by the literal; it stops at `bltu a3, a2`, UBSan's pointer-overflow check of &OW.t[i]
                    (a3 = ~(OW + 4), a2 = 12 * i), whose branch to the trap word is refuted by computing a3 (DX).
                    Run 4b (+0x44 .. +0xb8): p = OW + 4 + 12 * i; the token engine decides the three instrumented
                    checks of the stores at p, p + 4 and p + 8 against the shadow entry of OW's 304 bytes (MS_SH,
                    shadow 0 by trans_ow_cells: ms_shok), so no call of __asan_report_store4 (0x852f4, 0x85308,
                    0x8531c) is reached; the stores of st, the old M.state and why; a1 = i + 1 and its overflow check
                    (decided); OW.n = i + 1, M.state = st, `ret`.
   The post (ms_close): transport_cg_post over G_HARNESS_B, acall_kept_g by TransportGCg.v dk_kept_step_g over the
   stack window and mset_st_wr Bw st. The world relation at Bw' (ms_model): when M.state = st Bw' = Bw (TWorldG.v
   tw_kept); otherwise one TWorldG.v tw_write per field m_set_m sets (ms_world2 / ms_world3), each read from the chunks
   of the last state; every other payload byte is kept. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.

(* ------------------------------------------------------------------ *)
(* Bytes, branches and the model                                       *)
(* ------------------------------------------------------------------ *)

(* Byte j < 4 of a 64-bit word holding v is byte j of the 4-byte little-endian v (signed or not). *)
Lemma ms_bow : forall v j, (j < 4)%nat ->
  bv_unsigned (byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v 4 j.
Proof.
intros v j Hj. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64). change (8 * Z.of_nat 4) with 32.
change 256 with (2 ^ 8).
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* beq / blt / bltu on the sign-extended values. *)
Lemma ms_eqb : forall x y, -2^31 <= x < 2^31 -> -2^31 <= y < 2^31 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. apply bv_eqb_small; lia. Qed.
Lemma ms_lts : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2^63); lia). reflexivity.
Qed.

(* The 4-byte signed load of an atom holding the unsigned int u. *)
Lemma ms_sext_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (LMem.signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma ms_add_den : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma ms_some_inv : forall x y : list byte, Some (x, tt) = Some (y, tt) -> y = x.
Proof. intros x y H. injection H as H. symmetry. exact H. Qed.

(* The model's world after the call, by m_set's three outcomes (TCb.v m_set_m). *)
Lemma ms_model : forall Bw st why Bw',
  TCB.m_set_m Bw st why = Some (Bw', tt) ->
  (TW.M_state Bw = st /\ Bw' = Bw) \/
  (TW.M_state Bw <> st /\ TCB.TRANS_MAX <= TW.OW_n Bw /\ TW.OW_n Bw <> TCB.INT_MAX /\
     Bw' = TW.set_M_state (TW.set_OW_n Bw (TW.OW_n Bw + 1)) st) \/
  (TW.M_state Bw <> st /\ 0 <= TW.OW_n Bw < TCB.TRANS_MAX /\
     Bw' = TW.set_M_state (TW.set_OW_n (TW.set_OW_t_reason (TW.set_OW_t_old
       (TW.set_OW_t_state Bw (TW.OW_n Bw) st) (TW.OW_n Bw) (TW.M_state Bw)) (TW.OW_n Bw) why)
       (TW.OW_n Bw + 1)) st).
Proof.
intros Bw st why Bw' Hm.
unfold TCB.m_set_m, TCB.int_inc in Hm. cbv zeta in Hm. revert Hm.
destruct (Z.eqb_spec (TW.M_state Bw) st) as [Es|Es]; intros Hm; cbv beta iota in Hm.
- left. split; [exact Es|]. exact (ms_some_inv _ _ Hm).
- right. revert Hm.
  destruct (Z.ltb_spec (TW.OW_n Bw) TCB.TRANS_MAX) as [Lt|Ge];
  [destruct (Z.ltb_spec (TW.OW_n Bw) 0) as [L0|G0] |];
  destruct (Z.eqb_spec (TW.OW_n Bw) TCB.INT_MAX) as [EI|NI]; intros Hm; cbv beta iota in Hm;
  try discriminate Hm.
  + right. split; [exact Es|]. split; [lia|]. exact (ms_some_inv _ _ Hm).
  + left. split; [exact Es|]. split; [lia|]. split; [exact NI|]. exact (ms_some_inv _ _ Hm).
Qed.

(* ------------------------------------------------------------------ *)
(* The world relation at the model's world                             *)
(* ------------------------------------------------------------------ *)

(* A view that is rdF on the bytes P marks and rd0 elsewhere: the written bytes so far, the entry's on the others. *)
Definition ms_in (lo n x : Z) : bool := (lo <=? x) && (x <? lo + n).
Definition ms_mix (P : Z -> bool) (rdF rd0 : Z -> option Z) : Z -> option Z :=
  fun x => if P x then rdF x else rd0 x.

Lemma ms_in_true : forall lo n x, lo <= x < lo + n -> ms_in lo n x = true.
Proof. intros lo n x H. unfold ms_in. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma ms_in_false' : forall lo n x, ~ (lo <= x < lo + n) -> ms_in lo n x = false.
Proof.
intros lo n x H. unfold ms_in. destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + n)); cbn [andb];
  first [reflexivity | exfalso; lia].
Qed.
Lemma ms_in_false : forall lo n x, ms_in lo n x = false -> ~ (lo <= x < lo + n).
Proof. intros lo n x H Hx. rewrite (ms_in_true lo n x Hx) in H. discriminate H. Qed.

Lemma ms_tw_start : forall rdF rd0 Bw, tw_at TMAP_B rd0 Bw -> tw_at TMAP_B (ms_mix (fun _ => false) rdF rd0) Bw.
Proof. intros rdF rd0 Bw H. apply (tw_kept TMAP_B rd0 _ Bw H). intros x _. reflexivity. Qed.

(* One 4-byte store of v at the world offset ko = o + k of the row (o, b, n). *)
Lemma ms_tw_step : forall rdF rd0 P Bw o b n k ko v,
  tw_at TMAP_B (ms_mix P rdF rd0) Bw -> In (o, b, n) TMAP_B -> ko = o + k -> 0 <= k -> k + 4 <= n ->
  (forall j, (j < 4)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  tw_at TMAP_B (ms_mix (fun x => P x || ms_in (b + k) 4 x) rdF rd0) (TW.upd Bw ko (TW.put 4 v)).
Proof.
intros rdF rd0 P Bw o b n k ko v H Hin Hko Hk Hkn HV. subst ko.
apply (tw_write TMAP_B (ms_mix P rdF rd0) (ms_mix (fun x => P x || ms_in (b + k) 4 x) rdF rd0) Bw o b n k 4 v
  TMAP_B_ok H Hin Hk ltac:(change (Z.of_nat 4) with 4; lia)).
- intros j Hj. unfold ms_mix. cbv beta.
  rewrite (ms_in_true (b + k) 4 (b + k + Z.of_nat j)) by lia. rewrite orb_true_r. exact (HV j Hj).
- intros x Hx Hn. unfold ms_mix. cbv beta. change (Z.of_nat 4) with 4 in Hn.
  rewrite (ms_in_false' (b + k) 4 x) by lia. rewrite orb_false_r. reflexivity.
Qed.

Lemma ms_tw_end : forall rdF rd0 P Bw, tw_at TMAP_B (ms_mix P rdF rd0) Bw ->
  (forall x, tw_in TMAP_B x -> P x = false -> rdF x = rd0 x) -> tw_at TMAP_B rdF Bw.
Proof.
intros rdF rd0 P Bw H Hk. apply (tw_kept TMAP_B (ms_mix P rdF rd0) rdF Bw H).
intros x Hx. unfold ms_mix. destruct (P x) eqn:E; [reflexivity | exact (Hk x Hx E)].
Qed.

Ltac ms_unP HP :=
  cbv beta in HP;
  repeat match type of HP with
  | orb _ _ = false =>
      let Hq := fresh "Hq" in apply orb_false_iff in HP; destruct HP as [HP Hq]; apply ms_in_false in Hq
  end.

(* M.state <> st, OW.n >= TRANS_MAX: OW.n + 1 and M.state = st. *)
Lemma ms_world2 : forall Bw rd0 rdF n st,
  tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (n + 1) 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 12 + Z.of_nat j) = Some (YO0f.le_byte st 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_OW <= x < TB_OW + 4) -> ~ (TB_M + 12 <= x < TB_M + 16) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_state (TW.set_OW_n Bw (n + 1)) st).
Proof.
intros Bw rd0 rdF n st Htw VN VS Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold TW.set_M_state, TW.set_OW_n, TW.A_M_state, TW.A_OW_n.
pose proof (ms_tw_start rdF rd0 Bw Htw) as H0.
pose proof (ms_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 0 (TW.OFF_OW + 0) (n + 1) H0 TMAP_B_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VN) as H1.
pose proof (ms_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 12 (TW.OFF_M + 12) st H1 TMAP_B_M
  ltac:(lia) ltac:(lia) ltac:(lia) VS) as H2.
apply (ms_tw_end rdF rd0 _ _ H2).
intros x Hx HP. ms_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

(* M.state <> st, 0 <= OW.n = i < TRANS_MAX: also OW.t[i] = {st, old, why}. *)
Lemma ms_world3 : forall Bw rd0 rdF i st old why,
  tw_at TMAP_B rd0 Bw -> 0 <= i < 16 ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + (4 + 12 * i) + Z.of_nat j) = Some (YO0f.le_byte st 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + (8 + 12 * i) + Z.of_nat j) = Some (YO0f.le_byte old 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + (12 + 12 * i) + Z.of_nat j) = Some (YO0f.le_byte why 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (i + 1) 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 12 + Z.of_nat j) = Some (YO0f.le_byte st 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_OW + 4 + 12 * i <= x < TB_OW + 16 + 12 * i) -> ~ (TB_OW <= x < TB_OW + 4) ->
     ~ (TB_M + 12 <= x < TB_M + 16) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.set_M_state (TW.set_OW_n (TW.set_OW_t_reason (TW.set_OW_t_old
    (TW.set_OW_t_state Bw i st) i old) i why) (i + 1)) st).
Proof.
intros Bw rd0 rdF i st old why Htw Hi VTS VTO VTR VN VS Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold TW.set_M_state, TW.set_OW_n, TW.set_OW_t_reason, TW.set_OW_t_old, TW.set_OW_t_state,
  TW.A_M_state, TW.A_OW_n, TW.A_OW_t_reason, TW.A_OW_t_old, TW.A_OW_t_state.
pose proof (ms_tw_start rdF rd0 Bw Htw) as H0.
pose proof (ms_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW (4 + 12 * i) (TW.OFF_OW + 4 + 12 * i + 0)
  st H0 TMAP_B_OW ltac:(lia) ltac:(lia) ltac:(lia) VTS) as H1.
pose proof (ms_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW (8 + 12 * i) (TW.OFF_OW + 4 + 12 * i + 4)
  old H1 TMAP_B_OW ltac:(lia) ltac:(lia) ltac:(lia) VTO) as H2.
pose proof (ms_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW (12 + 12 * i) (TW.OFF_OW + 4 + 12 * i + 8)
  why H2 TMAP_B_OW ltac:(lia) ltac:(lia) ltac:(lia) VTR) as H3.
pose proof (ms_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 0 (TW.OFF_OW + 0) (i + 1) H3 TMAP_B_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VN) as H4.
pose proof (ms_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 12 (TW.OFF_M + 12) st H4 TMAP_B_M
  ltac:(lia) ltac:(lia) ltac:(lia) VS) as H5.
apply (ms_tw_end rdF rd0 _ _ H5).
intros x Hx HP. ms_unP HP. apply Hk; [exact Hx | lia | lia | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* G                                                                   *)
(* ------------------------------------------------------------------ *)

Lemma ms_inG : forall a, (TB_M <= a < TB_M + 1648) \/ (TB_OW <= a < TB_OW + 304) -> inG G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. destruct Ha as [Ha|Ha].
- exists (TB_M, TW.SZ_M). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_M) | unfold in_zr, TW.SZ_M; cbn [fst snd]; lia].
- exists (TB_OW, TW.SZ_OW). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_OW) | unfold in_zr, TW.SZ_OW; cbn [fst snd]; lia].
Qed.

(* A payload byte of the world table is a byte of G. *)
Lemma ms_tw_in_G : forall x, tw_in TMAP_B x -> inG G_HARNESS_B x.
Proof.
intros x (o & b & n & Hin & Hx).
pose proof (TMAP_B_in_G o b n Hin) as HG.
unfold inG. apply Exists_exists. exists (b, n). split; [exact HG | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The bytes m_set writes are bytes of G. *)
Lemma ms_wr_inG : forall Bw st a, mset_st_wr Bw st a -> inG G_HARNESS_B a.
Proof.
intros Bw st a [_ H]. apply ms_inG.
unfold mset_wr, twb_fld, TW.A_M_state, TW.A_OW_n, TW.A_OW_t_state, TW.OW_t_ESZ, TCB.TRANS_MAX in H.
destruct H as [[Hn H]|[H|H]]; [right; lia | right; lia | left; lia].
Qed.

Lemma ms_in4 : forall b a, b <= a < b + 4 -> exists j, (j < 4)%nat /\ a = b + Z.of_nat j.
Proof. intros b a H. exists (Z.to_nat (a - b)). split; lia. Qed.

Lemma ms_off0 : forall (rd : Z -> option Z) b v,
  (forall j, (j < 4)%nat -> rd (b + 0 + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  forall j, (j < 4)%nat -> rd (b + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof. intros rd b v H j Hj. rewrite <- (Z.add_0_r b) at 1. exact (H j Hj). Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the entry                                     *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base, 33 the 4 bytes of M.state and 34 the 4 bytes of
   OW.n as unsigned ints. Regions: the 16-byte frame below sp, the shadow base's GOT word (object 1) and its cell
   (object 95), M.state (object 58, the listing's image object at M + 12, which the code loads by `lw` at its auipc
   and stores by `sw a0, -0x440(a4)` from the auipc value hi 153 = M + 12 + 0x440: the alias of the facts), and OW.n
   (object 12, OW). *)
Definition ms_st_region : YP09.region := YP09.mkRegion (Some (A_OBJ 58)) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition ms_n_region : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))].
Definition ms_regions : smem :=
  [stack_region MSET_FRAME; got_regionP; bcell_regionP 32; ms_st_region; ms_n_region].
Definition ms_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (A_OBJ 58, mkAF (TB_M + 12) (TB_M + 12) 2); (A_OBJ 12, mkAF TB_OW TB_OW 5)] []
          [(SOff (A_HI 153) (-1088), SOff (A_OBJ 58) 0)].
Definition ss_ms : sstate := mkSS AF_m_set sr_atoms ms_regions None ms_facts.
(* The shadow entry of OW's 304 bytes (38 whole granules), and the shadow base of the token engine. *)
Definition MS_SH : list shent := [mkSHE (A_OBJ 12) 0 304].
Definition MS_Bx : sv := SOff 32 0.
(* OW.t[i]'s 12 bytes, the region the case OW.n = i adds. *)
Definition ms_tr_region (i : Z) : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 12)) (4 + 12 * i) (16 + 12 * i) (4 + 12 * i) (16 + 12 * i) [].

(* The writable windows of the runs: the frame, M.state and OW.n; with OW.n = i also OW.t[i]. *)
Definition ms_W0 (sp a : Z) : Prop :=
  (sp - 16 <= a < sp) \/ (TB_M + 12 <= a < TB_M + 16) \/ (TB_OW <= a < TB_OW + 4).
Definition ms_W3 (sp i a : Z) : Prop := ms_W0 sp a \/ (TB_OW + 4 + 12 * i <= a < TB_OW + 16 + 12 * i).

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ms_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ms_reg: no match for" T; fail
  end.

(* The windows a run wrote, each closed by tac. *)
Ltac ms_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of a run: the frame below sp (inside the caller's stack window), the read-only image cells (no
   writable byte), and the regions of M and OW (bytes of G). *)
Ltac ms_awr UspE UME UOE :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ lia
      | rewrite UspE in Ha; left; split; [unfold awr_byte; left; lia | lia]
      | rewrite UME in Ha; right; left; apply ms_inG; lia
      | rewrite UOE in Ha; right; left; apply ms_inG; lia ] |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

Section msw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma ms_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  VAL (A_OBJ 58) = TB_M + 12 /\ VAL (A_OBJ 12) = TB_OW /\ VAL (A_HI 153) = TB_M + 12 + 1088 /\
  BASE + AF_m_set = transportb_sigma TB_m_set.
Proof. vm_compute. repeat split. Qed.

(* The alias of the facts: the auipc value hi 153 less 0x440 is object 58 (M.state). *)
Lemma ms_alias : forall E, ew E (A_HI 153) = Z_to_bv 64 (VAL (A_HI 153)) ->
  ew E (A_OBJ 58) = Z_to_bv 64 (VAL (A_OBJ 58)) ->
  sv_denot E (SOff (A_HI 153) (-1088)) = sv_denot E (SOff (A_OBJ 58) 0).
Proof.
intros E H1 H2. destruct ms_vals as (_ & _ & V58 & _ & V153 & _).
cbn [sv_denot]. rewrite H1, H2, V58, V153.
rewrite !unsigned_lit_small by (unfold TB_M; lia). apply f_equal. lia.
Qed.

(* The two image cells hold what transport_cells says they hold, at any AR state. *)
Lemma ms_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H W) mem) got_regionP /\ region_ok segs E (mrestrict (w_H W) mem) (bcell_regionP 32).
Proof.
  intros ly S W mem md E HCELLS HAR E1 E95 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct ms_vals as (V1 & V95 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (R95 : 0 <= VAL (A_OBJ 95) < 2 ^ 47) by (rewrite V95; unfold FCells.CELL_K; lia).
  unfold got_regionP, bcell_regionP, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split.
  - rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 95) 0) (VAL (A_OBJ 95)));
    [cbn [sv_denot]; rewrite E95, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r, V1, V95. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E95) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 95)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r, V95. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
Qed.

(* OW's 304 bytes are addressable at every AR state: the shadow of its 38 whole granules is 0 (trans_ow_cells). *)
Lemma ms_ra : forall ly S (W : world segs) mem md,
  trans_ow_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF TB_OW 304.
Proof.
intros ly S W mem md HZ HAR x Hx.
assert (EO : TB_OW = 0x5f2ce0) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr.
exists 0. split; [|left; reflexivity].
assert (Hz := decode_zshadow_rd B ly S W mem md TB_OW (TB_OW + TW.SZ_OW) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The run's shadow entry holds at every AR state. *)
Lemma ms_shok : forall ly S (W : world segs) mem md (E : env),
  trans_ow_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 12) = Z_to_bv 64 TB_OW -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs MS_Bx MS_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HOW HAR E12 E32.
assert (EO : TB_OW = 0x5f2ce0) by reflexivity.
unfold sh_ok, MS_SH. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H W) mem E MS_Bx (A_OBJ 12) TB_OW 304 TB_OW 0 304 (ms_ra ly S W mem md HOW HAR)).
- unfold U, MS_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The walk's valuation: the 32 registers at the entry, the shadow base, and the world's M.state and OW.n. *)
Definition ms_E (regs : bvmap 5 word) (ust un : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 ust; Z_to_bv 64 un]).

(* The entry state, and the shadow entry of OW. *)
Lemma ms_entry : forall ly S (W : world segs) regs mem md ust un,
  transport_cells B -> trans_ow_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - MSET_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  0 <= ust < 2 ^ 32 -> 0 <= un < 2 ^ 32 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TB_M + 12 + 0) 4 ust ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TB_OW + 0) 4 un ->
  st_ok_pi segs VAL (ms_E regs ust un) ss_ms
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_set)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs MS_Bx MS_SH (ms_E regs ust un) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md ust un HCELLS HOW HAR Hpres Hsp Hsp16 Hust Hun Vst Vn.
  assert (EM : TB_M = 0x5dede0) by reflexivity. assert (EO : TB_OW = 0x5f2ce0) by reflexivity.
  assert (FF : MSET_FRAME = 16) by reflexivity.
  assert (E2 : ew (ms_E regs ust un) 2 = YK11.getr regs 2) by (unfold ms_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew (ms_E regs ust un) 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (E32 : ew (ms_E regs ust un) 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold ms_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew (ms_E regs ust un) 33 = Z_to_bv 64 ust)
    by (unfold ms_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew (ms_E regs ust un) 34 = Z_to_bv 64 un)
    by (unfold ms_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (EOB : forall j, (j < 97)%nat -> ew (ms_E regs ust un) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold ms_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (EHI : ew (ms_E regs ust un) (A_HI 153) = Z_to_bv 64 (VAL (A_HI 153)))
    by (unfold ms_E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
  destruct (ms_img_ok ly S W mem md (ms_E regs ust un) HCELLS HAR (EOB 1%nat ltac:(lia)) (EOB 95%nat ltac:(lia)) E32)
    as [RG RC].
  destruct ms_vals as (V1 & V95 & V58 & V12 & _).
  assert (VB : forall n v0, ew (ms_E regs ust un) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (ms_E regs ust un) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (B58 : base_val (ms_E regs ust un) (Some (A_OBJ 58)) = TB_M + 12)
    by (apply VB; [rewrite (EOB 58%nat ltac:(lia)), V58; reflexivity | lia]).
  assert (B12 : base_val (ms_E regs ust un) (Some (A_OBJ 12)) = TB_OW)
    by (apply VB; [rewrite (EOB 12%nat ltac:(lia)), V12; reflexivity | lia]).
  assert (U58 : bv_unsigned (ew (ms_E regs ust un) (A_OBJ 58)) = TB_M + 12) by exact B58.
  assert (U12 : bv_unsigned (ew (ms_E regs ust un) (A_OBJ 12)) = TB_OW) by exact B12.
  split.
  - rewrite restrict_mkst_fx. unfold ss_ms, ms_regions.
    apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_cons; [exact RC |]]].
      * unfold stack_region, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Usp. unfold MSET_FRAME in *.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- unfold ms_st_region, region_ok.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
           rewrite B58. split; [lia|]. split; [lia|]. split.
           ++ intros o Ho. apply (gx_rw_writable segs G_HARNESS_B (TB_M + 12 + o) G_HARNESS_B_rw). apply ms_inG. lia.
           ++ constructor; [|constructor].
              apply (chunk_ok_val segs (ms_E regs ust un) _ (TB_M + 12) 0 4 (SOff 33 0) ust);
              [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Vst].
        -- unfold ms_n_region, region_ok.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
           rewrite B12. split; [lia|]. split; [lia|]. split.
           ++ intros o Ho. apply (gx_rw_writable segs G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw). apply ms_inG. lia.
           ++ constructor; [|constructor].
              apply (chunk_ok_val segs (ms_E regs ust un) _ TB_OW 0 4 (SOff 34 0) un);
              [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Vn].
    + apply pairwise_disjoint_of_extents.
      unfold stack_region, got_regionP, bcell_regionP, ms_st_region, ms_n_region, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (EOB 95%nat ltac:(lia))) by (rewrite V95; unfold FCells.CELL_K; lia).
      rewrite B58, B12.
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      rewrite V1, V95. unfold FCells.GOT_CELL_K, FCells.CELL_K, MSET_FRAME in *.
      repeat split; first [exact I | lia].
    + unfold ms_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; [exact I | split; [exact (ms_alias _ EHI (EOB 58%nat ltac:(lia))) | exact I]]].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U58, U12, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite ?EM, ?EO; reflexivity].
  - apply (ms_shok ly S W mem md (ms_E regs ust un) HOW HAR); [rewrite (EOB 12%nat ltac:(lia)), V12; reflexivity | exact E32].
Qed.

(* The walk's valuation agrees with the entry registers below atom 32. *)
Lemma ms_agree : forall regs ust un,
  env_agree 32 (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 ust; Z_to_bv 64 un]) (ms_E regs ust un).
Proof.
  intros regs ust un. split.
  - intros n Hn. unfold ms_E. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity.
  - reflexivity.
Qed.

(* OW.t[i]'s region at any memory: its 12 bytes are bytes of G, so writable. *)
Lemma ms_tr_ok : forall E (m : word -> option byte) i, bv_unsigned (ew E (A_OBJ 12)) = TB_OW -> 0 <= i < 16 ->
  region_ok segs E m (ms_tr_region i).
Proof.
intros E m i HU Hi. assert (EO : TB_OW = 0x5f2ce0) by reflexivity.
unfold ms_tr_region, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HU. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw). apply ms_inG. lia.
Qed.

(* The 4 bytes of a chunk of value v (signed or not), read through the view. *)
Lemma ms_chunk_rd : forall (E : env) (H : word -> bool) (mm : word -> option byte) (base off : Z) (e : sv) (v : Z),
  YP09.chunk_ok segs E (mrestrict H mm) base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 4)%nat -> aview segs H mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
intros E H mm base off e v HC He j Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC (Z.of_nat j) ltac:(cbn; lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview segs H mm (base + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H mm) (base + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply ms_bow. exact Hj.
Qed.

(* The post at the return, from the walk's last facts. *)
Lemma ms_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw st Bw' regsF mF mdF,
  AR_laws segs B -> ameter_laws MT -> gx_ok segs B G_HARNESS_B ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MSET_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - MSET_STK -> spZ regs <= 2 ^ 47 ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mF mdF k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MSET_STK <= a < spZ regs) -> ~ mset_st_wr Bw st a ->
     aview segs (w_H W) mF a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mF a) ->
  tw_at TMAP_B (aview segs (w_H W) mF) Bw' ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 ->
  forall mat, @transport_mset_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw st Bw' W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw st Bw' regsF mF mdF
    LAWS MTL HGX HAR Hwin Hce Hsp47 Hra HJF KA GA HW HP RF1 mat.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : MSET_STK = 16) by reflexivity.
  assert (GLOW : forall a, inG G_HARNESS_B a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
  unfold transport_mset_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
  split.
  { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [unfold MSET_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transportb_segs_low G_HARNESS_B lyc Sc W memc mdc memc mF
      (spZ regs - MSET_STK) (spZ regs) (mset_st_wr Bw st)
      (fun a => (spZ regs - MSET_STK <= a < spZ regs) \/ mset_st_wr Bw st a) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - intros a Ha Hn. apply KA; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; exact H].
    - exact GA.
    - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso.
      pose proof (GLOW a (ms_wr_inG Bw st a Hw)) as Hl. unfold kLowMemEnd in Hl. lia.
    - intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    - intros a [Hw | Hw] Hi HnG _ _.
      + pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
      + apply HnG. exact (ms_wr_inG Bw st a Hw).
    - intros cid pos a Hin Hr [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  exact HW.
Qed.

Lemma ms_Forall_nth : forall {A : Type} (P : A -> Prop) (l : list A) (n : nat) (x : A),
  Forall P l -> nth_error l n = Some x -> P x.
Proof. intros A P l n x HF Hn. rewrite Forall_forall in HF. apply HF. exact (nth_error_In l n Hn). Qed.

(* The 4 bytes of the chunk number c of region number idx of the state of HS, base rewritten by UB. *)
Ltac ms_chunk HS idx c UB v Hden V :=
  let RG := fresh "RG" in let HC := fresh "HC" in let HC1 := fresh "HCk" in
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict ?Hh ?m) =>
    pose proof (st_ok_pi_region_nth EF _ (restrict Hh m) idx _ HS eq_refl) as RG end;
  cbn [ms_mem restrict] in RG;
  destruct RG as (_ & _ & _ & HC);
  cbn [YP09.r_base YP09.r_chunks base_val] in HC;
  rewrite UB in HC;
  pose proof (ms_Forall_nth _ _ c _ HC eq_refl) as HC1;
  pose proof (ms_chunk_rd _ _ _ _ _ _ v HC1 Hden) as V;
  clear HC HC1.

(* The walk. *)
Lemma ms_holds : @transport_m_set_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_m_set_cg_holds_stmt.
intros HCELLS HOW LAWS MTL HGX.
unfold transport_m_set_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs st why Bw Bw'
  HJ Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi Htw Hm Hst Hwhy Hev.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MSET_STK = 16) by reflexivity.
assert (FF : MSET_FRAME = 16) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (EM : TB_M = 0x5dede0) by reflexivity.
assert (EO : TB_OW = 0x5f2ce0) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - MSET_STK) by lia.
assert (Hwin : forall a, spZ regs - MSET_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (GLOW : forall a, inG G_HARNESS_B a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
(* the model *)
pose proof (ms_model Bw st why Bw' Hm) as HM. clear Hm.
(* the two ints the code loads, as the world holds them *)
pose proof (TWL.u_at_range Bw TW.A_M_state 4) as Rst. pose proof (TWL.u_at_range Bw TW.A_OW_n 4) as Rn.
change (8 * Z.of_nat 4) with 32 in Rst, Rn.
assert (Vst : YI04.val_mem segs (mrestrict (w_H W) memc) (TB_M + 12 + 0) 4 (TW.u_at Bw TW.A_M_state 4)).
{ rewrite Z.add_0_r. exact (tw_read_val segs (mrestrict (w_H W) memc) TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 12 4
    TMAP_B_ok Htw TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)). }
assert (Vn : YI04.val_mem segs (mrestrict (w_H W) memc) (TB_OW + 0) 4 (TW.u_at Bw TW.A_OW_n 4))
  by exact (tw_read_val segs (mrestrict (w_H W) memc) TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW 0 4
    TMAP_B_ok Htw TMAP_B_OW ltac:(lia) ltac:(unfold TW.SZ_OW; lia)).
(* the valuation of the walk and its atoms *)
set (E0 := ms_E regs (TW.u_at Bw TW.A_M_state 4) (TW.u_at Bw TW.A_OW_n 4)).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ms_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r Hn; unfold E0, ms_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E33 : ew E0 33 = Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4))
  by (unfold E0, ms_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (TW.u_at Bw TW.A_OW_n 4))
  by (unfold E0, ms_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
destruct ms_vals as (V1 & V95 & V58 & V12 & V153 & _).
assert (E12 : ew E0 (A_OBJ 12) = Z_to_bv 64 TB_OW).
{ unfold E0, ms_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V12. reflexivity. }
assert (U58 : bv_unsigned (ew E0 (A_OBJ 58)) = TB_M + 12).
{ unfold E0, ms_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V58.
  apply unsigned_lit_small. lia. }
assert (UO : bv_unsigned (ew E0 (A_OBJ 12)) = TB_OW).
{ rewrite E12. apply unsigned_lit_small. lia. }
assert (UG : bv_unsigned (ew E0 (A_OBJ 1)) = FCells.GOT_CELL_K).
{ unfold E0, ms_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V1.
  apply unsigned_lit_small. unfold FCells.GOT_CELL_K. lia. }
assert (UC : bv_unsigned (ew E0 (A_OBJ 95)) = FCells.CELL_K).
{ unfold E0, ms_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V95.
  apply unsigned_lit_small. unfold FCells.CELL_K. lia. }
assert (U58' : bv_unsigned (ew E0 299%nat) = TB_M + 12) by exact U58.
assert (UO' : bv_unsigned (ew E0 253%nat) = TB_OW) by exact UO.
assert (UG' : bv_unsigned (ew E0 242%nat) = FCells.GOT_CELL_K) by exact UG.
assert (UC' : bv_unsigned (ew E0 336%nat) = FCells.CELL_K) by exact UC.
assert (E12' : ew E0 253%nat = Z_to_bv 64 TB_OW) by exact E12.
(* the values the code loads and stores *)
assert (Dst : sv_denot E0 (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (TW.M_state Bw))
  by exact (ms_sext_den E0 33 _ E33 Rst).
assert (Dn : sv_denot E0 (SExt true 32 (SOff 34 0)) = Z_to_bv 64 (TW.OW_n Bw))
  by exact (ms_sext_den E0 34 _ E34 Rn).
assert (D10 : sv_denot E0 (SOff 10 0) = Z_to_bv 64 st).
{ cbn [sv_denot]. rewrite (EE 10%nat 10%bv eq_refl), H10, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (D11 : sv_denot E0 (SOff 11 0) = Z_to_bv 64 why).
{ cbn [sv_denot]. rewrite (EE 11%nat 11%bv eq_refl), H11, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (Dst1 : sv_denot E0 (SOff 33 0) = Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4))
  by (cbn [sv_denot]; rewrite E33, Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (Dn1 : sv_denot E0 (SOff 34 0) = Z_to_bv 64 (TW.u_at Bw TW.A_OW_n 4))
  by (cbn [sv_denot]; rewrite E34, Z.add_0_r; apply Z_to_bv_bv_unsigned).
pose proof (TWL.s32_range Bw TW.A_M_state) as Sst. pose proof (TWL.s32_range Bw TW.A_OW_n) as Sn.
change (TW.s32_at Bw TW.A_M_state) with (TW.M_state Bw) in Sst.
change (TW.s32_at Bw TW.A_OW_n) with (TW.OW_n Bw) in Sn.
destruct (ms_entry lyc Sc W regs memc mdc _ _ HCELLS HOW HAR ltac:(intros a Ha; apply Hpres0; lia) Hsp Hsp16
  Rst Rn Vst Vn) as [HS SHOK].
fold E0 in HS, SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
pose proof (paj_branch (PI := PI_transportb)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_set)) memc (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x00 .. +0x10: the frame, ra saved, M.state; it stops at `beq a7, a0`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ms_awr Usp U58' UO'. }
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody md1. clear mat.
rename ms into ms1.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ ms_W0 (spZ regs) a ->
  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
{ intros a Ha H1. apply (kept_of_frame _ _ _ _ _ (ms_W0 (spZ regs)) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. ms_win Hin Hx ltac:(rewrite ?Usp, ?U58', ?UO' in Hx; unfold ms_W0; lia). }
assert (GA1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* M.state = st: m_set returns at once (fuzz_transport.c:198-199) *)
  rewrite Dst, D10 in Hc. cbn [branch_taken] in Hc. rewrite (ms_eqb _ _ Sst Hst) in Hc. apply Z.eqb_eq in Hc.
  destruct HM as [[_ HB'] | [[Es _] | [Es _]]]; [| exfalso; exact (Es Hc) | exfalso; exact (Es Hc)].
  (* run 2a, +0x10 .. +0xb8: the epilogue and `ret` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ms_awr Usp U58' UO'. }
  set (mdF := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody mdF. clear mat.
  rename ms into msF.
  assert (KAT : forall a, 0 <= a < 2 ^ 64 -> ~ ms_W0 (spZ regs) a ->
    aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a).
  { intros a Ha H1. rewrite <- (KA1 a Ha H1).
    apply (kept_of_frame _ _ _ _ _ (ms_W0 (spZ regs)) HFr); [| exact Ha | exact H1].
    intros b wlo whi x Hin Hx. ms_win Hin Hx ltac:(rewrite ?Usp, ?U58', ?UO' in Hx; unfold ms_W0; lia). }
  assert (GAF : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msF) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
  clear HF HFr HG.
  ms_chunk HS 3%nat 0%nat U58' (TW.u_at Bw TW.A_M_state 4) Dst1 VST.
  ms_chunk HS 4%nat 0%nat UO' (TW.u_at Bw TW.A_OW_n 4) Dn1 VNN.
  pose proof (ms_off0 _ _ _ VST) as VST'.
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MSET_STK <= a < spZ regs) -> ~ mset_st_wr Bw st a ->
    aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a).
  { intros a Ha H1 H2.
    assert (D : ms_W0 (spZ regs) a \/ ~ ms_W0 (spZ regs) a) by (unfold ms_W0; lia).
    destruct D as [D | D]; [|exact (KAT a Ha D)].
    unfold ms_W0 in D. destruct D as [D | [D | D]].
    - exfalso. apply H1. rewrite FS. exact D.
    - destruct (ms_in4 (TB_M + 12) a D) as (j & Hj & ->).
      pose proof (tw_read TMAP_B _ Bw TW.OFF_M TB_M TW.SZ_M 12 4 j TMAP_B_ok Htw TMAP_B_M ltac:(lia)
        ltac:(unfold TW.SZ_M; lia) Hj) as ER.
      exact (eq_trans (VST' j Hj) (eq_sym ER)).
    - destruct (ms_in4 (TB_OW + 0) a ltac:(lia)) as (j & Hj & ->).
      pose proof (tw_read TMAP_B _ Bw TW.OFF_OW TB_OW TW.SZ_OW 0 4 j TMAP_B_ok Htw TMAP_B_OW ltac:(lia)
        ltac:(unfold TW.SZ_OW; lia) Hj) as ER.
      exact (eq_trans (VNN j Hj) (eq_sym ER)). }
  assert (HWF : tw_at TMAP_B (aview segs (w_H W) (ms_mem msF)) Bw').
  { rewrite HB'. apply (tw_kept TMAP_B (aview segs (w_H W) memc) _ Bw Htw).
    intros x Hx. pose proof (GLOW x (ms_tw_in_G x Hx)) as Hl. unfold kLowMemEnd in Hl.
    apply KAF; [lia | rewrite FS; lia | intros [Hw _]; exact (Hw Hc)]. }
  ms_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs msF)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ msF regs
      [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4); Z_to_bv 64 (TW.u_at Bw TW.A_OW_n 4)] HS).
    - apply ms_agree.
    - vm_compute. reflexivity. }
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  exact (ms_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw st Bw' (ms_regs msF) (ms_mem msF) mdF
    LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAF HWF HPF RF1 mat').
- (* M.state <> st *)
  rewrite Dst, D10 in Hc. cbn [branch_taken] in Hc. rewrite (ms_eqb _ _ Sst Hst) in Hc. apply Z.eqb_neq in Hc.
  rename Hc into Hne.
  (* run 2b, +0x10 .. +0x24: &OW, OW.n, a2 = 15; it stops at `blt a2, a6` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ms_awr Usp U58' UO'. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  rename ms into ms2.
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ ms_W0 (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) memc a).
  { intros a Ha H1. rewrite <- (KA1 a Ha H1).
    apply (kept_of_frame _ _ _ _ _ (ms_W0 (spZ regs)) HFr); [| exact Ha | exact H1].
    intros b wlo whi x Hin Hx. ms_win Hin Hx ltac:(rewrite ?Usp, ?U58', ?UO' in Hx; unfold ms_W0; lia). }
  assert (GA2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
  clear HF HFr HG KA1 GA1.
  clear dependent ms1.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* 15 < OW.n: the log is full (:200) *)
    rewrite Dn in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (ms_lts 15 (TW.OW_n Bw) ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_lt in Hc.
    destruct HM as [[Es _] | [[_ (Hn1 & Hn2 & HB')] | [_ (Hn & _)]]];
      [exfalso; exact (Hne Es) | | exfalso; unfold TCB.TRANS_MAX in Hn; lia].
    assert (Hn3 : TW.OW_n Bw + 1 < 2 ^ 31) by (unfold TCB.INT_MAX in Hn2; lia).
    (* a1 = OW.n + 1 (addiw): OW.n <> INT_MAX (the model premise), so the 32-bit add does not wrap *)
    assert (DA1 : sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1)) = Z_to_bv 64 (TW.OW_n Bw + 1)).
    { change (sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1)))
        with (sext 64 (alu32 ALU_ADD (low32 (sv_denot E0 (SExt true 32 (SOff 34 0)))) (low32 (Z_to_bv 64 1)))).
      rewrite Dn, zalu32_sound. unfold zalu32, zu32, M32. rewrite Z_to_bv64_canon. apply f_equal.
      cbn [zalu_raw]. change (1 mod 2 ^ 32) with 1.
      rewrite <- (swrap32_id (TW.OW_n Bw + 1)) by lia.
      replace (TW.OW_n Bw mod 2 ^ 32 + 1) with ((TW.OW_n Bw + 1) + (- (TW.OW_n Bw / 2 ^ 32)) * bv_modulus 32)
        by (change (bv_modulus 32) with (2 ^ 32); pose proof (Z.div_mod (TW.OW_n Bw) (2 ^ 32) ltac:(lia)); lia).
      apply swrap_add_mod. }
    (* run 3a, +0x24 .. +0xa4: a1 = OW.n + 1; it stops at `blt a1, a6` (UBSan's signed-overflow check of OW.n++) *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { ms_awr Usp U58' UO'. }
    set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
    rename ms into ms3.
    assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ ms_W0 (spZ regs) a ->
      aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) memc a).
    { intros a Ha H1. rewrite <- (KA2 a Ha H1).
      apply (kept_of_frame _ _ _ _ _ (ms_W0 (spZ regs)) HFr); [| exact Ha | exact H1].
      intros b wlo whi x Hin Hx. ms_win Hin Hx ltac:(rewrite ?Usp, ?U58', ?UO' in Hx; unfold ms_W0; lia). }
    assert (GA3 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms3) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
    clear HF HFr HG KA2 GA2.
    clear dependent ms2.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* OW.n + 1 < OW.n, the trap word 0x852e0: never, OW.n + 1 does not wrap *)
      exfalso. rewrite DA1, Dn in Hc0. cbn [branch_taken] in Hc0.
      rewrite (ms_lts (TW.OW_n Bw + 1) (TW.OW_n Bw) ltac:(lia) ltac:(lia)) in Hc0. apply Z.ltb_lt in Hc0. lia.
    * (* run 4a, +0xa4 .. +0xb8: OW.n = OW.n + 1, M.state = st, the epilogue and `ret` *)
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { ms_awr Usp U58' UO'. }
      set (mdF := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdF. clear mat.
      rename ms into msF.
      assert (KAT : forall a, 0 <= a < 2 ^ 64 -> ~ ms_W0 (spZ regs) a ->
        aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a).
      { intros a Ha H1. rewrite <- (KA3 a Ha H1).
        apply (kept_of_frame _ _ _ _ _ (ms_W0 (spZ regs)) HFr); [| exact Ha | exact H1].
        intros b wlo whi x Hin Hx. ms_win Hin Hx ltac:(rewrite ?Usp, ?U58', ?UO' in Hx; unfold ms_W0; lia). }
      assert (GAF : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msF) a)
        by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA3 a Ha))).
      clear HF HFr HG.
      ms_chunk HS 3%nat 0%nat U58' st D10 VS.
      ms_chunk HS 4%nat 0%nat UO' (TW.OW_n Bw + 1) DA1 VN.
      pose proof (ms_off0 _ _ _ VS) as VS'.
      assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MSET_STK <= a < spZ regs) -> ~ mset_st_wr Bw st a ->
        aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a).
      { intros a Ha H1 H2. apply KAT; [exact Ha|]. intros HW. apply H2. split; [exact Hne|].
        unfold ms_W0 in HW. unfold mset_wr, twb_fld, TW.A_M_state, TW.A_OW_n. rewrite FS in H1.
        destruct HW as [HW|[HW|HW]]; [exfalso; lia | right; right; lia | right; left; lia]. }
      assert (HWF : tw_at TMAP_B (aview segs (w_H W) (ms_mem msF)) Bw').
      { rewrite HB'. apply (ms_world2 Bw (aview segs (w_H W) memc) _ (TW.OW_n Bw) st Htw VN VS').
        intros x Hx N1 N2. pose proof (GLOW x (ms_tw_in_G x Hx)) as Hl. unfold kLowMemEnd in Hl.
        apply KAF; [lia | rewrite FS; lia |]. intros [_ Hw].
        unfold mset_wr, twb_fld, TW.A_M_state, TW.A_OW_n, TW.A_OW_t_state, TW.OW_t_ESZ in Hw.
        unfold TCB.TRANS_MAX in *.
        destruct Hw as [[Hw _]|[Hw|Hw]]; lia. }
      ms_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
        ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      assert (HPF : aregs_preserved regs (ms_regs msF)).
      { apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ msF regs
          [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4); Z_to_bv 64 (TW.u_at Bw TW.A_OW_n 4)] HS).
        - apply ms_agree.
        - vm_compute. reflexivity. }
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'.
      exact (ms_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw st Bw' (ms_regs msF) (ms_mem msF)
        mdF LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAF HWF HPF RF1 mat').
  + (* OW.n <= 15: OW.t[OW.n] = {st, old state, why} (:200-203) *)
    rewrite Dn in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (ms_lts 15 (TW.OW_n Bw) ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_ge in Hc.
    destruct HM as [[Es _] | [[_ (Hn1 & _)] | [_ (Hn & HB')]]];
      [exfalso; exact (Hne Es) | exfalso; unfold TCB.TRANS_MAX in Hn1; lia |].
    (* a3 = ~(OW + 4), the left side of UBSan's pointer-overflow check of &OW.t[i] *)
    assert (DX : sv_denot E0 (SAlu ALU_XOR (SOff 253 4) (SLit (-1))) =
      alu64 ALU_XOR (Z_to_bv 64 (TB_OW + 4)) (Z_to_bv 64 (-1))).
    { change (sv_denot E0 (SAlu ALU_XOR (SOff 253 4) (SLit (-1))))
        with (alu64 ALU_XOR (Z_to_bv 64 (bv_unsigned (ew E0 253%nat) + 4)) (Z_to_bv 64 (-1))).
      rewrite E12', unsigned_lit_small by lia. reflexivity. }
    assert (Hcase : TW.OW_n Bw = 0 \/ TW.OW_n Bw = 1 \/ TW.OW_n Bw = 2 \/ TW.OW_n Bw = 3 \/
      TW.OW_n Bw = 4 \/ TW.OW_n Bw = 5 \/ TW.OW_n Bw = 6 \/ TW.OW_n Bw = 7 \/
      TW.OW_n Bw = 8 \/ TW.OW_n Bw = 9 \/ TW.OW_n Bw = 10 \/ TW.OW_n Bw = 11 \/
      TW.OW_n Bw = 12 \/ TW.OW_n Bw = 13 \/ TW.OW_n Bw = 14 \/ TW.OW_n Bw = 15)
      by (unfold TCB.TRANS_MAX in Hn; lia).
    destruct Hcase as [Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|Hi]]]]]]]]]]]]]]].
    (* in each case OW.n = i (a literal): a6 = i, pinned *)
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      ms_reg HS (Z_to_bv 5 16) (Z_to_bv 64 i) Q16 ltac:(rewrite Dn, Hi; reflexivity) end.
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
        pose proof (st_ok_pi_pin_reg' Ex ss (restrict Hh m) (Z_to_bv 5 16) i HS Q16 eq_refl) as HSp end end.
    all: clear HS Q16.
    all: lazymatch type of HSp with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
      let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HSp end.
    (* the 12 bytes of OW.t[i] join the state, a writable region of G *)
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      lazymatch type of HSp with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
        pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) (ms_tr_region i) HSp eq_refl
          (ms_tr_ok Ex _ i UO ltac:(lia)) ltac:(cbn [ss_mem YP09.all_disjoint];
            unfold YP09.extent_disjoint, ms_tr_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
            rewrite ?Usp, ?U58', ?UO', ?UG', ?UC', ?UO;
            unfold FCells.GOT_CELL_K, FCells.CELL_K; repeat split; lia)) as HS end end.
    all: clear HSp.
    all: lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
      let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.
    (* run 3b, +0x24 .. +0x44: the index check `bgeu a6, 16` is decided (a6 = i); p - OW - 4 = 12 * i; it stops at
       `bltu a3, a2`, UBSan's pointer-overflow check of &OW.t[i] *)
    all: paj_run_tok RUN HS HJ SHOK YC4b.Bspan; [ms_awr Usp U58' UO' |].
    all: set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *; clearbody md3; clear mat; rename ms into ms3.
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ ms_W3 (spZ regs) i a ->
        aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) (ms_mem ms2) a)
      by (intros a Ha H1; apply (kept_of_frame _ _ _ _ _ (ms_W3 (spZ regs) i) HFr); [| exact Ha | exact H1];
          intros b wlo whi x Hin Hx; ms_win Hin Hx ltac:(rewrite ?Usp, ?U58', ?UO' in Hx; unfold ms_W3, ms_W0; lia))
      end.
    all: assert (GA3 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms3) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
    all: clear HF HFr HG.
    all: psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    (* the branch to the trap word 0x852e0: ~(OW + 4) < 12 * i never holds (OW + 4 + 12 * i < 2 ^ 64) *)
    all: lazymatch goal with
      | Hb : branch_taken BC_LTU _ _ = true |- _ =>
          exfalso; rewrite DX in Hb; cbn [branch_taken sv_denot] in Hb; vm_compute in Hb; discriminate Hb
      | _ => idtac end.
    (* run 4b, +0x44 .. +0xb8: the three checked stores at p, p + 4, p + 8 (each check decided by MS_SH: no call of
       __asan_report_store4), a1 = i + 1 and its overflow check (decided), OW.n = i + 1, M.state = st, `ret` *)
    all: paj_run_tok RUN HS HJ SHOK YC4b.Bspan; [ms_awr Usp U58' UO' |].
    all: set (mdF := with_vm_backing (m_vm_lazy md3) mat md3) in *; clearbody mdF; clear mat; rename ms into msF.
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ ms_W3 (spZ regs) i a ->
        aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) (ms_mem ms3) a)
      by (intros a Ha H1; apply (kept_of_frame _ _ _ _ _ (ms_W3 (spZ regs) i) HFr); [| exact Ha | exact H1];
          intros b wlo whi x Hin Hx; ms_win Hin Hx ltac:(rewrite ?Usp, ?U58', ?UO' in Hx; unfold ms_W3, ms_W0; lia))
      end.
    all: assert (GAF : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msF) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA3 a Ha))).
    all: clear HF HFr HG.
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MSET_STK <= a < spZ regs) -> ~ mset_st_wr Bw st a ->
        aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a)
      by (intros a Ha H1 H2;
          assert (NW : ~ ms_W3 (spZ regs) i a)
          by (intros HW; apply H2; split; [exact Hne|]; unfold ms_W3, ms_W0 in HW;
              unfold mset_wr, twb_fld, TW.A_M_state, TW.A_OW_n, TW.A_OW_t_state, TW.OW_t_ESZ;
              unfold TCB.TRANS_MAX; rewrite FS in H1;
              destruct HW as [[HW|[HW|HW]]|HW];
              [exfalso; lia | right; right; lia | right; left; lia | left; split; lia]);
          rewrite (KR4 a Ha NW), (KR3 a Ha NW); apply KA2; [exact Ha | intros HW; apply NW; left; exact HW])
      end.
    (* the bytes the code stored, read from the last state's chunks *)
    all: ms_chunk HS 4%nat 0%nat U58' st D10 VS.
    all: pose proof (ms_off0 _ _ _ VS) as VS'.
    all: ms_chunk HS 0%nat 2%nat UO' st D10 VTS.
    all: ms_chunk HS 0%nat 1%nat UO' (TW.M_state Bw) Dst VTO.
    all: ms_chunk HS 0%nat 0%nat UO' why D11 VTR.
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      assert (DNi : sv_denot E0 (SLit (i + 1)) = Z_to_bv 64 (TW.OW_n Bw + 1)) by (cbn [sv_denot]; rewrite Hi; reflexivity)
      end.
    all: ms_chunk HS 5%nat 0%nat UO' (TW.OW_n Bw + 1) DNi VN.
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      assert (HWF : tw_at TMAP_B (aview segs (w_H W) (ms_mem msF)) Bw')
      by (rewrite HB'; apply (ms_world3 Bw (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem msF))
            (TW.OW_n Bw) st (TW.M_state Bw) why Htw ltac:(unfold TCB.TRANS_MAX in Hn; lia));
          [ intros j Hj; rewrite Hi; exact (VTS j Hj)
          | intros j Hj; rewrite Hi; exact (VTO j Hj)
          | intros j Hj; rewrite Hi; exact (VTR j Hj)
          | exact VN
          | exact VS'
          | intros x Hx N1 N2 N3; pose proof (GLOW x (ms_tw_in_G x Hx)) as Hl; unfold kLowMemEnd in Hl;
            apply KAF; [lia | rewrite FS; lia |]; intros [_ Hw];
            unfold mset_wr, twb_fld, TW.A_M_state, TW.A_OW_n, TW.A_OW_t_state, TW.OW_t_ESZ in Hw;
            destruct Hw as [[_ Hw]|[Hw|Hw]]; lia ])
      end.
    (* the return *)
    all: ms_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
      ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    all: assert (HPF : aregs_preserved regs (ms_regs msF))
      by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ msF regs
            [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4); Z_to_bv 64 (TW.u_at Bw TW.A_OW_n 4)] HS);
          [apply ms_agree | vm_compute; reflexivity]).
    all: eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    all: let mat' := fresh "mat" in intros mat';
      exact (ms_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw st Bw' (ms_regs msF) (ms_mem msF) mdF
        LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAF HWF HPF RF1 mat').
Qed.

End msw.

(* The statement of lib/B/Prog/m_set_cg.v. *)
Theorem transport_m_set_cg_holds : forall fx rc B MT, @transport_m_set_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ms_holds fx rc B MT). Qed.

Print Assumptions transport_m_set_cg_holds.
