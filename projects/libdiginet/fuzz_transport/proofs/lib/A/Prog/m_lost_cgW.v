(* m_lost_cgW: Theorem transport_m_lost_cg_holds : the statement transport_m_lost_cg_holds_stmt of
   lib/A/Prog/m_lost_cg.v, the machine walk of m_lost (fuzz/fuzz_transport.c:210-215, m_set :196-207 inlined) on
   fuzz_transport.asan at 0x85004 = transport_sigma TS_m_lost (236 bytes, frame 16).

   The walk is a G-form walk, as lib/A/Prog/diginet_session_config_default.v: it holds the caller's journal
   ajournal_gx G_HARNESS 0 [] (lib/A/W_journalG.v) from the entry to the return, and the runs are the symbolic runs of
   lib/A/Prog/PaShadow.v taken over that journal (TransportGRunA.v paj_run_x); every store into M or OW is a byte of G,
   allowed by the run's write right awr_ok_x.
   The symbolic state (ml_regions): the 16-byte frame below sp, the shadow base's GOT word and cell, and four
   writable regions of G: M.state (M + 12, which holds atom 33, the world's 4 bytes as an unsigned int),
   M.desk_counter_valid (M + 76), M.fly.on (M + 96) and OW.n (OW + 0, atom 34). The atoms of M and OW are the
   listing's image objects 8 and 12, with exact facts (their bases, 32-byte aligned).
     run 1  (0x85004 .. 0x8502c)  the frame, ra saved, the shadow base through its GOT word, M.state loaded, the two
                                  stores of 0 at M + 76 and M + 96; it stops at `beqz a7` (a7 = M.state).
     M.state = 0:   run 2a (0x8502c .. 0x850b0) the epilogue and `ret`.
     M.state <> 0:  run 2b (0x8502c .. 0x85040) a4 = &OW, a5 = OW.n, a1 = 15; it stops at `blt a1, a5`.
       15 < OW.n:   run 3a (0x85040 .. 0x850b0) OW.n + 1 and M.state = 0 stored, the epilogue, `ret`.
       OW.n <= 15:  the model premise gives 0 <= OW.n (m_set_m is None below 0), so OW.n is one of 0 .. 15. In each
                    case a5 is pinned to that literal and the 12 bytes of OW.t[OW.n] join the state as a writable
                    region of G (ml_tr_region). Run 3b (0x85040 .. 0x850b0) computes p = OW + 4 + 12 * OW.n, and the
                    token engine decides the three instrumented checks of the stores at p, p + 4 and p + 8 against
                    the shadow entry of OW's 304 bytes (ML_SH, whose shadow is 0 by trans_ow_cells: ml_shok), so no
                    call of errpath_store4 (0x850c4, 0x850d8, 0x850ec) is reached; then OW.n + 1, M.state = 0, `ret`.
   The post (ml_close): transport_cg_post over G_HARNESS, acall_kept_g by TransportGCg.v dk_kept_step_g over the
   stack window and mlost_wr Bw. The world relation at Bw' (ml_world1 / ml_world2 / ml_world3): the model's world
   (ml_model) is one write per field it sets, each a TWorldG.v tw_write whose bytes are read from the chunks of the
   last state; every other payload byte is kept. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.

(* ------------------------------------------------------------------ *)
(* Bytes, branches and the model                                       *)
(* ------------------------------------------------------------------ *)

(* Byte j < 4 of a 64-bit word holding v is byte j of the 4-byte little-endian v (signed or not). *)
Lemma ml_bow : forall v j, (j < 4)%nat ->
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

(* beqz / blt on the sign-extended values (the plain walk's m_lost_eqb0 / m_lost_lts). *)
Lemma ml_eqb0 : forall x, -2^31 <= x < 2^31 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec x 0) as [->|Hne]; [reflexivity|].
  apply Z.eqb_neq. rewrite Zmod_0_l. intro E. Z.div_mod_to_equations. lia.
Qed.
Lemma ml_lts : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2^63); lia). reflexivity.
Qed.

(* The 4-byte signed load of an atom holding the unsigned int u. *)
Lemma ml_sext_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (LMem.signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma ml_add_den : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

(* the model's world after the two stores before m_set *)
Definition ml_B1 (Bw : list byte) : list byte := TW.set_M_desk_counter_valid (TW.set_M_fly_on Bw 0) 0.

Lemma ml_B1_len : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  Z.of_nat (length (TW.upd Bw (TW.OFF_M + 96 + 0) (TW.put 4 0))) = TW.W_LEN.
Proof.
intros Bw HL. assert (WL : TW.W_LEN = 65616) by reflexivity.
rewrite TWL.length_upd_put; [exact HL | unfold TW.OFF_M; lia | try change (Z.of_nat 4) with 4; unfold TW.OFF_M; lia].
Qed.

Lemma ml_B1_state : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> TW.M_state (ml_B1 Bw) = TW.M_state Bw.
Proof.
intros Bw HL. assert (WL : TW.W_LEN = 65616) by reflexivity. pose proof (ml_B1_len Bw HL) as L1.
unfold ml_B1, TW.M_state, TW.set_M_desk_counter_valid, TW.set_M_fly_on, TW.A_M_state, TW.A_M_desk_counter_valid,
  TW.A_M_fly_on.
rewrite (TWL.s32_at_upd_out _ (TW.put 4 0)) by (rewrite ?TWL.length_put, ?L1; try change (Z.of_nat 4) with 4;
  unfold TW.OFF_M in *; lia).
rewrite (TWL.s32_at_upd_out Bw (TW.put 4 0)) by (rewrite ?TWL.length_put; try change (Z.of_nat 4) with 4;
  unfold TW.OFF_M in *; lia).
reflexivity.
Qed.

Lemma ml_B1_n : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> TW.OW_n (ml_B1 Bw) = TW.OW_n Bw.
Proof.
intros Bw HL. assert (WL : TW.W_LEN = 65616) by reflexivity. pose proof (ml_B1_len Bw HL) as L1.
unfold ml_B1, TW.OW_n, TW.set_M_desk_counter_valid, TW.set_M_fly_on, TW.A_OW_n, TW.A_M_desk_counter_valid,
  TW.A_M_fly_on.
rewrite (TWL.s32_at_upd_out _ (TW.put 4 0)) by (rewrite ?TWL.length_put, ?L1; try change (Z.of_nat 4) with 4;
  unfold TW.OFF_M, TW.OFF_OW in *; lia).
rewrite (TWL.s32_at_upd_out Bw (TW.put 4 0)) by (rewrite ?TWL.length_put; try change (Z.of_nat 4) with 4;
  unfold TW.OFF_M, TW.OFF_OW in *; lia).
reflexivity.
Qed.

Lemma ml_some_inv : forall x y : list byte, Some (x, tt) = Some (y, tt) -> y = x.
Proof. intros x y H. injection H as H. symmetry. exact H. Qed.

(* The model's world after the call, by m_set's three outcomes. *)
Lemma ml_model : forall Bw why Bw', Z.of_nat (length Bw) = TW.W_LEN ->
  TCB.m_lost_m Bw why = Some (Bw', tt) ->
  (TW.M_state Bw = TCB.S_IDLE /\ Bw' = ml_B1 Bw) \/
  (TW.M_state Bw <> TCB.S_IDLE /\ TCB.TRANS_MAX <= TW.OW_n Bw /\ TW.OW_n Bw <> TCB.INT_MAX /\
     Bw' = TW.set_M_state (TW.set_OW_n (ml_B1 Bw) (TW.OW_n Bw + 1)) TCB.S_IDLE) \/
  (TW.M_state Bw <> TCB.S_IDLE /\ 0 <= TW.OW_n Bw < TCB.TRANS_MAX /\
     Bw' = TW.set_M_state (TW.set_OW_n (TW.set_OW_t_reason (TW.set_OW_t_old
       (TW.set_OW_t_state (ml_B1 Bw) (TW.OW_n Bw) TCB.S_IDLE) (TW.OW_n Bw) (TW.M_state Bw)) (TW.OW_n Bw) why)
       (TW.OW_n Bw + 1)) TCB.S_IDLE).
Proof.
intros Bw why Bw' HL Hm.
unfold TCB.m_lost_m, TCB.m_set_m, TCB.int_inc in Hm. fold (ml_B1 Bw) in Hm.
rewrite (ml_B1_state Bw HL), (ml_B1_n Bw HL) in Hm.
cbv zeta in Hm. revert Hm.
destruct (Z.eqb_spec (TW.M_state Bw) TCB.S_IDLE) as [Es|Es]; intros Hm; cbv beta iota in Hm.
- left. split; [exact Es|]. exact (ml_some_inv _ _ Hm).
- right. revert Hm.
  destruct (Z.ltb_spec (TW.OW_n Bw) TCB.TRANS_MAX) as [Lt|Ge];
  [destruct (Z.ltb_spec (TW.OW_n Bw) 0) as [L0|G0] |];
  destruct (Z.eqb_spec (TW.OW_n Bw) TCB.INT_MAX) as [EI|NI]; intros Hm; cbv beta iota in Hm;
  try discriminate Hm.
  + right. split; [exact Es|]. split; [lia|]. exact (ml_some_inv _ _ Hm).
  + left. split; [exact Es|]. split; [lia|]. split; [exact NI|]. exact (ml_some_inv _ _ Hm).
Qed.

(* ------------------------------------------------------------------ *)
(* The world relation at the model's world                             *)
(* ------------------------------------------------------------------ *)

(* A view that is rdF on the bytes P marks and rd0 elsewhere: the written bytes so far, the entry's on the others. *)
Definition ml_in (lo n x : Z) : bool := (lo <=? x) && (x <? lo + n).
Definition ml_mix (P : Z -> bool) (rdF rd0 : Z -> option Z) : Z -> option Z :=
  fun x => if P x then rdF x else rd0 x.

Lemma ml_in_true : forall lo n x, lo <= x < lo + n -> ml_in lo n x = true.
Proof. intros lo n x H. unfold ml_in. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma ml_in_false' : forall lo n x, ~ (lo <= x < lo + n) -> ml_in lo n x = false.
Proof.
intros lo n x H. unfold ml_in. destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + n)); cbn [andb];
  first [reflexivity | exfalso; lia].
Qed.
Lemma ml_in_false : forall lo n x, ml_in lo n x = false -> ~ (lo <= x < lo + n).
Proof. intros lo n x H Hx. rewrite (ml_in_true lo n x Hx) in H. discriminate H. Qed.

Lemma ml_tw_start : forall rdF rd0 Bw, tw_at TMAP_A rd0 Bw -> tw_at TMAP_A (ml_mix (fun _ => false) rdF rd0) Bw.
Proof. intros rdF rd0 Bw H. apply (tw_kept TMAP_A rd0 _ Bw H). intros x _. reflexivity. Qed.

(* One 4-byte store of v at the world offset ko = o + k of the row (o, b, n). *)
Lemma ml_tw_step : forall rdF rd0 P Bw o b n k ko v,
  tw_at TMAP_A (ml_mix P rdF rd0) Bw -> In (o, b, n) TMAP_A -> ko = o + k -> 0 <= k -> k + 4 <= n ->
  (forall j, (j < 4)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  tw_at TMAP_A (ml_mix (fun x => P x || ml_in (b + k) 4 x) rdF rd0) (TW.upd Bw ko (TW.put 4 v)).
Proof.
intros rdF rd0 P Bw o b n k ko v H Hin Hko Hk Hkn HV. subst ko.
apply (tw_write TMAP_A (ml_mix P rdF rd0) (ml_mix (fun x => P x || ml_in (b + k) 4 x) rdF rd0) Bw o b n k 4 v
  TMAP_A_ok H Hin Hk ltac:(change (Z.of_nat 4) with 4; lia)).
- intros j Hj. unfold ml_mix. cbv beta.
  rewrite (ml_in_true (b + k) 4 (b + k + Z.of_nat j)) by lia. rewrite orb_true_r. exact (HV j Hj).
- intros x Hx Hn. unfold ml_mix. cbv beta. change (Z.of_nat 4) with 4 in Hn.
  rewrite (ml_in_false' (b + k) 4 x) by lia. rewrite orb_false_r. reflexivity.
Qed.

Lemma ml_tw_end : forall rdF rd0 P Bw, tw_at TMAP_A (ml_mix P rdF rd0) Bw ->
  (forall x, tw_in TMAP_A x -> P x = false -> rdF x = rd0 x) -> tw_at TMAP_A rdF Bw.
Proof.
intros rdF rd0 P Bw H Hk. apply (tw_kept TMAP_A (ml_mix P rdF rd0) rdF Bw H).
intros x Hx. unfold ml_mix. destruct (P x) eqn:E; [reflexivity | exact (Hk x Hx E)].
Qed.

Ltac ml_unP HP :=
  cbv beta in HP;
  repeat match type of HP with
  | orb _ _ = false =>
      let Hq := fresh "Hq" in apply orb_false_iff in HP; destruct HP as [HP Hq]; apply ml_in_false in Hq
  end.

(* M.state = S_IDLE: M.fly.on and M.desk_counter_valid. *)
Lemma ml_world1 : forall Bw rd0 rdF,
  tw_at TMAP_A rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 76 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_M + 96 <= x < TA_M + 100) -> ~ (TA_M + 76 <= x < TA_M + 80) ->
     rdF x = rd0 x) ->
  tw_at TMAP_A rdF (ml_B1 Bw).
Proof.
intros Bw rd0 rdF Htw V96 V76 Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity.
unfold ml_B1, TW.set_M_desk_counter_valid, TW.set_M_fly_on, TW.A_M_desk_counter_valid, TW.A_M_fly_on.
pose proof (ml_tw_start rdF rd0 Bw Htw) as H0.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 96 (TW.OFF_M + 96 + 0) 0 H0 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(lia) V96) as H1.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 76 (TW.OFF_M + 76) 0 H1 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(lia) V76) as H2.
apply (ml_tw_end rdF rd0 _ _ H2).
intros x Hx HP. ml_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

(* M.state <> S_IDLE, OW.n >= TRANS_MAX: also OW.n + 1 and M.state. *)
Lemma ml_world2 : forall Bw rd0 rdF n,
  tw_at TMAP_A rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 76 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (n + 1) 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte TCB.S_IDLE 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_M + 96 <= x < TA_M + 100) -> ~ (TA_M + 76 <= x < TA_M + 80) ->
     ~ (TA_OW <= x < TA_OW + 4) -> ~ (TA_M + 12 <= x < TA_M + 16) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_M_state (TW.set_OW_n (ml_B1 Bw) (n + 1)) TCB.S_IDLE).
Proof.
intros Bw rd0 rdF n Htw V96 V76 VN VS Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold ml_B1, TW.set_M_state, TW.set_OW_n, TW.set_M_desk_counter_valid, TW.set_M_fly_on, TW.A_M_state,
  TW.A_OW_n, TW.A_M_desk_counter_valid, TW.A_M_fly_on.
pose proof (ml_tw_start rdF rd0 Bw Htw) as H0.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 96 (TW.OFF_M + 96 + 0) 0 H0 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(lia) V96) as H1.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 76 (TW.OFF_M + 76) 0 H1 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(lia) V76) as H2.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 0 (TW.OFF_OW + 0) (n + 1) H2 TMAP_A_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VN) as H3.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 12 (TW.OFF_M + 12) TCB.S_IDLE H3 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(lia) VS) as H4.
apply (ml_tw_end rdF rd0 _ _ H4).
intros x Hx HP. ml_unP HP. apply Hk; [exact Hx | lia | lia | lia | lia].
Qed.

(* M.state <> S_IDLE, 0 <= OW.n = i < TRANS_MAX: also OW.t[i]'s three fields. *)
Lemma ml_world3 : forall Bw rd0 rdF i st why,
  tw_at TMAP_A rd0 Bw -> 0 <= i < 16 ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 76 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + (4 + 12 * i) + Z.of_nat j) = Some (YO0f.le_byte TCB.S_IDLE 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + (8 + 12 * i) + Z.of_nat j) = Some (YO0f.le_byte st 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + (12 + 12 * i) + Z.of_nat j) = Some (YO0f.le_byte why 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (i + 1) 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte TCB.S_IDLE 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_M + 96 <= x < TA_M + 100) -> ~ (TA_M + 76 <= x < TA_M + 80) ->
     ~ (TA_OW + 4 + 12 * i <= x < TA_OW + 16 + 12 * i) -> ~ (TA_OW <= x < TA_OW + 4) ->
     ~ (TA_M + 12 <= x < TA_M + 16) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_M_state (TW.set_OW_n (TW.set_OW_t_reason (TW.set_OW_t_old
    (TW.set_OW_t_state (ml_B1 Bw) i TCB.S_IDLE) i st) i why) (i + 1)) TCB.S_IDLE).
Proof.
intros Bw rd0 rdF i st why Htw Hi V96 V76 VTS VTO VTR VN VS Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold ml_B1, TW.set_M_state, TW.set_OW_n, TW.set_OW_t_reason, TW.set_OW_t_old, TW.set_OW_t_state,
  TW.set_M_desk_counter_valid, TW.set_M_fly_on, TW.A_M_state, TW.A_OW_n, TW.A_OW_t_reason, TW.A_OW_t_old,
  TW.A_OW_t_state, TW.A_M_desk_counter_valid, TW.A_M_fly_on.
pose proof (ml_tw_start rdF rd0 Bw Htw) as H0.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 96 (TW.OFF_M + 96 + 0) 0 H0 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(lia) V96) as H1.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 76 (TW.OFF_M + 76) 0 H1 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(lia) V76) as H2.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW (4 + 12 * i) (TW.OFF_OW + 4 + 12 * i + 0)
  TCB.S_IDLE H2 TMAP_A_OW ltac:(lia) ltac:(lia) ltac:(lia) VTS) as H3.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW (8 + 12 * i) (TW.OFF_OW + 4 + 12 * i + 4)
  st H3 TMAP_A_OW ltac:(lia) ltac:(lia) ltac:(lia) VTO) as H4.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW (12 + 12 * i) (TW.OFF_OW + 4 + 12 * i + 8)
  why H4 TMAP_A_OW ltac:(lia) ltac:(lia) ltac:(lia) VTR) as H5.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 0 (TW.OFF_OW + 0) (i + 1) H5 TMAP_A_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VN) as H6.
pose proof (ml_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 12 (TW.OFF_M + 12) TCB.S_IDLE H6 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(lia) VS) as H7.
apply (ml_tw_end rdF rd0 _ _ H7).
intros x Hx HP. ml_unP HP. apply Hk; [exact Hx | lia | lia | lia | lia | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* G                                                                   *)
(* ------------------------------------------------------------------ *)

Lemma ml_inG : forall a, (TA_M <= a < TA_M + 1648) \/ (TA_OW <= a < TA_OW + 304) -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. destruct Ha as [Ha|Ha].
- exists (TA_M, TW.SZ_M). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_M) | unfold in_zr, TW.SZ_M; cbn [fst snd]; lia].
- exists (TA_OW, TW.SZ_OW). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_OW) | unfold in_zr, TW.SZ_OW; cbn [fst snd]; lia].
Qed.

(* A payload byte of the world table is a byte of G. *)
Lemma ml_tw_in_G : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x.
Proof.
intros x (o & b & n & Hin & Hx).
assert (HG : In (b, n) TG.G_HARNESS)
  by exact (tw_in_G_of TMAP_A TG.G_HARNESS ltac:(vm_compute; reflexivity) o b n Hin).
unfold inG. apply Exists_exists. exists (b, n). split; [exact HG | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The bytes m_lost writes are bytes of G. *)
Lemma ml_wr_inG : forall Bw a, mlost_wr Bw a -> inG TG.G_HARNESS a.
Proof.
intros Bw a H. apply ml_inG.
unfold mlost_wr, mset_wr, twa_fld, TW.A_M_desk_counter_valid, TW.A_M_fly_on, TW.A_M_state, TW.A_OW_n,
  TW.A_OW_t_state, TW.OW_t_ESZ, TCB.TRANS_MAX, TCB.S_IDLE in H.
lia.
Qed.

Lemma ml_in4 : forall b a, b <= a < b + 4 -> exists j, (j < 4)%nat /\ a = b + Z.of_nat j.
Proof. intros b a H. exists (Z.to_nat (a - b)). split; lia. Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the entry                                     *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base, 33 the 4 bytes of M.state and 34 the 4 bytes of
   OW.n as unsigned ints. Regions: the 16-byte frame below sp (ra at sp - 8), the shadow base's GOT word (object 1)
   and its cell (object 93), and the four fields of G the code loads or stores (M: object 8; OW: object 12). *)
Definition ml_st_region : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 12 16 12 16 [YP09.mkChunk 12 (CVal 4 (SOff 33 0))].
Definition ml_dcv_region : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 76 80 76 80 [].
Definition ml_fly_region : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 96 100 96 100 [].
Definition ml_n_region : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))].
Definition ml_regions : smem :=
  [stack_region MLOST_FRAME; got_regionP; bcell_regionP 32; ml_st_region; ml_dcv_region; ml_fly_region; ml_n_region].
Definition ml_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (A_OBJ 8, mkAF TA_M TA_M 5); (A_OBJ 12, mkAF TA_OW TA_OW 5)] [] [].
Definition ss_ml : sstate := mkSS AF_m_lost sr_atoms ml_regions None ml_facts.
(* The shadow entry of OW's 304 bytes (38 whole granules), and the shadow base of the token engine. *)
Definition ML_SH : list shent := [mkSHE (A_OBJ 12) 0 304].
Definition ML_Bx : sv := SOff 32 0.
(* OW.t[i]'s 12 bytes, the region the case OW.n = i adds before run 3b. *)
Definition ml_tr_region (i : Z) : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 12)) (4 + 12 * i) (16 + 12 * i) (4 + 12 * i) (16 + 12 * i) [].

(* The writable windows of the runs: the frame and the four fields; run 3b also OW.t[i]. *)
Definition ml_W0 (sp a : Z) : Prop :=
  (sp - 16 <= a < sp) \/ (TA_M + 12 <= a < TA_M + 16) \/ (TA_M + 76 <= a < TA_M + 80) \/
  (TA_M + 96 <= a < TA_M + 100) \/ (TA_OW <= a < TA_OW + 4).
Definition ml_W3 (sp i a : Z) : Prop := ml_W0 sp a \/ (TA_OW + 4 + 12 * i <= a < TA_OW + 16 + 12 * i).

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ml_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ml_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac ml_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of a run: the frame below sp (inside the caller's stack window), the read-only image cells (no
   writable byte), and the regions of M and OW (bytes of G). *)
Ltac ml_awr UspE UME UOE :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ lia
      | rewrite UspE in Ha; left; split; [unfold awr_byte; left; lia | lia]
      | rewrite UME in Ha; right; left; apply ml_inG; lia
      | rewrite UOE in Ha; right; left; apply ml_inG; lia ] |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

Section mlw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma ml_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 8) = TA_M /\ VAL (A_OBJ 12) = TA_OW /\ BASE + AF_m_lost = transport_sigma TS_m_lost.
Proof. vm_compute. repeat split. Qed.

(* The two image cells hold what transport_cells says they hold, at any AR state. *)
Lemma ml_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H W) mem) got_regionP /\ region_ok segs E (mrestrict (w_H W) mem) (bcell_regionP 32).
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct ml_vals as (V1 & V93 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (R93 : 0 <= VAL (A_OBJ 93) < 2 ^ 47) by (rewrite V93; unfold FCells.CELL_K; lia).
  unfold got_regionP, bcell_regionP, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split.
  - rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 93) 0) (VAL (A_OBJ 93)));
    [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 93)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
Qed.

(* OW's 304 bytes are addressable at every AR state: the shadow of its 38 whole granules is 0 (trans_ow_cells). *)
Lemma ml_ra : forall ly S (W : world segs) mem md,
  trans_ow_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF TA_OW 304.
Proof.
intros ly S W mem md HZ HAR x Hx.
assert (EO : TA_OW = 6238304) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr.
exists 0. split; [|left; reflexivity].
assert (Hz := decode_zshadow_rd B ly S W mem md TA_OW (TA_OW + TW.SZ_OW) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The run's shadow entry holds at every AR state. *)
Lemma ml_shok : forall ly S (W : world segs) mem md (E : env),
  trans_ow_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 12) = Z_to_bv 64 TA_OW -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs ML_Bx ML_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HOW HAR E12 E32.
assert (EO : TA_OW = 6238304) by reflexivity.
unfold sh_ok, ML_SH. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H W) mem E ML_Bx (A_OBJ 12) TA_OW 304 TA_OW 0 304 (ml_ra ly S W mem md HOW HAR)).
- unfold U, ML_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The walk's valuation: the 32 registers at the entry, the shadow base, and the world's M.state and OW.n. *)
Definition ml_E (regs : bvmap 5 word) (ust un : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 ust; Z_to_bv 64 un]).

(* The entry state, and the shadow entry of OW. *)
Lemma ml_entry : forall ly S (W : world segs) regs mem md ust un,
  transport_cells B -> trans_ow_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - MLOST_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  0 <= ust < 2 ^ 32 -> 0 <= un < 2 ^ 32 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TA_M + 12) 4 ust ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TA_OW + 0) 4 un ->
  st_ok_pi segs VAL (ml_E regs ust un) ss_ml
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_lost)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs ML_Bx ML_SH (ml_E regs ust un) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md ust un HCELLS HOW HAR Hpres Hsp Hsp16 Hust Hun Vst Vn.
  assert (EM : TA_M = 6156640) by reflexivity. assert (EO : TA_OW = 6238304) by reflexivity.
  assert (FF : MLOST_FRAME = 16) by reflexivity.
  assert (E2 : ew (ml_E regs ust un) 2 = YK11.getr regs 2) by (unfold ml_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew (ml_E regs ust un) 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (E32 : ew (ml_E regs ust un) 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold ml_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew (ml_E regs ust un) 33 = Z_to_bv 64 ust)
    by (unfold ml_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew (ml_E regs ust un) 34 = Z_to_bv 64 un)
    by (unfold ml_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (EOB : forall j, (j < 95)%nat -> ew (ml_E regs ust un) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold ml_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct (ml_img_ok ly S W mem md (ml_E regs ust un) HCELLS HAR (EOB 1%nat ltac:(lia)) (EOB 93%nat ltac:(lia)) E32)
    as [RG RC].
  destruct ml_vals as (V1 & V93 & V8 & V12 & _).
  assert (VB : forall n v0, ew (ml_E regs ust un) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (ml_E regs ust un) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (B8 : base_val (ml_E regs ust un) (Some (A_OBJ 8)) = TA_M)
    by (apply VB; [rewrite (EOB 8%nat ltac:(lia)), V8; reflexivity | lia]).
  assert (B12 : base_val (ml_E regs ust un) (Some (A_OBJ 12)) = TA_OW)
    by (apply VB; [rewrite (EOB 12%nat ltac:(lia)), V12; reflexivity | lia]).
  assert (U8 : bv_unsigned (ew (ml_E regs ust un) (A_OBJ 8)) = TA_M) by exact B8.
  assert (U12 : bv_unsigned (ew (ml_E regs ust un) (A_OBJ 12)) = TA_OW) by exact B12.
  split.
  - rewrite restrict_mkst_fx. unfold ss_ml, ml_regions.
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_cons; [exact RC |]]].
      * unfold stack_region, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Usp. unfold MLOST_FRAME in *.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
        -- unfold ml_st_region, region_ok.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
           rewrite B8. split; [lia|]. split; [lia|]. split.
           ++ intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply ml_inG. lia.
           ++ constructor; [|constructor].
              apply (chunk_ok_val segs (ml_E regs ust un) _ TA_M 12 4 (SOff 33 0) ust);
              [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Vst].
        -- unfold ml_dcv_region, region_ok.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
           rewrite B8. split; [lia|]. split; [lia|]. split; [|constructor].
           intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply ml_inG. lia.
        -- unfold ml_fly_region, region_ok.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
           rewrite B8. split; [lia|]. split; [lia|]. split; [|constructor].
           intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply ml_inG. lia.
        -- unfold ml_n_region, region_ok.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
           rewrite B12. split; [lia|]. split; [lia|]. split.
           ++ intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw). apply ml_inG. lia.
           ++ constructor; [|constructor].
              apply (chunk_ok_val segs (ml_E regs ust un) _ TA_OW 0 4 (SOff 34 0) un);
              [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Vn].
    + apply pairwise_disjoint_of_extents.
      unfold stack_region, got_regionP, bcell_regionP, ml_st_region, ml_dcv_region, ml_fly_region, ml_n_region,
        extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (EOB 93%nat ltac:(lia))) by (rewrite V93; unfold FCells.CELL_K; lia).
      rewrite B8, B12.
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      rewrite V1, V93. unfold FCells.GOT_CELL_K, FCells.CELL_K, MLOST_FRAME in *.
      repeat split; first [exact I | lia].
    + unfold ml_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U8, U12, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite ?EM, ?EO; reflexivity].
  - apply (ml_shok ly S W mem md (ml_E regs ust un) HOW HAR); [rewrite (EOB 12%nat ltac:(lia)), V12; reflexivity | exact E32].
Qed.

(* The walk's valuation agrees with the entry registers below atom 32. *)
Lemma ml_agree : forall regs ust un,
  env_agree 32 (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 ust; Z_to_bv 64 un]) (ml_E regs ust un).
Proof.
  intros regs ust un. split.
  - intros n Hn. unfold ml_E. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity.
  - reflexivity.
Qed.

(* OW.t[i]'s region at any memory: its 12 bytes are bytes of G, so writable. *)
Lemma ml_tr_ok : forall E (m : word -> option byte) i, bv_unsigned (ew E (A_OBJ 12)) = TA_OW -> 0 <= i < 16 ->
  region_ok segs E m (ml_tr_region i).
Proof.
intros E m i HU Hi. assert (EO : TA_OW = 6238304) by reflexivity.
unfold ml_tr_region, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HU. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw). apply ml_inG. lia.
Qed.

(* The 4 bytes of a chunk of value v (signed or not), read through the view. *)
Lemma ml_chunk_rd : forall (E : env) (H : word -> bool) (mm : word -> option byte) (base off : Z) (e : sv) (v : Z),
  YP09.chunk_ok segs E (mrestrict H mm) base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 4)%nat -> aview segs H mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
intros E H mm base off e v HC He j Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC (Z.of_nat j) ltac:(cbn; lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview segs H mm (base + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H mm) (base + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply ml_bow. exact Hj.
Qed.

(* The post at the return, from the walk's last facts. *)
Lemma ml_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw Bw' regsF mF mdF,
  AR_laws segs B -> ameter_laws MT -> gx_ok segs B TG.G_HARNESS ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MLOST_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - MLOST_STK -> spZ regs <= 2 ^ 47 ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mF mdF k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MLOST_STK <= a < spZ regs) -> ~ mlost_wr Bw a ->
     aview segs (w_H W) mF a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mF a) ->
  tw_at TMAP_A (aview segs (w_H W) mF) Bw' ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 ->
  forall mat, @transport_mlost_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' regsF mF mdF
    LAWS MTL HGX HAR Hwin Hce Hsp47 Hra HJF KA GA HW HP RF1 mat.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : MLOST_STK = 16) by reflexivity.
  assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (transport_segs_low a (proj1 (HGX a Ha)))).
  unfold transport_mlost_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
  split.
  { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [unfold MLOST_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc mF
      (spZ regs - MLOST_STK) (spZ regs) (mlost_wr Bw)
      (fun a => (spZ regs - MLOST_STK <= a < spZ regs) \/ mlost_wr Bw a) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - intros a Ha Hn. apply KA; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; exact H].
    - exact GA.
    - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso.
      pose proof (GLOW a (ml_wr_inG Bw a Hw)) as Hl. unfold kLowMemEnd in Hl. lia.
    - intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    - intros a [Hw | Hw] Hi HnG _ _.
      + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
      + apply HnG. exact (ml_wr_inG Bw a Hw).
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

Lemma ml_Forall_nth : forall {A : Type} (P : A -> Prop) (l : list A) (n : nat) (x : A),
  Forall P l -> nth_error l n = Some x -> P x.
Proof. intros A P l n x HF Hn. rewrite Forall_forall in HF. apply HF. exact (nth_error_In l n Hn). Qed.

(* The 4 bytes of the chunk number c of region number idx of the state of HS, base rewritten by UB: forall j < 4,
   the view at base + off + j is le_byte v 4 j, for the chunk value e and Hden : sv_denot E e = Z_to_bv 64 v. *)
Ltac ml_chunk HS idx c UB v Hden V :=
  let RG := fresh "RG" in let HC := fresh "HC" in let HC1 := fresh "HCk" in
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict ?Hh ?m) =>
    pose proof (st_ok_pi_region_nth EF _ (restrict Hh m) idx _ HS eq_refl) as RG end;
  cbn [ms_mem restrict] in RG;
  destruct RG as (_ & _ & _ & HC);
  cbn [YP09.r_base YP09.r_chunks base_val] in HC;
  rewrite UB in HC;
  pose proof (ml_Forall_nth _ _ c _ HC eq_refl) as HC1;
  pose proof (ml_chunk_rd _ _ _ _ _ _ v HC1 Hden) as V;
  clear HC HC1.

(* The walk. *)
Lemma ml_holds : @transport_m_lost_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_m_lost_cg_holds_stmt.
intros HCELLS HOW LAWS MTL HGX.
unfold transport_m_lost_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs why Bw Bw'
  HJ Hra Hra4 Hgp Htp H10 Hsp16 Hlo Hhi Htw Hm Hwhy Hev.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MLOST_STK = 16) by reflexivity.
assert (FF : MLOST_FRAME = 16) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (EM : TA_M = 6156640) by reflexivity.
assert (EO : TA_OW = 6238304) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - MLOST_STK) by lia.
assert (Hwin : forall a, spZ regs - MLOST_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transport_segs_low a (proj1 (HGX a Ha)))).
(* the model *)
assert (LB : Z.of_nat (length Bw) = TW.W_LEN)
  by (rewrite (tw_len _ _ _ Htw); rewrite Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]).
pose proof (ml_model Bw why Bw' LB Hm) as HM. clear Hm.
(* the two ints the code loads, as the world holds them *)
pose proof (TWL.u_at_range Bw TW.A_M_state 4) as Rst. pose proof (TWL.u_at_range Bw TW.A_OW_n 4) as Rn.
change (8 * Z.of_nat 4) with 32 in Rst, Rn.
assert (Vst : YI04.val_mem segs (mrestrict (w_H W) memc) (TA_M + 12) 4 (TW.u_at Bw TW.A_M_state 4))
  by exact (tw_read_val segs (mrestrict (w_H W) memc) TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 12 4
    TMAP_A_ok Htw TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
assert (Vn : YI04.val_mem segs (mrestrict (w_H W) memc) (TA_OW + 0) 4 (TW.u_at Bw TW.A_OW_n 4))
  by exact (tw_read_val segs (mrestrict (w_H W) memc) TMAP_A Bw TW.OFF_OW TA_OW TW.SZ_OW 0 4
    TMAP_A_ok Htw TMAP_A_OW ltac:(lia) ltac:(unfold TW.SZ_OW; lia)).
(* the valuation of the walk and its atoms *)
set (E0 := ml_E regs (TW.u_at Bw TW.A_M_state 4) (TW.u_at Bw TW.A_OW_n 4)).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ml_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r Hn; unfold E0, ml_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E33 : ew E0 33 = Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4))
  by (unfold E0, ml_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (TW.u_at Bw TW.A_OW_n 4))
  by (unfold E0, ml_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
destruct ml_vals as (V1 & V93 & V8 & V12 & _).
assert (UM : bv_unsigned (ew E0 (A_OBJ 8)) = TA_M).
{ unfold E0, ml_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V8.
  apply unsigned_lit_small. lia. }
assert (UO : bv_unsigned (ew E0 (A_OBJ 12)) = TA_OW).
{ unfold E0, ml_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V12.
  apply unsigned_lit_small. lia. }
assert (UG : bv_unsigned (ew E0 (A_OBJ 1)) = FCells.GOT_CELL_K).
{ unfold E0, ml_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V1.
  apply unsigned_lit_small. unfold FCells.GOT_CELL_K. lia. }
assert (UC : bv_unsigned (ew E0 (A_OBJ 93)) = FCells.CELL_K).
{ unfold E0, ml_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V93.
  apply unsigned_lit_small. unfold FCells.CELL_K. lia. }
assert (UM' : bv_unsigned (ew E0 249%nat) = TA_M) by exact UM.
assert (UO' : bv_unsigned (ew E0 253%nat) = TA_OW) by exact UO.
assert (UG' : bv_unsigned (ew E0 242%nat) = FCells.GOT_CELL_K) by exact UG.
assert (UC' : bv_unsigned (ew E0 334%nat) = FCells.CELL_K) by exact UC.
(* the values the code loads and stores *)
assert (Dst : sv_denot E0 (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (TW.M_state Bw))
  by exact (ml_sext_den E0 33 _ E33 Rst).
assert (Dn : sv_denot E0 (SExt true 32 (SOff 34 0)) = Z_to_bv 64 (TW.OW_n Bw))
  by exact (ml_sext_den E0 34 _ E34 Rn).
assert (D10 : sv_denot E0 (SOff 10 0) = Z_to_bv 64 why).
{ cbn [sv_denot]. rewrite (EE 10%nat 10%bv eq_refl), H10, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (Dst1 : sv_denot E0 (SOff 33 0) = Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4))
  by (cbn [sv_denot]; rewrite E33, Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (Dn1 : sv_denot E0 (SOff 34 0) = Z_to_bv 64 (TW.u_at Bw TW.A_OW_n 4))
  by (cbn [sv_denot]; rewrite E34, Z.add_0_r; apply Z_to_bv_bv_unsigned).
pose proof (TWL.s32_range Bw TW.A_M_state) as Sst. pose proof (TWL.s32_range Bw TW.A_OW_n) as Sn.
change (TW.s32_at Bw TW.A_M_state) with (TW.M_state Bw) in Sst.
change (TW.s32_at Bw TW.A_OW_n) with (TW.OW_n Bw) in Sn.
destruct (ml_entry lyc Sc W regs memc mdc _ _ HCELLS HOW HAR ltac:(intros a Ha; apply Hpres0; lia) Hsp Hsp16
  Rst Rn Vst Vn) as [HS SHOK].
fold E0 in HS, SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
pose proof (paj_branch (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_lost)) memc (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x00 .. +0x28: the frame, ra saved, the shadow base, M.state, the stores at M + 76 and M + 96; it stops
   at `beqz a7`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ml_awr Usp UM' UO'. }
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody md1. clear mat.
rename ms into ms1.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ ml_W0 (spZ regs) a ->
  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
{ intros a Ha H1. apply (kept_of_frame _ _ _ _ _ (ml_W0 (spZ regs)) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. ml_win Hin Hx ltac:(rewrite ?Usp, ?UM', ?UO' in Hx; unfold ml_W0; lia). }
assert (GA1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* M.state = S_IDLE: m_set returns at once (fuzz_transport.c:198-199) *)
  rewrite Dst in Hc. cbn [branch_taken sv_denot] in Hc. rewrite (ml_eqb0 _ Sst) in Hc. apply Z.eqb_eq in Hc.
  destruct HM as [[_ HB'] | [[Es _] | [Es _]]]; [| exfalso; exact (Es Hc) | exfalso; exact (Es Hc)].
  (* run 2a, +0x28 .. +0xac: the epilogue and `ret` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ml_awr Usp UM' UO'. }
  set (mdF := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody mdF. clear mat.
  rename ms into msF.
  assert (KAT : forall a, 0 <= a < 2 ^ 64 -> ~ ml_W0 (spZ regs) a ->
    aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a).
  { intros a Ha H1. rewrite <- (KA1 a Ha H1).
    apply (kept_of_frame _ _ _ _ _ (ml_W0 (spZ regs)) HFr); [| exact Ha | exact H1].
    intros b wlo whi x Hin Hx. ml_win Hin Hx ltac:(rewrite ?Usp, ?UM', ?UO' in Hx; unfold ml_W0; lia). }
  assert (GAF : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msF) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
  clear HF HFr HG.
  ml_chunk HS 3%nat 0%nat UM' (TW.u_at Bw TW.A_M_state 4) Dst1 VST.
  ml_chunk HS 4%nat 0%nat UM' 0 (@eq_refl _ (Z_to_bv 64 0)) V76.
  ml_chunk HS 5%nat 0%nat UM' 0 (@eq_refl _ (Z_to_bv 64 0)) V96.
  ml_chunk HS 6%nat 0%nat UO' (TW.u_at Bw TW.A_OW_n 4) Dn1 VNN.
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MLOST_STK <= a < spZ regs) -> ~ mlost_wr Bw a ->
    aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a).
  { intros a Ha H1 H2.
    assert (D : ml_W0 (spZ regs) a \/ ~ ml_W0 (spZ regs) a) by (unfold ml_W0; lia).
    destruct D as [D | D]; [|exact (KAT a Ha D)].
    unfold ml_W0 in D. destruct D as [D | [D | [D | [D | D]]]].
    - exfalso. apply H1. rewrite FS. exact D.
    - destruct (ml_in4 (TA_M + 12) a D) as (j & Hj & ->).
      pose proof (tw_read TMAP_A _ Bw TW.OFF_M TA_M TW.SZ_M 12 4 j TMAP_A_ok Htw TMAP_A_M ltac:(lia)
        ltac:(unfold TW.SZ_M; lia) Hj) as ER.
      exact (eq_trans (VST j Hj) (eq_sym ER)).
    - exfalso. apply H2. left. unfold twa_fld, TW.A_M_desk_counter_valid. lia.
    - exfalso. apply H2. right. left. unfold twa_fld, TW.A_M_fly_on. lia.
    - destruct (ml_in4 (TA_OW + 0) a ltac:(lia)) as (j & Hj & ->).
      pose proof (tw_read TMAP_A _ Bw TW.OFF_OW TA_OW TW.SZ_OW 0 4 j TMAP_A_ok Htw TMAP_A_OW ltac:(lia)
        ltac:(unfold TW.SZ_OW; lia) Hj) as ER.
      exact (eq_trans (VNN j Hj) (eq_sym ER)). }
  assert (HWF : tw_at TMAP_A (aview segs (w_H W) (ms_mem msF)) Bw').
  { rewrite HB'. apply (ml_world1 Bw (aview segs (w_H W) memc) _ Htw V96 V76).
    intros x Hx N1 N2. pose proof (GLOW x (ml_tw_in_G x Hx)) as Hl. unfold kLowMemEnd in Hl.
    apply KAF; [lia | rewrite FS; lia |].
    unfold mlost_wr, mset_wr, twa_fld, TW.A_M_desk_counter_valid, TW.A_M_fly_on.
    intros [Hw | [Hw | [Hw _]]]; [lia | lia | exact (Hw Hc)]. }
  ml_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs msF)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ msF regs
      [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4); Z_to_bv 64 (TW.u_at Bw TW.A_OW_n 4)] HS).
    - apply ml_agree.
    - vm_compute. reflexivity. }
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  exact (ml_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' (ms_regs msF) (ms_mem msF) mdF
    LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAF HWF HPF RF1 mat').
- (* M.state <> S_IDLE: m_set *)
  rewrite Dst in Hc. cbn [branch_taken sv_denot] in Hc. rewrite (ml_eqb0 _ Sst) in Hc. apply Z.eqb_neq in Hc.
  rename Hc into Hst.
  (* run 2b, +0x28 .. +0x3c: &OW, OW.n, a1 = 15; it stops at `blt a1, a5` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ml_awr Usp UM' UO'. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  rename ms into ms2.
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ ml_W0 (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) memc a).
  { intros a Ha H1. rewrite <- (KA1 a Ha H1).
    apply (kept_of_frame _ _ _ _ _ (ml_W0 (spZ regs)) HFr); [| exact Ha | exact H1].
    intros b wlo whi x Hin Hx. ml_win Hin Hx ltac:(rewrite ?Usp, ?UM', ?UO' in Hx; unfold ml_W0; lia). }
  assert (GA2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
  clear HF HFr HG KA1 GA1.
  clear dependent ms1.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* 15 < OW.n: the log is full (:200) *)
    rewrite Dn in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (ml_lts 15 (TW.OW_n Bw) ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_lt in Hc.
    destruct HM as [[Es _] | [[_ (Hn1 & Hn2 & HB')] | [_ (Hn & _)]]];
      [exfalso; exact (Hst Es) | | exfalso; unfold TCB.TRANS_MAX in Hn; lia].
    (* run 3a, +0x3c .. +0xac: OW.n + 1, M.state = 0, the epilogue and `ret` *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { ml_awr Usp UM' UO'. }
    set (mdF := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdF. clear mat.
    rename ms into msF.
    assert (KAT : forall a, 0 <= a < 2 ^ 64 -> ~ ml_W0 (spZ regs) a ->
      aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a).
    { intros a Ha H1. rewrite <- (KA2 a Ha H1).
      apply (kept_of_frame _ _ _ _ _ (ml_W0 (spZ regs)) HFr); [| exact Ha | exact H1].
      intros b wlo whi x Hin Hx. ml_win Hin Hx ltac:(rewrite ?Usp, ?UM', ?UO' in Hx; unfold ml_W0; lia). }
    assert (GAF : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msF) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
    clear HF HFr HG.
    assert (DN1 : sv_denot E0 (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1)) = Z_to_bv 64 (TW.OW_n Bw + 1)).
    { change (sv_denot E0 (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1)))
        with (alu64 ALU_ADD (sv_denot E0 (SExt true 32 (SOff 34 0))) (sv_denot E0 (SLit 1))).
      rewrite Dn. exact (ml_add_den (TW.OW_n Bw) 1). }
    ml_chunk HS 3%nat 0%nat UM' TCB.S_IDLE (@eq_refl _ (Z_to_bv 64 0)) VS.
    ml_chunk HS 4%nat 0%nat UM' 0 (@eq_refl _ (Z_to_bv 64 0)) V76.
    ml_chunk HS 5%nat 0%nat UM' 0 (@eq_refl _ (Z_to_bv 64 0)) V96.
    ml_chunk HS 6%nat 0%nat UO' (TW.OW_n Bw + 1) DN1 VN.
    assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MLOST_STK <= a < spZ regs) -> ~ mlost_wr Bw a ->
      aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a).
    { intros a Ha H1 H2. apply KAT; [exact Ha|]. intros HW. apply H2.
      unfold ml_W0 in HW. unfold mlost_wr, mset_wr, twa_fld, TW.A_M_desk_counter_valid, TW.A_M_fly_on,
        TW.A_M_state, TW.A_OW_n, TW.A_OW_t_state, TW.OW_t_ESZ.
      unfold TCB.S_IDLE, TCB.TRANS_MAX in *. rewrite FS in H1. lia. }
    assert (HWF : tw_at TMAP_A (aview segs (w_H W) (ms_mem msF)) Bw').
    { rewrite HB'. apply (ml_world2 Bw (aview segs (w_H W) memc) _ (TW.OW_n Bw) Htw V96 V76 VN VS).
      intros x Hx N1 N2 N3 N4. pose proof (GLOW x (ml_tw_in_G x Hx)) as Hl. unfold kLowMemEnd in Hl.
      apply KAF; [lia | rewrite FS; lia |].
      unfold mlost_wr, mset_wr, twa_fld, TW.A_M_desk_counter_valid, TW.A_M_fly_on, TW.A_M_state, TW.A_OW_n,
        TW.A_OW_t_state, TW.OW_t_ESZ.
      unfold TCB.TRANS_MAX in *. lia. }
    ml_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
      ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (HPF : aregs_preserved regs (ms_regs msF)).
    { apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ msF regs
        [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4); Z_to_bv 64 (TW.u_at Bw TW.A_OW_n 4)] HS).
      - apply ml_agree.
      - vm_compute. reflexivity. }
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    exact (ml_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' (ms_regs msF) (ms_mem msF) mdF
      LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAF HWF HPF RF1 mat').
  + (* OW.n <= 15: OW.t[OW.n] = {S_IDLE, old state, why} (:200-203) *)
    rewrite Dn in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (ml_lts 15 (TW.OW_n Bw) ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_ge in Hc.
    destruct HM as [[Es _] | [[_ (Hn1 & _)] | [_ (Hn & HB')]]];
      [exfalso; exact (Hst Es) | exfalso; unfold TCB.TRANS_MAX in Hn1; lia |].
    assert (Hcase : TW.OW_n Bw = 0 \/ TW.OW_n Bw = 1 \/ TW.OW_n Bw = 2 \/ TW.OW_n Bw = 3 \/
      TW.OW_n Bw = 4 \/ TW.OW_n Bw = 5 \/ TW.OW_n Bw = 6 \/ TW.OW_n Bw = 7 \/
      TW.OW_n Bw = 8 \/ TW.OW_n Bw = 9 \/ TW.OW_n Bw = 10 \/ TW.OW_n Bw = 11 \/
      TW.OW_n Bw = 12 \/ TW.OW_n Bw = 13 \/ TW.OW_n Bw = 14 \/ TW.OW_n Bw = 15)
      by (unfold TCB.TRANS_MAX in Hn; lia).
    destruct Hcase as [Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|Hi]]]]]]]]]]]]]]].
    (* in each case OW.n = i (a literal): a5 = i, pinned *)
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      ml_reg HS (Z_to_bv 5 15) (Z_to_bv 64 i) Q15 ltac:(rewrite Dn, Hi; reflexivity) end.
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
        pose proof (st_ok_pi_pin_reg' Ex ss (restrict Hh m) (Z_to_bv 5 15) i HS Q15 eq_refl) as HSp end end.
    all: clear HS Q15.
    all: lazymatch type of HSp with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
      let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HSp end.
    (* the 12 bytes of OW.t[i] join the state, a writable region of G *)
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      lazymatch type of HSp with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
        pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) (ml_tr_region i) HSp eq_refl
          (ml_tr_ok Ex _ i UO ltac:(lia)) ltac:(cbn [ss_mem YP09.all_disjoint];
            unfold YP09.extent_disjoint, ml_tr_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
            rewrite ?Usp, ?UM', ?UO', ?UG', ?UC', ?UO;
            unfold FCells.GOT_CELL_K, FCells.CELL_K; repeat split; lia)) as HS end end.
    all: clear HSp.
    all: lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
      let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.
    (* run 3b, +0x3c .. +0xac: p = OW + 4 + 12 * i, the three checked stores (each check decided by ML_SH), OW.n + 1,
       M.state = 0, the epilogue and `ret` *)
    all: paj_run_tok RUN HS HJ SHOK YC4b.Bspan; [ml_awr Usp UM' UO' |].
    all: set (mdF := with_vm_backing (m_vm_lazy md2) mat md2) in *; clearbody mdF; clear mat; rename ms into msF.
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ ml_W3 (spZ regs) i a ->
        aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) (ms_mem ms2) a)
      by (intros a Ha H1; apply (kept_of_frame _ _ _ _ _ (ml_W3 (spZ regs) i) HFr); [| exact Ha | exact H1];
          intros b wlo whi x Hin Hx; ml_win Hin Hx ltac:(rewrite ?Usp, ?UM', ?UO' in Hx; unfold ml_W3, ml_W0; lia))
      end.
    all: assert (GAF : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msF) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
    all: clear HF HFr HG.
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MLOST_STK <= a < spZ regs) -> ~ mlost_wr Bw a ->
        aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a)
      by (intros a Ha H1 H2;
          assert (NW : ~ ml_W3 (spZ regs) i a)
          by (intros HW; apply H2; unfold ml_W3, ml_W0 in HW;
              unfold mlost_wr, mset_wr, twa_fld, TW.A_M_desk_counter_valid, TW.A_M_fly_on,
                TW.A_M_state, TW.A_OW_n, TW.A_OW_t_state, TW.OW_t_ESZ;
              unfold TCB.S_IDLE, TCB.TRANS_MAX in *; rewrite FS in H1; lia);
          rewrite (KR3 a Ha NW); apply KA2; [exact Ha | intros HW; apply NW; left; exact HW])
      end.
    (* the bytes the code stored, read from the last state's chunks *)
    all: ml_chunk HS 6%nat 0%nat UM' 0 (@eq_refl _ (Z_to_bv 64 0)) V96.
    all: ml_chunk HS 5%nat 0%nat UM' 0 (@eq_refl _ (Z_to_bv 64 0)) V76.
    all: ml_chunk HS 0%nat 2%nat UO' TCB.S_IDLE (@eq_refl _ (Z_to_bv 64 0)) VTS.
    all: ml_chunk HS 0%nat 1%nat UO' (TW.M_state Bw) Dst VTO.
    all: ml_chunk HS 0%nat 0%nat UO' why D10 VTR.
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      assert (DNi : sv_denot E0 (SLit (i + 1)) = Z_to_bv 64 (TW.OW_n Bw + 1)) by (cbn [sv_denot]; rewrite Hi; reflexivity)
      end.
    all: ml_chunk HS 7%nat 0%nat UO' (TW.OW_n Bw + 1) DNi VN.
    all: ml_chunk HS 4%nat 0%nat UM' TCB.S_IDLE (@eq_refl _ (Z_to_bv 64 0)) VS.
    all: lazymatch goal with Hi : TW.OW_n _ = ?i |- _ =>
      assert (HWF : tw_at TMAP_A (aview segs (w_H W) (ms_mem msF)) Bw')
      by (rewrite HB'; apply (ml_world3 Bw (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem msF))
            (TW.OW_n Bw) (TW.M_state Bw) why Htw ltac:(unfold TCB.TRANS_MAX in Hn; lia) V96 V76);
          [ intros j Hj; rewrite Hi; exact (VTS j Hj)
          | intros j Hj; rewrite Hi; exact (VTO j Hj)
          | intros j Hj; rewrite Hi; exact (VTR j Hj)
          | exact VN
          | exact VS
          | intros x Hx N1 N2 N3 N4 N5; pose proof (GLOW x (ml_tw_in_G x Hx)) as Hl; unfold kLowMemEnd in Hl;
            apply KAF; [lia | rewrite FS; lia |];
            unfold mlost_wr, mset_wr, twa_fld, TW.A_M_desk_counter_valid, TW.A_M_fly_on, TW.A_M_state, TW.A_OW_n,
              TW.A_OW_t_state, TW.OW_t_ESZ; lia ])
      end.
    (* the return *)
    all: ml_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
      ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    all: assert (HPF : aregs_preserved regs (ms_regs msF))
      by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ msF regs
            [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4); Z_to_bv 64 (TW.u_at Bw TW.A_OW_n 4)] HS);
          [apply ml_agree | vm_compute; reflexivity]).
    all: eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    all: let mat' := fresh "mat" in intros mat';
      exact (ml_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' (ms_regs msF) (ms_mem msF) mdF
        LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAF HWF HPF RF1 mat').
Qed.

End mlw.

(* The statement of lib/A/Prog/m_lost_cg.v. *)
Theorem transport_m_lost_cg_holds : forall fx rc B MT, @transport_m_lost_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ml_holds fx rc B MT). Qed.

Print Assumptions transport_m_lost_cg_holds.
