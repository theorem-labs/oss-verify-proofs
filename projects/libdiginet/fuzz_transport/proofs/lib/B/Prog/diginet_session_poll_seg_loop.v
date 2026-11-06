(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 658 of its 726 lines of code are new or changed and 697 lines of the source are left out. *)
(* diginet_session_poll_seg_loop: Theorem pw_loop_piece : pw_loop_stmt (lib/B/Prog/diginet_session_poll_segs.v),
   the drain piece: from the cut loop (+0x2a4, 0x8ad3c) with fuel: io.ctx and io.recv loaded, the recv's
   arguments, `jalr a4` (+0x2b8; io_recv, diginet_session_poll_seg_grecv.v pw_recv_call); r <= 0 to the cut rel with
   s10 = r; else the checks of s + 88 (through the slot s1 + 24) and s + 64, `jalr a1` (+0x2e4; io_now,
   diginet_session_poll_seg_leaf.v pw_now_call), `jal diginet_session_rx` (+0x2f8; diginet_session_poll_seg_grx.v
   pw_rx_call), the checks of s + 80 and s + 64, back to the cut loop with one less fuel.
   The file also holds what the first-recv piece (diginet_session_poll_seg_recv1.v) shares with it: the symbolic
   state both pieces run from at any pc (pw_entry: the slot s1 + 24, the shadow bytes of [s + 64, s + 96) and g_s's
   three io words, read-only; the image addresses in s3, s5 .. s8, s11 as literals), that a run of either piece
   stores no byte (pw_run_kept), io_recv's copy carried to a later memory (pw_garr_move), and the cut registers
   kept across a callee (pw_rg_buf_pres, pw_rg_buf_call). Each run reads the shadow byte of a check through a
   register that holds its address, so the token mechanism of PaShadow.v is not used. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require io_now_cg diginet_session_deadline_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TRunInv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_seg_rt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  diginet_session_poll_seg_leaf diginet_session_poll_seg_grecv diginet_session_poll_seg_grx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TPoll TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TPL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TPoll.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module TRI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRunInv.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states the drain and the first recv run from           *)
(* ------------------------------------------------------------------ *)

(* The run's span and shadow base: this walk reads each shadow byte through a register that holds its address, so
   the token mechanism is not used (no shadow entry, an empty span). *)
Definition PW_B0 : Z * Z := (0, 0).
Definition PW_Bx : sv := SLit 0.

(* The three regions every run of the drain and of the first recv reads:
   - the slot s1 + 24, which holds the shadow address of s + 88 (pw_run);
   - the four shadow bytes of [s + 64, s + 96), all 0 (trans_poll_cells);
   - g_s's three io words at s + 64 (ctx), s + 80 (recv) and s + 88 (now_us), as the world's bytes (atoms 32 .. 34).
   No region is writable: neither piece stores a byte. *)
Definition PW_R_slot : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (YP09.CVal 8 (SLit PW_SH88))].
Definition PW_R_sh : YP09.region :=
  YP09.mkRegion None PW_SH64 (PW_SH64 + 4) 0 0 [YP09.mkChunk PW_SH64 (YP09.CZero 4)].
Definition PW_R_gs : YP09.region :=
  YP09.mkRegion None (POLL_S + 64) (POLL_S + 96) 0 0
    [YP09.mkChunk (POLL_S + 64) (YP09.CVal 8 (SOff 32 0));
     YP09.mkChunk (POLL_S + 80) (YP09.CVal 8 (SOff 33 0));
     YP09.mkChunk (POLL_S + 88) (YP09.CVal 8 (SOff 34 0))].
Definition PW_RGS : smem := [PW_R_slot; PW_R_sh; PW_R_gs].
Definition PW_FACTS : facts := mkFacts [] [] [].
(* The registers whose value is an address of the image: s3 = s, s5 and s11 the shadow addresses of s + 64 and
   s + 80, s6, s7, s8 the three fields' addresses. The others are atoms. *)
Definition PW_REGS : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    (Z_to_bv 5 19) (SLit POLL_S)) (Z_to_bv 5 21) (SLit PW_SH64)) (Z_to_bv 5 22) (SLit (POLL_S + 80)))
    (Z_to_bv 5 23) (SLit (POLL_S + 88))) (Z_to_bv 5 24) (SLit (POLL_S + 64))) (Z_to_bv 5 27) (SLit PW_SH80).
Definition PW_SS (pc : Z) : sstate := mkSS pc PW_REGS PW_RGS None PW_FACTS.

Section e. Context {rc : YM05.RunCeil}.
(* The valuation: the 32 registers, then the three io words of the world at the state. *)
Definition pw_vals (Bx : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 64) 8);
   Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 80) 8);
   Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 88) 8)].
Definition pw_E (regs : bvmap 5 word) (Bx : list byte) : env := Eimg (PI := PI_transportb) (Ereg regs (pw_vals Bx)).

(* The three shadow addresses and g_s's base as numerals (lia does not see into the shadow address's division). *)
Lemma pw_sh64 : PW_SH64 = 2148220624.
Proof. reflexivity. Qed.
Lemma pw_sh80 : PW_SH80 = 2148220626.
Proof. reflexivity. Qed.
Lemma pw_sh88 : PW_SH88 = 2148220627.
Proof. reflexivity. Qed.
Lemma pw_s_val : POLL_S = 6157888.
Proof. reflexivity. Qed.

(* The two io pointers at their numeral offsets of the world: the walk names them by the offset from here on. *)
Lemma pw_fld_recv : forall Bx, TW.S_io_recv Bx = TW.u_at Bx (TW.OFF_g_s + 80) 8.
Proof. reflexivity. Qed.
Lemma pw_fld_now : forall Bx, TW.S_io_now_us Bx = TW.u_at Bx (TW.OFF_g_s + 88) 8.
Proof. reflexivity. Qed.
(* io_now's result, the 8 bytes of g_now, is a 64-bit unsigned value. *)
Lemma pw_now_range : forall Bx, 0 <= TC.io_now_m Bx < 2 ^ 64.
Proof.
  intros Bx. pose proof (TWL.u_at_range Bx TW.OFF_g_now 8) as R.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R. exact R.
Qed.

(* The valuation's registers and its three extra atoms. *)
Lemma pw_ew_reg : forall regs Bx n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (pw_E regs Bx) n = YK11.getr regs r.
Proof. intros regs Bx n r Hn. unfold pw_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma pw_ew_ctx : forall regs Bx, ew (pw_E regs Bx) 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 64) 8).
Proof.
  intros regs Bx. unfold pw_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs (pw_vals Bx) 0).
Qed.
Lemma pw_ew_recv : forall regs Bx, ew (pw_E regs Bx) 33 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 80) 8).
Proof.
  intros regs Bx. unfold pw_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs (pw_vals Bx) 1).
Qed.
Lemma pw_ew_now : forall regs Bx, ew (pw_E regs Bx) 34 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 88) 8).
Proof.
  intros regs Bx. unfold pw_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs (pw_vals Bx) 2).
Qed.
Lemma pw_env_img : forall regs Bx, img_env (@pa_val _ transportb_listing PI_transportb) A_LIM (pw_E regs Bx).
Proof. intros regs Bx. unfold pw_E. apply Eimg_env. Qed.
End e.

(* A byte whose view is 0. *)
Lemma pw_mbyte0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview tfibsegs H m a = Some 0 -> YP09.mbyte tfibsegs (mrestrict H m) a = Some (Z_to_bv 8 0).
Proof.
  intros H m a Hv. unfold aview in Hv.
  destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Hv].
  cbn [option_map] in Hv. injection Hv as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* A chunk of zero bytes at an absolute address. *)
Lemma pw_chunk_zero : forall (E : env) (H : word -> bool) (m : word -> option byte) (off len : Z),
  (forall i, 0 <= i < len -> aview tfibsegs H m (off + i) = Some 0) ->
  YP09.chunk_ok tfibsegs E (mrestrict H m) 0 (YP09.mkChunk off (YP09.CZero len)).
Proof.
  intros E H m off len Hz i Hi.
  cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len YP09.cbyte] in *.
  exists (Z_to_bv 8 0). split; [reflexivity |].
  replace (0 + off + i) with (off + i) by lia. apply pw_mbyte0. exact (Hz i Hi).
Qed.

(* A branch on a signed 64-bit value and on equality with 0. *)
Lemma pw_lts : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !Z_to_bv_signed.
  assert (HM : bv_half_modulus 64 = 2 ^ 63) by reflexivity.
  rewrite !bv_swrap_small by (rewrite HM; lia). reflexivity.
Qed.
Lemma pw_eqb : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.eqb_spec a b) as [->|N]; [apply Z.eqb_refl |].
  apply Z.eqb_neq. intros E. apply N.
  assert (D : (a - b) mod 2 ^ 64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in D; [|lia]. destruct D as [q Eq]. nia.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac pw_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "pw_reg: no match for" T; fail
  end.

(* The write rights of a run from the three regions: none of them is writable. *)
Ltac pw_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS_B.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The four shadow bytes of [s + 64, s + 96) are 0: whole granules of g_s's payload (trans_poll_cells). *)
Lemma pw_shadow_zero : forall ly S (W : world segs) mem md,
  trans_poll_cells B -> @AR rc segs B ly S W mem md ->
  forall i, 0 <= i < 4 -> aview segs (w_H W) mem (PW_SH64 + i) = Some 0.
Proof.
  intros ly S W mem md HSC HAR i Hi.
  replace (PW_SH64 + i) with (BCells.shadow_addr (POLL_S + 64 + 8 * i)).
  - apply (decode_zshadow_rd B ly S W mem md POLL_S (POLL_S + TW.SZ_g_s) _ HAR); [| | | exact HSC].
    + rewrite pw_s_val. replace (6157888 + 64 + 8 * i) with ((769744 + i) * 8) by lia. apply Z.mod_mul. lia.
    + rewrite pw_s_val. lia.
    + rewrite pw_s_val. unfold TW.SZ_g_s. lia.
  - unfold BCells.shadow_addr, BCells.ASAN_K. rewrite pw_sh64, pw_s_val.
    replace (6157888 + 64 + 8 * i) with ((769744 + i) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

(* The symbolic state at any pc of the drain or of the first recv, from the facts every cut carries. *)
Lemma pw_entry : forall c pos ly2 S2 (W2 : world segs) mem2 md2 Bx (regs : bvmap 5 word) (pc : Z),
  pw_rt B MT -> pw_ok B c -> pw_run B MT c pos ly2 S2 W2 mem2 md2 Bx -> pw_rg_run B c pos regs ->
  st_ok_pi segs VAL (pw_E regs Bx) (PW_SS pc)
    (restrict (w_H W2) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem2 (YK11.seg_rom segs))).
Proof.
intros c pos ly2 S2 W2 mem2 md2 Bx regs pc RT OK HRUN HRG.
pose proof RT as (_ & _ & HSC & _).
pose proof (pw_ok_sp B MT c OK) as (_ & HSPR & _ & _ & _ & HSP1R & _).
pose proof HRUN as (HCUR & _ & _ & HSLOT).
pose proof HCUR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTW & _).
pose proof (pw_cur_frame B MT c pos ly2 S2 W2 mem2 md2 Bx RT OK HCUR) as (HAR2 & _).
pose proof HRG as ((R2 & R3 & R4 & R8 & R9 & R18) & R19 & R20 & R21 & R22 & R23 & R24 & R27).
rewrite restrict_mkst_fx.
set (E := pw_E regs Bx).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E; apply pw_ew_reg; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = pw_sp1 c)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
  by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 64) 8) as RG64.
pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 80) 8) as RG80.
pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 88) 8) as RG88.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RG64, RG80, RG88.
pose proof (pw_shadow_zero ly2 S2 W2 mem2 md2 HSC HAR2) as ZSH.
assert (H0 : st_ok_pi segs VAL E (mkSS pc sr_atoms PW_RGS None PW_FACTS)
  (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W2) mem2) (YK11.seg_rom segs))).
{ apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - unfold E, pw_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold PW_RGS. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, PW_R_slot, PW_R_sh, PW_R_gs;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [| apply Forall_nil].
      apply (chunk_ok_val segs E _ (pw_sp1 c) 24 8 (SLit PW_SH88) PW_SH88);
        [reflexivity | rewrite pw_sh88; lia | lia |].
      exact (val_mem_of_rdword segs (w_H W2) mem2 _ _ HSLOT).
    + split; [rewrite pw_sh64; lia|]. split; [rewrite pw_sh64; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [| apply Forall_nil].
      apply pw_chunk_zero. exact ZSH.
    + split; [rewrite pw_s_val; lia|]. split; [rewrite pw_s_val; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 (POLL_S + 64) 8 (SOff 32 0) (TW.u_at Bx (TW.OFF_g_s + 64) 8));
          [apply DEN; [unfold E; apply pw_ew_ctx | exact RG64] | exact RG64 | lia |].
        replace (0 + (POLL_S + 64)) with (TB_g_s + 64) by (unfold POLL_S; lia).
        exact (tw_read_val segs _ TMAP_B Bx TW.OFF_g_s TB_g_s TW.SZ_g_s 64 8 TMAP_B_ok HTW TMAP_B_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (POLL_S + 80) 8 (SOff 33 0) (TW.u_at Bx (TW.OFF_g_s + 80) 8));
          [apply DEN; [unfold E; apply pw_ew_recv | exact RG80] | exact RG80 | lia |].
        replace (0 + (POLL_S + 80)) with (TB_g_s + 80) by (unfold POLL_S; lia).
        exact (tw_read_val segs _ TMAP_B Bx TW.OFF_g_s TB_g_s TW.SZ_g_s 80 8 TMAP_B_ok HTW TMAP_B_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (POLL_S + 88) 8 (SOff 34 0) (TW.u_at Bx (TW.OFF_g_s + 88) 8));
          [apply DEN; [unfold E; apply pw_ew_now | exact RG88] | exact RG88 | lia |].
        replace (0 + (POLL_S + 88)) with (TB_g_s + 88) by (unfold POLL_S; lia).
        exact (tw_read_val segs _ TMAP_B Bx TW.OFF_g_s TB_g_s TW.SZ_g_s 88 8 TMAP_B_ok HTW TMAP_B_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  - apply pairwise_disjoint_of_extents.
    unfold PW_RGS, PW_R_slot, PW_R_sh, PW_R_gs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite ?pw_sh64, ?pw_s_val. repeat split; first [exact I | lia].
  - unfold PW_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 19) POLL_S H0 R19 eq_refl) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 21) PW_SH64 H1 R21 eq_refl) as H2.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 22) (POLL_S + 80) H2 R22 eq_refl) as H3.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 23) (POLL_S + 88) H3 R23 eq_refl) as H4.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) (POLL_S + 64) H4 R24 eq_refl) as H5.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 27) PW_SH80 H5 R27 eq_refl) as H6.
exact H6.
Qed.

(* A run of this piece writes no byte: every byte's view is the one it was given. *)
Lemma pw_run_kept : forall (E : env) (H : word -> bool) (m m' : word -> option byte),
  frame_of E PW_RGS (mrestrict H m) (mrestrict H m') ->
  forall a, aview segs H m' a = aview segs H m a.
Proof.
intros E H m m' HF a.
rewrite (aview_wrap64 segs H m' a), (aview_wrap64 segs H m a).
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hb.
apply (kept_of_frame E PW_RGS H m m' (fun _ => False) HF); [| lia | tauto].
intros b wlo whi x Hin Hx.
lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]).
destruct Hin.
Qed.

(* io_recv's copy at buf, read at a later memory whose view agrees on it. *)
Lemma pw_garr_move : forall (H : word -> bool) (m m' : word -> option byte) a l,
  garr8 segs (mrestrict H m) a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> aview segs H m' x = aview segs H m x) ->
  garr8 segs (mrestrict H m') a l.
Proof.
intros H m m' a l HG HK.
apply (garr8_frame segs (mrestrict H m) (mrestrict H m') a l HG).
intros x Hx. apply (mbyte_of_aview segs H H m m' x). exact (HK x Hx).
Qed.

(* The registers the cuts name are callee-saved, so a callee keeps them ... *)
Lemma pw_rg_buf_pres : forall c pos (regs regs' : bvmap 5 word),
  pw_rg_buf B c pos regs -> aregs_preserved regs regs' -> pw_rg_buf B c pos regs'.
Proof.
intros c pos regs regs' HR HP.
pose proof HR as (((R2 & R3 & R4 & R8 & R9 & R18) & R19 & R20 & R21 & R22 & R23 & R24 & R27) & R25).
unfold pw_rg_buf, pw_rg_run, pw_rg_base.
repeat apply conj;
  [ exact (eq_trans (HP 2 ltac:(hnf; lia)) R2) | exact (eq_trans (HP 3 ltac:(hnf; lia)) R3)
  | exact (eq_trans (HP 4 ltac:(hnf; lia)) R4) | exact (eq_trans (HP 8 ltac:(hnf; lia)) R8)
  | exact (eq_trans (HP 9 ltac:(hnf; lia)) R9) | exact (eq_trans (HP 18 ltac:(hnf; lia)) R18)
  | exact (eq_trans (HP 19 ltac:(hnf; lia)) R19) | exact (eq_trans (HP 20 ltac:(hnf; lia)) R20)
  | exact (eq_trans (HP 21 ltac:(hnf; lia)) R21) | exact (eq_trans (HP 22 ltac:(hnf; lia)) R22)
  | exact (eq_trans (HP 23 ltac:(hnf; lia)) R23) | exact (eq_trans (HP 24 ltac:(hnf; lia)) R24)
  | exact (eq_trans (HP 27 ltac:(hnf; lia)) R27) | exact (eq_trans (HP 25 ltac:(hnf; lia)) R25) ].
Qed.

(* ... and the link register of a jalr is the only one its step writes. *)
Lemma pw_rg_buf_call : forall c pos (regs regs' : bvmap 5 word),
  pw_rg_buf B c pos regs -> (forall r : bv 5, bv_unsigned r <> 1 -> YK11.getr regs' r = YK11.getr regs r) ->
  pw_rg_buf B c pos regs'.
Proof.
intros c pos regs regs' HR HP.
pose proof HR as (((R2 & R3 & R4 & R8 & R9 & R18) & R19 & R20 & R21 & R22 & R23 & R24 & R27) & R25).
unfold pw_rg_buf, pw_rg_run, pw_rg_base.
repeat apply conj;
  [ exact (eq_trans (HP 2%bv ltac:(vm_compute; discriminate)) R2)
  | exact (eq_trans (HP 3%bv ltac:(vm_compute; discriminate)) R3)
  | exact (eq_trans (HP 4%bv ltac:(vm_compute; discriminate)) R4)
  | exact (eq_trans (HP 8%bv ltac:(vm_compute; discriminate)) R8)
  | exact (eq_trans (HP 9%bv ltac:(vm_compute; discriminate)) R9)
  | exact (eq_trans (HP 18%bv ltac:(vm_compute; discriminate)) R18)
  | exact (eq_trans (HP 19%bv ltac:(vm_compute; discriminate)) R19)
  | exact (eq_trans (HP 20%bv ltac:(vm_compute; discriminate)) R20)
  | exact (eq_trans (HP 21%bv ltac:(vm_compute; discriminate)) R21)
  | exact (eq_trans (HP 22%bv ltac:(vm_compute; discriminate)) R22)
  | exact (eq_trans (HP 23%bv ltac:(vm_compute; discriminate)) R23)
  | exact (eq_trans (HP 24%bv ltac:(vm_compute; discriminate)) R24)
  | exact (eq_trans (HP 27%bv ltac:(vm_compute; discriminate)) R27)
  | exact (eq_trans (HP 25%bv ltac:(vm_compute; discriminate)) R25) ].
Qed.

Lemma pw_loop_holds : @pw_loop_stmt fx rc B MT.
Proof using All.
unfold pw_loop_stmt. intros c REL fuel IH RT KEEP OK pos ly2 S2 W2 mem2 md2 regs2 Bx HRUN HRG HMD HDRX.
pose proof RT as (HSM & HCELLS & HSC & HGU & HGNE & HROU & HRNE & LAWS & MTL & MTF & SMP & FFL & HGX & HGE &
  ASM & ASF8 & ASF0 & LIN & LSD & HRECVC & HRXC & HTICKC & HFREE).
pose proof (pw_drain_step timg_B (cx_TF c) Bx fuel (cx_Bw' c) (cx_r c) HMD) as (HIORECV & B1 & r1 & got & HM1 & HCASE).
pose proof (pw_ok_sp B MT c OK) as (HARc & HSPR & HCEIL & HPRES & HM32 & HSP1R & HSP0M & HSTKLE & HSPLE & HSTKEQ &
  HESIO & HIOSRX & HTKSRX).
pose proof (pw_recv_ret timg_B (cx_TF c) Bx B1 r1 got HM1) as (HR1R & HR1LEN).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* the loop head +0x2a4 .. +0x2b4: io.ctx, io.recv and the recv's arguments, up to `jalr a4` *)
pose proof (pw_entry c pos ly2 S2 W2 mem2 md2 Bx regs2 PW_LOOP RT OK HRUN (proj1 HRG)) as HS.
set (E0 := pw_E regs2 Bx) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply pw_env_img).
assert (SHOK : sh_ok segs PW_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (proj1 (proj1 HRUN)) as HJ.
paj_run_tok RUN HS HJ SHOK PW_B0.
{ pw_awr. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KD1 : forall a, aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a)
  by (intros a; exact (pw_run_kept E0 (w_H W2) mem2 (ms_mem ms) HFr a)).
assert (GR1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (HRUN1 : pw_run B MT c pos ly2 S2 W2 (ms_mem ms) md1 Bx)
  by (apply (pw_run_win B MT c pos ly2 S2 W2 mem2 md2 Bx (ms_mem ms) md1 RT OK HRUN HJ);
      [intros a _ _; exact (KD1 a) | exact GR1]).
(* +0x2b8: `jalr a4` through the recv pointer, at the image's io_recv (the model's call_recv tested it) *)
assert (EIOR : TI.ti_io_recv timg_B = 0x83368) by reflexivity.
assert (EION : TI.ti_io_now timg_B = 0x83410) by reflexivity.
assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0; apply pw_ew_reg; exact Hn).
assert (EV33 : ew E0 33 = Z_to_bv 64 (TI.ti_io_recv timg_B))
  by (unfold E0; rewrite pw_ew_recv, <- pw_fld_recv, HIORECV; reflexivity).
pose proof HRG as (HRGR & HRG25).
pose proof HRGR as ((R2 & R3 & R4 & R8 & R9 & R18) & R19 & R20 & R21 & R22 & R23 & R24 & R27).
pw_reg HS (Z_to_bv 5 2) (w64 (pw_sp1 c)) Q2
  ltac:(cbn [sv_denot]; rewrite (EE0 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
pw_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE0 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R3).
pw_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE0 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R4).
pw_reg HS (Z_to_bv 5 11) (w64 (pw_F c pos + 32)) Q11
  ltac:(cbn [sv_denot]; rewrite (EE0 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact HRG25).
pw_reg HS (Z_to_bv 5 12) (w64 TS0.DIGINET_MAX_FRAME_LEN) Q12 ltac:(reflexivity).
pw_reg HS (Z_to_bv 5 14) (Z_to_bv 64 (TI.ti_io_recv timg_B)) Q14
  ltac:(cbn [sv_denot]; rewrite EV33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
pw_reg HS (Z_to_bv 5 8) (w64 (pw_SP c)) Q8
  ltac:(cbn [sv_denot]; rewrite (EE0 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R8).
pw_reg HS (Z_to_bv 5 9) (w64 (pw_sp1 c)) Q9
  ltac:(cbn [sv_denot]; rewrite (EE0 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R9).
pw_reg HS (Z_to_bv 5 18) (w64 (pw_F c pos)) Q18
  ltac:(cbn [sv_denot]; rewrite (EE0 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R18).
pw_reg HS (Z_to_bv 5 19) (w64 POLL_S) Q19 ltac:(reflexivity).
pw_reg HS (Z_to_bv 5 20) (w64 (SHADOW_OFF + pw_F c pos / 8)) Q20
  ltac:(cbn [sv_denot]; rewrite (EE0 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20).
pw_reg HS (Z_to_bv 5 21) (w64 PW_SH64) Q21 ltac:(reflexivity).
pw_reg HS (Z_to_bv 5 22) (w64 (POLL_S + 80)) Q22 ltac:(reflexivity).
pw_reg HS (Z_to_bv 5 23) (w64 (POLL_S + 88)) Q23 ltac:(reflexivity).
pw_reg HS (Z_to_bv 5 24) (w64 (POLL_S + 64)) Q24 ltac:(reflexivity).
pw_reg HS (Z_to_bv 5 25) (w64 (pw_F c pos + 32)) Q25
  ltac:(cbn [sv_denot]; rewrite (EE0 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact HRG25).
pw_reg HS (Z_to_bv 5 27) (w64 PW_SH80) Q27 ltac:(reflexivity).
assert (HRGms : pw_rg_buf B c pos (ms_regs ms)).
{ unfold pw_rg_buf, pw_rg_run, pw_rg_base. repeat apply conj;
    [ exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20 | exact Q21
    | exact Q22 | exact Q23 | exact Q24 | exact Q27 | exact Q25 ]. }
eapply (SRr_jalr_call_pi (PL := PL_transportb) (PI := PI_transportb) W2 E0 _ _ _ _ 0x700e7 (1%bv : bv 5)
  (14%bv : bv 5) (TI.ti_io_recv timg_B) HEI HS eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact Q14
  | rewrite EIOR; lia | rewrite EIOR; reflexivity |].
intros matC ms1 Ems1 _. subst ms1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_io_recv timg_B) regsC mm mdC) Qx) end.
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (39600 + 4)))
  by (unfold regsC; rewrite YK11.getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc;
      discriminate Hc); reflexivity).
assert (RCK : forall r : bv 5, bv_unsigned r <> 1 -> YK11.getr regsC r = YK11.getr (ms_regs ms) r)
  by (intros r Hr; unfold regsC; apply YK11.getr_other; intros Eq; apply Hr; rewrite Eq; reflexivity).
assert (EBN : BASE + (39600 + 4) = 0x8ad54) by (vm_compute; reflexivity).
assert (HJC : ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c)
    (cx_md0 c) ((POLL_CID, pos) :: cx_own c) ly2 S2 W2 (ms_mem ms) mdC (cx_k c))
  by (unfold mdC; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ).
assert (HRUNC : pw_run B MT c pos ly2 S2 W2 (ms_mem ms) mdC Bx)
  by (apply (pw_run_win B MT c pos ly2 S2 W2 (ms_mem ms) md1 Bx (ms_mem ms) mdC RT OK HRUN1 HJC);
      [intros a _ _; reflexivity | intros a Ha; exact Ha]).
eapply SRr_bind.
{ exact (pw_recv_call B MT c pos ly2 S2 W2 (ms_mem ms) mdC Bx regsC B1 r1 got RT KEEP OK HRUNC
    ltac:(rewrite (RCK 2%bv ltac:(vm_compute; discriminate)); exact Q2)
    ltac:(rewrite (RCK 3%bv ltac:(vm_compute; discriminate)); exact Q3)
    ltac:(rewrite (RCK 4%bv ltac:(vm_compute; discriminate)); exact Q4)
    ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite RC1, EBN, unsigned_lit_small by lia; lia)
    ltac:(rewrite (RCK 11%bv ltac:(vm_compute; discriminate)); exact Q11)
    ltac:(rewrite (RCK 12%bv ltac:(vm_compute; discriminate)); exact Q12)
    HM1). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HP3 & HA03 & HX3 & HRUN3).
rewrite RC1.
change (Z_to_bv 64 (BASE + (39600 + 4))) with (Z_to_bv 64 (BASE + (PW_LOOP + 0x18))).
assert (HRG3 : pw_rg_buf B c pos regs3)
  by exact (pw_rg_buf_pres c pos regsC regs3 (pw_rg_buf_call c pos (ms_regs ms) regsC HRGms RCK) HP3).
pose proof (proj1 (proj1 HRUN3)) as HJ3.
clear dependent ms.
(* +0x2bc .. +0x2c0: s10 = r, up to `blez a0` *)
pose proof HRG3 as (((P2 & P3 & P4 & P8 & P9 & P18) & P19 & P20 & P21 & P22 & P23 & P24 & P27) & P25).
pose proof (pw_entry c pos ly3 S3 W3 mem3 md3 B1 regs3 (PW_LOOP + 0x18) RT OK HRUN3 (proj1 HRG3)) as HS2.
set (E1 := pw_E regs3 B1) in HS2.
assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1; apply pw_env_img).
assert (SHOK2 : sh_ok segs PW_Bx (@nil shent) E1 (mrestrict (w_H W3) mem3)) by constructor.
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = YK11.getr regs3 r)
  by (intros n r Hn; unfold E1; apply pw_ew_reg; exact Hn).
assert (D10 : sv_denot E1 (SOff 10 0) = Z_to_bv 64 r1)
  by (cbn [sv_denot]; rewrite (EE1 10%nat 10%bv eq_refl), HA03, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
paj_run_tok RUN HS2 HJ3 SHOK2 PW_B0.
{ pw_awr. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
assert (KD4 : forall a, aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W3) mem3 a)
  by (intros a; exact (pw_run_kept E1 (w_H W3) mem3 (ms_mem ms) HFr a)).
assert (HRUN4 : pw_run B MT c pos ly3 S3 W3 (ms_mem ms) md4 B1)
  by (apply (pw_run_win B MT c pos ly3 S3 W3 mem3 md3 B1 (ms_mem ms) md4 RT OK HRUN3 HJ3);
      [intros a _ _; exact (KD4 a) | intros a Ha; exact (apresent_grows _ _ _ a HG Ha)]).
assert (HX4 : exists X : list byte, length X = Z.to_nat TS0.DIGINET_MAX_FRAME_LEN /\
    garr8 segs (mrestrict (w_H W3) (ms_mem ms)) (pw_F c pos + 32) (TW.zs X) /\ firstn (length got) X = got).
{ destruct HX3 as (X & HXL & HXG & HXF). exists X. split; [exact HXL |]. split; [| exact HXF].
  apply (pw_garr_move (w_H W3) mem3 (ms_mem ms)); [exact HXG | intros x _; exact (KD4 x)]. }
pw_reg HS2 (Z_to_bv 5 26) (w64 r1) Q26
  ltac:(cbn [sv_denot]; rewrite (EE1 10%nat 10%bv eq_refl), HA03, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HBR : branch_taken BC_GE (sv_denot E1 (SLit 0)) (sv_denot E1 (SOff 10 0)) = negb (0 <? r1)).
{ cbn [branch_taken]. rewrite D10. change (sv_denot E1 (SLit 0)) with (Z_to_bv 64 0).
  rewrite (pw_lts 0 r1 ltac:(lia) ltac:(lia)). reflexivity. }
psrr_branch_tok RUN BR HS2 SHOK2 PW_B0.
- (* r <= 0: the drain returns r with the recv's world (:526), to the release cut *)
  rewrite HBR in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  destruct HCASE as [(Hle & EBw & Er) | (Hpos & _)]; [| lia].
  paj_run_to_tok RUNTO HS2 HJ3 SHOK2 PW_B0 PW_REL.
  { pw_awr. }
  set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
  assert (KD5 : forall a, aview segs (w_H W3) (ms_mem ms0) a = aview segs (w_H W3) (ms_mem ms) a)
    by (intros a; exact (pw_run_kept E1 (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a)).
  assert (HRUN5 : pw_run B MT c pos ly3 S3 W3 (ms_mem ms0) md5 B1)
    by (apply (pw_run_win B MT c pos ly3 S3 W3 (ms_mem ms) md4 B1 (ms_mem ms0) md5 RT OK HRUN4 HJ3);
        [intros a _ _; exact (KD5 a) | intros a Ha; exact (apresent_grows _ _ _ a HG0 Ha)]).
  pw_reg HS2 (Z_to_bv 5 2) (w64 (pw_sp1 c)) F2
    ltac:(cbn [sv_denot]; rewrite (EE1 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P2).
  pw_reg HS2 (Z_to_bv 5 3) (w64 (as_gp B)) F3
    ltac:(cbn [sv_denot]; rewrite (EE1 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P3).
  pw_reg HS2 (Z_to_bv 5 4) (w64 (as_tp B)) F4
    ltac:(cbn [sv_denot]; rewrite (EE1 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P4).
  pw_reg HS2 (Z_to_bv 5 8) (w64 (pw_SP c)) F8
    ltac:(cbn [sv_denot]; rewrite (EE1 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P8).
  pw_reg HS2 (Z_to_bv 5 9) (w64 (pw_sp1 c)) F9
    ltac:(cbn [sv_denot]; rewrite (EE1 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P9).
  pw_reg HS2 (Z_to_bv 5 18) (w64 (pw_F c pos)) F18
    ltac:(cbn [sv_denot]; rewrite (EE1 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P18).
  pw_reg HS2 (Z_to_bv 5 26) (w64 r1) F26
    ltac:(cbn [sv_denot]; rewrite (EE1 10%nat 10%bv eq_refl), HA03, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  pmkst HS2.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (@cfg_at fx segs (BASE + PW_REL) rg mm mdx) Q) end.
  apply (REL RT OK pos ly3 S3 W3 (ms_mem ms0) md5 (ms_regs ms0)).
  + rewrite EBw. exact (proj1 HRUN5).
  + repeat apply conj; [exact F2 | exact F3 | exact F4 | exact F8 | exact F9 | exact F18].
  + rewrite Er. exact F26.
- (* 0 < r: the checks, io_now, diginet_session_rx, and back to the loop head with one less fuel *)
  rewrite HBR in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  destruct HCASE as [(Hle & _) | (Hpos & f & B2 & r2 & Efuel & HNOW1 & HRXM & HDRAIN)]; [lia |].
  destruct (HR1LEN Hc) as (HGOTL & HR1CAP).
  rewrite Efuel in HDRX.
  pose proof (pw_drain_rx_step timg_B (cx_TF c) (poll_dn_in (cx_TF c)) Bx f B1 r1 got B2 r2
    HDRX HIORECV HM1 Hc HNOW1 HRXM) as (HDN & HDRX2).
  (* a0 = r is an int in [0, 1514]: the `sext.w s10, s10` at +0x2e0 is the identity *)
  assert (HAF : afact_ok E1 10 (mkAF 0 TS0.DIGINET_MAX_FRAME_LEN 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE1 10%nat 10%bv eq_refl), HA03. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia |]. split; [apply Z.mod_1_r | lia]. }
  pose proof (st_ok_pi_add_fact _ _ _ 10%nat (mkAF 0 TS0.DIGINET_MAX_FRAME_LEN 0) HS2 HAF) as HS3.
  clear HS2.
  paj_run_tok RUN HS3 HJ3 SHOK2 PW_B0.
  { pw_awr. }
  set (md6 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md6. clear mat.
  assert (KD6 : forall a, aview segs (w_H W3) (ms_mem ms0) a = aview segs (w_H W3) (ms_mem ms) a)
    by (intros a; exact (pw_run_kept E1 (w_H W3) (ms_mem ms) (ms_mem ms0) HFr0 a)).
  assert (HRUN6 : pw_run B MT c pos ly3 S3 W3 (ms_mem ms0) md6 B1)
    by (apply (pw_run_win B MT c pos ly3 S3 W3 (ms_mem ms) md4 B1 (ms_mem ms0) md6 RT OK HRUN4 HJ3);
        [intros a _ _; exact (KD6 a) | intros a Ha; exact (apresent_grows _ _ _ a HG0 Ha)]).
  assert (HX6 : exists X : list byte, length X = Z.to_nat TS0.DIGINET_MAX_FRAME_LEN /\
      garr8 segs (mrestrict (w_H W3) (ms_mem ms0)) (pw_F c pos + 32) (TW.zs X) /\ firstn (length got) X = got).
  { destruct HX4 as (X & HXL & HXG & HXF). exists X. split; [exact HXL |]. split; [| exact HXF].
    apply (pw_garr_move (w_H W3) (ms_mem ms) (ms_mem ms0)); [exact HXG | intros x _; exact (KD6 x)]. }
  (* +0x2e4: `jalr a1` = io_now at the recv's world (the model's call_now tested the pointer) *)
  assert (EV34 : ew E1 34 = Z_to_bv 64 (TI.ti_io_now timg_B))
    by (unfold E1; rewrite pw_ew_now, <- pw_fld_now, HNOW1; reflexivity).
  pw_reg HS3 (Z_to_bv 5 2) (w64 (pw_sp1 c)) N2
    ltac:(cbn [sv_denot]; rewrite (EE1 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P2).
  pw_reg HS3 (Z_to_bv 5 3) (w64 (as_gp B)) N3
    ltac:(cbn [sv_denot]; rewrite (EE1 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P3).
  pw_reg HS3 (Z_to_bv 5 4) (w64 (as_tp B)) N4
    ltac:(cbn [sv_denot]; rewrite (EE1 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P4).
  pw_reg HS3 (Z_to_bv 5 8) (w64 (pw_SP c)) N8
    ltac:(cbn [sv_denot]; rewrite (EE1 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P8).
  pw_reg HS3 (Z_to_bv 5 9) (w64 (pw_sp1 c)) N9
    ltac:(cbn [sv_denot]; rewrite (EE1 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P9).
  pw_reg HS3 (Z_to_bv 5 18) (w64 (pw_F c pos)) N18
    ltac:(cbn [sv_denot]; rewrite (EE1 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P18).
  pw_reg HS3 (Z_to_bv 5 19) (w64 POLL_S) N19 ltac:(reflexivity).
  pw_reg HS3 (Z_to_bv 5 20) (w64 (SHADOW_OFF + pw_F c pos / 8)) N20
    ltac:(cbn [sv_denot]; rewrite (EE1 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P20).
  pw_reg HS3 (Z_to_bv 5 21) (w64 PW_SH64) N21 ltac:(reflexivity).
  pw_reg HS3 (Z_to_bv 5 22) (w64 (POLL_S + 80)) N22 ltac:(reflexivity).
  pw_reg HS3 (Z_to_bv 5 23) (w64 (POLL_S + 88)) N23 ltac:(reflexivity).
  pw_reg HS3 (Z_to_bv 5 24) (w64 (POLL_S + 64)) N24 ltac:(reflexivity).
  pw_reg HS3 (Z_to_bv 5 25) (w64 (pw_F c pos + 32)) N25
    ltac:(cbn [sv_denot]; rewrite (EE1 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact P25).
  pw_reg HS3 (Z_to_bv 5 26) (w64 r1) N26
    ltac:(cbn [sv_denot]; rewrite (EE1 10%nat 10%bv eq_refl), HA03, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  pw_reg HS3 (Z_to_bv 5 27) (w64 PW_SH80) N27 ltac:(reflexivity).
  pw_reg HS3 (Z_to_bv 5 11) (Z_to_bv 64 (TI.ti_io_now timg_B)) N11
    ltac:(cbn [sv_denot]; rewrite EV34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (HRGms0 : pw_rg_buf B c pos (ms_regs ms0)).
  { unfold pw_rg_buf, pw_rg_run, pw_rg_base. repeat apply conj;
      [ exact N2 | exact N3 | exact N4 | exact N8 | exact N9 | exact N18 | exact N19 | exact N20 | exact N21
      | exact N22 | exact N23 | exact N24 | exact N27 | exact N25 ]. }
  eapply (SRr_jalr_call_pi (PL := PL_transportb) (PI := PI_transportb) W3 E1 _ _ _ _ 0x580e7 (1%bv : bv 5)
    (11%bv : bv 5) (TI.ti_io_now timg_B) HEI1 HS3 eq_refl);
    [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact N11
    | rewrite EION; lia | rewrite EION; reflexivity |].
  intros matN msN EmsN _. subst msN.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    set (regsN := rg); set (mdN := mdx);
    change (SRr segs Wx (@cfg_at fx segs (TI.ti_io_now timg_B) regsN mm mdN) Qx) end.
  assert (RN1 : YK11.getr regsN 1%bv = Z_to_bv 64 (BASE + (39644 + 4)))
    by (unfold regsN; rewrite YK11.getr_same by (intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq;
        discriminate Hq); reflexivity).
  assert (RNK : forall r : bv 5, bv_unsigned r <> 1 -> YK11.getr regsN r = YK11.getr (ms_regs ms0) r)
    by (intros r Hr; unfold regsN; apply YK11.getr_other; intros Eq; apply Hr; rewrite Eq; reflexivity).
  assert (EBN2 : BASE + (39644 + 4) = 0x8ad80) by (vm_compute; reflexivity).
  assert (HJN : ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c)
      (cx_md0 c) ((POLL_CID, pos) :: cx_own c) ly3 S3 W3 (ms_mem ms0) mdN (cx_k c))
    by (unfold mdN; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ3).
  assert (HRUNN : pw_run B MT c pos ly3 S3 W3 (ms_mem ms0) mdN B1)
    by (apply (pw_run_win B MT c pos ly3 S3 W3 (ms_mem ms0) md6 B1 (ms_mem ms0) mdN RT OK HRUN6 HJN);
        [intros a _ _; reflexivity | intros a Ha; exact Ha]).
  eapply SRr_bind.
  { exact (pw_now_call B MT c pos ly3 S3 W3 (ms_mem ms0) mdN B1 regsN RT OK HRUNN
      ltac:(rewrite (RNK 2%bv ltac:(vm_compute; discriminate)); exact N2)
      ltac:(rewrite (RNK 3%bv ltac:(vm_compute; discriminate)); exact N3)
      ltac:(rewrite (RNK 4%bv ltac:(vm_compute; discriminate)); exact N4)
      ltac:(rewrite RN1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
      ltac:(unfold raZ; rewrite RN1, EBN2, unsigned_lit_small by lia; lia)). }
  cbv beta. intros W4 c4 _ (EW4 & regs4 & mem4 & md7 & -> & HP4 & HA04 & HRUN7 & HKEEP4 & HGR4).
  subst W4.
  rewrite RN1.
  change (Z_to_bv 64 (BASE + (39644 + 4))) with (Z_to_bv 64 (BASE + (PW_LOOP + 0x44))).
  assert (HRG4 : pw_rg_buf B c pos regs4)
    by exact (pw_rg_buf_pres c pos regsN regs4 (pw_rg_buf_call c pos (ms_regs ms0) regsN HRGms0 RNK) HP4).
  assert (N26' : YK11.getr regs4 26 = w64 r1)
    by exact (eq_trans (HP4 26 ltac:(hnf; lia)) (eq_trans (RNK 26%bv ltac:(vm_compute; discriminate)) N26)).
  assert (HX7 : exists X : list byte, length X = Z.to_nat TS0.DIGINET_MAX_FRAME_LEN /\
      garr8 segs (mrestrict (w_H W3) mem4) (pw_F c pos + 32) (TW.zs X) /\ firstn (length got) X = got).
  { destruct HX6 as (X & HXL & HXG & HXF). exists X. split; [exact HXL |]. split; [| exact HXF].
    pose proof (pw_cur_frame B MT c pos ly3 S3 W3 (ms_mem ms0) md6 B1 RT OK (proj1 HRUN6))
      as (_ & _ & _ & _ & _ & _ & HF4096 & _ & HFceil & _).
    unfold POLL_FBYTES in HFceil.
    assert (HLEN : Z.of_nat (length (TW.zs X)) = TS0.DIGINET_MAX_FRAME_LEN)
      by (unfold TW.zs; rewrite length_map, HXL, Z2Nat.id by (cbv; discriminate); reflexivity).
    assert (HCAP : TS0.DIGINET_MAX_FRAME_LEN = 1514) by reflexivity.
    apply (pw_garr_move (w_H W3) (ms_mem ms0) mem4); [exact HXG |].
    intros x Hx. rewrite HLEN, HCAP in Hx.
    assert (H47 : 2 ^ 47 < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
    assert (HLE : pw_F c pos + 1546 <= pw_sp1 c - ESTACK) by lia.
    assert (HES : ESTACK = 4096) by reflexivity.
    apply HKEEP4; lia. }
  (* +0x2e8 .. +0x2f4: a3 = now, a0 = s, a1 = buf, a2 = r, up to `jal diginet_session_rx` *)
  pose proof (proj1 (proj1 HRUN7)) as HJ7.
  clear dependent ms0. clear dependent ms.
  pose proof HRG4 as (((M2 & M3 & M4 & M8 & M9 & M18) & M19 & M20 & M21 & M22 & M23 & M24 & M27) & M25).
  pose proof (pw_entry c pos ly3 S3 W3 mem4 md7 B1 regs4 (PW_LOOP + 0x44) RT OK HRUN7 (proj1 HRG4)) as HS4.
  set (E2 := pw_E regs4 B1) in HS4.
  assert (HEIR : img_env VAL A_LIM E2) by (unfold E2; apply pw_env_img).
  assert (SHOK4 : sh_ok segs PW_Bx (@nil shent) E2 (mrestrict (w_H W3) mem4)) by constructor.
  assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = YK11.getr regs4 r)
    by (intros n r Hn; unfold E2; apply pw_ew_reg; exact Hn).
  paj_run_tok RUN HS4 HJ7 SHOK4 PW_B0.
  { pw_awr. }
  set (md8 := with_vm_backing (m_vm_lazy md7) mat md7) in *. clearbody md8. clear mat.
  assert (KD8 : forall a, aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W3) mem4 a)
    by (intros a; exact (pw_run_kept E2 (w_H W3) mem4 (ms_mem ms) HFr a)).
  assert (HRUN8 : pw_run B MT c pos ly3 S3 W3 (ms_mem ms) md8 B1)
    by (apply (pw_run_win B MT c pos ly3 S3 W3 mem4 md7 B1 (ms_mem ms) md8 RT OK HRUN7 HJ7);
        [intros a _ _; exact (KD8 a) | intros a Ha; exact (apresent_grows _ _ _ a HG Ha)]).
  assert (HX8 : exists X : list byte, length X = Z.to_nat TS0.DIGINET_MAX_FRAME_LEN /\
      garr8 segs (mrestrict (w_H W3) (ms_mem ms)) (pw_F c pos + 32) (TW.zs X) /\ firstn (length got) X = got).
  { destruct HX7 as (X & HXL & HXG & HXF). exists X. split; [exact HXL |]. split; [| exact HXF].
    apply (pw_garr_move (w_H W3) mem4 (ms_mem ms)); [exact HXG | intros x _; exact (KD8 x)]. }
  pw_reg HS4 (Z_to_bv 5 1) (Z_to_bv 64 (BASE + 39668)) S1 ltac:(apply codeptr_val; exact HEIR).
  pw_reg HS4 (Z_to_bv 5 2) (w64 (pw_sp1 c)) S2r
    ltac:(cbn [sv_denot]; rewrite (EE2 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M2).
  pw_reg HS4 (Z_to_bv 5 3) (w64 (as_gp B)) S3r
    ltac:(cbn [sv_denot]; rewrite (EE2 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M3).
  pw_reg HS4 (Z_to_bv 5 4) (w64 (as_tp B)) S4r
    ltac:(cbn [sv_denot]; rewrite (EE2 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M4).
  pw_reg HS4 (Z_to_bv 5 10) (w64 POLL_S) S10 ltac:(reflexivity).
  pw_reg HS4 (Z_to_bv 5 11) (w64 (pw_F c pos + 32)) S11
    ltac:(cbn [sv_denot]; rewrite (EE2 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M25).
  pw_reg HS4 (Z_to_bv 5 12) (w64 (Z.of_nat (length got))) S12
    ltac:(cbn [sv_denot]; rewrite (EE2 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, N26', HGOTL;
          reflexivity).
  pw_reg HS4 (Z_to_bv 5 13) (w64 (TC.io_now_m B1)) S13
    ltac:(cbn [sv_denot]; rewrite (EE2 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact HA04).
  pw_reg HS4 (Z_to_bv 5 8) (w64 (pw_SP c)) S8
    ltac:(cbn [sv_denot]; rewrite (EE2 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M8).
  pw_reg HS4 (Z_to_bv 5 9) (w64 (pw_sp1 c)) S9
    ltac:(cbn [sv_denot]; rewrite (EE2 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M9).
  pw_reg HS4 (Z_to_bv 5 18) (w64 (pw_F c pos)) S18
    ltac:(cbn [sv_denot]; rewrite (EE2 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M18).
  pw_reg HS4 (Z_to_bv 5 19) (w64 POLL_S) S19 ltac:(reflexivity).
  pw_reg HS4 (Z_to_bv 5 20) (w64 (SHADOW_OFF + pw_F c pos / 8)) S20
    ltac:(cbn [sv_denot]; rewrite (EE2 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M20).
  pw_reg HS4 (Z_to_bv 5 21) (w64 PW_SH64) S21 ltac:(reflexivity).
  pw_reg HS4 (Z_to_bv 5 22) (w64 (POLL_S + 80)) S22 ltac:(reflexivity).
  pw_reg HS4 (Z_to_bv 5 23) (w64 (POLL_S + 88)) S23 ltac:(reflexivity).
  pw_reg HS4 (Z_to_bv 5 24) (w64 (POLL_S + 64)) S24 ltac:(reflexivity).
  pw_reg HS4 (Z_to_bv 5 25) (w64 (pw_F c pos + 32)) S25
    ltac:(cbn [sv_denot]; rewrite (EE2 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact M25).
  pw_reg HS4 (Z_to_bv 5 27) (w64 PW_SH80) S27 ltac:(reflexivity).
  assert (HRGms : pw_rg_buf B c pos (ms_regs ms)).
  { unfold pw_rg_buf, pw_rg_run, pw_rg_base. repeat apply conj;
      [ exact S2r | exact S3r | exact S4r | exact S8 | exact S9 | exact S18 | exact S19 | exact S20 | exact S21
      | exact S22 | exact S23 | exact S24 | exact S27 | exact S25 ]. }
  assert (EBN3 : BASE + 39668 = 0x8ad94) by (vm_compute; reflexivity).
  pmkst HS4.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr segs Wx (@cfg_at fx segs (transportb_sigma TB_diginet_session_rx) rg mm mdx) Qx) end.
  (* +0x2f8: diginet_session_rx at the recv's world, with the bytes it handed over and now *)
  assert (S1' : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 (BASE + 39668)) by exact S1.
  eapply SRr_bind.
  { exact (pw_rx_call B MT c pos ly3 S3 W3 (ms_mem ms) md8 B1 (ms_regs ms) got (TC.io_now_m B1) B2 r2
      RT KEEP OK HRUN8 S2r S3r S4r
      ltac:(rewrite S1'; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
      ltac:(unfold raZ; rewrite S1', EBN3, unsigned_lit_small by lia; lia)
      S10 S11 S12 S13 (pw_now_range B1) ltac:(lia) HX8 HRXM HDN). }
  cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md9 & -> & HP5 & HRUN9).
  rewrite S1'.
  change (Z_to_bv 64 (BASE + 39668)) with (Z_to_bv 64 (BASE + (PW_LOOP + 0x58))).
  assert (HRG5 : pw_rg_buf B c pos regs5) by exact (pw_rg_buf_pres c pos (ms_regs ms) regs5 HRGms HP5).
  pose proof (proj1 (proj1 HRUN9)) as HJ9.
  clear dependent ms.
  (* +0x2fc .. +0x308: the checks of s + 80 and s + 64, `beqz a0` back to the loop head *)
  pose proof HRG5 as (((V2 & V3 & V4 & V8 & V9 & V18) & V19 & V20 & V21 & V22 & V23 & V24 & V27) & V25).
  pose proof (pw_entry c pos ly5 S5 W5 mem5 md9 B2 regs5 (PW_LOOP + 0x58) RT OK HRUN9 (proj1 HRG5)) as HS5.
  set (E3 := pw_E regs5 B2) in HS5.
  assert (HEIL : img_env VAL A_LIM E3) by (unfold E3; apply pw_env_img).
  assert (SHOK5 : sh_ok segs PW_Bx (@nil shent) E3 (mrestrict (w_H W5) mem5)) by constructor.
  assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs5 r)
    by (intros n r Hn; unfold E3; apply pw_ew_reg; exact Hn).
  paj_run_to_tok RUNTO HS5 HJ9 SHOK5 PW_B0 PW_LOOP.
  { pw_awr. }
  set (md10 := with_vm_backing (m_vm_lazy md9) mat md9) in *. clearbody md10. clear mat.
  assert (KD10 : forall a, aview segs (w_H W5) (ms_mem ms) a = aview segs (w_H W5) mem5 a)
    by (intros a; exact (pw_run_kept E3 (w_H W5) mem5 (ms_mem ms) HFr a)).
  assert (HRUN10 : pw_run B MT c pos ly5 S5 W5 (ms_mem ms) md10 B2)
    by (apply (pw_run_win B MT c pos ly5 S5 W5 mem5 md9 B2 (ms_mem ms) md10 RT OK HRUN9 HJ9);
        [intros a _ _; exact (KD10 a) | intros a Ha; exact (apresent_grows _ _ _ a HG Ha)]).
  pw_reg HS5 (Z_to_bv 5 2) (w64 (pw_sp1 c)) U2
    ltac:(cbn [sv_denot]; rewrite (EE3 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V2).
  pw_reg HS5 (Z_to_bv 5 3) (w64 (as_gp B)) U3
    ltac:(cbn [sv_denot]; rewrite (EE3 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V3).
  pw_reg HS5 (Z_to_bv 5 4) (w64 (as_tp B)) U4
    ltac:(cbn [sv_denot]; rewrite (EE3 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V4).
  pw_reg HS5 (Z_to_bv 5 8) (w64 (pw_SP c)) U8
    ltac:(cbn [sv_denot]; rewrite (EE3 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V8).
  pw_reg HS5 (Z_to_bv 5 9) (w64 (pw_sp1 c)) U9
    ltac:(cbn [sv_denot]; rewrite (EE3 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V9).
  pw_reg HS5 (Z_to_bv 5 18) (w64 (pw_F c pos)) U18
    ltac:(cbn [sv_denot]; rewrite (EE3 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V18).
  pw_reg HS5 (Z_to_bv 5 19) (w64 POLL_S) U19 ltac:(reflexivity).
  pw_reg HS5 (Z_to_bv 5 20) (w64 (SHADOW_OFF + pw_F c pos / 8)) U20
    ltac:(cbn [sv_denot]; rewrite (EE3 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V20).
  pw_reg HS5 (Z_to_bv 5 21) (w64 PW_SH64) U21 ltac:(reflexivity).
  pw_reg HS5 (Z_to_bv 5 22) (w64 (POLL_S + 80)) U22 ltac:(reflexivity).
  pw_reg HS5 (Z_to_bv 5 23) (w64 (POLL_S + 88)) U23 ltac:(reflexivity).
  pw_reg HS5 (Z_to_bv 5 24) (w64 (POLL_S + 64)) U24 ltac:(reflexivity).
  pw_reg HS5 (Z_to_bv 5 25) (w64 (pw_F c pos + 32)) U25
    ltac:(cbn [sv_denot]; rewrite (EE3 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V25).
  pw_reg HS5 (Z_to_bv 5 27) (w64 PW_SH80) U27 ltac:(reflexivity).
  assert (HRGL : pw_rg_buf B c pos (ms_regs ms)).
  { unfold pw_rg_buf, pw_rg_run, pw_rg_base. repeat apply conj;
      [ exact U2 | exact U3 | exact U4 | exact U8 | exact U9 | exact U18 | exact U19 | exact U20 | exact U21
      | exact U22 | exact U23 | exact U24 | exact U27 | exact U25 ]. }
  pmkst HS5.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (@cfg_at fx segs (BASE + PW_LOOP) rg mm mdx) Qx) end.
  exact (IH f ltac:(lia) RT KEEP OK pos ly5 S5 W5 (ms_mem ms) md10 (ms_regs ms) B2 HRUN10 HRGL HDRAIN HDRX2).
Qed.

End s.

Theorem pw_loop_piece : forall fx rc B MT, @pw_loop_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@pw_loop_holds fx rc B MT). Qed.
