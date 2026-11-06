(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 697 of its 763 lines of code are new or changed and 1858 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/on_announce_seg_tail.v; 536 of its 615 lines of code are new or changed and 684 lines of the source are left out. *)
(* on_announce_seg_wk: Lemma onann_wk_piece : onann_wk_stmt (lib/B/Prog/OnannCutB.v: onann_nrel_at -> onann_wk_at),
   the wake piece of the walk of on_announce on fuzz_transport.asan-ubsan, offsets +0x470 .. +0x49c of the listing
   lib/B/Prog/DgnTransportBList.v (AF_on_announce = 0x6a28; 0x88138 .. 0x88164), then the n-release cut ONANN_NREL
   (+0x61c, 0x882e4), which the onann_nrel_at it is given closes.

   What the code does (diginet_session.c:204-205). +0x470 `bne a0, zero, +0x61c`: a0 is S_state B4, the state the
   code loaded before the cut (OnannCutB.v onann_regs_wk, sign-extended).
     A state other than S_IDLE goes to +0x61c; the model's world is B4 (OnannCutB.v onann_k_wk).
     S_IDLE: +0x474 .. +0x484 the check of the 4-byte load at s + 16 (cfg.auto_wake; its shadow byte is 0: g_s's
     payload lies in the record's zero shadow, on_announce_cg.v trans_onann_cells, read by DgnTransportBCg.v
     decode_zshadow_rd), +0x488 `lw a0, 0(a0)`: S_cfg_auto_wake B4, sign-extended; +0x48c `beq a0, zero, +0x61c`.
       auto_wake = 0 goes to +0x61c; the model's world is B4.
       auto_wake <> 0: +0x490 `mv a0, s4` (s), +0x494 `mv a1, s5` (now), +0x498 `jal diginet_session_wake`
       (0x86a38 = transportb_sigma TB_diginet_session_wake), return address +0x49c; +0x49c `j +0x61c`. The model's
       world is diginet_session_wake_m's B5.
   No instruction of the piece stores a byte.

   The runs are the token engine's over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x):
     the entry state at +0x470 has one read region, the 4 bytes of cfg.auto_wake at s4 + 16 (atom 32, read off the
     world B4 by TWorldG.v tw_read_val), and the shadow entry of the check of s + 16 (shadow base s8); it is split at
     once on the `bne` (DgnTransportBPaLib.v psrr_branch_tok);
       the arm to +0x61c        one instruction (onwk_nrel closes it);
       the other arm            runs +0x470 .. +0x48c and stops at the `beq`, which is taken up again from a state
                                with no region (the registers as atoms) and split;
         the arm to +0x61c      one instruction (onwk_nrel);
         the other arm          runs +0x48c .. the `jal` and stops at the call;
     after the call (+0x49c)    taken up again from a state with no region, one instruction to +0x61c (onwk_join).
   The diginet_session_wake call (diginet_session_wake_cg.v transport_diginet_session_wake_cg at transportb_sigma
   TB_diginet_session_wake, a G-form callee in the same journal), premise by premise: the journal at the call state
   (the own frame owned); ra = +0x49c (DgnTransportBPaLib.v ret_ok_codeptr_v); gp, tp kept by the runs; a0 = s = WAKE_S;
   a1 = now (s5, onann_regs_wk); sp = sp1, 16-aligned, and on_announce_cg.v onann_stk_eq places wake's window inside
   on_announce's; tw_at at B4 (the runs keep every byte); g_fail_next B4 <= 1, the run invariants at B4 (the cut's
   onann_wk_cur); the model (onann_k_wk on this arm, onwk_model_wake); trans_tframe_at and trans_rom_view_rd at the
   call state (on_announce_seg_kit.v onann_tf_cur, onann_rom_cur); trans_tf_off_g (onann_fix); wake_apart
   (on_announce_seg_kit.v onann_apart_wake); the counts (frames S2 = (ONANN_CID, pos) :: frames Sc, and ONANN_CID is
   neither WAKE_CID nor SENDCTL_CID: onwk_count); the events (onann_wk_cur's e + WAKE_EV <= ONANN_EV). Its post folds
   into onann_cur by TransportGCg.v dk_kept_trans_nf_g (wake_wr B4 is the row `exists Bx, wake_wr Bx` of onann_wr Bw b:
   on_announce_seg_kit.v onann_wr_wake), the saved words by its window clause and the frame's last word by its frame
   clause (a byte of wake_wr is a byte of G, outside the own frame: onann_wake_wr_G).

   Trap and error paths on this piece: the slow path of the check of s + 16 (`bne a1, zero` at +0x484 to +0x824): the
   shadow byte of s + 16 is 0 (trans_onann_cells). This piece passes no UBSan trap word. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_seg_kit.
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
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model on this piece                                          *)
(* ------------------------------------------------------------------ *)

(* The two later cut points of the piece: the `beq` after the load of cfg.auto_wake (+0x48c) and the return address
   of diginet_session_wake (+0x49c, `j +0x61c`). *)
Definition ONWK_AW : Z := AF_on_announce + 0x48c.
Definition ONWK_RET : Z := AF_on_announce + 0x49c.

(* `bne a0, zero` / `beq a0, zero` on a sign-extended 32-bit value. *)
Lemma onwk_eqb0 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0 (2 ^ 64)) by lia.
destruct (Z.eqb_spec v 0) as [-> | Hne]; [reflexivity|].
apply Z.eqb_neq. intros HH. apply Hne.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

(* The sign-extended 4-byte load of a world field is its s32_at. *)
Lemma onwk_sext : forall E X k, ew E 32 = Z_to_bv 64 (TW.u_at X k 4) ->
  sv_denot E (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.s32_at X k).
Proof.
intros E X k H.
assert (R : 0 <= TW.u_at X k 4 < 2 ^ 32) by exact (TWL.u_at_range X _ 4).
cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The model after the cut (OnannCutB.v onann_k_wk), by arm. *)
Lemma onwk_model_ne : forall I Fr B4 now Bw', TW.S_state B4 <> TS0.DIGINET_S_IDLE ->
  onann_k_wk I Fr B4 now = Some (Bw', tt) -> Bw' = B4.
Proof.
intros I Fr B4 now Bw' Hs H. unfold onann_k_wk in H.
replace (TW.S_state B4 =? TS0.DIGINET_S_IDLE) with false in H by (symmetry; apply Z.eqb_neq; exact Hs).
cbn [andb] in H. symmetry. exact (onann_some_inv _ _ H).
Qed.

Lemma onwk_model_aw0 : forall I Fr B4 now Bw', TW.S_cfg_auto_wake B4 = 0 ->
  onann_k_wk I Fr B4 now = Some (Bw', tt) -> Bw' = B4.
Proof.
intros I Fr B4 now Bw' Ha H. unfold onann_k_wk in H. rewrite Ha in H. cbn [Z.eqb negb] in H.
rewrite andb_false_r in H. cbv beta iota in H. symmetry. exact (onann_some_inv _ _ H).
Qed.

Lemma onwk_model_wake : forall I Fr B4 now Bw', TW.S_state B4 = TS0.DIGINET_S_IDLE -> TW.S_cfg_auto_wake B4 <> 0 ->
  onann_k_wk I Fr B4 now = Some (Bw', tt) ->
  exists B5 r, TSS.diginet_session_wake_m I Fr B4 now = Some (B5, r) /\ Bw' = B5.
Proof.
intros I Fr B4 now Bw' Hs Ha H. unfold onann_k_wk in H.
rewrite Hs, Z.eqb_refl in H.
replace (TW.S_cfg_auto_wake B4 =? 0) with false in H by (symmetry; apply Z.eqb_neq; exact Ha).
cbn [andb negb] in H.
destruct (TSS.diginet_session_wake_m I Fr B4 now) as [[B5 r]|]; cbv beta iota in H; [|discriminate H].
exists B5, r. split; [reflexivity|]. symmetry. exact (onann_some_inv _ _ H).
Qed.

(* The own class-3 frame counts for neither callee class. *)
Lemma onwk_count : forall c (l : list (Z * Z)) pos, c <> ONANN_CID ->
  count_cid c ((ONANN_CID, pos) :: l) = count_cid c l.
Proof.
intros c l pos Hc. cbn [count_cid].
destruct (Z.eqb_spec ONANN_CID c) as [E|_]; [exfalso; apply Hc; symmetry; exact E | lia].
Qed.

(* The stack: ONANN_STK holds the 208 bytes of the frame and the realignment above wake's window. *)
Lemma onwk_stk : 4304 <= ONANN_STK /\ ONANN_STK = 208 + WAKE_STK.
Proof.
split; [|rewrite onann_stk_eq; reflexivity].
unfold ONANN_STK, ONANN_FRAME, ONANN_ALIGN.
lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
  pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The entry state at +0x470: the 4 bytes of cfg.auto_wake at s4 + 16 (s4 = atom 20, read, atom 32); s4 = s (64-aligned)
   and s8 = the shadow base (atom 24); the shadow entry of the check of s + 16. *)
Definition onwk_rg_aw : YP09.region :=
  YP09.mkRegion (Some 20%nat) 16 20 16 16 [YP09.mkChunk 16 (YP09.CVal 4 (SOff 32 0))].
Definition onwk_facts : facts :=
  mkFacts [(20%nat, mkAF ONANN_S ONANN_S 6); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)]
    [] [].
Definition ss_onwk : sstate := mkSS ONANN_WK sr_atoms [onwk_rg_aw] None onwk_facts.
Definition ONWK_SH : list shent := [mkSHE 20 16 20].
Definition ONWK_BX : sv := SOff 24 0.
(* The runs with no shadow token: the span (0, 0). *)
Definition ONWK_B0 : Z * Z := (0, 0).

(* The register and region readers of a symbolic state (on_ack_seg_aft.v's oaf_reg / oaf_kreg; also in the form a
   run leaves at a call: st_ok at the callee's pc). *)
Ltac onwk_reg HS r v H tac :=
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
(* Register r of the machine state of HS, whose symbolic value is atom n, the start value of register rn (Q its
   value): the run's valuation agrees with the start valuation below atom 1024 (Elo), which reads the registers (EE). *)
Ltac onwk_kreg_of HS Elo EE r n rn Q H :=
  lazymatch type of Q with _ = ?v =>
    onwk_reg HS r v H
      ltac:(cbn [sv_denot]; try rewrite (Elo n ltac:(lia)); rewrite (EE n rn eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
            exact Q) end.
Ltac onwk_kreg HS Elo EE r n Q H := onwk_kreg_of HS Elo EE r n r Q H.
Ltac onwk_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The windows of a run's start state: none writes a byte. *)
Ltac onwk_win Hin Hx :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]);
  destruct Hin.
(* The model of the goal, named. *)
Ltac onwk_name_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md := m) in *; clearbody md end.
(* After a run: its valuation agrees with the start valuation E0 below atom 1024 (Hlo), and its machine state is
   named m. *)
Ltac onwk_lo HS E0 Hlo m :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  end.

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The valuations: the 32 registers (and, at the entry, atom 32 = the 4 bytes of cfg.auto_wake of the world X). *)
Definition onwk_E0 (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).
Definition onwk_E (regs : bvmap 5 word) (X : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 16) 4)]).

Lemma onwk_ew0 : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (onwk_E0 regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold onwk_E0. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma onwk_ew : forall regs X n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (onwk_E regs X) n = YK11.getr regs r.
Proof. intros regs X n r Hn. unfold onwk_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma onwk_ew32 : forall regs X, ew (onwk_E regs X) 32 = Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 16) 4).
Proof. intros regs X. unfold onwk_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.

(* g_s's bytes [s + 16, s + 20) are addressable at every AR state: a whole granule of the record's zero shadow. *)
Lemma onwk_ra_aw : forall ly S (W : world segs) mem md,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (ONANN_S + 16) 4.
Proof.
intros ly S W mem md HZ HAR x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : ONANN_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= ONANN_S + TW.SZ_g_s)
  by (unfold ONANN_S, TB_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The symbolic state at +0x470 holds of the machine state there, and the run's shadow entry holds. *)
Lemma onwk_entry : forall ly S (W : world segs) regs mem md X,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) X ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (onwk_E regs X) ss_onwk
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_WK)) mem (YK11.seg_rom segs))) /\
  sh_ok segs ONWK_BX ONWK_SH (onwk_E regs X) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md X HSC HAR Htw R20 R24.
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (U20 : bv_unsigned (ew (onwk_E regs X) 20) = ONANN_S)
  by (rewrite (onwk_ew regs X 20 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew (onwk_E regs X) 24) = SHADOW_OFF)
  by (rewrite (onwk_ew regs X 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R32 : 0 <= TW.u_at X (TW.OFF_g_s + 16) 4 < 2 ^ 32) by exact (TWL.u_at_range X _ 4).
assert (U32 : bv_unsigned (ew (onwk_E regs X) 32) = TW.u_at X (TW.OFF_g_s + 16) 4)
  by (rewrite onwk_ew32; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_onwk.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold onwk_rg_aw, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ ONANN_S 16 4 (SOff 32 0) (TW.u_at X (TW.OFF_g_s + 16) 4));
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | lia |].
    exact (tw_read_val segs _ TMAP_B X TW.OFF_g_s TB_g_s TW.SZ_g_s 16 4 TMAP_B_ok Htw TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold onwk_rg_aw, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold onwk_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U24, U32.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (onwk_ra_aw ly S W mem md HSC HAR) as HRA.
  assert (UB : U (onwk_E regs X) ONWK_BX = SHADOW_OFF).
  { unfold U, ONWK_BX. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, ONWK_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ ONWK_BX 20 (ONANN_S + 16) 4 ONANN_S 16 20 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* A state with no region at any pc of the listing (+0x48c and +0x49c are taken up from it). *)
Lemma onwk_entry0 : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (onwk_E0 regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.
End ent.

(* ------------------------------------------------------------------ *)
(* 3. The cut's facts carried, the release cut, the join, the piece    *)
(* ------------------------------------------------------------------ *)

Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* What every cut carries, at a later memory of the same state whose view is the cut memory's at every byte (the runs
   of this piece write nothing). *)
Lemma onwk_cur_keep : onann_laws B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 mem3 : word -> option byte) (md2 md3 : Model) (e : Z),
    onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
    (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
    (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
    onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ly2 S2 W2
  mem2 mem3 md2 md3 e HFIX HCUR HJ3 KV GA.
pose proof HLAWS as (_ & _ & _ & _ & _ & _ & _ & LAWS & _).
pose proof HCUR as (HJ & He & Hfrs & Hperm & HlyF & Hmo & HK & HSV & HFL).
destruct (onann_cur_ar B MT LAWS HFIX HCUR) as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF4096 & _ & HFce &
  _ & Hce & Hlo & Hhi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct onwk_stk as [HBS _].
refine (conj HJ3 (conj He (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj _ (conj _ _)))))))).
- apply (TransportGFrame.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2 mem3
    (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) (fun _ => False) HARc HK).
  + intros a Ha _. exact (KV a Ha).
  + exact GA.
  + intros a Hz. destruct Hz.
  + intros b0 m i _ _ Hz. destruct Hz.
  + intros a Hz. destruct Hz.
  + intros c p a _ _ Hz. destruct Hz.
- apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSV o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KV. lia.
- unfold ONANN_FBYTES in *. rewrite <- HFL. apply YCbq.rdword_ext. intros i Hi. apply KV. lia.
Qed.

(* The n-release cut, from a state of this piece that wrote nothing since the cut: the cut's facts there, the world
   relation at the model's world, and onann_nrel_at. *)
Lemma onwk_nrel : @onann_nrel_at fx rc B MT -> onann_laws B MT -> onann_callees B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 mem3 : word -> option byte) (md2 md3 : Model) (e : Z) (regs3 : bvmap 5 word),
    onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' -> TW.g_fail_next Bw' <= 1 ->
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
    (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
    (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
    onann_regs_rel regs regs3 sp1 F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + ONANN_NREL)) mem3 (YK11.seg_rom segs)) md3)
      (@transport_onann_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Proof.
intros NREL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 mem3 md2 md3 e regs3 HFIX HCUR Htw Hgf HJ3 KV GA HREGS.
pose proof HLAWS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGX & _).
pose proof (onwk_cur_keep HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F ly2 S2 W2 mem2 mem3 md2 md3 e HFIX HCUR HJ3 KV GA) as CUR3.
assert (TW3 : tw_at TMAP_B (aview segs (w_H W2) mem3) Bw').
{ apply (tw_kept_GB (aview segs (w_H W2) mem2)); [exact Htw|]. intros b0 n i Hbn Hi.
  assert (Hg : inG TG.G_HARNESS_B (b0 + i))
    by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  apply KV. lia. }
exact (NREL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem3 md3 e regs3 HFIX (conj CUR3 (conj TW3 Hgf)) HREGS).
Qed.

(* The join, +0x49c: `j +0x61c` from the state diginet_session_wake returned, then the n-release cut. *)
Lemma onwk_join : @onann_nrel_at fx rc B MT -> onann_laws B MT -> onann_callees B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly3 : alayout) (S3 : astate)
         (W3 : world segs) (mem3 : word -> option byte) (md3 : Model) (e : Z) (regs3 : bvmap 5 word),
    onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_rel_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b pos F ly3 S3 W3 mem3 md3 e ->
    onann_regs_rel regs regs3 sp1 F ->
    SRr segs W3 (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + ONWK_RET)) mem3 (YK11.seg_rom segs)) md3)
      (@transport_onann_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Proof.
intros NREL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly3 S3 W3 mem3 md3 e regs3 HFIX HREL HREGS.
pose proof HLAWS as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & _ & HGX & _).
pose proof HREL as (HCUR3 & Htw3 & Hgf3).
pose proof HCUR3 as (HJ & _).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25).
pose proof (onwk_entry0 (fx := fx) W3 regs3 mem3 ONWK_RET) as HS.
assert (SHOK : sh_ok segs ONWK_BX [] (onwk_E0 regs3) (mrestrict (w_H W3) mem3)) by constructor.
assert (HEI : img_env VAL A_LIM (onwk_E0 regs3)) by (unfold onwk_E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (onwk_E0 regs3) n = YK11.getr regs3 r)
  by (intros n r Hn; exact (onwk_ew0 regs3 n r Hn)).
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK ONWK_B0 ONANN_NREL.
{ onwk_awr_rs. apply awr_ok_x_nil. }
onwk_name_md md4.
onwk_lo HS (onwk_E0 regs3) E4lo ms4.
onwk_kreg HS E4lo EE (2%bv : bv 5) 2%nat R2 X2. onwk_kreg HS E4lo EE (3%bv : bv 5) 3%nat R3 X3.
onwk_kreg HS E4lo EE (4%bv : bv 5) 4%nat R4 X4. onwk_kreg HS E4lo EE (8%bv : bv 5) 8%nat R8 X8.
onwk_kreg HS E4lo EE (9%bv : bv 5) 9%nat R9 X9. onwk_kreg HS E4lo EE (18%bv : bv 5) 18%nat R18 X18.
onwk_kreg HS E4lo EE (19%bv : bv 5) 19%nat R19 X19. onwk_kreg HS E4lo EE (25%bv : bv 5) 25%nat R25 X25.
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
  intros b0 wlo whi x Hin Hx. cbv beta. onwk_win Hin Hx. }
assert (G4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_NREL)) mm rom) mdx) Q) end.
exact (onwk_nrel NREL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F ly3 S3 W3 mem3 (ms_mem ms4) md3 md4 e (ms_regs ms4) HFIX HCUR3 Htw3 Hgf3 HJ K4 G4
  (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X19 X25)))))))).
Qed.

(* The piece. *)
Lemma onann_wk_piece : @onann_wk_stmt fx rc B MT.
Proof.
unfold onann_wk_stmt, onann_wk_at.
intros NREL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  B4 ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof HLAWS as (_ & _ & HSC & _ & _ & _ & _ & LAWS & MTL & _ & _ & _ & FFL & HGX & _).
pose proof HCALL as (_ & _ & _ & _ & _ & _ & _ & HWAKE & _ & _).
pose proof HFIX as (HJe & _ & _ & Hgp & Htp & _ & _ & _ & Hsp16 & Hwin1 & Hwin2 & Hnow & _ & _ & _ & _ & _ & Hoff &
  _ & Hapart & _ & _ & Hc1 & Hc2 & Hnev & _ & EF & _ & _ & _ & _).
pose proof HCUR as (HCUR0 & HeW & Htw4 & Hk & Hgf4 & Hri4).
pose proof HCUR0 as (HJ2 & He & Hfrs & Hperm & HlyF & Hmo & HK & HSV & HFL).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25) & R20 & R24) & R10 & R21).
destruct (onann_cur_ar B MT LAWS HFIX HCUR0) as (HARc & HAR2 & Elo & Ehi & EFa & EFl & Hin2 & EFA2 & _ & _ & FNG &
  HF4096 & _ & HFce & _ & Hce & Hlo & Hhi & H47 & _ & _ & _ & _ & _ & Hsp1 & Hsp132 & Hsp146).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct onwk_stk as [HBS ESTK].
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (Hsp116 : sp1 mod 16 = 0).
{ pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp132, Z.add_0_r in D. rewrite D.
  replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
pose proof (TWL.s32_range B4 (TW.OFF_g_s + 112)) as HSR. rewrite <- onann_rd_state in HSR.
(* +0x470, from the state with the read of cfg.auto_wake and the shadow entry of its check *)
destruct (onwk_entry (fx := fx) B ly2 S2 W2 regs2 mem2 md2 B4 HSC HAR2 Htw4 R20 R24) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (onwk_E regs2 B4)) by (unfold onwk_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (onwk_E regs2 B4) n = YK11.getr regs2 r)
  by (intros n r Hn; exact (onwk_ew regs2 B4 n r Hn)).
assert (E32 : ew (onwk_E regs2 B4) 32 = Z_to_bv 64 (TW.u_at B4 (TW.OFF_g_s + 16) 4)) by exact (onwk_ew32 regs2 B4).
assert (D10 : sv_denot (onwk_E regs2 B4) (SOff 10 0) = Z_to_bv 64 (TW.S_state B4)).
{ cbn [sv_denot]. rewrite (EE 10%nat 10%bv eq_refl), R10, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (D0 : sv_denot (onwk_E regs2 B4) (SLit 0) = Z_to_bv 64 0) by reflexivity.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* S_state B4 <> S_IDLE: to the n-release cut; the model's world is B4 *)
  rewrite D10, D0 in Hc. cbn [branch_taken] in Hc. rewrite (onwk_eqb0 _ HSR) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  pose proof (onwk_model_ne _ _ _ _ _ Hc Hk) as EBw'.
  paj_run_to_tok RUNTO HS HJ2 SHOK YC4b.Bspan ONANN_NREL.
  { onwk_awr_rs.
    repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
    apply awr_ok_x_nil. }
  onwk_name_md md3.
  onwk_lo HS (onwk_E regs2 B4) E3lo ms3.
  onwk_kreg HS E3lo EE (2%bv : bv 5) 2%nat R2 X2. onwk_kreg HS E3lo EE (3%bv : bv 5) 3%nat R3 X3.
  onwk_kreg HS E3lo EE (4%bv : bv 5) 4%nat R4 X4. onwk_kreg HS E3lo EE (8%bv : bv 5) 8%nat R8 X8.
  onwk_kreg HS E3lo EE (9%bv : bv 5) 9%nat R9 X9. onwk_kreg HS E3lo EE (18%bv : bv 5) 18%nat R18 X18.
  onwk_kreg HS E3lo EE (19%bv : bv 5) 19%nat R19 X19. onwk_kreg HS E3lo EE (25%bv : bv 5) 25%nat R25 X25.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms3) a = aview segs (w_H W2) mem2 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta. onwk_win Hin Hx. }
  assert (G3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms3) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_NREL)) mm rom) mdx) Q) end.
  rewrite <- EBw' in Htw4, Hgf4.
  exact (onwk_nrel NREL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw
    Bw' pos sp1 F ly2 S2 W2 mem2 (ms_mem ms3) md2 md3 e (ms_regs ms3) HFIX HCUR0 Htw4 Hgf4 HJ2 K3 G3
    (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X19 X25)))))))).
- (* S_state B4 = S_IDLE: the check of s + 16, the load of cfg.auto_wake; the run stops at the `beq` *)
  rewrite D10, D0 in Hc. cbn [branch_taken] in Hc. rewrite (onwk_eqb0 _ HSR) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hst.
  paj_run_tok RUN HS HJ2 SHOK YC4b.Bspan.
  { onwk_awr_rs.
    repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
    apply awr_ok_x_nil. }
  onwk_name_md mdA.
  onwk_lo HS (onwk_E regs2 B4) EAlo msA.
  onwk_reg HS (10%bv : bv 5) (Z_to_bv 64 (TW.S_cfg_auto_wake B4)) XA10
    ltac:(rewrite onann_rd_auto_wake; apply onwk_sext; try rewrite (EAlo 32%nat ltac:(lia)); exact E32).
  onwk_kreg HS EAlo EE (2%bv : bv 5) 2%nat R2 XA2. onwk_kreg HS EAlo EE (3%bv : bv 5) 3%nat R3 XA3.
  onwk_kreg HS EAlo EE (4%bv : bv 5) 4%nat R4 XA4. onwk_kreg HS EAlo EE (8%bv : bv 5) 8%nat R8 XA8.
  onwk_kreg HS EAlo EE (9%bv : bv 5) 9%nat R9 XA9. onwk_kreg HS EAlo EE (18%bv : bv 5) 18%nat R18 XA18.
  onwk_kreg HS EAlo EE (19%bv : bv 5) 19%nat R19 XA19. onwk_kreg HS EAlo EE (25%bv : bv 5) 25%nat R25 XA25.
  onwk_kreg HS EAlo EE (20%bv : bv 5) 20%nat R20 XA20. onwk_kreg HS EAlo EE (21%bv : bv 5) 21%nat R21 XA21.
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msA) a = aview segs (w_H W2) mem2 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta. onwk_win Hin Hx. }
  assert (GAa : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msA) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  (* +0x48c: `beq a0, zero`, taken up again from a state with no region *)
  pmkst HS.
  clear HS SHOK.
  set (rA := ms_regs msA) in *. set (mA := ms_mem msA) in *. clearbody rA mA.
  pose proof (onwk_entry0 (fx := fx) W2 rA mA ONWK_AW) as HS.
  assert (SHOK : sh_ok segs ONWK_BX [] (onwk_E0 rA) (mrestrict (w_H W2) mA)) by constructor.
  assert (HEIb : img_env VAL A_LIM (onwk_E0 rA)) by (unfold onwk_E0; apply Eimg_env).
  assert (EEb : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (onwk_E0 rA) n = YK11.getr rA r)
    by (intros n r Hn; exact (onwk_ew0 rA n r Hn)).
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONWK_AW)) mm rom) mdx) Q) end.
  assert (D10b : sv_denot (onwk_E0 rA) (SOff 10 0) = Z_to_bv 64 (TW.S_cfg_auto_wake B4))
    by (cbn [sv_denot]; rewrite (EEb 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact XA10).
  assert (D0b : sv_denot (onwk_E0 rA) (SLit 0) = Z_to_bv 64 0) by reflexivity.
  pose proof (TWL.s32_range B4 (TW.OFF_g_s + 16)) as HAW. rewrite <- onann_rd_auto_wake in HAW.
  psrr_branch_tok RUN BR HS SHOK ONWK_B0.
  + (* cfg.auto_wake = 0: to the n-release cut; the model's world is B4 *)
    rewrite D10b, D0b in Hc. cbn [branch_taken] in Hc. rewrite (onwk_eqb0 _ HAW) in Hc.
    apply Z.eqb_eq in Hc.
    pose proof (onwk_model_aw0 _ _ _ _ _ Hc Hk) as EBw'.
    paj_run_to_tok RUNTO HS HJ2 SHOK ONWK_B0 ONANN_NREL.
    { onwk_awr_rs. apply awr_ok_x_nil. }
    onwk_name_md md3.
    onwk_lo HS (onwk_E0 rA) E3lo ms3.
    onwk_kreg HS E3lo EEb (2%bv : bv 5) 2%nat XA2 X2. onwk_kreg HS E3lo EEb (3%bv : bv 5) 3%nat XA3 X3.
    onwk_kreg HS E3lo EEb (4%bv : bv 5) 4%nat XA4 X4. onwk_kreg HS E3lo EEb (8%bv : bv 5) 8%nat XA8 X8.
    onwk_kreg HS E3lo EEb (9%bv : bv 5) 9%nat XA9 X9. onwk_kreg HS E3lo EEb (18%bv : bv 5) 18%nat XA18 X18.
    onwk_kreg HS E3lo EEb (19%bv : bv 5) 19%nat XA19 X19. onwk_kreg HS E3lo EEb (25%bv : bv 5) 25%nat XA25 X25.
    assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms3) a = aview segs (w_H W2) mem2 a).
    { intros a Ha. rewrite <- (KA a Ha).
      apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
      intros b0 wlo whi x Hin Hx. cbv beta. onwk_win Hin Hx. }
    assert (G3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms3) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAa a Ha))).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_NREL)) mm rom) mdx) Q) end.
    rewrite <- EBw' in Htw4, Hgf4.
    exact (onwk_nrel NREL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw
      Bw' pos sp1 F ly2 S2 W2 mem2 (ms_mem ms3) md2 md3 e (ms_regs ms3) HFIX HCUR0 Htw4 Hgf4 HJ2 K3 G3
      (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X19 X25)))))))).
  + (* cfg.auto_wake <> 0: a0 = s, a1 = now, `jal diginet_session_wake` *)
    rewrite D10b, D0b in Hc. cbn [branch_taken] in Hc. rewrite (onwk_eqb0 _ HAW) in Hc.
    apply Z.eqb_neq in Hc. rename Hc into Haw.
    destruct (onwk_model_wake _ _ _ _ _ Hst Haw Hk) as (B5 & r' & Pmod & EBw').
    paj_run_tok RUN HS HJ2 SHOK ONWK_B0.
    { onwk_awr_rs. apply awr_ok_x_nil. }
    onwk_name_md mdW.
    onwk_lo HS (onwk_E0 rA) EWlo msW.
    (* the registers at diginet_session_wake's entry *)
    onwk_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 28356)) Z1 ltac:(apply codeptr_val; assumption).
    onwk_kreg HS EWlo EEb (2%bv : bv 5) 2%nat XA2 Z2. onwk_kreg HS EWlo EEb (3%bv : bv 5) 3%nat XA3 Z3.
    onwk_kreg HS EWlo EEb (4%bv : bv 5) 4%nat XA4 Z4. onwk_kreg HS EWlo EEb (8%bv : bv 5) 8%nat XA8 Z8.
    onwk_kreg HS EWlo EEb (9%bv : bv 5) 9%nat XA9 Z9. onwk_kreg HS EWlo EEb (18%bv : bv 5) 18%nat XA18 Z18.
    onwk_kreg HS EWlo EEb (19%bv : bv 5) 19%nat XA19 Z19. onwk_kreg HS EWlo EEb (25%bv : bv 5) 25%nat XA25 Z25.
    onwk_kreg_of HS EWlo EEb (10%bv : bv 5) 20%nat (20%bv : bv 5) XA20 Z10.
    onwk_kreg_of HS EWlo EEb (11%bv : bv 5) 21%nat (21%bv : bv 5) XA21 Z11.
    (* the runs wrote no byte *)
    assert (KW : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msW) a = aview segs (w_H W2) mem2 a).
    { intros a Ha. rewrite <- (KA a Ha).
      apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
      intros b0 wlo whi x Hin Hx. cbv beta. onwk_win Hin Hx. }
    assert (GW : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msW) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAa a Ha))).
    set (mW := ms_mem msW) in *. set (rW := ms_regs msW) in *.
    (* the cut's facts at the call's memory *)
    pose proof (onwk_cur_keep HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw
      Bw' pos sp1 F ly2 S2 W2 mem2 mW md2 mdW e HFIX HCUR0 HJ2 KW GW) as CURW.
    pose proof CURW as (_ & _ & _ & _ & _ & _ & KCw & HSVw & HFLw).
    unfold ONANN_FBYTES in HFLw.
    (* diginet_session_wake's premises *)
    assert (NSP : spZ rW = sp1) by (unfold spZ; rewrite Z2; unfold w64; apply unsigned_lit_small; lia).
    assert (EBR : BASE + 28356 = 0x88164) by (vm_compute; reflexivity).
    assert (Pret : YK0s.ret_ok (YK11.getr rW 1))
      by (rewrite Z1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity]).
    assert (Pra4 : 4096 <= raZ rW) by (unfold raZ; rewrite Z1, EBR, unsigned_lit_small by lia; lia).
    assert (Pgp : YK11.getr rW 3 = w64 (as_gp B)) by (rewrite Z3; exact Hgp).
    assert (Ptp : YK11.getr rW 4 = w64 (as_tp B)) by (rewrite Z4; exact Htp).
    assert (Pa0 : YK11.getr rW 10 = w64 WAKE_S) by (rewrite Z10; reflexivity).
    assert (Pa1 : YK11.getr rW 11 = w64 now) by exact Z11.
    assert (Psp16 : spZ rW mod 16 = 0) by (rewrite NSP; exact Hsp116).
    assert (Pwin1 : sp0 - STK <= spZ rW - WAKE_STK) by (rewrite NSP; lia).
    assert (Pwin2 : spZ rW <= sp0) by (rewrite NSP; lia).
    assert (Pt1 : spZ regs - ONANN_STK <= spZ rW - WAKE_STK) by (rewrite NSP; lia).
    assert (Pt2 : spZ rW <= spZ regs) by (rewrite NSP; lia).
    assert (Ptw : tw_at TMAP_B (aview segs (w_H W2) mW) B4).
    { apply (tw_kept_GB (aview segs (w_H W2) mem2)); [exact Htw4|]. intros b0 n i Hbn Hi.
      assert (Hg : inG TG.G_HARNESS_B (b0 + i))
        by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
      pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
      apply KW. lia. }
    pose proof (onann_tf_cur B MT HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw
      Bw' pos sp1 F ly2 S2 W2 mW mdW e rW WAKE_STK HFIX CURW Pt1 Pt2) as Ptf.
    pose proof (onann_rom_cur B MT HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF
      Bw Bw' pos sp1 F ly2 S2 W2 mW mdW e HFIX CURW) as Prom.
    pose proof (onann_apart_wake TF Bw b B4 Hapart) as Pap.
    destruct Hri4 as (Pri1 & Pri4 & _).
    assert (Pcnt1 : count_cid WAKE_CID (frames S2) < fs_frames WAKE_CID).
    { rewrite Hfrs, onwk_count by (unfold WAKE_CID, ONANN_CID; discriminate). exact Hc1. }
    assert (Pcnt2 : count_cid SENDCTL_CID (frames S2) + 1 < fs_frames SENDCTL_CID).
    { rewrite Hfrs, onwk_count by (unfold SENDCTL_CID, ONANN_CID; discriminate). exact Hc2. }
    assert (Pnev : st_nev S + (k + e) + WAKE_EV <= EV_MAX) by lia.
    (* +0x498: diginet_session_wake, in the same G journal *)
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (@cfg_at fx sg (transportb_sigma TB_diginet_session_wake) rg mm mdx) Q) end.
    eapply SRr_bind.
    { exact (HWAKE fx STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mW mdW (k + e) rW now r' TF B4 B5
        HJ2 Pret Pra4 Pgp Ptp Pa0 Pa1 Psp16 Pwin1 Pwin2 Hnow Ptw Hgf4 Pmod Ptf Hoff Prom Pap Pri1 Pri4 Pcnt1 Pcnt2
        Pnev). }
    intros W3 c3 _ HPOST.
    unfold transport_wake_post, transport_cg_post in HPOST.
    destruct HPOST as (ly3 & S3 & regs5 & mem5 & md6 & e' & -> & He' & HJ6 & HP6 & Hfr6 & Hperm6 & HK6 & Hmo6 & _ &
      Htw6 & Hgf6).
    rewrite NSP in HK6.
    (* the state diginet_session_wake returned: the cut's facts there *)
    assert (ELF3 : ly_F ly3 = ly_F lyc).
    { pose proof HJe as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hlyc & _).
      pose proof HJ6 as (_ & _ & (memS6 & HJ6i & _) & _). pose proof HJ6i as (_ & Hly3 & _).
      pose proof Hly3 as (_ & _ & _ & _ & _ & E3 & _). pose proof Hlyc as (_ & _ & _ & _ & _ & Ec & _).
      rewrite E3, Ec. reflexivity. }
    destruct (TransportGFrame.dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F
      (flag_addr lyc ONANN_CID pos) HAR2 Hfrs Hbl2 HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
    assert (K5 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem5 (spZ regs - ONANN_STK) (spZ regs)
      (onann_wr Bw b)).
    { assert (Hce1 : alloc_ceiling <= spZ regs - ONANN_STK) by lia.
      assert (Hlo1 : spZ regs <= 2 ^ 64) by lia.
      apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 mW W3 mem5
        (spZ regs - ONANN_STK) (spZ regs) (sp1 - WAKE_STK) sp1 (onann_wr Bw b)
        (wake_wr B4) (dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos))
        Hce1 Hlo1 EFa ltac:(intros f Hf; rewrite Hfrs; right; exact Hf) Hbl2 N1 N3 KCw HK6).
      - lia.
      - lia.
      - intros a Ha. left. exact (onann_wr_wake B4 Bw b a Ha). }
    assert (HSV5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem5) (spZ regs - fst o) =
        Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
    { apply Forall_forall. intros o Hin. cbv beta.
      pose proof (proj1 (Forall_forall _ _) HSVw o Hin) as Hv. cbv beta in Hv.
      assert (Ho : 8 <= fst o <= 104).
      { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
        repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
      rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. destruct HK6 as (L1 & _). apply L1; lia. }
    assert (HFL5 : rdword (aview segs (w_H W3) mem5) (F + 512 - 8) = Some (flag_addr lyc ONANN_CID pos)).
    { rewrite <- HFLw. apply YCbq.rdword_ext. intros i Hi. destruct HK6 as (_ & _ & _ & L4 & _).
      apply (L4 ONANN_CID pos (F + 512 - 8 + i) Hin2).
      - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA2. change (fs_frame_bytes ONANN_CID) with 512. lia.
      - intros Hw. exact (FNG (F + 512 - 8 + i) ltac:(lia) (onann_wake_wr_G _ _ Hw)). }
    rewrite Z1.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONWK_RET)) mm rom) mdx) Q) end.
    apply (onwk_join NREL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
      pos sp1 F ly3 S3 W3 mem5 md6 (e + e') regs5 HFIX).
    * unfold onann_rel_cur, onann_cur.
      refine (conj (conj _ (conj _ (conj _ (conj _ (conj ELF3 (conj _ (conj K5 (conj HSV5 _))))))))
        (conj _ _)).
      -- replace (k + (e + e')) with (k + e + e') by lia. exact HJ6.
      -- lia.
      -- rewrite Hfr6. exact Hfrs.
      -- exact (Permutation_trans Hperm6 Hperm).
      -- exact (mo_le_trans MT MTL Sc S2 S3 0 0 Hmo Hmo6).
      -- unfold ONANN_FBYTES. exact HFL5.
      -- rewrite EBw'. exact Htw6.
      -- rewrite EBw'. exact Hgf6.
    * unfold onann_regs_rel.
      split; [exact (eq_trans (HP6 2 ltac:(hnf; lia)) Z2)|].
      split; [exact (eq_trans (HP6 3 ltac:(hnf; lia)) Z3)|].
      split; [exact (eq_trans (HP6 4 ltac:(hnf; lia)) Z4)|].
      split; [exact (eq_trans (HP6 8 ltac:(hnf; lia)) Z8)|].
      split; [exact (eq_trans (HP6 9 ltac:(hnf; lia)) Z9)|].
      split; [exact (eq_trans (HP6 18 ltac:(hnf; lia)) Z18)|].
      split; [exact (eq_trans (HP6 19 ltac:(hnf; lia)) Z19)|].
      exact (eq_trans (HP6 25 ltac:(hnf; lia)) Z25).
Qed.
End main.

Print Assumptions onann_wk_piece.
