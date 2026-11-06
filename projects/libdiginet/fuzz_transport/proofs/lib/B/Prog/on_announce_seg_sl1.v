(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 648 of its 734 lines of code are new or changed and 679 lines of the source are left out. *)
(* on_announce_seg_sl1: Lemma onann_sl1_piece : onann_sl1_stmt (lib/B/Prog/OnannCutB.v), the first inlined
   session_lost of the walk of on_announce on fuzz_transport.asan-ubsan, offsets +0x424 .. +0x46c of the listing
   lib/B/Prog/DgnTransportBList.v (AF_on_announce = 0x6a28; 0x880ec .. 0x88134), then the wake cut ONANN_WK (+0x470,
   0x88138), which the onann_wk_at it is given closes.

   What the code does (diginet_session.c:203, session_lost :162-164 inlined; image B CALLS set_state).
     +0x424 .. +0x438  `addi a0, s4, 212`, the shadow byte of s + 212 through s8 (`lb`; 0: g_s's payload lies in the
                       record's zero shadow, on_announce_cg.v trans_onann_cells, read by DgnTransportBCg.v
                       decode_zshadow_rd), `bne` to the slow path not taken, `sw zero, 212(s4)` (inflight);
     +0x43c .. +0x450  the same check of s + 168 and `sw zero, 168(s4)` (desk_counter_valid): the world is now
                       slost_w1 Bx (diginet_session_tick_cg.v), Bx = set_S_foreign B2 0;
     +0x454 .. +0x460  a2 = 3 (DIGINET_R_DESK_OFFLINE), a0 = s, a1 = 0 (S_IDLE), `jal set_state` (0x872cc =
                       transportb_sigma TB_set_state), return address +0x464 (0x8812c);
     +0x464 .. +0x46c  `lb a0, 0(s10)` (the shadow byte of s + 112, 0), `bne` not taken, `lw a0, 0(s6)`: a0 = S_state
                       of set_state's world B4, sign-extended; the wake cut at +0x470.
   The runs are the token engine's over the caller's G journal (lib/B/Prog/TransportGRunB.v):
     run S    +0x424 .. the `jal`  two written regions over s4 (atom 20, pinned to ONANN_S with alignment 2 ^ 6):
                                   [s + 212, s + 216) and [s + 168, s + 172), bytes of G (W_journalG.v
                                   awr_ok_x_cons_g); the shadow entry of [s + 168, s + 216); s8 = atom 24, the
                                   shadow base. The world relation goes to slost_w1 Bx by two TWorldG.v tw_write.
     the call                      set_state_cg.v transport_set_state_cg at transportb_sigma TB_set_state, a G-form
                                   callee in the same journal: the cut's facts moved to the run's memory
                                   (TransportGFrame.dk_kept_step_gw over the two fields, rows of onann_wr), then TF
                                   and the read-only bytes there by on_announce_seg_kit.v onann_tf_cur /
                                   onann_rom_cur; the model by diginet_session_tick_cg.v slost_model_sstate
                                   (osl_k_sl1); sstate_apart by onann_apart_sstate (sstate_wr reads its world
                                   through S_state and GOT.n only, which Bx shares with Bw: the onann_same lemmas); the
                                   class-2 count from the count premise (the own frame is of class 3).
     run R    +0x464 .. +0x470     two read regions: the shadow byte at s10 (value 0), the 4 bytes of S_state at s6
                                   (atom 32, read off B4 by TWorldG.v tw_read_val); it stops at the wake cut.
   set_state's post folds into onann_cur by TransportGCg.v dk_kept_trans_nf_g (its written range sstate_wr
   (slost_w1 Bx) S_IDLE 3 is a row of onann_wr: onann_wr_slost), the 13 saved words by its window clause and the frame's
   last word by its frame clause (no byte of the own frame is a byte of G). The run invariants carry to B4:
   slost_w1 and set_state's store of the state are g_s stores (onann_ri_upd); its N_STATE notice stores GOT.t[GOT.n]
   and GOT.n, above g_cmd's 1024 entries and g_ncmd, which onann_ri's index bound keeps out of reach (osl_ri_hi,
   osl_ri_ntc, osl_ri_sstate). g_fail_next B4 <= 1 is set_state's X.
   Trap and error paths on this piece: the slow paths of the checks of s + 212, s + 168 (store4) and s + 112 (load4):
   the shadow bytes are 0 (trans_onann_cells). No UBSan trap word on this piece. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model and the worlds on this piece                           *)
(* ------------------------------------------------------------------ *)

(* set_state's return address (+0x464), where run R starts. *)
Definition OSL_RET : Z := AF_on_announce + 0x464.

(* The rest of the model at the cut (OnannCutB.v onann_k_sl1): set_state's step of session_lost at slost_w1 Bx with
   S_IDLE and R_DESK_OFFLINE (diginet_session_tick_cg.v slost_model_sstate), then onann_k_wk at its world B4. *)
Lemma osl_k_sl1 : forall (TF : option TI.tframe) Bx now Bw',
  onann_k_sl1 timg_B TF Bx now = Some (Bw', tt) ->
  exists B4, TSS.set_state_m timg_B TF (slost_w1 Bx) TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_OFFLINE = Some (B4, tt) /\
             onann_k_wk timg_B TF B4 now = Some (Bw', tt).
Proof.
intros TF Bx now Bw' H. unfold onann_k_sl1 in H. rewrite slost_model_sstate in H.
destruct (TSS.set_state_m timg_B TF (slost_w1 Bx) TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_OFFLINE) as [[B4 u]|] eqn:E;
  rewrite ?E in H; [|discriminate H].
destruct u. exists B4. split; [rewrite ?E; reflexivity | exact H].
Qed.

(* The two stores of :162-163 and set_state's store of the state at their numeral offsets. *)
Lemma osl_w1_eq : forall X,
  slost_w1 X = TW.upd (TW.upd X (TW.OFF_g_s + 212) (TW.put 4 0)) (TW.OFF_g_s + 168) (TW.put 4 0).
Proof. intros X. reflexivity. Qed.
Lemma osl_sw_eq : forall X,
  sstate_w X TS0.DIGINET_S_IDLE = TW.upd X (TW.OFF_g_s + 112) (TW.put 4 TS0.DIGINET_S_IDLE).
Proof. intros X. reflexivity. Qed.

(* The two stores keep g_fail_next and the run invariants (g_s stores). *)
Lemma osl_w1_facts : forall X, length X = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (slost_w1 X) = TW.g_fail_next X /\ (onann_ri (slost_w1 X) <-> onann_ri X).
Proof.
intros X LX.
assert (L1 : length (TW.upd X (TW.OFF_g_s + 212) (TW.put 4 0)) = Z.to_nat TW.W_LEN)
  by (apply onann_upd_len; [exact LX | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_s, TW.W_LEN; lia]).
rewrite osl_w1_eq. split.
- rewrite (onann_gfn_upd _ (TW.OFF_g_s + 168) 4 0 L1) by (left; unfold TW.OFF_g_s, TW.SZ_g_s; lia).
  apply (onann_gfn_upd X (TW.OFF_g_s + 212) 4 0 LX). left; unfold TW.OFF_g_s, TW.SZ_g_s; lia.
- rewrite (onann_ri_upd _ (TW.OFF_g_s + 168) 4 0 L1) by (unfold TW.OFF_g_s, TW.SZ_g_s; lia).
  apply (onann_ri_upd X (TW.OFF_g_s + 212) 4 0 LX); unfold TW.OFF_g_s, TW.SZ_g_s; lia.
Qed.

(* A store at or above GOT keeps the run invariants: it lies above g_ncmd, and onann_ri's index bound keeps every
   Cmd_st s / Cmd_len s it reads inside g_cmd's 1024 entries, below g_q. *)
Lemma osl_ri_hi : forall X k (n : nat) v, length X = Z.to_nat TW.W_LEN ->
  64988 <= k -> k + Z.of_nat n <= TW.W_LEN ->
  onann_ri X -> onann_ri (TW.upd X k (TW.put n v)).
Proof.
intros X k n v LX Hk Hkn (R1 & R4 & RN).
assert (LZ : Z.of_nat (length X) = TW.W_LEN) by (rewrite LX; unfold TW.W_LEN; lia).
assert (LP : Z.of_nat (length (TW.put n v)) = Z.of_nat n) by (rewrite TWL.length_put; reflexivity).
unfold TW.W_LEN in LZ, Hkn.
assert (EN : TW.g_ncmd (TW.upd X k (TW.put n v)) = TW.g_ncmd X).
{ unfold TW.g_ncmd, TW.OFF_g_ncmd. apply TWL.u_at_upd_out; rewrite ?LP; lia. }
split; [|split].
- assert (E1 : TW.M_fly_on (TW.upd X k (TW.put n v)) = TW.M_fly_on X).
  { unfold TW.M_fly_on, TW.A_M_fly_on, TW.OFF_M. apply TWL.s32_at_upd_out; rewrite ?LP; lia. }
  assert (E2 : TW.M_fly_len (TW.upd X k (TW.put n v)) = TW.M_fly_len X).
  { unfold TW.M_fly_len, TW.A_M_fly_len, TW.OFF_M. apply TWL.u_at_upd_out; rewrite ?LP; lia. }
  rewrite E1, E2. exact R1.
- intros s Hs Hst. rewrite EN in Hs.
  assert (Hs1 : s < 1024) by (unfold TC.CMDS_MAX in RN; lia).
  assert (Est : TW.Cmd_st (TW.upd X k (TW.put n v)) s = TW.Cmd_st X s).
  { unfold TW.Cmd_st, TW.A_Cmd_st, TW.OFF_g_cmd. apply TWL.s32_at_upd_out; rewrite ?LP; lia. }
  assert (Eln : TW.Cmd_len (TW.upd X k (TW.put n v)) s = TW.Cmd_len X s).
  { unfold TW.Cmd_len, TW.A_Cmd_len, TW.OFF_g_cmd. apply TWL.u_at_upd_out; rewrite ?LP; lia. }
  rewrite Est in Hst. rewrite Eln. exact (R4 s Hs Hst).
- rewrite EN. exact RN.
Qed.

(* The length of a world after stores inside it. *)
Ltac osl_len L :=
  repeat (apply onann_upd_len; [| unfold TW.W_LEN; lia | unfold TW.W_LEN; lia]); exact L.

(* An N_STATE notice whose new state is not S_ONLINE (TCb.v notice_m: GOT.t[GOT.n] when 0 <= GOT.n < TRANS_MAX,
   then GOT.n) keeps the run invariants. *)
Lemma osl_ri_ntc : forall I F Y (n : TI.ntc) Y', TI.n_kind n = TC.N_STATE -> TI.n_state n = 0 ->
  length Y = Z.to_nat TW.W_LEN -> TC.notice_m I F Y n = Some (Y', tt) -> onann_ri Y -> onann_ri Y'.
Proof.
intros I F Y n Y' K Hs0 L H HR.
unfold TC.notice_m in H. rewrite K in H. cbn [Z.eqb TC.N_STATE Pos.eqb] in H.
set (g := TW.GOT_n Y) in H.
destruct (TI.n_state n =? TC.S_ONLINE) eqn:ES; rewrite ?ES in H.
{ rewrite Hs0 in ES. vm_compute in ES. discriminate ES. }
destruct (g <? TC.TRANS_MAX) eqn:E1; rewrite ?E1 in H.
- destruct (g <? 0) eqn:E2; rewrite ?E2 in H; [discriminate H|].
  destruct (TC.int_inc g) as [g1|] eqn:E3; rewrite ?E3 in H; [|discriminate H].
  apply Z.ltb_lt in E1. apply Z.ltb_ge in E2. unfold TC.TRANS_MAX in E1.
  clear ES.
  cbv beta iota zeta in H. pose proof (onann_some_inv _ _ H) as EY. rewrite <- EY.
  unfold TW.set_GOT_n, TW.set_GOT_t_reason, TW.set_GOT_t_old, TW.set_GOT_t_state, TW.A_GOT_n, TW.A_GOT_t_reason,
    TW.A_GOT_t_old, TW.A_GOT_t_state, TW.OFF_GOT.
  apply osl_ri_hi; [osl_len L | lia | unfold TW.W_LEN; lia |].
  apply osl_ri_hi; [osl_len L | lia | unfold TW.W_LEN; lia |].
  apply osl_ri_hi; [osl_len L | lia | unfold TW.W_LEN; lia |].
  apply osl_ri_hi; [osl_len L | lia | unfold TW.W_LEN; lia |].
  exact HR.
- destruct (TC.int_inc g) as [g1|] eqn:E3; rewrite ?E3 in H; [|discriminate H].
  clear ES.
  cbv beta iota zeta in H. pose proof (onann_some_inv _ _ H) as EY. rewrite <- EY.
  unfold TW.set_GOT_n, TW.A_GOT_n, TW.OFF_GOT.
  apply osl_ri_hi; [exact L | lia | unfold TW.W_LEN; lia |].
  exact HR.
Qed.

(* set_state's world from a world in state S_ONLINE keeps the run invariants: its store of the state is a g_s
   store, its notice osl_ri_ntc's. *)
Lemma osl_ri_sstate : forall (TF : option TI.tframe) X B4, length X = Z.to_nat TW.W_LEN ->
  TW.S_state X = TS0.DIGINET_S_ONLINE -> onann_ri X ->
  TSS.set_state_m timg_B TF X TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_OFFLINE = Some (B4, tt) -> onann_ri B4.
Proof.
intros TF X B4 LX HS HR H.
rewrite sstate_model in H.
destruct (TW.S_state X =? TS0.DIGINET_S_IDLE) eqn:EZ; rewrite ?EZ in H.
{ rewrite HS in EZ. vm_compute in EZ. discriminate EZ. }
unfold TSS.call_notify in H.
destruct (TW.S_notify (sstate_w X TS0.DIGINET_S_IDLE) =? TI.ti_notice timg_B) eqn:EN; rewrite ?EN in H;
  [|discriminate H].
assert (LY : length (sstate_w X TS0.DIGINET_S_IDLE) = Z.to_nat TW.W_LEN).
{ rewrite osl_sw_eq. apply onann_upd_len; [exact LX | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_s, TW.W_LEN; lia]. }
apply (osl_ri_ntc timg_B TF (sstate_w X TS0.DIGINET_S_IDLE)
  (sstate_ntc X TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_OFFLINE) B4 eq_refl eq_refl LY H).
rewrite osl_sw_eq.
apply (proj2 (onann_ri_upd X (TW.OFF_g_s + 112) 4 TS0.DIGINET_S_IDLE LX ltac:(unfold TW.OFF_g_s; lia)
  ltac:(unfold TW.OFF_g_s, TW.SZ_g_s; lia))).
exact HR.
Qed.

(* The world relation after the stores of 0 at s + 212 and s + 168 (two tw_write). *)
Lemma osl_tw_w1 : forall (rd rd' : Z -> option Z) X,
  tw_at TMAP_B rd X ->
  (forall j, (j < 4)%nat -> rd' (TB_g_s + 212 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_s + 168 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_g_s + 212 <= x < TB_g_s + 216) -> ~ (TB_g_s + 168 <= x < TB_g_s + 172) ->
     rd' x = rd x) ->
  tw_at TMAP_B rd' (slost_w1 X).
Proof.
intros rd rd' X Hat HI HD HO.
set (rdm := fun x => if ((TB_g_s + 168 <=? x) && (x <? TB_g_s + 172))%bool then rd x else rd' x).
assert (H1 : tw_at TMAP_B rdm (TW.upd X (TW.OFF_g_s + 212) (TW.put 4 0))).
{ apply (tw_write TMAP_B rd rdm X TW.OFF_g_s TB_g_s TW.SZ_g_s 212 4 0 TMAP_B_ok Hat TMAP_B_g_s);
    [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. unfold rdm.
    assert (Hb : ((TB_g_s + 168 <=? TB_g_s + 212 + Z.of_nat j) && (TB_g_s + 212 + Z.of_nat j <? TB_g_s + 172))%bool
      = false) by (apply andb_false_iff; right; apply Z.ltb_ge; lia).
    rewrite Hb. exact (HI j Hj).
  - intros x Hx Hn. unfold rdm.
    destruct ((TB_g_s + 168 <=? x) && (x <? TB_g_s + 172))%bool eqn:Eb; [reflexivity|].
    apply andb_false_iff in Eb.
    apply HO; [exact Hx | lia |].
    destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia. }
rewrite osl_w1_eq.
apply (tw_write TMAP_B rdm rd' _ TW.OFF_g_s TB_g_s TW.SZ_g_s 168 4 0 TMAP_B_ok H1 TMAP_B_g_s);
  [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. exact (HD j Hj).
- intros x Hx Hn. unfold rdm.
  destruct ((TB_g_s + 168 <=? x) && (x <? TB_g_s + 172))%bool eqn:Eb; [|reflexivity].
  apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  exfalso. apply Hn. lia.
Qed.

(* S_state at its numeral offset (OFF_g_s + 112), its range, and the sign-extended 4-byte load of it. *)
Lemma osl_state_at : forall X, TW.S_state X = bv_swrap 32 (TW.u_at X (TW.OFF_g_s + 112) 4).
Proof. intros X. reflexivity. Qed.

Lemma osl_sext : forall E X, ew E 32 = Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_state X).
Proof.
intros E X H.
assert (R : 0 <= TW.u_at X (TW.OFF_g_s + 112) 4 < 2 ^ 32) by exact (TWL.u_at_range X _ 4).
cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. rewrite osl_state_at. reflexivity.
Qed.

(* The bytes the run S writes: g_s.inflight and g_s.desk_counter_valid. *)
Definition osl_Z (x : Z) : Prop :=
  ONANN_S + 212 <= x < ONANN_S + 216 \/ ONANN_S + 168 <= x < ONANN_S + 172.

(* g_s's payload bytes are bytes of G. *)
Lemma osl_inG : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, ONANN_S, TB_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

Lemma osl_Z_G : forall a, osl_Z a -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply osl_inG. unfold osl_Z in Ha. unfold TW.SZ_g_s. lia. Qed.

(* ... and rows of onann_wr (the inlined session_lost's two stores). *)
Lemma osl_Z_wr : forall Bw b a, osl_Z a -> onann_wr Bw b a.
Proof.
intros Bw b a [Ha | Ha].
- apply onann_wr_inflight. unfold twb_fld, TW.A_S_inflight, TW.OFF_g_s. unfold ONANN_S in Ha. lia.
- apply onann_wr_dcv. unfold twb_fld, TW.A_S_desk_counter_valid, TW.OFF_g_s. unfold ONANN_S in Ha. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* run S at +0x424: g_s's inflight and desk_counter_valid at s4 (atom 20, written); s4 = s, s8 = the shadow base;
   the shadow entry of the two checks. *)
Definition osl_rg_if : YP09.region := YP09.mkRegion (Some 20%nat) 212 216 212 216 [].
Definition osl_rg_dc : YP09.region := YP09.mkRegion (Some 20%nat) 168 172 168 172 [].
Definition osl_facts_s : facts :=
  mkFacts [(20%nat, mkAF ONANN_S ONANN_S 6); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_osls : sstate := mkSS ONANN_SL1 sr_atoms [osl_rg_if; osl_rg_dc] None osl_facts_s.
Definition OSL_SH : list shent := [mkSHE 20 168 216].
Definition OSL_BX : sv := SOff 24 0.
(* run R at +0x464: the shadow byte of s + 112 at s10 (atom 26, read, 0); the 4 bytes of S_state at s6 (atom 22,
   read, atom 32). No shadow token: the span (0, 0). *)
Definition OSL_B0 : Z * Z := (0, 0).
Definition osl_rg_sh : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SLit 0))].
Definition osl_rg_st : YP09.region := YP09.mkRegion (Some 22%nat) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 32 0))].
Definition osl_facts_r : facts := mkFacts [(32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_oslr : sstate := mkSS OSL_RET sr_atoms [osl_rg_sh; osl_rg_st] None osl_facts_r.

(* The register and region readers of a symbolic state (lib/B/Prog/DgnTransportBPaLib.v's forms). *)
Ltac osl_reg HS r v H tac :=
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
   value): the run's valuation agrees with the start valuation below atom 1024 (Elo), which reads the registers
   (EE). *)
Ltac osl_kreg_of HS Elo EE r n rn Q H :=
  lazymatch type of Q with _ = ?v =>
    osl_reg HS r v H
      ltac:(cbn [sv_denot]; try rewrite (Elo n ltac:(lia)); rewrite (EE n rn eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
            exact Q) end.
Ltac osl_kreg HS Elo EE r n Q H := osl_kreg_of HS Elo EE r n r Q H.
Ltac osl_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac osl_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac osl_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The model of the goal, named. *)
Ltac osl_name_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md := m) in *; clearbody md end.
(* After a run: its valuation agrees with the start valuation E0 below atom 1024 (Hlo), and its machine state is
   named m. *)
Ltac osl_lo HS E0 Hlo m :=
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

(* The valuations: the 32 registers (and, for run R, atom 32 = the 4 bytes of S_state of the world X). *)
Definition osl_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).
Definition osl_Ea (regs : bvmap 5 word) (X : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4)]).

Lemma osl_ew : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (osl_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold osl_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma osl_ewa : forall regs X n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (osl_Ea regs X) n = YK11.getr regs r.
Proof. intros regs X n r Hn. unfold osl_Ea. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma osl_ewa32 : forall regs X, ew (osl_Ea regs X) 32 = Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4).
Proof. intros regs X. unfold osl_Ea. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.

(* The bytes of a value in memory, read byte by byte through the view. *)
Lemma osl_aview_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v -> forall j, (j < n)%nat ->
  aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* One byte read off the view, in val_mem's form. *)
Lemma osl_val_mem1 : forall H (m : word -> option byte) a v,
  aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [x|]; [|discriminate Hv].
cbn [option_map] in Hv. injection Hv as <-. f_equal. apply bv_eq.
pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256 in R.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (bv_unsigned x) 256 R). reflexivity.
Qed.

(* g_s's bytes [s + 168, s + 216) are addressable at every AR state: whole granules of the record's zero shadow. *)
Lemma osl_ra : forall ly S (W : world segs) mem md,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (ONANN_S + 168) 48.
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

(* The symbolic state at +0x424 holds of the machine state there, and the run's shadow entry holds. *)
Lemma osl_entry_s : forall ly S (W : world segs) regs mem md,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (osl_E regs) ss_osls
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_SL1)) mem (YK11.seg_rom segs))) /\
  sh_ok segs OSL_BX OSL_SH (osl_E regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md HSC HAR R20 R24.
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (U20 : bv_unsigned (ew (osl_E regs) 20) = ONANN_S)
  by (rewrite (osl_ew regs 20 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew (osl_E regs) 24) = SHADOW_OFF)
  by (rewrite (osl_ew regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_osls.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [osl_rg_if osl_rg_dc YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite U20; (split; [lia|]); (split; [lia|]); (split; [|constructor]);
      intros o Ho; apply (gx_rw_writable segs TG.G_HARNESS_B (ONANN_S + o) G_HARNESS_B_rw);
      apply osl_inG; unfold TW.SZ_g_s; lia.
  + apply pairwise_disjoint_of_extents.
    unfold osl_rg_if, osl_rg_dc, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U20. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + unfold osl_facts_s, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U24.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (osl_ra ly S W mem md HSC HAR) as HRA.
  assert (UB : U (osl_E regs) OSL_BX = SHADOW_OFF).
  { unfold U, OSL_BX. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, OSL_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ OSL_BX 20 (ONANN_S + 168) 48 ONANN_S 168 216 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The symbolic state at +0x464 holds of the machine state there (the world X: set_state's B4). *)
Lemma osl_entry_r : forall ly S (W : world segs) regs mem md X,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) X ->
  YK11.getr regs 22 = w64 (ONANN_S + 112) -> YK11.getr regs 26 = w64 (SHADOW_OFF + (ONANN_S + 112) / 8) ->
  st_ok_pi segs VAL (osl_Ea regs X) ss_oslr
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OSL_RET)) mem (YK11.seg_rom segs))).
Proof.
intros ly S W regs mem md X HSC HAR Htw R22 R26.
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (E26 : SHADOW_OFF + (ONANN_S + 112) / 8 = 2148220630) by reflexivity.
rewrite E26 in R26.
assert (U22 : bv_unsigned (ew (osl_Ea regs X) 22) = ONANN_S + 112)
  by (rewrite (osl_ewa regs X 22 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew (osl_Ea regs X) 26) = 2148220630)
  by (rewrite (osl_ewa regs X 26 26%bv eq_refl), R26; apply unsigned_lit_small; lia).
assert (R32 : 0 <= TW.u_at X (TW.OFF_g_s + 112) 4 < 2 ^ 32) by exact (TWL.u_at_range X _ 4).
assert (U32 : bv_unsigned (ew (osl_Ea regs X) 32) = TW.u_at X (TW.OFF_g_s + 112) 4)
  by (rewrite osl_ewa32; apply unsigned_lit_small; lia).
assert (Hs : aview segs (w_H W) mem 2148220630 = Some 0).
{ pose proof (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) (ONANN_S + 112) HAR
    ltac:(rewrite CS; reflexivity) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) HSC) as H.
  replace 2148220630 with (FCells.shadow_addr (ONANN_S + 112)) by reflexivity. exact H. }
rewrite restrict_mkst_fx. unfold ss_oslr.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks osl_rg_sh osl_rg_st base_val];
    rewrite ?U22, ?U26.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ 2148220630 0 1 (SLit 0) 0); [reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (osl_val_mem1 _ _ _ _ Hs).
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ (ONANN_S + 112) 0 4 (SOff 32 0) (TW.u_at X (TW.OFF_g_s + 112) 4));
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | lia |].
    replace (ONANN_S + 112 + 0) with (TB_g_s + 112) by reflexivity.
    exact (tw_read_val segs _ TMAP_B X TW.OFF_g_s TB_g_s TW.SZ_g_s 112 4 TMAP_B_ok Htw TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, osl_rg_sh, osl_rg_st. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U22, U26. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold osl_facts_r, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
End ent.

(* ------------------------------------------------------------------ *)
(* 3. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma onann_sl1_piece : @onann_sl1_stmt fx rc B MT.
Proof.
unfold onann_sl1_stmt, onann_sl1_at.
intros WK HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  B2 ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof HLAWS as (_ & _ & HSC & _ & _ & _ & _ & LAWS & MTL & _ & _ & _ & FFL & HGX & _).
pose proof HCALL as (_ & _ & _ & _ & _ & _ & HSST & _ & _ & _).
pose proof HFIX as (HJe & _ & _ & Hgp & Htp & _ & _ & _ & Hsp16 & Hwin1 & Hwin2 & _ & _ & Htw0 & _ & _ & _ & _ & _ &
  Hapart & _ & _ & _ & Hc2 & Hnev & _ & EF & _ & _ & _ & _).
pose proof HCUR as (HCUR0 & Htw2 & Hb2 & Hst & Hk & Hgf2 & Hri2).
pose proof HCUR0 as (HJ1 & He & Hfrs & Hperm & HlyF & Hmo & HK & HSV & HFL).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25) & R20 & R24) & R21 & R22 & R26).
destruct (onann_cur_ar B MT LAWS HFIX HCUR0) as (HARc & HAR2 & Elo2 & Ehi2 & EFAll & EFLall & Hin2 & EFA2 &
  HFpres & HFSpres & FNG & HF4096 & HF64 & HFc & HFapp & Hceil & Hslo & Hshi & H47 & HFLp & HFLo & HFLb & HFLs1 &
  HFLs2 & Hsp1 & Hsp132 & Hsp146).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (CS' : ONANN_S = TB_g_s) by reflexivity.
unfold ONANN_FBYTES in HFL.
assert (HBS : 4304 <= ONANN_STK).
{ unfold ONANN_STK, ONANN_FRAME, ONANN_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
assert (HSTK : SSTATE_STK + 352 <= ONANN_STK).
{ rewrite onann_stk_eq. unfold ONANN_FRAME, ONANN_ALIGN, WAKE_STK, WAKE_FRAME, WAKE_ALIGN. lia. }
assert (EVS : SSTATE_EV = 0) by reflexivity.
assert (EVO : ONANN_EV = WAKE_EV) by reflexivity.
assert (EVW : 0 <= WAKE_EV) by (vm_compute; intro HH; discriminate HH).
assert (Hsp : alloc_ceiling <= spZ regs - ONANN_STK /\ spZ regs <= 2 ^ 47) by lia.
destruct Hsp as [Hspc Hsp47].
assert (Hsp116 : sp1 mod 16 = 0).
{ pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp132, Z.add_0_r in D. rewrite D.
  replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
(* the worlds: Bx = set_S_foreign B2 0 shares Bw's state and GOT.n *)
destruct Hb2 as (_ & d & EB2).
pose proof (tw_len _ _ _ Htw0) as LBw.
pose proof (tw_len _ _ _ Htw2) as LBx.
assert (HSAME : onann_same Bw (TW.set_S_foreign B2 0)).
{ rewrite EB2. pose proof (onann_w1_len timg_B Bw b LBw) as L1.
  pose proof (onann_same_desk (onann_w1 timg_B Bw b) d L1) as SD.
  pose proof SD as (L2 & _). rewrite L1 in L2.
  exact (onann_same_trans _ _ _ (onann_same_trans _ _ _ (onann_same_w1 timg_B Bw b LBw) SD)
    (onann_same_foreign _ 0 L2)). }
destruct HSAME as (_ & ESt & _ & _ & _ & _ & EGn & _ & _).
set (Bx := TW.set_S_foreign B2 0) in *.
clearbody Bx. clear EB2 HCUR.
(* the model: set_state's world B4 *)
destruct (osl_k_sl1 TF Bx now Bw' Hk) as (B4 & EB4 & Hk4).
pose proof (onann_sl_len Bx LBx) as L1x.
pose proof (osl_w1_facts Bx LBx) as (Egf1 & Eri1).
assert (Hst1 : TW.S_state (slost_w1 Bx) = TS0.DIGINET_S_ONLINE) by (rewrite (onann_sl_state Bx LBx); exact Hst).
assert (Pgf : TW.g_fail_next (slost_w1 Bx) <= 1) by (rewrite Egf1; exact Hgf2).
pose proof (osl_ri_sstate TF (slost_w1 Bx) B4 L1x Hst1 (proj2 Eri1 Hri2) EB4) as Hri4.
(* the own frame, apart from the call's blocks, image and frames *)
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (TransportGFrame.dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F
  (flag_addr lyc ONANN_CID pos) HAR2 Hfrs Hbl2 HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
(* run S, +0x424 .. +0x460: the checked stores of 0 at s + 212 and s + 168, a2 = 3, a0 = s, a1 = 0, `jal set_state` *)
destruct (osl_entry_s (fx := fx) B ly2 S2 W2 regs2 mem2 md2 HSC HAR2 R20 R24) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (osl_E regs2)) by (unfold osl_E; apply Eimg_env).
assert (EES : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (osl_E regs2) n = YK11.getr regs2 r)
  by (intros n r Hn; exact (osl_ew regs2 n r Hn)).
assert (U20s : bv_unsigned (ew (osl_E regs2) 20) = ONANN_S)
  by (rewrite (EES 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
pose proof HJ1 as HJ.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ osl_awr_rs.
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20s in Ha;
    apply osl_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20s in Ha;
    apply osl_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_nil. }
rename HF into HFs, HFr into HFrs, HG into HGs.
osl_name_md mdS.
osl_lo HS (osl_E regs2) ESlo msS.
(* the registers at set_state's entry, and the ones the code after it reads *)
osl_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 28300)) Y1 ltac:(apply codeptr_val; assumption).
osl_reg HS (11%bv : bv 5) (Z_to_bv 64 0) Y11 ltac:(reflexivity).
osl_reg HS (12%bv : bv 5) (Z_to_bv 64 3) Y12 ltac:(reflexivity).
osl_kreg_of HS ESlo EES (10%bv : bv 5) 20%nat (20%bv : bv 5) R20 Y10.
osl_kreg HS ESlo EES (2%bv : bv 5) 2%nat R2 Y2. osl_kreg HS ESlo EES (3%bv : bv 5) 3%nat R3 Y3.
osl_kreg HS ESlo EES (4%bv : bv 5) 4%nat R4 Y4. osl_kreg HS ESlo EES (8%bv : bv 5) 8%nat R8 Y8.
osl_kreg HS ESlo EES (9%bv : bv 5) 9%nat R9 Y9. osl_kreg HS ESlo EES (18%bv : bv 5) 18%nat R18 Y18.
osl_kreg HS ESlo EES (19%bv : bv 5) 19%nat R19 Y19. osl_kreg HS ESlo EES (20%bv : bv 5) 20%nat R20 Y20.
osl_kreg HS ESlo EES (21%bv : bv 5) 21%nat R21 Y21. osl_kreg HS ESlo EES (22%bv : bv 5) 22%nat R22 Y22.
osl_kreg HS ESlo EES (24%bv : bv 5) 24%nat R24 Y24. osl_kreg HS ESlo EES (25%bv : bv 5) 25%nat R25 Y25.
osl_kreg HS ESlo EES (26%bv : bv 5) 26%nat R26 Y26.
(* the run wrote [s + 212, s + 216) and [s + 168, s + 172) only *)
assert (KS : forall a, 0 <= a < 2 ^ 64 -> ~ osl_Z a ->
  aview segs (w_H W2) (ms_mem msS) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ osl_Z HFrs); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. unfold osl_Z.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U20s in Hx; lia |]).
  destruct Hin. }
assert (GS : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msS) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGs Ha)).
(* the stored bytes: 0 at s + 212 (region 0) and at s + 168 (region 1) *)
osl_region HS 0%nat HRi.
lazymatch type of HRi with region_ok _ ?Ex _ (YP09.mkRegion _ _ _ _ _ [YP09.mkChunk _ (CVal _ ?ev)]) =>
  assert (DEN : sv_denot Ex ev = Z_to_bv 64 0) by (cbn [sv_denot]; reflexivity);
  assert (U20f : bv_unsigned (ew Ex 20) = ONANN_S) by (try rewrite (ESlo 20%nat ltac:(lia)); exact U20s);
  pose proof (can_field_of_region Ex _ 20 ONANN_S _ 212 216 212 216 212 4%N ev 0 HRi U20f ltac:(osl_in) DEN
    ltac:(cbn; lia) ltac:(cbn; lia)) as VI
end.
clear HRi DEN U20f.
osl_region HS 1%nat HRd.
lazymatch type of HRd with region_ok _ ?Ex _ (YP09.mkRegion _ _ _ _ _ [YP09.mkChunk _ (CVal _ ?ev)]) =>
  assert (DEN : sv_denot Ex ev = Z_to_bv 64 0) by (cbn [sv_denot]; reflexivity);
  assert (U20f : bv_unsigned (ew Ex 20) = ONANN_S) by (try rewrite (ESlo 20%nat ltac:(lia)); exact U20s);
  pose proof (can_field_of_region Ex _ 20 ONANN_S _ 168 172 168 172 168 4%N ev 0 HRd U20f ltac:(osl_in) DEN
    ltac:(cbn; lia) ltac:(cbn; lia)) as VD
end.
clear HRd DEN U20f.
change (N.to_nat 4) with 4%nat in VI, VD.
(* the world relation at slost_w1 Bx *)
assert (TWS : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msS)) (slost_w1 Bx)).
{ apply (osl_tw_w1 (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem msS)) Bx Htw2).
  - intros j Hj. rewrite <- CS'. exact (osl_aview_of_val _ _ _ 4 _ VI j Hj).
  - intros j Hj. rewrite <- CS'. exact (osl_aview_of_val _ _ _ 4 _ VD j Hj).
  - intros x Hx H1 H2.
    assert (Hg : inG TG.G_HARNESS_B x).
    { destruct Hx as (o & b0 & n & Hin & Hb). pose proof (TMAP_B_in_G o b0 n Hin) as HG0.
      unfold inG. apply Exists_exists. exists (b0, n). split; [exact HG0 | unfold in_zr; cbn [fst snd]; lia]. }
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX Hg) as Hl. unfold kLowMemEnd in Hl.
    apply KS; [lia|]. unfold osl_Z. rewrite CS'. intros [X | X]; [exact (H1 X) | exact (H2 X)]. }
(* the cut's facts at the run's memory *)
assert (KGS : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (ms_mem msS) (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (TransportGFrame.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2
    (ms_mem msS) (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) osl_Z HARc HK KS GS).
  - intros a Hz Hc. exfalso. unfold osl_Z in Hz. rewrite CS in Hz. lia.
  - intros b0 m i _ _ Hz. exact (osl_Z_wr Bw b _ Hz).
  - intros a Hz _ HnG _ _. exfalso. exact (HnG (osl_Z_G a Hz)).
  - intros c p a _ _ Hz. exact (osl_Z_wr Bw b _ Hz). }
assert (HSVS : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) (ms_mem msS)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSV o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KS; [lia|]. unfold osl_Z. rewrite CS. lia. }
assert (HFLS : rdword (aview segs (w_H W2) (ms_mem msS)) (F + 512 - 8) = Some (flag_addr lyc ONANN_CID pos)).
{ rewrite <- HFL. apply YCbq.rdword_ext. intros i Hi. apply KS; [lia|]. intros X.
  exact (FNG (F + 512 - 8 + i) ltac:(lia) (osl_Z_G _ X)). }
assert (CURS : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 (ms_mem msS)
  mdS 0).
{ unfold onann_cur.
  refine (conj HJ (conj He (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj KGS (conj HSVS _)))))))).
  unfold ONANN_FBYTES. exact HFLS. }
(* set_state's premises *)
assert (NSP : spZ (ms_regs msS) = sp1) by (unfold spZ; rewrite Y2; unfold w64; apply unsigned_lit_small; lia).
assert (Hw1' : spZ regs - ONANN_STK <= spZ (ms_regs msS) - SSTATE_STK) by (rewrite NSP; lia).
assert (Hw2' : spZ (ms_regs msS) <= spZ regs) by (rewrite NSP; lia).
pose proof (onann_tf_cur B MT HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F ly2 S2 W2 (ms_mem msS) mdS 0 (ms_regs msS) SSTATE_STK HFIX CURS Hw1' Hw2') as Ptf.
pose proof (onann_rom_cur B MT HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F ly2 S2 W2 (ms_mem msS) mdS 0 HFIX CURS) as Prom.
assert (EBR : BASE + 28300 = 0x8812c) by (vm_compute; reflexivity).
assert (Pret : YK0s.ret_ok (YK11.getr (ms_regs msS) 1))
  by (rewrite Y1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity]).
assert (Pra4 : 4096 <= raZ (ms_regs msS)) by (unfold raZ; rewrite Y1, EBR, unsigned_lit_small by lia; lia).
assert (Pgp : YK11.getr (ms_regs msS) 3 = w64 (as_gp B)) by (rewrite Y3; exact Hgp).
assert (Ptp : YK11.getr (ms_regs msS) 4 = w64 (as_tp B)) by (rewrite Y4; exact Htp).
assert (Pa0 : YK11.getr (ms_regs msS) 10 = w64 SSTATE_S) by exact Y10.
assert (Pa1 : YK11.getr (ms_regs msS) 11 = w64 TS0.DIGINET_S_IDLE) by exact Y11.
assert (Pa2 : YK11.getr (ms_regs msS) 12 = w64 TS0.DIGINET_R_DESK_OFFLINE) by exact Y12.
assert (Psp16 : spZ (ms_regs msS) mod 16 = 0) by (rewrite NSP; exact Hsp116).
assert (Pwin1 : sp0 - STK <= spZ (ms_regs msS) - SSTATE_STK) by (rewrite NSP; lia).
assert (Pwin2 : spZ (ms_regs msS) <= sp0) by (rewrite NSP; lia).
assert (Pst : 0 <= TS0.DIGINET_S_IDLE < 2 ^ 31) by (unfold TS0.DIGINET_S_IDLE; lia).
assert (Pwhy : 0 <= TS0.DIGINET_R_DESK_OFFLINE < 2 ^ 31) by (unfold TS0.DIGINET_R_DESK_OFFLINE; lia).
pose proof (onann_apart_sstate TF Bw b Bx TS0.DIGINET_R_DESK_OFFLINE LBx LBw EGn ESt Hapart) as Pap.
assert (Pcnt : count_cid SSTATE_CID (frames S2) < fs_frames SSTATE_CID).
{ rewrite Hfrs.
  change (count_cid SSTATE_CID ((ONANN_CID, pos) :: frames Sc)) with (0 + count_cid SSTATE_CID (frames Sc)).
  change SSTATE_CID with SENDCTL_CID. lia. }
assert (Pnev : st_nev S + (k + 0) + SSTATE_EV <= EV_MAX) by (rewrite EVS; lia).
(* +0x460: set_state, in the same G journal *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sg (transportb_sigma TB_set_state) rg mm mdx) Q) end.
eapply SRr_bind.
{ exact (HSST fx STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 (ms_mem msS) mdS (k + 0) (ms_regs msS)
    TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_OFFLINE TF (slost_w1 Bx) B4 HJ Pret Pra4 Pgp Ptp Pa0 Pa1 Pa2 Psp16 Pwin1
    Pwin2 TWS Pgf EB4 Pst Pwhy Ptf Prom Pap Pcnt Pnev). }
intros W3 c3 _ HPOST.
unfold transport_sstate_post, transport_cg_post in HPOST.
destruct HPOST as (ly3 & S3 & regs5 & mem5 & md6 & e' & -> & He' & HJ6 & HP6 & Hfr6 & Hperm6 & HK6 & Hmo6 & Htw6 & Hgf6).
rewrite NSP in HK6.
assert (He0 : e' = 0) by (rewrite EVS in He'; lia).
subst e'.
(* the state set_state returned: the cut's facts there *)
assert (ELF3 : ly_F ly3 = ly_F lyc).
{ pose proof HJe as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & Hlyc & _). pose proof Hlyc as (_ & _ & _ & _ & _ & Ec & _).
  pose proof HJ6 as (_ & _ & (memS6 & HJ6i & _) & _). pose proof HJ6i as (_ & Hly3 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & E3 & _).
  rewrite E3, Ec. reflexivity. }
assert (K5 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem5 (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ assert (Hlo1 : spZ regs <= 2 ^ 64) by lia.
  apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 (ms_mem msS) W3 mem5
    (spZ regs - ONANN_STK) (spZ regs) (sp1 - SSTATE_STK) sp1 (onann_wr Bw b)
    (sstate_wr (slost_w1 Bx) TS0.DIGINET_S_IDLE TS0.DIGINET_R_DESK_OFFLINE)
    (dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos))
    Hspc Hlo1 EFAll ltac:(intros f Hf; rewrite Hfrs; right; exact Hf) Hbl2 N1 N3 KGS HK6).
  - lia.
  - lia.
  - intros a Ha. left. exact (onann_wr_slost Bw b Bx TS0.DIGINET_R_DESK_OFFLINE a LBx LBw EGn ESt Ha). }
assert (HSV5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem5) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSVS o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. destruct HK6 as (L1 & _). apply L1; lia. }
assert (HFL5 : rdword (aview segs (w_H W3) mem5) (F + 512 - 8) = Some (flag_addr lyc ONANN_CID pos)).
{ rewrite <- HFLS. apply YCbq.rdword_ext. intros i Hi. destruct HK6 as (_ & _ & _ & L4 & _).
  apply (L4 ONANN_CID pos (F + 512 - 8 + i) Hin2).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA2, onann_fbytes. unfold ONANN_FBYTES. lia.
  - intros Hw. exact (FNG (F + 512 - 8 + i) ltac:(lia) (onann_sstate_wr_G _ _ _ _ Hw)). }
(* the registers set_state kept *)
assert (P2 : YK11.getr regs5 2 = w64 sp1) by exact (eq_trans (HP6 2 ltac:(hnf; lia)) Y2).
assert (P3 : YK11.getr regs5 3 = YK11.getr regs 3) by exact (eq_trans (HP6 3 ltac:(hnf; lia)) Y3).
assert (P4 : YK11.getr regs5 4 = YK11.getr regs 4) by exact (eq_trans (HP6 4 ltac:(hnf; lia)) Y4).
assert (P8 : YK11.getr regs5 8 = w64 (spZ regs)) by exact (eq_trans (HP6 8 ltac:(hnf; lia)) Y8).
assert (P9 : YK11.getr regs5 9 = w64 sp1) by exact (eq_trans (HP6 9 ltac:(hnf; lia)) Y9).
assert (P18 : YK11.getr regs5 18 = w64 (SHADOW_OFF + F / 8)) by exact (eq_trans (HP6 18 ltac:(hnf; lia)) Y18).
assert (P19 : YK11.getr regs5 19 = w64 F) by exact (eq_trans (HP6 19 ltac:(hnf; lia)) Y19).
assert (P20 : YK11.getr regs5 20 = w64 ONANN_S) by exact (eq_trans (HP6 20 ltac:(hnf; lia)) Y20).
assert (P21 : YK11.getr regs5 21 = w64 now) by exact (eq_trans (HP6 21 ltac:(hnf; lia)) Y21).
assert (P22 : YK11.getr regs5 22 = w64 (ONANN_S + 112)) by exact (eq_trans (HP6 22 ltac:(hnf; lia)) Y22).
assert (P24 : YK11.getr regs5 24 = w64 SHADOW_OFF) by exact (eq_trans (HP6 24 ltac:(hnf; lia)) Y24).
assert (P25 : YK11.getr regs5 25 = w64 F) by exact (eq_trans (HP6 25 ltac:(hnf; lia)) Y25).
assert (P26 : YK11.getr regs5 26 = w64 (SHADOW_OFF + (ONANN_S + 112) / 8))
  by exact (eq_trans (HP6 26 ltac:(hnf; lia)) Y26).
(* run R, +0x464 .. +0x46c: the check of s + 112, the load of S_state; it stops at the wake cut *)
rewrite Y1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OSL_RET)) mm rom) mdx) Q) end.
clear HS SHOK HJ.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as HAR3.
pose proof (osl_entry_r (fx := fx) B ly3 S3 W3 regs5 mem5 md6 B4 HSC HAR3 Htw6 P22 P26) as HS.
assert (SHOK : sh_ok segs OSL_BX [] (osl_Ea regs5 B4) (mrestrict (w_H W3) mem5)) by constructor.
assert (HEIr : img_env VAL A_LIM (osl_Ea regs5 B4)) by (unfold osl_Ea; apply Eimg_env).
assert (EER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (osl_Ea regs5 B4) n = YK11.getr regs5 r)
  by (intros n r Hn; exact (osl_ewa regs5 B4 n r Hn)).
pose proof HJ6 as HJ.
paj_run_to_tok RUNTO HS HJ SHOK OSL_B0 ONANN_WK.
{ osl_awr_rs.
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
osl_name_md mdR.
osl_lo HS (osl_Ea regs5 B4) ERlo msR.
osl_reg HS (10%bv : bv 5) (Z_to_bv 64 (TW.S_state B4)) Z10
  ltac:(apply osl_sext; try rewrite (ERlo 32%nat ltac:(lia)); exact (osl_ewa32 regs5 B4)).
osl_kreg HS ERlo EER (2%bv : bv 5) 2%nat P2 Z2. osl_kreg HS ERlo EER (3%bv : bv 5) 3%nat P3 Z3.
osl_kreg HS ERlo EER (4%bv : bv 5) 4%nat P4 Z4. osl_kreg HS ERlo EER (8%bv : bv 5) 8%nat P8 Z8.
osl_kreg HS ERlo EER (9%bv : bv 5) 9%nat P9 Z9. osl_kreg HS ERlo EER (18%bv : bv 5) 18%nat P18 Z18.
osl_kreg HS ERlo EER (19%bv : bv 5) 19%nat P19 Z19. osl_kreg HS ERlo EER (20%bv : bv 5) 20%nat P20 Z20.
osl_kreg HS ERlo EER (21%bv : bv 5) 21%nat P21 Z21. osl_kreg HS ERlo EER (24%bv : bv 5) 24%nat P24 Z24.
osl_kreg HS ERlo EER (25%bv : bv 5) 25%nat P25 Z25.
(* run R wrote no byte *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msR) a = aview segs (w_H W3) mem5 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
  intros b0 wlo whi x Hin Hx. cbv beta.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]).
  destruct Hin. }
assert (GR : forall a, apresent (w_H W3) mem5 a -> apresent (w_H W3) (ms_mem msR) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (K7 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 (ms_mem msR) (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (TransportGFrame.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W3 mem5
    (ms_mem msR) (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) (fun _ => False) HARc K5
    ltac:(intros a Ha _; exact (KR a Ha)) GR).
  - intros a [].
  - intros b0 m i _ _ [].
  - intros a [].
  - intros c p a _ _ []. }
assert (HSV7 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) (ms_mem msR)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSV5 o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KR. lia. }
assert (HFL7 : rdword (aview segs (w_H W3) (ms_mem msR)) (F + 512 - 8) = Some (flag_addr lyc ONANN_CID pos)).
{ rewrite <- HFL5. apply YCbq.rdword_ext. intros i Hi. apply KR. lia. }
assert (TW7 : tw_at TMAP_B (aview segs (w_H W3) (ms_mem msR)) B4).
{ apply (tw_kept_GB (aview segs (w_H W3) mem5)); [exact Htw6|]. intros b0 n i Hbn Hi.
  assert (Hg : inG TG.G_HARNESS_B (b0 + i))
    by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  apply KR. lia. }
(* the wake cut *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_WK)) mm rom) mdx) Q) end.
apply (WK HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  B4 ly3 S3 W3 (ms_mem msR) mdR 0 (ms_regs msR) HFIX).
- unfold onann_wk_cur, onann_cur.
  refine (conj (conj _ (conj _ (conj _ (conj _ (conj ELF3 (conj _ (conj K7 (conj HSV7 _))))))))
    (conj _ (conj TW7 (conj Hk4 (conj Hgf6 Hri4))))).
  + replace (k + 0) with (k + 0 + 0) by lia. exact HJ.
  + rewrite EVO. lia.
  + rewrite Hfr6. exact Hfrs.
  + exact (Permutation_trans Hperm6 Hperm).
  + exact (mo_le_trans MT MTL Sc S2 S3 0 0 Hmo Hmo6).
  + unfold ONANN_FBYTES. exact HFL7.
  + rewrite EVO. lia.
- exact (conj (conj (conj Z2 (conj Z3 (conj Z4 (conj Z8 (conj Z9 (conj Z18 (conj Z19 Z25))))))) (conj Z20 Z24))
    (conj Z10 Z21)).
Qed.
End main.

Print Assumptions onann_sl1_piece.
