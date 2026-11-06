(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 697 of its 763 lines of code are new or changed and 1858 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/on_announce_seg_tail.v, with its module names changed; 523 of its 604 lines of code are new or changed and 682 lines of the source are left out. *)
(* on_announce_seg_lp: Lemma onann_lp_piece : onann_lp_stmt (lib/B/Prog/OnannCutB.v), the parse piece of on_announce's
   image-B walk, offsets +0x19c .. +0x1a8 of the listing lib/B/Prog/DgnTransportBList.v (fuzz_transport.asan-ubsan
   0x87e64 .. 0x87e70), from the parse cut onann_lp_at to the ignore cut onann_ign_at (+0x1ac) or the personality cut
   onann_pf_at (+0x1e0), which the piece is given.

   What the code does (:187). +0x19c `mv a0, s6` (fp), +0x1a0 `mv a1, s10` (a = F + 32), +0x1a4 `jal
   diginet_announce_parse` (0x8bdec = transportb_sigma TB_diginet_announce_parse), return address +0x1a8; +0x1a8 `beq
   a0, zero`: a code that is not 0 runs on to +0x1ac (the ignore cut), 0 jumps to +0x1e0 (the personality cut).

   The runs are the token engine's over the caller's G journal (lib/B/Prog/TransportGRunB.v): from a state with no
   region at +0x19c, one run through the two moves and the `jal` to diginet_announce_parse's entry; from a state with
   no region at +0x1a8, the `beq` split by DgnTransportBPaLib.v psrr_branch_tok and one run of one instruction to each
   cut. No run writes a byte.
   The call (diginet_announce_parse_cg.v transport_diginet_announce_parse_cg, a donor-form callee lifted by
   TransportGCg.v gx_call_cg), premise by premise: the donor journal from the G journal (gx_call_cg); ra = +0x1a8
   (DgnTransportBPaLib.v ret_ok_codeptr_v); gp, tp kept; a0 = fp, a1 = ap = F + 32 (the moves); sp = sp1, 32-aligned,
   and the callee's window inside on_announce's (ONANN_STK = 208 + WAKE_STK, TRANS_ANP_STK <= WAKE_STK); fp's facts,
   the bytes at f + 30 and f + 32, buf's placement and bytes (on_announce_seg_kit.v onann_f30 at the call state); the
   body bb = fr_body b at buf + 30, a sub-range of buf's (DgnTransportBCg.v trans_src_ok_sub, decode_off_win_sub;
   onn_lp_body_garr8); aj, the 40 bytes present at ap (YI00.v garr8_of_present); ap in the own class-3 frame
   (decode_in_fake, decode_twr_ok by the journal's own frame list, decode_rd_ok by a's 5 zero shadow bytes,
   TransportGNotice.v frame_ra_zero / frame_hull_vis); ap apart from f (onann_f30) and from bb (DgnTransportBCg.v
   trans_src_ok_disj_own); no event. Its post folds into onann_cur by TransportGCg.v dk_kept_trans_nf_g (its written
   range trans_anp_wr ap lies in the own frame, TransportGFrame.v dkg_nf_sep_gw), the saved words and the frame's last
   word by its kept clauses, the world relation by its gx_kept; its a0 is ann_code (fr_cmd b) (length (fr_body b)),
   whose test against 0 is onann_ign b's (onn_lp_body_len), and, when it is 0, the 40 bytes at ap are
   diginet_announce_parse_c.v ann_cells, read as onann_a_ok by onn_lp_a_ok_of (version and name: TSess.v ann_field is a
   prefix of copy_strz's field, onn_lp_field_prefix; unknown and unknown_len: onn_lp_rdword_le8).
   This piece passes no trap word and no instrumented check. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TNeed TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_announce_parse_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LCel := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module LPAnn := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_announce_parse_c.
Module LPGN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model and the bytes the parse leaves                         *)
(* ------------------------------------------------------------------ *)

(* The return address of the call, the `beq` (+0x1a8). *)
Definition ONN_LP_RET : Z := AF_on_announce + 0x1a8.
Definition ONN_LP_B0 : Z * Z := (0, 0).

(* `beq a0, zero` on a value of [-2^63, 2^63): the test against 0. *)
Lemma onn_lp_eqb0 : forall v, - 2 ^ 63 <= v < 2 ^ 63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0 (2 ^ 64)) by lia.
destruct (Z.eqb_spec v 0) as [-> | Hne]; [reflexivity|].
apply Z.eqb_neq. intros HH. apply Hne.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

(* The parse's code is -9, -4 or 0. *)
Lemma onn_lp_code_range : forall c l, - 2 ^ 63 <= DSpec.ann_code c l < 2 ^ 63.
Proof.
intros c l. unfold DSpec.ann_code.
destruct (negb (DSpec.ann_cmd c)); [lia|]. destruct (l <? 33); lia.
Qed.

(* A frame parsed with code 0: the body has fr_body_len b bytes, from byte 30 of b on. *)
Lemma onn_lp_body_len : forall b, DSpec.fr_code b = 0 ->
  Z.of_nat (length (DSpec.fr_body b)) = DSpec.fr_body_len b /\ 0 <= DSpec.fr_body_len b /\
  30 + DSpec.fr_body_len b <= Z.of_nat (length b) /\ (30 <= length b)%nat.
Proof.
intros b H. destruct (DSpec.fr_code_ok b H) as (H30 & _ & H16 & Hnb).
unfold DSpec.fr_body, DSpec.fr_body_len in *.
rewrite length_firstn, length_skipn. lia.
Qed.

(* The body's bytes at buf + 30, read off the frame's bytes at buf. *)
Lemma onn_lp_body_garr8 : forall (m : word -> option byte) buf b,
  DSpec.fr_code b = 0 -> garr8 tfibsegs m buf (TW.zs b) ->
  garr8 tfibsegs m (buf + 30) (map DSpec.bz (DSpec.fr_body b)).
Proof.
intros m buf b H0 HG.
destruct (onn_lp_body_len b H0) as (_ & _ & _ & H30).
unfold TW.zs in HG. rewrite <- (firstn_skipn 30 b), map_app in HG.
apply garr8_app in HG as [_ HG]. rewrite length_map, length_firstn in HG.
replace (buf + Z.of_nat (Nat.min 30 (length b))) with (buf + 30) in HG by lia.
unfold DSpec.fr_body.
rewrite <- (firstn_skipn (Z.to_nat (DSpec.fr_body_len b)) (skipn 30 b)), map_app in HG.
apply garr8_app in HG as [HG _]. exact HG.
Qed.

(* copy_strz's 10-byte field keeps its length. *)
Lemma onn_lp_copy_len : forall src old, length old = 10%nat -> length (DSpec.copy_strz 10 9 src old) = 10%nat.
Proof.
intros src old Hl.
assert (Hk : (DSpec.copy_len 10 9 src <= Nat.min 9 (length src))%nat).
{ unfold DSpec.copy_len. etransitivity; [apply DSpec.nz_run_le|]. rewrite length_firstn. lia. }
unfold DSpec.copy_strz. rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn. lia.
Qed.

(* The string notice() reads (TSess.v ann_field) is a prefix of the field copy_strz writes. *)
Lemma onn_lp_field_prefix : forall src old,
  DSpec.copy_strz 10 9 src old = TSS.ann_field src ++ skipn (S (DSpec.copy_len 10 9 src)) old.
Proof. intros src old. unfold DSpec.copy_strz, TSS.ann_field. rewrite <- app_assoc. reflexivity. Qed.

(* Eight bytes of the value v, read back as a word through the view. *)
Lemma onn_lp_rdword_le8 : forall (H : word -> bool) (m : word -> option byte) a v, 0 <= v < 2 ^ 64 ->
  garr8 tfibsegs (mrestrict H m) a (map DSpec.bz (LMem.le8 (Z_to_bv 64 v))) ->
  rdword (aview tfibsegs H m) a = Some v.
Proof.
intros H m a v Hv HG. rewrite TWL.le8_put in HG.
assert (HB : forall j, (j < 8)%nat -> aview tfibsegs H m (a + Z.of_nat j) = Some (YO0f.le_byte v 8 j)).
{ intros j Hj.
  assert (Hj' : (j < length (map DSpec.bz (TW.put 8 v)))%nat) by (rewrite length_map, TWL.length_put; exact Hj).
  destruct (HG j Hj') as [HV HR].
  assert (E : nth j (map DSpec.bz (TW.put 8 v)) 0 = YO0f.le_byte v 8 j).
  { rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) by exact Hj'.
    rewrite map_nth. unfold DSpec.bz. apply tw_le_byte_put. exact Hj. }
  rewrite E in HV, HR. exact (aview_of_val_mem1 H m _ _ HV HR). }
unfold rdword.
pose proof (HB 0%nat ltac:(lia)) as H0. pose proof (HB 1%nat ltac:(lia)) as H1.
pose proof (HB 2%nat ltac:(lia)) as H2. pose proof (HB 3%nat ltac:(lia)) as H3.
pose proof (HB 4%nat ltac:(lia)) as H4. pose proof (HB 5%nat ltac:(lia)) as H5.
pose proof (HB 6%nat ltac:(lia)) as H6. pose proof (HB 7%nat ltac:(lia)) as H7.
cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3, H4, H5, H6, H7.
rewrite Z.add_0_r in H0.
rewrite H0, H1, H2, H3, H4, H5, H6, H7. f_equal. apply le_bytes8. exact Hv.
Qed.

(* The 40 bytes diginet_announce_parse leaves at ap on code 0 (diginet_announce_parse_c.v ann_cells), read as
   OnannCutB.v onann_a_ok reads them: the version's and the name's bytes up to their 0, unknown, unknown_len. *)
Lemma onn_lp_a_ok_of : forall (H : word -> bool) (m : word -> option byte) ap body (bb aj : list byte),
  length aj = 40%nat -> 0 <= body < 2 ^ 64 ->
  garr8 tfibsegs (mrestrict H m) ap (map DSpec.bz (LCel.cells_bytes (LPAnn.ann_cells body bb aj))) ->
  garr8 tfibsegs (mrestrict H m) ap (map DSpec.bz (TSS.ann_field (skipn 15 bb))) /\
  garr8 tfibsegs (mrestrict H m) (ap + 10) (map DSpec.bz (TSS.ann_field (skipn 24 bb))) /\
  rdword (aview tfibsegs H m) (ap + 24) = Some body /\
  rdword (aview tfibsegs H m) (ap + 32) = Some 15.
Proof.
intros H m ap body bb aj Haj Hb HG.
assert (L1 : length (DSpec.ann_version bb (firstn 10 aj)) = 10%nat)
  by (apply onn_lp_copy_len; rewrite length_firstn; lia).
assert (L2 : length (DSpec.ann_name bb (firstn 10 (skipn 10 aj))) = 10%nat)
  by (apply onn_lp_copy_len; rewrite length_firstn, length_skipn; lia).
assert (L3 : length (firstn 4 (skipn 20 aj)) = 4%nat) by (rewrite length_firstn, length_skipn; lia).
unfold LPAnn.ann_cells in HG. cbn [LCel.cells_bytes LCel.cbytes] in HG. rewrite !map_app in HG.
apply garr8_app in HG as [GV HG]. rewrite length_map, L1 in HG.
apply garr8_app in HG as [GN HG]. rewrite length_map, L2 in HG.
apply garr8_app in HG as [_ HG]. rewrite length_map, L3 in HG.
apply garr8_app in HG as [GU HG]. rewrite length_map, LMem.length_le8 in HG.
apply garr8_app in HG as [GL _].
replace (ap + Z.of_nat 10) with (ap + 10) in GN by lia.
replace (ap + Z.of_nat 10 + Z.of_nat 10 + Z.of_nat 4) with (ap + 24) in GU by lia.
replace (ap + Z.of_nat 10 + Z.of_nat 10 + Z.of_nat 4 + Z.of_nat 8) with (ap + 32) in GL by lia.
unfold DSpec.ann_version in GV. unfold DSpec.ann_name in GN.
rewrite onn_lp_field_prefix, map_app in GV, GN.
apply garr8_app in GV as [GV _]. apply garr8_app in GN as [GN _].
split; [exact GV|]. split; [exact GN|].
split; [exact (onn_lp_rdword_le8 H m _ _ Hb GU)|].
exact (onn_lp_rdword_le8 H m (ap + 32) 15 ltac:(lia) GL).
Qed.

(* On code 0 the 40 bytes are ann_cells. *)
Lemma onn_lp_anp_ok : forall cmd body (bb aj : list byte), ann_ok cmd bb = true ->
  trans_anp_bytes cmd body bb aj = map DSpec.bz (LCel.cells_bytes (LPAnn.ann_cells body bb aj)).
Proof. intros cmd body bb aj H. unfold trans_anp_bytes, trans_anp_cells. rewrite H. reflexivity. Qed.

(* A list of byte values, as the bytes it names. *)
Lemma onn_lp_garr8_bytes : forall (m : word -> option byte) a l, garr8 tfibsegs m a l ->
  garr8 tfibsegs m a (map DSpec.bz (map (Z_to_bv 8) l)).
Proof.
intros m a l HG.
pose proof (garr8_bytes_ok tfibsegs m a l HG) as HB. unfold bytes_ok in HB. rewrite Forall_forall in HB.
replace (map DSpec.bz (map (Z_to_bv 8) l)) with (map (fun x : Z => x) l); [rewrite map_id; exact HG|].
rewrite map_map. apply map_ext_in. intros x Hx. cbv beta. specialize (HB x Hx).
unfold DSpec.bz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_small by lia. reflexivity.
Qed.

(* The tactics of the runs (on_ack_seg_aft.v's oaf_ tactics). *)
Ltac onn_lp_reg HS r v H tac :=
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
Ltac onn_lp_kreg_of HS Elo EE r n rn Q H :=
  lazymatch type of Q with _ = ?v =>
    onn_lp_reg HS r v H
      ltac:(cbn [sv_denot]; try rewrite (Elo n ltac:(lia)); rewrite (EE n rn eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
            exact Q) end.
Ltac onn_lp_kreg HS Elo EE r n Q H := onn_lp_kreg_of HS Elo EE r n r Q H.
Ltac onn_lp_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
Ltac onn_lp_win Hin Hx :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]);
  destruct Hin.
Ltac onn_lp_name_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md := m) in *; clearbody md end.
Ltac onn_lp_lo HS E0 Hlo m :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  end.

(* ------------------------------------------------------------------ *)
(* 2. States with no region, and what a cut carries across a run       *)
(* ------------------------------------------------------------------ *)

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The valuation of the runs: the 32 registers. *)
Definition onn_lp_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Lemma onn_lp_ew : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (onn_lp_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold onn_lp_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

(* A state with no region at any pc of the listing. *)
Lemma onn_lp_entry0 : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (onn_lp_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
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

(* A run whose regions have empty write windows changes no byte of the view. *)
Lemma onn_lp_kd_of_frame : forall (W : world segs) E rs (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b0 wlo whi a, In (b0, wlo, whi) (windows rs) ->
     base_val E b0 + wlo <= a < base_val E b0 + whi -> False) ->
  forall a, aview segs (w_H W) m' a = aview segs (w_H W) m a.
Proof.
intros W E rs m m' HFr HW a.
rewrite (aview_wrap64 segs _ m' a), (aview_wrap64 segs _ m a).
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
apply (kept_of_frame E rs (w_H W) m m' (fun _ : Z => False) HFr HW); [exact Ha | tauto].
Qed.

(* The facts every cut carries move to a later memory whose view is the same at every address. *)
Lemma onn_lp_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2
    (W2 : world segs) mem2 md2 mem3 md3 e,
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONANN_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 KD GR.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b0 m i Hb Hi Hn. rewrite KD. exact (K2 b0 m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. cbv beta in Ho |- *.
  rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
Qed.

(* The parse's fields at a, at a later memory whose view is the same at every address. *)
Lemma onn_lp_a_ok_move : forall (W2 : world segs) mem2 mem3 F buf b,
  onann_a_ok W2 mem2 F buf b ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  onann_a_ok W2 mem3 F buf b.
Proof.
intros W2 mem2 mem3 F buf b (A1 & A2 & A3 & A4 & A5) KD.
split; [|split; [|split; [|split]]].
- apply (garr8_frame segs _ _ _ _ A1). intros a _. apply mbyte_of_aview. exact (KD a).
- apply (garr8_frame segs _ _ _ _ A2). intros a _. apply mbyte_of_aview. exact (KD a).
- rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => KD _)). exact A3.
- rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => KD _)). exact A4.
- intros i Hi. rewrite KD. exact (A5 i Hi).
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
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma onann_lp_piece : @onann_lp_stmt fx rc B MT.
Proof.
unfold onann_lp_stmt. intros IGN PF. unfold onann_lp_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HOC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof CALLEES as (HASM & HANP & HPFN & HBCMP & HMS & HNT & HSST & HWK & HMON & HSH5).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hgf &
  Hm & HTF & HTFG & Hrom & Hapart & Hri & Hc3 & Hc1 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp0).
pose proof HDF as (HFC0 & Hbuf0 & Hbufg & Hbufsrc & Hbufwin & HbufG & Hfp0 & Hfp8 & Hfjlen & Hfgarr & Hffake &
  Hfrd & Hfwin).
pose proof HCUR as (HCUR0 & Htw2 & HZA).
pose proof HCUR0 as (HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25) & R20 & R24) & R22 & R23 & R26).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKe : ONANN_STK = 208 + WAKE_STK)
  by (rewrite onann_stk_eq; unfold ONANN_FRAME, ONANN_ALIGN; lia).
assert (HWKS : TRANS_ANP_STK <= WAKE_STK) by (vm_compute; discriminate).
assert (ETA : TRANS_ANP_STK = 32 + ESTACK) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (HEVA : TRANS_ANP_EV = 0) by reflexivity.
assert (HEV0 : 0 <= ONANN_EV) by (vm_compute; discriminate).
destruct (onn_lp_body_len b HFC0) as (Elen & Hbl0 & Hbl30 & Hblen).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* ---- +0x19c .. +0x1a4: the two moves and `jal diginet_announce_parse` ---- *)
pose proof (onn_lp_entry0 (fx := fx) W2 regs2 mem2 ONANN_LP) as HS.
assert (HEI : img_env VAL A_LIM (onn_lp_E regs2)) by (unfold onn_lp_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (onn_lp_E regs2) n = YK11.getr regs2 r)
  by (intros n r Hn; exact (onn_lp_ew regs2 n r Hn)).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) (onn_lp_E regs2) (mrestrict (w_H W2) mem2)) by constructor.
pose proof HJ1 as HJ.
paj_run_tok RUN HS HJ SHOK ONN_LP_B0.
{ onn_lp_awr_rs. apply awr_ok_x_nil. }
onn_lp_name_md mdC.
onn_lp_lo HS (onn_lp_E regs2) EClo msC.
onn_lp_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 27600)) Q1 ltac:(apply codeptr_val; assumption).
onn_lp_kreg_of HS EClo EE (10%bv : bv 5) 22%nat (22%bv : bv 5) R22 Q10.
onn_lp_kreg_of HS EClo EE (11%bv : bv 5) 26%nat (26%bv : bv 5) R26 Q11.
onn_lp_kreg HS EClo EE (2%bv : bv 5) 2%nat R2 Q2. onn_lp_kreg HS EClo EE (3%bv : bv 5) 3%nat R3 Q3.
onn_lp_kreg HS EClo EE (4%bv : bv 5) 4%nat R4 Q4. onn_lp_kreg HS EClo EE (8%bv : bv 5) 8%nat R8 Q8.
onn_lp_kreg HS EClo EE (9%bv : bv 5) 9%nat R9 Q9. onn_lp_kreg HS EClo EE (18%bv : bv 5) 18%nat R18 Q18.
onn_lp_kreg HS EClo EE (19%bv : bv 5) 19%nat R19 Q19. onn_lp_kreg HS EClo EE (20%bv : bv 5) 20%nat R20 Q20.
onn_lp_kreg HS EClo EE (22%bv : bv 5) 22%nat R22 Q22. onn_lp_kreg HS EClo EE (23%bv : bv 5) 23%nat R23 Q23.
onn_lp_kreg HS EClo EE (24%bv : bv 5) 24%nat R24 Q24. onn_lp_kreg HS EClo EE (25%bv : bv 5) 25%nat R25 Q25.
onn_lp_kreg HS EClo EE (26%bv : bv 5) 26%nat R26 Q26.
(* the run wrote no byte *)
assert (KCall : forall a, aview segs (w_H W2) (ms_mem msC) a = aview segs (w_H W2) mem2 a).
{ apply (onn_lp_kd_of_frame W2 _ _ mem2 (ms_mem msC) HFr). intros b0 wlo whi x Hin Hx. onn_lp_win Hin Hx. }
assert (GC : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msC) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
set (mC := ms_mem msC) in *. set (rC := ms_regs msC) in *.
(* the cut's facts at the call's memory *)
pose proof (onn_lp_cur_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2
  mC mdC 0 HCUR0 HJ KCall GC) as CURC.
pose proof (onann_cur_ar B MT LAWS HFIX CURC) as (HARc & HARC & ESLO & ESHI & EFA & EFL & HinC & EFC & HFbC & HFshC &
  HFnG & HF4096 & HF64' & HFce & HFapp & Hce_lo & Hlo_sp & Hsp_hi & H47 & HFLp & HFLo & HFLb & HFLf & HFLs & Hsp1r &
  Hsp132 & Hsp146).
clear HFLf HFLs.
pose proof CURC as (_ & _ & HfrsC & HpermC & HlyFC & HmoC & KCC & HSVC & HFLC).
assert (HspC : spZ rC = sp1) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (PW1 : spZ regs - ONANN_STK <= spZ rC - TRANS_ANP_STK) by (rewrite HspC; lia).
assert (PW2 : spZ rC <= spZ regs) by (rewrite HspC; lia).
pose proof (onann_f30 B MT LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F ly2 S2 W2 mC mdC 0 rC TRANS_ANP_STK HFIX CURC PW1 PW2) as (Hfp4096 & Hfpce & Hfp8' & HfpF & Kfg & Kffake &
  Kfrd & Kfwin & Hcmd & Kf30v & Kf30 & Kf30s & Kf32 & Kbuf0 & Kbg & Kbsrc & Kbwin & KbnG).
assert (F8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (DF8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)) as D; rewrite F8, Z.add_0_r in D; exact D).
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
assert (HSHF : SHADOW_OFF + F / 8 + 64 <= F \/ F + 512 <= SHADOW_OFF + F / 8).
{ pose proof HFapp as HFa. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFa.
  destruct HFa as (_ & [HL | (HH1 & HH2)]); [right | left]; unfold SHADOW_OFF; lia. }
assert (HZAC : forall i, 4 <= i < 9 -> aview segs (w_H W2) mC (SHADOW_OFF + F / 8 + i) = Some 0)
  by (intros i Hi; rewrite KCall; exact (HZA i Hi)).
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; exact (Permutation_in _ (Permutation_sym HpermC) Hb)).
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mC mdC ONANN_CID pos F
  (flag_addr lyc ONANN_CID pos) HARC HfrsC Hbl2 HlyFC EF eq_refl FFL) as (N1 & N2 & N3 & N4).
assert (Hbody : 0 <= buf + 30 < 2 ^ 64).
{ destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc buf (Z.of_nat (length b)) HARc Hbufsrc ltac:(lia))
    as [Hp | Hp]; lia. }
(* aj: the 40 bytes present at ap *)
assert (HAJ : exists l, length l = 40%nat /\ garr8 tfibsegs (mrestrict (w_H W2) mC) (F + ONANN_A) l).
{ apply garr8_of_present. intros a Ha. unfold ONANN_A in Ha. destruct (proj1 (HFbC a ltac:(lia))) as [Hh [x Hx]].
  hnf. exists x. unfold mrestrict. rewrite Hh. exact Hx. }
destruct HAJ as (laj & Hlaj & Hgaj).
set (aj := map (Z_to_bv 8) laj).
(* diginet_announce_parse's premises at the call state *)
assert (EBR : BASE + 27600 = 0x87e70) by (vm_compute; reflexivity).
assert (P_ra : YK0s.ret_ok (YK11.getr rC 1))
  by (rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity]).
assert (P_ra4 : 4096 <= raZ rC) by (unfold raZ; rewrite Q1, EBR; rewrite unsigned_lit_small by lia; lia).
assert (P_gp : YK11.getr rC 3 = w64 (as_gp B)) by exact (eq_trans Q3 Hgp).
assert (P_tp : YK11.getr rC 4 = w64 (as_tp B)) by exact (eq_trans Q4 Htp).
assert (P_sp16 : spZ rC mod 16 = 0).
{ rewrite HspC. pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp132, Z.add_0_r in D. rewrite D.
  replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring. apply Z.mod_mul. lia. }
assert (P_lo : sp0 - STK <= spZ rC - TRANS_ANP_STK) by lia.
assert (P_hi : spZ rC <= sp0) by lia.
assert (P_ap8 : (F + ONANN_A) mod 8 = 0) by (unfold ONANN_A; rewrite Z.add_mod, F8 by lia; reflexivity).
assert (P_bsrc : (0 < length (DSpec.fr_body b))%nat ->
  trans_src_ok B ly2 S2 W2 mC (buf + 30) (Z.of_nat (length (DSpec.fr_body b)))).
{ intros Hp. eapply trans_src_ok_sub; [exact Kbsrc | lia | lia | lia]. }
assert (P_bwin : (0 < length (DSpec.fr_body b))%nat ->
  decode_off_win rC TRANS_ANP_STK (buf + 30) (Z.of_nat (length (DSpec.fr_body b)))).
{ intros Hp. eapply decode_off_win_sub; [exact Kbwin | lia | lia | lia]. }
assert (P_bg : garr8 segs (mrestrict (w_H W2) mC) (buf + 30) (map DSpec.bz (DSpec.fr_body b)))
  by exact (onn_lp_body_garr8 _ buf b HFC0 Kbg).
assert (P_ajl : length aj = 40%nat) by (unfold aj; rewrite length_map; exact Hlaj).
assert (P_ajg : garr8 segs (mrestrict (w_H W2) mC) (F + ONANN_A) (map DSpec.bz aj))
  by (unfold aj; exact (onn_lp_garr8_bytes _ _ _ Hgaj)).
assert (P_fake : decode_in_fake ly2 S2 (F + ONANN_A) 40).
{ exists ONANN_CID, pos. split; [exact HinC|]. rewrite EFC. change (fs_frame_bytes ONANN_CID) with 512.
  unfold ONANN_A. lia. }
assert (P_twr : decode_twr_ok B STK sp0 FP ly S ly2 S2 ((ONANN_CID, pos) :: own) W2 mC (spZ rC) (F + ONANN_A) 40).
{ intros a Ha. unfold ONANN_A in Ha. rewrite HspC.
  destruct (HFbC a ltac:(lia)) as [Hpa Hno].
  split; [|split; [exact Hpa | split; [exact Hno | lia]]].
  unfold awr_byte. right; right; right. unfold in_frames. exists ONANN_CID, pos. split; [left; reflexivity|].
  left. unfold in_zr. cbn [fst snd]. rewrite EFC. change (fs_frame_bytes ONANN_CID) with 512. lia. }
assert (P_ard : decode_rd_ok W2 mC (F + ONANN_A) 40).
{ unfold decode_rd_ok, ONANN_A. split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. apply can_aview_vis. exact (proj1 (HFbC a ltac:(lia))).
  - apply (LPGN.frame_ra_zero _ F (F + 32) 40 4 9); [lia | exact F8 | lia | lia | exact HZAC].
  - apply (LPGN.frame_hull_vis _ F 512 (F + 32) 40); [lia | exact HF64 | reflexivity | lia | lia | lia |].
    intros i Hi. rewrite ESH. apply can_aview_vis. change (512 / 8) with 64 in Hi. exact (proj1 (HFshC i Hi)).
  - apply (amem_range_sub_app F 512); [exact HFapp | lia | lia | lia | lia].
  - lia.
  - lia. }
assert (P_awin : decode_off_win rC TRANS_ANP_STK (F + ONANN_A) 40)
  by (left; unfold ONANN_A; rewrite HspC; lia).
assert (P_apf : F + ONANN_A + 40 <= fp \/ fp + FRAME_F_SIZE <= F + ONANN_A)
  by (destruct HfpF as [Hd | Hd]; [right | left]; unfold FRAME_F_SIZE, ONANN_FBYTES, ONANN_A in *; lia).
assert (P_apb : (0 < length (DSpec.fr_body b))%nat ->
  F + ONANN_A + 40 <= buf + 30 \/ buf + 30 + Z.of_nat (length (DSpec.fr_body b)) <= F + ONANN_A).
{ intros _. destruct (trans_src_ok_disj_own B LAWS lyc Sc W memc mdc ly2 S2 W2 mC mdC ONANN_CID pos buf
    (Z.of_nat (length b)) HARc HARC HfrsC HpermC EFA Hbufsrc ltac:(lia)) as [Hd | Hd];
  rewrite EFC in Hd; change (fs_frame_bytes ONANN_CID) with 512 in Hd; [right | left]; unfold ONANN_A; lia. }
assert (P_ev : st_nev S + (k + 0) + TRANS_ANP_EV <= EV_MAX) by (rewrite HEVA; lia).
(* ---- +0x1a4: diginet_announce_parse, a donor-form callee in the G journal ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sg (transportb_sigma TB_diginet_announce_parse) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (gx_call_cg segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mC mdC
    (k + 0) _ rC TRANS_ANP_STK TRANS_ANP_EV 0 (trans_anp_wr (F + ONANN_A))
    (fun regs3 (W3 : world segs) mem3 =>
       YK11.getr regs3 10 = w64 (DSpec.ann_code (DSpec.fr_cmd b) (Z.of_nat (length (DSpec.fr_body b)))) /\
       garr8 segs (mrestrict (w_H W3) mem3) (F + ONANN_A)
         (trans_anp_bytes (DSpec.fr_cmd b) (buf + 30) (DSpec.fr_body b) aj)) HGX HGE HJ).
  intros memS HJS.
  eapply SRr_mono.
  { exact (HANP fx STK sp0 FP ly S W0 memS md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mC mdC (k + 0) rC fp
      (F + ONANN_A) (DSpec.fr_cmd b) (buf + 30) (DSpec.fr_body b) aj HJS P_ra P_ra4 P_gp P_tp Q10 Q11 P_sp16 P_lo
      P_hi ltac:(lia) ltac:(unfold ONANN_A; lia) Hfp8' P_ap8 ltac:(lia) Hcmd Kf30 Kf32 Kfrd Kfwin P_bsrc P_bwin
      P_bg P_ajl P_ajg P_fake P_twr P_ard P_awin P_apf P_apb P_ev). }
  intros W2' c2 _ H2. apply decode_cg_post_dcg. exact H2. }
intros W3 c3 _ HPOST.
unfold transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
  (HA0 & HAG) & HGK3).
assert (He30 : e3 = 0) by (rewrite HEVA in He3; lia). subst e3.
replace (k + 0 + 0) with (k + 0) in HJ3 by lia.
rewrite HspC in HK3.
pose proof HK3 as (L1 & _ & _ & L4 & _).
(* ---- the state diginet_announce_parse returned: the cut's facts there ---- *)
assert (ELF3 : ly_F ly3 = ly_F lyc).
{ pose proof HJ3 as (_ & _ & (memS3 & HJ3i & _) & _). pose proof HJ3i as (_ & Hly3 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & E3 & _).
  pose proof HJ0 as (_ & _ & (memS0 & HJ0i & _) & _). pose proof HJ0i as (_ & Hly0 & _).
  pose proof Hly0 as (_ & _ & _ & _ & _ & E0 & _).
  congruence. }
assert (KC3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 mC W3 mem3
    (spZ regs - ONANN_STK) (spZ regs) (sp1 - TRANS_ANP_STK) sp1 (onann_wr Bw b) (trans_anp_wr (F + ONANN_A))
    (dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos))).
  - lia.
  - lia.
  - exact EFA.
  - intros f Hf. rewrite HfrsC. right. exact Hf.
  - exact Hbl2.
  - exact N1.
  - exact N3.
  - exact KCC.
  - exact HK3.
  - lia.
  - lia.
  - intros a Ha. right. unfold dkg_nf. left. change (fs_frame_bytes ONANN_CID) with 512.
    unfold trans_anp_wr, ONANN_A in Ha. lia. }
assert (CUR3 : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mem3 md3 0).
{ refine (conj HJ3 (conj _ (conj _ (conj _ (conj ELF3 (conj _ (conj KC3 (conj _ _)))))))).
  - split; [lia | exact HEV0].
  - rewrite Hfr3. exact HfrsC.
  - exact (Permutation_trans Hperm3 HpermC).
  - exact (mo_le_trans MT MTL Sc S2 S3 0 0 HmoC Hmo3).
  - apply Forall_forall. intros o Hin. cbv beta.
    pose proof (proj1 (Forall_forall _ _) HSVC o Hin) as Hv. cbv beta in Hv.
    assert (Ho : 8 <= fst o <= 104).
    { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
    rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply L1; lia.
  - rewrite <- HFLC. apply YCbq.rdword_ext. intros i Hi.
    apply (L4 ONANN_CID pos (F + ONANN_FBYTES - 8 + i) HinC).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFC. change (fs_frame_bytes ONANN_CID) with 512.
      unfold ONANN_FBYTES. lia.
    + unfold trans_anp_wr, ONANN_A, ONANN_FBYTES. lia. }
assert (TWC : tw_at TMAP_B (aview segs (w_H W2) mC) Bw)
  by (apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact Htw2 | intros x _; exact (KCall x)]).
assert (TW3 : tw_at TMAP_B (aview segs (w_H W3) mem3) Bw).
{ apply (tw_kept_GB (aview segs (w_H W2) mC)); [exact TWC|]. intros b0 n0 i Hin Hi.
  exact (gx_kept_rows segs _ W2 mC W3 mem3 HGK3 b0 n0 i Hin Hi). }
assert (HZ3 : forall i, 4 <= i < 9 -> aview segs (w_H W3) mem3 (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. transitivity (aview segs (w_H W2) mC (SHADOW_OFF + F / 8 + i)); [|exact (HZAC i Hi)].
  apply (L4 ONANN_CID pos (SHADOW_OFF + F / 8 + i) HinC).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFC, ESH. change (fs_frame_bytes ONANN_CID / 8) with 64. lia.
  - unfold trans_anp_wr, ONANN_A. destruct HSHF; lia. }
(* the registers the parse kept *)
assert (S2r : YK11.getr regs3 (Z_to_bv 5 2) = w64 sp1) by exact (eq_trans (HP3 2 ltac:(hnf; lia)) Q2).
assert (S3r : YK11.getr regs3 (Z_to_bv 5 3) = YK11.getr regs 3) by exact (eq_trans (HP3 3 ltac:(hnf; lia)) Q3).
assert (S4r : YK11.getr regs3 (Z_to_bv 5 4) = YK11.getr regs 4) by exact (eq_trans (HP3 4 ltac:(hnf; lia)) Q4).
assert (S8r : YK11.getr regs3 (Z_to_bv 5 8) = w64 (spZ regs)) by exact (eq_trans (HP3 8 ltac:(hnf; lia)) Q8).
assert (S9r : YK11.getr regs3 (Z_to_bv 5 9) = w64 sp1) by exact (eq_trans (HP3 9 ltac:(hnf; lia)) Q9).
assert (S18r : YK11.getr regs3 (Z_to_bv 5 18) = w64 (SHADOW_OFF + F / 8))
  by exact (eq_trans (HP3 18 ltac:(hnf; lia)) Q18).
assert (S19r : YK11.getr regs3 (Z_to_bv 5 19) = w64 F) by exact (eq_trans (HP3 19 ltac:(hnf; lia)) Q19).
assert (S20r : YK11.getr regs3 (Z_to_bv 5 20) = w64 ONANN_S) by exact (eq_trans (HP3 20 ltac:(hnf; lia)) Q20).
assert (S22r : YK11.getr regs3 (Z_to_bv 5 22) = w64 fp) by exact (eq_trans (HP3 22 ltac:(hnf; lia)) Q22).
assert (S23r : YK11.getr regs3 (Z_to_bv 5 23) = w64 now) by exact (eq_trans (HP3 23 ltac:(hnf; lia)) Q23).
assert (S24r : YK11.getr regs3 (Z_to_bv 5 24) = w64 SHADOW_OFF) by exact (eq_trans (HP3 24 ltac:(hnf; lia)) Q24).
assert (S25r : YK11.getr regs3 (Z_to_bv 5 25) = w64 F) by exact (eq_trans (HP3 25 ltac:(hnf; lia)) Q25).
assert (S26r : YK11.getr regs3 (Z_to_bv 5 26) = w64 (F + ONANN_A)) by exact (eq_trans (HP3 26 ltac:(hnf; lia)) Q26).
(* ---- +0x1a8: `beq a0, zero`, from a state with no region ---- *)
rewrite Q1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONN_LP_RET)) mm rom) mdx) Q) end.
clear HS SHOK.
pose proof (onn_lp_entry0 (fx := fx) W3 regs3 mem3 ONN_LP_RET) as HS.
assert (HEI3 : img_env VAL A_LIM (onn_lp_E regs3)) by (unfold onn_lp_E; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (onn_lp_E regs3) n = YK11.getr regs3 r)
  by (intros n r Hn; exact (onn_lp_ew regs3 n r Hn)).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) (onn_lp_E regs3) (mrestrict (w_H W3) mem3)) by constructor.
assert (D10 : sv_denot (onn_lp_E regs3) (SOff 10 0) =
  Z_to_bv 64 (DSpec.ann_code (DSpec.fr_cmd b) (Z.of_nat (length (DSpec.fr_body b)))))
  by (cbn [sv_denot]; rewrite (EE3 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact HA0).
clear HJ. pose proof HJ3 as HJ.
psrr_branch_tok RUN BR HS SHOK ONN_LP_B0.
- (* a0 = 0: the frame is an announce, to the personality cut (+0x1e0) *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (onn_lp_E regs3) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (onn_lp_eqb0 _ (onn_lp_code_range (DSpec.fr_cmd b) (Z.of_nat (length (DSpec.fr_body b))))) in Hc.
  assert (HIGN : onann_ign b = false).
  { unfold onann_ign. rewrite <- Elen. change DLib.DIGINET_OK with 0. rewrite Hc. reflexivity. }
  assert (AOK3 : onann_a_ok W3 mem3 F buf b).
  { rewrite (onn_lp_anp_ok (DSpec.fr_cmd b) (buf + 30) (DSpec.fr_body b) aj Hc) in HAG.
    destruct (onn_lp_a_ok_of (w_H W3) mem3 (F + ONANN_A) (buf + 30) (DSpec.fr_body b) aj P_ajl Hbody HAG)
      as (AV & AN & AU & AL).
    exact (conj AV (conj AN (conj AU (conj AL HZ3)))). }
  paj_run_to_tok RUNTO HS HJ SHOK ONN_LP_B0 ONANN_PF.
  { onn_lp_awr_rs. apply awr_ok_x_nil. }
  onn_lp_name_md mdP.
  onn_lp_lo HS (onn_lp_E regs3) EPlo msP.
  onn_lp_kreg HS EPlo EE3 (2%bv : bv 5) 2%nat S2r P2. onn_lp_kreg HS EPlo EE3 (3%bv : bv 5) 3%nat S3r P3.
  onn_lp_kreg HS EPlo EE3 (4%bv : bv 5) 4%nat S4r P4. onn_lp_kreg HS EPlo EE3 (8%bv : bv 5) 8%nat S8r P8.
  onn_lp_kreg HS EPlo EE3 (9%bv : bv 5) 9%nat S9r P9. onn_lp_kreg HS EPlo EE3 (18%bv : bv 5) 18%nat S18r P18.
  onn_lp_kreg HS EPlo EE3 (19%bv : bv 5) 19%nat S19r P19. onn_lp_kreg HS EPlo EE3 (20%bv : bv 5) 20%nat S20r P20.
  onn_lp_kreg HS EPlo EE3 (22%bv : bv 5) 22%nat S22r P22. onn_lp_kreg HS EPlo EE3 (23%bv : bv 5) 23%nat S23r P23.
  onn_lp_kreg HS EPlo EE3 (24%bv : bv 5) 24%nat S24r P24. onn_lp_kreg HS EPlo EE3 (25%bv : bv 5) 25%nat S25r P25.
  onn_lp_kreg HS EPlo EE3 (26%bv : bv 5) 26%nat S26r P26.
  assert (KP : forall a, aview segs (w_H W3) (ms_mem msP) a = aview segs (w_H W3) mem3 a).
  { apply (onn_lp_kd_of_frame W3 _ _ mem3 (ms_mem msP) HFr). intros b0 wlo whi x Hin Hx. onn_lp_win Hin Hx. }
  assert (GP : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msP) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (onn_lp_cur_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mem3
    md3 (ms_mem msP) mdP 0 CUR3 HJ KP GP) as CURP.
  assert (TWP : tw_at TMAP_B (aview segs (w_H W3) (ms_mem msP)) Bw)
    by (apply (tw_kept TMAP_B (aview segs (w_H W3) mem3)); [exact TW3 | intros x _; exact (KP x)]).
  pose proof (onn_lp_a_ok_move W3 mem3 (ms_mem msP) F buf b AOK3 KP) as AOKP.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_PF)) mm rom) mdx) Q) end.
  apply (PF LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1
    F ly3 S3 W3 (ms_mem msP) mdP (ms_regs msP) HFIX).
  + unfold onann_pf_cur. exact (conj CURP (conj TWP (conj HIGN AOKP))).
  + exact (conj (conj (conj P2 (conj P3 (conj P4 (conj P8 (conj P9 (conj P18 (conj P19 P25))))))) (conj P20 P24))
      (conj P22 (conj P23 P26))).
- (* a0 <> 0: the frame is ignored, to the ignore cut (+0x1ac) *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (onn_lp_E regs3) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (onn_lp_eqb0 _ (onn_lp_code_range (DSpec.fr_cmd b) (Z.of_nat (length (DSpec.fr_body b))))) in Hc.
  assert (HIGN : onann_ign b = true).
  { unfold onann_ign. rewrite <- Elen. change DLib.DIGINET_OK with 0. rewrite Hc. reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK ONN_LP_B0 ONANN_IGN.
  { onn_lp_awr_rs. apply awr_ok_x_nil. }
  onn_lp_name_md mdP.
  onn_lp_lo HS (onn_lp_E regs3) EPlo msP.
  onn_lp_kreg HS EPlo EE3 (2%bv : bv 5) 2%nat S2r P2. onn_lp_kreg HS EPlo EE3 (3%bv : bv 5) 3%nat S3r P3.
  onn_lp_kreg HS EPlo EE3 (4%bv : bv 5) 4%nat S4r P4. onn_lp_kreg HS EPlo EE3 (8%bv : bv 5) 8%nat S8r P8.
  onn_lp_kreg HS EPlo EE3 (9%bv : bv 5) 9%nat S9r P9. onn_lp_kreg HS EPlo EE3 (18%bv : bv 5) 18%nat S18r P18.
  onn_lp_kreg HS EPlo EE3 (19%bv : bv 5) 19%nat S19r P19. onn_lp_kreg HS EPlo EE3 (20%bv : bv 5) 20%nat S20r P20.
  onn_lp_kreg HS EPlo EE3 (24%bv : bv 5) 24%nat S24r P24. onn_lp_kreg HS EPlo EE3 (25%bv : bv 5) 25%nat S25r P25.
  assert (KP : forall a, aview segs (w_H W3) (ms_mem msP) a = aview segs (w_H W3) mem3 a).
  { apply (onn_lp_kd_of_frame W3 _ _ mem3 (ms_mem msP) HFr). intros b0 wlo whi x Hin Hx. onn_lp_win Hin Hx. }
  assert (GP : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msP) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (onn_lp_cur_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mem3
    md3 (ms_mem msP) mdP 0 CUR3 HJ KP GP) as CURP.
  assert (TWP : tw_at TMAP_B (aview segs (w_H W3) (ms_mem msP)) Bw)
    by (apply (tw_kept TMAP_B (aview segs (w_H W3) mem3)); [exact TW3 | intros x _; exact (KP x)]).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_IGN)) mm rom) mdx) Q) end.
  apply (IGN LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos
    sp1 F ly3 S3 W3 (ms_mem msP) mdP (ms_regs msP) HFIX).
  + unfold onann_ign_cur. exact (conj CURP (conj TWP HIGN)).
  + exact (conj (conj P2 (conj P3 (conj P4 (conj P8 (conj P9 (conj P18 (conj P19 P25))))))) (conj P20 P24)).
Qed.
End main.
