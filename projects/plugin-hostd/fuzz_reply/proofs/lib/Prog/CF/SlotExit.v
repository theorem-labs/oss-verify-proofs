(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 663 lines of code are new or changed and 1184 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass9G.v, with its module paths, module names, addresses and numbers changed; 1606 of its 1709 lines of code are new or changed and 560 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass1w.v, with its module paths and addresses changed; 735 of its 816 lines of code are new or changed and 1628 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotEntry.v, with its module names changed; 1081 of its 1143 lines of code are new or changed and 754 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
  YK11 YK0o YK0s YK15 YM06 YP09 YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09
  YL01 YL00 YL0g YI06 YI16 YI14 YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import
  Img0 Contract ContractT FrameAPI SlotKept SlotPack AllocPack MemNorm AllocBound.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotMove SlotResReply SlotExitMove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import source_reset_c check_shape_ends_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c op_add_c SlotInv SlotSteps SlotRes SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessGlue HarnessFrame SlotHead SlotHeadQ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotExitRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotExitWip SlotEntry RelayCap SlotExitFinAux SlotExitFin SlotExitScanAux SlotExitScan SlotExitEndAux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require SlotRI3 SlotNcWt ListFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma xr_skip : forall (l : list (hsrc * nat)) jj, existsb (Nat.eqb jj) (map snd l) = false ->
  List.filter (fun p => Nat.leb (S jj) (snd p)) l = List.filter (fun p => Nat.leb jj (snd p)) l.
Proof.
  intros l jj. induction l as [|x l IH]; intros H; [reflexivity|].
  cbn [map existsb] in H. apply orb_false_iff in H as [H1 H2]. apply Nat.eqb_neq in H1.
  cbn [List.filter]. rewrite (IH H2).
  destruct (Nat.leb_spec (S jj) (snd x)); destruct (Nat.leb_spec jj (snd x)); try reflexivity; lia.
Qed.

Lemma xr_pick : forall (l : list (hsrc * nat)) jj y, List.NoDup (map snd l) -> In y l -> snd y = jj ->
  exists l1 l2, List.filter (fun p => Nat.leb jj (snd p)) l = l1 ++ y :: l2 /\
    List.filter (fun p => Nat.leb (S jj) (snd p)) l = l1 ++ l2.
Proof.
  intros l jj y. induction l as [|x l IH]; intros ND Hy Hs; [destruct Hy|].
  cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NX ND].
  destruct Hy as [EX|Hy].
  - subst x.
    assert (NE : existsb (Nat.eqb jj) (map snd l) = false).
    { apply not_true_iff_false. intros X. apply existsb_exists in X as (z & Hz & Ez).
      apply Nat.eqb_eq in Ez. subst z. apply NX. rewrite Hs. exact Hz. }
    exists [], (List.filter (fun p => Nat.leb jj (snd p)) l). cbn [List.filter app]. rewrite Hs, Nat.leb_refl.
    destruct (Nat.leb_spec (S jj) jj) as [X|_]; [lia|]. split; [reflexivity|exact (xr_skip l jj NE)].
  - destruct (IH ND Hy Hs) as (l1 & l2 & E1 & E2).
    assert (NE : snd x <> jj).
    { intros X. apply NX. rewrite X, <- Hs. apply in_map. exact Hy. }
    cbn [List.filter]. rewrite E1, E2.
    destruct (Nat.leb_spec jj (snd x)); destruct (Nat.leb_spec (S jj) (snd x)); try lia.
    + exists (x :: l1), l2. split; reflexivity.
    + exists l1, l2. split; reflexivity.
Qed.

Lemma xr_zero : forall (l : list (hsrc * nat)), List.filter (fun p => Nat.leb 0 (snd p)) l = l.
Proof. intros l. induction l as [|x l IH]; [reflexivity|exact (f_equal (cons x) IH)]. Qed.

Lemma held_back : forall h H' q, hl_v H' = hl_v (hs_held h) -> hl_cap H' = hl_cap (hs_held h) ->
  In q (hs_blocks h) -> In q (hs_blocks (set_held h H')) \/ In q (map fst (hl_recs (hs_held h))).
Proof.
  intros h H' q EV EC Hq. unfold hs_blocks in Hq. unfold hs_blocks, set_held.
  cbn [hs_pending hs_partial hs_expected hs_held].
  apply in_app_or in Hq as [Hq|Hq]; [left; apply in_or_app; left; exact Hq|].
  apply in_app_or in Hq as [Hq|Hq]; [left; apply in_or_app; right; apply in_or_app; left; exact Hq|].
  apply in_app_or in Hq as [Hq|Hq].
  { left. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hq. }
  unfold list_blocks in Hq. apply in_app_or in Hq as [Hq|Hq]; [|right; exact Hq].
  left. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
  unfold list_blocks. apply in_or_app. left. rewrite EV, EC. exact Hq.
Qed.

Section End.
Context {rc : RunCeil} {fx0 fx : FPState} {B : malloc_syms} {API : forall rc : RunCeil, AllocAPI B}
  {LS : lib_shape} {SH : sink_head} {SK : sink_syms} {ra empty : Z} {j : nat} {CS : list byte -> list Z}
  {F : ResFormT} {E : sstart} {RI : res_inv} {t k : Z} {L0 : layout} {A0 : astate} {regs0 : bvmap 5 word}
  {m0 : word -> option byte} {md0 : Model} {cl br gn dd ei G nfd : Z} {mx nout cap out : word}
  {es : list rentry} {hj : list (hsrc * nat)} {OUT' CAP' : Z} {Hs : nat -> hlist}.

Hypothesis HFR : slot_frame B API LS SH SK ra empty rc fx0 j E CS.
Hypothesis HRE : RI_end RI CS.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis HAX : AllocExtra B (aa_MR (API rc)).
Hypothesis HBW : blocks_writable B (API rc).
Hypothesis HPLG : forall a, 0x30fc0 <= a < 0x311c0 \/ 0x20d38 <= a < 0x20d48 -> img_plain B a.
Hypothesis HEA : errno_addr B = 0x311ec.
Hypothesis HTPE : YK11.getr (ss_regs E) 4 = Z_to_bv 64 (ms_tp B).
Hypothesis HB1 : @YM05.alloc_ceiling rc <= spZ (ss_regs E) - SLOT_STACK.
Hypothesis HB2 : slot_sp E + 192 < 2 ^ 63.
Hypothesis HB3 : slot_sp E mod 16 = 0.
Hypothesis HB4 : spZ (ss_regs E) = slot_sp E + 192.
Hypothesis HCSD : check_shape_done_contract.
Hypothesis HSRC : @source_reset_contract fx rc B (API rc) F.
Hypothesis HR0 : forall L A G1 out1 es1 hj1, RI E k (view_of G1 out1 es1 hj1) L A -> List.NoDup (map fst (blocks L A)) ->
  res_tr F (exit_RV_s RI E k L A G1 out1 es1 hj1 [] []) A [].
Hypothesis HR1 : forall L A mem HA h G1 out1 es1 hj1, RI E k (view_of G1 out1 es1 hj1) L A ->
  List.NoDup (map fst (blocks L A)) -> src_at (rc := rc) B L A mem HA h ->
  res_tr F (reset_RV_s RI E k L A G1 out1 es1 hj1 h) A (source_reset_tr (known_at L A) h).
Hypothesis HFZ : frm_zero (@fp_csr fx).
Hypothesis HEXS : exit_state (rc := rc) B (API rc) E RI t k L0 A0 regs0 m0 md0 cl br gn dd ei G nfd mx nout cap out
  es hj.
Hypothesis HLIVE : send_live cl br dd (entries_total es) = true ->
  entries_total es <= CAP' /\ CAP' <= Z.max (bv_unsigned cap) (2 * entries_total es) /\
  fresh_block (rc := rc) B OUT' CAP' /\
  (forall q m, In (q, m) (blocks L0 A0) -> q <> bv_unsigned out -> ~ In q (concat (map entry_blocks es)) -> 0 < m ->
     q <> OUT').
Hypothesis HHS : forall p, (p < length hj)%nat ->
  hl_v (Hs p) = hl_v (hs_held (fst (nth p hj pd0))) /\ hl_cap (Hs p) = hl_cap (hs_held (fst (nth p hj pd0))) /\
  hl_recs (Hs p) = [].

Definition xN : nat := length es.
Definition xTOT : Z := entries_total es.
Definition xOUT : Z := bv_unsigned out.
Definition xCAP : Z := bv_unsigned cap.
Definition xlive : bool := send_live cl br dd xTOT.
Definition xoff : bool := send_off cl br xTOT.
Definition xb : Z := slot_sp E.
Definition xh (p : nat) : hsrc := fst (nth p hj pd0).
Definition xs (p : nat) : nat := snd (nth p hj pd0).
Definition xHA (i : nat) : Z := G_S + SRC_SIZE * Z.of_nat i.
Definition xcur (p : nat) : hsrc := set_held (xh p) (Hs p).
Definition xNO : word := Z_to_bv 64 (if xlive then xTOT else 0).
Definition xCAPw : word := if xlive then Z_to_bv 64 CAP' else cap.
Definition xOUTw : word := if xlive then Z_to_bv 64 OUT' else out.
Definition xTA : list Z := target_addrs G xOUT es hj.
Definition xE (a : Z) : Prop := exit_fin_E xlive xOUT xCAP G a \/ scan_E hj a \/ G_S <= a < G_S + SRC_SIZE * 4.
Definition xF (q : Z) : Prop :=
  exit_fin_F xlive xOUT es q \/ scan_F hj q \/ exists p, (p < xN)%nat /\ In q (hs_blocks (xh p)).
Definition xrest (jj : nat) : list (hsrc * nat) := List.filter (fun p => Nat.leb jj (snd p)) hj.
Definition xV (jj : nat) : rview := view_of G (if xlive then OUT' else xOUT) [] (xrest jj).

Definition xprov (jj : nat) (L : layout) (A : astate) : Prop :=
  forall q m, In (q, m) (blocks L A) ->
    (In (q, m) (blocks (ss_L E) (ss_A E)) /\ ~ In (q, m) (ss_T E)) \/ q = G \/
    (xlive = true /\ q = OUT' /\ m = CAP') \/ (xlive = false /\ 0 < xCAP /\ q = xOUT /\ m = xCAP) \/
    exists p, (p < xN)%nat /\ (jj <= xs p)%nat /\ In q (hs_blocks (xcur p)).

Definition xglob (mem : word -> option byte) : Prop :=
  rw_cells (ms_segs B) mem G_LISTEN [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
  rw_cells (ms_segs B) mem G_WAKE0 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
  rw_cells (ms_segs B) mem G_THREAD_UP [C1 (Z_to_bv 8 0)] /\
  rw_cells (ms_segs B) mem G_NSRC [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16)] /\
  rw_cells (ms_segs B) mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
  rw_cells (ms_segs B) mem (G_LOCK + 12) [CB 28 (nulbytes 28)] /\
  rw_cells (ms_segs B) mem G_SRC [C8 (Z_to_bv 64 G)] /\
  rw_cells (ms_segs B) mem G_BROKEN [C1 (Z_to_bv 8 (if xoff then br else dd))] /\
  rw_cells (ms_segs B) mem G_GONE [C1 (Z_to_bv 8 gn)] /\
  rw_cells (ms_segs B) mem G_DEAD [C1 (Z_to_bv 8 dd)] /\
  rw_cells (ms_segs B) mem G_EINTR [C1 (Z_to_bv 8 (if xoff then ei else 0))] /\
  rw_cells (ms_segs B) mem G_OUTV [C8 mx; C8 xNO; C8 xCAPw; C8 xOUTw].

Definition xfacts (jj : nat) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop :=
  rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) xE xF L0 A0 m0 md0 L A mem md /\
  st_init_done A = true /\ ro_agree (ms_segs B) mem /\ RI E k (xV jj) L A /\
  rw_cells (ms_segs B) mem (xb + 88) (saved_cells (ss_regs E)) /\
  xglob mem /\
  (forall p, (p < xN)%nat -> (jj <= xs p)%nat -> src_at (rc := rc) B L A mem (xHA (xs p)) (xcur p)) /\
  (forall i, (i < 4)%nat -> ((i < jj)%nat \/ slot_open hj i = false) ->
     rw_cells (ms_segs B) mem (xHA i) [CB 96%nat (nulbytes 96)]) /\
  In (G, SRC_TABLE) (blocks L A) /\
  (xlive = true -> In (OUT', CAP') (blocks L A)) /\
  (xlive = false -> 0 < xCAP -> In (xOUT, xCAP) (blocks L A)) /\ xprov jj L A.

Definition xkeep (regs : bvmap 5 word) : Prop :=
  forall r, (r = 2 \/ r = 3 \/ r = 4) -> YK11.getr regs (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r).

Definition x_call (jj : nat) (c : config) : Prop :=
  exists L A regs mem md,
    c = mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x145fc) mem (seg_rom (ms_segs B))) md /\
    xkeep regs /\ getr regs 1 = Z_to_bv 64 0x141a4 /\ getr regs 8 = Z_to_bv 64 (xHA jj) /\
    getr regs 9 = Z_to_bv 64 0x311c0 /\ getr regs 10 = Z_to_bv 64 (xHA jj) /\ xfacts jj L A mem md.

Definition x_back (jj : nat) (c : config) : Prop :=
  exists L A regs mem md,
    c = mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x141a4) mem (seg_rom (ms_segs B))) md /\
    xkeep regs /\ getr regs 8 = Z_to_bv 64 (xHA jj) /\ getr regs 9 = Z_to_bv 64 0x311c0 /\
    xfacts (S jj) L A mem md.

Definition x_end (c : config) : Prop :=
  exists L A regs mem md,
    c = mkCfg (@YK11.mkst fx regs (ret_pc (YK11.getr (ss_regs E) (Z_to_bv 5 1))) mem (seg_rom (ms_segs B))) md /\
    YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 0 /\ regs_preserved (ss_regs E) regs /\ xfacts 4 L A mem md.

Definition xm2 (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 (if gn =? 0 then xTOT else 0) /\
  rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) (fun a => exit_fin_E xlive xOUT xCAP G a \/ scan_E hj a)
    (fun q => exit_fin_F xlive xOUT es q \/ scan_F hj q) L0 A0 m0 md0 L A mem md /\
  st_init_done A = true /\ ro_agree (ms_segs B) mem /\
  (forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 20 \/ 25 <= r <= 27) ->
     YK11.getr regs (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r)) /\
  rw_cells (ms_segs B) mem (xb + 88) (saved_cells (ss_regs E)) /\
  rw_cells (ms_segs B) mem G_WAKE0 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
  rw_cells (ms_segs B) mem G_GONE [C1 (Z_to_bv 8 gn)] /\
  rw_cells (ms_segs B) mem (G_LOCK + 12) [CB 28 (nulbytes 28)] /\
  rw_cells (ms_segs B) mem G_THREAD_UP [C1 (Z_to_bv 8 0)] /\
  rw_cells (ms_segs B) mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
  rw_cells (ms_segs B) mem G_NSRC [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16)] /\
  rw_cells (ms_segs B) mem G_SRC [C8 (Z_to_bv 64 G)] /\
  rw_cells (ms_segs B) mem G_LISTEN [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
  rw_cells (ms_segs B) mem G_BROKEN [C1 (Z_to_bv 8 (if xoff then br else dd))] /\
  rw_cells (ms_segs B) mem G_DEAD [C1 (Z_to_bv 8 dd)] /\
  rw_cells (ms_segs B) mem G_EINTR [C1 (Z_to_bv 8 (if xoff then ei else 0))] /\
  (forall p, (p < length hj)%nat ->
     src_at (rc := rc) B L A mem (G_S + SRC_SIZE * Z.of_nat (snd (nth p hj pd0))) (set_held (fst (nth p hj pd0)) (Hs p))) /\
  (forall i, (i < 4)%nat -> slot_open hj i = false ->
     rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat i) [CB 96%nat (nulbytes 96)]) /\
  In (G, SRC_TABLE) (blocks L A) /\
  (forall q m, In (q, m) (blocks L A) <->
     ((In (q, m) (blocks L0 A0) /\ q <> xOUT /\ ~ In q (concat (map entry_blocks es))) \/
      (xlive = true /\ q = OUT' /\ m = CAP') \/ (xlive = false /\ 0 < xCAP /\ q = xOUT /\ m = xCAP)) /\
     ~ scan_F hj q) /\
  (xlive = false -> rw_cells (ms_segs B) mem G_OUTV [C8 mx; C8 (Z_to_bv 64 0); C8 cap; C8 out]) /\
  (xlive = true ->
     rw_cells (ms_segs B) mem G_OUTV [C8 mx; C8 (Z_to_bv 64 xTOT); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')]) /\
  RI E k (view_of G (if xlive then OUT' else xOUT) [] hj) L A.

Ltac exs := pose proof HEXS as (Ht & Hk & Hn & HX & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK &
  HGL & Hnfd & HOUT & HREL & Hes & Hcost & HRI).

Lemma x_len : length hj = xN.
Proof.
  exs. pose proof HREL as (_ & _ & _ & _ & _ & _ & HPA & _). symmetry. exact (Forall2_length HPA).
Qed.

Lemma x_wf0 : WF A0.
Proof. exs. exact HWF. Qed.

Lemma x_ndb : forall L A mem md, aa_MR (API rc) L A mem md -> List.NoDup (map fst (blocks L A)).
Proof.
  intros L A mem md HM. pose proof HFR as (FF & _).
  assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
  pose proof (ALL rc fx) as FA.
  assert (NDB : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
  pose proof (NDB L A mem md HM) as X. first [exact (proj1 (NoDup_ListNoDup _) X)|exact X].
Qed.

Lemma x_rest_len : forall jj, (length (xrest jj) <= 4)%nat.
Proof.
  intros jj. unfold xrest. pose proof (mv_filter_len (fun p => Nat.leb jj (snd p)) hj) as H.
  rewrite x_len in H. exs. unfold xN in H. lia.
Qed.

Lemma x_in : forall p, (p < xN)%nat -> In (nth p hj pd0) hj.
Proof. intros p Hp. apply nth_In. rewrite x_len. exact Hp. Qed.

Lemma x_hj : forall p, In p hj -> src_at (rc := rc) B L0 A0 m0 (G_S + SRC_SIZE * Z.of_nat (snd p)) (fst p) /\
  (snd p < 4)%nat.
Proof.
  intros p Hp. exs. pose proof HREL as (_ & _ & _ & _ & _ & _ & HPA & _).
  destruct (In_nth _ _ pd0 Hp) as (i & Hi & <-).
  assert (Hi' : (i < length es)%nat) by (rewrite (Forall2_length HPA); exact Hi).
  destruct (nth_error es i) as [e0|] eqn:He; [|apply nth_error_None in He; lia].
  pose proof (f2_nth _ _ _ e0 pd0 i HPA Hi') as X. unfold pair_ok in X. cbv zeta in X.
  destruct X as (S1 & S2 & _). split; [exact S1|exact S2].
Qed.

Lemma x_nd : NoDup xTA.
Proof. exs. pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NDA). exact NDA. Qed.

Lemma x_tg : forall p q, In p hj -> In q (hs_blocks (fst p)) ->
  q <> G /\ q <> xOUT /\ ~ In q (concat (map entry_blocks es)).
Proof.
  intros p q Hp Hq. destruct (fin_target G xOUT es hj x_nd) as (_ & _ & _ & _ & TPH). exact (TPH p q Hp Hq).
Qed.

Lemma x_ta_hs : forall p q, In p hj -> In q (hs_blocks (fst p)) -> In q xTA.
Proof.
  intros p q Hp Hq. unfold xTA, target_addrs. right. right. apply in_or_app. right. apply in_concat.
  exists (hs_blocks (fst p)). split; [exact (in_map (fun p0 => hs_blocks (fst p0)) hj p Hp)|exact Hq].
Qed.

Lemma x_pos0 : forall p q, In p hj -> In q (hs_blocks (fst p)) -> exists m, 0 < m /\ In (q, m) (blocks L0 A0).
Proof. intros p q Hp Hq. exact (blk_pos _ _ _ _ _ q (proj1 (x_hj p Hp)) Hq). Qed.

Lemma x_out : xlive = true -> forall p q, In p hj -> In q (hs_blocks (fst p)) -> q <> OUT'.
Proof.
  intros HL p q Hp Hq. destruct (HLIVE HL) as (_ & _ & _ & HQ).
  destruct (x_pos0 p q Hp Hq) as (m & M1 & M2). destruct (x_tg p q Hp Hq) as (_ & T2 & T3).
  exact (HQ q m M2 T2 T3 M1).
Qed.

Lemma x_slt : forall p, (p < xN)%nat -> (xs p < 4)%nat.
Proof. intros p Hp. exact (proj2 (x_hj _ (x_in p Hp))). Qed.

Lemma x_sinj : forall p p', (p < xN)%nat -> (p' < xN)%nat -> xs p = xs p' -> p = p'.
Proof.
  intros p p' Hp Hp' HSS. exs. pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & NDH & _).
  apply NoDup_ListNoDup in NDH. pose proof x_len as LH.
  apply (proj1 (List.NoDup_nth_error _) NDH p p').
  - rewrite length_map. lia.
  - rewrite !nth_error_map. rewrite (nth_error_nth' hj pd0 (n := p)) by lia.
    rewrite (nth_error_nth' hj pd0 (n := p')) by lia.
    cbn. unfold xs in HSS. rewrite HSS. reflexivity.
Qed.

Lemma x_disj : forall p p' q, (p < xN)%nat -> (p' < xN)%nat -> p <> p' ->
  In q (hs_blocks (xh p)) -> In q (hs_blocks (xh p')) -> False.
Proof.
  intros p p' q Hp Hp' Hne H1 H2. pose proof x_nd as ND. apply NoDup_ListNoDup in ND.
  unfold xTA, target_addrs in ND. apply List.NoDup_cons_iff in ND as [_ ND].
  apply List.NoDup_cons_iff in ND as [_ ND].
  apply List.NoDup_app_remove_l in ND. pose proof x_len as LH.
  apply (nodup_concat_nth (fun p => hs_blocks (fst p)) hj pd0 p p' q ND); [lia|lia|exact Hne|exact H1|exact H2].
Qed.

Lemma x_open : forall jj, slot_open hj jj = true -> exists p, (p < xN)%nat /\ xs p = jj.
Proof.
  intros jj H. unfold slot_open in H. apply existsb_exists in H as (x & Hx & Ex). apply Nat.eqb_eq in Ex. subst x.
  destruct (In_nth _ _ (snd pd0) Hx) as (p & Hp & Ep). rewrite length_map, x_len in Hp.
  exists p. split; [exact Hp|]. unfold xs. rewrite <- Ep. symmetry. apply (map_nth snd).
Qed.

Lemma x_open_rev : forall p, (p < xN)%nat -> slot_open hj (xs p) = true.
Proof.
  intros p Hp. unfold slot_open. apply existsb_exists. exists (xs p). split; [|apply Nat.eqb_refl].
  exact (in_map snd hj _ (x_in p Hp)).
Qed.

Lemma x_rest_skip : forall jj, slot_open hj jj = false -> xrest (S jj) = xrest jj.
Proof. intros jj H. exact (xr_skip hj jj H). Qed.

Lemma x_rest_pick : forall jj p, (p < xN)%nat -> xs p = jj ->
  exists p1 p2, pend_view (xrest jj) = p1 ++ map snd (hl_recs (hs_pending (xh p))) :: p2 /\
                pend_view (xrest (S jj)) = p1 ++ p2.
Proof.
  intros jj p Hp Hsp. exs. pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & NDH & _).
  apply NoDup_ListNoDup in NDH.
  destruct (xr_pick hj jj (nth p hj pd0) NDH (x_in p Hp) Hsp) as (l1 & l2 & E1 & E2).
  exists (pend_view l1), (pend_view l2). unfold xrest, pend_view. rewrite E1, E2, !map_app. split; reflexivity.
Qed.

Lemma x_cur : forall p q, (p < xN)%nat -> In q (hs_blocks (xcur p)) -> In q (hs_blocks (xh p)).
Proof.
  intros p q Hp Hq. rewrite <- x_len in Hp. destruct (HHS p Hp) as (V1 & V2 & V3).
  exact (held_done_blocks _ _ q V1 V2 V3 Hq).
Qed.

Lemma x_move_reset : forall jj p L A mem md L' A', (p < xN)%nat -> xs p = jj -> aa_MR (API rc) L A mem md ->
  List.NoDup (map fst (blocks L' A')) -> src_at (rc := rc) B L A mem (xHA jj) (xcur p) ->
  (forall t, In t (blocks L' A') <-> In t (blocks L A) /\ ~ In (fst t) (hs_blocks (xcur p))) ->
  nc_move (view_of G (if xlive then OUT' else xOUT) [] (xrest jj)) L A
    (view_of G (if xlive then OUT' else xOUT) [] (xrest (S jj))) L' A' (src_dels (xcur p)) [].
Proof.
  intros jj p L A mem md L' A' Hp Hsp HM NP Sx HP.
  pose proof HEXS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREL & _).
  pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & NDH & _).
  apply NoDup_ListNoDup in NDH.
  destruct (xr_pick hj jj (nth p hj pd0) NDH (x_in p Hp) Hsp) as (l1 & l2 & E1 & E2).
  unfold xrest. rewrite E1, E2.
  apply (mv_reset L A L' A' G (if xlive then OUT' else xOUT) l1 l2 (nth p hj pd0) (xcur p)).
  - exact (x_ndb L A mem md HM).
  - exact NP.
  - intros q m Hq. exact (proj1 (mv_blk B (API rc) L A mem md q m HM Hq)).
  - exact (mv_src_dels_in B L A mem (xHA jj) (xcur p) Sx).
  - pose proof Sx as S. apply src_at_iff in S. destruct S as (_ & _ & _ & ND).
    first [exact (proj1 (NoDup_ListNoDup _) ND)|exact ND].
  - pose proof Hp as Hp'. rewrite <- x_len in Hp'. destruct (HHS p Hp') as (V1 & V2 & _).
    unfold xcur. apply mv_set_held_nc; assumption.
  - intros q Hq. pose proof (x_cur p q Hp Hq) as Hq0. destruct (x_tg _ q (x_in p Hp) Hq0) as (T1 & T2 & _).
    split; [exact T1|]. split.
    + destruct xlive eqn:HL; [exact (x_out HL _ q (x_in p Hp) Hq0)|exact T2].
    + intros X. apply in_concat in X as (l & Hl & Hq'). apply in_map_iff in Hl as (z & <- & Hz). cbv beta in Hq'.
      assert (Hz' : In z (List.filter (fun p => Nat.leb (S jj) (snd p)) hj)) by (rewrite E2; exact Hz).
      apply filter_In in Hz' as (Hzh & Hzs). apply Nat.leb_le in Hzs.
      destruct (In_nth _ _ pd0 Hzh) as (p' & Hp' & Ep). rewrite x_len in Hp'.
      assert (Hsz : xs p' = snd z) by (unfold xs; rewrite Ep; reflexivity).
      assert (Hne : p <> p') by (intros ->; lia).
      apply (x_disj p p' q Hp Hp' Hne Hq0). apply mv_snc_hb. unfold xh. rewrite Ep. exact Hq'.
  - exact HP.
Qed.

Lemma x_gl : (cl = 3 \/ cl = -1) /\ (br = 0 \/ br = 1) /\ (gn = 0 \/ gn = 1) /\ (dd = 0 \/ dd = 1) /\
  (ei = 0 \/ ei = 1) /\ ((gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) /\ (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1)).
Proof.
  exs. pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R1 & R2 & R3 & R4 & R5 & R6 & _).
  tauto.
Qed.

Lemma x_gn : xlive = true -> gn = 0.
Proof.
  intros HL. pose proof x_gl as (RCL & RBR & RGN & RDD & _ & (_ & G1)).
  destruct RGN as [|E1]; [assumption|]. exfalso. unfold xlive, send_live, send_off in HL.
  apply andb_prop in HL as [H1 H2]. apply negb_true_iff in H1. apply orb_false_iff in H1 as [H1 H3].
  apply orb_false_iff in H1 as [H1 H4]. apply Z.ltb_ge in H1. apply Z.eqb_neq in H4. apply Z.eqb_eq in H2.
  destruct (G1 E1) as [X|[X|X]]; lia.
Qed.

Lemma x_tot0 : gn = 0 -> xlive = false -> xTOT = 0.
Proof.
  intros H0 HL. pose proof x_gl as (_ & _ & _ & _ & _ & (G0 & _)).
  destruct (G0 H0) as (E1 & E2 & E3). unfold xlive, send_live, send_off in HL. rewrite E1, E2, E3 in HL.
  destruct (Z.eqb_spec xTOT 0) as [X|X]; [exact X|].
  try rewrite (proj2 (Z.eqb_neq _ _) X) in HL. cbn in HL. discriminate.
Qed.

Lemma x_livepos : xlive = true -> 0 < xTOT.
Proof.
  intros HL. pose proof (exit_entries_nonneg es). unfold xlive, send_live, send_off in HL.
  destruct (Z.eqb_spec xTOT 0) as [X|X]; [|unfold xTOT in *; lia].
  try rewrite (proj2 (Z.eqb_eq _ _) X) in HL. rewrite !orb_true_r in HL. cbn in HL. discriminate.
Qed.

Lemma x_tot : 0 <= xTOT <= k.
Proof.
  exs. pose proof HREL as (_ & _ & _ & HES & _ & _ & HPA & _).
  split; [apply exit_entries_nonneg|]. eapply Z.le_trans; [|exact Hcost].
  apply exit_entries_cost; [exact (Forall2_length HPA)|]. eapply Forall_impl; [|exact HES].
  intros e (_ & _ & _ & _ & _ & _ & U & _). rewrite <- U. lia.
Qed.

Lemma x_kb : k < 2 ^ 26.
Proof. exs. unfold INPUT_MAX in Hn. lia. Qed.

Lemma x_ac : @YM05.alloc_ceiling rc + 65344 <= xb /\ 2 ^ 40 <= @YM05.alloc_ceiling rc /\
  xb + 192 < 2 ^ 63 /\ xb mod 16 = 0 /\ spZ (ss_regs E) = xb + 192.
Proof.
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc).
  unfold xb. split; [pose proof HB1 as X; rewrite HB4 in X; unfold SLOT_STACK in X; lia|]. split; [lia|].
  split; [exact HB2|]. split; [exact HB3|exact HB4].
Qed.

Lemma x_sp : forall regs, xkeep regs -> YK11.getr regs (Z_to_bv 5 2) = Z_to_bv 64 xb.
Proof. intros regs KP. rewrite (KP 2 ltac:(lia)). exs. destruct HR as (B2 & _). exact B2. Qed.

Lemma x_spZ : forall regs, xkeep regs -> spZ regs = xb.
Proof.
  intros regs KP. unfold spZ. transitivity (bv_unsigned (YK11.getr regs (Z_to_bv 5 2))); [reflexivity|].
  rewrite (x_sp regs KP). apply unsigned_lit. pose proof x_ac as (A1 & A2 & A3 & _). lia.
Qed.

Lemma x_gp : forall regs, xkeep regs -> YK11.getr regs (Z_to_bv 5 3) = YK11.getr (ss_regs E) (Z_to_bv 5 3).
Proof. intros regs KP. rewrite (KP 3 ltac:(lia)). exs. destruct HR as (_ & B3 & _). exact B3. Qed.

Lemma x_tp : forall regs, xkeep regs -> YK11.getr regs (Z_to_bv 5 4) = YK11.getr (ss_regs E) (Z_to_bv 5 4).
Proof. intros regs KP. rewrite (KP 4 ltac:(lia)). exs. destruct HR as (_ & _ & B4 & _). exact B4. Qed.

Lemma x_outat : (0 < xCAP -> In (xOUT, xCAP) (blocks L0 A0)) /\ (xCAP = 0 -> xOUT = 0) /\ 0 <= xCAP <= TBBYTES.
Proof.
  exs. destruct HOUT as ((O & junk & HO) & HC). pose proof (bv_unsigned_in_range 64 cap) as R.
  unfold bv_modulus in R. unfold xCAP, xOUT.
  destruct HO as [(C0 & O0 & _)|(C0 & _ & IN & _)].
  - split; [intros X; exfalso; lia|]. split; [intros _; exact O0|]. lia.
  - split; [intros _; exact IN|]. split; [lia|]. lia.
Qed.

Lemma x_gb : In (G, SRC_TABLE) (blocks L0 A0) /\ fresh_block (rc := rc) B G SRC_TABLE.
Proof. exs. pose proof HREL as (_ & GIN & GFR & _). split; assumption. Qed.

Lemma x_E : forall a, xE a ->
  in_globals G_reply a \/ exists q n, In (q, n) (blocks L0 A0) /\ In q xTA /\ q <= a < q + n.
Proof.
  intros a [X|[X|X]].
  - unfold exit_fin_E, send_writes in X.
    destruct X as [X|[[X|[X|[X|(LV & X)]]]|[X|[X|[X|X]]]]];
      try (left; apply in_G_bss; unfold G_OUTV, G_BROKEN, G_EINTR, G_LOCK, G_NSRC in X; lia).
    + right. exists xOUT, xCAP. split; [apply (proj1 x_outat); lia|].
      split; [unfold xTA, target_addrs; right; left; reflexivity|lia].
    + left. exists 0x20d38, 16. split; [left; reflexivity|]. unfold G_LISTEN, G_CLIENT in X. lia.
    + right. exists G, SRC_TABLE. split; [exact (proj1 x_gb)|].
      split; [unfold xTA, target_addrs; left; reflexivity|lia].
  - destruct X as (p & Hp & [X|(Xc & X)]).
    + left. apply in_G_bss. pose proof (proj2 (x_hj p Hp)). unfold G_S, SRC_SIZE in X. lia.
    + right. destruct (x_hj p Hp) as [S _]. apply src_at_iff in S. destruct S as (_ & _ & LH & _).
      destruct (hf_list_v B L0 A0 m0 _ _ _ LH Xc) as [X1 X2].
      exists (hl_v (hs_held (fst p))), (16 * hl_cap (hs_held (fst p))). split; [exact X1|].
      split; [exact (x_ta_hs p _ Hp (held_in_blocks _ _ X2))|lia].
  - left. apply in_G_bss. unfold G_S, SRC_SIZE in X. lia.
Qed.

Lemma x_F : forall q, xF q -> In q xTA.
Proof.
  intros q [X|[X|X]].
  - unfold exit_fin_F in X. unfold xTA, target_addrs. destruct X as [(_ & ->)|X].
    + right. left. reflexivity.
    + right. right. apply in_or_app. left. exact X.
  - destruct X as (p & Hp & Hq). apply (x_ta_hs p q Hp). apply held_in_blocks. unfold list_blocks.
    apply in_or_app. right. exact Hq.
  - destruct X as (p & Hp & Hq). exact (x_ta_hs _ q (x_in p Hp) Hq).
Qed.

Ltac xg_tac T Q := apply T; [exact Q|]; intros i Hi; cbn [cells_size csize] in Hi;
  unfold G_WAKE0, G_GONE, G_LOCK, G_THREAD_UP, G_NSRC, G_SRC, G_LISTEN, G_BROKEN, G_DEAD, G_EINTR, G_OUTV, G_S; lia.

Lemma xglob_keep : forall mem mem',
  (forall a cs, rw_cells (ms_segs B) mem a cs ->
     (forall i, 0 <= i < Z.of_nat (cells_size cs) -> 0x30fc0 <= a + i < G_S \/ 0x20d38 <= a + i < 0x20d48) ->
     rw_cells (ms_segs B) mem' a cs) ->
  xglob mem -> xglob mem'.
Proof.
  intros mem mem' T (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
  split; [xg_tac T Q1|]. split; [xg_tac T Q2|]. split; [xg_tac T Q3|]. split; [xg_tac T Q4|].
  split; [xg_tac T Q5|]. split; [xg_tac T Q6|]. split; [xg_tac T Q7|]. split; [xg_tac T Q8|].
  split; [xg_tac T Q9|]. split; [xg_tac T Q10|]. split; [xg_tac T Q11|]. xg_tac T Q12.
Qed.

Lemma x_nowrite : forall jj L A mem md m1, xfacts jj L A mem md ->
  mem_rel rsegs m1 (normalize rsegs mem) -> ro_same rsegs mem m1 -> xfacts jj L A m1 md.
Proof.
  intros jj L A mem md m1 RF MREL ROS.
  destruct RF as (RMC & INIT & RO & HRI & ST & GL & SRCS & ZS & GIN & OIN & OIN2 & PV).
  pose proof RMC as (HM & HWF' & HBD & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC).
  pose proof x_ac as (A1 & A2 & A3 & A4 & A5).
  pose proof x_wf0 as HWF0.
  assert (RO' : ro_agree rsegs mem) by (rewrite <- HSEG; exact RO).
  assert (HK : @YM05.alloc_ceiling rc <= xb - SOURCE_RESET_K)
    by (unfold SOURCE_RESET_K, SOURCE_RESET_FRAME, ALLOC_STACK; lia).
  destruct (rmid_norm B (API rc) SOURCE_RESET_K xb (fun _ => False) (fun _ => False) L A mem md
              (normalize rsegs mem) m1 [] HSEG RO' MREL ROS (munch_refl _ _) (wmono_refl _ _) HM HWF' HBD HK)
    as (RMn & MU & WM).
  { intros a Ha. apply SC. unfold sk in *. rewrite A5.
    unfold SLOT_STACK, SOURCE_RESET_K, SOURCE_RESET_FRAME, ALLOC_STACK in *. lia. }
  { intros x Hx O. exfalso. exact (O I). }
  { intros a Ho. exact I. }
  { intros p n i Hp Hi O. exfalso. exact (O I). }
  assert (WM' : wmono (ms_segs B) mem m1) by (rewrite HSEG; exact WM).
  assert (TR : forall a cs, rw_cells (ms_segs B) mem a cs -> rw_cells (ms_segs B) m1 a cs)
    by (intros a cs H; exact (rw_cells_transport (ms_segs B) [] mem m1 a cs H MU WM' I)).
  assert (RMw : rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) (fun _ => False) (fun _ => False) L A mem md L A m1 md).
  { apply (rmid_widen B (API rc) SOURCE_RESET_K xb); [exact HM| | | | | |intros a _ X; exact X|exact RMn].
    - rewrite A5. unfold SLOT_STACK, SOURCE_RESET_K, SOURCE_RESET_FRAME, ALLOC_STACK. lia.
    - lia.
    - rewrite A5. unfold SLOT_STACK. lia.
    - lia.
    - intros a Ha. apply SC. unfold sk. left. exact Ha. }
  split.
  { eapply rmid_EF; [exact (rmid_seq B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF0 RMC RMw)| |].
    - intros a [X|[]]. exact X.
    - intros q [X|[]]. exact X. }
  split; [exact INIT|].
  split; [rewrite HSEG; exact (ro_agree_same rsegs mem m1 RO' ROS)|].
  split; [exact HRI|].
  split; [exact (TR _ _ ST)|].
  split; [exact (xglob_keep mem m1 (fun a cs H _ => TR a cs H) GL)|].
  split.
  { intros p Hp Hj. pose proof (x_slt p Hp).
    apply (fin_src rc B (API rc) SOURCE_RESET_K xb (fun _ => False) (fun _ => False) L A mem md L A m1 md
             (xHA (xs p)) _ HAX HBW HSEG HK HM RMn); [| |exact (SRCS p Hp Hj)].
    - intros i Hi. split; [apply HPLG; unfold xHA, G_S, SRC_SIZE; lia|intros []].
    - intros q _. split; [intros []|intros kq i _ _ []]. }
  split; [intros i Hi Hc; exact (TR _ _ (ZS i Hi Hc))|].
  split; [exact GIN|]. split; [exact OIN|]. split; [exact OIN2|exact PV].
Qed.

Lemma x_m2 : forall L A regs mem md, xm2 L A regs mem md -> xfacts 0 L A mem md.
Proof.
  intros L A regs mem md (RA & RM & INIT & RO & KEEP & SAVED & Q14 & Q15 & Q17 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 &
    Q24 & Q25 & SRCS & ZH & GIN & BLK & NL & YL & HRI).
  split; [eapply rmid_EF; [exact RM|intros a [X|X]; [left; exact X|right; left; exact X]|
                                    intros q [X|X]; [left; exact X|right; left; exact X]]|].
  split; [exact INIT|]. split; [exact RO|]. split; [unfold xV, xrest; rewrite xr_zero; exact HRI|].
  split; [exact SAVED|].
  split.
  { split; [exact Q22|]. split; [exact Q14|]. split; [exact Q18|]. split; [exact Q20|]. split; [exact Q19|].
    split; [exact Q17|]. split; [exact Q21|]. split; [exact Q23|]. split; [exact Q15|]. split; [exact Q24|].
    split; [exact Q25|].
    unfold xNO, xCAPw, xOUTw. destruct xlive eqn:HL; [exact (YL ltac:(first [exact HL|reflexivity]))|exact (NL ltac:(first [exact HL|reflexivity]))]. }
  split.
  { intros p Hp _. rewrite <- x_len in Hp. exact (SRCS p Hp). }
  split.
  { intros i Hi [X|X]; [lia|exact (ZH i Hi X)]. }
  split; [exact GIN|].
  split.
  { intros HL. apply BLK. split; [right; left; split; [exact HL|split; reflexivity]|].
    intros (p & Hp & Hq). apply (x_out HL p OUT' Hp); [|reflexivity].
    apply held_in_blocks. unfold list_blocks. apply in_or_app. right. exact Hq. }
  split.
  { intros HL HC. apply BLK. split; [right; right; split; [exact HL|split; [exact HC|split; reflexivity]]|].
    intros (p & Hp & Hq). apply (proj1 (proj2 (x_tg p xOUT Hp
      ltac:(apply held_in_blocks; unfold list_blocks; apply in_or_app; right; exact Hq)))). reflexivity. }
  intros q m Hq. destruct (proj1 (BLK q m) Hq) as [[(H0 & NO & NE)|[X|X]] NS].
  - pose proof HEXS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDK & _).
    destruct HDK as (_ & _ & _ & DK4).
    destruct (DK4 q m H0) as [Y|Y]; [left; exact Y|].
    unfold target_addrs in Y. destruct Y as [Y|[Y|Y]].
    + right. left. symmetry. exact Y.
    + exfalso. apply NO. unfold xOUT. symmetry. exact Y.
    + apply in_app_or in Y as [Y|Y]; [exfalso; exact (NE Y)|].
      apply in_concat in Y as (bl & Hbl & Hq'). apply in_map_iff in Hbl as (p0 & <- & Hp0). cbv beta in Hq'.
      destruct (In_nth _ _ pd0 Hp0) as (i & Hi & <-).
      destruct (HHS i Hi) as (V1 & V2 & _).
      destruct (held_back _ _ q V1 V2 Hq') as [Z|Z].
      * right. right. right. right. exists i. split; [rewrite <- x_len; exact Hi|]. split; [lia|exact Z].
      * exfalso. apply NS. exists (nth i hj pd0). split; [apply nth_In; exact Hi|exact Z].
  - right. right. left. exact X.
  - right. right. right. left. exact X.
Qed.

Lemma x_split : forall jj p, (p < xN)%nat -> xs p = jj ->
  exists l1 l2, xrest jj = l1 ++ nth p hj pd0 :: l2 /\ xrest (S jj) = l1 ++ l2.
Proof.
  intros jj p Hp Hsp. exs. pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & NDH & _).
  apply NoDup_ListNoDup in NDH.
  exact (xr_pick hj jj (nth p hj pd0) NDH (x_in p Hp) Hsp).
Qed.

Lemma x_rest_ek : forall jj p, (p < xN)%nat -> xs p = jj ->
  exists e1 e2, ek_view (xrest jj) = e1 ++ ekeys_hl (hs_expected (xcur p)) ++ e2 /\ ek_view (xrest (S jj)) = e1 ++ e2.
Proof.
  intros jj p Hp Hsp. destruct (x_split jj p Hp Hsp) as (l1 & l2 & E1 & E2).
  exists (ek_view l1), (ek_view l2). rewrite E1, E2. unfold ek_view. rewrite !map_app, !concat_app.
  cbn [map concat]. split; reflexivity.
Qed.

Lemma x_nw_src_ge : forall h, NW_SRC0 <= nw_src h.
Proof. intros h. unfold nw_src, nw_list, NW_SRC0, hl_n, NC_PER, DATA_PER, CF.op_add_c.PARTIAL_BYTES. lia. Qed.

Lemma x_rest_wt : forall jj p, (p < xN)%nat -> xs p = jj -> nc_wt [] (xrest (S jj)) <= nc_wt [] (xrest jj).
Proof.
  intros jj p Hp Hsp. destruct (x_split jj p Hp Hsp) as (l1 & l2 & E1 & E2). rewrite E1, E2.
  unfold nc_wt. rewrite !zsum_app, zsum_cons, !length_app. cbn [length]. cbv beta.
  pose proof (x_nw_src_ge (fst (nth p hj pd0))) as X. unfold NW_SRC0, NW_ENT0, CF.op_add_c.PARTIAL_BYTES in *. lia.
Qed.

Lemma x_cur_nc : forall p, (p < xN)%nat -> src_nc (xcur p) = src_nc (xh p).
Proof.
  intros p Hp. rewrite <- x_len in Hp. destruct (HHS p Hp) as (E1 & E2 & _).
  unfold xcur, src_nc, arr_nc, set_held. cbn [hs_pending hs_partial hs_expected hs_held]. unfold xh.
  rewrite E1, E2. reflexivity.
Qed.

Lemma x_src_wt : forall jj L A mem, List.NoDup (map fst (blocks L A)) ->
  (forall p, (p < xN)%nat -> (jj <= xs p)%nat -> src_at (rc := rc) B L A mem (xHA (xs p)) (xcur p)) ->
  zsum (CF.SlotRI3.nc_sz L A) (concat (map (fun p => src_nc (fst p)) (xrest jj))) <=
  zsum (fun p => nw_src (fst p)) (xrest jj).
Proof.
  intros jj L A mem HN SR. rewrite CF.SlotNcWt.nw_zsum_concat. apply CF.SlotNcWt.nw_zsum_le.
  intros y Hy. unfold xrest in Hy. apply filter_In in Hy as [Hy Hj]. apply Nat.leb_le in Hj.
  destruct (In_nth _ _ pd0 Hy) as (p & Hp & <-). rewrite x_len in Hp.
  change (fst (nth p hj pd0)) with (xh p). change (snd (nth p hj pd0)) with (xs p) in Hj.
  pose proof (CF.SlotNcWt.nw_src_le B L A mem (xHA (xs p)) (xcur p) HN (SR p Hp Hj)) as X.
  rewrite (x_cur_nc p Hp) in X. eapply Z.le_trans; [exact X|].
  assert (Hp' : (p < length hj)%nat) by (rewrite x_len; exact Hp).
  destruct (HHS p Hp') as (_ & E2 & E3).
  unfold xcur, nw_src, nw_list, set_held, pending_stream, hl_n. cbn [hs_pending hs_off hs_expected hs_held].
  unfold xh. rewrite E2, E3. cbn [length]. unfold NC_PER, DATA_PER. lia.
Qed.

Lemma x_ncs : forall jj L A mem md, aa_MR (API rc) L A mem md ->
  (forall p, (p < xN)%nat -> (jj <= xs p)%nat -> src_at (rc := rc) B L A mem (xHA (xs p)) (xcur p)) ->
  In (G, SRC_TABLE) (blocks L A) -> (xlive = true -> In (OUT', CAP') (blocks L A)) ->
  (xlive = false -> 0 < xCAP -> In (xOUT, xCAP) (blocks L A)) ->
  CF.SlotRI3.ncs (xV jj) L A <= nc_wt [] (xrest jj).
Proof.
  intros jj L A mem md HM SR GIN OIN OIN2. pose proof (x_ndb L A mem md HM) as HN. unfold xV.
  apply fin_ncs_view; [exact HN|exact GIN| |exact (x_src_wt jj L A mem HN SR)|exact (x_rest_len jj)].
  pose proof x_outat as (_ & OZ & OC). pose proof x_tot as TB. pose proof x_kb as KB.
  destruct xlive eqn:HL.
  - change (CF.SlotRI3.nc_sz L A OUT' <= TBBYTES).
    assert (OI : In (OUT', CAP') (blocks L A)) by first [exact (OIN HL)|exact (OIN eq_refl)].
    rewrite (CF.SlotNcWt.nw_sz_at L A OUT' CAP' HN OI).
    destruct (HLIVE HL) as (T1 & T2 & _). unfold xTOT, xCAP in *. unfold TBBYTES in *. lia.
  - change (CF.SlotRI3.nc_sz L A xOUT <= TBBYTES).
    destruct (Z.eq_dec xCAP 0) as [C0|C0].
    + rewrite (OZ C0). rewrite (CF.SlotNcWt.nw_sz_none L A 0 (CF.SlotNcWt.nw_no_zero B (API rc) L A mem md HM)).
      unfold TBBYTES. lia.
    + assert (OI : In (xOUT, xCAP) (blocks L A)) by first [exact (OIN2 HL ltac:(lia))|exact (OIN2 eq_refl ltac:(lia))].
      rewrite (CF.SlotNcWt.nw_sz_at L A xOUT xCAP HN OI). lia.
Qed.

Lemma x_call_step : forall jj L A regs mem md, (jj < 4)%nat -> xkeep regs ->
  getr regs 1 = Z_to_bv 64 0x141a4 -> getr regs 8 = Z_to_bv 64 (xHA jj) -> getr regs 9 = Z_to_bv 64 0x311c0 ->
  getr regs 10 = Z_to_bv 64 (xHA jj) -> xfacts jj L A mem md ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x145fc) mem (seg_rom (ms_segs B))) md) (x_back jj).
Proof.
  intros jj L A regs mem md Hjj KP R1 R8 R9 R10 RF.
  pose proof RF as (RMC & INIT & RO & HRI & ST & GL & SRCS & ZS & GIN & OIN & OIN2 & PV).
  pose proof RMC as (HM & HWF1 & HBD1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC).
  pose proof x_ac as (A1 & A2 & A3 & A4 & A5).
  pose proof x_wf0 as HWF0.
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (SPZ : spZ regs = xb) by exact (x_spZ regs KP).
  assert (HK : @YM05.alloc_ceiling rc <= xb - SOURCE_RESET_K)
    by (unfold SOURCE_RESET_K, SOURCE_RESET_FRAME, ALLOC_STACK; lia).
  assert (PICK : exists h bnd,
    (src_at (rc := rc) B L A mem (xHA jj) h \/ rw_cells (ms_segs B) mem (xHA jj) [CB 96%nat (nulbytes 96)]) /\
    rt_ok F A bnd /\
    (forall q, src_at (rc := rc) B L A mem (xHA jj) h -> In q (hs_blocks h) ->
       exists p, (p < xN)%nat /\ xs p = jj /\ In q (hs_blocks (xh p))) /\
    (forall L' A', (src_at (rc := rc) B L A mem (xHA jj) h ->
          exists qs, length qs = nretF (source_reset_tr (known_at L A) h) /\
            rt_ok F A' (runF F qs bnd (source_reset_tr (known_at L A) h))) ->
       (rw_cells (ms_segs B) mem (xHA jj) [CB 96%nat (nulbytes 96)] -> rt_ok F A' bnd) ->
       List.NoDup (map fst (blocks L' A')) ->
       (src_at (rc := rc) B L A mem (xHA jj) h ->
          forall t, In t (blocks L' A') <-> In t (blocks L A) /\ ~ In (fst t) (hs_blocks h)) ->
       (rw_cells (ms_segs B) mem (xHA jj) [CB 96%nat (nulbytes 96)] -> blocks L' A' = blocks L A) ->
       layout_le A L L' -> CF.SlotRI3.ncs (xV (S jj)) L' A' <= nc_wt [] (xrest (S jj)) ->
       RI E k (xV (S jj)) L' A') /\
    (slot_open hj jj = true -> src_at (rc := rc) B L A mem (xHA jj) h /\
       forall p q, (p < xN)%nat -> xs p = jj -> In q (hs_blocks (xcur p)) -> In q (hs_blocks h))).
  { assert (KB : forall q m, In (q, m) (blocks L A) -> 0 <= m)
      by (intros q m Hq; exact (proj1 (mv_blk B (API rc) L A mem md q m HM Hq))).
    destruct (slot_open hj jj) eqn:Ho.
    - destruct (x_open jj Ho) as (p & Hp & Hsp).
      pose proof (SRCS p Hp ltac:(lia)) as Sx. rewrite Hsp in Sx.
      destruct (HR1 L A mem (xHA jj) (xcur p) G (if xlive then OUT' else xOUT) [] (xrest jj) HRI
                  (x_ndb L A mem md HM) Sx) as (bnd & ROK & ROOM & RIK).
      exists (xcur p), bnd. split; [left; exact Sx|]. split; [exact ROK|]. split.
      + intros q _ Hq. exists p. split; [exact Hp|]. split; [exact Hsp|]. exact (x_cur p q Hp Hq).
      + split.
        * intros L' A' X _ NP HP _ LY NCS. destruct (X Sx) as (qs & QLEN & QOK).
          apply (RIK L' A' qs QLEN QOK G (if xlive then OUT' else xOUT) [] (xrest (S jj))).
          -- intros q m Y. left. exact (proj1 (proj1 (HP Sx (q, m)) Y)).
          -- exact (x_rest_pick jj p Hp Hsp).
          -- exact (x_rest_ek jj p Hp Hsp).
          -- apply Nat.le_0_l.
          -- exact (x_rest_len (S jj)).
          -- exact (x_move_reset jj p L A mem md L' A' Hp Hsp HM NP Sx (HP Sx)).
          -- exact NP.
          -- intros p0 n n' H1 H2 H3 H4. rewrite (CF.ListFrame.lf_addr A L L' p0 n HWF1 LY H1).
             rewrite mv_map_fst_src, (x_cur_nc p Hp) in H4.
             destruct (x_split jj p Hp Hsp) as (l1 & l2 & E1 & E2). rewrite E1 in H3. rewrite E2.
             unfold view_of in *. cbn [rv_nc map concat app] in *.
             rewrite map_app, concat_app in H3. rewrite map_app, concat_app. cbn [map concat] in H3.
             destruct H3 as [H3|[H3|H3]]; [left; exact H3|right; left; exact H3|right; right].
             apply in_app_iff in H3 as [H3|H3]; [apply in_or_app; left; exact H3|].
             apply in_app_iff in H3 as [H3|H3]; [exfalso; apply H4; exact H3|apply in_or_app; right; exact H3].
          -- exact NCS.
          -- exact (x_rest_wt jj p Hp Hsp).
        * intros _. split; [exact Sx|]. intros p' q Hp' Hs' Hq.
          rewrite (x_sinj p' p Hp' Hp ltac:(lia)) in Hq. exact Hq.
    - destruct (HR0 L A G (if xlive then OUT' else xOUT) [] (xrest jj) HRI (x_ndb L A mem md HM))
        as (bnd & ROK & ROOM & RIK).
      pose proof (ZS jj Hjj (or_intror Ho)) as Z0.
      exists src0, bnd. split; [right; exact Z0|]. split; [exact ROK|]. split.
      + intros q X. exfalso. destruct X as (_ & _ & _ & X & _). discriminate X.
      + split.
        * intros L' A' _ Y NP _ EQ LY NCS. pose proof (EQ Z0) as E0.
          apply (RIK L' A' [] eq_refl (Y Z0) G (if xlive then OUT' else xOUT) [] (xrest (S jj))).
          -- intros q m W. left. rewrite <- E0. exact W.
          -- exact (f_equal pend_view (x_rest_skip jj Ho)).
          -- exact (f_equal ek_view (x_rest_skip jj Ho)).
          -- apply Nat.le_0_l.
          -- exact (x_rest_len (S jj)).
          -- rewrite (x_rest_skip jj Ho). exact (mv_same _ L A L' A' KB E0).
          -- exact NP.
          -- intros p0 n n' H1 H2 H3 _. rewrite (CF.ListFrame.lf_addr A L L' p0 n HWF1 LY H1).
             rewrite (x_rest_skip jj Ho). exact H3.
          -- exact NCS.
          -- rewrite (x_rest_skip jj Ho). lia.
        * intros X. discriminate X. }
  destruct PICK as (h & bnd & SZ & ROK & HBL & RIK & OPN).
  pose proof (HSRC L A regs mem md bnd h jj) as HC. cbv zeta in HC.
  eapply SR_bind.
  { apply HC; clear HC.
    - exact HSEG.
    - eapply (cpk_of_rmid B (API rc) _ _ _ _ L0 A0 m0 md0 L A mem md regs SOURCE_RESET_K RMC INIT).
      + change (YK11.getr regs 1) with (getr regs 1). rewrite R1. apply ret_ok_even. vm_compute. reflexivity.
      + transitivity (YK11.getr regs (Z_to_bv 5 4)); [reflexivity|]. rewrite (x_tp regs KP). exact HTPE.
      + rewrite SPZ. exact A4.
      + rewrite SPZ, A5. unfold SLOT_STACK, SOURCE_RESET_K, SOURCE_RESET_FRAME, ALLOC_STACK. lia.
      + rewrite SPZ, A5. lia.
      + unfold SOURCE_RESET_K, SOURCE_RESET_FRAME, ALLOC_STACK. lia.
      + rewrite SPZ. unfold SOURCE_RESET_K, SOURCE_RESET_FRAME, ALLOC_STACK. lia.
      + rewrite SPZ. lia.
    - exact INIT.
    - exact RO.
    - intros a Ha. apply HPLG. unfold G_S, SRC_SIZE, SOURCES_MAX in Ha. lia.
    - exact Hjj.
    - exact R10.
    - exact SZ.
    - rewrite HSEG. apply CF.SlotEntryRun.entry_global_cells; [unfold xHA, G_S, SRC_SIZE; lia|unfold xHA, G_S, SRC_SIZE; lia|].
      intros i Hi. apply in_G_bss. unfold xHA, G_S, SRC_SIZE. lia.
    - exact ROK. }
  intros c' (L' & A' & regs' & mem' & md' & EC & RP & INIT' & RO' & ZJ & SRCQ & ZQ).
  destruct (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as [RMn PR]. rewrite SPZ in RMn.
  lazymatch type of RMn with rmid _ _ _ _ ?Ee0 ?Ff0 _ _ _ _ _ _ _ _ =>
    set (Ee := Ee0) in RMn; set (Ff := Ff0) in RMn end.
  assert (NEh : forall a, 0x311c0 <= a -> ~ Ee a) by (intros a Ha X; unfold Ee, G_S, SRC_SIZE in X; lia).
  assert (RMw : rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) Ee Ff L A mem md L' A' mem' md').
  { apply (rmid_widen B (API rc) SOURCE_RESET_K xb); [exact HM| | | | | | |exact RMn].
    - rewrite A5. unfold SLOT_STACK, SOURCE_RESET_K, SOURCE_RESET_FRAME, ALLOC_STACK. lia.
    - lia.
    - rewrite A5. unfold SLOT_STACK. lia.
    - lia.
    - intros a Ha. apply SC. unfold sk. left. exact Ha.
    - intros a Ha. apply NEh. rewrite A5 in Ha. unfold SLOT_STACK in Ha. lia. }
  assert (RMC' : rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) xE xF L0 A0 m0 md0 L' A' mem' md').
  { eapply rmid_EF; [exact (rmid_seq B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF0 RMC RMw)| |].
    - intros a [X|X]; [exact X|]. unfold xE. right. right. unfold Ee, SRC_SIZE in X. unfold SRC_SIZE. lia.
    - intros q [X|X]; [exact X|]. unfold xF. right. right. unfold Ff in X. destruct X as (X1 & X2).
      destruct (HBL q X1 X2) as (p & Hp & _ & Hq). exists p. split; [exact Hp|exact Hq]. }
  assert (TG : forall a cs, rw_cells (ms_segs B) mem a cs ->
      (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
         (0x30fc0 <= a + i < 0x311c0 \/ 0x20d38 <= a + i < 0x20d48) /\ ~ Ee (a + i)) ->
      rw_cells (ms_segs B) mem' a cs).
  { intros a cs H D.
    apply (rmid_rw_img B (API rc) HAX SOURCE_RESET_K xb Ee Ff L A mem md L' A' mem' md' a cs (hg_img_low B HSEG)
      HK HM RMn H).
    intros i Hi. destruct (D i Hi) as [D1 D2]. split; [apply HPLG; exact D1|exact D2]. }
  assert (BKEEP : forall q m, In (q, m) (blocks L A) -> (forall p, (p < xN)%nat -> In q (hs_blocks (xh p)) -> False) ->
      In (q, m) (blocks L' A')).
  { intros q m Hq NQ. destruct SZ as [Sx|Zx].
    - destruct (SRCQ Sx) as (_ & BK1 & _). apply BK1; [exact Hq|].
      intros X. destruct (HBL q Sx X) as (p & Hp & _ & Hq'). exact (NQ p Hp Hq').
    - destruct (ZQ Zx) as (_ & BEQ). rewrite BEQ. exact Hq. }
  assert (BI : forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A)).
  { intros q m X. destruct SZ as [Sx|Zx]; [exact (proj1 (proj2 (proj2 (SRCQ Sx)) q m X))|].
  rewrite <- (proj2 (ZQ Zx)). exact X. }
  pose proof RMn as (_ & _ & _ & LYn & _).
  assert (SRC' : forall p, (p < xN)%nat -> (S jj <= xs p)%nat ->
      src_at (rc := rc) B L' A' mem' (xHA (xs p)) (xcur p)).
  { intros p Hp Hj. pose proof (x_slt p Hp) as SL.
    assert (Hne : xs p <> jj) by lia.
    apply (fin_src rc B (API rc) SOURCE_RESET_K xb Ee Ff L A mem md L' A' mem' md' (xHA (xs p)) _
             HAX HBW HSEG HK HM RMn); [| |exact (SRCS p Hp ltac:(lia))].
    - intros i Hi. split; [apply HPLG; unfold xHA, G_S, SRC_SIZE; lia|].
      unfold Ee, xHA, G_S, SRC_SIZE. lia.
    - intros q Hq. split.
      + intros X. unfold Ff in X. destruct X as (X1 & X2). destruct (HBL q X1 X2) as (p' & Hp' & Hs' & Hq').
        assert (Hpp : p <> p') by (intros ->; lia).
        exact (x_disj p p' q Hp Hp' Hpp (x_cur p q Hp Hq) Hq').
      + intros kq i Hin Hi X. apply (hf_blk_img B (API rc) HAX L A mem md q kq i HM Hin Hi).
        apply (proj1 (HPLG (q + i) ltac:(unfold Ee, G_S, SRC_SIZE in X; lia))). }
  assert (GIN' : In (G, SRC_TABLE) (blocks L' A')).
  { apply BKEEP; [exact GIN|]. intros p Hp Hq. exact (proj1 (x_tg _ _ (x_in p Hp) Hq) eq_refl). }
  assert (OIN' : xlive = true -> In (OUT', CAP') (blocks L' A')).
  { intros HL. apply BKEEP; [exact (OIN HL)|]. intros p Hp Hq. exact (x_out HL _ _ (x_in p Hp) Hq eq_refl). }
  assert (OIN2' : xlive = false -> 0 < xCAP -> In (xOUT, xCAP) (blocks L' A')).
  { intros HL HCp. apply BKEEP; [exact (OIN2 HL HCp)|]. intros p Hp Hq.
    exact (proj1 (proj2 (x_tg _ _ (x_in p Hp) Hq)) eq_refl). }
  eapply SR_ret. exists L', A', regs', mem', md'.
  split; [rewrite EC, R1; reflexivity|].
  split; [intros r Hr; rewrite (PR r ltac:(unfold callee_saved; lia)); exact (KP r Hr)|].
  split; [transitivity (YK11.getr regs' (Z_to_bv 5 8)); [reflexivity|];
    rewrite (PR 8 ltac:(unfold callee_saved; lia)); exact R8|].
  split; [transitivity (YK11.getr regs' (Z_to_bv 5 9)); [reflexivity|];
    rewrite (PR 9 ltac:(unfold callee_saved; lia)); exact R9|].
  split; [exact RMC'|]. split; [exact INIT'|]. split; [exact RO'|].
  split.
  { pose proof RMC' as (HM' & _). apply RIK.
    - intros Sx. exact (proj1 (SRCQ Sx)).
    - intros Zx. exact (proj1 (ZQ Zx)).
    - exact (x_ndb L' A' mem' md' HM').
    - intros Sx [q m]. cbn [fst]. destruct (SRCQ Sx) as (_ & BK1 & BK2).
      split; [intros X; exact (BK2 q m X)|intros [X1 X2]; exact (BK1 q m X1 X2)].
    - intros Zx. exact (proj2 (ZQ Zx)).
    - exact LYn.
    - exact (x_ncs (S jj) L' A' mem' md' HM' SRC' GIN' OIN' OIN2'). }
  split.
  { apply (rmid_rw_hi B (API rc) SOURCE_RESET_K xb Ee Ff L A mem md L' A' mem' md' (xb + 88) _);
      first [exact HM|exact RMn|exact ST|lia|(rewrite HEA; lia)|(unfold saved_cells; cbn [cells_size csize]; lia)|
             (intros i Hi; apply NEh; lia)]. }
  split.
  { apply (xglob_keep mem mem'); [|exact GL]. intros a cs H D. apply TG; [exact H|].
    intros i Hi. destruct (D i Hi) as [D1|D1]; unfold Ee, G_S, SRC_SIZE in *; split; lia. }
  split; [exact SRC'|].
  split.
  { intros i Hi Hc. destruct (Nat.eq_dec i jj) as [->|Hij].
    - exact ZJ.
    - assert (Hc' : (i < jj)%nat \/ slot_open hj i = false) by (destruct Hc as [X|X]; [left; lia|right; exact X]).
      apply TG; [exact (ZS i Hi Hc')|]. intros x Hx. cbn [cells_size csize] in Hx.
      split; [unfold xHA, G_S, SRC_SIZE; lia|]. unfold Ee, xHA, G_S, SRC_SIZE. lia. }
  split; [exact GIN'|].
  split; [exact OIN'|].
  split; [exact OIN2'|].
  intros q m Hq'. destruct (PV q m (BI q m Hq')) as [X|[X|[X|[X|(p & Hp & Hj & Hq0)]]]].
  - left. exact X.
  - right. left. exact X.
  - right. right. left. exact X.
  - right. right. right. left. exact X.
  - destruct (Nat.eq_dec (xs p) jj) as [Heq|Hne].
    + exfalso. destruct (slot_open hj jj) eqn:Ho.
      * destruct (OPN eq_refl) as (Sx & COV).
        exact (proj2 (proj2 (proj2 (SRCQ Sx)) q m Hq') (COV p q Hp Heq Hq0)).
      * pose proof (x_open_rev p Hp) as Y. rewrite Heq, Ho in Y. discriminate Y.
    + right. right. right. right. exists p. split; [exact Hp|]. split; [lia|exact Hq0].
Qed.

Lemma x_next : forall jj c, (jj < 4)%nat -> x_back jj c ->
  SR (ms_segs B) c (fun c' => ((S jj < 4)%nat /\ x_call (S jj) c') \/ (jj = 3%nat /\ x_end c')).
Proof.
  intros jj c Hjj (L & A & regs & mem & md & -> & KP & R8 & R9 & RF).
  pose proof RF as (RMC & _ & RO & _ & ST & _).
  pose proof RMC as (HM & _).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HM) as (Hh & Hl & _).
  assert (RO' : ro_agree rsegs mem) by (rewrite <- HSEG; exact RO).
  pose proof x_ac as (A1 & A2 & A3 & A4 & A5).
  assert (STn : rw_cells rsegs (normalize rsegs mem) (xb + 88) (saved_cells (ss_regs E))).
  { pose proof ST as X. rewrite HSEG in X. apply rw_cells_normalize; [exact RO'|exact X|].
    intros x Hx. apply ro_addr_hi. unfold saved_cells in Hx. cbn [cells_size csize] in Hx. lia. }
  rewrite HSEG.
  eapply kseg; [exact wx_apart_rsegs|exact RO'|exact Hh|exact Hl| | |].
  { unfold Regs6ss.mkR_of. unfold saved_cells in STn.
    eapply exit_reset_next with (b := xb) (HA := xHA jj).
    - transitivity (YK11.getr regs (Z_to_bv 5 2)); [reflexivity|exact (x_sp regs KP)].
    - transitivity (YK11.getr regs (Z_to_bv 5 8)); [reflexivity|exact R8].
    - transitivity (YK11.getr regs (Z_to_bv 5 9)); [reflexivity|exact R9].
    - lia.
    - lia.
    - unfold xHA, G_S, SRC_SIZE. lia.
    - unfold xHA, G_S, SRC_SIZE. lia.
    - exact STn. }
  { intros s0 [(_ & ->)|(_ & ->)]; do 3 eexists; reflexivity. }
  intros R pc' m0' regs1 m1 HQ GR MREL ROS.
  assert (EM : m0' = normalize rsegs mem).
  { destruct HQ as [(_ & EQ)|(_ & EQ)]; injection EQ as _ _ X; exact X. }
  subst m0'. pose proof (x_nowrite _ _ _ _ _ m1 RF MREL ROS) as RF1.
  rewrite <- HSEG. apply SR_ret.
  destruct HQ as [(Q1 & EQ)|(Q1 & EQ)]; injection EQ as ER EP; subst R pc'.
  - left. split; [unfold xHA, G_S, SRC_SIZE in Q1; lia|].
    exists L, A, regs1, m1, md. split; [reflexivity|].
    split.
    { intros r Hr. rewrite GR, <- (KP r Hr).
      destruct Hr as [-> | [-> | ->]]; reflexivity. }
    split; [transitivity (YK11.getr regs1 (Z_to_bv 5 1)); [reflexivity|rewrite GR; reflexivity]|].
    split.
    { transitivity (YK11.getr regs1 (Z_to_bv 5 8)); [reflexivity|rewrite GR].
      transitivity (Z_to_bv 64 (xHA jj + 96)); [reflexivity|f_equal; unfold xHA, SRC_SIZE; lia]. }
    split; [transitivity (YK11.getr regs1 (Z_to_bv 5 9)); [reflexivity|rewrite GR; exact R9]|].
    split.
    { transitivity (YK11.getr regs1 (Z_to_bv 5 10)); [reflexivity|rewrite GR].
      transitivity (Z_to_bv 64 (xHA jj + 96)); [reflexivity|f_equal; unfold xHA, SRC_SIZE; lia]. }
    exact RF1.
  - right. assert (J3 : jj = 3%nat) by (unfold xHA, G_S, SRC_SIZE in Q1; lia). split; [exact J3|].
    exists L, A, regs1, m1, md. split; [reflexivity|].
    split; [rewrite GR; reflexivity|].
    split.
    { intros r Hr. rewrite GR. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
        r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct C as [->|[->|[->|C]]].
      - transitivity (Z_to_bv 64 (xb + 192)); [reflexivity|]. rewrite <- A5. unfold spZ. apply Z_to_bv_bv_unsigned.
      - transitivity (YK11.getr regs (Z_to_bv 5 3)); [reflexivity|exact (x_gp regs KP)].
      - transitivity (YK11.getr regs (Z_to_bv 5 4)); [reflexivity|exact (x_tp regs KP)].
      - repeat (destruct C as [C|C]; [subst r; reflexivity|]); subst r; reflexivity. }
    subst jj. exact RF1.
Qed.

Lemma x_loop : forall jj c, (jj < 4)%nat -> x_call jj c -> SR (ms_segs B) c x_end.
Proof.
  intros jj c Hjj HC.
  refine (SR_loop (ms_segs B) nat (fun w => (4 - w)%nat) (fun w c => (w < 4)%nat /\ x_call w c) x_end _ jj c
            (conj Hjj HC)).
  intros w c' (Hw & (L & A & regs & mem & md & -> & KP & R1 & R8 & R9 & R10 & RF)).
  eapply SR_bind; [exact (x_call_step w L A regs mem md Hw KP R1 R8 R9 R10 RF)|].
  intros c1 H1. eapply SR_mono; [exact (x_next w c1 Hw H1)|].
  intros c2 [(H3 & H2)|(H3 & H2)].
  - right. exists (S w). split; [lia|]. split; [exact H3|exact H2].
  - left. exact H2.
Qed.

Lemma x_start : forall L A regs mem md, xm2 L A regs mem md ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x14190) mem (seg_rom (ms_segs B))) md) (x_call 0).
Proof.
  intros L A regs mem md M2.
  pose proof (x_m2 L A regs mem md M2) as RF.
  pose proof M2 as (RA & RM & _ & RO & KEEP & _).
  pose proof RF as (_ & _ & _ & _ & _ & GL & _).
  pose proof GL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QO).
  pose proof RM as (HM & _).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HM) as (Hh & Hl & _).
  assert (RO' : ro_agree rsegs mem) by (rewrite <- HSEG; exact RO).
  assert (KP : xkeep regs) by (intros r Hr; apply KEEP; lia).
  assert (NOW : xNO = Z_to_bv 64 (if gn =? 0 then xTOT else 0)).
  { unfold xNO. destruct xlive eqn:HL.
    - rewrite (x_gn HL). reflexivity.
    - destruct (Z.eqb_spec gn 0) as [G0|G0]; [rewrite (x_tot0 G0 HL)|]; reflexivity. }
  assert (NB : bytes_at rsegs mem 0x31000 (le8 (YK11.getr regs (Z_to_bv 5 10)))).
  { rewrite RA, <- NOW. rewrite HSEG in QO. exact (proj1 (ea_outv _ _ _ _ _ _ QO)). }
  rewrite HSEG.
  eapply kseg; [exact wx_apart_rsegs|exact RO'|exact Hh|exact Hl| | |].
  { unfold Regs6ss.mkR_of. apply (exit_done_call HCSD).
    - transitivity (YK11.getr regs (Z_to_bv 5 20)); [reflexivity|]. rewrite (KEEP 20 ltac:(lia)).
      exs. destruct HR as (_ & _ & _ & B20 & _). exact B20.
    - exact (bytes_at_normalize rsegs mem _ _ RO' NB). }
  { intros s0 (x11 & ->). do 3 eexists. reflexivity. }
  intros R pc' m0' regs1 m1 (x11 & EQ) GR MREL ROS. injection EQ as ER EP EM. subst R pc' m0'.
  pose proof (x_nowrite _ _ _ _ _ m1 RF MREL ROS) as RF1.
  rewrite <- HSEG. apply SR_ret. exists L, A, regs1, m1, md. split; [reflexivity|].
  split.
  { intros r Hr. rewrite GR, <- (KP r Hr). destruct Hr as [-> | [-> | ->]]; reflexivity. }
  split; [transitivity (YK11.getr regs1 (Z_to_bv 5 1)); [reflexivity|rewrite GR; reflexivity]|].
  split; [transitivity (YK11.getr regs1 (Z_to_bv 5 8)); [reflexivity|rewrite GR; reflexivity]|].
  split; [transitivity (YK11.getr regs1 (Z_to_bv 5 9)); [reflexivity|rewrite GR; reflexivity]|].
  split; [transitivity (YK11.getr regs1 (Z_to_bv 5 10)); [reflexivity|rewrite GR; reflexivity]|].
  exact RF1.
Qed.

Lemma x_capv : (xlive = true -> bv_unsigned xCAPw = CAP' /\ bv_unsigned xOUTw = OUT') /\
  (xlive = false -> bv_unsigned xCAPw = xCAP /\ bv_unsigned xOUTw = xOUT).
Proof.
  unfold xCAPw, xOUTw. split; intros HL; rewrite HL; [|split; reflexivity].
  destruct (HLIVE HL) as (T1 & T2 & (F0 & F1 & _) & _). pose proof x_tot. pose proof (@YM05.alloc_ceiling_lt rc).
  split; apply unsigned_lit; unfold xTOT in *; lia.
Qed.

Lemma x_pack : forall c, x_end c -> slot_post (rc := rc) (SH := SH) (SK := SK) B (API rc) ra j E CS c.
Proof.
  intros c (L & A & regs & mem & md & -> & R10 & PRS & RF).
  pose proof RF as (RMC & INIT & RO & HRIe & ST & GL & SRCS & ZS & GIN & OIN & OIN2 & PV).
  pose proof GL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
  pose proof HFR as (FF & _ & HP & _).
  destruct HP as (PRE & _ & _ & _ & _ & _ & _ & _ & _ & _).
  destruct PRE as (PRE & _). destruct PRE as (_ & _ & _ & _ & RA & _).
  assert (RAEV : ra mod 2 = 0) by (unfold frame_facts in FF; tauto).
  pose proof x_capv as (CV1 & CV2).
  pose proof x_outat as (OA1 & OA2 & OA3).
  pose proof x_gb as (GB0 & (GF0 & GF1 & _)).
  pose proof x_tot as TB. pose proof x_kb as KB.
  pose proof (bv_unsigned_in_range 64 cap) as RC. unfold bv_modulus in RC.
  set (T' := kept_blocks 16 G (bv_unsigned xCAPw) (bv_unsigned xOUTw)).
  assert (CPOS : bv_unsigned xCAPw <> 0 -> 0 < bv_unsigned xCAPw).
  { pose proof (bv_unsigned_in_range 64 xCAPw) as X. unfold bv_modulus in X. lia. }
  assert (OB : bv_unsigned xCAPw <> 0 -> In (bv_unsigned xOUTw, bv_unsigned xCAPw) (blocks L A)).
  { intros HC. destruct xlive eqn:HL.
    - destruct (CV1 ltac:(first [exact HL|reflexivity])) as [-> ->]. exact (OIN ltac:(first [exact HL|reflexivity])).
    - destruct (CV2 ltac:(first [exact HL|reflexivity])) as [X1 X2]. rewrite X1, X2 in *. apply OIN2; [first [exact HL|reflexivity]|]. unfold xCAP in *. lia. }
  assert (GO : bv_unsigned xCAPw <> 0 -> G <> bv_unsigned xOUTw).
  { intros HC. destruct (fin_target G xOUT es hj x_nd) as (TGO & TGE & _). destruct xlive eqn:HL.
    - destruct (CV1 ltac:(first [exact HL|reflexivity])) as [_ ->]. destruct (HLIVE HL) as (_ & _ & _ & HQ).
      apply (HQ G SRC_TABLE GB0 TGO TGE). unfold SRC_TABLE, SRC_ENTRY. lia.
    - destruct (CV2 ltac:(first [exact HL|reflexivity])) as [_ ->]. exact TGO. }
  assert (TE : T' = (G, SRC_TABLE) ::
      (if bv_unsigned xCAPw =? 0 then [] else [(bv_unsigned xOUTw, bv_unsigned xCAPw)])) by reflexivity.
  assert (TBL : tb_live L A T').
  { rewrite TE. destruct (Z.eqb_spec (bv_unsigned xCAPw) 0) as [X|X]; split.
    - first [apply NoDup_ListNoDup|idtac]. constructor; [intros []|constructor].
    - intros t0 [<-|[]]. exact GIN.
    - first [apply NoDup_ListNoDup|idtac]. constructor; [|constructor; [intros []|constructor]].
      intros [Y|[]]. injection Y as Y _. exact (GO X (eq_sym Y)).
    - intros t0 [<-|[<-|[]]]; [exact GIN|exact (OB X)]. }
  assert (TIN : forall t0, In t0 T' -> In t0 (blocks (ss_L E) (ss_A E)) -> In t0 (ss_T E)).
  { pose proof HEXS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDK & _).
    intros t0 Ht. rewrite TE in Ht.
    assert (TG0 : In (G, SRC_TABLE) (blocks (ss_L E) (ss_A E)) -> In (G, SRC_TABLE) (ss_T E)).
    { apply (ea_T B E xTA L0 A0 m0 (G, SRC_TABLE) HDK); [cbn; unfold SRC_TABLE, SRC_ENTRY; lia|].
      left. cbn [fst]. unfold xTA, target_addrs. left. reflexivity. }
    destruct (Z.eqb_spec (bv_unsigned xCAPw) 0) as [X|X].
    - destruct Ht as [<-|[]]. exact TG0.
    - destruct Ht as [<-|[<-|[]]]; [exact TG0|].
      apply (ea_T B E xTA L0 A0 m0 _ HDK); [cbn; exact (CPOS X)|]. cbn [fst]. destruct xlive eqn:HL.
      + right. destruct (CV1 ltac:(first [exact HL|reflexivity])) as [_ ->]. destruct (HLIVE HL) as (_ & _ & _ & HQ).
        intros q m Hq Hm NT. apply (HQ q m Hq).
        * intros EQ. apply NT. rewrite EQ. unfold xTA, target_addrs. right. left. reflexivity.
        * intros Y. apply NT. unfold xTA, target_addrs. right. right. apply in_or_app. left. exact Y.
        * exact Hm.
      + left. destruct (CV2 ltac:(first [exact HL|reflexivity])) as [_ ->]. unfold xTA, target_addrs. right. left. reflexivity. }
  assert (NDA : List.NoDup (map fst (blocks L A))).
  { assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    pose proof (ALL rc fx) as FA.
    assert (NDB : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
    pose proof RMC as (HM & _). pose proof (NDB L A mem md HM) as X.
    first [exact (proj1 (NoDup_ListNoDup _) X)|exact X]. }
  assert (CAPB : bv_unsigned xCAPw <= TBBYTES).
  { destruct xlive eqn:HL.
    - destruct (CV1 ltac:(first [exact HL|reflexivity])) as [-> _]. destruct (HLIVE HL) as (_ & T2 & _).
      unfold TBBYTES in *. unfold xCAP in OA3. unfold xTOT in *. lia.
    - destruct (CV2 ltac:(first [exact HL|reflexivity])) as [-> _]. exact (proj2 OA3). }
  assert (PVE : forall t0, In t0 (blocks L A) ->
      (In t0 (blocks (ss_L E) (ss_A E)) /\ ~ In t0 (ss_T E)) \/ In t0 T').
  { intros [q m] Hq. rewrite TE.
    destruct (PV q m Hq) as [X|[X|[X|[X|(p & Hp & Hj & _)]]]].
    - left. exact X.
    - right. left. subst q. rewrite (mv_fst_uniq (blocks L A) G SRC_TABLE m NDA GIN Hq). reflexivity.
    - right. right. destruct X as (HL & -> & ->). destruct (CV1 HL) as [C1 O1]. rewrite C1, O1.
      destruct (HLIVE HL) as (T1 & _). pose proof (x_livepos HL).
      rewrite (proj2 (Z.eqb_neq CAP' 0) ltac:(unfold xTOT in *; lia)). left. reflexivity.
    - right. right. destruct X as (HL & HC & -> & ->). destruct (CV2 HL) as [C2 O2]. rewrite C2, O2.
      rewrite (proj2 (Z.eqb_neq xCAP 0) ltac:(lia)). left. reflexivity.
    - exfalso. pose proof (x_slt p Hp). lia. }
  assert (TLN : (length T' <= 2)%nat) by (rewrite TE; destruct (bv_unsigned xCAPw =? 0); cbn [length]; lia).
  assert (TSZ : forall t0, In t0 T' -> 0 < snd t0 <= TBBYTES).
  { intros t0 Ht. rewrite TE in Ht. destruct Ht as [<-|Ht].
    - cbn [snd]. unfold SRC_TABLE, SRC_ENTRY, TBBYTES. lia.
    - revert Ht. destruct (Z.eqb_spec (bv_unsigned xCAPw) 0) as [X|X]; intros Ht; [destruct Ht|].
      destruct Ht as [<-|[]]. cbn [snd]. pose proof (CPOS X). lia. }
  exists fx, L, A, regs, mem, md, T'.
  split.
  { assert (RA' : YK11.getr (ss_regs E) (Z_to_bv 5 1) = Z_to_bv 64 ra) by exact RA.
    rewrite RA', ret_pc_of_ok; [reflexivity|]. apply ret_ok_even. rewrite unsigned_lit_wrap.
    Z.div_mod_to_equations. lia. }
  split; [exact HFZ|].
  split.
  - pose proof HEXS as (_ & _ & _ & _ & _ & HMR & _ & _ & _ & HVM & _ & HIK & _ & HDK & _).
    pose proof (HRE B API LS SH SK ra empty rc fx0 j E HFR k _ L A T' HRIe NDA PVE TLN TSZ) as (HREa & HREg).
    split; [|exact HREg].
    apply (ea_post CS B API LS SH SK ra empty rc fx0 j E xTA L0 A0 m0 md0 xE xF L A regs mem md T' HFR HMR HVM HIK
             HDK RMC x_E x_F INIT RO R10 PRS); [|exact TBL|exact TIN].
    exact HREa.
  - pose proof x_gl as (_ & RBR & RGN & RDD & REI & _).
    rewrite HSEG in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12.
    assert (ZS' : forall i, (i < 4)%nat -> rw_cells rsegs mem (G_S + SRC_SIZE * Z.of_nat i) [CB 96%nat (nulbytes 96)]).
    { intros i Hi. pose proof (ZS i Hi (or_introl Hi)) as X. rewrite HSEG in X. exact X. }
    pose proof (ea_GI j mem (Z_to_bv 64 G) xNO xCAPw xOUTw mx (if xoff then br else dd) gn dd (if xoff then ei else 0)
      Q1 Q2 Q3 Q4 Q5 Q6 ZS' Q8 Q9 Q10 Q11 ltac:(destruct xoff; tauto) RGN RDD ltac:(destruct xoff; tauto) Q7 Q12)
      as GI.
    rewrite (unsigned_lit G) in GI by (unfold SRC_TABLE, SRC_ENTRY in *; pose proof (@YM05.alloc_ceiling_lt rc); lia).
    apply GI.
    + unfold xNO. destruct xlive eqn:HL.
      * destruct (CV1 ltac:(first [exact HL|reflexivity])) as [-> _]. destruct (HLIVE HL) as (T1 & _). rewrite unsigned_lit by (unfold xTOT in *; lia).
        unfold xTOT. exact T1.
      * destruct (CV2 ltac:(first [exact HL|reflexivity])) as [-> _]. rewrite unsigned_lit by lia. unfold xCAP. lia.
    + destruct xlive eqn:HL.
      * destruct (CV1 ltac:(first [exact HL|reflexivity])) as [-> _]. destruct (HLIVE HL) as (_ & T2 & _). unfold TBBYTES in *. unfold xCAP in OA3.
        unfold xTOT in *. lia.
      * destruct (CV2 ltac:(first [exact HL|reflexivity])) as [-> _]. exact (proj2 OA3).
    + destruct xlive eqn:HL.
      * destruct (CV1 ltac:(first [exact HL|reflexivity])) as [-> _]. destruct (HLIVE HL) as (T1 & _). pose proof (x_livepos HL).
        unfold xTOT in *. lia.
      * destruct (CV2 ltac:(first [exact HL|reflexivity])) as [-> ->]. exact OA2.
Qed.

Lemma x_main : forall L A regs mem md, xm2 L A regs mem md ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x14190) mem (seg_rom (ms_segs B))) md)
    (slot_post (rc := rc) (SH := SH) (SK := SK) B (API rc) ra j E CS).
Proof.
  intros L A regs mem md M2.
  eapply SR_bind; [exact (x_start L A regs mem md M2)|].
  intros c1 H1. eapply SR_mono; [exact (x_loop 0 c1 ltac:(lia) H1)|exact x_pack].
Qed.

End End.

Theorem exit_end : forall CS RI (F : ResFormT),
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @source_reset_contract fx rc B (API rc) F) ->
  check_shape_done_contract ->
  exit_res_reset_s F RI CS ->
  RI_end RI CS ->
  forall B API LS SH SK ra empty rc fx j E,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    forall t k c,
      exit_mid2 (rc := rc) B (API rc) E RI t k c ->
      SR (ms_segs B) c (slot_post (rc := rc) (SH := SH) (SK := SK) B (API rc) ra j E CS).
Proof.
  intros CS RI F HSR HCSD HRES HRE B API LS SH SK ra empty rc fx j E HF t k c HM2.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  assert (FG : forall a, in_globals frame_G a -> img_plain B a)
    by (unfold frame_facts, img_plain in *; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL rc fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  assert (BW : blocks_writable B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (ETP : ms_tp B = 0x31290) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  assert (EA : errno_addr B = 0x311ec) by (unfold errno_addr; rewrite ETP, EOFF; reflexivity).
  assert (PLG : forall a, 0x30fc0 <= a < 0x311c0 \/ 0x20d38 <= a < 0x20d48 -> img_plain B a).
  { intros a [Ha|Ha]; apply FG.
    - apply in_G_bss. lia.
    - exists 0x20d38, 16. split; [left; reflexivity|lia]. }
  destruct (proj1 (proj1 PRE)) as (MRE & _ & _ & _ & _ & ALIGN & SPLO & SPHI & _ & TPE & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (HB2 : slot_sp E + 192 < 2 ^ 63) by (unfold slot_sp, SLOT_FRAME in *; lia).
  assert (HB3 : slot_sp E mod 16 = 0) by (unfold slot_sp, SLOT_FRAME; Z.div_mod_to_equations; lia).
  assert (HB4 : spZ (ss_regs E) = slot_sp E + 192) by (unfold slot_sp, SLOT_FRAME; lia).
  assert (HSL : @YM05.alloc_ceiling rc <= spZ (ss_regs E) - SLOT_STACK) by lia.
  destruct HM2 as (fx' & L0 & A0 & regs0 & m0 & md0 & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es &
    hj & tail & L & A & regs & mem & md & OUT' & CAP' & junk' & Hs & HM2).
  cbv zeta in HM2.
  destruct HM2 as (Hc & RA & FZ & EXS & TB & RM & INIT & RO & KEEP & SAVED & S2 & S3 & S4 & Q14 & Q15 & Q16 & Q17 &
    Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & SRCS & ZH & TAB & GIN & BLK & NL & YL & HRI).
  subst c.
  pose proof (HSR B API LS SH SK ra empty rc fx' FF) as HSRC.
  assert (HR0 : forall L A G1 out1 es1 hj1, RI E k (view_of G1 out1 es1 hj1) L A ->
      List.NoDup (map fst (blocks L A)) -> res_tr F (exit_RV_s RI E k L A G1 out1 es1 hj1 [] []) A []).
  { intros L1 A1 G1 out1 es1 hj1 H ND.
    exact (proj1 (HRES B API LS SH SK ra empty rc fx j E HF k L1 A1 G1 out1 es1 hj1 H ND)). }
  assert (HR1 : forall L A mem HA h G1 out1 es1 hj1, RI E k (view_of G1 out1 es1 hj1) L A ->
      List.NoDup (map fst (blocks L A)) -> src_at (rc := rc) B L A mem HA h ->
      res_tr F (reset_RV_s RI E k L A G1 out1 es1 hj1 h) A (source_reset_tr (known_at L A) h)).
  { intros L1 A1 mem1 HA h G1 out1 es1 hj1 H ND S.
    exact (proj2 (HRES B API LS SH SK ra empty rc fx j E HF k L1 A1 G1 out1 es1 hj1 H ND) mem1 HA h S). }
  assert (HLIVE : send_live cl br dd (entries_total es) = true ->
    entries_total es <= CAP' /\ CAP' <= Z.max (bv_unsigned cap) (2 * entries_total es) /\
    fresh_block (rc := rc) B OUT' CAP' /\
    (forall q m, In (q, m) (blocks L0 A0) -> q <> bv_unsigned out -> ~ In q (concat (map entry_blocks es)) -> 0 < m ->
       q <> OUT')).
  { intros HL. destruct (YL HL) as (Y1 & _ & Y3 & Y4 & Y5 & _). exact (conj Y1 (conj Y3 (conj Y4 Y5))). }
  assert (HHS : forall p, (p < length hj)%nat ->
    hl_v (Hs p) = hl_v (hs_held (fst (nth p hj pd0))) /\ hl_cap (Hs p) = hl_cap (hs_held (fst (nth p hj pd0))) /\
    hl_recs (Hs p) = []).
  { intros p Hp. destruct (SRCS p Hp) as (V1 & V2 & V3 & _). exact (conj V1 (conj V2 V3)). }
  eapply (x_main (rc := rc) (fx0 := fx) (fx := fx') (B := B) (API := API) (LS := LS) (SH := SH) (SK := SK)
    (ra := ra) (empty := empty) (j := j) (CS := CS) (F := F) (E := E) (RI := RI) (t := t) (k := k) (L0 := L0)
    (A0 := A0) (regs0 := regs0) (m0 := m0) (md0 := md0) (cl := cl) (br := br) (gn := gn) (dd := dd) (ei := ei)
    (G := G) (nfd := nfd) (mx := mx) (nout := nout) (cap := cap) (out := out) (es := es) (hj := hj) (OUT' := OUT')
    (CAP' := CAP') (Hs := Hs)); try eassumption.
  unfold xm2.
  split; [exact RA|]. split; [exact RM|]. split; [exact INIT|]. split; [exact RO|]. split; [exact KEEP|].
  split; [exact SAVED|]. split; [exact Q14|]. split; [exact Q15|]. split; [exact Q17|]. split; [exact Q18|].
  split; [exact Q19|]. split; [exact Q20|]. split; [exact Q21|]. split; [exact Q22|]. split; [exact Q23|].
  split; [exact Q24|]. split; [exact Q25|].
  split; [intros p Hp; exact (proj2 (proj2 (proj2 (SRCS p Hp))))|].
  split; [exact ZH|]. split; [exact GIN|]. split; [exact BLK|]. split; [exact NL|].
  split; [|exact HRI].
  intros HL. destruct (YL HL) as (_ & _ & _ & _ & _ & _ & _ & Y8). exact Y8.
Qed.

Theorem exit_holds : forall CS RI (F : ResFormT),
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @relay_finish_contract fx rc B (API rc) F) ->
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @check_shape_ends_contract fx rc B (API rc) F) ->
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @source_reset_contract fx rc B (API rc) F) ->
  check_shape_done_contract ->
  exit_res_fin_d F RI CS -> exit_res_ends_s F RI CS -> exit_res_reset_s F RI CS -> RI_end RI CS ->
  exit_ok CS RI.
Proof.
  intros CS RI F HRF HCE HSR HCSD HRA HRB HRC HRE.
  unfold exit_ok. intros B API LS SH SK ra empty rc fx j E HF t k c HL HX.
  eapply SR_bind; [exact (exit_fin CS RI F HRF HRA B API LS SH SK ra empty rc fx j E HF t k c HL HX)|].
  intros c1 H1. eapply SR_bind; [exact (exit_scan CS RI F HCE HRB B API LS SH SK ra empty rc fx j E HF t k c1 H1)|].
  intros c2 H2. exact (exit_end CS RI F HSR HCSD HRC HRE B API LS SH SK ra empty rc fx j E HF t k c2 H2).
Qed.
